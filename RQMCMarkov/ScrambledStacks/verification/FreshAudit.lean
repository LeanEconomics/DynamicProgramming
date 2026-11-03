import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Int.Star
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monte Carlo: unbiasedness, variance `σ²/n`, RMSE `n^{-1/2}`, CLT (post #1)

Copied from `RQMCMarkov/MarkovDriving` (from `RQMCMarkov/PointSets`); see that project for
its documentation.

Post #1 introduces the Monte Carlo estimator `X̄ₙ = (1/n) Σᵢ f(Xᵢ)` for i.i.d. draws `Xᵢ`, says
that its error is of order `n^{-1/2}`, that it is asymptotically normal, and that it offers no
worst-case guarantee: "on rare occasion we will be very unlucky in our random draw and get, e.g.,
that all `n = 10` draws of our `U(0,1)` are less than 0.1".

**Choice of the uniform law.** The uniform law on `[0,1)` is `uniformIco = volume.restrict
(Ico 0 1)`, and on `[0,1)^s` it is `uniformCube s = Measure.pi fun _ ↦ uniformIco` on
`Fin s → ℝ`. Points live in `ℝ` (resp. `Fin s → ℝ`) rather than in a subtype, so that the shifts
and affine maps of the later modules are ordinary real functions.

**Estimator.** `sampleMean n f x = (n)⁻¹ * Σᵢ f (xᵢ)` for a point set `x : Fin n → E`; the random
estimator is `ω ↦ sampleMean n f (fun i ↦ X i ω)`.

## Main results

The general results take independent points `X i` whose laws `νᵢ = P.map (X i)` average to `μ`,
`Σᵢ νᵢ = n • μ` (identically distributed points, stratified points, ...):

* `integral_sampleMean_of_sum_map_eq`: the estimator is unbiased (no independence needed);
* `variance_sampleMean_of_sum_map_eq`: with independence, `Var = n⁻² Σᵢ Var_{νᵢ}(f)`;
* `variance_sampleMean_le_of_sum_map_eq`: with independence, `Var ≤ Var_μ(f) / n`, the MC
  variance. Independent points whose laws average to `μ` never do worse than MC.

Monte Carlo (post #1), i.i.d. draws with law `μ`:

* `integral_sampleMean_iid`: `E[X̄ₙ] = ∫ f dμ`;
* `variance_sampleMean_iid`: `Var(X̄ₙ) = σ² / n`;
* `rmse_sampleMean_iid`: `√E[(X̄ₙ − μ)²] = σ / √n`, the `n^{-1/2}` rate;
* `tendstoInDistribution_sampleMean_iid`: the CLT `√n (X̄ₙ − μ) ⇒ N(0, σ²)`, from Mathlib's
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`;
* `measure_all_draws_lt_tenth`, `measure_all_draws_lt_tenth_pos`: for i.i.d. `U[0,1)` draws,
  `P(all n draws < 1/10) = (1/10)ⁿ > 0`;
* `measure_sampleMean_far_pos`: hence for every `n ≥ 1`, `P(|X̄ₙ − 1/2| > 2/5) ≥ (1/10)ⁿ > 0`:
  MC has no worst-case error bound below `2/5`, for any sample size.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The uniform law on `[0,1)`: Lebesgue measure restricted to `Ico 0 1`. -/
noncomputable abbrev uniformIco : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)

/-- `uniformIco` is a probability measure. -/
theorem isProbabilityMeasure_uniformIco : IsProbabilityMeasure uniformIco :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]⟩

/-- The uniform law on the unit cube `[0,1)^s`, on `Fin s → ℝ`. -/
noncomputable abbrev uniformCube (s : ℕ) : Measure (Fin s → ℝ) :=
  Measure.pi fun _ ↦ uniformIco

/-- `uniformCube s` is a probability measure. -/
theorem isProbabilityMeasure_uniformCube (s : ℕ) : IsProbabilityMeasure (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  exact Measure.pi.instIsProbabilityMeasure _

/-- The sample mean `(1/n) Σᵢ f (xᵢ)` of `f` over a point set `x : Fin n → E`. -/
noncomputable def sampleMean {E : Type*} (n : ℕ) (f : E → ℝ) (x : Fin n → E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (x i)

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}

/-- If the laws of the points sum to `n • μ`, each law is at most `n • μ`. -/
theorem map_le_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E} {μ : Measure E}
    (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) (i : Fin n) : P.map (X i) ≤ (n : ℝ≥0∞) • μ := by
  rw [← hμ]
  exact Finset.single_le_sum (f := fun j ↦ P.map (X j)) (fun j _ ↦ Measure.zero_le _)
    (Finset.mem_univ i)

/-- If the laws of the points sum to `n • μ`, a `μ`-integrable `f` is integrable for each law. -/
theorem integrable_map_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} (hf : Integrable f μ)
    (i : Fin n) : Integrable f (P.map (X i)) :=
  (hf.smul_measure (ENNReal.natCast_ne_top n)).mono_measure (map_le_of_sum_map_eq hμ i)

/-- If the laws of the points sum to `n • μ`, an `f ∈ L^p(μ)` is in `L^p` of each law. -/
theorem memLp_map_of_sum_map_eq {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (i : Fin n) : MemLp f p (P.map (X i)) :=
  (hf.smul_measure (ENNReal.natCast_ne_top n)).mono_measure (map_le_of_sum_map_eq hμ i)

/-- **Unbiasedness from averaged marginals.** If the laws of the points `X i` average to `μ`
(`Σᵢ P.map (X i) = n • μ`, no assumption on the joint law), then
`E[(1/n) Σᵢ f(Xᵢ)] = ∫ f dμ` for every `μ`-integrable `f`. -/
theorem integral_sampleMean_of_sum_map_eq {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ} (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ := by
  have hi := integrable_map_of_sum_map_eq hμ hf
  have hcomp : ∀ i, ∫ ω, f (X i ω) ∂P = ∫ x, f x ∂(P.map (X i)) := fun i ↦
    (integral_map (hX i) (hi i).aestronglyMeasurable).symm
  have hic : ∀ i, Integrable (fun ω ↦ f (X i ω)) P := fun i ↦
    (integrable_map_measure (hi i).aestronglyMeasurable (hX i)).1 (hi i)
  unfold sampleMean
  change ∫ ω, (n : ℝ)⁻¹ * ∑ i, f (X i ω) ∂P = _
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hic i),
    Finset.sum_congr rfl (fun i _ ↦ hcomp i),
    ← integral_finsetSum_measure (fun i _ ↦ hi i), hμ, integral_smul_measure,
    ENNReal.toReal_natCast, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn),
    one_mul]

/-- **Variance from averaged marginals, independent points.** For independent points `X i`,
`Var((1/n) Σᵢ f(Xᵢ)) = n⁻² Σᵢ Var_{νᵢ}(f)`, where `νᵢ = P.map (X i)`. -/
theorem variance_sampleMean_of_sum_map_eq {n : ℕ} {P : Measure Ω}
    {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hind : iIndepFun X P) (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[f; P.map (X i)] := by
  have hL := memLp_map_of_sum_map_eq hμ hf
  have hLc : ∀ i, MemLp (fun ω ↦ f (X i ω)) 2 P := fun i ↦
    (memLp_map_measure_iff (hL i).aestronglyMeasurable (hX i)).1 (hL i)
  have hind' : iIndepFun (fun i ↦ f ∘ X i) P :=
    hind.comp₀ (fun _ ↦ f) hX (fun i ↦ (hL i).aestronglyMeasurable.aemeasurable)
  unfold sampleMean
  rw [variance_const_mul]
  congr 1
  have hsum : (fun ω ↦ ∑ i, f (X i ω)) = ∑ i, (fun ω ↦ f (X i ω)) := by
    funext ω
    rw [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum (fun i _ ↦ hLc i)
    (fun i _ j _ hij ↦ hind'.indepFun hij)]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [variance_map (hL i).aestronglyMeasurable.aemeasurable (hX i)]
  rfl

/-- **Independent points whose laws average to `μ` never do worse than MC.** For independent
points `X i` with `Σᵢ P.map (X i) = n • μ`, `Var((1/n) Σᵢ f(Xᵢ)) ≤ Var_μ(f) / n`. -/
theorem variance_sampleMean_le_of_sum_map_eq {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (hn : n ≠ 0) {X : Fin n → Ω → E} {μ : Measure E} (hX : ∀ i, AEMeasurable (X i) P)
    (hind : iIndepFun X P) (hμ : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] ≤ Var[f; μ] / n := by
  have hL := memLp_map_of_sum_map_eq hμ hf
  set m := ∫ x, f x ∂μ with hm
  have hle : ∀ i, Var[f; P.map (X i)] ≤ ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) := by
    intro i
    rw [← variance_sub_const (hL i).aestronglyMeasurable m]
    exact variance_le_expectation_sq ((hL i).aestronglyMeasurable.sub aestronglyMeasurable_const)
  have hsq : ∀ i, Integrable (fun x ↦ (f x - m) ^ 2) (P.map (X i)) := fun i ↦
    ((hL i).sub (memLp_const m)).integrable_sq
  have hsum : ∑ i, ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) = n * Var[f; μ] := by
    rw [← integral_finsetSum_measure (fun i _ ↦ hsq i), hμ, integral_smul_measure,
      ENNReal.toReal_natCast, smul_eq_mul,
      variance_eq_integral hf.aestronglyMeasurable.aemeasurable]
  rw [variance_sampleMean_of_sum_map_eq hX hind hμ hf]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[f; P.map (X i)]
      ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∫ x, (f x - m) ^ 2 ∂(P.map (X i)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hle i) (sq_nonneg _)
    _ = Var[f; μ] / n := by
        rw [hsum]
        field_simp

/-- Identically distributed points have laws summing to `n • μ`. -/
theorem sum_map_eq_of_hasLaw {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E} {μ : Measure E}
    (hlaw : ∀ i, HasLaw (X i) μ P) : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ := by
  rw [Finset.sum_congr rfl (fun i _ ↦ (hlaw i).map_eq), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]

/-- **MC is unbiased** (post #1): for draws `Xᵢ` with law `μ` (no assumption on the joint law),
`E[X̄ₙ] = ∫ f dμ`. -/
theorem integral_sampleMean_iid {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) {f : E → ℝ} (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ :=
  integral_sampleMean_of_sum_map_eq hn (fun i ↦ (hlaw i).aemeasurable)
    (sum_map_eq_of_hasLaw hlaw) hf

/-- **MC variance** (post #1): for i.i.d. draws with law `μ`, `Var(X̄ₙ) = σ² / n` where
`σ² = Var_μ(f)`. -/
theorem variance_sampleMean_iid {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] = Var[f; μ] / n := by
  rw [variance_sampleMean_of_sum_map_eq (fun i ↦ (hlaw i).aemeasurable) hind
    (sum_map_eq_of_hasLaw hlaw) hf, Finset.sum_congr rfl (fun i _ ↦ by rw [(hlaw i).map_eq]),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero, inv_zero, div_zero]
    ring
  · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
    field_simp

/-- **MC root-mean-square error** (post #1): for i.i.d. draws with law `μ` and `n ≥ 1`,
`√E[(X̄ₙ − ∫ f dμ)²] = σ / √n`, the `n^{-1/2}` rate. -/
theorem rmse_sampleMean_iid {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : n ≠ 0)
    {X : Fin n → Ω → E}
    {μ : Measure E} (hlaw : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, (sampleMean n f (fun i ↦ X i ω) - ∫ x, f x ∂μ) ^ 2 ∂P) =
      Real.sqrt Var[f; μ] / Real.sqrt n := by
  have hL : ∀ i, MemLp f 2 (P.map (X i)) := fun i ↦ by rw [(hlaw i).map_eq]; exact hf
  have hμP : IsProbabilityMeasure μ := by
    rw [← (hlaw ⟨0, Nat.pos_of_ne_zero hn⟩).map_eq]
    infer_instance
  have hmeas : AEMeasurable (fun ω ↦ sampleMean n f (fun i ↦ X i ω)) P := by
    unfold sampleMean
    refine AEMeasurable.const_mul ?_ _
    exact Finset.aemeasurable_fun_sum _ (fun i _ ↦
      (hL i).aestronglyMeasurable.aemeasurable.comp_aemeasurable (hlaw i).aemeasurable)
  rw [← integral_sampleMean_iid hn hlaw (hf.integrable one_le_two), ← variance_eq_integral hmeas,
    variance_sampleMean_iid hlaw hind hf, Real.sqrt_div' _ (Nat.cast_nonneg n)]

/-- **MC central limit theorem** (post #2: "If we were to use standard MC, the asymptotic
distribution of the estimates would be normally distributed"). For an i.i.d. sequence `X k` with
law `μ` and `f ∈ L²(μ)`, `√n (X̄ₙ − ∫ f dμ)` converges in distribution to `N(0, σ²)`. A
restatement of Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem tendstoInDistribution_sampleMean_iid {P : Measure Ω} [IsProbabilityMeasure P] {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → E}
    {μ : Measure E} (hlaw : ∀ k, HasLaw (X k) μ P) (hind : iIndepFun X P) {f : E → ℝ}
    (hf : MemLp f 2 μ) {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 Var[f; μ].toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt n * (sampleMean n f (fun i : Fin n ↦ X i ω) - ∫ x, f x ∂μ))
      atTop Z (fun _ ↦ P) P' := by
  have hL : ∀ k, MemLp f 2 (P.map (X k)) := fun k ↦ by rw [(hlaw k).map_eq]; exact hf
  have hfm : ∀ k, AEMeasurable f (P.map (X k)) := fun k ↦
    (hL k).aestronglyMeasurable.aemeasurable
  set Y : ℕ → Ω → ℝ := fun k ω ↦ f (X k ω) with hY
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) P P := by
    intro k
    have h0 : IdentDistrib (X k) (X 0) P P :=
      ⟨(hlaw k).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw k).map_eq, (hlaw 0).map_eq]⟩
    exact h0.comp_of_aemeasurable (hfm k)
  have hindY : iIndepFun Y P := hind.comp₀ (fun _ ↦ f) (fun k ↦ (hlaw k).aemeasurable) hfm
  have hY0 : MemLp (Y 0) 2 P :=
    (memLp_map_measure_iff (hL 0).aestronglyMeasurable (hlaw 0).aemeasurable).1 (hL 0)
  have hmean : P[Y 0] = ∫ x, f x ∂μ := by
    rw [hY, ← (hlaw 0).map_eq, integral_map (hlaw 0).aemeasurable (hL 0).aestronglyMeasurable]
  have hvar : Var[Y 0; P] = Var[f; μ] := by
    rw [← (hlaw 0).map_eq, variance_map (hfm 0) (hlaw 0).aemeasurable]
    rfl
  rw [← hvar] at hZ
  have key := tendstoInDistribution_inv_sqrt_mul_sum_sub hZ hY0 hindY hident
  rw [hmean] at key
  convert key using 1
  funext n ω
  unfold sampleMean
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ f (X k ω)) n]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, zero_mul]
  · have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 h)
    have hsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt n := ⟨_, rfl⟩
    rw [← hr] at hs hsq
    rw [← hr, hsq]
    simp only [hY]
    field_simp

/-- **The unlucky draw** (post #1). For independent draws `Xᵢ ~ U[0,1)`,
`P(all n draws are < 1/10) = (1/10)ⁿ`. -/
theorem measure_all_draws_lt_tenth {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    P {ω | ∀ i, X i ω < 1 / 10} = (1 / 10 : ℝ≥0∞) ^ n := by
  have hset : {ω | ∀ i, X i ω < 1 / 10} = ⋂ i ∈ (Finset.univ : Finset (Fin n)),
      X i ⁻¹' Iio (1 / 10) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_univ, mem_preimage, mem_Iio, true_imp_iff]
  have hI : Iio (1 / 10 : ℝ) ∩ Ico 0 1 = Ico 0 (1 / 10) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  have hone : ∀ i, P (X i ⁻¹' Iio (1 / 10)) = 1 / 10 := by
    intro i
    rw [← Measure.map_apply_of_aemeasurable (hlaw i).aemeasurable measurableSet_Iio,
      (hlaw i).map_eq, Measure.restrict_apply measurableSet_Iio,
      hI, Real.volume_Ico, sub_zero, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  rw [hset, hind.measure_inter_preimage_eq_mul Finset.univ (fun _ _ ↦ measurableSet_Iio),
    Finset.prod_congr rfl (fun i _ ↦ hone i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The unlucky draw has positive probability, for every `n` (post #1). -/
theorem measure_all_draws_lt_tenth_pos {n : ℕ} {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    0 < P {ω | ∀ i, X i ω < 1 / 10} := by
  rw [measure_all_draws_lt_tenth hlaw hind]
  exact ENNReal.pow_pos (by norm_num) n

/-- **MC has no worst-case guarantee** (post #1). For i.i.d. `U[0,1)` draws and every `n ≥ 1`,
the MC estimate of `μ = 1/2` misses by more than `2/5` with probability at least `(1/10)ⁿ > 0`. -/
theorem measure_sampleMean_far_pos {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) uniformIco P) (hind : iIndepFun X P) :
    (1 / 10 : ℝ≥0∞) ^ n ≤ P {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} ∧
      0 < P {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} := by
  have hsub : {ω | ∀ i, X i ω < 1 / 10} ⊆
      {ω | 2 / 5 < |sampleMean n id (fun i ↦ X i ω) - 1 / 2|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hlt : sampleMean n id (fun i ↦ X i ω) < 1 / 10 := by
      unfold sampleMean
      have hs : ∑ i, id (X i ω) < ∑ _i : Fin n, (1 / 10 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩)
          (fun i _ ↦ hω i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      rw [inv_mul_lt_iff₀ hn']
      linarith
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have h1 := measure_mono (μ := P) hsub
  rw [measure_all_draws_lt_tenth hlaw hind] at h1
  exact ⟨h1, lt_of_lt_of_le (ENNReal.pow_pos (by norm_num) n) h1⟩

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# RQMC requirement (i): marginally uniform points give an unbiased estimator (posts #1–#2)

Copied from `RQMCMarkov/MarkovDriving` (from `RQMCMarkov/PointSets`); see that project for
its documentation.

Posts #1 and #2 require of an RQMC point set `{z₁, …, zₙ}` that "(i) each individual point is
uniformly distributed (0,1), marginally", and say that RQMC then gives "an unbiased …
estimator". Reading: in `s` dimensions, points `zᵢ : Ω → (Fin s → ℝ)` with each law
`P.map zᵢ = uniformCube s` (nothing assumed on the joint law).

## Main results

* `integral_sampleMean_of_hasLaw_uniformCube`: under (i), `E[(1/n) Σᵢ f(zᵢ)] = ∫ f` over
  `[0,1)^s`, for every integrable `f`.
* Random shift modulo 1 (post #2's "random shift", the randomization of lattice rules):
  `measurePreserving_fract_add` (`u ↦ fract (c + u)` preserves `U[0,1)`),
  `measurePreserving_shiftMod1` (the same coordinatewise on `[0,1)^s`), `hasLaw_shiftMod1`,
  `shiftMod1_mem_cube`, and `integral_sampleMean_shiftMod1`: shifting ANY fixed point set
  `y₁, …, yₙ ∈ ℝ^s` by one common `U ~ U[0,1)^s` modulo 1 satisfies (i), hence is unbiased.
* Stratification (post #2): strata `stratum n i = [i/n, (i+1)/n)` and the affine maps
  `stratumMap n i u = (i + u)/n`; `map_stratumMap_uniformIco` (the law of `(i + U)/n` is uniform on
  stratum `i`), `iUnion_stratum`, `pairwise_disjoint_stratum`, `sum_map_stratumMap`,
  `sum_map_stratified` and `integral_sampleMean_stratified`: one point `(i + Vᵢ)/n` per stratum
  with `Vᵢ ~ U[0,1)` (any joint law: independent `Vᵢ`, or one common `V`) is unbiased.
* `integral_sampleMean_of_hasLaw_const`, `variance_sampleMean_const`: requirement (i) alone does
  not reduce variance (all points equal to one uniform `U`); requirement (ii) is what matters
  for the variance.

**Correction.** Requirement (i) is sufficient for unbiasedness but not necessary, and
stratified sampling — post #2's first RQMC method — violates it:
`not_hasLaw_stratumMap` shows that for `n ≥ 2` the point `(i + V)/n` of stratum `i` is NOT
marginally `U[0,1)` (it is uniform on its stratum). The exact condition is that the marginal laws
AVERAGE to the uniform law, `Σᵢ P.map zᵢ = n • μ`: it implies unbiasedness for every integrable
`f` (`integral_sampleMean_of_sum_map_eq`, in `MonteCarlo`), and it is implied by unbiasedness for
indicator functions (`sum_map_eq_of_integral_sampleMean_indicator`), so it is equivalent to
unbiasedness for all bounded measurable `f`. (Randomly permuting the labels of a stratified set
would restore (i) without changing the estimator.)
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **RQMC requirement (i) gives unbiasedness** (posts #1–#2): if each point `zᵢ` is marginally
uniform on `[0,1)^s` (no assumption on the joint law), then
`E[(1/n) Σᵢ f(zᵢ)] = ∫ f d U[0,1)^s` for every integrable `f`. -/
theorem integral_sampleMean_of_hasLaw_uniformCube {n s : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {z : Fin n → Ω → (Fin s → ℝ)} (hz : ∀ i, HasLaw (z i) (uniformCube s) P)
    {f : (Fin s → ℝ) → ℝ} (hf : Integrable f (uniformCube s)) :
    ∫ ω, sampleMean n f (fun i ↦ z i ω) ∂P = ∫ x, f x ∂(uniformCube s) :=
  integral_sampleMean_iid hn hz hf

/-- `uniformIco` is Lebesgue measure restricted to `(0,1]`. -/
theorem uniformIco_eq_restrict_Ioc : uniformIco = volume.restrict (Ioc (0 : ℝ) 1) :=
  Measure.restrict_congr_set Ico_ae_eq_Ioc

/-- The pushforward of Lebesgue measure on `(t, t+1]` by `Int.fract` does not depend on `t`. -/
theorem map_fract_restrict_Ioc (t : ℝ) :
    (volume.restrict (Ioc t (t + 1))).map Int.fract =
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))).map Int.fract := by
  set h : UnitAddCircle → ℝ := fun x ↦ ((AddCircle.equivIco (1 : ℝ) 0 x : Ico (0 : ℝ) (0 + 1)) : ℝ)
    with hh
  have hhm : Measurable h :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hfr : (Int.fract : ℝ → ℝ) = h ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x
    simp only [hh, Function.comp_apply]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  have key : ∀ t : ℝ, (volume.restrict (Ioc t (t + 1))).map Int.fract =
      (volume : Measure UnitAddCircle).map h := by
    intro t
    rw [hfr, ← Measure.map_map hhm AddCircle.measurable_mk',
      (UnitAddCircle.measurePreserving_mk t).map_eq]
  rw [key t, key 0]

/-- **A shift modulo 1 preserves the uniform law**: `u ↦ fract (c + u)` maps `U[0,1)` to itself,
for every real `c`. -/
theorem measurePreserving_fract_add (c : ℝ) :
    MeasurePreserving (fun u ↦ Int.fract (c + u)) uniformIco uniformIco := by
  have hm : Measurable fun u : ℝ ↦ Int.fract (c + u) :=
    measurable_fract.comp (measurable_const_add c)
  refine ⟨hm, ?_⟩
  have hfr : (fun u : ℝ ↦ Int.fract (c + u)) = Int.fract ∘ (fun u ↦ c + u) := rfl
  have hshift : (volume.restrict (Ioc (0 : ℝ) 1)).map (fun u ↦ c + u) =
      volume.restrict (Ioc c (c + 1)) := by
    have hpre : (fun u : ℝ ↦ c + u) ⁻¹' Ioc c (c + 1) = Ioc 0 1 := by
      ext u
      simp only [mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    rw [← hpre, ← Measure.restrict_map (measurable_const_add c) measurableSet_Ioc,
      map_add_left_eq_self]
  have hid : uniformIco.map Int.fract = uniformIco := by
    have hae : Int.fract =ᵐ[uniformIco] id :=
      ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ Int.fract_eq_self.2 hx)
    rw [Measure.map_congr hae, Measure.map_id]
  rw [hfr, ← Measure.map_map measurable_fract (measurable_const_add c)]
  nth_rewrite 1 [uniformIco_eq_restrict_Ioc]
  rw [hshift, map_fract_restrict_Ioc, zero_add, ← uniformIco_eq_restrict_Ioc, hid]

/-- The random shift modulo 1 of a point `y ∈ ℝ^s` by `u`: `k ↦ fract (y k + u k)`. -/
noncomputable def shiftMod1 {s : ℕ} (y u : Fin s → ℝ) : Fin s → ℝ :=
  fun k ↦ Int.fract (y k + u k)

/-- A shifted point lies in `[0,1)^s`. -/
theorem shiftMod1_mem_cube {s : ℕ} (y u : Fin s → ℝ) (k : Fin s) :
    shiftMod1 y u k ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The shift modulo 1 preserves `U[0,1)^s`**, for every fixed `y ∈ ℝ^s`. -/
theorem measurePreserving_shiftMod1 {s : ℕ} (y : Fin s → ℝ) :
    MeasurePreserving (shiftMod1 y) (uniformCube s) (uniformCube s) := by
  have := isProbabilityMeasure_uniformIco
  exact measurePreserving_pi _ _ (fun k ↦ measurePreserving_fract_add (y k))

/-- If `U ~ U[0,1)^s` then `shiftMod1 y U ~ U[0,1)^s`. -/
theorem hasLaw_shiftMod1 {s : ℕ} (y : Fin s → ℝ) {P : Measure Ω} {U : Ω → Fin s → ℝ}
    (hU : HasLaw U (uniformCube s) P) : HasLaw (fun ω ↦ shiftMod1 y (U ω)) (uniformCube s) P :=
  (measurePreserving_shiftMod1 y).fun_comp_hasLaw hU

/-- **The randomly shifted point set is unbiased** (post #2): for ANY fixed points
`y₁, …, yₙ ∈ ℝ^s` and one common `U ~ U[0,1)^s`, the points `fract (yᵢ + U)` satisfy
requirement (i), so `E[(1/n) Σᵢ f(fract (yᵢ + U))] = ∫ f d U[0,1)^s`. -/
theorem integral_sampleMean_shiftMod1 {n s : ℕ} (hn : n ≠ 0) (y : Fin n → Fin s → ℝ)
    {P : Measure Ω} {U : Ω → Fin s → ℝ} (hU : HasLaw U (uniformCube s) P)
    {f : (Fin s → ℝ) → ℝ} (hf : Integrable f (uniformCube s)) :
    ∫ ω, sampleMean n f (fun i ↦ shiftMod1 (y i) (U ω)) ∂P = ∫ x, f x ∂(uniformCube s) :=
  integral_sampleMean_of_hasLaw_uniformCube hn (fun i ↦ hasLaw_shiftMod1 (y i) hU) hf

/-- The `i`-th stratum `[i/n, (i+1)/n)` of `[0,1)`. -/
def stratum (n i : ℕ) : Set ℝ := Ico ((i : ℝ) / n) ((i + 1) / n)

/-- Strata are measurable. -/
theorem measurableSet_stratum (n i : ℕ) : MeasurableSet (stratum n i) := measurableSet_Ico

/-- The affine map `u ↦ (i + u)/n` from `[0,1)` onto the `i`-th stratum. -/
noncomputable def stratumMap (n i : ℕ) (u : ℝ) : ℝ := (i + u) / n

/-- `stratumMap n i` is measurable. -/
theorem measurable_stratumMap (n i : ℕ) : Measurable (stratumMap n i) :=
  (measurable_const_add _).div_const _

/-- `stratumMap n i` maps `[0,1)` onto the stratum: `(i + u)/n ∈ stratum n i ↔ u ∈ [0,1)`. -/
theorem stratumMap_preimage_stratum {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    stratumMap n i ⁻¹' stratum n i = Ico 0 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  ext u
  simp only [stratum, stratumMap, mem_preimage, mem_Ico]
  rw [div_le_div_iff_of_pos_right hn', div_lt_div_iff_of_pos_right hn']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **The law of `(i + U)/n`**, `U ~ U[0,1)`, is `n` times Lebesgue measure on stratum `i`. -/
theorem map_stratumMap_uniformIco {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    uniformIco.map (stratumMap n i) = (n : ℝ≥0∞) • volume.restrict (stratum n i) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hvol : (volume : Measure ℝ).map (stratumMap n i) = (n : ℝ≥0∞) • volume := by
    have hcomp : stratumMap n i = (fun x : ℝ ↦ x * (n : ℝ)⁻¹) ∘ (fun u : ℝ ↦ (i : ℝ) + u) := by
      funext u
      simp only [stratumMap, Function.comp_apply, div_eq_mul_inv]
    rw [hcomp, ← Measure.map_map (measurable_mul_const _) (measurable_const_add _),
      map_add_left_eq_self, Real.map_volume_mul_right (inv_ne_zero hn'.ne'), inv_inv,
      abs_of_pos hn', ENNReal.ofReal_natCast]
  change (volume.restrict (Ico (0 : ℝ) 1)).map (stratumMap n i) = _
  rw [← stratumMap_preimage_stratum hn i,
    ← Measure.restrict_map (measurable_stratumMap n i) (measurableSet_stratum n i), hvol,
    Measure.restrict_smul]

/-- The strata cover `[0,1)`. -/
theorem iUnion_stratum {n : ℕ} (hn : n ≠ 0) : ⋃ i : Fin n, stratum n i = Ico 0 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  ext x
  simp only [mem_iUnion, stratum, mem_Ico]
  constructor
  · rintro ⟨i, h1, h2⟩
    have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) hn'.le) h1, ?_⟩
    calc x < ((i : ℝ) + 1) / n := h2
      _ ≤ n / n := div_le_div_of_nonneg_right hi hn'.le
      _ = 1 := div_self hn'.ne'
  · rintro ⟨h0, h1⟩
    have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg hn'.le h0
    have hlt : ⌊(n : ℝ) * x⌋₊ < n := by
      rw [Nat.floor_lt hnx]
      calc (n : ℝ) * x < n * 1 := mul_lt_mul_of_pos_left h1 hn'
        _ = n := mul_one _
    refine ⟨⟨⌊(n : ℝ) * x⌋₊, hlt⟩, ?_, ?_⟩
    · change ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n ≤ x
      rw [div_le_iff₀ hn', mul_comm x]
      exact Nat.floor_le hnx
    · change x < ((⌊(n : ℝ) * x⌋₊ : ℕ) + 1 : ℝ) / n
      rw [lt_div_iff₀ hn', mul_comm x]
      exact Nat.lt_floor_add_one _

/-- Distinct strata are disjoint. -/
theorem pairwise_disjoint_stratum (n : ℕ) :
    Pairwise (Function.onFun Disjoint fun i : Fin n ↦ stratum n i) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  simp only [stratum, mem_Ico] at hxi hxj
  rcases Nat.eq_zero_or_pos n with h | h
  · exact (Fin.elim0 (h ▸ i))
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 h
  rw [div_le_iff₀ hn', lt_div_iff₀ hn'] at hxi hxj
  have h1 : (i : ℝ) < j + 1 := by linarith
  have h2 : (j : ℝ) < i + 1 := by linarith
  have h1' : (i : ℕ) < j + 1 := by exact_mod_cast h1
  have h2' : (j : ℕ) < i + 1 := by exact_mod_cast h2
  exact hij (Fin.ext (by omega))

/-- **The stratum laws average to the uniform law**: `Σᵢ law((i + U)/n) = n • U[0,1)`. -/
theorem sum_map_stratumMap {n : ℕ} (hn : n ≠ 0) :
    ∑ i : Fin n, uniformIco.map (stratumMap n i) = (n : ℝ≥0∞) • uniformIco := by
  rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ map_stratumMap_uniformIco hn i),
    ← Finset.smul_sum,
    ← Measure.sum_fintype, ← Measure.restrict_iUnion (pairwise_disjoint_stratum n)
      (fun _ ↦ measurableSet_Ico), iUnion_stratum hn]

/-- **Stratified points have uniformly averaged marginals**: if `Vᵢ ~ U[0,1)` for each `i` (any
joint law), the points `(i + Vᵢ)/n` satisfy `Σᵢ P.map ((i + Vᵢ)/n) = n • U[0,1)`. -/
theorem sum_map_stratified {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) :
    ∑ i : Fin n, P.map (fun ω ↦ stratumMap n i (V i ω)) = (n : ℝ≥0∞) • uniformIco := by
  rw [← sum_map_stratumMap hn]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← (hV i).map_eq, AEMeasurable.map_map_of_aemeasurable
    (measurable_stratumMap n i).aemeasurable (hV i).aemeasurable]
  rfl

/-- **Stratified sampling is unbiased** (post #2): one point `(i + Vᵢ)/n` in each stratum, with
`Vᵢ ~ U[0,1)` (independent, or one common `V`, or any joint law), gives
`E[(1/n) Σᵢ f((i + Vᵢ)/n)] = ∫₀¹ f`. -/
theorem integral_sampleMean_stratified {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) {f : ℝ → ℝ}
    (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean n f (fun i ↦ stratumMap n i (V i ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_of_sum_map_eq hn
    (fun i ↦ (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable)
    (sum_map_stratified hn hV) hf

/-- **Correction: stratified points violate requirement (i).** For `n ≥ 2` the stratified point
`(i + V)/n`, `V ~ U[0,1)`, is not marginally uniform on `[0,1)` (it is uniform on its stratum),
although the stratified estimator is unbiased (`integral_sampleMean_stratified`). -/
theorem not_hasLaw_stratumMap {n : ℕ} (hn : 2 ≤ n) (i : Fin n) {P : Measure Ω} {V : Ω → ℝ}
    (hV : HasLaw V uniformIco P) :
    ¬ HasLaw (fun ω ↦ stratumMap n i (V ω)) uniformIco P := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  have hlaw : uniformIco = (n : ℝ≥0∞) • volume.restrict (stratum n i) := by
    rw [← h.map_eq, ← map_stratumMap_uniformIco hn0 i, ← hV.map_eq,
      AEMeasurable.map_map_of_aemeasurable (measurable_stratumMap n i).aemeasurable
        hV.aemeasurable]
    rfl
  have hsub : stratum n i ⊆ Ico 0 1 := by
    rw [← iUnion_stratum hn0]
    exact subset_iUnion (fun j : Fin n ↦ stratum n j) i
  have hvol : volume (stratum n i) = ENNReal.ofReal (1 / n) := by
    rw [stratum, Real.volume_Ico]
    congr 1
    ring
  have h1 : uniformIco (stratum n i) = ENNReal.ofReal (1 / n) := by
    change volume.restrict (Ico (0 : ℝ) 1) (stratum n i) = _
    rw [Measure.restrict_apply (measurableSet_stratum n i), inter_eq_self_of_subset_left hsub,
      hvol]
  have h2 : ((n : ℝ≥0∞) • volume.restrict (stratum n i)) (stratum n i) = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_stratum n i), inter_self, hvol,
      smul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
      mul_one_div_cancel hn'.ne', ENNReal.ofReal_one]
  rw [← hlaw, h1, ENNReal.ofReal_eq_one] at h2
  have : (n : ℝ) = 1 := by
    rw [div_eq_one_iff_eq hn'.ne'] at h2
    exact h2.symm
  have : n = 1 := by exact_mod_cast this
  omega

/-- **Corrected statement: averaged marginals are necessary.** If the estimator is unbiased for
every indicator function, `E[(1/n) Σᵢ 1_A(zᵢ)] = μ(A)`, then the marginal laws average to `μ`:
`Σᵢ P.map zᵢ = n • μ`. With `integral_sampleMean_of_sum_map_eq` this makes averaged marginals
the exact condition for unbiasedness. -/
theorem sum_map_eq_of_integral_sampleMean_indicator {E : Type*} {mE : MeasurableSpace E}
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {z : Fin n → Ω → E} {μ : Measure E}
    [IsFiniteMeasure μ] (hz : ∀ i, AEMeasurable (z i) P)
    (h : ∀ A, MeasurableSet A →
      ∫ ω, sampleMean n (A.indicator 1) (fun i ↦ z i ω) ∂P = μ.real A) :
    ∑ i, P.map (z i) = (n : ℝ≥0∞) • μ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_smul]
  ext A hA
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hint : ∀ i, Integrable (fun ω ↦ A.indicator (1 : E → ℝ) (z i ω)) P := fun i ↦
    ((integrable_const (1 : ℝ)).indicator hA).comp_aemeasurable (hz i)
  have hreal : ∀ i, ∫ ω, A.indicator (1 : E → ℝ) (z i ω) ∂P = (P.map (z i)).real A := fun i ↦ by
    rw [← integral_indicator_one hA,
      integral_map (hz i) ((measurable_one.indicator hA).aestronglyMeasurable)]
  have hA' := h A hA
  unfold sampleMean at hA'
  change ∫ ω, (n : ℝ)⁻¹ * ∑ i, A.indicator (1 : E → ℝ) (z i ω) ∂P = _ at hA'
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hint i),
    Finset.sum_congr rfl (fun i _ ↦ hreal i), inv_mul_eq_iff_eq_mul₀ hn'] at hA'
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hfin : ∀ i, P.map (z i) A = ENNReal.ofReal ((P.map (z i)).real A) := fun i ↦
    (ofReal_measureReal (measure_ne_top _ A)).symm
  rw [Finset.sum_congr rfl (fun i _ ↦ hfin i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ measureReal_nonneg), hA',
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
    ofReal_measureReal (measure_ne_top _ A)]

/-- With all points equal, the sample mean is the value at that point. -/
theorem sampleMean_const_points {E : Type*} {n : ℕ} (hn : n ≠ 0) (f : E → ℝ) (x : E) :
    sampleMean n f (fun _ ↦ x) = f x := by
  rw [sampleMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul]

/-- **Requirement (i) alone: all points equal.** Taking every point equal to one `U ~ μ`
satisfies (i) and is unbiased ... -/
theorem integral_sampleMean_of_hasLaw_const {E : Type*} {mE : MeasurableSpace E} {n : ℕ}
    (hn : n ≠ 0) {P : Measure Ω} {U : Ω → E} {μ : Measure E} (hU : HasLaw U μ P) {f : E → ℝ}
    (hf : Integrable f μ) :
    ∫ ω, sampleMean n f (fun _ : Fin n ↦ U ω) ∂P = ∫ x, f x ∂μ :=
  integral_sampleMean_iid hn (fun _ ↦ hU) hf

/-- **... but its variance is the variance of ONE draw**, `Var_μ(f)`, not `Var_μ(f)/n`: (i)
says nothing about the variance; the joint structure (requirement (ii)) is what reduces it. -/
theorem variance_sampleMean_const {E : Type*} {mE : MeasurableSpace E} {n : ℕ} (hn : n ≠ 0)
    {P : Measure Ω} {U : Ω → E} {μ : Measure E} (hU : HasLaw U μ P) {f : E → ℝ}
    (hf : AEMeasurable f μ) :
    Var[fun ω ↦ sampleMean n f (fun _ : Fin n ↦ U ω); P] = Var[f; μ] := by
  have hfun : (fun ω ↦ sampleMean n f (fun _ : Fin n ↦ U ω)) = f ∘ U := by
    funext ω
    exact sampleMean_const_points hn f (U ω)
  rw [hfun, ← variance_map (hU.map_eq ▸ hf) hU.aemeasurable, hU.map_eq]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Driving a finite Markov chain by uniforms: inverse CDF, paths, stacks, counts (post #3)

Copied from `RQMCMarkov/MarkovDriving` (namespace and imports renamed).

Post #3 simulates a chain with `n` states and transition matrix `P` by the inverse-CDF rule: from
state `i` with a uniform `u`, go to the smallest `j` with `u ≤ cs_{ij} = Σ_{k ≤ j} p_{ik}`. A
uniform sequence `u¹, u², …` then "drives" the chain; in the stack representation each state has
its own sequence, and the `k`-th departure from `i` uses point `k` of stack `i`.

**Conventions.** States are `Fin n`, `0`-indexed (post #3's `x_j` is `j - 1 : Fin n`); a
stochastic matrix is `P : Fin n → Fin n → ℝ` with `IsStochastic P` (nonnegative rows summing to
one). Time starts at `0`: a path is `x : ℕ → S` with `x 0 = x₀`, and `u t` drives the
transition `t → t + 1` (post #3's `u^t` and `x^{t+1}`). Counts over the horizon `T` use the
times `t < T` (occupation) and the transitions `t → t + 1`, `t < T`.

## Main definitions

* `IsStochastic P`; `cumProb P i m = Σ_{k < m} P i k` (post #3's `cs_{ij}` is `cumProb P i j`);
  `step P i u`, the inverse-CDF update, total (the last state when no `j` qualifies, `u > 1`).
* `drive G x₀ u` (any update rule `G : S → α → S`) and `drivenPath P x₀ u = drive (step P) x₀ u`.
* `stackDrive G x₀ v` (per-state stacks `v : S → ℕ → α`), `stackPath P x₀ v`, and the
  `departureIndex path t = #{t' < t : path t' = path t}`.
* `occCount path i T` (the visit counter) and `transCount path i j T`.
* `IsSpellStart`, `runLength path t T` (censored at `T`), `spellCount path i T`.

## Main results

* `step_eq_iff`: for `u ∈ (0, 1]`, `step P i u = j ↔ cs_{i,j-1} < u ≤ cs_{ij}`;
  `step_preimage_inter_Ioc`, `step_mono`, `measurable_step`; `step_zero` (precision: at `u = 0`
  the rule picks the first state even if `p_{i1} = 0`, a null event).
* `uniformIco_step_eq`, `volume_step_eq`: `volume {u ∈ [0,1) : step P i u = j} = P i j`
  (post #3, "the probability that it falls in the interval … is exactly … `p_{2j}`").
* `step_post3_example`: post #3's `n = 3` example (`u = 0.79` goes to the second state).
* `drive_eq_iff`, `stackDrive_eq_iff`: pathwise descriptions (the path equals `s` up to `T` iff
  `s` starts at `x₀` and each transition of `s` is produced by the corresponding uniform);
  `stackDrive_succ` ("the `k`-th visit to state `i` uses point `k` of stack `i`");
  `departureIndex_injective`: the stack entries used at different times are different.
* Counts: `occCount_succ`, `transCount_succ`, `occCount_add`, `transCount_add`,
  `sum_occCount` (`Σ_i N_i(T) = T`), `sum_transCount_right` (`Σ_j N_ij(T) = N_i(T)`),
  `sum_transCount_left`, `flowBalance`, `abs_flowBalance_le` (post #3, "every state is entered as
  often as it is left (allowing for the first and last states)").
* Spells: `runLength_eq_iff`, `spellCount_succ_eq` (spells of `i` = start + entries into `i`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory Finset

/-- A **stochastic matrix** on a finite state space: nonnegative rows summing to one. -/
structure IsStochastic {S : Type*} [Fintype S] (P : S → S → ℝ) : Prop where
  /-- Every transition probability is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Every row sums to one. -/
  sum_eq_one : ∀ i, ∑ j, P i j = 1

variable {n : ℕ}

/-- The cumulative row sum `cumProb P i m = Σ_{k < m} P i k` (states `Fin n`, `0`-indexed).
Post #3's `cs_{ij} = Σ_{k=1}^{j} p_{ik}` (`1`-indexed) is `cumProb P i j`; for a state
`j : Fin n` the post's interval `(cs_{i,j-1}, cs_{ij}]` is `(cumProb P i j, cumProb P i (j+1)]`. -/
noncomputable def cumProb (P : Fin n → Fin n → ℝ) (i : Fin n) (m : ℕ) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin n ↦ (k : ℕ) < m), P i k

/-- The last state `n - 1` of `Fin n` (`Fin n` is nonempty since it contains `i`). -/
def lastState (i : Fin n) : Fin n := ⟨n - 1, by have := i.isLt; omega⟩

/-- **The inverse-CDF update** (post #3): from state `i` with uniform `u`, go to the smallest
`j` with `u ≤ cs_{ij}`, i.e. `u ≤ cumProb P i (j + 1)`. Total: if no such `j` exists (only when
`u > 1`), go to the last state. -/
noncomputable def step (P : Fin n → Fin n → ℝ) (i : Fin n) (u : ℝ) : Fin n :=
  (insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min'
    (insert_nonempty _ _)

/-- `cumProb P i 0 = 0`. -/
theorem cumProb_zero (P : Fin n → Fin n → ℝ) (i : Fin n) : cumProb P i 0 = 0 := by
  unfold cumProb
  rw [Finset.sum_eq_zero]
  intro k hk
  exact absurd (Finset.mem_filter.1 hk).2 (Nat.not_lt_zero _)

/-- `cumProb P i (j + 1) = cumProb P i j + P i j`. -/
theorem cumProb_succ (P : Fin n → Fin n → ℝ) (i j : Fin n) :
    cumProb P i (j + 1) = cumProb P i j + P i j := by
  unfold cumProb
  have h : univ.filter (fun k : Fin n ↦ (k : ℕ) < j + 1) =
      insert j (univ.filter (fun k : Fin n ↦ (k : ℕ) < j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, Fin.ext_iff]
    tauto
  rw [h, Finset.sum_insert, add_comm]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_irrefl, not_false_eq_true]

/-- For `m ≥ n`, `cumProb P i m` is the whole row sum. -/
theorem cumProb_of_le (P : Fin n → Fin n → ℝ) (i : Fin n) {m : ℕ} (hm : n ≤ m) :
    cumProb P i m = ∑ k, P i k := by
  unfold cumProb
  rw [Finset.filter_true_of_mem]
  intro k _
  exact lt_of_lt_of_le k.isLt hm

/-- The cumulative sums of a nonnegative row are monotone. -/
theorem cumProb_mono {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    Monotone (cumProb P i) := by
  intro a b hab
  unfold cumProb
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ ↦ hP i k)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  omega

/-- The cumulative sums of a stochastic row lie in `[0, 1]`. -/
theorem cumProb_mem_Icc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (m : ℕ) :
    cumProb P i m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← cumProb_zero P i]
    exact cumProb_mono hP.nonneg i (Nat.zero_le m)
  · rw [← hP.sum_eq_one i, ← cumProb_of_le P i (le_max_left n m)]
    exact cumProb_mono hP.nonneg i (le_max_right n m)

/-- **The inverse-CDF rule** (post #3): for `u ∈ (0, 1]`, `step P i u = j` iff
`cs_{i,j-1} < u ≤ cs_{ij}`, i.e. `cumProb P i j < u ≤ cumProb P i (j + 1)`. -/
theorem step_eq_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    step P i u = j ↔ cumProb P i j < u ∧ u ≤ cumProb P i (j + 1) := by
  have hlast : cumProb P i ((lastState i : ℕ) + 1) = 1 := by
    rw [cumProb_of_le P i (by simp only [lastState]; omega), hP.sum_eq_one i]
  constructor
  · intro h
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      h ▸ Finset.min'_mem _ _
    refine ⟨?_, ?_⟩
    · by_cases hj0 : (j : ℕ) = 0
      · rw [hj0, cumProb_zero]
        exact hu.1
      · by_contra hcon
        have hk : (⟨j - 1, by omega⟩ : Fin n) ∈
            insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
          refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
          have : (j : ℕ) - 1 + 1 = j := by omega
          change u ≤ cumProb P i ((j : ℕ) - 1 + 1)
          rw [this]
          exact le_of_not_gt hcon
        have hle : step P i u ≤ ⟨j - 1, by omega⟩ := Finset.min'_le _ _ hk
        rw [h, Fin.le_def] at hle
        change (j : ℕ) ≤ j - 1 at hle
        omega
    · rcases Finset.mem_insert.1 hj with hj | hj
      · rw [hj, hlast]
        exact hu.2
      · exact (Finset.mem_filter.1 hj).2
  · rintro ⟨h1, h2⟩
    have hj : j ∈ insert (lastState i) (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
    refine le_antisymm (Finset.min'_le _ _ hj) (Finset.le_min' _ _ _ ?_)
    intro y hy
    rcases Finset.mem_insert.1 hy with hy | hy
    · rw [hy, Fin.le_def]
      simp only [lastState]
      omega
    · have hy' := (Finset.mem_filter.1 hy).2
      by_contra hlt
      rw [not_le, Fin.lt_def] at hlt
      have := cumProb_mono hP.nonneg i (show (y : ℕ) + 1 ≤ j by omega)
      linarith

/-- The inverse-CDF update is monotone in the uniform. -/
theorem step_mono (P : Fin n → Fin n → ℝ) (i : Fin n) : Monotone (step P i) := by
  intro u u' huu'
  refine Finset.min'_subset _ ?_
  intro j hj
  rcases Finset.mem_insert.1 hj with hj | hj
  · exact hj ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨Finset.mem_univ _, le_trans huu' (Finset.mem_filter.1 hj).2⟩)

/-- **Precision on post #3's rule at `u = 0`**: "the smallest index such that `u ≤ cs`" sends
`u = 0` to the first state even when `p_{i1} = 0`; this is why `step_eq_iff` takes
`u ∈ (0, 1]`. The event `u = 0` has probability zero, so the law is unaffected. -/
theorem step_zero {P : Fin n → Fin n → ℝ} (hP : ∀ i j, 0 ≤ P i j) (i : Fin n) :
    (step P i 0 : ℕ) = 0 := by
  have h0 : (⟨0, by have := i.isLt; omega⟩ : Fin n) ∈
      insert (lastState i) (univ.filter fun j : Fin n ↦ (0 : ℝ) ≤ cumProb P i (j + 1)) := by
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [← cumProb_zero P i]
    exact cumProb_mono hP i (Nat.zero_le _)
  have hle : step P i 0 ≤ ⟨0, by have := i.isLt; omega⟩ := Finset.min'_le _ _ h0
  rw [Fin.le_def] at hle
  exact Nat.le_zero.1 hle

/-- The inverse-CDF update is measurable in the uniform. -/
theorem measurable_step (P : Fin n → Fin n → ℝ) (i : Fin n) : Measurable (step P i) := by
  refine measurable_to_countable' fun j ↦ ?_
  refine Set.OrdConnected.measurableSet ⟨fun a ha b hb x hx ↦ ?_⟩
  have ha' : step P i a = j := ha
  have hb' : step P i b = j := hb
  change step P i x = j
  exact le_antisymm (hb' ▸ step_mono P i hx.2) (ha' ▸ step_mono P i hx.1)

/-- The preimage of `j` within `(0, 1]` is post #3's interval `(cs_{i,j-1}, cs_{ij}]`. -/
theorem step_preimage_inter_Ioc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    {u | step P i u = j} ∩ Set.Ioc 0 1 = Set.Ioc (cumProb P i j) (cumProb P i (j + 1)) := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨h, hu⟩
    exact (step_eq_iff hP i j hu).1 h
  · rintro ⟨h1, h2⟩
    have hu : u ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (cumProb_mem_Icc hP i j).1 h1, h2.trans (cumProb_mem_Icc hP i _).2⟩
    exact ⟨(step_eq_iff hP i j hu).2 ⟨h1, h2⟩, hu⟩

/-- **Key fact** (post #3): "the probability that [the uniform] falls in the interval
`(cs_{2,j-1}, cs_{2j}]` is exactly `p_{2j}`": `U[0,1){u : step P i u = j} = P i j`. -/
theorem uniformIco_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    uniformIco {u | step P i u = j} = ENNReal.ofReal (P i j) := by
  rw [uniformIco_eq_restrict_Ioc, Measure.restrict_apply' measurableSet_Ioc,
    step_preimage_inter_Ioc hP, Real.volume_Ioc, cumProb_succ, add_sub_cancel_left]

/-- **Key fact**, Lebesgue form: `volume {u ∈ [0,1) : step P i u = j} = P i j`. -/
theorem volume_step_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i j : Fin n) :
    volume ({u | step P i u = j} ∩ Set.Ico 0 1) = ENNReal.ofReal (P i j) := by
  rw [← uniformIco_step_eq hP i j, Measure.restrict_apply' measurableSet_Ico]

/-- **Post #3's worked example**: with `n = 3` and row `[0.2, 0.6, 0.2]` from the second state
(`1 : Fin 3`), the draw `u = 0.79` sends the chain to the second state, "because this is above
0.2 and below 0.8"; draws in `(0, 0.2]` go to the first state and draws in `(0.8, 1]` to the
third. -/
theorem step_post3_example {P : Fin 3 → Fin 3 → ℝ} (hP : IsStochastic P) (h0 : P 1 0 = 0.2)
    (h1 : P 1 1 = 0.6) (h2 : P 1 2 = 0.2) :
    step P 1 0.79 = 1 ∧ (∀ u ∈ Set.Ioc (0 : ℝ) 0.2, step P 1 u = 0) ∧
      (∀ u ∈ Set.Ioc (0.8 : ℝ) 1, step P 1 u = 2) := by
  have c0 : cumProb P 1 0 = 0 := cumProb_zero P 1
  have c1 : cumProb P 1 1 = 0.2 := by
    have : cumProb P 1 1 = cumProb P 1 0 + P 1 0 := cumProb_succ P 1 0
    change cumProb P 1 1 = 0.2
    rw [this, c0, h0, zero_add]
  have c2 : cumProb P 1 2 = 0.8 := by
    have : cumProb P 1 2 = cumProb P 1 1 + P 1 1 := cumProb_succ P 1 1
    change cumProb P 1 2 = 0.8
    rw [this, c1, h1]
    norm_num
  have c3 : cumProb P 1 3 = 1 := by
    have : cumProb P 1 3 = cumProb P 1 2 + P 1 2 := cumProb_succ P 1 2
    change cumProb P 1 3 = 1
    rw [this, c2, h2]
    norm_num
  refine ⟨?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
  · rw [step_eq_iff hP 1 1 ⟨by norm_num, by norm_num⟩]
    change cumProb P 1 1 < 0.79 ∧ 0.79 ≤ cumProb P 1 (1 + 1)
    rw [c1, c2]
    norm_num
  · rw [step_eq_iff hP 1 0 ⟨hu.1, hu.2.trans (by norm_num)⟩]
    change cumProb P 1 0 < u ∧ u ≤ cumProb P 1 (0 + 1)
    rw [c0, c1]
    exact hu
  · rw [step_eq_iff hP 1 2 ⟨lt_trans (by norm_num) hu.1, hu.2⟩]
    change cumProb P 1 2 < u ∧ u ≤ cumProb P 1 (2 + 1)
    rw [c2, c3]
    exact hu

/-! ### Paths driven by a sequence -/

variable {S : Type*}

/-- The path driven by a sequence `u` through an update rule `G` (post #3, "this sequence of
uniform random numbers 'driving' the Markov chain"): `x 0 = x₀`, `x (t+1) = G (x t) (u t)`. So
`u t` drives the transition from time `t` to `t + 1` (post #3's `u^t`, `x^{t+1}`, shifted to
start at `0`). -/
def drive {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : ℕ → S
  | 0 => x₀
  | t + 1 => G (drive G x₀ u t) (u t)

/-- The path driven by `u` from `x₀` with the inverse-CDF update `step P` (post #3's MC/QMC
simulation of the chain, depending on what `u` is). -/
noncomputable abbrev drivenPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (u : ℕ → ℝ) : ℕ → Fin n :=
  drive (step P) x₀ u

/-- `drive` starts at `x₀`. -/
theorem drive_zero {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) : drive G x₀ u 0 = x₀ :=
  rfl

/-- The recursion of `drive`. -/
theorem drive_succ {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (t : ℕ) :
    drive G x₀ u (t + 1) = G (drive G x₀ u t) (u t) :=
  rfl

/-- **Pathwise description of `drive`**: the driven path equals `s` at times `0, …, T` iff
`s 0 = x₀` and every transition `s t → s (t+1)`, `t < T`, is the update of `s t` by `u t`. -/
theorem drive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (u : ℕ → α) (s : ℕ → S) (T : ℕ) :
    (∀ t ≤ T, drive G x₀ u t = s t) ↔ s 0 = x₀ ∧ ∀ t < T, G (s t) (u t) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, drive_succ]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, drive_succ, hT T le_rfl, hs T (Nat.lt_succ_self T)]

/-! ### Counts -/

variable [DecidableEq S]

/-- **Occupation count** (the visit counter): `occCount path i T = #{t < T : path t = i}`, the
number of visits to `i` strictly before time `T` (times `0, …, T - 1`). -/
def occCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i).card

/-- **Transition count** `transCount path i j T = #{t < T : path t = i ∧ path (t+1) = j}`, the
number of transitions `i → j` among the first `T` transitions (times `0 → 1, …, T-1 → T`). -/
def transCount (path : ℕ → S) (i j : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ path t = i ∧ path (t + 1) = j).card

/-- No visits before time `0`. -/
theorem occCount_zero (path : ℕ → S) (i : S) : occCount path i 0 = 0 := rfl

/-- No transitions before time `0`. -/
theorem transCount_zero (path : ℕ → S) (i j : S) : transCount path i j 0 = 0 := rfl

/-- One more period adds one visit iff the path is in `i` at time `T`. -/
theorem occCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    occCount path i (T + 1) = occCount path i T + if path T = i then 1 else 0 := by
  unfold occCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i
  · simp only [h, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- One more transition adds one to `transCount i j` iff it is `i → j`. -/
theorem transCount_succ (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j (T + 1) =
      transCount path i j T + if path T = i ∧ path (T + 1) = j then 1 else 0 := by
  unfold transCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : path T = i ∧ path (T + 1) = j
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

/-- At most `T` visits before time `T`. -/
theorem occCount_le (path : ℕ → S) (i : S) (T : ℕ) : occCount path i T ≤ T :=
  (Finset.card_filter_le _ _).trans (Finset.card_range T).le

/-- The occupation count is monotone in the horizon. -/
theorem occCount_mono (path : ℕ → S) (i : S) {T T' : ℕ} (h : T ≤ T') :
    occCount path i T ≤ occCount path i T' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- `transCount i j ≤ occCount i`. -/
theorem transCount_le_occCount (path : ℕ → S) (i j : S) (T : ℕ) :
    transCount path i j T ≤ occCount path i T :=
  Finset.card_le_card fun t ht ↦ by
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩

/-- The occupation count before `T` depends only on the path before `T`. -/
theorem occCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t < T, p t = q t) (i : S) :
    occCount p i T = occCount q i T := by
  unfold occCount
  rw [Finset.filter_congr fun t ht ↦ by rw [h t (Finset.mem_range.1 ht)]]

/-- The first `T` transition counts depend only on the path up to time `T`. -/
theorem transCount_congr {p q : ℕ → S} {T : ℕ} (h : ∀ t ≤ T, p t = q t) (i j : S) :
    transCount p i j T = transCount q i j T := by
  unfold transCount
  refine congrArg _ (Finset.filter_congr fun t ht ↦ ?_)
  have ht' := Finset.mem_range.1 ht
  rw [h t ht'.le, h (t + 1) ht']

/-- Splitting the horizon: visits before `a + b` are those before `a` plus those of the shifted
path `t ↦ path (a + t)` before `b`. -/
theorem occCount_add (path : ℕ → S) (i : S) (a b : ℕ) :
    occCount path i (a + b) = occCount path i a + occCount (fun t ↦ path (a + t)) i b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, occCount_succ, ih, occCount_succ, add_assoc]

/-- Splitting the horizon for transition counts. -/
theorem transCount_add (path : ℕ → S) (i j : S) (a b : ℕ) :
    transCount path i j (a + b) =
      transCount path i j a + transCount (fun t ↦ path (a + t)) i j b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← add_assoc, transCount_succ, ih, transCount_succ, add_assoc]
    rfl

/-! ### Per-state stacks -/

/-- The **departure index** at time `t`: the number of earlier visits to the current state,
`#{t' < t : path t' = path t}`. The departure from `path t` at time `t` is the
`departureIndex`-th departure (counting from `0`) from that state. -/
def departureIndex (path : ℕ → S) (t : ℕ) : ℕ := occCount path (path t) t

/-- The departure index at time `t` depends only on the path up to time `t`. -/
theorem departureIndex_congr {p q : ℕ → S} {t : ℕ} (h : ∀ t' ≤ t, p t' = q t') :
    departureIndex p t = departureIndex q t := by
  unfold departureIndex
  rw [h t le_rfl]
  exact occCount_congr (fun t' ht' ↦ h t' ht'.le) _

/-- Later visits to the same state have larger departure indices; so the pairs
`(path t, departureIndex path t)` are distinct for distinct `t`. -/
theorem departureIndex_lt {path : ℕ → S} {t t' : ℕ} (htt' : t < t') (h : path t = path t') :
    departureIndex path t < departureIndex path t' := by
  unfold departureIndex
  rw [← h]
  have h1 := occCount_succ path (path t) t
  simp only [eq_self, ↓reduceIte] at h1
  have h2 := occCount_mono path (path t) (show t + 1 ≤ t' from htt')
  omega

/-- Injectivity of `t ↦ (path t, departureIndex path t)`. -/
theorem departureIndex_injective (path : ℕ → S) :
    Function.Injective fun t ↦ (path t, departureIndex path t) := by
  intro t t' h
  simp only [Prod.mk.injEq] at h
  rcases lt_trichotomy t t' with htt' | htt' | htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1).ne
  · exact htt'
  · exact absurd h.2 (departureIndex_lt htt' h.1.symm).ne'

/-- The state and the per-state departure counters of the stack representation. -/
def stackState {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) : ℕ → S × (S → ℕ)
  | 0 => (x₀, fun _ ↦ 0)
  | t + 1 =>
    let p := stackState G x₀ v t
    (G p.1 (v p.1 (p.2 p.1)), Function.update p.2 p.1 (p.2 p.1 + 1))

/-- **The stack representation** (post #3, "each state has its own stack … the `k`-th visit to
state `i` uses point `k` of stack `i`"): each state `i` has its own sequence `v i`, and the
`k`-th departure from `i` (`k = 0, 1, …`) is driven by `v i k` through the update `G`. -/
def stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) : S :=
  (stackState G x₀ v t).1

/-- The stack-driven chain with the inverse-CDF update. -/
noncomputable abbrev stackPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) :
    ℕ → Fin n :=
  stackDrive (step P) x₀ v

/-- The counters of `stackState` are the visit counts of the stack path. -/
theorem stackState_snd {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) (i : S) :
    (stackState G x₀ v t).2 i = occCount (stackDrive G x₀ v) i t := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [occCount_succ, ← ih]
    change Function.update (stackState G x₀ v t).2 (stackState G x₀ v t).1
      ((stackState G x₀ v t).2 (stackState G x₀ v t).1 + 1) i = _
    unfold stackDrive
    by_cases h : (stackState G x₀ v t).1 = i
    · subst h
      rw [Function.update_self]
      simp only [eq_self, ↓reduceIte]
    · rw [Function.update_of_ne (Ne.symm h)]
      simp only [h, ↓reduceIte, add_zero]

/-- `stackDrive` starts at `x₀`. -/
theorem stackDrive_zero {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) :
    stackDrive G x₀ v 0 = x₀ :=
  rfl

/-- **The stack recursion**: the transition at time `t` uses entry `departureIndex t` of the
stack of the current state. -/
theorem stackDrive_succ {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (t : ℕ) :
    stackDrive G x₀ v (t + 1) = G (stackDrive G x₀ v t)
      (v (stackDrive G x₀ v t) (departureIndex (stackDrive G x₀ v) t)) := by
  unfold departureIndex
  rw [← stackState_snd]
  rfl

/-- **Pathwise description of the stack representation**: the stack path equals `s` at times
`0, …, T` iff `s 0 = x₀` and each transition `s t → s (t+1)`, `t < T`, is the update of `s t`
by entry `departureIndex s t` of stack `s t`. -/
theorem stackDrive_eq_iff {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (s : ℕ → S)
    (T : ℕ) : (∀ t ≤ T, stackDrive G x₀ v t = s t) ↔
      s 0 = x₀ ∧ ∀ t < T, G (s t) (v (s t) (departureIndex s t)) = s (t + 1) := by
  induction T with
  | zero =>
    constructor
    · intro h
      exact ⟨(h 0 le_rfl).symm, fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨h0, -⟩ t ht
      rw [Nat.le_zero.1 ht]
      exact h0.symm
  | succ T ih =>
    constructor
    · intro h
      have hT := ih.1 fun t ht ↦ h t (ht.trans (Nat.le_succ T))
      refine ⟨hT.1, fun t ht ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · exact hT.2 t ht
      · rw [ht, ← h T (Nat.le_succ T), ← h (T + 1) le_rfl, stackDrive_succ,
          departureIndex_congr fun t' ht' ↦ h t' (ht'.trans (Nat.le_succ T))]
    · rintro ⟨h0, hs⟩ t ht
      have hT := ih.2 ⟨h0, fun t ht ↦ hs t (ht.trans (Nat.lt_succ_self T))⟩
      rcases Nat.le_succ_iff.1 ht with ht | ht
      · exact hT t ht
      · rw [ht, stackDrive_succ, hT T le_rfl, departureIndex_congr hT,
          hs T (Nat.lt_succ_self T)]

/-! ### Spells -/

/-- A **spell** (maximal run of equal states) starts at time `t` iff `t = 0` or the state
changes at `t`. -/
abbrev IsSpellStart (path : ℕ → S) (t : ℕ) : Prop := t = 0 ∨ path (t - 1) ≠ path t

/-- The **length of the run starting at `t`**, censored at the horizon `T`: the number of
`k < T - t` such that the path stays in `path t` throughout times `t, …, t + k`. For a spell
start `t`, this is the length of that spell (or of its part before `T`). -/
def runLength (path : ℕ → S) (t T : ℕ) : ℕ :=
  ((range (T - t)).filter fun k ↦ ∀ m ≤ k, path (t + m) = path t).card

/-- The number of spells in state `i` that start before `T`. -/
def spellCount (path : ℕ → S) (i : S) (T : ℕ) : ℕ :=
  ((range T).filter fun t ↦ IsSpellStart path t ∧ path t = i).card

/-- A run that stays exactly `k` periods and then leaves, before the horizon, has length `k`. -/
theorem runLength_eq_of_exit {path : ℕ → S} {t T k : ℕ} (hk : t + k < T)
    (hstay : ∀ m < k, path (t + m) = path t) (hexit : path (t + k) ≠ path t) :
    runLength path t T = k := by
  unfold runLength
  have : (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) = range k := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hm⟩
      by_contra hmk
      exact hexit (hm k (not_lt.1 hmk))
    · intro hmk
      exact ⟨by omega, fun m' hm' ↦ hstay m' (lt_of_le_of_lt hm' hmk)⟩
  rw [this, Finset.card_range]

/-- **Run lengths**: for `t + k < T`, the run starting at `t` has length `k` iff the path stays
in `path t` for times `t, …, t + k - 1` and leaves at `t + k`. -/
theorem runLength_eq_iff {path : ℕ → S} {t T k : ℕ} (hk : t + k < T) :
    runLength path t T = k ↔
      (∀ m < k, path (t + m) = path t) ∧ path (t + k) ≠ path t := by
  constructor
  · intro h
    by_cases hall : ∀ m ≤ k, path (t + m) = path t
    · exfalso
      have hsub : range (k + 1) ⊆
          (range (T - t)).filter (fun k ↦ ∀ m ≤ k, path (t + m) = path t) := by
        intro m hm
        rw [Finset.mem_range] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, fun m' hm' ↦ hall m' (by omega)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      unfold runLength at h
      omega
    · have hex : ∃ m, m ≤ k ∧ path (t + m) ≠ path t := by
        by_contra hne
        exact hall fun m hm ↦ by
          by_contra hm'
          exact hne ⟨m, hm, hm'⟩
      classical
      let m0 := Nat.find hex
      have hm0 : m0 ≤ k ∧ path (t + m0) ≠ path t := Nat.find_spec hex
      have hstay : ∀ m < m0, path (t + m) = path t := fun m hm ↦ by
        by_contra hne
        exact Nat.find_min hex hm ⟨by omega, hne⟩
      have := runLength_eq_of_exit (show t + m0 < T by omega) hstay hm0.2
      rw [h] at this
      rw [this]
      exact ⟨hstay, hm0.2⟩
  · rintro ⟨hstay, hexit⟩
    exact runLength_eq_of_exit hk hstay hexit

/-- One more period adds one spell of `i` iff a spell of `i` starts at time `T`. -/
theorem spellCount_succ (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      spellCount path i T + if IsSpellStart path T ∧ path T = i then 1 else 0 := by
  unfold spellCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : IsSpellStart path T ∧ path T = i
  · simp only [h, and_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hT
    exact lt_irrefl T (Finset.mem_range.1 (Finset.mem_filter.1 hT).1)
  · simp only [h, ↓reduceIte, add_zero]

variable [Fintype S]

/-- The occupation counts before `T` add up to `T`. -/
theorem sum_occCount (path : ℕ → S) (T : ℕ) : ∑ i, occCount path i T = T := by
  induction T with
  | zero => exact Finset.sum_const_zero
  | succ T ih =>
    simp only [occCount_succ]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]

/-- **Departures**: `Σ_j transCount i j T = occCount i T` (each visit before `T` is followed by
exactly one transition among the first `T`). -/
theorem sum_transCount_right (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path i j T = occCount path i T := by
  unfold transCount occCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t ↦ path (t + 1)) (t := univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.filter_filter]

/-- **Arrivals**: `Σ_j transCount j i T + 1{path 0 = i} = occCount i T + 1{path T = i}`. -/
theorem sum_transCount_left (path : ℕ → S) (i : S) (T : ℕ) :
    ∑ j, transCount path j i T + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
  induction T with
  | zero => rw [Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i, occCount_zero]
  | succ T ih =>
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib, occCount_succ]
    have h1 : ∑ j, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte]
    rw [h1]
    omega

/-- **Flow balance** (post #3, "every state is entered as often as it is left (allowing for
the first and last states)"): out-count minus in-count is `1{path 0 = i} − 1{path T = i}`. -/
theorem flowBalance (path : ℕ → S) (i : S) (T : ℕ) :
    (∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T =
      (if path 0 = i then 1 else 0) - if path T = i then 1 else 0 := by
  have h1 := sum_transCount_right path i T
  have h2 := sum_transCount_left path i T
  have h1' : (∑ j, transCount path i j T : ℤ) = occCount path i T := by exact_mod_cast h1
  have h2' : (∑ j, transCount path j i T : ℤ) + (if path 0 = i then 1 else 0) =
      occCount path i T + if path T = i then 1 else 0 := by
    have := congrArg (fun m : ℕ ↦ (m : ℤ)) h2
    push_cast [apply_ite (fun m : ℕ ↦ (m : ℤ))] at this
    exact this
  push_cast
  linarith

/-- **Flow balance**, bound form: `|Σ_j transCount i j − Σ_j transCount j i| ≤ 1`. -/
theorem abs_flowBalance_le (path : ℕ → S) (i : S) (T : ℕ) :
    |(∑ j, transCount path i j T : ℤ) - ∑ j, transCount path j i T| ≤ 1 := by
  rw [flowBalance]
  split_ifs <;> norm_num

/-- All transition counts add up to the number of transitions `T`. -/
theorem sum_sum_transCount (path : ℕ → S) (T : ℕ) : ∑ i, ∑ j, transCount path i j T = T := by
  simp only [sum_transCount_right]
  exact sum_occCount path T

/-- **Spells are entries**: the spells of `i` starting at times `0, …, T` are the start (if
`path 0 = i`) plus the entries `j → i`, `j ≠ i`, among the first `T` transitions. -/
theorem spellCount_succ_eq (path : ℕ → S) (i : S) (T : ℕ) :
    spellCount path i (T + 1) =
      (if path 0 = i then 1 else 0) + ∑ j ∈ univ.erase i, transCount path j i T := by
  induction T with
  | zero =>
    rw [spellCount_succ, Finset.sum_eq_zero fun j _ ↦ transCount_zero path j i]
    have h0 : IsSpellStart path 0 := Or.inl rfl
    simp only [h0, true_and]
    change 0 + _ = _ + 0
    rw [zero_add, add_zero]
  | succ T ih =>
    rw [spellCount_succ, ih]
    simp only [transCount_succ]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ j ∈ univ.erase i, (if path T = j ∧ path (T + 1) = i then 1 else 0) =
        if path T ≠ i ∧ path (T + 1) = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_eq]
      by_cases h : path T = i
      · simp only [h, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      · simp only [h, Finset.mem_erase, ne_eq, not_false_eq_true, Finset.mem_univ, and_self,
          ↓reduceIte]
    rw [h1]
    have h2 : (IsSpellStart path (T + 1) ∧ path (T + 1) = i) ↔
        (path T ≠ i ∧ path (T + 1) = i) := by
      unfold IsSpellStart
      rw [Nat.add_sub_cancel]
      constructor
      · rintro ⟨h | h, hi⟩
        · exact absurd h (Nat.succ_ne_zero T)
        · exact ⟨hi ▸ h, hi⟩
      · rintro ⟨h, hi⟩
        exact ⟨Or.inr (hi ▸ h), hi⟩
    rw [if_congr h2 rfl rfl]
    omega

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The discrepancy-to-occupation inequality (post #3)

Copied from `RQMCMarkov/MarkovDriving` (namespace and imports renamed).

Post #3 ranks the ways of driving a chain by how fast the occupation frequencies `N_s(T)/T` and
the empirical transition matrix converge: MC at `O(1/√T)`, per-state low-discrepancy stacks
"faster than `O(1/√T)`" (`O(log T / T)`), rotors at `O(1/T)`. All three rates come from one
**deterministic** inequality, valid for *any* path `x : ℕ → S`, proved here by telescoping
Poisson's equation (Meyn and Tweedie, Ch. 17; Holroyd and Propp 2010 use the same device).

For a test function `g`, the **departure discrepancy** of state `i` up to time `T` is
`D_i(g, T) = Σ_{t < T, x t = i} (g(x_{t+1}) − (Pg)(i))`: the error of the departures from `i`
as a sample of the row `P(i, ·)`. If `h − Ph = f − c` then

`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`        (`sum_sub_eq_boundary_add`),

so for `f = 1_{s}` and `c = π_s` (`occCount_sub_eq_boundary_add`, `abs_occCount_sub_le`):

`|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i |D_i(h, T)|`  (occupation error ≤ boundary + departure
discrepancies).

The transition counts satisfy the exact identity `N_ij(T) − p_ij N_i(T) = D_i(1_{j}, T)`
(`transCount_sub_eq_departureDiscrepancy`), and hence (`abs_transCount_sub_le`)
`|N_ij(T) − T π_i p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2‖h‖∞ + Σ_k |D_k(h, T)|)`.

For a path built from per-state stacks (`stackDrive`, which covers the QMC stacks of post #3
and the rotor-router), the departures from `i` are the first `N_i(T)` entries of stack `i`
(`sum_filter_occCount_eq`, `departureDiscrepancy_stackDrive`, `transCount_stackDrive`), so the
departure discrepancy is an ordinary one-dimensional sampling error, bounded in `StackBound`
(van der Corput stacks), `RotorRouter` (rotors) and `MCRate` (i.i.d. stacks).

The sup-norm `‖h‖∞` enters through any bound `M` with `∀ i, |h i| ≤ M`.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **departure discrepancy** of state `i` for the test function `g` up to time `T`:
`Σ_{t < T, x t = i} (g (x (t+1)) − (Pg)(i))`. -/
noncomputable def departureDiscrepancy (P : Matrix S S ℝ) (g : S → ℝ) (x : ℕ → S) (i : S)
    (T : ℕ) : ℝ :=
  ∑ t ∈ (range T).filter (fun t => x t = i), (g (x (t + 1)) - (P *ᵥ g) i)

/-- **The telescoping identity.** If `h − Ph = f − c`, then along any path
`Σ_{t<T} f(x_t) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem sum_sub_eq_boundary_add (P : Matrix S S ℝ) {f h : S → ℝ} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = f i - c) (x : ℕ → S) (T : ℕ) :
    ∑ t ∈ range T, f (x t) - T * c =
      h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  have e1 : ∑ t ∈ range T, f (x t) - T * c = ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) := by
    rw [← card_range T, ← nsmul_eq_mul, ← sum_const, card_range, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => (hh (x t)).symm
  have e2 : ∑ t ∈ range T, (h (x t) - (P *ᵥ h) (x t)) =
      ∑ t ∈ range T, (h (x t) - h (x (t + 1))) +
        ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  have e3 : ∑ t ∈ range T, (h (x (t + 1)) - (P *ᵥ h) (x t)) =
      ∑ i, departureDiscrepancy P h x i T := by
    rw [← sum_fiberwise (range T) x]
    refine sum_congr rfl fun i _ => sum_congr rfl fun t ht => ?_
    rw [(mem_filter.1 ht).2]
  rw [e1, e2, e3, sum_range_sub' (fun t => h (x t)) T]

omit [Fintype S] in
/-- `Σ_{t<T} 1_{s}(x_t) = N_s(T)`. -/
theorem sum_indicator_eq_occCount (x : ℕ → S) (s : S) (T : ℕ) :
    ∑ t ∈ range T, (if x t = s then (1 : ℝ) else 0) = occCount x s T := by
  rw [sum_boole]
  rfl

/-- **Occupation identity.** If `h − Ph = 1_{s} − c` (Poisson's equation, with `c = π_s`), then
along any path `N_s(T) − T c = h(x_0) − h(x_T) + Σ_i D_i(h, T)`. -/
theorem occCount_sub_eq_boundary_add (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (x : ℕ → S) (T : ℕ) :
    (occCount x s T : ℝ) - T * c = h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T := by
  rw [← sum_indicator_eq_occCount]
  exact sum_sub_eq_boundary_add P hh x T

/-- **The discrepancy-to-occupation inequality** (the backbone of post #3's rates): for any path,
`|N_s(T) − T c| ≤ 2M + Σ_i |D_i(h, T)|`, where `h − Ph = 1_{s} − c` and `|h| ≤ M`. -/
theorem abs_occCount_sub_le (P : Matrix S S ℝ) {h : S → ℝ} {s : S} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (x : ℕ → S) (T : ℕ) :
    |(occCount x s T : ℝ) - T * c| ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| := by
  rw [occCount_sub_eq_boundary_add P hh x T]
  have hb : |h (x 0) - h (x T)| ≤ 2 * M := by
    have := abs_sub (h (x 0)) (h (x T))
    linarith [hM (x 0), hM (x T)]
  calc |h (x 0) - h (x T) + ∑ i, departureDiscrepancy P h x i T|
      ≤ |h (x 0) - h (x T)| + |∑ i, departureDiscrepancy P h x i T| := abs_add_le _ _
    _ ≤ 2 * M + ∑ i, |departureDiscrepancy P h x i T| :=
        add_le_add hb (abs_sum_le_sum_abs _ _)

/-- `(P 1_{j})(i) = P i j`. -/
theorem mulVec_indicator (P : Matrix S S ℝ) (i j : S) :
    (P *ᵥ fun k => if k = j then (1 : ℝ) else 0) i = P i j := by
  simp only [mulVec, dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ,
    ite_true]

/-- **Transition identity.** `N_ij(T) − p_ij N_i(T)` is exactly the departure discrepancy of `i`
for the indicator `1_{j}`. -/
theorem transCount_sub_eq_departureDiscrepancy (P : Matrix S S ℝ) (x : ℕ → S) (i j : S)
    (T : ℕ) : (transCount x i j T : ℝ) - P i j * occCount x i T =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T := by
  unfold departureDiscrepancy
  rw [mulVec_indicator, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm (P i j), sum_boole,
    filter_filter]
  rfl

/-- **Transition counts against the target `T π_i p_ij`** (post #3's "number of each
transition"): `|N_ij(T) − T c p_ij| ≤ |D_i(1_{j}, T)| + p_ij (2M + Σ_k |D_k(h, T)|)`, where
`h − Ph = 1_{i} − c` and `|h| ≤ M`. -/
theorem abs_transCount_sub_le (P : Matrix S S ℝ) (hP0 : ∀ i j, 0 ≤ P i j) {h : S → ℝ} {i : S}
    {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c) (hM : ∀ k, |h k| ≤ M)
    (x : ℕ → S) (j : S) (T : ℕ) :
    |(transCount x i j T : ℝ) - T * c * P i j| ≤
      |departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T| +
        P i j * (2 * M + ∑ k, |departureDiscrepancy P h x k T|) := by
  have e : (transCount x i j T : ℝ) - T * c * P i j =
      departureDiscrepancy P (fun k => if k = j then 1 else 0) x i T +
        P i j * ((occCount x i T : ℝ) - T * c) := by
    rw [← transCount_sub_eq_departureDiscrepancy]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg (hP0 i j)]
  exact mul_le_mul_of_nonneg_left (abs_occCount_sub_le P hh hM x T) (hP0 i j)

omit [Fintype S] in
/-- **Departures are read off in order.** Summing over the visits `t < T` to `i` a function of
the visit index `N_i(t)` is summing over the first `N_i(T)` indices. -/
theorem sum_filter_occCount_eq {R : Type*} [AddCommMonoid R] (x : ℕ → S) (i : S) (φ : ℕ → R)
    (T : ℕ) : ∑ t ∈ (range T).filter (fun t => x t = i), φ (occCount x i t) =
      ∑ k ∈ range (occCount x i T), φ k := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [range_add_one, filter_insert, occCount_succ]
    by_cases hT : x T = i
    · have hnot : T ∉ (range T).filter (fun t => x t = i) := fun hm =>
        lt_irrefl T (mem_range.1 (mem_filter.1 hm).1)
      simp only [hT, ite_true]
      rw [sum_insert hnot, ih, sum_range_succ, add_comm]
    · simp only [hT, ite_false, add_zero]
      exact ih

omit [Fintype S] in
/-- In a stack path, the `t`-th transition out of `i` uses entry `N_i(t)` of stack `i`. -/
theorem stackDrive_succ_of_eq {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) {i : S}
    {t : ℕ} (ht : stackDrive G x₀ v t = i) :
    stackDrive G x₀ v (t + 1) = G i (v i (occCount (stackDrive G x₀ v) i t)) := by
  rw [stackDrive_succ]
  unfold departureIndex
  rw [ht]

/-- **Departure discrepancy of a stack path**: the departures from `i` up to `T` are
`G i (v i k)`, `k < N_i(T)`, so `D_i(g, T) = Σ_{k < N_i(T)} (g(G i (v i k)) − (Pg)(i))`. -/
theorem departureDiscrepancy_stackDrive {α : Type*} (P : Matrix S S ℝ) (g : S → ℝ)
    (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i : S) (T : ℕ) :
    departureDiscrepancy P g (stackDrive G x₀ v) i T =
      ∑ k ∈ range (occCount (stackDrive G x₀ v) i T), (g (G i (v i k)) - (P *ᵥ g) i) := by
  unfold departureDiscrepancy
  rw [← sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => g (G i (v i k)) - (P *ᵥ g) i) T]
  refine sum_congr rfl fun t ht => ?_
  rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]

omit [Fintype S] in
/-- **Transition counts of a stack path**: `N_ij(T) = #{k < N_i(T) : G i (v i k) = j}`. -/
theorem transCount_stackDrive {α : Type*} (G : S → α → S) (x₀ : S) (v : S → ℕ → α) (i j : S)
    (T : ℕ) : transCount (stackDrive G x₀ v) i j T =
      ((range (occCount (stackDrive G x₀ v) i T)).filter fun k => G i (v i k) = j).card := by
  have h1 := sum_filter_occCount_eq (stackDrive G x₀ v) i
    (fun k => if G i (v i k) = j then 1 else 0) T
  simp only [sum_boole, Nat.cast_id] at h1
  have h2 : ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if G i (v i (occCount (stackDrive G x₀ v) i t)) = j then 1 else 0) =
      ∑ t ∈ (range T).filter (fun t => stackDrive G x₀ v t = i),
      (if stackDrive G x₀ v (t + 1) = j then (1 : ℕ) else 0) :=
    sum_congr rfl fun t ht => by rw [stackDrive_succ_of_eq G x₀ v (mem_filter.1 ht).2]
  simp only [sum_boole, Nat.cast_id, filter_filter] at h2
  unfold transCount
  rw [← h1, ← h2, filter_filter]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Discrepancy of finite point sets in `[0,1)`

Copied from `RQMCMarkov/MarkovDriving` (from `RQMCMarkov/PointSets`); see that project for
its documentation.

Posts #1-#2 of the VFI Toolkit discourse topic 687 call a point set *low-discrepancy* when the
discrepancy between its empirical distribution and `Uniform(0,1)` falls faster than `n^{-1/2}`.
This module fixes the one-dimensional definitions (Niederreiter 1992, Ch. 2; L'Ecuyer 2016).

**Representation.** A point set of size `n` is the first `n` terms `x 0, …, x (n-1)` of a
sequence `x : ℕ → ℝ`. Sequences (van der Corput) and finite sets (the midpoint rule) then share
one type, and blocks of consecutive terms are `Finset.range` shifts. The hypothesis that the
points lie in `[0,1)` is `InUnitIco x n`. A family `y : Fin n → ℝ` can be used through
`fun i => if h : i < n then y ⟨i, h⟩ else 0`.

**Definitions.**
* `countBelow x n t = #{i < n : x i < t}`, and `countAtMost x n t = #{i < n : x i ≤ t}`;
* `localDiscrepancy x n t = |#{i < n : x i < t}/n - t|`;
* `starDiscrepancy x n = D*ₙ = sup_{t ∈ [0,1]} localDiscrepancy x n t`;
* `qmcEstimate f x n = (1/n) ∑_{i<n} f (x i)`, the QMC estimator of post #1;
* `midpointRule n i = (2i+1)/(2n)`, the stratification QMC point set of post #2.

**Results.**
* `starDiscrepancy_nonneg`, `starDiscrepancy_le_one`: `0 ≤ D*ₙ ≤ 1`.
* `countAtMost_div_sub_le_starDiscrepancy`: the right limits of the local discrepancy are also
  bounded by `D*ₙ`.
* `inv_two_mul_le_starDiscrepancy`: every `n`-point set in `[0,1)` has `D*ₙ ≥ 1/(2n)`. No point
  set does better than order `1/n` (post #1's "faster than `n^{-1/2}`" is at most `n^{-1}`).
* `starDiscrepancy_midpointRule`: the midpoint rule has `D*ₙ = 1/(2n)` exactly, so it is an
  optimal point set (`starDiscrepancy_midpointRule_le`); for `n = 3` it is post #2's
  `{1/6, 1/2, 5/6}` with `D*₃ = 1/6` (`midpointRule_three`, `starDiscrepancy_midpointRule_three`).
-/

namespace RQMCMarkov.ScrambledStacks

open Finset

/-- The first `n` terms of `x` lie in `[0,1)`. -/
def InUnitIco (x : ℕ → ℝ) (n : ℕ) : Prop := ∀ i < n, x i ∈ Set.Ico (0 : ℝ) 1

/-- The number of the first `n` points that lie strictly below `t`: `#{i < n : x i < t}`. -/
noncomputable def countBelow (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range n).filter (fun i => x i < t)).card

/-- The number of the first `n` points that lie at or below `t`: `#{i < n : x i ≤ t}`. -/
noncomputable def countAtMost (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range n).filter (fun i => x i ≤ t)).card

/-- The local discrepancy at `t`: `|#{i < n : x i < t}/n - t|`, the gap between the empirical
distribution function of the first `n` points and the uniform one at `t`. -/
noncomputable def localDiscrepancy (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  |(countBelow x n t : ℝ) / n - t|

/-- The star discrepancy `D*ₙ = sup_{t ∈ [0,1]} |#{i < n : x i < t}/n - t|`. -/
noncomputable def starDiscrepancy (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) 1, localDiscrepancy x n t

/-- The QMC estimator `(1/n) ∑_{i<n} f (x i)` of `∫₀¹ f` (post #1). -/
noncomputable def qmcEstimate (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, f (x i)) / n

/-- The midpoint rule `xᵢ = (2i+1)/(2n)`: the midpoints of the `n` equal strata of `[0,1)`
(post #2's stratification QMC set). -/
noncomputable def midpointRule (n : ℕ) : ℕ → ℝ := fun i => (2 * i + 1) / (2 * n)

/-- At most `n` of the first `n` points lie below `t`. -/
theorem countBelow_le (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : countBelow x n t ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- The counting function is monotone in `t`. -/
theorem countBelow_mono (x : ℕ → ℝ) (n : ℕ) {s t : ℝ} (h : s ≤ t) :
    countBelow x n s ≤ countBelow x n t := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

/-- The empirical distribution function `#{i < n : x i < t}/n` lies in `[0,1]`. -/
theorem countBelow_div_mem_Icc (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countBelow x n t : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast countBelow_le x n t

/-- The local discrepancy at a point of `[0,1]` is at most `1`. -/
theorem localDiscrepancy_le_one (x : ℕ → ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localDiscrepancy x n t ≤ 1 := by
  have h := countBelow_div_mem_Icc x n t
  exact abs_sub_le_iff.mpr ⟨by linarith [h.2, ht.1], by linarith [h.1, ht.2]⟩

/-- For `n ≠ 0` the local discrepancy is `|#{i < n : x i < t} - n t| / n`. -/
theorem localDiscrepancy_eq_abs_div (x : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    localDiscrepancy x n t = |(countBelow x n t : ℝ) - n * t| / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by positivity
  unfold localDiscrepancy
  rw [show (countBelow x n t : ℝ) / n - t = ((countBelow x n t : ℝ) - n * t) / n by
    rw [sub_div, mul_div_cancel_left₀ _ hn0], abs_div, abs_of_pos hpos]

/-- The local discrepancies over `t ∈ [0,1]` are bounded above (by `1`). -/
theorem bddAbove_localDiscrepancy (x : ℕ → ℝ) (n : ℕ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 => localDiscrepancy x n t) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact localDiscrepancy_le_one x n t.2

/-- Each local discrepancy at `t ∈ [0,1]` is at most the star discrepancy. -/
theorem localDiscrepancy_le_starDiscrepancy (x : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : localDiscrepancy x n t ≤ starDiscrepancy x n :=
  le_ciSup (bddAbove_localDiscrepancy x n) (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1)

/-- A uniform bound on the local discrepancies over `[0,1]` bounds the star discrepancy. -/
theorem starDiscrepancy_le_of_forall (x : ℕ → ℝ) (n : ℕ) {c : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, localDiscrepancy x n t ≤ c) : starDiscrepancy x n ≤ c := by
  have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩
  exact ciSup_le fun t => h t t.2

/-- `0 ≤ D*ₙ`. -/
theorem starDiscrepancy_nonneg (x : ℕ → ℝ) (n : ℕ) : 0 ≤ starDiscrepancy x n :=
  (abs_nonneg _).trans
    (localDiscrepancy_le_starDiscrepancy x n (Set.left_mem_Icc.mpr zero_le_one))

/-- `D*ₙ ≤ 1`. -/
theorem starDiscrepancy_le_one (x : ℕ → ℝ) (n : ℕ) : starDiscrepancy x n ≤ 1 :=
  starDiscrepancy_le_of_forall x n fun _ ht => localDiscrepancy_le_one x n ht

/-- The right limits of the local discrepancy are bounded by `D*ₙ` too: for `a ∈ [0,1)`,
`#{i < n : x i ≤ a}/n - a ≤ D*ₙ`. -/
theorem countAtMost_div_sub_le_starDiscrepancy (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) : (countAtMost x n a : ℝ) / n - a ≤ starDiscrepancy x n := by
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  have hδpos : 0 < min ε (1 - a) := lt_min hε (by linarith)
  have hδε : min ε (1 - a) ≤ ε := min_le_left _ _
  have hδa : min ε (1 - a) ≤ 1 - a := min_le_right _ _
  have hmem : a + min ε (1 - a) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hloc := localDiscrepancy_le_starDiscrepancy x n hmem
  have hcount : countAtMost x n a ≤ countBelow x n (a + min ε (1 - a)) := by
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by linarith [hi.2]⟩
  have hc : (countAtMost x n a : ℝ) / n ≤ (countBelow x n (a + min ε (1 - a)) : ℝ) / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg n)
  have h1 : (countBelow x n (a + min ε (1 - a)) : ℝ) / n - (a + min ε (1 - a)) ≤
      localDiscrepancy x n (a + min ε (1 - a)) := le_abs_self _
  linarith

/-- **Lower bound.** Every set of `n ≥ 1` points in `[0,1)` has star discrepancy at least
`1/(2n)`. -/
theorem inv_two_mul_le_starDiscrepancy {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    1 / (2 * n) ≤ starDiscrepancy x n := by
  have h0 := hx 0 hn
  have hlow : x 0 - (countBelow x n (x 0) : ℝ) / n ≤ starDiscrepancy x n := by
    have h1 := neg_le_abs ((countBelow x n (x 0) : ℝ) / n - x 0)
    have h2 := localDiscrepancy_le_starDiscrepancy x n (Set.Ico_subset_Icc_self h0)
    unfold localDiscrepancy at h2
    linarith
  have hup := countAtMost_div_sub_le_starDiscrepancy x n h0.1 h0.2
  have hcnt : countBelow x n (x 0) + 1 ≤ countAtMost x n (x 0) := by
    have hnot : (0 : ℕ) ∉ (Finset.range n).filter (fun i => x i < x 0) := by
      intro h
      rw [Finset.mem_filter] at h
      exact lt_irrefl _ h.2
    unfold countBelow countAtMost
    rw [← Finset.card_insert_of_notMem hnot]
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_insert] at hi
    rw [Finset.mem_filter]
    rcases hi with rfl | hi
    · exact ⟨Finset.mem_range.mpr hn, le_refl _⟩
    · rw [Finset.mem_filter] at hi
      exact ⟨hi.1, hi.2.le⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcntR : (countBelow x n (x 0) : ℝ) + 1 ≤ countAtMost x n (x 0) := by exact_mod_cast hcnt
  have hdiff : 1 / (n : ℝ) ≤ (countAtMost x n (x 0) : ℝ) / n - (countBelow x n (x 0) : ℝ) / n := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  rw [show (1 : ℝ) / (2 * n) = (1 / n) / 2 by rw [div_div, mul_comm]]
  linarith

/-- The midpoint-rule points lie in `[0,1)`. -/
theorem midpointRule_mem (n : ℕ) : InUnitIco (midpointRule n) n := by
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  have hpos : (0 : ℝ) < 2 * n := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  change (0 : ℝ) ≤ (2 * i + 1) / (2 * n) ∧ (2 * (i : ℝ) + 1) / (2 * n) < 1
  refine ⟨div_nonneg (by positivity) hpos.le, ?_⟩
  rw [div_lt_one hpos]
  linarith

/-- A midpoint-rule point lies below `t` iff `2i + 1 < 2nt`. -/
theorem midpointRule_lt_iff {n : ℕ} (hn : 0 < n) (i : ℕ) (t : ℝ) :
    midpointRule n i < t ↔ 2 * (i : ℝ) + 1 < 2 * n * t := by
  have hpos : (0 : ℝ) < 2 * n := by positivity
  unfold midpointRule
  rw [div_lt_iff₀ hpos, mul_comm t]

/-- Upper bound on the midpoint-rule count: if `2nt ≤ 2m + 1` then at most `m` points lie
below `t`. -/
theorem countBelow_midpointRule_le {n : ℕ} (hn : 0 < n) {t : ℝ} {m : ℕ}
    (h : 2 * n * t ≤ 2 * (m : ℝ) + 1) : countBelow (midpointRule n) n t ≤ m := by
  calc countBelow (midpointRule n) n t ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter, midpointRule_lt_iff hn] at hi
        rw [Finset.mem_range]
        have : (i : ℝ) < m := by linarith [hi.2]
        exact_mod_cast this
    _ = m := Finset.card_range m

/-- Lower bound on the midpoint-rule count: if `m ≤ n` and `m < nt + 1/2` then at least `m`
points lie below `t`. -/
theorem le_countBelow_midpointRule {n : ℕ} (hn : 0 < n) {t : ℝ} {m : ℕ} (hmn : m ≤ n)
    (h : (m : ℝ) < n * t + 1 / 2) : m ≤ countBelow (midpointRule n) n t := by
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ countBelow (midpointRule n) n t := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, midpointRule_lt_iff hn, Finset.mem_range]
        have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
        exact ⟨lt_of_lt_of_le hi hmn, by linarith⟩

/-- The midpoint rule satisfies `|#{i < n : xᵢ < t} - nt| ≤ 1/2` for every `t ∈ [0,1]`. -/
theorem abs_countBelow_midpointRule_sub_le {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow (midpointRule n) n t : ℝ) - n * t| ≤ 1 / 2 := by
  have hn0 : (0 : ℝ) ≤ n * t := mul_nonneg (Nat.cast_nonneg n) ht.1
  have hnt : (n : ℝ) * t ≤ n := by
    have := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
    linarith
  -- upper bound: `m = ⌊nt + 1/2⌋₊`
  have hA : (countBelow (midpointRule n) n t : ℝ) ≤ n * t + 1 / 2 := by
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ n * t + 1 / 2 by linarith)
    have hlt := Nat.lt_floor_add_one (n * t + 1 / 2 : ℝ)
    have hc := countBelow_midpointRule_le hn (m := ⌊(n : ℝ) * t + 1 / 2⌋₊) (t := t)
      (by linarith)
    have hc' : (countBelow (midpointRule n) n t : ℝ) ≤ ⌊(n : ℝ) * t + 1 / 2⌋₊ := by
      exact_mod_cast hc
    linarith
  -- lower bound: `m = ⌈nt - 1/2⌉₊`
  have hB : n * t - 1 / 2 ≤ (countBelow (midpointRule n) n t : ℝ) := by
    have hmn : ⌈(n : ℝ) * t - 1 / 2⌉₊ ≤ n := Nat.ceil_le.mpr (by linarith)
    have hlt : (⌈(n : ℝ) * t - 1 / 2⌉₊ : ℝ) < n * t + 1 / 2 := by
      rcases le_or_gt 0 ((n : ℝ) * t - 1 / 2) with h | h
      · have := Nat.ceil_lt_add_one h
        linarith
      · rw [Nat.ceil_eq_zero.mpr h.le, Nat.cast_zero]
        linarith
    have hc := le_countBelow_midpointRule hn hmn hlt
    have hc' : (⌈(n : ℝ) * t - 1 / 2⌉₊ : ℝ) ≤ countBelow (midpointRule n) n t := by
      exact_mod_cast hc
    linarith [Nat.le_ceil ((n : ℝ) * t - 1 / 2)]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **The midpoint rule has star discrepancy exactly `1/(2n)`** (post #2's stratification QMC
point set). -/
theorem starDiscrepancy_midpointRule {n : ℕ} (hn : 0 < n) :
    starDiscrepancy (midpointRule n) n = 1 / (2 * n) := by
  apply le_antisymm _ (inv_two_mul_le_starDiscrepancy (midpointRule_mem n) hn)
  apply starDiscrepancy_le_of_forall
  intro t ht
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [localDiscrepancy_eq_abs_div _ hn.ne' t,
    show (1 : ℝ) / (2 * n) = (1 / 2) / n by rw [div_div]]
  exact div_le_div_of_nonneg_right (abs_countBelow_midpointRule_sub_le hn ht) hpos.le

/-- The midpoint rule is an optimal `n`-point set: no point set in `[0,1)` has smaller star
discrepancy. -/
theorem starDiscrepancy_midpointRule_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    starDiscrepancy (midpointRule n) n ≤ starDiscrepancy x n := by
  rw [starDiscrepancy_midpointRule hn]
  exact inv_two_mul_le_starDiscrepancy hx hn

/-- For `n = 3` the midpoint rule is post #2's set `{1/6, 1/2, 5/6}`. -/
theorem midpointRule_three :
    midpointRule 3 0 = 1 / 6 ∧ midpointRule 3 1 = 1 / 2 ∧ midpointRule 3 2 = 5 / 6 := by
  unfold midpointRule
  norm_num

/-- Post #2's stratification set `{1/6, 1/2, 5/6}` has star discrepancy `1/6`. -/
theorem starDiscrepancy_midpointRule_three : starDiscrepancy (midpointRule 3) 3 = 1 / 6 := by
  rw [starDiscrepancy_midpointRule (by norm_num)]
  norm_num

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Koksma's inequality in one dimension

Copied from `RQMCMarkov/MarkovDriving` (from `RQMCMarkov/PointSets`); see that project for
its documentation.

Post #1 says QMC beats MC when the discrepancy of the point set falls faster than `n^{-1/2}`.
The link between discrepancy and integration error is Koksma's inequality (Koksma 1942;
Niederreiter 1992, Thm 2.9; L'Ecuyer 2016):
`|(1/n) ∑_{i<n} f(xᵢ) - ∫₀¹ f| ≤ V(f) D*ₙ` for `f` of bounded variation on `[0,1]`.

**Results.**
* `abs_sum_indicator_upperSet_sub_le`: for every upper set `U ⊆ ℝ`, the empirical measure of
  `U` and its Lebesgue measure in `(0,1]` differ by at most `D*ₙ`.
* `koksma_monotone`, `koksma_monotoneOn`: Koksma's inequality for monotone `f`, with
  `V(f) = f 1 - f 0`. The proof is the layer-cake formula on both sides
  (`Integrable.integral_eq_integral_Ioc_meas_le` for the Lebesgue side).
* `koksma_sub_monotoneOn`: for `f = p - q` with `p, q` monotone on `[0,1]`, the bound is
  `((p 1 - p 0) + (q 1 - q 0)) D*ₙ`.
* `koksma_boundedVariationOn`: **Koksma's inequality** for `f` of bounded variation on `[0,1]`,
  with `V(f) = totalVariation f = (eVariationOn f [0,1]).toReal`, via the Jordan decomposition
  into positive and negative variations (`variationOnFromTo.add_self_monotoneOn`,
  `variationOnFromTo.sub_self_monotoneOn`).
* `koksma_hasDerivAt`: the `C¹` corollary, with `V(f)` replaced by `∫₀¹ |f'|`, for `f`
  differentiable on `[0,1]` with integrable derivative (proved through the decomposition
  `f = (f 0 + ∫₀ˣ f'⁺) - ∫₀ˣ f'⁻`), and `totalVariation_le_integral_abs_deriv`:
  `V(f) ≤ ∫₀¹ |f'|` (only this inequality is needed for the bound; equality also holds
  classically but is not formalised).

The hypothesis `0 < n` is needed: for `n = 0` the estimator is `0` while `D*₀ = 1`, and the
inequality fails for constant `f ≠ 0`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory

/-- The total variation `V(f)` of `f` on `[0,1]`, as a real number (the extended-real
`eVariationOn f [0,1]` converted with `toReal`, so `0` when the variation is infinite). -/
noncomputable def totalVariation (f : ℝ → ℝ) : ℝ := (eVariationOn f (Set.Icc 0 1)).toReal

/-- The counting function as a sum of indicators: `#{i < n : x i < t} = ∑ 1_{(-∞,t)}(x i)`. -/
theorem countBelow_eq_sum_indicator (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countBelow x n t : ℝ) = ∑ i ∈ Finset.range n, (Set.Iio t).indicator 1 (x i) := by
  unfold countBelow
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_ite]
  split_ifs with h
  · rw [Set.indicator_of_mem (show x i ∈ Set.Iio t from h), Nat.cast_one, Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x i ∉ Set.Iio t from h), Nat.cast_zero]

/-- The closed counting function as a sum of indicators: `#{i < n : x i ≤ t}`. -/
theorem countAtMost_eq_sum_indicator (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (countAtMost x n t : ℝ) = ∑ i ∈ Finset.range n, (Set.Iic t).indicator 1 (x i) := by
  unfold countAtMost
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_ite]
  split_ifs with h
  · rw [Set.indicator_of_mem (show x i ∈ Set.Iic t from h), Nat.cast_one, Pi.one_apply]
  · rw [Set.indicator_of_notMem (show x i ∉ Set.Iic t from h), Nat.cast_zero]

/-- At most `n` of the first `n` points lie at or below `t`. -/
theorem countAtMost_le (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : countAtMost x n t ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

/-- The right-limit bound `#{i < n : x i ≤ a}/n - a ≤ D*ₙ` holds on all of `[0,1]`. -/
theorem countAtMost_div_sub_le_starDiscrepancy_of_mem (x : ℕ → ℝ) (n : ℕ) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : (countAtMost x n a : ℝ) / n - a ≤ starDiscrepancy x n := by
  rcases ha.2.lt_or_eq with h | h
  · exact countAtMost_div_sub_le_starDiscrepancy x n ha.1 h
  · have hle : (countAtMost x n a : ℝ) / n ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, Nat.cast_zero, div_zero]
        exact zero_le_one
      · rw [div_le_one (by exact_mod_cast hn)]
        exact_mod_cast countAtMost_le x n a
    linarith [starDiscrepancy_nonneg x n]

/-- An indicator with value `1` takes values in `[0,1]`. -/
theorem indicator_one_mem_Icc (U : Set ℝ) (y : ℝ) :
    U.indicator (1 : ℝ → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : y ∈ U
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact ⟨zero_le_one, le_refl 1⟩
  · rw [Set.indicator_of_notMem h]
    exact ⟨le_refl 0, zero_le_one⟩

/-- **Upper sets.** For every upper set `U ⊆ ℝ` the empirical measure `#{i < n : x i ∈ U}/n`
and the Lebesgue measure of `U ∩ (0,1]` differ by at most `D*ₙ`. -/
theorem abs_sum_indicator_upperSet_sub_le {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n)
    (hn : 0 < n) {U : Set ℝ} (hU : IsUpperSet U) :
    |(∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n - volume.real (U ∩ Set.Ioc 0 1)| ≤
      starDiscrepancy x n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hD := starDiscrepancy_nonneg x n
  by_cases h1 : (1 : ℝ) ∈ U
  · have hSne : (U ∩ Set.Icc (0 : ℝ) 1).Nonempty := ⟨1, h1, zero_le_one, le_refl 1⟩
    have hSbdd : BddBelow (U ∩ Set.Icc (0 : ℝ) 1) := ⟨0, fun y hy => hy.2.1⟩
    have ha0 : 0 ≤ sInf (U ∩ Set.Icc (0 : ℝ) 1) := le_csInf hSne fun y hy => hy.2.1
    have ha1 : sInf (U ∩ Set.Icc (0 : ℝ) 1) ≤ 1 := csInf_le hSbdd ⟨h1, zero_le_one, le_refl 1⟩
    have hlow : ∀ y ∈ U ∩ Set.Icc (0 : ℝ) 1, sInf (U ∩ Set.Icc (0 : ℝ) 1) ≤ y :=
      fun y hy => csInf_le hSbdd hy
    have hup : ∀ y, sInf (U ∩ Set.Icc (0 : ℝ) 1) < y → y ∈ U := by
      intro y hay
      obtain ⟨u, hu, huy⟩ := exists_lt_of_csInf_lt hSne hay
      exact hU huy.le hu.1
    have hvol : volume.real (U ∩ Set.Ioc 0 1) = 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1) := by
      apply le_antisymm
      · calc volume.real (U ∩ Set.Ioc 0 1)
            ≤ volume.real (Set.Icc (sInf (U ∩ Set.Icc (0 : ℝ) 1)) 1) := by
              refine measureReal_mono ?_ measure_Icc_lt_top.ne
              intro y hy
              exact ⟨hlow y ⟨hy.1, hy.2.1.le, hy.2.2⟩, hy.2.2⟩
          _ = 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1) := Real.volume_real_Icc_of_le ha1
      · calc 1 - sInf (U ∩ Set.Icc (0 : ℝ) 1)
            = volume.real (Set.Ioc (sInf (U ∩ Set.Icc (0 : ℝ) 1)) 1) :=
              (Real.volume_real_Ioc_of_le ha1).symm
          _ ≤ volume.real (U ∩ Set.Ioc 0 1) := by
              refine measureReal_mono ?_
                (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_Ioc_lt_top).ne
              intro y hy
              exact ⟨hup y hy.1, lt_of_le_of_lt ha0 hy.1, hy.2⟩
    have hsum_lo : (n : ℝ) - countAtMost x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) ≤
        ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) := by
      rw [countAtMost_eq_sum_indicator]
      have hn' : (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hn', ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i hi => ?_
      have hxi := hx i (Finset.mem_range.mp hi)
      by_cases hle : x i ≤ sInf (U ∩ Set.Icc (0 : ℝ) 1)
      · rw [Set.indicator_of_mem (show x i ∈ Set.Iic _ from hle), Pi.one_apply, sub_self]
        exact (indicator_one_mem_Icc U (x i)).1
      · have hmem : x i ∈ U := hup (x i) (lt_of_not_ge hle)
        rw [Set.indicator_of_notMem (show x i ∉ Set.Iic _ from hle), Set.indicator_of_mem hmem,
          Pi.one_apply, sub_zero]
    have hsum_hi : ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) ≤
        (n : ℝ) - countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) := by
      rw [countBelow_eq_sum_indicator]
      have hn' : (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hn', ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i hi => ?_
      have hxi := hx i (Finset.mem_range.mp hi)
      by_cases hlt : x i < sInf (U ∩ Set.Icc (0 : ℝ) 1)
      · have hnot : x i ∉ U := fun hmem =>
          absurd (hlow (x i) ⟨hmem, hxi.1, hxi.2.le⟩) (not_le.mpr hlt)
        rw [Set.indicator_of_mem (show x i ∈ Set.Iio _ from hlt), Pi.one_apply, sub_self,
          Set.indicator_of_notMem hnot]
      · rw [Set.indicator_of_notMem (show x i ∉ Set.Iio _ from hlt), sub_zero]
        exact (indicator_one_mem_Icc U (x i)).2
    have hA := countAtMost_div_sub_le_starDiscrepancy_of_mem x n
      (a := sInf (U ∩ Set.Icc (0 : ℝ) 1)) ⟨ha0, ha1⟩
    have hB : sInf (U ∩ Set.Icc (0 : ℝ) 1) -
        (countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) : ℝ) / n ≤ starDiscrepancy x n := by
      have h1 := neg_le_abs ((countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1)) : ℝ) / n -
        sInf (U ∩ Set.Icc (0 : ℝ) 1))
      have h2 := localDiscrepancy_le_starDiscrepancy x n
        (t := sInf (U ∩ Set.Icc (0 : ℝ) 1)) ⟨ha0, ha1⟩
      unfold localDiscrepancy at h2
      linarith
    have hlo' : ((n : ℝ) - countAtMost x n (sInf (U ∩ Set.Icc (0 : ℝ) 1))) / n ≤
        (∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n :=
      div_le_div_of_nonneg_right hsum_lo hpos.le
    have hhi' : (∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i)) / n ≤
        ((n : ℝ) - countBelow x n (sInf (U ∩ Set.Icc (0 : ℝ) 1))) / n :=
      div_le_div_of_nonneg_right hsum_hi hpos.le
    rw [sub_div, div_self hpos.ne'] at hlo' hhi'
    rw [hvol]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  · have hnot : ∀ y, y ≤ 1 → y ∉ U := fun y hy hyU => h1 (hU hy hyU)
    have hsum : ∑ i ∈ Finset.range n, U.indicator (1 : ℝ → ℝ) (x i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      exact Set.indicator_of_notMem (hnot (x i) (hx i (Finset.mem_range.mp hi)).2.le) _
    have hempty : U ∩ Set.Ioc (0 : ℝ) 1 = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => hnot y hy.2.2 hy.1
    rw [hsum, hempty, measureReal_empty, zero_div, sub_zero, abs_zero]
    exact hD

/-- The indicator of `(-∞, c]` is antitone. -/
theorem antitone_indicator_Iic (c : ℝ) : Antitone ((Set.Iic c).indicator (1 : ℝ → ℝ)) := by
  intro s s' hss'
  by_cases hs' : s' ∈ Set.Iic c
  · have hs : s ∈ Set.Iic c := le_trans hss' hs'
    rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs, Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem hs']
    exact (indicator_one_mem_Icc _ s).1

/-- `∫₀^V 1_{s ≤ c} ds = c` for `0 ≤ c ≤ V`. -/
theorem integral_indicator_Iic_one {c V : ℝ} (hc0 : 0 ≤ c) (hcV : c ≤ V) :
    ∫ s in (0 : ℝ)..V, (Set.Iic c).indicator (1 : ℝ → ℝ) s = c := by
  rw [intervalIntegral.integral_of_le (hc0.trans hcV), setIntegral_indicator measurableSet_Iic,
    Set.Ioc_inter_Iic, inf_eq_right.mpr hcV]
  simp only [Pi.one_apply]
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hc0, smul_eq_mul, mul_one, sub_zero]

/-- **Layer cake, empirical side.** If `0 ≤ h (x i) ≤ V` for `i < n`, then
`(1/n) ∑ h(xᵢ) = ∫₀^V (1/n) #{i : s ≤ h(xᵢ)} ds`. -/
theorem sum_div_eq_integral_indicator {h : ℕ → ℝ} {n : ℕ} {V : ℝ}
    (hh : ∀ i < n, 0 ≤ h i ∧ h i ≤ V) :
    (∑ i ∈ Finset.range n, h i) / n =
      ∫ s in (0 : ℝ)..V, (∑ i ∈ Finset.range n, (Set.Iic (h i)).indicator (1 : ℝ → ℝ) s) / n := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    fun i _ => (antitone_indicator_Iic _).intervalIntegrable]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have := hh i (Finset.mem_range.mp hi)
  exact (integral_indicator_Iic_one this.1 this.2).symm

/-- **Layer cake, Lebesgue side.** For monotone `g`,
`∫₀¹ (g - g 0) = ∫₀^{g 1 - g 0} λ{t ∈ (0,1] : s ≤ g t - g 0} ds`. -/
theorem integral_sub_eq_integral_measureReal {g : ℝ → ℝ} (hg : Monotone g) :
    (∫ t in (0 : ℝ)..1, (g t - g 0)) =
      ∫ s in (0 : ℝ)..(g 1 - g 0), (volume.restrict (Set.Ioc (0 : ℝ) 1)).real
        {a | s ≤ g a - g 0} := by
  have hV : 0 ≤ g 1 - g 0 := sub_nonneg.mpr (hg zero_le_one)
  have hmono : Monotone fun t => g t - g 0 := fun a b hab => sub_le_sub_right (hg hab) _
  have hint : Integrable (fun t => g t - g 0) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hmono.intervalIntegrable (μ := volume))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => g t - g 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_nonneg.mpr (hg ht.1.le)
  have hbdd : (fun t => g t - g 0) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun _ => g 1 - g 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sub_le_sub_right (hg ht.2) _
  rw [intervalIntegral.integral_of_le zero_le_one, hint.integral_eq_integral_Ioc_meas_le hnn hbdd,
    intervalIntegral.integral_of_le hV]

/-- **Koksma's inequality for monotone `f`.** For `g` monotone on `ℝ` and `n ≥ 1` points in
`[0,1)`: `|(1/n) ∑ g(xᵢ) - ∫₀¹ g| ≤ (g 1 - g 0) D*ₙ`. -/
theorem koksma_monotone {g : ℝ → ℝ} (hg : Monotone g) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) * starDiscrepancy x n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : 0 ≤ g 1 - g 0 := sub_nonneg.mpr (hg zero_le_one)
  have hQ : qmcEstimate g x n = (∑ i ∈ Finset.range n, (g (x i) - g 0)) / n + g 0 := by
    unfold qmcEstimate
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_div,
      mul_div_cancel_left₀ _ hpos.ne']
    ring
  have hI : ∫ t in (0 : ℝ)..1, g t = (∫ t in (0 : ℝ)..1, (g t - g 0)) + g 0 := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul]
    ring
  have hh : ∀ i < n, 0 ≤ g (x i) - g 0 ∧ g (x i) - g 0 ≤ g 1 - g 0 := fun i hi =>
    ⟨sub_nonneg.mpr (hg (hx i hi).1), sub_le_sub_right (hg (hx i hi).2.le) _⟩
  have hanti : Antitone fun s => (volume.restrict (Set.Ioc (0 : ℝ) 1)).real
      {a | s ≤ g a - g 0} := fun s s' hss' => measureReal_mono fun a ha => le_trans hss' ha
  have hint1 : IntervalIntegrable (fun s => (∑ i ∈ Finset.range n,
      (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s) / n) volume 0 (g 1 - g 0) := by
    refine Antitone.intervalIntegrable fun s s' hss' => ?_
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
      antitone_indicator_Iic _ hss') hpos.le
  rw [hQ, hI, show ∀ A B C : ℝ, A + C - (B + C) = A - B from fun A B C => by ring,
    sum_div_eq_integral_indicator (h := fun i => g (x i) - g 0) hh,
    integral_sub_eq_integral_measureReal hg,
    ← intervalIntegral.integral_sub hint1 hanti.intervalIntegrable, ← Real.norm_eq_abs]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := g 1 - g 0)
    (C := starDiscrepancy x n) (f := fun s => (∑ i ∈ Finset.range n,
      (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s) / n -
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).real {a | s ≤ g a - g 0}) ?_
  · rw [sub_zero, abs_of_nonneg hV, mul_comm] at hbound
    exact hbound
  intro s _
  have hU : IsUpperSet {a : ℝ | s ≤ g a - g 0} := fun a b hab ha =>
    le_trans ha (sub_le_sub_right (hg hab) _)
  have hsum : ∑ i ∈ Finset.range n, (Set.Iic (g (x i) - g 0)).indicator (1 : ℝ → ℝ) s =
      ∑ i ∈ Finset.range n, {a : ℝ | s ≤ g a - g 0}.indicator (1 : ℝ → ℝ) (x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hs : s ≤ g (x i) - g 0
    · rw [Set.indicator_of_mem (show s ∈ Set.Iic (g (x i) - g 0) from hs),
        Set.indicator_of_mem (show x i ∈ {a : ℝ | s ≤ g a - g 0} from hs), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Iic (g (x i) - g 0) from hs),
        Set.indicator_of_notMem (show x i ∉ {a : ℝ | s ≤ g a - g 0} from hs)]
  rw [Real.norm_eq_abs, hsum, measureReal_restrict_apply' measurableSet_Ioc]
  exact abs_sum_indicator_upperSet_sub_le hx hn hU

/-- Extending a function monotone on `[0,1]` by its end values gives a monotone function on
`ℝ` that agrees with it on `[0,1]`. -/
theorem monotone_comp_projIcc {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc 0 1)) :
    Monotone fun t => g (Set.projIcc (0 : ℝ) 1 zero_le_one t) := fun a b hab =>
  hg (Set.projIcc (0 : ℝ) 1 zero_le_one a).2 (Set.projIcc (0 : ℝ) 1 zero_le_one b).2
    (Set.monotone_projIcc zero_le_one hab)

/-- `g ∘ projIcc` agrees with `g` on `[0,1]`. -/
theorem comp_projIcc_eq {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g (Set.projIcc (0 : ℝ) 1 zero_le_one t) = g t := by
  rw [Set.projIcc_of_mem zero_le_one ht]

/-- Functions that agree on `[0,1]` have the same QMC error at points of `[0,1)`. -/
theorem qmcError_congr {f g : ℝ → ℝ} (hfg : Set.EqOn f g (Set.Icc 0 1)) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) :
    qmcEstimate f x n - (∫ t in (0 : ℝ)..1, f t) =
      qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t := by
  have hQ : qmcEstimate f x n = qmcEstimate g x n := by
    unfold qmcEstimate
    congr 1
    exact Finset.sum_congr rfl fun i hi =>
      hfg (Set.Ico_subset_Icc_self (hx i (Finset.mem_range.mp hi)))
  have hI : ∫ t in (0 : ℝ)..1, f t = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr (by rw [Set.uIcc_of_le zero_le_one]; exact hfg)
  rw [hQ, hI]

/-- **Koksma's inequality for `f` monotone on `[0,1]`**:
`|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ (f 1 - f 0) D*ₙ`. -/
theorem koksma_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc 0 1)) {x : ℕ → ℝ} {n : ℕ}
    (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate g x n - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) * starDiscrepancy x n := by
  have h := koksma_monotone (monotone_comp_projIcc hg) hx hn
  have hc : Set.EqOn g (fun t => g (Set.projIcc (0 : ℝ) 1 zero_le_one t)) (Set.Icc 0 1) :=
    fun t ht => (comp_projIcc_eq ht).symm
  rw [qmcError_congr hc hx]
  rwa [comp_projIcc_eq (g := g) (Set.right_mem_Icc.mpr zero_le_one),
    comp_projIcc_eq (g := g) (Set.left_mem_Icc.mpr zero_le_one)] at h

/-- **Koksma's inequality for differences of monotone functions.** If `f = p - q` on `[0,1]`
with `p, q` monotone on `[0,1]`, then
`|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ ((p 1 - p 0) + (q 1 - q 0)) D*ₙ`. -/
theorem koksma_sub_monotoneOn {f p q : ℝ → ℝ} (hp : MonotoneOn p (Set.Icc 0 1))
    (hq : MonotoneOn q (Set.Icc 0 1)) (hf : Set.EqOn f (p - q) (Set.Icc 0 1)) {x : ℕ → ℝ}
    {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤
      ((p 1 - p 0) + (q 1 - q 0)) * starDiscrepancy x n := by
  have hpI : IntervalIntegrable p volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact hp)
  have hqI : IntervalIntegrable q volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact hq)
  have hsplit : qmcEstimate (p - q) x n - (∫ t in (0 : ℝ)..1, (p - q) t) =
      (qmcEstimate p x n - ∫ t in (0 : ℝ)..1, p t) -
        (qmcEstimate q x n - ∫ t in (0 : ℝ)..1, q t) := by
    unfold qmcEstimate
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, sub_div, intervalIntegral.integral_sub hpI hqI]
    ring
  rw [qmcError_congr hf hx, hsplit]
  have h1 := koksma_monotoneOn hp hx hn
  have h2 := koksma_monotoneOn hq hx hn
  calc _ ≤ |qmcEstimate p x n - ∫ t in (0 : ℝ)..1, p t| +
        |qmcEstimate q x n - ∫ t in (0 : ℝ)..1, q t| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Koksma's inequality** (one dimension). For `f` of bounded variation on `[0,1]` and
`n ≥ 1` points in `[0,1)`: `|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ V(f) D*ₙ`. -/
theorem koksma_boundedVariationOn {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n) (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤ totalVariation f * starDiscrepancy x n := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hloc := hf.locallyBoundedVariationOn
  have hadd := variationOnFromTo.add_self_monotoneOn hloc h0
  have hsub := variationOnFromTo.sub_self_monotoneOn hloc h0
  have hp : MonotoneOn (fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t + f t) / 2)
      (Set.Icc 0 1) := fun a ha b hb hab =>
    div_le_div_of_nonneg_right (hadd ha hb hab) zero_le_two
  have hq : MonotoneOn (fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t - f t) / 2)
      (Set.Icc 0 1) := fun a ha b hb hab =>
    div_le_div_of_nonneg_right (hsub ha hb hab) zero_le_two
  have hfpq : Set.EqOn f ((fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t + f t) / 2) -
      fun t => (variationOnFromTo f (Set.Icc 0 1) 0 t - f t) / 2) (Set.Icc 0 1) := by
    intro t _
    simp only [Pi.sub_apply]
    ring
  have h := koksma_sub_monotoneOn hp hq hfpq hx hn
  have hV0 : variationOnFromTo f (Set.Icc 0 1) 0 0 = 0 := variationOnFromTo.self f _ 0
  have hV1 : variationOnFromTo f (Set.Icc 0 1) 0 1 = totalVariation f := by
    rw [variationOnFromTo.eq_of_le f _ zero_le_one, Set.inter_self]
    rfl
  rw [hV0, hV1] at h
  calc _ ≤ _ := h
    _ = totalVariation f * starDiscrepancy x n := by ring

/-- **Koksma's inequality, `C¹` form.** If `f` has derivative `f'` at every point of `[0,1]`
and `f'` is integrable on `[0,1]`, then `|(1/n) ∑ f(xᵢ) - ∫₀¹ f| ≤ (∫₀¹ |f'|) D*ₙ`. -/
theorem koksma_hasDerivAt {f f' : ℝ → ℝ} (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) {x : ℕ → ℝ} {n : ℕ} (hx : InUnitIco x n)
    (hn : 0 < n) :
    |qmcEstimate f x n - ∫ t in (0 : ℝ)..1, f t| ≤
      (∫ t in (0 : ℝ)..1, |f' t|) * starDiscrepancy x n := by
  have hplus : IntervalIntegrable (fun t => (|f' t| + f' t) / 2) volume 0 1 :=
    (hint.abs.add hint).div_const 2
  have hminus : IntervalIntegrable (fun t => (|f' t| - f' t) / 2) volume 0 1 :=
    (hint.abs.sub hint).div_const 2
  have hsubI : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      Set.uIcc a b ⊆ Set.uIcc 0 1 := by
    intro a b ha hb
    rw [Set.uIcc_of_le zero_le_one]
    exact Set.uIcc_subset_Icc ha hb
  -- monotonicity of `t ↦ ∫₀ᵗ φ` for nonnegative integrable `φ`
  have hmonoInt : ∀ φ : ℝ → ℝ, IntervalIntegrable φ volume 0 1 → (∀ t, 0 ≤ φ t) →
      MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, φ s) (Set.Icc 0 1) := by
    intro φ hφ hnn a ha b hb hab
    have hsub := intervalIntegral.integral_interval_sub_left
      (hφ.mono_set (hsubI (Set.left_mem_Icc.mpr zero_le_one) hb))
      (hφ.mono_set (hsubI (Set.left_mem_Icc.mpr zero_le_one) ha))
    have hnonneg : 0 ≤ ∫ s in a..b, φ s := intervalIntegral.integral_nonneg hab fun u _ => hnn u
    linarith
  have hp : MonotoneOn (fun t => f 0 + ∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2)
      (Set.Icc 0 1) := by
    intro a ha b hb hab
    have := hmonoInt _ hplus (fun t => by
      have := neg_abs_le (f' t)
      linarith) ha hb hab
    simp only at this ⊢
    linarith
  have hq : MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) (Set.Icc 0 1) :=
    hmonoInt _ hminus fun t => by
      have := le_abs_self (f' t)
      linarith
  have hfpq : Set.EqOn f ((fun t => f 0 + ∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2) -
      fun t => ∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) (Set.Icc 0 1) := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
    have hft : ∫ s in (0 : ℝ)..t, f' s = f t - f 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hderiv u ?_)
        (hint.mono_set (hsubI h0 ht))
      rw [Set.uIcc_of_le ht.1] at hu
      exact ⟨hu.1, hu.2.trans ht.2⟩
    have hsplit : (∫ s in (0 : ℝ)..t, (|f' s| + f' s) / 2) -
        (∫ s in (0 : ℝ)..t, (|f' s| - f' s) / 2) = ∫ s in (0 : ℝ)..t, f' s := by
      rw [← intervalIntegral.integral_sub (hplus.mono_set (hsubI h0 ht))
        (hminus.mono_set (hsubI h0 ht))]
      exact intervalIntegral.integral_congr fun u _ => by ring
    simp only [Pi.sub_apply]
    linarith
  have h := koksma_sub_monotoneOn hp hq hfpq hx hn
  have htot : (f 0 + ∫ s in (0 : ℝ)..1, (|f' s| + f' s) / 2) -
      (f 0 + ∫ s in (0 : ℝ)..0, (|f' s| + f' s) / 2) +
      ((∫ s in (0 : ℝ)..1, (|f' s| - f' s) / 2) - (∫ s in (0 : ℝ)..0, (|f' s| - f' s) / 2)) =
      ∫ t in (0 : ℝ)..1, |f' t| := by
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same, add_zero, sub_zero,
      add_sub_cancel_left, ← intervalIntegral.integral_add hplus hminus]
    exact intervalIntegral.integral_congr fun u _ => by ring
  beta_reduce at h
  rw [htot] at h
  exact h

/-- **Variation of a differentiable function.** If `f` has derivative `f'` on `[0,1]` and `f'` is
integrable there, then `eVariationOn f [0,1] ≤ ∫₀¹ |f'|`. -/
theorem eVariationOn_le_integral_abs_deriv {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) :
    eVariationOn f (Set.Icc 0 1) ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, |f' t|) := by
  have hsubI : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      Set.uIcc a b ⊆ Set.uIcc 0 1 := by
    intro a b ha hb
    rw [Set.uIcc_of_le zero_le_one]
    exact Set.uIcc_subset_Icc ha hb
  refine iSup_le fun ⟨N, u, hu, hus⟩ => ?_
  dsimp only
  have hstep : ∀ i, |f (u (i + 1)) - f (u i)| ≤ ∫ t in (u i)..(u (i + 1)), |f' t| := by
    intro i
    have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hFTC : ∫ t in (u i)..(u (i + 1)), f' t = f (u (i + 1)) - f (u i) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t ?_)
        (hint.mono_set (hsubI (hus i) (hus (i + 1))))
      rw [Set.uIcc_of_le hle] at ht
      exact ⟨(hus i).1.trans ht.1, ht.2.trans (hus (i + 1)).2⟩
    rw [← hFTC]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have htele : ∑ i ∈ Finset.range N, ∫ t in (u i)..(u (i + 1)), |f' t| =
      ∫ t in (u 0)..(u N), |f' t| :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ =>
      hint.abs.mono_set (hsubI (hus k) (hus (k + 1)))
  have hmono : ∫ t in (u 0)..(u N), |f' t| ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
    intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le N)) (hus N).2
      (Filter.Eventually.of_forall fun t => abs_nonneg (f' t)) hint.abs
  have hsum : ∑ i ∈ Finset.range N, |f (u (i + 1)) - f (u i)| ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
    (Finset.sum_le_sum fun i _ => hstep i).trans (htele.le.trans hmono)
  have hed : ∀ i ∈ Finset.range N, edist (f (u (i + 1))) (f (u i)) =
      ENNReal.ofReal |f (u (i + 1)) - f (u i)| := fun i _ => by
    rw [edist_dist, Real.dist_eq]
  rw [Finset.sum_congr rfl hed, ← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
  exact ENNReal.ofReal_le_ofReal hsum

/-- A function with integrable derivative on `[0,1]` has bounded variation there. -/
theorem boundedVariationOn_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) : BoundedVariationOn f (Set.Icc 0 1) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_le_integral_abs_deriv hderiv hint)

/-- **The `C¹` corollary.** `V(f) ≤ ∫₀¹ |f'|` for `f` with integrable derivative on `[0,1]`, so
Koksma's bound `V(f) D*ₙ` is at most `(∫₀¹ |f'|) D*ₙ` (see also `koksma_hasDerivAt`). -/
theorem totalVariation_le_integral_abs_deriv {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume 0 1) :
    totalVariation f ≤ ∫ t in (0 : ℝ)..1, |f' t| :=
  ENNReal.toReal_le_of_le_ofReal
    (intervalIntegral.integral_nonneg zero_le_one fun t _ => abs_nonneg (f' t))
    (eVariationOn_le_integral_abs_deriv hderiv hint)

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The van der Corput sequence

Copied from `RQMCMarkov/MarkovDriving` (from `RQMCMarkov/PointSets`); see that project for
its documentation.

Post #2 builds QMC point sets from the Sobol sequence. In one dimension the Sobol sequence is the
base-2 van der Corput sequence (radical inverse): write `k = ∑ⱼ bⱼ 2ʲ` in binary and reflect
the digits about the binary point, `φ(k) = ∑ⱼ bⱼ 2^{-(j+1)}` (van der Corput 1935;
Niederreiter 1992, Ch. 3; L'Ecuyer 2016).

**Definition.** `vanDerCorput 0 = 0` and `vanDerCorput k = (k mod 2)/2 + vanDerCorput (k/2)/2`,
which is the radical inverse read off the binary digits.

**Results.**
* `vanDerCorput_mem_Ico`: every term lies in `[0,1)`.
* `card_vanDerCorput_mem_dyadic`: **net property.** Any `2^m` *consecutive* terms
  `φ(a), …, φ(a + 2^m - 1)` put exactly one point in each dyadic interval
  `[j/2^m, (j+1)/2^m)`. This holds for every start `a`, in particular for the aligned blocks
  starting at a multiple of `2^m` (`card_vanDerCorput_mem_dyadic_aligned`).
* `abs_countBelow_vanDerCorput_sub_le`: `|#{i < n : φ(i) < t} - nt| ≤ log₂ n + 1`, by splitting
  `n` along its binary expansion into blocks of `2^m` consecutive terms.
* `starDiscrepancy_vanDerCorput_le`: `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`, and
  `starDiscrepancy_vanDerCorput_le_log`: `D*ₙ ≤ 2 (log n + 1)/n` (natural log).
* `abs_qmcError_vanDerCorput_le`: by Koksma, the QMC error for `f` of bounded variation is at
  most `V(f) · 2 (log n + 1)/n`.
* `tendsto_sqrt_mul_qmcError_vanDerCorput`: hence `√n · |QMC error| → 0`, i.e. the van der
  Corput QMC error is `o(n^{-1/2})`, faster than the MC root-mean-square error `σ/√n` (post #1,
  post #2 "QMC/RQMC have faster rates of convergence than MC").
-/

namespace RQMCMarkov.ScrambledStacks

open Filter Topology

/-- The base-2 van der Corput (radical-inverse) sequence: `φ(0) = 0` and
`φ(k) = (k mod 2)/2 + φ(⌊k/2⌋)/2`. -/
noncomputable def vanDerCorput : ℕ → ℝ
  | 0 => 0
  | k + 1 => (((k + 1) % 2 : ℕ) : ℝ) / 2 + vanDerCorput ((k + 1) / 2) / 2
decreasing_by omega

/-- The defining recursion of the van der Corput sequence, for every `k`. -/
theorem vanDerCorput_eq (k : ℕ) :
    vanDerCorput k = ((k % 2 : ℕ) : ℝ) / 2 + vanDerCorput (k / 2) / 2 := by
  cases k with
  | zero =>
    rw [Nat.zero_mod, Nat.zero_div, vanDerCorput.eq_1, Nat.cast_zero]
    ring
  | succ k => rw [vanDerCorput]

/-- `φ(2q + b) = b/2 + φ(q)/2` for a binary digit `b`. -/
theorem vanDerCorput_two_mul_add (q b : ℕ) (hb : b < 2) :
    vanDerCorput (2 * q + b) = (b : ℝ) / 2 + vanDerCorput q / 2 := by
  rw [vanDerCorput_eq, show (2 * q + b) % 2 = b by omega, show (2 * q + b) / 2 = q by omega]

/-- The first terms: `φ(1) = 1/2`, `φ(2) = 1/4`, `φ(3) = 3/4`. -/
theorem vanDerCorput_one_two_three :
    vanDerCorput 1 = 1 / 2 ∧ vanDerCorput 2 = 1 / 4 ∧ vanDerCorput 3 = 3 / 4 := by
  have h0 : vanDerCorput 0 = 0 := vanDerCorput.eq_1
  have h1 : vanDerCorput 1 = 1 / 2 := by
    rw [vanDerCorput_eq, show (1 : ℕ) / 2 = 0 by norm_num, h0]
    norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [vanDerCorput_eq, show (2 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num
  · rw [vanDerCorput_eq, show (3 : ℕ) / 2 = 1 by norm_num, h1]
    norm_num

/-- Every van der Corput point lies in `[0,1)`. -/
theorem vanDerCorput_mem_Ico (k : ℕ) : vanDerCorput k ∈ Set.Ico (0 : ℝ) 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [vanDerCorput.eq_1]
      exact ⟨le_refl 0, zero_lt_one⟩
    · have h := ih (k / 2) (Nat.div_lt_self hk (by norm_num))
      have hb : ((k % 2 : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt k (by norm_num))
      have hb0 : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [vanDerCorput_eq]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The first `n` van der Corput points lie in `[0,1)`, for every `n`. -/
theorem vanDerCorput_inUnitIco (n : ℕ) : InUnitIco vanDerCorput n :=
  fun i _ => vanDerCorput_mem_Ico i

/-- The `m`-digit index `⌊2^m φ(k)⌋` is below `2^m`. -/
theorem floor_two_pow_mul_vanDerCorput_lt (m k : ℕ) :
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ < 2 ^ m := by
  have h := vanDerCorput_mem_Ico k
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_lt (mul_nonneg hpos.le h.1), Nat.cast_pow, Nat.cast_ofNat]
  exact mul_lt_of_lt_one_right hpos h.2

/-- The digit recursion: `⌊2^{m+1} φ(k)⌋ = (k mod 2) 2^m + ⌊2^m φ(⌊k/2⌋)⌋`. -/
theorem floor_two_pow_succ_mul_vanDerCorput (m k : ℕ) :
    ⌊(2 : ℝ) ^ (m + 1) * vanDerCorput k⌋₊ =
      k % 2 * 2 ^ m + ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ := by
  have h : (2 : ℝ) ^ (m + 1) * vanDerCorput k =
      (2 : ℝ) ^ m * vanDerCorput (k / 2) + ((k % 2 * 2 ^ m : ℕ) : ℝ) := by
    rw [vanDerCorput_eq k, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [h, Nat.floor_add_natCast (mul_nonneg (pow_nonneg zero_le_two m)
    (vanDerCorput_mem_Ico _).1), add_comm]

/-- The `m`-digit index determines `k mod 2^m`. -/
theorem mod_eq_of_floor_vanDerCorput_eq (m : ℕ) : ∀ {k k' : ℕ},
    ⌊(2 : ℝ) ^ m * vanDerCorput k⌋₊ = ⌊(2 : ℝ) ^ m * vanDerCorput k'⌋₊ →
      k % 2 ^ m = k' % 2 ^ m := by
  induction m with
  | zero =>
    intro k k' _
    rw [pow_zero, Nat.mod_one, Nat.mod_one]
  | succ m ih =>
    intro k k' h
    rw [floor_two_pow_succ_mul_vanDerCorput, floor_two_pow_succ_mul_vanDerCorput] at h
    have hA := floor_two_pow_mul_vanDerCorput_lt m (k / 2)
    have hA' := floor_two_pow_mul_vanDerCorput_lt m (k' / 2)
    have hbits : k % 2 = k' % 2 ∧ ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ =
        ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ := by
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k / 2)⌋₊ = A at h hA ⊢
      generalize ⌊(2 : ℝ) ^ m * vanDerCorput (k' / 2)⌋₊ = A' at h hA' ⊢
      generalize (2 : ℕ) ^ m = P at h hA hA' ⊢
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;>
      rcases Nat.mod_two_eq_zero_or_one k' with hk' | hk' <;>
      rw [hk, hk'] at h ⊢ <;> omega
    rw [pow_succ', Nat.mod_mul, Nat.mod_mul, hbits.1, ih hbits.2]

/-- Within any block of `2^m` consecutive terms, the `m`-digit index is injective. -/
theorem floor_vanDerCorput_injOn (m a : ℕ) :
    Set.InjOn (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) := by
  intro r hr r' hr' h
  have hr1 : r < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hr1' : r' < 2 ^ m := Finset.mem_range.mp (Finset.mem_coe.mp hr')
  have hmod : a + r ≡ a + r' [MOD 2 ^ m] := mod_eq_of_floor_vanDerCorput_eq m h
  have := Nat.ModEq.add_left_cancel' a hmod
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at this

/-- A point `v ≥ 0` lies in the dyadic interval `[j/2^m, (j+1)/2^m)` iff `⌊2^m v⌋ = j`. -/
theorem mem_dyadic_iff_floor (m j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m) ↔ ⌊(2 : ℝ) ^ m * v⌋₊ = j := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  rw [Nat.floor_eq_iff (mul_nonneg hpos.le hv), Set.mem_Ico, div_le_iff₀ hpos, lt_div_iff₀ hpos,
    mul_comm v]

/-- **Net property.** Any `2^m` consecutive van der Corput terms `φ(a), …, φ(a + 2^m - 1)` put
exactly one point in each dyadic interval `[j/2^m, (j+1)/2^m)`, `j < 2^m`. -/
theorem card_vanDerCorput_mem_dyadic (m a j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 := by
  have hmaps : Set.MapsTo (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊)
      (Finset.range (2 ^ m) : Set ℕ) (Finset.range (2 ^ m) : Set ℕ) := fun r _ =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr (floor_two_pow_mul_vanDerCorput_lt m (a + r)))
  have hsurj := Finset.surjOn_of_injOn_of_card_le _ hmaps (floor_vanDerCorput_injOn m a)
    (le_refl _)
  obtain ⟨r, hr, hrj⟩ := hsurj (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
  rw [Finset.card_eq_one]
  refine ⟨r, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1]
    exact ⟨Finset.mem_coe.mp hr, hrj⟩
  · intro r' hr'
    rw [Finset.mem_filter, mem_dyadic_iff_floor m j (vanDerCorput_mem_Ico _).1] at hr'
    exact floor_vanDerCorput_injOn m a (Finset.mem_coe.mpr hr'.1) hr (hr'.2.trans hrj.symm)

/-- **Net property, aligned blocks.** The block `φ(k 2^m), …, φ(k 2^m + 2^m - 1)` hits each
dyadic interval of length `2^{-m}` exactly once. -/
theorem card_vanDerCorput_mem_dyadic_aligned (m k j : ℕ) (hj : j < 2 ^ m) :
    ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (k * 2 ^ m + r) ∈
      Set.Ico ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m))).card = 1 :=
  card_vanDerCorput_mem_dyadic m (k * 2 ^ m) j hj

/-- A block of `2^m` consecutive van der Corput terms has local counting error at most `1`:
`|#{r < 2^m : φ(a + r) < t} - 2^m t| ≤ 1` for `t ∈ [0,1]`. -/
theorem abs_card_block_vanDerCorput_sub_le (m a : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) -
      2 ^ m * t| ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hmt : 0 ≤ (2 : ℝ) ^ m * t := mul_nonneg hpos.le ht.1
  have hinj := floor_vanDerCorput_injOn m a
  -- upper bound
  have hup : ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card ≤
      ⌊(2 : ℝ) ^ m * t⌋₊ + 1 := by
    have := Finset.card_le_card_of_injOn (t := Finset.range (⌊(2 : ℝ) ^ m * t⌋₊ + 1))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => vanDerCorput (a + r) < t) _)))
    · rwa [Finset.card_range] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left hr.2.le hpos.le)
  -- lower bound, through the complement
  have hcompl : ((Finset.range (2 ^ m)).filter (fun r => ¬ vanDerCorput (a + r) < t)).card ≤
      2 ^ m - ⌊(2 : ℝ) ^ m * t⌋₊ := by
    have := Finset.card_le_card_of_injOn (t := Finset.Ico ⌊(2 : ℝ) ^ m * t⌋₊ (2 ^ m))
      (fun r => ⌊(2 : ℝ) ^ m * vanDerCorput (a + r)⌋₊) ?_
      (hinj.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (fun r : ℕ => ¬ vanDerCorput (a + r) < t) _)))
    · rwa [Nat.card_Ico] at this
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Finset.mem_Ico]
    exact ⟨Nat.floor_le_floor (mul_le_mul_of_nonneg_left (not_lt.mp hr.2) hpos.le),
      floor_two_pow_mul_vanDerCorput_lt m (a + r)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ m))
    (fun r : ℕ => vanDerCorput (a + r) < t)
  rw [Finset.card_range] at hsplit
  have hj : ⌊(2 : ℝ) ^ m * t⌋₊ ≤ 2 ^ m := by
    apply Nat.floor_le_of_le
    rw [Nat.cast_pow, Nat.cast_ofNat]
    have := mul_le_mul_of_nonneg_left ht.2 hpos.le
    linarith
  have hlow : ⌊(2 : ℝ) ^ m * t⌋₊ ≤
      ((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card := by omega
  have hupR : (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) ≤
      (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) + 1 := by exact_mod_cast hup
  have hlowR : (⌊(2 : ℝ) ^ m * t⌋₊ : ℝ) ≤
      (((Finset.range (2 ^ m)).filter (fun r => vanDerCorput (a + r) < t)).card : ℝ) := by
    exact_mod_cast hlow
  have hfl := Nat.floor_le hmt
  have hfl' := Nat.lt_floor_add_one ((2 : ℝ) ^ m * t)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Splitting the counting function: the first `N + M` points are the first `N` points and the
block of `M` points starting at `N`. -/
theorem countBelow_add (x : ℕ → ℝ) (N M : ℕ) (t : ℝ) :
    countBelow x (N + M) t =
      countBelow x N t + ((Finset.range M).filter (fun r => x (N + r) < t)).card := by
  unfold countBelow
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]

/-- **Counting error of the van der Corput sequence.** For `t ∈ [0,1]`,
`|#{i < n : φ(i) < t} - nt| ≤ ⌊log₂ n⌋ + 1`. -/
theorem abs_countBelow_vanDerCorput_sub_le (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(countBelow vanDerCorput N t : ℝ) - N * t| ≤ Nat.log 2 N + 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul, sub_zero,
        abs_zero]
      positivity
    · have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
      have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 2 ^ Nat.log 2 N := ⟨N - 2 ^ Nat.log 2 N, by omega⟩
      have hN'lt : N' < 2 ^ Nat.log 2 N := by rw [pow_succ] at hlt; omega
      have hblock := abs_card_block_vanDerCorput_sub_le (Nat.log 2 N) N' ht
      have hsplit : (countBelow vanDerCorput N t : ℝ) - N * t =
          ((countBelow vanDerCorput N' t : ℝ) - N' * t) +
          ((((Finset.range (2 ^ Nat.log 2 N)).filter
            (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t) := by
        conv_lhs => rw [hN', countBelow_add]
        push_cast
        ring
      have hrest : |(countBelow vanDerCorput N' t : ℝ) - N' * t| ≤ Nat.log 2 N := by
        rcases Nat.eq_zero_or_pos N' with h0 | h0
        · rw [h0, show countBelow vanDerCorput 0 t = 0 from rfl, Nat.cast_zero, zero_mul,
            sub_zero, abs_zero]
          positivity
        · have hlog : Nat.log 2 N' < Nat.log 2 N := Nat.log_lt_of_lt_pow h0.ne' hN'lt
          have hlogR : (Nat.log 2 N' : ℝ) + 1 ≤ Nat.log 2 N := by exact_mod_cast hlog
          exact (ih N' (by omega)).trans hlogR
      rw [hsplit]
      calc _ ≤ |(countBelow vanDerCorput N' t : ℝ) - N' * t| +
            |(((Finset.range (2 ^ Nat.log 2 N)).filter
              (fun r => vanDerCorput (N' + r) < t)).card : ℝ) - 2 ^ Nat.log 2 N * t| :=
            abs_add_le _ _
        _ ≤ _ := by linarith

/-- **Star discrepancy of the van der Corput sequence:** `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ ((Nat.log 2 n : ℝ) + 1) / n := by
  apply starDiscrepancy_le_of_forall
  intro t ht
  rw [localDiscrepancy_eq_abs_div _ hn.ne' t]
  exact div_le_div_of_nonneg_right (abs_countBelow_vanDerCorput_sub_le n ht) (Nat.cast_nonneg n)

/-- `⌊log₂ n⌋ + 1 ≤ 2 (log n + 1)` for `n ≥ 1` (natural logarithm). -/
theorem natLog_two_add_one_le {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) + 1 ≤ 2 * (Real.log n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  rw [Nat.cast_pow, Nat.cast_ofNat] at hpow
  have hlog := Real.log_le_log (pow_pos two_pos _) hpow
  rw [Real.log_pow] at hlog
  have hl2 := Real.log_two_gt_d9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

/-- **Star discrepancy of the van der Corput sequence, natural-log form:**
`D*ₙ ≤ 2 (log n + 1)/n`. -/
theorem starDiscrepancy_vanDerCorput_le_log {n : ℕ} (hn : 0 < n) :
    starDiscrepancy vanDerCorput n ≤ 2 * (Real.log n + 1) / n :=
  (starDiscrepancy_vanDerCorput_le hn).trans
    (div_le_div_of_nonneg_right (natLog_two_add_one_le hn) (Nat.cast_nonneg n))

/-- **QMC error of the van der Corput sequence** (Koksma): for `f` of bounded variation on
`[0,1]`, `|(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| ≤ V(f) · 2 (log n + 1)/n`. -/
theorem abs_qmcError_vanDerCorput_le {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc 0 1))
    {n : ℕ} (hn : 0 < n) :
    |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t| ≤
      totalVariation f * (2 * (Real.log n + 1) / n) :=
  (koksma_boundedVariationOn hf (vanDerCorput_inUnitIco n) hn).trans
    (mul_le_mul_of_nonneg_left (starDiscrepancy_vanDerCorput_le_log hn) ENNReal.toReal_nonneg)

/-- `(log x + 1)/√x → 0`. -/
theorem tendsto_log_add_one_div_sqrt :
    Tendsto (fun x : ℝ => (Real.log x + 1) / Real.sqrt x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr fun x => ?_
  rw [Real.sqrt_eq_rpow, add_div, one_div (x ^ (1 / 2 : ℝ))]

/-- **QMC beats MC (the bound).** `√n · 2 (log n + 1)/n → 0`: the van der Corput discrepancy
bound falls faster than the MC rate `n^{-1/2}`. -/
theorem tendsto_sqrt_mul_vanDerCorput_bound :
    Tendsto (fun n : ℕ => Real.sqrt n * (2 * (Real.log n + 1) / n)) atTop (𝓝 0) := by
  have h := (tendsto_log_add_one_div_sqrt.comp tendsto_natCast_atTop_atTop).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
  simp only [Function.comp_apply]
  calc 2 * ((Real.log n + 1) / Real.sqrt n)
      = 2 * (Real.log n + 1) * Real.sqrt n / (Real.sqrt n * Real.sqrt n) := by
        rw [mul_div_mul_right _ _ hs.ne', mul_div_assoc]
    _ = Real.sqrt n * (2 * (Real.log n + 1) / n) := by
        rw [hsq]
        ring

/-- **QMC beats MC (the error).** For `f` of bounded variation on `[0,1]`, the van der Corput
QMC error is `o(n^{-1/2})`: `√n · |(1/n) ∑_{i<n} f(φ(i)) - ∫₀¹ f| → 0`. MC has root-mean-square
error exactly `σ(f)/√n`, so it is beaten whenever `σ(f) > 0`. -/
theorem tendsto_sqrt_mul_qmcError_vanDerCorput {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => Real.sqrt n * |qmcEstimate f vanDerCorput n - ∫ t in (0 : ℝ)..1, f t|)
      atTop (𝓝 0) := by
  have h := tendsto_sqrt_mul_vanDerCorput_bound.const_mul (totalVariation f)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have := mul_le_mul_of_nonneg_left (abs_qmcError_vanDerCorput_le hf hn)
    (Real.sqrt_nonneg (n : ℝ))
  calc _ ≤ _ := this
    _ = _ := by ring

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Per-state stacks: departures are balanced (post #3)

Copied from `RQMCMarkov/MarkovDriving` (namespace and imports renamed).

Post #3: "with a separate QMC-generated uniform sequence used for the transitions out of each
state … the departures from each state are balanced, so the empirical transition matrix
converges faster than `O(1/√T)`". In the stack representation (`stackPath P x₀ v`) the `k`-th
departure from `i` goes to `step P i (v i k)`, and that departure goes to `j` iff
`v i k ∈ (cs_{i,j−1}, cs_{ij}]` (`step_lt_iff`: `step P i u < m ↔ u ≤ cs_{i,m}`, valid also at
`u = 0`). So the departures from `i` are a one-dimensional QMC sample of the row `P(i, ·)`, and
their error is controlled by the star discrepancy `D*_N` of the first `N = N_i(T)` points of
stack `i` (Niederreiter 1992, Ch. 2; L'Ecuyer 2016).

**Results** (`N = N_i(T)` departures from `i`, stack points in `[0,1)`).
* `abs_card_step_eq_sub_le`, `abs_transCount_stackPath_sub_le`:
  `|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`.
* `abs_sum_step_sub_le` (discrete Koksma inequality, by summation by parts),
  `abs_departureDiscrepancy_stackPath_le`: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`, where
  `V(g) = stateVariation g = Σ_{j < n−1} |g(j+1) − g(j)|` bounds the total variation of the
  step function `u ↦ g(step P i u)` on `[0,1]` (equal to it when every `p_ij > 0`), and
  `stateVariation_le`: `V(g) ≤ 2 (n − 1) ‖g‖∞`.
* `abs_occCount_stackPath_sub_le`: `|N_s(T) − T π_s| ≤ 2‖h‖∞ + Σ_i V(h) N_i D*_{N_i}(v i)`.
* **Van der Corput stacks** (one copy of the van der Corput sequence, the one-dimensional Sobol
  sequence, for each state): with `L = ⌊log₂ T⌋ + 1`,
  - `abs_transCount_vdc_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2L`;
  - `abs_occCount_vdc_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) L ≤ 2M + 2n(n−1) M L`;
  - `abs_occFreq_vdc_sub_le`: occupation frequency error `≤ (2M + n V(h) L)/T`, i.e.
    `O(log T / T)` (`occFreq_vdc_isBigO`);
  - `abs_empiricalTrans_vdc_sub_le`: empirical transition matrix error
    `|N_ij/N_i − p_ij| ≤ 2(⌊log₂ N_i⌋ + 1)/N_i`, and `empiricalTrans_vdc_isBigO`: it is
    `O(log T / T)` for an irreducible chain (`N_i(T) ≥ T π_i / 2` eventually).
  This is the precise form of "faster than `O(1/√T)`" and "QMC's `O(log T / T)`" (post #3).
-/

namespace RQMCMarkov.ScrambledStacks

open Finset Matrix Filter Asymptotics

variable {n : ℕ}

/-- **The inverse-CDF rule as a threshold**: for `u ≤ 1` and `m ≥ 1`,
`step P i u < m ↔ u ≤ cumProb P i m` (post #3's `u ≤ cs_{i,m}`). This also covers `u = 0`. -/
theorem step_lt_iff {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) {u : ℝ}
    (hu : u ≤ 1) {m : ℕ} (hm : 1 ≤ m) : (step P i u : ℕ) < m ↔ u ≤ cumProb P i m := by
  have hstep : step P i u = (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))).min' (insert_nonempty _ _) := rfl
  constructor
  · intro h
    have hmem := Finset.min'_mem (insert (lastState i)
      (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1))) (insert_nonempty _ _)
    rw [← hstep] at hmem
    rcases mem_insert.1 hmem with hl | hf
    · have hnm : n ≤ m := by
        rw [hl] at h
        simp only [lastState] at h
        omega
      rw [cumProb_of_le P i hnm, hP.sum_eq_one i]
      exact hu
    · exact (mem_filter.1 hf).2.trans (cumProb_mono hP.nonneg i (by omega))
  · intro h
    by_cases hmn : m ≤ n
    · have hj : (⟨m - 1, by omega⟩ : Fin n) ∈ insert (lastState i)
          (univ.filter fun j : Fin n ↦ u ≤ cumProb P i (j + 1)) := by
        refine mem_insert_of_mem (mem_filter.2 ⟨mem_univ _, ?_⟩)
        have e : ((⟨m - 1, by omega⟩ : Fin n) : ℕ) + 1 = m := by
          change m - 1 + 1 = m
          omega
        rw [e]
        exact h
      have hle := Finset.min'_le _ _ hj
      rw [← hstep] at hle
      have hle' : (step P i u : ℕ) ≤ m - 1 := hle
      omega
    · exact lt_of_lt_of_le (step P i u).isLt (by omega)

/-- The number of the first `N` points of `v` whose departure from `i` goes to a state `< m`. -/
noncomputable def departuresBelow (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N m : ℕ) :
    ℕ :=
  ((range N).filter fun k => (step P i (v k) : ℕ) < m).card

/-- For `m ≥ 1` and points in `[0,1)`, `departuresBelow` is the counting function
`#{k < N : v k ≤ cs_{i,m}}`. -/
theorem departuresBelow_eq_countAtMost {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) {m : ℕ} (hm : 1 ≤ m) :
    departuresBelow P i v N m = countAtMost v N (cumProb P i m) := by
  unfold departuresBelow countAtMost
  congr 1
  refine filter_congr fun k hk => ?_
  exact step_lt_iff hP i (hv k (mem_range.1 hk)).2.le hm

/-- **One threshold**: `|#{k < N : step(v k) < m} − N cs_{i,m}| ≤ N D*_N`. -/
theorem abs_departuresBelow_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (m : ℕ) :
    |(departuresBelow P i v N m : ℝ) - N * cumProb P i m| ≤ N * starDiscrepancy v N := by
  have hD := starDiscrepancy_nonneg v N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : departuresBelow P i v 0 m = 0 := by
      unfold departuresBelow
      rw [range_zero, filter_empty, card_empty]
    rw [h0]
    simp only [Nat.cast_zero, zero_mul, sub_zero, abs_zero, le_refl]
  rw [departuresBelow_eq_countAtMost hP i hv hm]
  have ha := cumProb_mem_Icc hP i m
  set a := cumProb P i m with ha_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le ha.2 with ha1 | ha1
  · have hup := countAtMost_div_sub_le_starDiscrepancy v N ha.1 ha1
    have hbelow : countBelow v N a ≤ countAtMost v N a := by
      apply Finset.card_le_card
      intro k hk
      rw [mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.le⟩
    have hloc := localDiscrepancy_le_starDiscrepancy v N ha
    unfold localDiscrepancy at hloc
    have hlow : a - (countBelow v N a : ℝ) / N ≤ starDiscrepancy v N :=
      (neg_le_abs _).trans' (by linarith) |>.trans hloc
    have hb : (countBelow v N a : ℝ) ≤ countAtMost v N a := by exact_mod_cast hbelow
    rw [abs_le]
    constructor
    · have : a - (countAtMost v N a : ℝ) / N ≤ starDiscrepancy v N := by
        have : (countBelow v N a : ℝ) / N ≤ (countAtMost v N a : ℝ) / N :=
          div_le_div_of_nonneg_right hb hNpos.le
        linarith
      have h2 : (N : ℝ) * (a - (countAtMost v N a : ℝ) / N) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left this hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
    · have h2 : (N : ℝ) * ((countAtMost v N a : ℝ) / N - a) ≤ N * starDiscrepancy v N :=
        mul_le_mul_of_nonneg_left hup hNpos.le
      rw [mul_sub, mul_div_cancel₀ _ hNpos.ne'] at h2
      linarith
  · have hall : countAtMost v N a = N := by
      unfold countAtMost
      rw [filter_true_of_mem fun k hk => ?_, card_range]
      rw [ha1]
      exact (hv k (mem_range.1 hk)).2.le
    rw [hall, ha1, mul_one, sub_self, abs_zero]
    positivity

/-- The count of departures to `j` is a difference of two thresholds. -/
theorem card_step_eq_eq_sub (P : Fin n → Fin n → ℝ) (i : Fin n) (v : ℕ → ℝ) (N : ℕ) (j : Fin n) :
    (((range N).filter fun k => step P i (v k) = j).card : ℝ) =
      departuresBelow P i v N (j + 1) - departuresBelow P i v N j := by
  unfold departuresBelow
  rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_boole, ← sum_boole, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : step P i (v k) = j
  · rw [h1]
    simp only [lt_irrefl, Nat.lt_add_one, ite_true, ite_false, add_zero]
  · have h1' : (step P i (v k) : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    by_cases h2 : (step P i (v k) : ℕ) < j
    · have h3 : (step P i (v k) : ℕ) < j + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : ¬ ((step P i (v k) : ℕ) < j + 1) := by omega
      simp only [h1, h2, h3, ite_false, add_zero]

/-- **Balanced departures from one stack**: `|#{k < N : step(v k) = j} − N p_ij| ≤ 2 N D*_N`. -/
theorem abs_card_step_eq_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (j : Fin n) :
    |(((range N).filter fun k => step P i (v k) = j).card : ℝ) - P i j * N| ≤
      2 * (N * starDiscrepancy v N) := by
  rw [card_step_eq_eq_sub]
  have e : (departuresBelow P i v N (j + 1) : ℝ) - departuresBelow P i v N j - P i j * N =
      ((departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i v N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_sub_le hP i hv (j + 1)
  have h2 := abs_departuresBelow_sub_le hP i hv j
  calc _ ≤ |(departuresBelow P i v N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i v N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- A function on the states `Fin n`, extended by `0` to `ℕ`. -/
noncomputable def extendNat (g : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then g ⟨j, h⟩ else 0

/-- The **variation of `g` along the state order** `V(g) = Σ_{j < n−1} |g(j+1) − g(j)|`; it
bounds the total variation on `[0,1]` of the step function `u ↦ g(step P i u)` (with equality
when every `p_ij > 0`). -/
noncomputable def stateVariation (g : Fin n → ℝ) : ℝ :=
  ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|

/-- `0 ≤ V(g)`. -/
theorem stateVariation_nonneg (g : Fin n → ℝ) : 0 ≤ stateVariation g :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- `V(g) ≤ 2 (n − 1) M` when `|g| ≤ M`. -/
theorem stateVariation_le {g : Fin n → ℝ} {M : ℝ} (hM : ∀ j, |g j| ≤ M) :
    stateVariation g ≤ 2 * (n - 1 : ℕ) * M := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold stateVariation
    rw [Nat.zero_sub, range_zero, sum_empty, Nat.cast_zero, mul_zero, zero_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ⟨0, hn⟩)
  have hext : ∀ j, |extendNat g j| ≤ M := by
    intro j
    unfold extendNat
    split_ifs with h
    · exact hM _
    · rw [abs_zero]
      exact hM0
  unfold stateVariation
  calc ∑ j ∈ range (n - 1), |extendNat g (j + 1) - extendNat g j|
      ≤ ∑ _j ∈ range (n - 1), 2 * M := sum_le_sum fun j _ => by
        have := abs_sub (extendNat g (j + 1)) (extendNat g j)
        linarith [hext (j + 1), hext j]
    _ = 2 * (n - 1 : ℕ) * M := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Summation by parts.** If `B 0 = 0` then
`Σ_{j ≤ m} f_j (B_{j+1} − B_j) = f_m B_{m+1} − Σ_{j < m} (f_{j+1} − f_j) B_{j+1}`. -/
theorem sum_mul_sub_eq_abel (f B : ℕ → ℝ) (hB : B 0 = 0) (m : ℕ) :
    ∑ j ∈ range (m + 1), f j * (B (j + 1) - B j) =
      f m * B (m + 1) - ∑ j ∈ range m, (f (j + 1) - f j) * B (j + 1) := by
  induction m with
  | zero => rw [sum_range_one, range_zero, sum_empty, hB, sub_zero, sub_zero]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- **Discrete Koksma inequality for one stack**:
`|Σ_{k<N} g(step P i (v k)) − N (Pg)(i)| ≤ V(g) · N · D*_N`. -/
theorem abs_sum_step_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {v : ℕ → ℝ} {N : ℕ} (hv : InUnitIco v N) (g : Fin n → ℝ) :
    |∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i)| ≤
      stateVariation g * (N * starDiscrepancy v N) := by
  -- `B m = #{step < m} − N cs_m`
  set B : ℕ → ℝ := fun m => (departuresBelow P i v N m : ℝ) - N * cumProb P i m with hBdef
  have hB0 : B 0 = 0 := by
    have h0 : departuresBelow P i v N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    simp only [hBdef, h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hBn : B n = 0 := by
    have hn : departuresBelow P i v N n = N := by
      unfold departuresBelow
      rw [filter_true_of_mem fun k _ => (step P i (v k)).isLt, card_range]
    simp only [hBdef, hn, cumProb_of_le P i le_rfl, hP.sum_eq_one i, mul_one, sub_self]
  have hBb : ∀ m, |B m| ≤ N * starDiscrepancy v N := abs_departuresBelow_sub_le hP i hv
  -- the sum as `Σ_j g_j (B(j+1) − B(j))`
  have e1 : ∑ k ∈ range N, (g (step P i (v k)) - (P *ᵥ g) i) =
      ∑ j : Fin n, g j * (B (j + 1) - B j) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [← sum_fiberwise (range N) (fun k => step P i (v k))]
    have e2 : ∀ j : Fin n, ∑ k ∈ (range N).filter (fun k => step P i (v k) = j),
        g (step P i (v k)) = g j * (((range N).filter fun k => step P i (v k) = j).card : ℝ) :=
      fun j => by
        rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul,
          mul_comm]
    rw [sum_congr rfl fun j _ => e2 j]
    have e3 : (N : ℝ) * (P *ᵥ g) i = ∑ j : Fin n, g j * (P i j * N) := by
      simp only [mulVec, dotProduct, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e3, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sub, card_step_eq_eq_sub]
    congr 1
    simp only [hBdef]
    rw [cumProb_succ]
    ring
  rw [e1]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [Finset.univ_eq_empty, sum_empty, abs_zero]
    exact mul_nonneg (stateVariation_nonneg g)
      (mul_nonneg (Nat.cast_nonneg _) (starDiscrepancy_nonneg v N))
  -- to `ℕ`-indexed sums, then summation by parts
  have e4 : ∑ j : Fin n, g j * (B (j + 1) - B j) =
      ∑ j ∈ range n, extendNat g j * (B (j + 1) - B j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extendNat g j * (B (j + 1) - B j)) n]
    refine sum_congr rfl fun j _ => ?_
    simp only [extendNat, j.isLt, ↓reduceDIte, Fin.eta]
  rw [e4]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_mul_sub_eq_abel _ B hB0 m, hBn, mul_zero, zero_sub, abs_neg]
  unfold stateVariation
  rw [Nat.add_sub_cancel, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBb (j + 1)) (abs_nonneg _)

variable {P : Fin n → Fin n → ℝ}

/-- **Stacks balance the transitions** (post #3): in a stack path with stack points in `[0,1)`,
`|N_ij(T) − p_ij N_i(T)| ≤ 2 N D*_N(v i)`, `N = N_i(T)`. -/
theorem abs_transCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ v) i j T : ℝ) - P i j * occCount (stackPath P x₀ v) i T| ≤
      2 * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  rw [transCount_stackDrive]
  exact abs_card_step_eq_sub_le hP i (fun k _ => hv i k) j

/-- **Departure discrepancy of a stack path**: `|D_i(g, T)| ≤ V(g) · N · D*_N(v i)`. -/
theorem abs_departureDiscrepancy_stackPath_le (hP : IsStochastic P) (x₀ : Fin n)
    {v : Fin n → ℕ → ℝ} (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) (g : Fin n → ℝ) (i : Fin n)
    (T : ℕ) : |departureDiscrepancy P g (stackPath P x₀ v) i T| ≤
      stateVariation g * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) := by
  exact (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ v i T)).trans_le
    (abs_sum_step_sub_le hP i (fun k _ => hv i k) g)

/-- **Occupation error of a stack path**: `|N_s(T) − T π_s| ≤ 2M + Σ_i V(h) N_i D*_{N_i}(v i)`,
for `h − Ph = 1_{s} − π_s`, `|h| ≤ M`. -/
theorem abs_occCount_stackPath_sub_le (hP : IsStochastic P) (x₀ : Fin n) {v : Fin n → ℕ → ℝ}
    (hv : ∀ i k, v i k ∈ Set.Ico (0 : ℝ) 1) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ v) s T : ℝ) - T * c| ≤
      2 * M + ∑ i, stateVariation h * (occCount (stackPath P x₀ v) i T *
        starDiscrepancy (v i) (occCount (stackPath P x₀ v) i T)) :=
  (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl
    (sum_le_sum fun i _ => abs_departureDiscrepancy_stackPath_le hP x₀ hv h i T))

/-- `N D*_N(φ) ≤ ⌊log₂ T⌋ + 1` for the van der Corput sequence `φ` and `N ≤ T`. -/
theorem mul_starDiscrepancy_vdc_le {N T : ℕ} (hNT : N ≤ T) :
    N * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 T : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, zero_mul]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := starDiscrepancy_vanDerCorput_le hN
  have h2 : (N : ℝ) * starDiscrepancy vanDerCorput N ≤ (Nat.log 2 N : ℝ) + 1 := by
    rw [le_div_iff₀ hNpos] at h1
    linarith
  have h3 : (Nat.log 2 N : ℝ) ≤ Nat.log 2 T := by exact_mod_cast Nat.log_mono_right hNT
  linarith

/-- **Van der Corput stacks balance the transitions**: `|N_ij(T) − p_ij N_i(T)| ≤
2 (⌊log₂ T⌋ + 1)`. -/
theorem abs_transCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ fun _ => vanDerCorput) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  (abs_transCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) i j T).trans
    (mul_le_mul_of_nonneg_left (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) zero_le_two)

/-- **Van der Corput stacks: occupation error `O(log T)`**:
`|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`. -/
theorem abs_occCount_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (T : ℕ) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
  refine (abs_occCount_stackPath_sub_le hP x₀ (fun _ k => vanDerCorput_mem_Ico k) hh hM T).trans
    (add_le_add le_rfl ?_)
  calc ∑ i, stateVariation h * (occCount (stackPath P x₀ fun _ => vanDerCorput) i T *
        starDiscrepancy vanDerCorput (occCount (stackPath P x₀ fun _ => vanDerCorput) i T))
      ≤ ∑ _i : Fin n, stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (mul_starDiscrepancy_vdc_le (occCount_le _ _ _)) (stateVariation_nonneg h)
    _ = n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Van der Corput stacks: occupation frequency error `O(log T / T)`** (post #3, "QMC's
`O(log T / T)`"): `|N_s(T)/T − π_s| ≤ (2M + n V(h) (⌊log₂ T⌋ + 1))/T`. -/
theorem abs_occFreq_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) {T : ℕ} (hT : 0 < T) :
    |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c| ≤
      (2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm c]
  exact abs_occCount_vdc_sub_le hP x₀ hh hM T

/-- **Van der Corput stacks: empirical transition matrix error**:
`|N_ij(T)/N_i(T) − p_ij| ≤ 2 (⌊log₂ T⌋ + 1)/N_i(T)` whenever `N_i(T) > 0`. -/
theorem abs_empiricalTrans_vdc_sub_le (hP : IsStochastic P) (x₀ : Fin n) (i j : Fin n) {T : ℕ}
    (hN : 0 < occCount (stackPath P x₀ fun _ => vanDerCorput) i T) :
    |(transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) / occCount (stackPath P x₀ fun _ => vanDerCorput) i T := by
  set N := occCount (stackPath P x₀ fun _ => vanDerCorput) i T
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos, ← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos, sub_mul,
    div_mul_cancel₀ _ hNpos.ne']
  exact abs_transCount_vdc_sub_le hP x₀ i j T

/-- `1 ≤ log x` for `x ≥ 3`. -/
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `(⌊log₂ T⌋ + 1) / T`-type bounds are `O(log T / T)`: if `|e T| ≤ (A + B (⌊log₂ T⌋ + 1))/T`
for `T > 0`, with `A, B ≥ 0`, then `e = O(log T / T)`. -/
theorem isBigO_log_div_of_le {e : ℕ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : ∀ T : ℕ, 0 < T → |e T| ≤ (A + B * ((Nat.log 2 T : ℝ) + 1)) / T) :
    e =O[atTop] fun T : ℕ => Real.log T / T := by
  refine IsBigO.of_bound (A + 4 * B) ?_
  filter_upwards [eventually_ge_atTop 3] with T hT
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ Real.log T) (Nat.cast_nonneg T)),
    mul_div_assoc']
  refine (he T hTpos).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have h3 : B * ((Nat.log 2 T : ℝ) + 1) ≤ B * (2 * (Real.log T + 1)) :=
    mul_le_mul_of_nonneg_left h2 hB
  nlinarith [mul_le_mul_of_nonneg_left hlog hA, mul_le_mul_of_nonneg_left hlog hB]

/-- **Van der Corput stacks: the occupation frequencies converge at `O(log T / T)`**
(post #3's "QMC's `O(log T / T)`"). -/
theorem occFreq_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) / T - c) =O[atTop]
      fun T : ℕ => Real.log T / T :=
  isBigO_log_div_of_le (by linarith [(abs_nonneg _).trans (hM s)])
    (mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h))
    fun _ hT => abs_occFreq_vdc_sub_le hP x₀ hh hM hT

/-- **Van der Corput stacks: the empirical transition matrix converges at `O(log T / T)`**, for
a state `i` with `π_i = c > 0` (post #3, "faster than `O(1/√T)`"). The number of departures
`N_i(T)` is at least `T c / 2` eventually, by the occupation bound. -/
theorem empiricalTrans_vdc_isBigO (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {i : Fin n} {c M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - c)
    (hM : ∀ k, |h k| ≤ M) (hc : 0 < c) (j : Fin n) :
    (fun T : ℕ => (transCount (stackPath P x₀ fun _ => vanDerCorput) i j T : ℝ) /
        occCount (stackPath P x₀ fun _ => vanDerCorput) i T - P i j) =O[atTop]
      fun T : ℕ => Real.log T / T := by
  set x := stackPath P x₀ fun _ => vanDerCorput with hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM i)
  set V := stateVariation h
  have hV0 : 0 ≤ (n : ℝ) * V := mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h)
  -- eventually `log T ≤ (c / (8 (n V + 1))) T` and `2M + 2nV ≤ T c / 4`
  have hlogo := (Real.isLittleO_log_id_atTop.bound (c := c / (8 * ((n : ℝ) * V + 1)))
    (by positivity))
  have hlogN : ∀ᶠ T : ℕ in atTop,
      Real.log T ≤ c / (8 * ((n : ℝ) * V + 1)) * T := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlogo, eventually_ge_atTop 1]
      with T hT hT1
    have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hTR),
      abs_of_nonneg (by linarith)] at hT
  have hbig : ∀ᶠ T : ℕ in atTop, 4 * (2 * M + 2 * ((n : ℝ) * V)) / c ≤ T :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine IsBigO.of_bound (16 / c) ?_
  filter_upwards [hlogN, hbig, eventually_ge_atTop 3] with T hlogT hbigT hT3
  have hTpos : 0 < T := by omega
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT3
  have hTR0 : (0 : ℝ) < T := by linarith
  have hlog1 := one_le_log_of_three_le hTR
  have h2 := natLog_two_add_one_le hTpos
  -- the occupation bound gives `N_i(T) ≥ T c / 2`
  have hocc := abs_occCount_vdc_sub_le hP x₀ hh hM T
  have hNlow : T * c / 2 ≤ (occCount x i T : ℝ) := by
    have h4 : (n : ℝ) * V * ((Nat.log 2 T : ℝ) + 1) ≤ (n : ℝ) * V * (2 * (Real.log T + 1)) :=
      mul_le_mul_of_nonneg_left h2 hV0
    have h5 : (n : ℝ) * V * (2 * Real.log T) ≤ T * c / 4 := by
      have h6 : (n : ℝ) * V * Real.log T ≤ ((n : ℝ) * V + 1) * Real.log T :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h7 : ((n : ℝ) * V + 1) * Real.log T ≤
          ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) :=
        mul_le_mul_of_nonneg_left hlogT (by linarith)
      have h8 : ((n : ℝ) * V + 1) * (c / (8 * ((n : ℝ) * V + 1)) * T) = T * c / 8 := by
        field_simp
      linarith
    have h9 : 2 * M + 2 * ((n : ℝ) * V) ≤ T * c / 4 := by
      rw [div_le_iff₀ hc] at hbigT
      linarith
    have := (abs_le.1 hocc).1
    nlinarith
  have hNpos' : (0 : ℝ) < occCount x i T := lt_of_lt_of_le (by positivity) hNlow
  have hNpos : 0 < occCount x i T := by exact_mod_cast hNpos'
  have hb := abs_empiricalTrans_vdc_sub_le hP x₀ i j hNpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hTR0.le)]
  refine hb.trans ?_
  rw [div_le_iff₀ hNpos']
  have h10 : 2 * ((Nat.log 2 T : ℝ) + 1) ≤ 8 * Real.log T := by linarith
  have h11 : 16 / c * (Real.log T / T) * (T * c / 2) = 8 * Real.log T := by
    field_simp
    ring
  have h12 : 0 ≤ 16 / c * (Real.log T / T) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hNlow h12]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Per-state scrambled van der Corput stacks: definitions (post #3, codes (ii) and (iii))

Post #3, codes (ii) and (iii): "one Sobol sequence per state + random digital shift" and "one
Sobol sequence per state + Owen scrambling", used as stacks (the `k`-th departure from state `i`
uses point `k` of stack `i`). In one dimension the Sobol sequence is the base-2 van der Corput
sequence, whose point `k` has binary digit `j + 1` equal to bit `j` of `k`.

**Model (Owen's nested uniform scramble of all digits, Owen 1997).** A flip table
`f : ℕ → ℕ → Bool` flips digit `j + 1` of point `k` by `f j (k % 2^j)`: the flip depends on the
original digits `1, …, j` (the node `k % 2^j` of the binary tree). The scrambled point is
`scrambledVdc f k = Σ_j d_j / 2^(j+1)` with `d_j = scrambledDigit f k j = bit_j(k) xor
f j (k % 2^j)`. All digits are scrambled, also those beyond the bit length of `k` (there the node
is `k` itself), so there is no truncation. A **digital shift** is a table `shiftTable e` with
`f j p = e j`. A state space `Fin n` has one table per state, `f : Fin n → ℕ → ℕ → Bool`, and
stacks `scrambledStack f i k = scrambledVdc (f i) k`.

**Probability spaces.** `owenMeasure n` is the product of fair coins (`fairCoin`) on
`Fin n × ℕ × ℕ` (state, depth, node; nodes `p ≥ 2^j` are unused) with table `owenTable ω`;
`shiftMeasure n` is the product of fair coins on `Fin n × ℕ` with table `shiftFlips ω`. The
tables of different states use disjoint coordinates, so the stacks are independent.

## Main results

* `binaryVal b = Σ_j b_j / 2^(j+1)` and `digitPrefix b m` (the first `m` digits as a number):
  `binaryVal_eq_digitPrefix_add`, `digitPrefix_div_le_binaryVal`,
  `binaryVal_le_digitPrefix_add_one_div`
  (each point lies in the closed dyadic cell of its first `m` digits), `digitPrefix_lt`,
  `digitPrefix_eq_iff` (the digits of `digitPrefix` are the `testBit`s), `digitPrefix_congr`,
  `eq_of_digitPrefix_eq`.
* `NotEventuallyConst b`: the digits are not eventually constant. Then the point is in the open
  cell (`digitPrefix_div_lt_binaryVal`, `binaryVal_lt_digitPrefix_add_one_div`) and is not a
  dyadic rational (`binaryVal_ne_dyadic`), in particular not `0` or `1`.
* `scrambledVdc_mem_Icc`: every scrambled point lies in `[0, 1]`, for every flip table.
* `IsGoodTable f`: no stack digit sequence is eventually constant (no stack point is a dyadic
  rational, `scrambledStack_ne_dyadic`). `ae_isGoodTable_owen`, `ae_isGoodTable_shift`: this
  event has probability one under both randomisations.
* `infinitePi_xor_cylinder`: fixing `m` digits `xor (c j) (ω (g j))` (injective `g`) has
  probability `2^{-m}`; `measure_digitPrefix_eq`, `measure_digitPrefix_lt`;
  `map_binaryVal_xor_eq_uniformIco`: such a digit sequence gives a `U[0,1)` point.
* `map_scrambledStack_owen`, `map_scrambledStack_shift` (post #2's requirement (i)): every stack
  point is uniform on `[0,1)` under Owen scrambling and under the digital shift;
  `owen_digitPrefix_eq`, `shift_digitPrefix_eq`: its first `m` scrambled digits are uniform.
* Measurability: `measurable_binaryVal`, `measurable_scrambledStack_owen`,
  `measurable_scrambledStack_shift`, `measurable_stackPath_restrict_of`, `measurable_stackPath_of`,
  `measurable_occCount_of`, `measurable_transCount_of` (the path coordinates and counts are
  random variables for any measurable family of stacks).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory Finset Filter Topology

variable {n : ℕ}

/-! ### Binary expansions -/

/-- The real number `Σ_j b_j / 2^(j+1)` with binary digits `b_0, b_1, …` (digit `j + 1` after
the binary point is `b j`). -/
noncomputable def binaryVal (b : ℕ → Bool) : ℝ := ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1)

/-- A digit term is at most `(1/2)^j / 2`. -/
theorem digitTerm_le (b : ℕ → Bool) (j : ℕ) :
    (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) ≤ 1 / 2 / 2 ^ j := by
  have h : (if b j then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  rw [div_le_div_iff₀ h2 (by positivity), pow_succ]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j]

/-- A digit term is nonnegative. -/
theorem digitTerm_nonneg (b : ℕ → Bool) (j : ℕ) :
    0 ≤ (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) := by
  have h : (0 : ℝ) ≤ if b j then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  positivity

/-- The digit series is summable. -/
theorem summable_digitTerm (b : ℕ → Bool) :
    Summable fun j => (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) :=
  Summable.of_nonneg_of_le (digitTerm_nonneg b) (digitTerm_le b) (summable_geometric_two' 1)

/-- `0 ≤ binaryVal b`. -/
theorem binaryVal_nonneg (b : ℕ → Bool) : 0 ≤ binaryVal b :=
  tsum_nonneg (digitTerm_nonneg b)

/-- `binaryVal b ≤ 1`. -/
theorem binaryVal_le_one (b : ℕ → Bool) : binaryVal b ≤ 1 := by
  unfold binaryVal
  calc ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) ≤ ∑' j : ℕ, (1 : ℝ) / 2 / 2 ^ j :=
        (summable_digitTerm b).tsum_le_tsum (digitTerm_le b) (summable_geometric_two' 1)
    _ = 1 := tsum_geometric_two' 1

/-- `binaryVal b > 0` if some digit is `1`. -/
theorem binaryVal_pos {b : ℕ → Bool} (h : ∃ j, b j = true) : 0 < binaryVal b := by
  obtain ⟨j, hj⟩ := h
  refine (summable_digitTerm b).tsum_pos (digitTerm_nonneg b) j ?_
  simp only [hj, ite_true]
  positivity

/-- `binaryVal b < 1` if some digit is `0`. -/
theorem binaryVal_lt_one {b : ℕ → Bool} (h : ∃ j, b j = false) : binaryVal b < 1 := by
  obtain ⟨j, hj⟩ := h
  unfold binaryVal
  calc ∑' j, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) < ∑' j : ℕ, (1 : ℝ) / 2 / 2 ^ j := by
        refine (summable_digitTerm b).tsum_lt_tsum (digitTerm_le b) (i := j) ?_
          (summable_geometric_two' 1)
        simp only [hj, Bool.false_eq_true, ite_false, zero_div]
        positivity
    _ = 1 := tsum_geometric_two' 1

/-- The first `m` digits of `b` as a natural number (`b 0` is the most significant):
`digitPrefix b (m + 1) = 2 digitPrefix b m + b_m`. -/
def digitPrefix (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * digitPrefix b m + if b m then 1 else 0

/-- `digitPrefix b m < 2^m`. -/
theorem digitPrefix_lt (b : ℕ → Bool) (m : ℕ) : digitPrefix b m < 2 ^ m := by
  induction m with
  | zero => simp [digitPrefix]
  | succ m ih =>
    have h : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [digitPrefix, pow_succ]
    omega

/-- `digitPrefix` depends only on the first `m` digits. -/
theorem digitPrefix_congr {b b' : ℕ → Bool} {m : ℕ} (h : ∀ j < m, b j = b' j) :
    digitPrefix b m = digitPrefix b' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [digitPrefix]
    rw [ih fun j hj => h j (by omega), h m (by omega)]

/-- Equal prefixes have equal digits. -/
theorem eq_of_digitPrefix_eq {b b' : ℕ → Bool} {m : ℕ} (h : digitPrefix b m = digitPrefix b' m) :
    ∀ j < m, b j = b' j := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    simp only [digitPrefix] at h
    have hb : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hb' : (if b' m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h1 : digitPrefix b m = digitPrefix b' m := by omega
    have h2 : (if b m then 1 else 0) = (if b' m then 1 else 0) := by omega
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h1 j hj
    · cases hbj : b j <;> cases hbj' : b' j <;> simp_all

/-- **The digits of `digitPrefix`**: `digitPrefix b m = d` iff `d < 2^m` and the digits
`b 0, …, b (m-1)` are the bits `m - 1, …, 0` of `d`. -/
theorem digitPrefix_eq_iff (b : ℕ → Bool) (m d : ℕ) :
    digitPrefix b m = d ↔ d < 2 ^ m ∧ ∀ j < m, b j = d.testBit (m - 1 - j) := by
  induction m generalizing d with
  | zero =>
    simp only [digitPrefix, pow_zero, Nat.lt_one_iff, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, and_true]
    exact eq_comm
  | succ m ih =>
    have hb : (if b m then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hbit : ((if b m then 1 else 0) = d % 2) ↔ b m = d.testBit 0 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> cases b m <;> simp [h]
    simp only [digitPrefix]
    constructor
    · intro h
      have hd2 : digitPrefix b m = d / 2 := by omega
      have hm2 : (if b m then 1 else 0) = d % 2 := by omega
      refine ⟨h ▸ digitPrefix_lt b (m + 1), fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have e : m + 1 - 1 - j = (m - 1 - j) + 1 := by omega
        rw [e, ← Nat.testBit_div_two, ← hd2]
        exact ((ih (digitPrefix b m)).1 rfl).2 j hj
      · have e : j + 1 - 1 - j = 0 := by omega
        rw [e]
        exact hbit.1 hm2
    · rintro ⟨hd, hdig⟩
      have hm2 : (if b m then 1 else 0) = d % 2 := by
        refine hbit.2 ?_
        have := hdig m (by omega)
        rwa [show m + 1 - 1 - m = 0 by omega] at this
      have hd2 : digitPrefix b m = d / 2 := by
        refine (ih (d / 2)).2 ⟨by rw [pow_succ] at hd; omega, fun j hj => ?_⟩
        rw [Nat.testBit_div_two, hdig j (by omega)]
        congr 1
        omega
      rw [hd2, hm2]
      exact Nat.div_add_mod d 2

/-- The first `m` digit terms sum to `digitPrefix b m / 2^m`. -/
theorem sum_digitTerm_eq_digitPrefix (b : ℕ → Bool) (m : ℕ) :
    ∑ j ∈ range m, (if b j then (1 : ℝ) else 0) / 2 ^ (j + 1) = digitPrefix b m / 2 ^ m := by
  induction m with
  | zero => simp [digitPrefix]
  | succ m ih =>
    rw [sum_range_succ, ih]
    simp only [digitPrefix, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    cases b m <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_zero,
      Nat.cast_one] <;> field_simp <;> ring

/-- **Cell decomposition**: `binaryVal b = (digitPrefix b m + binaryVal (b (· + m))) / 2^m`. -/
theorem binaryVal_eq_digitPrefix_add (b : ℕ → Bool) (m : ℕ) :
    binaryVal b = (digitPrefix b m + binaryVal fun j => b (j + m)) / 2 ^ m := by
  unfold binaryVal
  rw [← (summable_digitTerm b).sum_add_tsum_nat_add m, sum_digitTerm_eq_digitPrefix, add_div]
  congr 1
  rw [← tsum_div_const]
  refine tsum_congr fun j => ?_
  rw [div_div, ← pow_add]
  congr 2
  ring

/-- The point lies above the left end of its level-`m` cell. -/
theorem digitPrefix_div_le_binaryVal (b : ℕ → Bool) (m : ℕ) :
    (digitPrefix b m : ℝ) / 2 ^ m ≤ binaryVal b := by
  rw [binaryVal_eq_digitPrefix_add b m]
  have := binaryVal_nonneg fun j => b (j + m)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The point lies below the right end of its level-`m` cell. -/
theorem binaryVal_le_digitPrefix_add_one_div (b : ℕ → Bool) (m : ℕ) :
    binaryVal b ≤ ((digitPrefix b m : ℝ) + 1) / 2 ^ m := by
  rw [binaryVal_eq_digitPrefix_add b m]
  have := binaryVal_le_one fun j => b (j + m)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The digit sequence `b` is **not eventually constant**: beyond every position there is a
`1` and a `0`. -/
def NotEventuallyConst (b : ℕ → Bool) : Prop :=
  ∀ J, (∃ j, J ≤ j ∧ b j = true) ∧ ∃ j, J ≤ j ∧ b j = false

/-- Shifting the digits keeps them not eventually constant. -/
theorem NotEventuallyConst.shift {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    NotEventuallyConst fun j => b (j + m) := by
  intro J
  obtain ⟨⟨j, hj, hbj⟩, ⟨j', hj', hbj'⟩⟩ := hb (J + m)
  refine ⟨⟨j - m, by omega, ?_⟩, ⟨j' - m, by omega, ?_⟩⟩
  · change b (j - m + m) = true
    rw [Nat.sub_add_cancel (by omega)]
    exact hbj
  · change b (j' - m + m) = false
    rw [Nat.sub_add_cancel (by omega)]
    exact hbj'

/-- With digits not eventually constant the point is strictly inside its level-`m` cell (left). -/
theorem digitPrefix_div_lt_binaryVal {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    (digitPrefix b m : ℝ) / 2 ^ m < binaryVal b := by
  rw [binaryVal_eq_digitPrefix_add b m]
  obtain ⟨⟨j, -, hj⟩, -⟩ := hb.shift m 0
  have := binaryVal_pos (b := fun j => b (j + m)) ⟨j, hj⟩
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- With digits not eventually constant the point is strictly inside its level-`m` cell
(right). -/
theorem binaryVal_lt_digitPrefix_add_one_div {b : ℕ → Bool} (hb : NotEventuallyConst b) (m : ℕ) :
    binaryVal b < ((digitPrefix b m : ℝ) + 1) / 2 ^ m := by
  rw [binaryVal_eq_digitPrefix_add b m]
  obtain ⟨-, ⟨j, -, hj⟩⟩ := hb.shift m 0
  have := binaryVal_lt_one (b := fun j => b (j + m)) ⟨j, hj⟩
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- **No dyadic rationals**: digits that are not eventually constant never give `a / 2^m`
(in particular never `0` or `1`). -/
theorem binaryVal_ne_dyadic {b : ℕ → Bool} (hb : NotEventuallyConst b) (a : ℤ) (m : ℕ) :
    binaryVal b ≠ a / 2 ^ m := by
  intro h
  have h1 := digitPrefix_div_lt_binaryVal hb m
  have h2 := binaryVal_lt_digitPrefix_add_one_div hb m
  rw [h] at h1 h2
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_div_iff_of_pos_right hp] at h1 h2
  have h1' : ((digitPrefix b m : ℕ) : ℤ) < a := by exact_mod_cast h1
  have h2' : a < ((digitPrefix b m : ℕ) : ℤ) + 1 := by exact_mod_cast h2
  omega

/-! ### Scrambled van der Corput points -/

/-- **Owen-scrambled digit** `j` (digit `j + 1` after the binary point) of the van der Corput
point `k` under the flip table `f`: `bit_j(k) xor f j (k % 2^j)`. -/
def scrambledDigit (f : ℕ → ℕ → Bool) (k j : ℕ) : Bool := xor (k.testBit j) (f j (k % 2 ^ j))

/-- The **scrambled van der Corput point** `k`: `Σ_j scrambledDigit f k j / 2^(j+1)`. -/
noncomputable def scrambledVdc (f : ℕ → ℕ → Bool) (k : ℕ) : ℝ := binaryVal (scrambledDigit f k)

/-- `scrambledVdc` written out as a series. -/
theorem scrambledVdc_eq_tsum (f : ℕ → ℕ → Bool) (k : ℕ) :
    scrambledVdc f k = ∑' j, (if scrambledDigit f k j then (1 : ℝ) else 0) / 2 ^ (j + 1) := rfl

/-- The **digital-shift** flip table: digit `j + 1` is flipped by `e j`, at every node. -/
def shiftTable (e : ℕ → Bool) : ℕ → ℕ → Bool := fun j _ => e j

/-- Under a digital shift, digit `j` is `bit_j(k) xor e j`. -/
theorem scrambledDigit_shiftTable (e : ℕ → Bool) (k j : ℕ) :
    scrambledDigit (shiftTable e) k j = xor (k.testBit j) (e j) := rfl

/-- Every scrambled point lies in `[0, 1]`, for every flip table. -/
theorem scrambledVdc_mem_Icc (f : ℕ → ℕ → Bool) (k : ℕ) : scrambledVdc f k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨binaryVal_nonneg _, binaryVal_le_one _⟩

/-- The **stacks**: stack `i` is the scrambled van der Corput sequence with the table `f i`. -/
noncomputable def scrambledStack (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (k : ℕ) : ℝ :=
  scrambledVdc (f i) k

/-- Stack points lie in `[0, 1]`. -/
theorem scrambledStack_mem_Icc (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (k : ℕ) :
    scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 :=
  scrambledVdc_mem_Icc _ _

/-- The **good event**: no digit sequence of any stack point is eventually constant. -/
def IsGoodTable (f : Fin n → ℕ → ℕ → Bool) : Prop :=
  ∀ i k, NotEventuallyConst (scrambledDigit (f i) k)

/-- On the good event no stack point is a dyadic rational (nor `0`, nor `1`). -/
theorem scrambledStack_ne_dyadic {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin n)
    (k : ℕ) (a : ℤ) (m : ℕ) : scrambledStack f i k ≠ a / 2 ^ m :=
  binaryVal_ne_dyadic (hf i k) a m

/-- On the good event every stack point lies in `(0, 1)`. -/
theorem scrambledStack_mem_Ioo {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin n)
    (k : ℕ) : scrambledStack f i k ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 := digitPrefix_div_lt_binaryVal (hf i k) 0
  have h1 := binaryVal_lt_digitPrefix_add_one_div (hf i k) 0
  simp only [digitPrefix, Nat.cast_zero, pow_zero, div_one, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-! ### The probability spaces -/

/-- A fair coin on `Bool`. -/
noncomputable abbrev fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Each face of the fair coin has probability `1/2`. -/
theorem fairCoin_singleton (b : Bool) : fairCoin {b} = 2⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  rfl

/-- **Owen's measure**: i.i.d. fair coins indexed by (state, depth, node). -/
noncomputable abbrev owenMeasure (n : ℕ) : Measure (Fin n × ℕ × ℕ → Bool) :=
  Measure.infinitePi fun _ => fairCoin

/-- The flip tables of a realisation `ω` of Owen's coins. -/
def owenTable (ω : Fin n × ℕ × ℕ → Bool) : Fin n → ℕ → ℕ → Bool := fun i j p => ω (i, j, p)

/-- **The digital-shift measure**: i.i.d. fair coins indexed by (state, depth). -/
noncomputable abbrev shiftMeasure (n : ℕ) : Measure (Fin n × ℕ → Bool) :=
  Measure.infinitePi fun _ => fairCoin

/-- The (digital-shift) flip tables of a realisation `ω`. -/
def shiftFlips (ω : Fin n × ℕ → Bool) : Fin n → ℕ → ℕ → Bool :=
  fun i => shiftTable fun j => ω (i, j)

/-- `owenMeasure n` is a probability measure. -/
theorem isProbabilityMeasure_owenMeasure (n : ℕ) : IsProbabilityMeasure (owenMeasure n) :=
  inferInstance

/-- `shiftMeasure n` is a probability measure. -/
theorem isProbabilityMeasure_shiftMeasure (n : ℕ) : IsProbabilityMeasure (shiftMeasure n) :=
  inferInstance

/-- Under Owen's measure, digit `j` of point `k` of stack `i` is `bit_j(k) xor ω (i, j, k % 2^j)`.
-/
theorem scrambledDigit_owenTable (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (k j : ℕ) :
    scrambledDigit (owenTable ω i) k j = xor (k.testBit j) (ω (i, j, k % 2 ^ j)) := rfl

/-- Under the digital shift, digit `j` of point `k` of stack `i` is `bit_j(k) xor ω (i, j)`. -/
theorem scrambledDigit_shiftFlips (ω : Fin n × ℕ → Bool) (i : Fin n) (k j : ℕ) :
    scrambledDigit (shiftFlips ω i) k j = xor (k.testBit j) (ω (i, j)) := rfl

/-- **Cylinders of an i.i.d. product** (as `infinitePi_setOf_forall_mem` of `MarkovDriving`):
for injective coordinates `c`, `P(w (c t) ∈ B t, t < T) = ∏_{t<T} ν (B t)`. -/
theorem infinitePi_setOf_forall_mem' {ι α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {c : ℕ → ι} (hc : Function.Injective c) {B : ℕ → Set α}
    (hB : ∀ t, MeasurableSet (B t)) (T : ℕ) :
    Measure.infinitePi (fun _ : ι ↦ ν) {w | ∀ t < T, w (c t) ∈ B t} = ∏ t ∈ range T, ν (B t) := by
  classical
  set B' : ι → Set α := fun p ↦ {a | ∀ t < T, c t = p → a ∈ B t} with hB'def
  have hset : {w : ι → α | ∀ t < T, w (c t) ∈ B t} = Set.pi ↑((range T).image c) B' := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range, hB'def]
    constructor
    · rintro h p ⟨t', ht', rfl⟩ t ht hct
      rw [← hc hct] at ht' ⊢
      exact h t ht
    · intro h t ht
      exact h (c t) ⟨t, ht, rfl⟩ t ht rfl
  have hB'c : ∀ t < T, B' (c t) = B t := by
    intro t ht
    ext a
    simp only [hB'def, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h t ht rfl
    · intro h t' _ hct
      rw [hc hct]
      exact h
  have hmeas : ∀ p, MeasurableSet (B' p) := by
    intro p
    have : B' p = ⋂ (t : ℕ) (_ : t < T) (_ : c t = p), B t := by
      ext a
      simp only [hB'def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun t ↦ .iInter fun _ ↦ .iInter fun _ ↦ hB t
  rw [hset, Measure.infinitePi_pi (fun _ : ι ↦ ν) fun p _ ↦ hmeas p,
    Finset.prod_image fun a _ b _ h ↦ hc h]
  exact Finset.prod_congr rfl fun t ht ↦ by rw [hB'c t (Finset.mem_range.1 ht)]

/-- Digit cylinders are measurable. -/
theorem measurableSet_xor_cylinder {ι : Type*} (g : ℕ → ι) (c w : ℕ → Bool) (m : ℕ) :
    MeasurableSet {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} := by
  have : {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      ⋂ (j : ℕ) (_ : j < m), (fun ω : ι → Bool => ω (g j)) ⁻¹' {xor (c j) (w j)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    cases c j <;> cases w j <;> cases ω (g j) <;> simp
  rw [this]
  exact MeasurableSet.iInter fun j => .iInter fun _ =>
    measurable_pi_apply (g j) (measurableSet_singleton _)

/-- **Digit cylinders have probability `2^{-m}`**: if the digits are `xor (c j) (ω (g j))` with
`g` injective, fixing the first `m` of them has probability `2^{-m}`. -/
theorem infinitePi_xor_cylinder {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c w : ℕ → Bool) (m : ℕ) :
    Measure.infinitePi (fun _ : ι => fairCoin) {ω | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      2⁻¹ ^ m := by
  have : {ω : ι → Bool | ∀ j < m, xor (c j) (ω (g j)) = w j} =
      {ω | ∀ j < m, ω (g j) ∈ ({xor (c j) (w j)} : Set Bool)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    cases c j <;> cases w j <;> cases ω (g j) <;> simp
  rw [this, infinitePi_setOf_forall_mem' fairCoin hg (fun t => measurableSet_singleton _) m]
  simp only [fairCoin_singleton, prod_const, card_range]

/-- The event `digitPrefix = d` is a digit cylinder. -/
theorem setOf_digitPrefix_eq {Ω : Type*} (D : Ω → ℕ → Bool) {m d : ℕ} (hd : d < 2 ^ m) :
    {ω | digitPrefix (D ω) m = d} = {ω | ∀ j < m, D ω j = d.testBit (m - 1 - j)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]

/-- **Uniform prefixes**: for digits `xor (c j) (ω (g j))` with injective `g`, each value
`d < 2^m` of the first `m` digits has probability `2^{-m}`. -/
theorem measure_digitPrefix_eq {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g) (c : ℕ → Bool)
    {m d : ℕ} (hd : d < 2 ^ m) :
    Measure.infinitePi (fun _ : ι => fairCoin)
      {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} = 2⁻¹ ^ m := by
  have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} =
      {ω | ∀ j < m, xor (c j) (ω (g j)) = d.testBit (m - 1 - j)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]
  rw [hset]
  exact infinitePi_xor_cylinder hg c (fun j => d.testBit (m - 1 - j)) m

/-- The prefix events are measurable. -/
theorem measurableSet_digitPrefix_eq {ι : Type*} (g : ℕ → ι) (c : ℕ → Bool) (m d : ℕ) :
    MeasurableSet {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} := by
  by_cases hd : d < 2 ^ m
  · have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} =
        {ω | ∀ j < m, xor (c j) (ω (g j)) = d.testBit (m - 1 - j)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, digitPrefix_eq_iff, hd, true_and]
    rw [hset]
    exact measurableSet_xor_cylinder g c (fun j => d.testBit (m - 1 - j)) m
  · have : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hd (h ▸ digitPrefix_lt _ m)
    rw [this]
    exact MeasurableSet.empty

/-- `P(digitPrefix < a) = a 2^{-m}` for `a ≤ 2^m`. -/
theorem measure_digitPrefix_lt {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g) (c : ℕ → Bool)
    {m a : ℕ} (ha : a ≤ 2 ^ m) :
    Measure.infinitePi (fun _ : ι => fairCoin)
      {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} = a * 2⁻¹ ^ m := by
  have hset : {ω : ι → Bool | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} =
      ⋃ d ∈ range a, {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m = d} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_range, exists_prop, exists_eq_right']
  rw [hset, measure_biUnion_finset]
  · rw [sum_congr rfl fun d hd => measure_digitPrefix_eq hg c
      (lt_of_lt_of_le (mem_range.1 hd) ha), sum_const, card_range, nsmul_eq_mul]
  · intro d _ d' _ hdd'
    exact Set.disjoint_left.2 fun ω h h' => hdd' (h.symm.trans h')
  · exact fun d _ => measurableSet_digitPrefix_eq g c m d

/-- `digitPrefix` is a measurable function of the digits. -/
theorem measurable_digitPrefix (m : ℕ) : Measurable fun b : ℕ → Bool => digitPrefix b m := by
  refine measurable_to_countable' fun d => ?_
  have := measurableSet_digitPrefix_eq (ι := ℕ) id (fun _ => false) m d
  simp only [Bool.false_xor, id] at this
  exact this

/-- `binaryVal` is measurable (for the product σ-algebra on `ℕ → Bool`). -/
theorem measurable_binaryVal : Measurable binaryVal := by
  have hf : ∀ m, Measurable fun b : ℕ → Bool => (digitPrefix b m : ℝ) / 2 ^ m := fun m =>
    (measurable_from_nat (f := fun d : ℕ => (d : ℝ) / 2 ^ m)).comp (measurable_digitPrefix m)
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun b => ?_)
  have hlo : ∀ m, binaryVal b - (1 / 2) ^ m ≤ (digitPrefix b m : ℝ) / 2 ^ m := fun m => by
    have := binaryVal_le_digitPrefix_add_one_div b m
    rw [add_div] at this
    rw [one_div_pow]
    linarith
  have hhi : ∀ m, (digitPrefix b m : ℝ) / 2 ^ m ≤ binaryVal b := digitPrefix_div_le_binaryVal b
  have hlim : Tendsto (fun m : ℕ => binaryVal b - (1 / 2 : ℝ) ^ m) atTop (𝓝 (binaryVal b)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_sub (binaryVal b)
    rwa [sub_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi

/-- Coordinates `ω ↦ xor (c j) (ω (g j))` give a measurable digit sequence. -/
theorem measurable_xor_digits {ι : Type*} (g : ℕ → ι) (c : ℕ → Bool) :
    Measurable fun ω : ι → Bool => fun j => xor (c j) (ω (g j)) :=
  measurable_pi_iff.2 fun j =>
    (measurable_from_top (f := fun x : Bool => xor (c j) x)).comp (measurable_pi_apply (g j))

/-- **Uniform law of a point with i.i.d. fair digits** (post #2's requirement (i)): if the
digits are `xor (c j) (ω (g j))` with `g` injective, the point `Σ_j d_j / 2^(j+1)` is
`U[0,1)`. Proof: `P(X ≤ x)` is squeezed between `⌊2^m x⌋ 2^{-m}` and `(⌊2^m x⌋ + 1) 2^{-m}`
for every `m`. -/
theorem map_binaryVal_xor_eq_uniformIco {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c : ℕ → Bool) :
    (Measure.infinitePi fun _ : ι => fairCoin).map
      (fun ω => binaryVal fun j => xor (c j) (ω (g j))) = uniformIco := by
  set μ := Measure.infinitePi fun _ : ι => fairCoin with hμ
  set X : (ι → Bool) → ℝ := fun ω => binaryVal fun j => xor (c j) (ω (g j)) with hX
  have hXm : Measurable X := measurable_binaryVal.comp (measurable_xor_digits g c)
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hXm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hpre : X ⁻¹' Set.Iic x = {ω | X ω ≤ x} := rfl
  rw [hpre]
  rcases lt_or_ge x 0 with hx0 | hx0
  · have h1 : {ω | X ω ≤ x} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hx0 (binaryVal_nonneg _)
    have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_empty_iff_false,
        iff_false, not_and, not_lt]
      intro hy hy0
      linarith
    rw [h1, h2, measure_empty, measure_empty]
  rcases le_or_gt 1 x with hx1 | hx1
  · have h1 : {ω | X ω ≤ x} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (binaryVal_le_one _).trans hx1
    have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = Set.Ico 0 1 := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, and_iff_right_iff_imp]
      intro hy
      linarith [hy.2]
    rw [h1, h2, measure_univ, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
  have h2 : Set.Iic x ∩ Set.Ico (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [h2, Real.volume_Icc, sub_zero]
  -- the squeeze, level by level
  have hfin : μ {ω | X ω ≤ x} ≠ ⊤ := measure_ne_top _ _
  have hbound : ∀ m : ℕ, |(μ {ω | X ω ≤ x}).toReal - x| ≤ (1 / 2) ^ m := by
    intro m
    set a := ⌊(2 : ℝ) ^ m * x⌋₊ with ha
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have ha1 : (a : ℝ) ≤ 2 ^ m * x := Nat.floor_le (by positivity)
    have ha2 : 2 ^ m * x < (a : ℝ) + 1 := Nat.lt_floor_add_one _
    have ham : a < 2 ^ m := by
      have : (a : ℝ) < 2 ^ m := lt_of_le_of_lt ha1 (by nlinarith)
      exact_mod_cast this
    -- `{prefix < a} ⊆ {X ≤ x} ⊆ {prefix < a + 1}`
    have hsub1 : {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a} ⊆ {ω | X ω ≤ x} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h := binaryVal_le_digitPrefix_add_one_div (fun j => xor (c j) (ω (g j))) m
      have hk : ((digitPrefix (fun j => xor (c j) (ω (g j))) m : ℕ) : ℝ) + 1 ≤ a := by
        exact_mod_cast hω
      refine h.trans ?_
      rw [div_le_iff₀ hp]
      linarith
    have hsub2 : {ω | X ω ≤ x} ⊆ {ω | digitPrefix (fun j => xor (c j) (ω (g j))) m < a + 1} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      by_contra hcon
      have hk : (a : ℝ) + 1 ≤ ((digitPrefix (fun j => xor (c j) (ω (g j))) m : ℕ) : ℝ) := by
        exact_mod_cast (not_lt.1 hcon)
      have h := digitPrefix_div_le_binaryVal (fun j => xor (c j) (ω (g j))) m
      rw [div_le_iff₀ hp] at h
      have : X ω * 2 ^ m ≤ x * 2 ^ m := mul_le_mul_of_nonneg_right hω hp.le
      have hXω : X ω = binaryVal (fun j => xor (c j) (ω (g j))) := rfl
      rw [← hXω] at h
      nlinarith
    have hlo := measure_mono (μ := μ) hsub1
    have hhi := measure_mono (μ := μ) hsub2
    rw [measure_digitPrefix_lt hg c ham.le] at hlo
    rw [measure_digitPrefix_lt hg c ham] at hhi
    have e : ∀ b : ℕ, ((b : ENNReal) * 2⁻¹ ^ m).toReal = b / 2 ^ m := by
      intro b
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat, inv_pow, div_eq_mul_inv]
    have hlo' := ENNReal.toReal_mono hfin hlo
    have hhi' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))) hhi
    rw [e] at hlo' hhi'
    push_cast at hhi'
    rw [abs_le, one_div_pow]
    have h3 : (a : ℝ) / 2 ^ m ≤ x := by rw [div_le_iff₀ hp]; linarith
    have h4 : x < ((a : ℝ) + 1) / 2 ^ m := by rw [lt_div_iff₀ hp]; linarith
    rw [add_div] at hhi' h4
    constructor <;> linarith
  have heq : (μ {ω | X ω ≤ x}).toReal = x := by
    by_contra hne
    have hpos : 0 < |(μ {ω | X ω ≤ x}).toReal - x| := abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
    linarith [hbound m]
  rw [show ENNReal.ofReal x = ENNReal.ofReal (μ {ω | X ω ≤ x}).toReal by rw [heq],
    ENNReal.ofReal_toReal hfin]

/-! ### The stacks under Owen scrambling and the digital shift -/

/-- The Owen coordinates of the digits of point `k` of stack `i` are distinct. -/
theorem owen_coord_injective (i : Fin n) (k : ℕ) :
    Function.Injective fun j : ℕ => (i, j, k % 2 ^ j) :=
  fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).1

/-- The digital-shift coordinates of the digits of a point of stack `i` are distinct. -/
theorem shift_coord_injective (i : Fin n) : Function.Injective fun j : ℕ => (i, j) :=
  fun _ _ h => (Prod.mk.inj h).2

/-- **Each Owen-scrambled stack point is `U[0,1)`** (post #2's requirement (i)). -/
theorem map_scrambledStack_owen (i : Fin n) (k : ℕ) :
    (owenMeasure n).map (fun ω => scrambledStack (owenTable ω) i k) = uniformIco :=
  map_binaryVal_xor_eq_uniformIco (owen_coord_injective i k) fun j => k.testBit j

/-- **Each digitally shifted stack point is `U[0,1)`**. -/
theorem map_scrambledStack_shift (i : Fin n) (k : ℕ) :
    (shiftMeasure n).map (fun ω => scrambledStack (shiftFlips ω) i k) = uniformIco :=
  map_binaryVal_xor_eq_uniformIco (shift_coord_injective i) fun j => k.testBit j

/-- Under Owen's measure, the first `m` scrambled digits of a stack point are uniform. -/
theorem owen_digitPrefix_eq (i : Fin n) (k : ℕ) {m d : ℕ} (hd : d < 2 ^ m) :
    owenMeasure n {ω | digitPrefix (scrambledDigit (owenTable ω i) k) m = d} = 2⁻¹ ^ m :=
  measure_digitPrefix_eq (owen_coord_injective i k) (fun j => k.testBit j) hd

/-- Under the digital shift, the first `m` scrambled digits of a stack point are uniform. -/
theorem shift_digitPrefix_eq (i : Fin n) (k : ℕ) {m d : ℕ} (hd : d < 2 ^ m) :
    shiftMeasure n {ω | digitPrefix (scrambledDigit (shiftFlips ω i) k) m = d} = 2⁻¹ ^ m :=
  measure_digitPrefix_eq (shift_coord_injective i) (fun j => k.testBit j) hd

/-- Owen stack points are measurable. -/
theorem measurable_scrambledStack_owen (i : Fin n) (k : ℕ) :
    Measurable fun ω : Fin n × ℕ × ℕ → Bool => scrambledStack (owenTable ω) i k :=
  measurable_binaryVal.comp (measurable_xor_digits (fun j => (i, j, k % 2 ^ j)) _)

/-- Digitally shifted stack points are measurable. -/
theorem measurable_scrambledStack_shift (i : Fin n) (k : ℕ) :
    Measurable fun ω : Fin n × ℕ → Bool => scrambledStack (shiftFlips ω) i k :=
  measurable_binaryVal.comp (measurable_xor_digits (fun j => (i, j)) _)

/-- **Digits with i.i.d. fair coins beyond every position are a.s. not eventually constant.** -/
theorem ae_notEventuallyConst_xor {ι : Type*} {g : ℕ → ι} (hg : Function.Injective g)
    (c : ℕ → Bool) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ι => fairCoin),
      NotEventuallyConst fun j => xor (c j) (ω (g j)) := by
  set μ := Measure.infinitePi fun _ : ι => fairCoin
  -- for each start `J` and value `b`, `{∀ j ≥ J, digit = b}` is null
  have hnull : ∀ (J : ℕ) (b : Bool),
      μ {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} = 0 := by
    intro J b
    have hg' : Function.Injective fun j => g (J + j) :=
      fun _ _ h => by have := hg h; omega
    have hle : ∀ M : ℕ, μ {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} ≤ 2⁻¹ ^ M := by
      intro M
      rw [← infinitePi_xor_cylinder hg' (fun j => c (J + j)) (fun _ => b) M]
      exact measure_mono fun ω hω j _ => hω (J + j) (by omega)
    have hlim : Tendsto (fun M : ℕ => (2⁻¹ : ENNReal) ^ M) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    exact le_antisymm (ge_of_tendsto' hlim hle) (zero_le)
  have hsub : {ω : ι → Bool | ¬ NotEventuallyConst fun j => xor (c j) (ω (g j))} ⊆
      ⋃ (J : ℕ) (b : Bool), {ω | ∀ j, J ≤ j → xor (c j) (ω (g j)) = b} := by
    intro ω hω
    simp only [NotEventuallyConst, Set.mem_ofPred_eq, not_forall, not_and_or, not_exists] at hω
    obtain ⟨J, hJ | hJ⟩ := hω
    · refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨false, fun j hj => ?_⟩⟩
      have := (hJ j).resolve_left (not_not.2 hj)
      simpa using this
    · refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨true, fun j hj => ?_⟩⟩
      have := (hJ j).resolve_left (not_not.2 hj)
      simpa using this
  rw [ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null fun J => measure_iUnion_null fun b =>
    hnull J b)

/-- **The good event has probability one under Owen scrambling.** -/
theorem ae_isGoodTable_owen (n : ℕ) : ∀ᵐ ω ∂owenMeasure n, IsGoodTable (owenTable ω) := by
  unfold IsGoodTable
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  exact ae_notEventuallyConst_xor (owen_coord_injective i k) fun j => k.testBit j

/-- **The good event has probability one under the digital shift.** -/
theorem ae_isGoodTable_shift (n : ℕ) : ∀ᵐ ω ∂shiftMeasure n, IsGoodTable (shiftFlips ω) := by
  unfold IsGoodTable
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  exact ae_notEventuallyConst_xor (shift_coord_injective i) fun j => k.testBit j

/-! ### Measurability of the path -/

/-- The first `T + 1` states of a stack path driven by a measurable family of stacks form a
random vector. -/
theorem measurable_stackPath_restrict_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (T : ℕ) :
    Measurable fun ω => fun t : Fin (T + 1) => stackPath P x₀ (V ω) t := by
  refine measurable_to_countable' fun s => ?_
  set s' : ℕ → Fin n := fun t => s ⟨min t T, by omega⟩ with hs'
  have hset : (fun ω => fun t : Fin (T + 1) => stackPath P x₀ (V ω) t) ⁻¹' {s} =
      {ω | s' 0 = x₀ ∧ ∀ t < T,
        step P (s' t) (V ω (s' t) (departureIndex s' t)) = s' (t + 1)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [← stackDrive_eq_iff]
    constructor
    · intro h t ht
      refine (congrFun h ⟨t, by omega⟩).trans ?_
      simp only [hs']
      congr 1
      ext
      simp only
      omega
    · intro h
      funext t
      refine (h t (by omega)).trans ?_
      simp only [hs']
      congr 1
      ext
      simp only
      omega
  rw [hset, Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  have : {ω | ∀ t < T, step P (s' t) (V ω (s' t) (departureIndex s' t)) = s' (t + 1)} =
      ⋂ (t : ℕ) (_ : t < T), (fun ω => V ω (s' t) (departureIndex s' t)) ⁻¹'
        {u | step P (s' t) u = s' (t + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun t => .iInter fun _ =>
    hV _ _ (measurable_step P (s' t) (measurableSet_singleton _))

/-- Every function of the first `T + 1` states of the path is measurable. -/
theorem measurable_comp_stackPath_of {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {V : Ω → Fin n → ℕ → ℝ} (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ)
    (x₀ : Fin n) (T : ℕ) (F : (Fin (T + 1) → Fin n) → β) :
    Measurable fun ω => F fun t : Fin (T + 1) => stackPath P x₀ (V ω) t :=
  (measurable_of_countable F).comp (measurable_stackPath_restrict_of hV P x₀ T)

/-- **The path coordinates are random variables.** -/
theorem measurable_stackPath_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (t : ℕ) :
    Measurable fun ω => stackPath P x₀ (V ω) t :=
  measurable_comp_stackPath_of hV P x₀ t fun y => y (Fin.last t)

/-- **The occupation counts are random variables.** -/
theorem measurable_occCount_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (i : Fin n)
    (T : ℕ) : Measurable fun ω => occCount (stackPath P x₀ (V ω)) i T := by
  have h := measurable_comp_stackPath_of hV P x₀ T
    fun y => occCount (fun t => y ⟨min t T, by omega⟩) i T
  have e : (fun ω => occCount (stackPath P x₀ (V ω)) i T) = fun ω =>
      occCount (fun t => stackPath P x₀ (V ω) (⟨min t T, by omega⟩ : Fin (T + 1))) i T := by
    funext ω
    refine occCount_congr (fun t ht => ?_) i
    congr 1
    simp only
    omega
  rw [e]
  exact h

/-- **The transition counts are random variables.** -/
theorem measurable_transCount_of {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin n → ℕ → ℝ}
    (hV : ∀ i k, Measurable fun ω => V ω i k) (P : Fin n → Fin n → ℝ) (x₀ : Fin n)
    (i j : Fin n) (T : ℕ) : Measurable fun ω => transCount (stackPath P x₀ (V ω)) i j T := by
  have h := measurable_comp_stackPath_of hV P x₀ T
    fun y => transCount (fun t => y ⟨min t T, by omega⟩) i j T
  have e : (fun ω => transCount (stackPath P x₀ (V ω)) i j T) = fun ω =>
      transCount (fun t => stackPath P x₀ (V ω) (⟨min t T, by omega⟩ : Fin (T + 1))) i j T := by
    funext ω
    refine transCount_congr (fun t ht => ?_) i j
    congr 1
    simp only
    omega
  rw [e]
  exact h

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Scrambled van der Corput stacks are `(0,1)`-sequences: the QMC rate for every scramble

Post #3: "Balancing the departures from each state ((ii)–(iv)) gets the transition counts almost
exactly right". For codes (ii) and (iii) (per-state Sobol = van der Corput stacks, digitally
shifted or Owen-scrambled) this holds **for every realisation** of the randomisation: the
scrambled sequence keeps the net property of the van der Corput sequence (Owen 1997;
Niederreiter 1992, Ch. 4), and the departure counts inherit the QMC rate `O(log T)`.

**Aligned blocks** (`image_digitPrefix_scrambledDigit_block`): for every flip table `f`, the
`2^m` points with indices `a 2^m, …, (a+1) 2^m − 1` have first `m` scrambled digits running over
all of `{0,1}^m` (one point per dyadic cell of length `2^{-m}`): the first `m` scrambled digits
depend only on `k mod 2^m` (`digitPrefix_scrambledDigit_mod`) and determine it
(`mod_eq_of_digitPrefix_scrambledDigit_eq`). Hence (`abs_segErr_scrambledVdc_block_le`) the
counting error `segErr u x N L = #{N ≤ k < N + L : u k ≤ x} − L x` of an aligned block is at most
`1` for every threshold `x ∈ [0,1]`.

**Segments** (generic, for any sequence with per-level block bounds `β m`):
* `abs_segErr_prefix_le`: a prefix of length `L < 2^m` of an aligned `2^m`-block has error
  `≤ Σ_{j<m} β j`;
* `abs_segErr_le_of_block` (**segment lemma**): every segment `[N, N + L)` with `L ≤ 2^m` has
  error `≤ 2 Σ_{j<m} β j + β m` (it is a suffix of one aligned `2^m`-block plus a prefix of the
  next, or a difference of two prefixes).
For scrambled van der Corput points (`β = 1`): `abs_segErr_scrambledVdc_le`:
`|segErr| ≤ 2m + 1` for `L ≤ 2^m`, `abs_segErr_scrambledVdc_log_le`: `≤ 2⌊log₂ L⌋ + 3`, and
`abs_segErr_scrambledVdc_zero_le`: an initial segment `[0, N)` has error `≤ ⌊log₂ N⌋ + 1`.

**Step functions** (`abs_sum_step_sub_le_of_count`, discrete Koksma by summation by parts): if
every threshold count over a finite index set `s` has error `≤ D`, then
`|Σ_{k∈s} (g(step P i (u k)) − (Pg)(i))| ≤ V(g) D`. Hence for every flip table:
* `abs_sum_step_scrambledVdc_segment_le` (exported for the CLT): over any segment of length
  `L ≤ 2^m`, `|Σ_{k<L} φ(u (N + k))| ≤ V(g) (2m + 1)` with `φ(u) = g(step P i u) − (Pg)(i)`;
* `abs_transCount_scrambled_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)`;
* `abs_departureDiscrepancy_scrambled_le`: `|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`;
* `abs_occCount_scrambled_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`;
* `occFreq_scrambled_isBigO`: occupation frequencies converge at `O(log T / T)`;
* `abs_transCount_owen_sub_le`, `abs_transCount_shift_sub_le`, `abs_occCount_owen_sub_le`,
  `abs_occCount_shift_sub_le`: the same bounds for every realisation `ω` of Owen scrambling and
  of the digital shift. These are the constants of `StackBound` for unscrambled van der Corput
  stacks: no realisation of either randomisation is worse than plain QMC.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset Matrix Filter Asymptotics

variable {n : ℕ}

/-! ### Counting errors of segments -/

/-- The **counting error** of the segment `[N, N + L)` of `u` at the threshold `x`:
`#{N ≤ k < N + L : u k ≤ x} − L x`, as a sum. -/
noncomputable def segErr (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) : ℝ :=
  ∑ k ∈ range L, ((if u (N + k) ≤ x then (1 : ℝ) else 0) - x)

/-- The empty segment has error `0`. -/
theorem segErr_zero (u : ℕ → ℝ) (x : ℝ) (N : ℕ) : segErr u x N 0 = 0 := by
  simp [segErr]

/-- **Additivity**: `[N, N + L₁ + L₂) = [N, N + L₁) ∪ [N + L₁, N + L₁ + L₂)`. -/
theorem segErr_add (u : ℕ → ℝ) (x : ℝ) (N L₁ L₂ : ℕ) :
    segErr u x N (L₁ + L₂) = segErr u x N L₁ + segErr u x (N + L₁) L₂ := by
  unfold segErr
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [add_assoc]

/-- The counting error as a count: `segErr = #{k < L : u (N + k) ≤ x} − L x`. -/
theorem segErr_eq_card (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) :
    segErr u x N L = (((range L).filter fun k => u (N + k) ≤ x).card : ℝ) - L * x := by
  unfold segErr
  rw [sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul]

/-- **Prefixes of aligned blocks.** If every aligned `2^m`-block has error `≤ β m`, a prefix of
length `L < 2^m` of an aligned `2^m`-block has error `≤ Σ_{j<m} β j` (split off the first half
when `L ≥ 2^{m-1}`). -/
theorem abs_segErr_prefix_le {u : ℕ → ℝ} {x : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ m a, |segErr u x (a * 2 ^ m) (2 ^ m)| ≤ β m) (m : ℕ) :
    ∀ a L, L < 2 ^ m → |segErr u x (a * 2 ^ m) L| ≤ ∑ j ∈ range m, β j := by
  induction m with
  | zero =>
    intro a L hL
    have hL0 : L = 0 := by simpa using hL
    rw [hL0, segErr_zero, abs_zero, range_zero, sum_empty]
  | succ m ih =>
    intro a L hL
    have hβm : 0 ≤ β m := (abs_nonneg _).trans (hβ m 0)
    have e : a * 2 ^ (m + 1) = (2 * a) * 2 ^ m := by ring
    rw [e, sum_range_succ]
    by_cases hLm : L < 2 ^ m
    · linarith [ih (2 * a) L hLm]
    · obtain ⟨L', rfl⟩ : ∃ L', L = 2 ^ m + L' := ⟨L - 2 ^ m, by omega⟩
      have hL' : L' < 2 ^ m := by rw [pow_succ] at hL; omega
      rw [segErr_add]
      have e2 : 2 * a * 2 ^ m + 2 ^ m = (2 * a + 1) * 2 ^ m := by ring
      rw [e2]
      have h1 := hβ m (2 * a)
      have h2 := ih (2 * a + 1) L' hL'
      calc |segErr u x (2 * a * 2 ^ m) (2 ^ m) + segErr u x ((2 * a + 1) * 2 ^ m) L'|
          ≤ |segErr u x (2 * a * 2 ^ m) (2 ^ m)| + |segErr u x ((2 * a + 1) * 2 ^ m) L'| :=
            abs_add_le _ _
        _ ≤ ∑ j ∈ range m, β j + β m := by linarith

/-- **The segment lemma.** If every aligned `2^m`-block has error `≤ β m`, every segment
`[N, N + L)` with `L ≤ 2^m` has error `≤ 2 Σ_{j<m} β j + β m`. -/
theorem abs_segErr_le_of_block {u : ℕ → ℝ} {x : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ m a, |segErr u x (a * 2 ^ m) (2 ^ m)| ≤ β m) (N L m : ℕ) (hL : L ≤ 2 ^ m) :
    |segErr u x N L| ≤ 2 * ∑ j ∈ range m, β j + β m := by
  set S := ∑ j ∈ range m, β j with hSdef
  have hS : 0 ≤ S := sum_nonneg fun j _ => (abs_nonneg _).trans (hβ j 0)
  have hβm : 0 ≤ β m := (abs_nonneg _).trans (hβ m 0)
  have hpos : 0 < 2 ^ m := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ m := ⟨_, rfl⟩
  obtain ⟨a, r, hN, hr⟩ : ∃ a r, N = a * 2 ^ m + r ∧ r < 2 ^ m :=
    ⟨N / 2 ^ m, N % 2 ^ m, by rw [mul_comm]; exact (Nat.div_add_mod N (2 ^ m)).symm,
      Nat.mod_lt _ hpos⟩
  obtain ⟨A, hA⟩ : ∃ A, A = a * 2 ^ m := ⟨_, rfl⟩
  have hpre : ∀ b ℓ, ℓ ≤ 2 ^ m → |segErr u x (b * 2 ^ m) ℓ| ≤ S + β m := by
    intro b ℓ hℓ
    rcases lt_or_eq_of_le hℓ with h | h
    · linarith [abs_segErr_prefix_le hβ m b ℓ h]
    · rw [h]
      linarith [hβ m b]
  by_cases hrL : r + L ≤ 2 ^ m
  · have e : segErr u x N L = segErr u x (a * 2 ^ m) (r + L) - segErr u x (a * 2 ^ m) r := by
      rw [segErr_add, hN]
      ring
    rw [e]
    have h1 := hpre a (r + L) hrL
    have h2 := abs_segErr_prefix_le hβ m a r hr
    calc |segErr u x (a * 2 ^ m) (r + L) - segErr u x (a * 2 ^ m) r|
        ≤ |segErr u x (a * 2 ^ m) (r + L)| + |segErr u x (a * 2 ^ m) r| := abs_sub _ _
      _ ≤ (S + β m) + S := add_le_add h1 h2
      _ = 2 * S + β m := by ring
  · obtain ⟨L', hL'⟩ : ∃ L', L = (2 ^ m - r) + L' := ⟨L - (2 ^ m - r), by omega⟩
    have hL'lt : L' < 2 ^ m := by omega
    have e1 : segErr u x (a * 2 ^ m) (2 ^ m) =
        segErr u x (a * 2 ^ m) r + segErr u x N (2 ^ m - r) := by
      rw [hN, ← segErr_add]
      congr 1
      omega
    have e2 : N + (2 ^ m - r) = (a + 1) * 2 ^ m := by
      rw [add_mul, one_mul, ← hA, hN, ← hA]
      omega
    have e : segErr u x N L = (segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r) +
        segErr u x ((a + 1) * 2 ^ m) L' := by
      rw [hL', segErr_add, e2, e1]
      ring
    rw [e]
    have h1 := hβ m a
    have h2 := abs_segErr_prefix_le hβ m a r hr
    have h3 := abs_segErr_prefix_le hβ m (a + 1) L' hL'lt
    calc |(segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r) +
          segErr u x ((a + 1) * 2 ^ m) L'|
        ≤ |segErr u x (a * 2 ^ m) (2 ^ m) - segErr u x (a * 2 ^ m) r| +
          |segErr u x ((a + 1) * 2 ^ m) L'| := abs_add_le _ _
      _ ≤ (|segErr u x (a * 2 ^ m) (2 ^ m)| + |segErr u x (a * 2 ^ m) r|) +
          |segErr u x ((a + 1) * 2 ^ m) L'| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ (β m + S) + S := add_le_add (add_le_add h1 h2) h3
      _ = 2 * S + β m := by ring

/-! ### Aligned blocks of the scrambled van der Corput sequence -/

/-- Equal low bits give equal residues: if bits `0, …, j-1` of `K` and `K'` agree then
`K % 2^j = K' % 2^j`. -/
theorem mod_two_pow_eq_of_testBit_eq {K K' j : ℕ} (h : ∀ i < j, K.testBit i = K'.testBit i) :
    K % 2 ^ j = K' % 2 ^ j := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < j
  · simp only [hi, decide_true, Bool.true_and]
    exact h i hi
  · simp only [hi, decide_false, Bool.false_and]

/-- If the first `m` scrambled digits of `K` and `K'` agree (same flip table), so do their first
`m` bits: the scramble is a bijection on each level of the binary tree. -/
theorem testBit_eq_of_scrambledDigit_eq {f : ℕ → ℕ → Bool} {K K' m : ℕ}
    (h : ∀ j < m, scrambledDigit f K j = scrambledDigit f K' j) :
    ∀ j < m, K.testBit j = K'.testBit j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hmod : K % 2 ^ j = K' % 2 ^ j :=
      mod_two_pow_eq_of_testBit_eq fun i hi => ih i hi (by omega)
    have hd := h j hj
    unfold scrambledDigit at hd
    rw [hmod] at hd
    cases hK : K.testBit j <;> cases hK' : K'.testBit j <;> cases f j (K' % 2 ^ j) <;>
      simp_all

/-- **The first `m` scrambled digits determine `k mod 2^m`.** -/
theorem mod_eq_of_digitPrefix_scrambledDigit_eq {f : ℕ → ℕ → Bool} {K K' m : ℕ}
    (h : digitPrefix (scrambledDigit f K) m = digitPrefix (scrambledDigit f K') m) :
    K % 2 ^ m = K' % 2 ^ m :=
  mod_two_pow_eq_of_testBit_eq (testBit_eq_of_scrambledDigit_eq (eq_of_digitPrefix_eq h))

/-- **The first `m` scrambled digits depend only on `k mod 2^m`.** -/
theorem digitPrefix_scrambledDigit_mod (f : ℕ → ℕ → Bool) (K m : ℕ) :
    digitPrefix (scrambledDigit f (K % 2 ^ m)) m = digitPrefix (scrambledDigit f K) m := by
  refine digitPrefix_congr fun j hj => ?_
  unfold scrambledDigit
  rw [Nat.testBit_mod_two_pow, Nat.mod_mod_of_dvd K (pow_dvd_pow 2 hj.le)]
  simp only [hj, decide_true, Bool.true_and]

/-- Within the aligned block `[a 2^m, (a+1) 2^m)`, the first `m` scrambled digits of point
`a 2^m + k` are those of point `k`. -/
theorem digitPrefix_scrambledDigit_block (f : ℕ → ℕ → Bool) (a m : ℕ) {k : ℕ} (hk : k < 2 ^ m) :
    digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m = digitPrefix (scrambledDigit f k) m := by
  rw [← digitPrefix_scrambledDigit_mod f (a * 2 ^ m + k), Nat.mul_add_mod',
    Nat.mod_eq_of_lt hk]

/-- `k ↦` (first `m` scrambled digits of point `k`) is injective on `[0, 2^m)`. -/
theorem injOn_digitPrefix_scrambledDigit (f : ℕ → ℕ → Bool) (m : ℕ) :
    Set.InjOn (fun k => digitPrefix (scrambledDigit f k) m) (range (2 ^ m) : Set ℕ) := by
  intro k hk k' hk' h
  have := mod_eq_of_digitPrefix_scrambledDigit_eq h
  rwa [Nat.mod_eq_of_lt (mem_range.1 hk), Nat.mod_eq_of_lt (mem_range.1 hk')] at this

/-- **The aligned-block property** (Owen 1997: scrambling preserves `(0,m,1)`-nets): for every
flip table, the first `m` scrambled digits of the `2^m` points `a 2^m + k`, `k < 2^m`, run over
all of `{0, …, 2^m − 1}`, i.e. there is one point in each dyadic cell of length `2^{-m}`. -/
theorem image_digitPrefix_scrambledDigit_block (f : ℕ → ℕ → Bool) (a m : ℕ) :
    (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m) =
      range (2 ^ m) := by
  have e : (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m) =
      (range (2 ^ m)).image (fun k => digitPrefix (scrambledDigit f k) m) :=
    image_congr fun k hk => digitPrefix_scrambledDigit_block f a m (mem_range.1 hk)
  rw [e]
  refine eq_of_subset_of_card_le (fun d hd => ?_) ?_
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hd
    exact mem_range.2 (digitPrefix_lt _ m)
  · rw [card_image_of_injOn (injOn_digitPrefix_scrambledDigit f m)]

/-- **Counting through the aligned block**: the number of points of an aligned `2^m`-block whose
first `m` scrambled digits satisfy `p` is the number of `d < 2^m` with `p d`. -/
theorem card_filter_digitPrefix_block (f : ℕ → ℕ → Bool) (a m : ℕ) (p : ℕ → Prop)
    [DecidablePred p] :
    ((range (2 ^ m)).filter fun k => p (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m)).card =
      ((range (2 ^ m)).filter p).card := by
  have hinj : Set.InjOn (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m)
      (range (2 ^ m) : Set ℕ) := by
    intro k hk k' hk' h
    simp only at h
    rw [digitPrefix_scrambledDigit_block f a m (mem_range.1 hk),
      digitPrefix_scrambledDigit_block f a m (mem_range.1 hk')] at h
    exact injOn_digitPrefix_scrambledDigit f m hk hk' h
  rw [← card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _))), ← filter_image,
    image_digitPrefix_scrambledDigit_block]

/-- The number of `d < 2^m` with `d < c` is `min c 2^m`. -/
theorem card_filter_lt_range (c m : ℕ) :
    ((range (2 ^ m)).filter fun d => d < c).card = min c (2 ^ m) := by
  have : (range (2 ^ m)).filter (fun d => d < c) = range (min c (2 ^ m)) := by
    ext d
    simp only [mem_filter, mem_range, lt_min_iff]
    tauto
  rw [this, card_range]

/-- **Aligned blocks of a scrambled van der Corput sequence have counting error `≤ 1`**, at
every threshold `x ∈ [0,1]` and for every flip table. -/
theorem abs_segErr_scrambledVdc_block_le (f : ℕ → ℕ → Bool) (m a : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : |segErr (scrambledVdc f) x (a * 2 ^ m) (2 ^ m)| ≤ 1 := by
  rw [segErr_eq_card]
  set D : ℕ → ℕ := fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m with hD
  set c := ⌊(2 : ℝ) ^ m * x⌋₊ with hc
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hc1 : (c : ℝ) ≤ 2 ^ m * x := Nat.floor_le (by positivity)
  have hc2 : 2 ^ m * x < (c : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcm : (c : ℝ) ≤ 2 ^ m := hc1.trans (by nlinarith)
  have hcount : ∀ c', ((range (2 ^ m)).filter fun k => D k < c').card = min c' (2 ^ m) :=
    fun c' => (card_filter_digitPrefix_block f a m (· < c')).trans (card_filter_lt_range c' m)
  have hsub1 : (range (2 ^ m)).filter (fun k => D k < c) ⊆
      (range (2 ^ m)).filter (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ x) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have h := binaryVal_le_digitPrefix_add_one_div (scrambledDigit f (a * 2 ^ m + k)) m
    have hk2 : ((D k : ℕ) : ℝ) + 1 ≤ c := by exact_mod_cast hk.2
    refine h.trans ?_
    rw [div_le_iff₀ hp]
    change ((D k : ℕ) : ℝ) + 1 ≤ x * 2 ^ m
    linarith
  have hsub2 : (range (2 ^ m)).filter (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ x) ⊆
      (range (2 ^ m)).filter (fun k => D k < c + 1) := by
    intro k hk
    rw [mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_contra hcon
    have hk2 : (c : ℝ) + 1 ≤ ((D k : ℕ) : ℝ) := by exact_mod_cast not_lt.1 hcon
    have h := digitPrefix_div_le_binaryVal (scrambledDigit f (a * 2 ^ m + k)) m
    rw [div_le_iff₀ hp] at h
    have h3 : scrambledVdc f (a * 2 ^ m + k) * 2 ^ m ≤ x * 2 ^ m :=
      mul_le_mul_of_nonneg_right hk.2 hp.le
    change ((D k : ℕ) : ℝ) ≤ scrambledVdc f (a * 2 ^ m + k) * 2 ^ m at h
    linarith
  have hlo := card_le_card hsub1
  have hhi := card_le_card hsub2
  rw [hcount] at hlo hhi
  have hcm' : c ≤ 2 ^ m := by exact_mod_cast hcm
  rw [min_eq_left hcm'] at hlo
  have hlo' : (c : ℝ) ≤ ((range (2 ^ m)).filter fun k =>
      scrambledVdc f (a * 2 ^ m + k) ≤ x).card := by exact_mod_cast hlo
  have hhi' : (((range (2 ^ m)).filter fun k =>
      scrambledVdc f (a * 2 ^ m + k) ≤ x).card : ℝ) ≤ c + 1 := by
    exact_mod_cast hhi.trans (min_le_left _ _)
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- **Segments of a scrambled van der Corput sequence**: for every flip table and threshold
`x ∈ [0,1]`, a segment of length `L ≤ 2^m` has counting error `≤ 2m + 1`. -/
theorem abs_segErr_scrambledVdc_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N L m : ℕ) (hL : L ≤ 2 ^ m) : |segErr (scrambledVdc f) x N L| ≤ 2 * m + 1 := by
  have h := abs_segErr_le_of_block (β := fun _ => 1)
    (fun m a => abs_segErr_scrambledVdc_block_le f m a hx0 hx1) N L m hL
  simpa only [sum_const, card_range, nsmul_eq_mul, mul_one] using h

/-- **Segment lemma, logarithmic form**: `|segErr| ≤ 2 ⌊log₂ L⌋ + 3`. -/
theorem abs_segErr_scrambledVdc_log_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N L : ℕ) : |segErr (scrambledVdc f) x N L| ≤ 2 * (Nat.log 2 L : ℝ) + 3 := by
  have h := abs_segErr_scrambledVdc_le f hx0 hx1 N L (Nat.log 2 L + 1)
    (Nat.lt_pow_succ_log_self (by norm_num) L).le
  push_cast at h
  linarith

/-- **Initial segments**: `|#{k < N : u k ≤ x} − N x| ≤ ⌊log₂ N⌋ + 1`, for every flip table
(the van der Corput bound `N D*_N ≤ ⌊log₂ N⌋ + 1` survives every scramble). -/
theorem abs_segErr_scrambledVdc_zero_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N : ℕ) : |segErr (scrambledVdc f) x 0 N| ≤ (Nat.log 2 N : ℝ) + 1 := by
  have h := abs_segErr_prefix_le (β := fun _ => 1)
    (fun m a => abs_segErr_scrambledVdc_block_le f m a hx0 hx1) (Nat.log 2 N + 1) 0 N
    (Nat.lt_pow_succ_log_self (by norm_num) N)
  simp only [zero_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  push_cast at h
  exact h

/-! ### Step functions: summation by parts on any finite index set -/

/-- The count of departures to `j` is a difference of two thresholds (any index set `s`). -/
theorem card_filter_step_eq_eq_sub (P : Fin n → Fin n → ℝ) (i : Fin n) (u : ℕ → ℝ)
    (s : Finset ℕ) (j : Fin n) :
    ((s.filter fun k => step P i (u k) = j).card : ℝ) =
      ((s.filter fun k => (step P i (u k) : ℕ) < j + 1).card : ℝ) -
        ((s.filter fun k => (step P i (u k) : ℕ) < j).card : ℝ) := by
  rw [eq_sub_iff_add_eq, ← sum_boole, ← sum_boole, ← sum_boole, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h1 : step P i (u k) = j
  · rw [h1]
    simp only [lt_irrefl, Nat.lt_add_one, ite_true, ite_false, add_zero]
  · have h1' : (step P i (u k) : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    by_cases h2 : (step P i (u k) : ℕ) < j
    · have h3 : (step P i (u k) : ℕ) < j + 1 := by omega
      simp only [h1, h2, h3, ite_true, ite_false, zero_add]
    · have h3 : ¬ ((step P i (u k) : ℕ) < j + 1) := by omega
      simp only [h1, h2, h3, ite_false, add_zero]

/-- **Discrete Koksma inequality on any index set**: if `u k ≤ 1` on `s` and every threshold
count `#{k ∈ s : u k ≤ cs_{i,m}}`, `m ≥ 1`, has error `≤ D`, then
`|Σ_{k∈s} (g(step P i (u k)) − (Pg)(i))| ≤ V(g) D`. -/
theorem abs_sum_step_sub_le_of_count {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    {u : ℕ → ℝ} {s : Finset ℕ} (hu : ∀ k ∈ s, u k ≤ 1) {D : ℝ}
    (hD : ∀ m : ℕ, 1 ≤ m →
      |((s.filter fun k => u k ≤ cumProb P i m).card : ℝ) - s.card * cumProb P i m| ≤ D)
    (g : Fin n → ℝ) :
    |∑ k ∈ s, (g (step P i (u k)) - (P *ᵥ g) i)| ≤ stateVariation g * D := by
  set B : ℕ → ℝ := fun m =>
    ((s.filter fun k => (step P i (u k) : ℕ) < m).card : ℝ) - s.card * cumProb P i m with hBdef
  have hB0 : B 0 = 0 := by
    have h0 : (s.filter fun k => (step P i (u k) : ℕ) < 0) = ∅ :=
      filter_eq_empty_iff.2 fun k _ hk => Nat.not_lt_zero _ hk
    simp only [hBdef, h0, card_empty, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hBn : B n = 0 := by
    have hn : (s.filter fun k => (step P i (u k) : ℕ) < n) = s :=
      filter_true_of_mem fun k _ => (step P i (u k)).isLt
    simp only [hBdef, hn, cumProb_of_le P i le_rfl, hP.sum_eq_one i, mul_one, sub_self]
  have hBb : ∀ m, 1 ≤ m → |B m| ≤ D := by
    intro m hm
    have e : (s.filter fun k => (step P i (u k) : ℕ) < m) =
        s.filter fun k => u k ≤ cumProb P i m :=
      filter_congr fun k hk => step_lt_iff hP i (hu k hk) hm
    simp only [hBdef, e]
    exact hD m hm
  have e1 : ∑ k ∈ s, (g (step P i (u k)) - (P *ᵥ g) i) =
      ∑ j : Fin n, g j * (B (j + 1) - B j) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← sum_fiberwise s (fun k => step P i (u k))]
    have e2 : ∀ j : Fin n, ∑ k ∈ s.filter (fun k => step P i (u k) = j),
        g (step P i (u k)) = g j * ((s.filter fun k => step P i (u k) = j).card : ℝ) :=
      fun j => by
        rw [sum_congr rfl fun k hk => by rw [(mem_filter.1 hk).2], sum_const, nsmul_eq_mul,
          mul_comm]
    rw [sum_congr rfl fun j _ => e2 j]
    have e3 : (s.card : ℝ) * (P *ᵥ g) i = ∑ j : Fin n, g j * (P i j * s.card) := by
      simp only [mulVec, dotProduct, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e3, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sub, card_filter_step_eq_eq_sub]
    congr 1
    simp only [hBdef]
    rw [cumProb_succ]
    ring
  rw [e1]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 1 le_rfl)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [Finset.univ_eq_empty, sum_empty, abs_zero]
    exact mul_nonneg (stateVariation_nonneg g) hD0
  have e4 : ∑ j : Fin n, g j * (B (j + 1) - B j) =
      ∑ j ∈ range n, extendNat g j * (B (j + 1) - B j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extendNat g j * (B (j + 1) - B j)) n]
    refine sum_congr rfl fun j _ => ?_
    simp only [extendNat, j.isLt, ↓reduceDIte, Fin.eta]
  rw [e4]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_mul_sub_eq_abel _ B hB0 m, hBn, mul_zero, zero_sub, abs_neg]
  unfold stateVariation
  rw [Nat.add_sub_cancel, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hBb (j + 1) (by omega)) (abs_nonneg _)

/-- Threshold counts of a segment are its counting errors. -/
theorem card_filter_segment_sub_eq_segErr (u : ℕ → ℝ) (x : ℝ) (N L : ℕ) :
    (((range L).filter fun k => u (N + k) ≤ x).card : ℝ) - (range L).card * x =
      segErr u x N L := by
  rw [segErr_eq_card, card_range]

/-- **The segment lemma for step functions** (exported): for every flip table and every
segment of length `L ≤ 2^m`, `|Σ_{k<L} (g(step P i (u (N+k))) − (Pg)(i))| ≤ V(g) (2m + 1)`,
`u = scrambledVdc f`. -/
theorem abs_sum_step_scrambledVdc_segment_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (i : Fin n) (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N L m : ℕ) (hL : L ≤ 2 ^ m) :
    |∑ k ∈ range L, (g (step P i (scrambledVdc f (N + k))) - (P *ᵥ g) i)| ≤
      stateVariation g * (2 * m + 1) :=
  abs_sum_step_sub_le_of_count (u := fun k => scrambledVdc f (N + k)) hP i
    (fun k _ => (scrambledVdc_mem_Icc f _).2) (fun m' _ => by
      rw [card_filter_segment_sub_eq_segErr]
      exact abs_segErr_scrambledVdc_le f (cumProb_mem_Icc hP i m').1 (cumProb_mem_Icc hP i m').2
        N L m hL) g

/-- **The segment lemma for step functions, logarithmic form**: `≤ V(g) (2 ⌊log₂ L⌋ + 3)`. -/
theorem abs_sum_step_scrambledVdc_segment_log_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (i : Fin n) (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N L : ℕ) :
    |∑ k ∈ range L, (g (step P i (scrambledVdc f (N + k))) - (P *ᵥ g) i)| ≤
      stateVariation g * (2 * (Nat.log 2 L : ℝ) + 3) := by
  have h := abs_sum_step_scrambledVdc_segment_le hP i f g N L (Nat.log 2 L + 1)
    (Nat.lt_pow_succ_log_self (by norm_num) L).le
  push_cast at h
  linarith

/-- **Initial segments of step-function sums**: `|Σ_{k<N} φ(u k)| ≤ V(g) (⌊log₂ N⌋ + 1)`. -/
theorem abs_sum_step_scrambledVdc_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n)
    (f : ℕ → ℕ → Bool) (g : Fin n → ℝ) (N : ℕ) :
    |∑ k ∈ range N, (g (step P i (scrambledVdc f k)) - (P *ᵥ g) i)| ≤
      stateVariation g * ((Nat.log 2 N : ℝ) + 1) :=
  abs_sum_step_sub_le_of_count hP i (fun k _ => (scrambledVdc_mem_Icc f k).2) (fun m' _ => by
    have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m') 0 N
    simp only [zero_add] at h
    rw [h]
    exact abs_segErr_scrambledVdc_zero_le f (cumProb_mem_Icc hP i m').1
      (cumProb_mem_Icc hP i m').2 N) g

/-! ### Chains driven by scrambled stacks -/

variable {P : Fin n → Fin n → ℝ}

/-- `|#{k < N : step P i (u k) < m} − N cs_{i,m}| ≤ ⌊log₂ N⌋ + 1` for a scrambled stack. -/
theorem abs_departuresBelow_scrambledVdc_sub_le (hP : IsStochastic P) (i : Fin n)
    (f : ℕ → ℕ → Bool) (N m : ℕ) :
    |(departuresBelow P i (scrambledVdc f) N m : ℝ) - N * cumProb P i m| ≤
      (Nat.log 2 N : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i (scrambledVdc f) N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  have e : departuresBelow P i (scrambledVdc f) N m =
      ((range N).filter fun k => scrambledVdc f (0 + k) ≤ cumProb P i m).card := by
    unfold departuresBelow
    congr 1
    refine filter_congr fun k _ => ?_
    rw [zero_add]
    exact step_lt_iff hP i (scrambledVdc_mem_Icc f k).2 hm
  rw [e]
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m) 0 N
  rw [card_range] at h
  rw [h]
  exact abs_segErr_scrambledVdc_zero_le f (cumProb_mem_Icc hP i m).1 (cumProb_mem_Icc hP i m).2 N

/-- **Scrambled stacks balance the transitions, for every flip table** (post #3, codes (ii) and
(iii)): `|N_ij(T) − p_ij N_i(T)| ≤ 2 (⌊log₂ T⌋ + 1)`. -/
theorem abs_transCount_scrambled_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack f)) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) i T
  rw [transCount_stackDrive]
  have hv : scrambledStack f i = scrambledVdc (f i) := rfl
  rw [hv, card_step_eq_eq_sub]
  have e : (departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) -
        departuresBelow P i (scrambledVdc (f i)) N j - P i j * N =
      ((departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_scrambledVdc_sub_le hP i (f i) N (j + 1)
  have h2 := abs_departuresBelow_scrambledVdc_sub_le hP i (f i) N j
  have hlog : (Nat.log 2 N : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (occCount_le (stackPath P x₀ (scrambledStack f)) i T)
  calc _ ≤ |(departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Departure discrepancy of a scrambled-stack path, for every flip table**:
`|D_i(g, T)| ≤ V(g) (⌊log₂ T⌋ + 1)`. -/
theorem abs_departureDiscrepancy_scrambled_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    |departureDiscrepancy P g (stackPath P x₀ (scrambledStack f)) i T| ≤
      stateVariation g * ((Nat.log 2 T : ℝ) + 1) := by
  refine (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ (scrambledStack f) i
    T)).trans_le ((abs_sum_step_scrambledVdc_le hP i (f i) g _).trans ?_)
  have hlog : (Nat.log 2 (occCount (stackPath P x₀ (scrambledStack f)) i T) : ℝ) ≤
      Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (occCount_le (stackPath P x₀ (scrambledStack f)) i T)
  exact mul_le_mul_of_nonneg_left (by linarith) (stateVariation_nonneg g)

/-- **Occupation error of a scrambled-stack path, for every flip table** (post #3, "QMC's
`O(log T / T)`" for codes (ii) and (iii)): `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)`,
where `h − Ph = 1_{s} − π_s` and `|h| ≤ M`. -/
theorem abs_occCount_scrambled_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
  refine (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl ?_)
  calc ∑ i, |departureDiscrepancy P h (stackPath P x₀ (scrambledStack f)) i T|
      ≤ ∑ _i : Fin n, stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
        sum_le_sum fun i _ => abs_departureDiscrepancy_scrambled_le hP x₀ f h i T
    _ = n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The occupation frequencies of a scrambled-stack path converge at `O(log T / T)`, for
every flip table.** -/
theorem occFreq_scrambled_isBigO (hP : IsStochastic P) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    (fun T : ℕ => (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) / T - c) =O[atTop]
      fun T : ℕ => Real.log T / T := by
  refine isBigO_log_div_of_le (A := 2 * M) (B := n * stateVariation h)
    (by linarith [(abs_nonneg _).trans (hM s)])
    (mul_nonneg (Nat.cast_nonneg n) (stateVariation_nonneg h)) fun T hT => ?_
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ hTpos, ← abs_of_pos hTpos, ← abs_mul, abs_of_pos hTpos, sub_mul,
    div_mul_cancel₀ _ hTpos.ne', mul_comm c]
  exact abs_occCount_scrambled_sub_le hP x₀ f hh hM T

/-- Owen scrambling: the transition bound holds for **every** realisation `ω`. -/
theorem abs_transCount_owen_sub_le (hP : IsStochastic P) (x₀ : Fin n)
    (ω : Fin n × ℕ × ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack (owenTable ω))) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack (owenTable ω))) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  abs_transCount_scrambled_sub_le hP x₀ (owenTable ω) i j T

/-- Digital shift: the transition bound holds for **every** realisation `ω`. -/
theorem abs_transCount_shift_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ → Bool)
    (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i T| ≤
      2 * ((Nat.log 2 T : ℝ) + 1) :=
  abs_transCount_scrambled_sub_le hP x₀ (shiftFlips ω) i j T

/-- Owen scrambling: the occupation bound holds for **every** realisation `ω`. -/
theorem abs_occCount_owen_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ × ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
  abs_occCount_scrambled_sub_le hP x₀ (owenTable ω) hh hM T

/-- Digital shift: the occupation bound holds for **every** realisation `ω`. -/
theorem abs_occCount_shift_sub_le (hP : IsStochastic P) (x₀ : Fin n) (ω : Fin n × ℕ → Bool)
    {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (T : ℕ) : |(occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1) :=
  abs_occCount_scrambled_sub_le hP x₀ (shiftFlips ω) hh hM T

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two-state stack chains: the error is a sum of two local discrepancies (post #3)

Post #3, codes (ii) and (iii), two-state chain. Let state `0` leave to `1` iff its stack point
exceeds `c₀ = p₀₀`, and state `1` leave to `0` iff its stack point is `≤ c₁ = p₁₀`. The chain
alternates between `0→1` and `1→0` transitions, so their numbers differ by at most one. With
`N_i(T)` the occupation times and `D_i(N) = #{k < N : v_i(k) ≤ c_i} − N c_i` the local
discrepancies of the two stacks, this gives, for EVERY pair of stacks with values in `[0,1]`,

  `|q (N₀(T) − T π₀) − D₀(N₀(T)) − D₁(N₁(T))| ≤ 1`,  `q = p₀₁ + p₁₀`, `π₀ = p₁₀ / q`.

For scrambled van der Corput stacks (every flip table) the `D_i` are `O(log)` and vary by
`O(log L)` over segments of length `L` (`StackNet`), so the random indices `N_i(T)` may be
replaced by the deterministic `n_i(T) = ⌊T π_i⌋` at a cost `O(log log T)`: a deterministic
Anscombe theorem (here in the form `O(log log T)`, with the logarithm of `⌊log₂ T⌋ + 1`; we
use the segment lemma `abs_segErr_scrambledVdc_log_le` of `StackNet`).

## Main results

* `step_two_eq_zero_iff`: in a two-state chain, `step P i u = 0 ↔ u ≤ p_{i0}` for `u ∈ [0,1]`.
* `abs_two_state_identity`: the identity above, for any stacks in `[0,1]`.
* `abs_occErr_le`: `|N₀(T) − T π₀| ≤ (2⌊log₂ T⌋ + 3)/q` (scrambled stacks, every flip table).
* `abs_segErr_sub_segErr_le`: `|D(N) − D(n)| ≤ 2⌊log₂ |N − n|⌋ + 3` (every flip table).
* `piZero`, `piOne`, `occErr P x₀ f T = N₀(T) − T π₀`, `mainTerm`, `anscConst`, `anscBound`.
* `abs_occErr_sub_mainTerm_le` (**deterministic Anscombe**): with
  `mainTerm = (D₀(⌊Tπ₀⌋) + D₁(⌊Tπ₁⌋))/q`,
  `|N₀(T) − T π₀ − mainTerm| ≤ anscBound P T = (7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q`,
  `A = ⌈3/q⌉ + 1`, for every flip table.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset

/-- In a two-state chain the update goes to state `0` iff `u ≤ p_{i0}` (for `u ∈ [0,1]`). -/
theorem step_two_eq_zero_iff {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (i : Fin 2) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : step P i u = 0 ↔ u ≤ P i 0 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero hP.nonneg i
    exact ⟨fun _ ↦ hP.nonneg i 0, fun _ ↦ Fin.ext h⟩
  · have h := step_eq_iff hP i 0 ⟨hpos, hu.2⟩
    have h1 : cumProb P i ((0 : Fin 2) : ℕ) = 0 := cumProb_zero P i
    have h2 : cumProb P i (((0 : Fin 2) : ℕ) + 1) = P i 0 := by
      rw [cumProb_succ, h1, zero_add]
    rw [h1, h2] at h
    exact h.trans ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hpos, h'⟩⟩

/-- The local discrepancy `D(N) = #{k < N : v k ≤ c} − N c`, as `segErr v c 0 N`. -/
theorem segErr_zero_eq_card (v : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    segErr v c 0 N = (((range N).filter fun k ↦ v k ≤ c).card : ℝ) - N * c := by
  rw [segErr_eq_card]
  simp only [zero_add]

/-- **The two-state identity.** For any stacks with values in `[0,1]`,
`|q (N₀ − T π₀) − D₀(N₀) − D₁(N₁)| ≤ 1`, written as `|q N₀ − T p₁₀ − D₀ − D₁| ≤ 1`. -/
theorem abs_two_state_identity {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    {v : Fin 2 → ℕ → ℝ} (hv : ∀ i k, v i k ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    |(P 0 1 + P 1 0) * occCount (stackPath P x₀ v) 0 T - T * P 1 0 -
        segErr (v 0) (P 0 0) 0 (occCount (stackPath P x₀ v) 0 T) -
        segErr (v 1) (P 1 0) 0 (occCount (stackPath P x₀ v) 1 T)| ≤ 1 := by
  classical
  set x := stackPath P x₀ v with hx
  set N0 := occCount x 0 T with hN0
  set N1 := occCount x 1 T with hN1
  have hsum : N0 + N1 = T := by
    have := sum_occCount x T
    rwa [Fin.sum_univ_two] at this
  have hflow := abs_flowBalance_le x 0 T
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hflow
  have h01 : transCount x 0 1 T = N0 - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card := by
    rw [hx, transCount_stackDrive]
    have e : ((range N0).filter fun k ↦ step P 0 (v 0 k) = 1) =
        (range N0).filter fun k ↦ ¬ v 0 k ≤ P 0 0 := by
      refine filter_congr fun k _ ↦ ?_
      rw [← step_two_eq_zero_iff hP 0 (hv 0 k)]
      constructor
      · intro h h0
        rw [h0] at h
        exact absurd h (by decide)
      · intro h
        rcases Fin.exists_fin_two.1 ⟨step P 0 (v 0 k), rfl⟩ with h' | h'
        · exact absurd h' h
        · exact h'
    rw [e, filter_not, card_sdiff_of_subset (filter_subset _ _), card_range]
  have h10 : transCount x 1 0 T = ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card := by
    rw [hx, transCount_stackDrive]
    congr 1
    exact filter_congr fun k _ ↦ step_two_eq_zero_iff hP 1 (hv 1 k)
  have hle : ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card ≤ N0 :=
    (card_filter_le _ _).trans (card_range N0).le
  rw [h01, h10] at hflow
  rw [segErr_zero_eq_card, segErr_zero_eq_card]
  have hT : (T : ℝ) = N0 + N1 := by exact_mod_cast hsum.symm
  have hrow : P 0 0 + P 0 1 = 1 := by
    have := hP.sum_eq_one 0
    rwa [Fin.sum_univ_two] at this
  have hflow' : |((N0 : ℤ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
      ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card| ≤ 1 := by
    have e : ((N0 - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card : ℕ) : ℤ) =
        (N0 : ℤ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card := Nat.cast_sub hle
    simpa [e] using hflow
  have hflowR : |((N0 : ℝ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
      ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card| ≤ 1 := by
    exact_mod_cast hflow'
  rw [hT]
  have e : (P 0 1 + P 1 0) * N0 - (N0 + N1) * P 1 0 -
      (((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card - N0 * P 0 0) -
      (((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card - N1 * P 1 0) =
      ((N0 : ℝ) - ((range N0).filter fun k ↦ v 0 k ≤ P 0 0).card) -
        ((range N1).filter fun k ↦ v 1 k ≤ P 1 0).card := by
    have : P 0 1 = 1 - P 0 0 := by linarith
    rw [this]
    ring
  rw [e]
  exact hflowR

/-- The stationary probability `π₀ = p₁₀ / (p₀₁ + p₁₀)` of a two-state chain. -/
noncomputable def piZero (P : Fin 2 → Fin 2 → ℝ) : ℝ := P 1 0 / (P 0 1 + P 1 0)

/-- The stationary probability `π₁ = p₀₁ / (p₀₁ + p₁₀)` of a two-state chain. -/
noncomputable def piOne (P : Fin 2 → Fin 2 → ℝ) : ℝ := P 0 1 / (P 0 1 + P 1 0)

/-- The occupation error `N₀(T) − T π₀` of the chain driven by scrambled stacks with flip
table `f`. -/
noncomputable def occErr (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool)
    (T : ℕ) : ℝ :=
  occCount (stackPath P x₀ (scrambledStack f)) 0 T - T * piZero P

/-- The main term `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋)) / q`: the local discrepancies of the two stacks at
deterministic indices. -/
noncomputable def mainTerm (P : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) : ℝ :=
  (segErr (scrambledStack f 0) (P 0 0) 0 ⌊T * piZero P⌋₊ +
    segErr (scrambledStack f 1) (P 1 0) 0 ⌊T * piOne P⌋₊) / (P 0 1 + P 1 0)

/-- The constant `A = ⌈3/q⌉ + 1` of the Anscombe bound. -/
noncomputable def anscConst (P : Fin 2 → Fin 2 → ℝ) : ℕ := ⌈3 / (P 0 1 + P 1 0)⌉₊ + 1

/-- The Anscombe bound `(7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q`. -/
noncomputable def anscBound (P : Fin 2 → Fin 2 → ℝ) (T : ℕ) : ℝ :=
  (7 + 4 * (Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) : ℝ)) / (P 0 1 + P 1 0)

/-- Variation of the local discrepancy of a scrambled van der Corput sequence between two
indices: `|D(N) − D(n)| ≤ 2⌊log₂ |N − n|⌋ + 3`. -/
theorem abs_segErr_sub_segErr_le (g : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (N n : ℕ) :
    |segErr (scrambledVdc g) c 0 N - segErr (scrambledVdc g) c 0 n| ≤
      2 * (Nat.log 2 (N - n + (n - N)) : ℝ) + 3 := by
  rcases le_total n N with h | h
  · have e : N = n + (N - n) := by omega
    have := abs_segErr_scrambledVdc_log_le g hc0 hc1 n (N - n)
    rw [e, segErr_add, zero_add, add_sub_cancel_left, show n + (N - n) - n = N - n by omega,
      show n - (n + (N - n)) = 0 by omega, add_zero]
    exact this
  · have e : n = N + (n - N) := by omega
    have := abs_segErr_scrambledVdc_log_le g hc0 hc1 N (n - N)
    rw [e, segErr_add, zero_add, sub_add_cancel_left, abs_neg,
      show N - (N + (n - N)) = 0 by omega, zero_add, show N + (n - N) - N = n - N by omega]
    exact this

/-- `q = p₀₁ + p₁₀` and the stationary identities. -/
theorem piZero_add_piOne {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) :
    piZero P + piOne P = 1 := by
  rw [piZero, piOne, ← add_div, add_comm, div_self hq.ne']

/-- **QMC rate for the two-state stack chain** (every flip table):
`|N₀(T) − T π₀| ≤ (2⌊log₂ T⌋ + 3)/q`. -/
theorem abs_occErr_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0)
    (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    |occErr P x₀ f T| ≤ (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) := by
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have hid := abs_two_state_identity hP x₀ hv T
  set N0 := occCount (stackPath P x₀ (scrambledStack f)) 0 T
  set N1 := occCount (stackPath P x₀ (scrambledStack f)) 1 T
  have hsum : N0 + N1 = T := by
    have := sum_occCount (stackPath P x₀ (scrambledStack f)) T
    rwa [Fin.sum_univ_two] at this
  have hc00 := hP.nonneg 0 0
  have hc01 : P 0 0 ≤ 1 := by
    have := hP.sum_eq_one 0
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 0 1]
  have hc10 := hP.nonneg 1 0
  have hc11 : P 1 0 ≤ 1 := by
    have := hP.sum_eq_one 1
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 1 1]
  have h0 := abs_segErr_scrambledVdc_zero_le (f 0) hc00 hc01 N0
  have h1 := abs_segErr_scrambledVdc_zero_le (f 1) hc10 hc11 N1
  have hl0 : (Nat.log 2 N0 : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have hl1 : (Nat.log 2 N1 : ℝ) ≤ Nat.log 2 T := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have e0 : scrambledStack f 0 = scrambledVdc (f 0) := rfl
  have e1 : scrambledStack f 1 = scrambledVdc (f 1) := rfl
  rw [e0, e1] at hid
  have hkey : (P 0 1 + P 1 0) * occErr P x₀ f T =
      (P 0 1 + P 1 0) * N0 - T * P 1 0 := by
    rw [occErr, piZero]
    field_simp
    rfl
  have hm : |occErr P x₀ f T| * (P 0 1 + P 1 0) = |(P 0 1 + P 1 0) * occErr P x₀ f T| := by
    rw [abs_mul, abs_of_pos hq, mul_comm]
  rw [le_div_iff₀ hq, hm, hkey]
  have := abs_sub_abs_le_abs_sub ((P 0 1 + P 1 0) * N0 - T * P 1 0)
    (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 + segErr (scrambledVdc (f 1)) (P 1 0) 0 N1)
  have e : (P 0 1 + P 1 0) * N0 - T * P 1 0 -
      (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 + segErr (scrambledVdc (f 1)) (P 1 0) 0 N1) =
      (P 0 1 + P 1 0) * N0 - T * P 1 0 - segErr (scrambledVdc (f 0)) (P 0 0) 0 N0 -
        segErr (scrambledVdc (f 1)) (P 1 0) 0 N1 := by ring
  rw [e] at this
  have habs := abs_add_le (segErr (scrambledVdc (f 0)) (P 0 0) 0 N0)
    (segErr (scrambledVdc (f 1)) (P 1 0) 0 N1)
  linarith

/-- A natural number within real distance `R ≤ A (⌊log₂ T⌋ + 1)` of a real point: the
logarithm of the distance is controlled. -/
theorem natLog_dist_le {N n A T : ℕ} {r : ℝ} (hN : |(N : ℝ) - r| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1)
    (hn : |r - n| < 1) : Nat.log 2 (N - n + (n - N)) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
  refine Nat.log_mono_right ?_
  have hd : ((N - n + (n - N) : ℕ) : ℝ) = |(N : ℝ) - n| := by
    rcases le_total n N with h | h
    · rw [show N - n + (n - N) = N - n by omega, Nat.cast_sub h,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ N - n by omega))]
    · rw [show N - n + (n - N) = n - N by omega, Nat.cast_sub h, abs_sub_comm,
        abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ n - N by omega))]
  have h1 : |(N : ℝ) - n| ≤ |(N : ℝ) - r| + |r - n| := abs_sub_le _ _ _
  have h2 : ((N - n + (n - N) : ℕ) : ℝ) ≤ ((A * (Nat.log 2 T + 1) : ℕ) : ℝ) := by
    rw [hd]
    push_cast
    linarith
  exact_mod_cast h2

/-- **Deterministic Anscombe theorem for the two-state stack chain** (every flip table). The
occupation error is the main term `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋))/q` up to
`(7 + 4⌊log₂ (A (⌊log₂ T⌋ + 1))⌋)/q = O(log log T)`. -/
theorem abs_occErr_sub_mainTerm_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P)
    (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    |occErr P x₀ f T - mainTerm P f T| ≤ anscBound P T := by
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have hid := abs_two_state_identity hP x₀ hv T
  have hocc := abs_occErr_le hP hq x₀ f T
  have e0 : scrambledStack f 0 = scrambledVdc (f 0) := rfl
  have e1 : scrambledStack f 1 = scrambledVdc (f 1) := rfl
  have hz : (P 0 1 + P 1 0) * (T * piZero P) = T * P 1 0 := by
    rw [piZero]
    field_simp
  have hmt : (P 0 1 + P 1 0) * mainTerm P f T =
      segErr (scrambledVdc (f 0)) (P 0 0) 0 ⌊T * piZero P⌋₊ +
        segErr (scrambledVdc (f 1)) (P 1 0) 0 ⌊T * piOne P⌋₊ := by
    rw [mainTerm, e0, e1]
    field_simp
  have hkey : (P 0 1 + P 1 0) * (occErr P x₀ f T - mainTerm P f T) =
      ((P 0 1 + P 1 0) * occCount (stackPath P x₀ (scrambledStack f)) 0 T - T * P 1 0 -
        segErr (scrambledVdc (f 0)) (P 0 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 0 T)
        - segErr (scrambledVdc (f 1)) (P 1 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 1 T))
      + (segErr (scrambledVdc (f 0)) (P 0 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 0 T)
        - segErr (scrambledVdc (f 0)) (P 0 0) 0 ⌊T * piZero P⌋₊)
      + (segErr (scrambledVdc (f 1)) (P 1 0) 0 (occCount (stackPath P x₀ (scrambledStack f)) 1 T)
        - segErr (scrambledVdc (f 1)) (P 1 0) 0 ⌊T * piOne P⌋₊) := by
    rw [mul_sub, hmt, occErr, mul_sub, hz]
    ring
  set N0 := occCount (stackPath P x₀ (scrambledStack f)) 0 T with hN0
  set N1 := occCount (stackPath P x₀ (scrambledStack f)) 1 T with hN1
  set n0 := ⌊T * piZero P⌋₊ with hn0
  set n1 := ⌊T * piOne P⌋₊ with hn1
  have hsum : N0 + N1 = T := by
    have := sum_occCount (stackPath P x₀ (scrambledStack f)) T
    rwa [Fin.sum_univ_two] at this
  have hpz : 0 ≤ piZero P := div_nonneg (hP.nonneg 1 0) hq.le
  have hpo : 0 ≤ piOne P := div_nonneg (hP.nonneg 0 1) hq.le
  have hc00 := hP.nonneg 0 0
  have hc01 : P 0 0 ≤ 1 := by
    have := hP.sum_eq_one 0
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 0 1]
  have hc10 := hP.nonneg 1 0
  have hc11 : P 1 0 ≤ 1 := by
    have := hP.sum_eq_one 1
    rw [Fin.sum_univ_two] at this
    linarith [hP.nonneg 1 1]
  -- the constant
  set A := anscConst P with hA
  have hAge : 3 / (P 0 1 + P 1 0) + 1 ≤ (A : ℝ) := by
    rw [hA, anscConst]
    push_cast
    linarith [Nat.le_ceil (3 / (P 0 1 + P 1 0))]
  have hlogT : (0 : ℝ) ≤ Nat.log 2 T := Nat.cast_nonneg _
  have hR : (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) ≤
      (A : ℝ) * (Nat.log 2 T + 1) - 1 := by
    have h1 : (2 * (Nat.log 2 T : ℝ) + 3) / (P 0 1 + P 1 0) ≤
        3 / (P 0 1 + P 1 0) * (Nat.log 2 T + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
      linarith
    nlinarith
  -- the two occupation errors
  have hN0r : |(N0 : ℝ) - T * piZero P| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1 := hocc.trans hR
  have hN1r : |(N1 : ℝ) - T * piOne P| ≤ (A : ℝ) * (Nat.log 2 T + 1) - 1 := by
    have e : (N1 : ℝ) - T * piOne P = -((N0 : ℝ) - T * piZero P) := by
      have hT : (T : ℝ) = N0 + N1 := by exact_mod_cast hsum.symm
      have h1 := piZero_add_piOne hq
      rw [hT]
      linear_combination (-((N0 : ℝ) + N1)) * h1
    rw [e, abs_neg]
    exact hN0r
  have hfl : ∀ y : ℝ, 0 ≤ y → |y - ⌊y⌋₊| < 1 := fun y hy ↦ by
    rw [abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
    linarith [Nat.lt_floor_add_one y]
  have hL0 := natLog_dist_le hN0r (hfl _ (mul_nonneg (Nat.cast_nonneg T) hpz))
  have hL1 := natLog_dist_le hN1r (hfl _ (mul_nonneg (Nat.cast_nonneg T) hpo))
  have hd0 := abs_segErr_sub_segErr_le (f 0) hc00 hc01 N0 n0
  have hd1 := abs_segErr_sub_segErr_le (f 1) hc10 hc11 N1 n1
  have hL0' : (Nat.log 2 (N0 - n0 + (n0 - N0)) : ℝ) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
    exact_mod_cast hL0
  have hL1' : (Nat.log 2 (N1 - n1 + (n1 - N1)) : ℝ) ≤ Nat.log 2 (A * (Nat.log 2 T + 1)) := by
    exact_mod_cast hL1
  rw [e0, e1] at hid
  -- assemble
  rw [anscBound, le_div_iff₀ hq]
  have hm : |occErr P x₀ f T - mainTerm P f T| * (P 0 1 + P 1 0) =
      |(P 0 1 + P 1 0) * (occErr P x₀ f T - mainTerm P f T)| := by
    rw [abs_mul, abs_of_pos hq, mul_comm]
  rw [hm, hkey]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  linarith

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aligned dyadic blocks: prefix and segment bounds (for post #3)

Post #3, codes (ii) and (iii): one scrambled base-2 van der Corput (one-dimensional Sobol)
sequence per state drives the chain by the stack rule. The first `2^m` points of any aligned
block of indices `a·2^m, …, (a+1)·2^m − 1` of such a sequence put exactly one point in each
dyadic cell of length `2^{-m}`, for every flip table. Hence, for a threshold `c ∈ [0,1)`, the
block's contribution to the local discrepancy `Σ_k (1{x_k ≤ c} − c)` is
`1{x* ≤ c} − {2^m c}`, where `x*` is the block's point in the cell of `c`: it lies in `[−1, 1]`.

This module is model-free: it works with any real sequence `F : ℕ → ℝ` (the partial sums of the
local discrepancy) whose increments over aligned blocks are bounded by `B`, and with any
sequence `x` with the aligned-block property.

## Main results

* `AlignedBlockBound F B`: `|F((a+1)2^m) − F(a 2^m)| ≤ B` for all `m, a`.
* `abs_sub_alignedPrefix_le`: a prefix of length `r < 2^m` of an aligned block contributes at
  most `B·m` (binary expansion of `r`).
* `abs_sub_le_of_le_add_pow`: `|F N' − F N| ≤ B(2m+1)` when `N ≤ N' ≤ N + 2^m`.
* `abs_sub_le_log` (**segment lemma**): `|F(N+L) − F N| ≤ B(2⌊log₂ L⌋ + 3)`.
* `abs_sub_zero_le_log`: `|F N − F 0| ≤ B(⌊log₂ N⌋ + 1)`.
* `card_le_add_frac_eq` (**per-block jump formula**, abstract): if the `2^m` points
  `x (a 2^m + r)`, `r < 2^m`, lie one in each dyadic cell `[j/2^m, (j+1)/2^m)`, then
  `#{r : x (a 2^m + r) ≤ c} − 2^m c = 1{x* ≤ c} − {2^m c}` with `x*` the point in the cell of
  `c`; `alignedBlockBound_of_cells`: such sequences satisfy `AlignedBlockBound` with `B = 1`.
-/

namespace RQMCMarkov.ScrambledStacks

open Finset

/-- **Aligned-block bound.** The increments of `F` over every aligned dyadic block of indices
`[a 2^m, (a+1) 2^m)` are bounded by `B`. -/
def AlignedBlockBound (F : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ m a : ℕ, |F ((a + 1) * 2 ^ m) - F (a * 2 ^ m)| ≤ B

/-- The block bound is nonnegative. -/
theorem AlignedBlockBound.nonneg {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) : 0 ≤ B :=
  (abs_nonneg _).trans (hF 0 0)

/-- **Prefix of an aligned block.** A prefix of length `r < 2^m` of the aligned block starting at
`a 2^m` changes `F` by at most `B m`. -/
theorem abs_sub_alignedPrefix_le {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (m : ℕ) :
    ∀ a r : ℕ, r < 2 ^ m → |F (a * 2 ^ m + r) - F (a * 2 ^ m)| ≤ B * m := by
  induction m with
  | zero =>
      intro a r hr
      have hr0 : r = 0 := by
        rw [pow_zero] at hr
        omega
      rw [hr0, add_zero, sub_self, abs_zero, Nat.cast_zero, mul_zero]
  | succ m ih =>
      intro a r hr
      have hB := hF.nonneg
      have h2 : a * 2 ^ (m + 1) = (2 * a) * 2 ^ m := by ring
      rw [h2]
      by_cases hrm : r < 2 ^ m
      · refine (ih (2 * a) r hrm).trans ?_
        push_cast
        nlinarith
      · obtain ⟨r', rfl⟩ : ∃ r', r = 2 ^ m + r' := ⟨r - 2 ^ m, by omega⟩
        have hr' : r' < 2 ^ m := by
          rw [pow_succ] at hr
          omega
        have e1 : 2 * a * 2 ^ m + (2 ^ m + r') = (2 * a + 1) * 2 ^ m + r' := by ring
        rw [e1]
        have k1 := ih (2 * a + 1) r' hr'
        have k2 := hF m (2 * a)
        calc |F ((2 * a + 1) * 2 ^ m + r') - F (2 * a * 2 ^ m)|
            = |(F ((2 * a + 1) * 2 ^ m + r') - F ((2 * a + 1) * 2 ^ m)) +
                (F ((2 * a + 1) * 2 ^ m) - F (2 * a * 2 ^ m))| := by ring_nf
          _ ≤ |F ((2 * a + 1) * 2 ^ m + r') - F ((2 * a + 1) * 2 ^ m)| +
                |F ((2 * a + 1) * 2 ^ m) - F (2 * a * 2 ^ m)| := abs_add_le _ _
          _ ≤ B * m + B := add_le_add k1 k2
          _ = B * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Two nearby indices.** If `N ≤ N' ≤ N + 2^m` then `|F N' − F N| ≤ B (2m + 1)`. -/
theorem abs_sub_le_of_le_add_pow {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) {m N N' : ℕ}
    (h1 : N ≤ N') (h2 : N' ≤ N + 2 ^ m) : |F N' - F N| ≤ B * (2 * m + 1) := by
  have hB := hF.nonneg
  have hp : 0 < 2 ^ m := Nat.two_pow_pos m
  set a := N / 2 ^ m with ha
  set r := N % 2 ^ m with hr
  have hN : N = a * 2 ^ m + r := by rw [ha, hr, mul_comm]; exact (Nat.div_add_mod N _).symm
  have hrlt : r < 2 ^ m := Nat.mod_lt _ hp
  have hpre := abs_sub_alignedPrefix_le hF m a r hrlt
  rw [← hN] at hpre
  by_cases hN' : N' < (a + 1) * 2 ^ m
  · have hpre' := abs_sub_alignedPrefix_le hF m a (N' - a * 2 ^ m) (by
      rw [add_mul, one_mul] at hN'
      omega)
    have e : a * 2 ^ m + (N' - a * 2 ^ m) = N' := by omega
    rw [e] at hpre'
    calc |F N' - F N| = |(F N' - F (a * 2 ^ m)) - (F N - F (a * 2 ^ m))| := by ring_nf
      _ ≤ |F N' - F (a * 2 ^ m)| + |F N - F (a * 2 ^ m)| := abs_sub _ _
      _ ≤ B * m + B * m := add_le_add hpre' hpre
      _ ≤ B * (2 * m + 1) := by nlinarith
  · push Not at hN'
    have hlt : N' - (a + 1) * 2 ^ m < 2 ^ m := by
      rw [add_mul, one_mul] at hN' ⊢
      omega
    have hpre' := abs_sub_alignedPrefix_le hF m (a + 1) (N' - (a + 1) * 2 ^ m) hlt
    have e : (a + 1) * 2 ^ m + (N' - (a + 1) * 2 ^ m) = N' := by omega
    rw [e] at hpre'
    have hblk := hF m a
    calc |F N' - F N| = |(F N' - F ((a + 1) * 2 ^ m)) + (F ((a + 1) * 2 ^ m) - F (a * 2 ^ m))
          - (F N - F (a * 2 ^ m))| := by ring_nf
      _ ≤ |F N' - F ((a + 1) * 2 ^ m)| + |F ((a + 1) * 2 ^ m) - F (a * 2 ^ m)|
          + |F N - F (a * 2 ^ m)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ B * m + B + B * m := by gcongr
      _ = B * (2 * m + 1) := by ring

/-- **Segment lemma.** For an aligned-block-bounded `F`, a segment of `L` indices changes `F` by
at most `B (2 ⌊log₂ L⌋ + 3)`. -/
theorem abs_sub_le_log {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N L : ℕ) :
    |F (N + L) - F N| ≤ B * (2 * Nat.log 2 L + 3) := by
  have hL : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have h := abs_sub_le_of_le_add_pow hF (m := Nat.log 2 L + 1) (N := N) (N' := N + L)
    (Nat.le_add_right N L) (by omega)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- The segment lemma for two indices in either order (`N' - N + (N - N')` is `|N' − N|`). -/
theorem abs_sub_le_log_dist {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N N' : ℕ) :
    |F N' - F N| ≤ B * (2 * Nat.log 2 (N' - N + (N - N')) + 3) := by
  rcases le_total N N' with h | h
  · have e : N' - N + (N - N') = N' - N := by omega
    have := abs_sub_le_log hF N (N' - N)
    rwa [Nat.add_sub_cancel' h, ← e] at this
  · have e : N' - N + (N - N') = N - N' := by omega
    have := abs_sub_le_log hF N' (N - N')
    rw [Nat.add_sub_cancel' h, abs_sub_comm, ← e] at this
    exact this

/-- **Global bound.** `|F N − F 0| ≤ B (⌊log₂ N⌋ + 1)`. -/
theorem abs_sub_zero_le_log {F : ℕ → ℝ} {B : ℝ} (hF : AlignedBlockBound F B) (N : ℕ) :
    |F N - F 0| ≤ B * (Nat.log 2 N + 1) := by
  have hN : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h := abs_sub_alignedPrefix_le hF (Nat.log 2 N + 1) 0 N hN
  rw [zero_mul, zero_add] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Per-block jump formula (abstract).** Let the `2^m` points `x (a 2^m + r)`, `r < 2^m`, of
an aligned block lie one in each dyadic cell: `r ↦ ⌊2^m x (a 2^m + r)⌋₊` is a bijection onto
`{0, …, 2^m − 1}`, with all points in `[0,1)`. Let `r*` be the index of the point in the cell of
`c ∈ [0,1)`. Then `#{r < 2^m : x (a 2^m + r) ≤ c} = ⌊2^m c⌋₊ + 1{x(a 2^m + r*) ≤ c}`. -/
theorem card_le_add_frac_eq {x : ℕ → ℝ} {m a rs : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hx0 : ∀ r < 2 ^ m, 0 ≤ x (a * 2 ^ m + r))
    (hinj : ∀ r < 2 ^ m, ∀ r' < 2 ^ m,
      ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ = ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r')⌋₊ → r = r')
    (hlt : ∀ r < 2 ^ m, ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ < 2 ^ m)
    (hrs : rs < 2 ^ m) (hcell : ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + rs)⌋₊ = ⌊(2 : ℝ) ^ m * c⌋₊) :
    ((range (2 ^ m)).filter fun r ↦ x (a * 2 ^ m + r) ≤ c).card =
      ⌊(2 : ℝ) ^ m * c⌋₊ + if x (a * 2 ^ m + rs) ≤ c then 1 else 0 := by
  classical
  set g : ℕ → ℕ := fun r ↦ ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ with hg
  set j0 := ⌊(2 : ℝ) ^ m * c⌋₊ with hj0
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  -- membership: `x ≤ c` iff the cell is below that of `c`, or it is `c`'s cell and `x ≤ c`
  have key : ∀ r < 2 ^ m,
      (x (a * 2 ^ m + r) ≤ c ↔ g r < j0 ∨ (r = rs ∧ x (a * 2 ^ m + rs) ≤ c)) := by
    intro r hr
    have hx := hx0 r hr
    constructor
    · intro hle
      have hmono : g r ≤ j0 := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle hp.le)
      rcases hmono.lt_or_eq with h | h
      · exact Or.inl h
      · right
        have := hinj r hr rs hrs (h.trans hcell.symm)
        exact ⟨this, this ▸ hle⟩
    · rintro (h | ⟨rfl, h⟩)
      · have h1 : (2 : ℝ) ^ m * x (a * 2 ^ m + r) < g r + 1 := Nat.lt_floor_add_one _
        have h2 : ((g r : ℕ) : ℝ) + 1 ≤ j0 := by exact_mod_cast h
        have h3 : (j0 : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
        have : (2 : ℝ) ^ m * x (a * 2 ^ m + r) ≤ 2 ^ m * c := by linarith
        exact le_of_mul_le_mul_left this hp
      · exact h
  have hfilter : (range (2 ^ m)).filter (fun r ↦ x (a * 2 ^ m + r) ≤ c) =
      ((range (2 ^ m)).filter fun r ↦ g r < j0) ∪
        (if x (a * 2 ^ m + rs) ≤ c then {rs} else ∅) := by
    ext r
    simp only [mem_filter, mem_range, mem_union]
    constructor
    · rintro ⟨hr, h⟩
      rcases (key r hr).1 h with h' | ⟨rfl, h'⟩
      · exact Or.inl ⟨hr, h'⟩
      · right
        simp [h']
    · rintro (⟨hr, h⟩ | h)
      · exact ⟨hr, (key r hr).2 (Or.inl h)⟩
      · by_cases hc : x (a * 2 ^ m + rs) ≤ c
        · simp only [hc, ite_true, mem_singleton] at h
          subst h
          exact ⟨hrs, hc⟩
        · simp [hc] at h
  have hdisj : Disjoint ((range (2 ^ m)).filter fun r ↦ g r < j0)
      (if x (a * 2 ^ m + rs) ≤ c then {rs} else ∅) := by
    by_cases hc : x (a * 2 ^ m + rs) ≤ c
    · simp only [hc, ite_true, disjoint_singleton_right, mem_filter, mem_range, not_and,
        not_lt]
      intro _
      rw [hg]
      exact hcell.ge
    · simp [hc]
  -- the cells below `c`'s: `g` is a bijection from `{r : g r < j0}` onto `range j0`
  have hj0lt : j0 < 2 ^ m := by
    have : (2 : ℝ) ^ m * c < 2 ^ m := by nlinarith
    have h := Nat.floor_lt (by positivity : (0 : ℝ) ≤ 2 ^ m * c) |>.2
      (by exact_mod_cast this : (2 : ℝ) ^ m * c < ((2 ^ m : ℕ) : ℝ))
    exact h
  have hcard : ((range (2 ^ m)).filter fun r ↦ g r < j0).card = j0 := by
    have hbij : ((range (2 ^ m)).filter fun r ↦ g r < j0).card = (range j0).card := by
      refine card_bij (fun r _ ↦ g r) ?_ ?_ ?_
      · intro r hr
        simp only [mem_filter] at hr
        exact mem_range.2 hr.2
      · intro r hr r' hr' h
        simp only [mem_filter, mem_range] at hr hr'
        exact hinj r hr.1 r' hr'.1 h
      · -- surjectivity: `g` maps `range (2^m)` injectively into `range (2^m)`, so onto
        intro j hj
        have hsurj : (range (2 ^ m)).image g = range (2 ^ m) := by
          refine eq_of_subset_of_card_le ?_ ?_
          · intro y hy
            obtain ⟨r, hr, rfl⟩ := mem_image.1 hy
            exact mem_range.2 (hlt r (mem_range.1 hr))
          · rw [card_image_of_injOn]
            intro r hr r' hr' h
            exact hinj r (mem_range.1 hr) r' (mem_range.1 hr') h
        have hjm : j ∈ (range (2 ^ m)).image g := by
          rw [hsurj]
          exact mem_range.2 ((mem_range.1 hj).trans hj0lt)
        obtain ⟨r, hr, hrj⟩ := mem_image.1 hjm
        refine ⟨r, ?_, hrj⟩
        simp only [mem_filter]
        exact ⟨hr, hrj ▸ mem_range.1 hj⟩
    rw [hbij, card_range]
  rw [hfilter, card_union_of_disjoint hdisj, hcard]
  by_cases hc : x (a * 2 ^ m + rs) ≤ c
  · simp [hc]
  · simp [hc]

/-- **One point per cell gives the block bound.** If every aligned block of `x` has one point
in each dyadic cell (all points in `[0,1)`), then the local discrepancy partial sums
`F N = #{k < N : x k ≤ c} − N c` satisfy `AlignedBlockBound F 1`. -/
theorem alignedBlockBound_of_cells {x : ℕ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hx0 : ∀ k, 0 ≤ x k)
    (hinj : ∀ m a, ∀ r < 2 ^ m, ∀ r' < 2 ^ m,
      ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ = ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r')⌋₊ → r = r')
    (hlt : ∀ m a, ∀ r < 2 ^ m, ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊ < 2 ^ m) :
    AlignedBlockBound
      (fun N ↦ (((range N).filter fun k ↦ x k ≤ c).card : ℝ) - N * c) 1 := by
  classical
  intro m a
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  -- the point in the cell of `c`
  have hj0lt : ⌊(2 : ℝ) ^ m * c⌋₊ < 2 ^ m := by
    have : (2 : ℝ) ^ m * c < 2 ^ m := by nlinarith
    exact Nat.floor_lt (by positivity) |>.2 (by exact_mod_cast this)
  have hsurj : (range (2 ^ m)).image (fun r ↦ ⌊(2 : ℝ) ^ m * x (a * 2 ^ m + r)⌋₊) =
      range (2 ^ m) := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hy
      exact mem_range.2 (hlt m a r (mem_range.1 hr))
    · rw [card_image_of_injOn]
      intro r hr r' hr' h
      exact hinj m a r (mem_range.1 hr) r' (mem_range.1 hr') h
  obtain ⟨rs, hrs, hcell⟩ := mem_image.1 (hsurj ▸ mem_range.2 hj0lt :
    ⌊(2 : ℝ) ^ m * c⌋₊ ∈ (range (2 ^ m)).image _)
  have hrs' := mem_range.1 hrs
  have hblock := card_le_add_frac_eq hc0 hc1 (fun r _ ↦ hx0 _) (hinj m a) (hlt m a) hrs' hcell
  -- split the count over `[0, (a+1) 2^m)` into `[0, a 2^m)` and the block
  have hsplit : ((range ((a + 1) * 2 ^ m)).filter fun k ↦ x k ≤ c).card =
      ((range (a * 2 ^ m)).filter fun k ↦ x k ≤ c).card +
        ((range (2 ^ m)).filter fun r ↦ x (a * 2 ^ m + r) ≤ c).card := by
    have e : (a + 1) * 2 ^ m = a * 2 ^ m + 2 ^ m := by ring
    rw [e, card_filter, card_filter, card_filter, sum_range_add]
  simp only
  rw [hsplit, hblock]
  push_cast
  have hfl0 : (⌊(2 : ℝ) ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
  have hfl1 : (2 : ℝ) ^ m * c < ⌊(2 : ℝ) ^ m * c⌋₊ + 1 := Nat.lt_floor_add_one _
  have hI0 : (0 : ℝ) ≤ if x (a * 2 ^ m + rs) ≤ c then 1 else 0 := by split_ifs <;> norm_num
  have hI1 : (if x (a * 2 ^ m + rs) ≤ c then 1 else 0 : ℝ) ≤ 1 := by split_ifs <;> norm_num
  rw [abs_le]
  constructor <;> nlinarith

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A Lindeberg CLT for triangular arrays of bounded independent terms (for post #2)

Copied from `RQMCMarkov/OwenScrambling`.

Mathlib has the CLT for i.i.d. sequences only. Post #2's claim about Owen scrambling ("a standard
CLT applies") concerns sums of independent but NOT identically distributed terms (one per cell of
the net, see `Owen1DScramble`), whose number grows with `n`: a triangular array. This module
proves the CLT for such arrays under the bounded form of Lindeberg's condition, by characteristic
functions and Lévy's continuity theorem (Mathlib's
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`).

## Main results

* `norm_prod_sub_prod_le`: `‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖` when all `‖aᵢ‖, ‖cᵢ‖ ≤ 1`.
* `norm_charFun_sub_le_of_abs_le`: for centred `X` with `|X| ≤ δ` a.s. and `|t| δ ≤ 1`,
  `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`.
* `tendstoInDistribution_sum_of_bounded` (**Lindeberg CLT, bounded form**): for each `n` let
  `X n 0, …, X n (L n − 1)` be independent and centred on a probability space `(Ωₙ, Pₙ)` with
  `|X n i| ≤ δₙ` a.s., `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i ⇒ N(0, v)`.

The bounded condition `max |X n i| ≤ δₙ → 0` with `Σᵢ Var → v` implies Lindeberg's condition
(each truncated second moment vanishes once `δₙ < ε`), and it is what the stratified estimator
satisfies for `C¹` integrands.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology

/-- **Telescoping bound for products** of complex numbers of norm at most one:
`‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖`. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a c : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ ≤ ∑ i ∈ s, ‖a i - c i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, sub_self, norm_zero, Finset.sum_empty]
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
      have hc' : ∀ i ∈ s, ‖c i‖ ≤ 1 := fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
      have hQ : ‖∏ i ∈ s, c i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) hc'
      have haj := ha j (Finset.mem_insert_self j s)
      have heq : a j * ∏ i ∈ s, a i - c j * ∏ i ∈ s, c i =
          a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i := by ring
      rw [heq]
      calc ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i‖
          ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ + ‖a j - c j‖ * ‖∏ i ∈ s, c i‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ 1 * ∑ i ∈ s, ‖a i - c i‖ + ‖a j - c j‖ * 1 := by
            gcongr
            exact ih ha' hc'
        _ = ‖a j - c j‖ + ∑ i ∈ s, ‖a i - c i‖ := by ring

/-- The cubic Taylor bound for `e^{iy}`: `‖e^{iy} − (1 − y²/2 + i y)‖ ≤ |y|³` for `|y| ≤ 1`. -/
theorem norm_cexp_mul_I_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ |y| ^ 3 := by
  have hz : ‖(y : ℂ) * I‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := (y : ℂ) * I) (by rw [hz]; exact hy) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      mul_pow, I_sq, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]
    push_cast
    ring
  rw [hsum, hz] at hb
  refine hb.trans ?_
  have h3 : (0 : ℝ) ≤ |y| ^ 3 := by positivity
  have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  calc |y| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹)
      ≤ |y| ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h3
    _ = |y| ^ 3 := mul_one _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Characteristic function of a bounded centred variable**: if `|X| ≤ δ` a.s., `E[X] = 0` and
`|t| δ ≤ 1`, then `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`. -/
theorem norm_charFun_sub_le_of_abs_le {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {δ : ℝ} (hb : ∀ᵐ ω ∂P, |X ω| ≤ δ) (h0 : ∫ ω, X ω ∂P = 0) {t : ℝ}
    (ht : |t| * δ ≤ 1) :
    ‖charFun (P.map X) t - ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * δ * ∫ ω, X ω ^ 2 ∂P := by
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable δ
    (hb.mono fun ω hω ↦ by rw [Real.norm_eq_abs]; exact hω)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) P := by
    refine Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (δ ^ 2) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  set q : Ω → ℂ := fun ω ↦ ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ((t * X ω : ℝ) : ℂ) * I with hq
  have hqi : Integrable q P := by
    refine Integrable.add ?_ ?_
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have hqint : ∫ ω, q ω ∂P = ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) := by
    rw [hq, integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_const_mul, h0, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    · congr 1
      rw [integral_sub (integrable_const 1) ((hX2.const_mul (t ^ 2)).div_const 2 |>.congr
        (Eventually.of_forall fun ω ↦ by
          change t ^ 2 * X ω ^ 2 / 2 = (t * X ω) ^ 2 / 2
          rw [mul_pow])), integral_const, integral_div,
        integral_congr_ae (Eventually.of_forall fun ω ↦ (mul_pow t (X ω) 2 : _)),
        integral_const_mul]
      rw [probReal_univ, one_smul]
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have he : Integrable (fun ω ↦ cexp (((t * X ω : ℝ) : ℂ) * I)) P := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω ↦ ?_)
    · exact (Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hX.const_mul t).aestronglyMeasurable).mul aestronglyMeasurable_const))
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hcf : charFun (P.map X) t = ∫ ω, cexp (((t * X ω : ℝ) : ℂ) * I) ∂P := by
    rw [charFun_apply_real, integral_map hX]
    · congr 1
      funext ω
      push_cast
      rfl
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const)).aestronglyMeasurable
  rw [hcf, ← hqint, ← integral_sub he hqi]
  refine (norm_integral_le_of_norm_le ((hX2.const_mul (|t| ^ 3 * δ))) ?_).trans ?_
  · filter_upwards [hb] with ω hω
    have hy : |t * X ω| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans ht
    refine (norm_cexp_mul_I_sub_le hy).trans ?_
    have h3 : |X ω| ^ 3 = |X ω| * X ω ^ 2 := by
      rw [← sq_abs (X ω)]
      ring
    rw [abs_mul, mul_pow, h3]
    have hX0 : 0 ≤ X ω ^ 2 := sq_nonneg _
    have ht0 : 0 ≤ |t| ^ 3 := by positivity
    calc |t| ^ 3 * (|X ω| * X ω ^ 2) ≤ |t| ^ 3 * (δ * X ω ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hω hX0) ht0
      _ = |t| ^ 3 * δ * X ω ^ 2 := by ring
  · rw [integral_const_mul]

/-- **Lindeberg CLT for triangular arrays, bounded form.** For each `n` let `X n i`, `i < L n`, be
independent, centred random variables on a probability space `(Ωₙ, Pₙ)`, with `|X n i| ≤ δₙ`
almost surely, `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i` converges in distribution to
`N(0, v)`. -/
theorem tendstoInDistribution_sum_of_bounded {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {L : ℕ → ℕ}
    {X : (n : ℕ) → Fin (L n) → Ω n → ℝ} (hXm : ∀ n i, AEMeasurable (X n i) (P n))
    (hind : ∀ n, iIndepFun (X n) (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hbd : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω| ≤ δ n)
    {v : ℝ} (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 v))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Z P P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    -- notation
    set w : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ ∫ ω, X n i ω ^ 2 ∂(P n) with hw
    set sv : ℕ → ℝ := fun n ↦ ∑ i, w n i with hsv
    have hw0 : ∀ n i, 0 ≤ w n i := fun n i ↦ integral_nonneg fun ω ↦ sq_nonneg _
    have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦ hw0 n i
    have hwδ : ∀ n i, w n i ≤ δ n ^ 2 := by
      intro n i
      have h : ∫ ω, X n i ω ^ 2 ∂(P n) ≤ ∫ _ω, δ n ^ 2 ∂(P n) := by
        refine integral_mono_ae ?_ (integrable_const _) ?_
        · refine Integrable.of_bound ((hXm n i).pow_const 2).aestronglyMeasurable (δ n ^ 2) ?_
          filter_upwards [hbd n i] with ω hω
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        · filter_upwards [hbd n i] with ω hω
          rw [← sq_abs (X n i ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      rw [integral_const, probReal_univ, one_smul] at h
      exact h
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t) atTop
      (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      congr 1
      ring
    rw [htarget]
    have hprod : ∀ n, charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t =
        ∏ i, charFun ((P n).map (X n i)) t := fun n ↦ by
      rw [(hind n).charFun_map_fun_sum_eq_prod (hXm n), Finset.prod_apply]
    simp_rw [hprod]
    -- the Gaussian comparison products
    set a : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ t ^ 2 * w n i / 2 with ha
    have hcprod : ∀ n, ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2 * sv n / 2)) : ℝ) : ℂ) := fun n ↦ by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      congr 3
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hlimc : Tendsto (fun n ↦ ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ)) := by
      simp_rw [hcprod]
      refine Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((hv.const_mul (t ^ 2)).div_const 2).neg
    -- the error bound
    set B : ℕ → ℝ := fun n ↦ |t| ^ 3 * |δ n| * sv n + t ^ 2 * δ n ^ 2 / 2 * (t ^ 2 * sv n / 2)
      with hB
    have hB0 : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto B atTop
          (𝓝 (|t| ^ 3 * |(0 : ℝ)| * v + t ^ 2 * (0 : ℝ) ^ 2 / 2 * (t ^ 2 * v / 2))) := by
        refine Tendsto.add ((tendsto_const_nhds.mul hδ.abs).mul hv) ?_
        exact (((tendsto_const_nhds.mul (hδ.pow 2)).div_const 2).mul
          ((hv.const_mul (t ^ 2)).div_const 2))
      rw [abs_zero] at h1
      convert h1 using 2
      ring
    have hev : ∀ᶠ n in atTop, |t| * |δ n| ≤ 1 := by
      have h := (tendsto_const_nhds (x := |t|)).mul hδ.abs
      rw [abs_zero, mul_zero] at h
      exact h.eventually (ge_mem_nhds one_pos)
    have hbound : ∀ᶠ n in atTop, ‖∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤ B n := by
      filter_upwards [hev] with n hn
      have hai0 : ∀ i, 0 ≤ a n i := fun i ↦ by
        rw [ha]
        have := hw0 n i
        positivity
      have haiδ : ∀ i, a n i ≤ t ^ 2 * δ n ^ 2 / 2 := fun i ↦ by
        rw [ha]
        have := hwδ n i
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have := mul_le_mul_of_nonneg_left this ht2
        linarith
      have htd : t ^ 2 * δ n ^ 2 ≤ 1 := by
        have h1 : (|t| * |δ n|) ^ 2 ≤ 1 := by
          have h0' : 0 ≤ |t| * |δ n| := by positivity
          nlinarith
        rw [mul_pow, sq_abs, sq_abs] at h1
        exact h1
      have hai1 : ∀ i, a n i ≤ 1 := fun i ↦ by linarith [haiδ i]
      refine (norm_prod_sub_prod_le Finset.univ _ _ (fun i _ ↦ norm_charFun_le_one _)
        (fun i _ ↦ ?_)).trans ?_
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        linarith [hai0 i]
      have hterm : ∀ i, ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
          |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := by
        intro i
        have h1 := norm_charFun_sub_le_of_abs_le (hXm n i)
          ((hbd n i).mono fun ω hω ↦ hω.trans (le_abs_self _)) (h0 n i) hn
        have h2 : |Real.exp (-a n i) - 1 - (-a n i)| ≤ (-a n i) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (hai0 i)]; exact hai1 i)
        have h3 : ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
            t ^ 2 * δ n ^ 2 / 2 * a n i := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - t ^ 2 * w n i / 2 - Real.exp (-a n i) =
              -(Real.exp (-a n i) - 1 - (-a n i)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq, sq]
          exact mul_le_mul_of_nonneg_right (haiδ i) (hai0 i)
        calc ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖
            ≤ ‖charFun ((P n).map (X n i)) t - (((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := add_le_add h1 h3
      refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hB]
      congr 2
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hdiff : Tendsto (fun n ↦ ∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop (𝓝 0) :=
      squeeze_zero_norm' hbound hB0
    have := hdiff.add hlimc
    rw [zero_add] at this
    refine this.congr (fun n ↦ ?_)
    ring

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A CLT for sums of locally dependent terms of an i.i.d. sequence (for post #3)

Post #3 reports that "normality cannot be rejected for the per-state Sobol sequences ((ii) and
(iii))". For base-2 scrambled van der Corput stacks the error of the chain is (up to a
negligible remainder) a sum over the binary levels `m` of terms that are functions of i.i.d.
fair coins `e_m, e_{m+1}, …` (`CltPathBits`), each depending on coins far above `m` only with
geometrically small probability. This module proves the central limit theorem for such sums,
by truncating every term at depth `L` (an `L`-dependent array) and Bernstein's big-block /
small-block method, with the bounded Lindeberg CLT (`Owen1DLindeberg`).

## Main results

* `IsLocal F S`: `F : (ι → α) → β` depends only on the coordinates in the finite set `S`;
  `IsLocal.measurable` (for countable discrete `α`), `IsLocal.indepFun` (functions local on
  disjoint sets are independent under a product measure `Measure.infinitePi`).
* `charFun_map_sum_range_eq_prod`: sequential independence makes the characteristic function of
  a sum the product of the characteristic functions.
* `tendstoInDistribution_sum_range_of_bounded`: the bounded Lindeberg CLT under sequential
  independence (sums over `range (L n)`).
* `tendstoInMeasure_of_integral_sq`: second moments tending to `0` give convergence in measure.
* `sq_covariance_le`: Cauchy–Schwarz for the covariance.
* `tendstoInDistribution_of_blocks`: if `X n = Σ_b U n b + D n` with sequentially independent
  bounded blocks, `max |U n b| = o(σ_n)` and `Var D n = o(σ_n²)`, then
  `(X n − E X n)/σ_n ⇒ N(0,1)`.
* `tendstoInDistribution_of_truncations` (**the dependent CLT**): let `Y n m`, `m < K n`, be
  bounded by `B`, and for every depth `L` let `Yt n m L` be bounded by `B`, depend only on
  coordinates of levels in `[m, m + L)`, with `E[(Y n m − Yt n m L)²] ≤ C 2^{-L}`. If
  `K n → ∞` and `Var(Σ_m Y n m) ≥ κ K n` eventually, then the normalised sums are
  asymptotically `N(0,1)`. The proof takes `L = 2(⌊log₂ K⌋ + 1)` (so `K² 2^{-L} ≤ 1`: the
  truncation costs `O(1)` in `L²`) and windows of length `p = L³` (so `p = o(√K)` and
  `L²/p → 0`): the condition `L_K² ≪ p_K ≪ √K`, made explicit.
* `tendsto_natLog_pow_six_div`, `sqrt_variance_sum_le`, `abs_sqrt_variance_sub_le`: tools.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Local functions of a product -/

/-- `F` depends only on the coordinates in the finite set `S`. -/
def IsLocal {ι α β : Type*} (F : (ι → α) → β) (S : Finset ι) : Prop :=
  ∀ ω ω' : ι → α, (∀ i ∈ S, ω i = ω' i) → F ω = F ω'

variable {ι α β γ : Type*}

/-- Locality is inherited by larger coordinate sets. -/
theorem IsLocal.mono {F : (ι → α) → β} {S T : Finset ι} (h : IsLocal F S) (hST : S ⊆ T) :
    IsLocal F T :=
  fun ω ω' hω ↦ h ω ω' fun i hi ↦ hω i (hST hi)

/-- A function of a local function is local. -/
theorem IsLocal.comp {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) (g : β → γ) :
    IsLocal (fun ω ↦ g (F ω)) S :=
  fun ω ω' hω ↦ congrArg g (h ω ω' hω)

/-- Constants are local on any set. -/
theorem isLocal_const (b : β) (S : Finset ι) : IsLocal (fun _ : ι → α ↦ b) S :=
  fun _ _ _ ↦ rfl

/-- Sums of functions local on `S` are local on `S`. -/
theorem isLocal_sum {κ : Type*} {F : κ → (ι → α) → ℝ} {S : Finset ι} (s : Finset κ)
    (h : ∀ k ∈ s, IsLocal (F k) S) : IsLocal (fun ω ↦ ∑ k ∈ s, F k ω) S :=
  fun ω ω' hω ↦ Finset.sum_congr rfl fun k hk ↦ h k hk ω ω' hω

/-- The sum of two functions local on `S` is local on `S`. -/
theorem IsLocal.add {F G : (ι → α) → ℝ} {S : Finset ι} (hF : IsLocal F S) (hG : IsLocal G S) :
    IsLocal (fun ω ↦ F ω + G ω) S :=
  fun ω ω' hω ↦ by simp only [hF ω ω' hω, hG ω ω' hω]

open Classical in
/-- Extension of a point of `S → α` to `ι → α` by a fixed point `ω₀` off `S`. -/
noncomputable def localExtend (S : Finset ι) (ω₀ : ι → α) (g : S → α) : ι → α :=
  fun i ↦ if h : i ∈ S then g ⟨i, h⟩ else ω₀ i

/-- A local function factors through the restriction to its coordinate set. -/
theorem IsLocal.eq_restrict {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) (ω₀ : ι → α)
    (ω : ι → α) : F ω = F (localExtend S ω₀ (S.restrict ω)) := by
  refine h _ _ fun i hi ↦ ?_
  simp only [localExtend, hi, dite_true, Finset.restrict]

variable [MeasurableSpace α]

/-- **Local functions are measurable** (countable discrete coordinate space). -/
theorem IsLocal.measurable [Countable α] [MeasurableSingletonClass α] [Nonempty α]
    [MeasurableSpace β] {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) : Measurable F := by
  have ω₀ : ι → α := fun _ ↦ Classical.arbitrary α
  have : F = (fun g ↦ F (localExtend S ω₀ g)) ∘ S.restrict := funext (h.eq_restrict ω₀)
  rw [this]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict S)

/-- **Independence of local functions.** Under a product measure, functions depending on
disjoint finite sets of coordinates are independent. -/
theorem IsLocal.indepFun [Countable α] [MeasurableSingletonClass α] [Nonempty α]
    [MeasurableSpace β] [MeasurableSpace γ] (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    {F : (ι → α) → β} {G : (ι → α) → γ} {S T : Finset ι} (hF : IsLocal F S) (hG : IsLocal G T)
    (hST : Disjoint S T) : IndepFun F G (Measure.infinitePi ν) := by
  have ω₀ : ι → α := fun _ ↦ Classical.arbitrary α
  have hcoord : iIndepFun (fun i (ω : ι → α) ↦ ω i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hST' := hcoord.indepFun_finset S T hST (fun i ↦ measurable_pi_apply i)
  have h1 : F = (fun g ↦ F (localExtend S ω₀ g)) ∘ (fun ω (i : S) ↦ ω i) :=
    funext (hF.eq_restrict ω₀)
  have h2 : G = (fun g ↦ G (localExtend T ω₀ g)) ∘ (fun ω (i : T) ↦ ω i) :=
    funext (hG.eq_restrict ω₀)
  rw [h1, h2]
  exact hST'.comp (measurable_of_countable _) (measurable_of_countable _)

/-! ### The Lindeberg CLT under sequential independence -/

/-- **Characteristic function of a sequentially independent sum.** If each `X i` is independent
of the partial sum of its predecessors, the characteristic function of `Σ_{i<k} X i` is the
product of the characteristic functions. -/
theorem charFun_map_sum_range_eq_prod {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) P)
    (hind : ∀ i, IndepFun (fun ω ↦ ∑ j ∈ range i, X j ω) (X i) P) (k : ℕ) (t : ℝ) :
    charFun (P.map fun ω ↦ ∑ i ∈ range k, X i ω) t = ∏ i ∈ range k, charFun (P.map (X i)) t := by
  induction k with
  | zero =>
      simp only [range_zero, sum_empty, prod_empty, Measure.map_const, measure_univ, one_smul,
        charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  | succ k ih =>
      have hsum : (fun ω ↦ ∑ i ∈ range (k + 1), X i ω) =
          fun ω ↦ (∑ i ∈ range k, X i ω) + X k ω := funext fun ω ↦ sum_range_succ _ _
      rw [hsum, (hind k).charFun_map_fun_add_eq_mul
        (Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm i) (hXm k), Pi.mul_apply, ih,
        prod_range_succ]

/-- **Lindeberg CLT, bounded form, sequential independence.** For each `n` let `X n i`,
`i < L n`, be centred random variables on `(Ωₙ, Pₙ)`, each independent of the partial sum of its
predecessors, with `|X n i| ≤ δₙ` a.s., `δₙ → 0` and `Σ_{i<L n} E[(X n i)²] → v`. Then
`Σ_{i<L n} X n i ⇒ N(0, v)`. (The proof of `tendstoInDistribution_sum_of_bounded`, with the
product formula `charFun_map_sum_range_eq_prod` in place of mutual independence.) -/
theorem tendstoInDistribution_sum_range_of_bounded {Ω : ℕ → Type*}
    {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {L : ℕ → ℕ} {X : (n : ℕ) → ℕ → Ω n → ℝ}
    (hXm : ∀ n i, AEMeasurable (X n i) (P n))
    (hind : ∀ n i, IndepFun (fun ω ↦ ∑ j ∈ range i, X n j ω) (X n i) (P n))
    (h0 : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hbd : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω| ≤ δ n)
    {v : ℝ} (hv : Tendsto (fun n ↦ ∑ i ∈ range (L n), ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 v))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i ∈ range (L n), X n i ω) atTop Z P P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    set w : (n : ℕ) → ℕ → ℝ := fun n i ↦ ∫ ω, X n i ω ^ 2 ∂(P n) with hw
    set sv : ℕ → ℝ := fun n ↦ ∑ i ∈ range (L n), w n i with hsv
    have hw0 : ∀ n i, 0 ≤ w n i := fun n i ↦ integral_nonneg fun ω ↦ sq_nonneg _
    have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦ hw0 n i
    have hwδ : ∀ n i, w n i ≤ δ n ^ 2 := by
      intro n i
      have h : ∫ ω, X n i ω ^ 2 ∂(P n) ≤ ∫ _ω, δ n ^ 2 ∂(P n) := by
        refine integral_mono_ae ?_ (integrable_const _) ?_
        · refine Integrable.of_bound ((hXm n i).pow_const 2).aestronglyMeasurable (δ n ^ 2) ?_
          filter_upwards [hbd n i] with ω hω
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        · filter_upwards [hbd n i] with ω hω
          rw [← sq_abs (X n i ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      rw [integral_const, probReal_univ, one_smul] at h
      exact h
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ ∑ i ∈ range (L n), X n i ω) t) atTop
      (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      congr 1
      ring
    rw [htarget]
    have hprod : ∀ n, charFun ((P n).map fun ω ↦ ∑ i ∈ range (L n), X n i ω) t =
        ∏ i ∈ range (L n), charFun ((P n).map (X n i)) t := fun n ↦
      charFun_map_sum_range_eq_prod (hXm n) (hind n) (L n) t
    simp_rw [hprod]
    set a : (n : ℕ) → ℕ → ℝ := fun n i ↦ t ^ 2 * w n i / 2 with ha
    have hcprod : ∀ n, ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2 * sv n / 2)) : ℝ) : ℂ) := fun n ↦ by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      congr 3
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hlimc : Tendsto (fun n ↦ ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ)) := by
      simp_rw [hcprod]
      refine Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((hv.const_mul (t ^ 2)).div_const 2).neg
    set B : ℕ → ℝ := fun n ↦ |t| ^ 3 * |δ n| * sv n + t ^ 2 * δ n ^ 2 / 2 * (t ^ 2 * sv n / 2)
      with hB
    have hB0 : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto B atTop
          (𝓝 (|t| ^ 3 * |(0 : ℝ)| * v + t ^ 2 * (0 : ℝ) ^ 2 / 2 * (t ^ 2 * v / 2))) := by
        refine Tendsto.add ((tendsto_const_nhds.mul hδ.abs).mul hv) ?_
        exact (((tendsto_const_nhds.mul (hδ.pow 2)).div_const 2).mul
          ((hv.const_mul (t ^ 2)).div_const 2))
      rw [abs_zero] at h1
      convert h1 using 2
      ring
    have hev : ∀ᶠ n in atTop, |t| * |δ n| ≤ 1 := by
      have h := (tendsto_const_nhds (x := |t|)).mul hδ.abs
      rw [abs_zero, mul_zero] at h
      exact h.eventually (ge_mem_nhds one_pos)
    have hbound : ∀ᶠ n in atTop, ‖∏ i ∈ range (L n), charFun ((P n).map (X n i)) t -
        ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤ B n := by
      filter_upwards [hev] with n hn
      have hai0 : ∀ i, 0 ≤ a n i := fun i ↦ by
        rw [ha]
        have := hw0 n i
        positivity
      have haiδ : ∀ i, a n i ≤ t ^ 2 * δ n ^ 2 / 2 := fun i ↦ by
        rw [ha]
        have := hwδ n i
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have := mul_le_mul_of_nonneg_left this ht2
        linarith
      have htd : t ^ 2 * δ n ^ 2 ≤ 1 := by
        have h1 : (|t| * |δ n|) ^ 2 ≤ 1 := by
          have h0' : 0 ≤ |t| * |δ n| := by positivity
          nlinarith
        rw [mul_pow, sq_abs, sq_abs] at h1
        exact h1
      have hai1 : ∀ i, a n i ≤ 1 := fun i ↦ by linarith [haiδ i]
      refine (norm_prod_sub_prod_le (range (L n)) _ _ (fun i _ ↦ norm_charFun_le_one _)
        (fun i _ ↦ ?_)).trans ?_
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        linarith [hai0 i]
      have hterm : ∀ i, ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
          |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := by
        intro i
        have h1 := norm_charFun_sub_le_of_abs_le (hXm n i)
          ((hbd n i).mono fun ω hω ↦ hω.trans (le_abs_self _)) (h0 n i) hn
        have h2 : |Real.exp (-a n i) - 1 - (-a n i)| ≤ (-a n i) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (hai0 i)]; exact hai1 i)
        have h3 : ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
            t ^ 2 * δ n ^ 2 / 2 * a n i := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - t ^ 2 * w n i / 2 - Real.exp (-a n i) =
              -(Real.exp (-a n i) - 1 - (-a n i)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq, sq]
          exact mul_le_mul_of_nonneg_right (haiδ i) (hai0 i)
        calc ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖
            ≤ ‖charFun ((P n).map (X n i)) t - (((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := add_le_add h1 h3
      refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hB]
      congr 2
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hdiff : Tendsto (fun n ↦ ∏ i ∈ range (L n), charFun ((P n).map (X n i)) t -
        ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)) atTop (𝓝 0) :=
      squeeze_zero_norm' hbound hB0
    have := hdiff.add hlimc
    rw [zero_add] at this
    refine this.congr (fun n ↦ ?_)
    ring

/-! ### Second-moment tools -/

/-- **Second moments to zero give convergence in measure** (Chebyshev). -/
theorem tendstoInMeasure_of_integral_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (h : Tendsto (fun n ↦ ∫ ω, f n ω ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_)
    ((h.div_const (ε ^ 2)).trans (by rw [zero_div]))
  have hint : Integrable (fun ω ↦ f n ω ^ 2) μ := (hf n).integrable_sq
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg (f n ω))
    hint (ε ^ 2)
  have hsub : {x | ε ≤ ‖f n x - 0‖} ⊆ {x | ε ^ 2 ≤ f n x ^ 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hx ⊢
    rw [← sq_abs (f n x)]
    exact pow_le_pow_left₀ hε.le hx 2
  calc μ.real {x | ε ≤ ‖f n x - 0‖} ≤ μ.real {x | ε ^ 2 ≤ f n x ^ 2} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (∫ ω, f n ω ^ 2 ∂μ) / ε ^ 2 := by
        rw [le_div_iff₀ hε2, mul_comm]
        exact hmk

/-- **Cauchy–Schwarz for the covariance**: `cov[X, Y]² ≤ Var X · Var Y`. -/
theorem sq_covariance_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have hq : ∀ t : ℝ, 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    intro t
    have h := variance_fun_add (hX.const_mul t) hY
    rw [variance_const_mul, covariance_const_mul_left] at h
    have h0 := variance_nonneg (fun ω ↦ t * X ω + Y ω) μ
    rw [h] at h0
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- `|cov[X, Y]| ≤ √Var X · √Var Y`. -/
theorem abs_covariance_le_sqrt {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |cov[X, Y; μ]| ≤ √Var[X; μ] * √Var[Y; μ] := by
  rw [← Real.sqrt_mul (variance_nonneg _ _), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_covariance_le hX hY)

/-- **Triangle inequality for the standard deviation.** -/
theorem sqrt_variance_add_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    √Var[fun ω ↦ X ω + Y ω; μ] ≤ √Var[X; μ] + √Var[Y; μ] := by
  have hc := abs_covariance_le_sqrt hX hY
  have hsX := Real.sq_sqrt (variance_nonneg X μ)
  have hsY := Real.sq_sqrt (variance_nonneg Y μ)
  rw [Real.sqrt_le_left (by positivity), variance_fun_add hX hY]
  nlinarith [le_abs_self (cov[X, Y; μ])]

/-- The standard deviations of `X` and `W` differ by at most that of `X − W`. -/
theorem abs_sqrt_variance_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X W : Ω → ℝ} (hX : MemLp X 2 μ) (hW : MemLp W 2 μ) :
    |√Var[W; μ] - √Var[X; μ]| ≤ √Var[fun ω ↦ X ω - W ω; μ] := by
  have hD : MemLp (fun ω ↦ X ω - W ω) 2 μ := hX.sub hW
  have h1 := sqrt_variance_add_le hW hD
  have h2 := sqrt_variance_add_le hX hD.neg
  have e1 : (fun ω ↦ W ω + (X ω - W ω)) = X := funext fun ω ↦ by ring
  have e2 : (fun ω ↦ X ω + (-(fun ω ↦ X ω - W ω)) ω) = W := funext fun ω ↦ by simp
  have e3 : Var[-(fun ω ↦ X ω - W ω); μ] = Var[fun ω ↦ X ω - W ω; μ] := variance_neg
  rw [e1] at h1
  rw [e2, e3] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The CLT from independent bounded blocks -/

/-- **CLT from sequentially independent bounded blocks.** On a fixed probability space let
`X n = Σ_{b < J n} U n b + D n`, where each block `U n b` is independent of the sum of the
previous blocks, the blocks are pairwise independent, `|U n b| ≤ M n` with `M n = o(σ_n)`, and
`Var (D n) = o(σ_n²)`, `σ_n² = Var (X n)`. Then `(X n − E X n)/σ_n ⇒ N(0,1)`. -/
theorem tendstoInDistribution_of_blocks {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {U : ℕ → ℕ → Ω → ℝ} {J : ℕ → ℕ} {M : ℕ → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hUm : ∀ n b, Measurable (U n b))
    (hUb : ∀ n b ω, |U n b ω| ≤ M n)
    (hind : ∀ n b, IndepFun (fun ω ↦ ∑ j ∈ range b, U n j ω) (U n b) μ)
    (hpair : ∀ n b b', b ≠ b' → IndepFun (U n b) (U n b') μ)
    (hpos : ∀ᶠ n in atTop, 0 < Var[X n; μ])
    (hM : Tendsto (fun n ↦ M n / √Var[X n; μ]) atTop (𝓝 0))
    (hD : Tendsto (fun n ↦ Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] / Var[X n; μ])
      atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ (X n ω - μ[X n]) / √Var[X n; μ]) atTop Z
      (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  set σ : ℕ → ℝ := fun n ↦ √Var[X n; μ] with hσ
  have hσ0 : ∀ n, 0 ≤ σ n := fun n ↦ Real.sqrt_nonneg _
  have hM0 : ∀ n, 0 ≤ M n := fun n ↦ (abs_nonneg _).trans (hUb n 0 (Classical.arbitrary Ω))
  have hU2 : ∀ n b, MemLp (U n b) 2 μ := fun n b ↦
    MemLp.of_bound (hUm n b).aestronglyMeasurable (M n)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hUb n b ω)
  have hUi : ∀ n b, Integrable (U n b) μ := fun n b ↦ (hU2 n b).integrable one_le_two
  have hEU : ∀ n b, |μ[U n b]| ≤ M n := fun n b ↦ by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := U n b) (C := M n)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hUb n b ω)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  -- the normalised centred blocks
  set ξ : ℕ → ℕ → Ω → ℝ := fun n b ω ↦ (U n b ω - μ[U n b]) / σ n with hξ
  have hξm : ∀ n b, Measurable (ξ n b) := fun n b ↦
    ((hUm n b).sub measurable_const).div_const _
  have hW2 : ∀ n, MemLp (fun ω ↦ ∑ b ∈ range (J n), U n b ω) 2 μ := fun n ↦
    memLp_finsetSum _ fun b _ ↦ hU2 n b
  -- `Σ_b Var (U n b) = Var (Σ_b U n b)`
  have hvarsum : ∀ n, ∑ b ∈ range (J n), Var[U n b; μ] =
      Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] := fun n ↦ by
    have h := IndepFun.variance_sum (μ := μ) (X := U n) (s := range (J n))
      (fun b _ ↦ hU2 n b) (fun b _ b' _ hbb' ↦ hpair n b b' hbb')
    rw [← h]
    congr 1
    funext ω
    simp only [Finset.sum_apply]
  -- the variance ratio of the block sum tends to one
  have hratio : Tendsto (fun n ↦ Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] / σ n ^ 2) atTop
      (𝓝 1) := by
    have hsq : Tendsto (fun n ↦ √(Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] /
        Var[X n; μ])) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hD
      rwa [Real.sqrt_zero] at this
    have hr : Tendsto (fun n ↦ √Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] / σ n) atTop
        (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hsq
      filter_upwards [hpos] with n hn
      have hσn : 0 < σ n := Real.sqrt_pos.2 hn
      have h := abs_sqrt_variance_sub_le (hX n) (hW2 n)
      rw [Real.norm_eq_abs, div_sub_one hσn.ne', abs_div, abs_of_pos hσn,
        Real.sqrt_div' _ hn.le]
      exact div_le_div_of_nonneg_right h hσn.le
    have := hr.pow 2
    rw [one_pow] at this
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    rw [div_pow, Real.sq_sqrt (variance_nonneg _ _)]
  have hLind : TendstoInDistribution (fun n ω ↦ ∑ b ∈ range (J n), ξ n b ω) atTop Z
      (fun _ ↦ μ) P' := by
    refine tendstoInDistribution_sum_range_of_bounded (P := fun _ ↦ μ) (L := J) (X := ξ)
      (fun n b ↦ (hξm n b).aemeasurable) (fun n b ↦ ?_) (fun n b ↦ ?_)
      (δ := fun n ↦ 2 * M n / σ n) ?_ (fun n b ↦ Eventually.of_forall fun ω ↦ ?_) (v := 1) ?_
      (by rwa [Real.toNNReal_one])
    · -- sequential independence is preserved by the affine normalisation
      have h := (hind n b).comp (φ := fun y ↦ (y - ∑ j ∈ range b, μ[U n j]) / σ n)
        (ψ := fun y ↦ (y - μ[U n b]) / σ n) (by fun_prop) (by fun_prop)
      refine h.congr ?_ (Eventually.of_forall fun ω ↦ rfl)
      refine Eventually.of_forall fun ω ↦ ?_
      simp only [Function.comp_apply, hξ, ← Finset.sum_div, Finset.sum_sub_distrib]
    · rw [hξ]
      simp only
      rw [integral_div, integral_sub (hUi n b) (integrable_const _), integral_const,
        probReal_univ, one_smul, sub_self, zero_div]
    · have := hM.const_mul 2
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      ring
    · rw [hξ]
      simp only
      rw [abs_div, abs_of_nonneg (hσ0 n)]
      refine div_le_div_of_nonneg_right ?_ (hσ0 n)
      calc |U n b ω - μ[U n b]| ≤ |U n b ω| + |μ[U n b]| := abs_sub _ _
        _ ≤ M n + M n := add_le_add (hUb n b ω) (hEU n b)
        _ = 2 * M n := by ring
    · refine hratio.congr' ?_
      filter_upwards [hpos] with n hn
      rw [← hvarsum, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [hξ]
      simp only
      rw [variance_eq_integral (hUm n b).aemeasurable, ← integral_div]
      congr 1
      funext ω
      rw [div_pow]
  -- the remainder tends to zero in measure
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hLind ?_
    (fun n ↦ (((hX n).aestronglyMeasurable.aemeasurable).sub aemeasurable_const).div_const _)
  have hDm : ∀ n, MemLp (fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω) 2 μ := fun n ↦
    (hX n).sub (hW2 n)
  set D : ℕ → Ω → ℝ := fun n ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω with hDdef
  have hED : ∀ n, μ[D n] = μ[X n] - ∑ b ∈ range (J n), μ[U n b] := fun n ↦ by
    rw [hDdef]
    simp only
    rw [integral_sub ((hX n).integrable one_le_two) (integrable_finsetSum _ fun b _ ↦ hUi n b),
      integral_finsetSum _ fun b _ ↦ hUi n b]
  have hpt : ∀ n, ((fun n ω ↦ (X n ω - μ[X n]) / √Var[X n; μ]) -
      fun n ω ↦ ∑ b ∈ range (J n), ξ n b ω) n = fun ω ↦ (D n ω - μ[D n]) * (σ n)⁻¹ := by
    intro n
    funext ω
    simp only [Pi.sub_apply, hξ, ← Finset.sum_div, Finset.sum_sub_distrib]
    rw [hED n]
    simp only [hDdef, hσ]
    ring
  refine tendstoInMeasure_of_integral_sq (fun n ↦ ?_) ?_
  · rw [hpt n]
    exact ((hDm n).sub (memLp_const _)).mul_const _
  · simp_rw [hpt]
    refine hD.congr' ?_
    filter_upwards [hpos] with n hn
    rw [variance_eq_integral (hDm n).aestronglyMeasurable.aemeasurable, div_eq_mul_inv,
      ← integral_mul_const]
    congr 1
    funext ω
    rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]

/-! ### Asymptotics of the block lengths -/

/-- `⌊log₂ k⌋ → ∞`. -/
theorem tendsto_natLog_atTop : Tendsto (fun k : ℕ ↦ (Nat.log 2 k : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp ?_
  refine tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun k hk ↦ Nat.le_log_of_pow_le one_lt_two hk⟩

/-- `(⌊log₂ k⌋ + 1)⁶ / k → 0`. -/
theorem tendsto_natLog_pow_six_div : Tendsto (fun k : ℕ ↦ ((Nat.log 2 k : ℝ) + 1) ^ 6 / k)
    atTop (𝓝 0) := by
  have hl : Tendsto (fun k : ℕ ↦ Real.log k ^ 6 / (1 * (k : ℝ) + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hc := hl.const_mul ((2 / Real.log 2) ^ 6)
  rw [mul_zero] at hc
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hc
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : 1 ≤ Nat.log 2 k := Nat.le_log_of_pow_le one_lt_two (by simpa using hk)
  have h2 : (Nat.log 2 k : ℝ) ≤ Real.log k / Real.log 2 := by
    have := Real.natLog_le_logb k 2
    rwa [Real.logb, Nat.cast_ofNat] at this
  have h3 : (Nat.log 2 k : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log k := by
    have : (1 : ℝ) ≤ Nat.log 2 k := by exact_mod_cast h1
    have : (Nat.log 2 k : ℝ) + 1 ≤ 2 * (Real.log k / Real.log 2) := by linarith
    calc (Nat.log 2 k : ℝ) + 1 ≤ 2 * (Real.log k / Real.log 2) := this
      _ = 2 / Real.log 2 * Real.log k := by ring
  have h0 : (0 : ℝ) ≤ (Nat.log 2 k : ℝ) + 1 := by positivity
  rw [one_mul, add_zero, mul_div_assoc', ← mul_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h3 6) hk0.le

/-- **Finite triangle inequality for the standard deviation.** -/
theorem sqrt_variance_sum_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {κ : Type*} (s : Finset κ) {X : κ → Ω → ℝ}
    (hX : ∀ k ∈ s, MemLp (X k) 2 μ) :
    √Var[fun ω ↦ ∑ k ∈ s, X k ω; μ] ≤ ∑ k ∈ s, √Var[X k; μ] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty]
      rw [show (fun _ : Ω ↦ (0 : ℝ)) = 0 from rfl, variance_zero, Real.sqrt_zero]
  | insert j s hj ih =>
      have hXs : ∀ k ∈ s, MemLp (X k) 2 μ := fun k hk ↦ hX k (mem_insert_of_mem hk)
      have e : (fun ω ↦ ∑ k ∈ insert j s, X k ω) = fun ω ↦ X j ω + ∑ k ∈ s, X k ω :=
        funext fun ω ↦ sum_insert hj
      rw [e, sum_insert hj]
      exact (sqrt_variance_add_le (hX j (mem_insert_self j s))
        (memLp_finsetSum s hXs)).trans (add_le_add le_rfl (ih hXs))

/-! ### The truncation CLT -/

/-- Finite sets of coordinates whose levels lie in disjoint ranges are disjoint. -/
theorem disjoint_of_lev {ι : Type*} (lev : ι → ℕ) {A A' : Finset ι} {a b : ℕ}
    (hA : ∀ i ∈ A, lev i < a) (hA' : ∀ i ∈ A', b ≤ lev i) (hab : a ≤ b) : Disjoint A A' :=
  Finset.disjoint_left.2 fun i hi hi' ↦ by
    have h1 := hA i hi
    have h2 := hA' i hi'
    omega

/-- The index window of `m` for blocks of length `p`: `p ⌊m/p⌋ ≤ m < p ⌊m/p⌋ + p`. -/
theorem div_mul_le_and_lt (m p : ℕ) (hp : 0 < p) : m / p * p ≤ m ∧ m < m / p * p + p :=
  ⟨Nat.div_mul_le_self m p, Nat.lt_div_mul_add hp⟩

variable {ι : Type*} [Countable α] [MeasurableSingletonClass α] [Nonempty α] in
/-- **CLT for sums of truncatable level terms of an independent sequence.** Coordinates `i : ι`
carry levels `lev i`; under the product measure `μ = ⊗ᵢ νᵢ` let `Y n m`, `m < K n`, be measurable
and bounded by `B`, and suppose each `Y n m` has, for every depth `L`, a truncation `Yt n m L`
bounded by `B` that depends only on finitely many coordinates of levels in `[m, m + L)`, with
`E[(Y n m − Yt n m L)²] ≤ C 2^{-L}`. If `K n → ∞` and `Var (Σ_{m<K n} Y n m) ≥ κ K n`
eventually (`κ > 0`), then the normalised sums converge in distribution to `N(0,1)`.

Proof: truncate at depth `L = 2(⌊log₂ K⌋ + 1)` (error `O(1)` in `L²`), cut the levels into
windows of length `p = L³`, keep in each window the terms whose truncation stays inside it
(independent bounded blocks of size `≤ p B = o(√K)`), and discard the last `L` levels of each
window (independent across windows, total variance `≤ (K/p + 1) L² B² = o(K)`); then
`tendstoInDistribution_of_blocks`. -/
theorem tendstoInDistribution_of_truncations (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (lev : ι → ℕ) {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    {Y : ℕ → ℕ → (ι → α) → ℝ} {Yt : ℕ → ℕ → ℕ → (ι → α) → ℝ} {B C κ : ℝ}
    (hYm : ∀ n m, Measurable (Y n m)) (hYb : ∀ n m ω, |Y n m ω| ≤ B)
    (hYtb : ∀ n m L ω, |Yt n m L ω| ≤ B)
    (hloc : ∀ n m L, ∃ S : Finset ι, (∀ i ∈ S, m ≤ lev i ∧ lev i < m + L) ∧
      IsLocal (Yt n m L) S)
    (htr : ∀ n m L,
      ∫ ω, (Y n m ω - Yt n m L ω) ^ 2 ∂(Measure.infinitePi ν) ≤ C * (1 / 2) ^ L)
    (hκ : 0 < κ)
    (hvar : ∀ᶠ n in atTop,
      κ * K n ≤ Var[fun ω ↦ ∑ m ∈ range (K n), Y n m ω; Measure.infinitePi ν])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ ((∑ m ∈ range (K n), Y n m ω) -
        (Measure.infinitePi ν)[fun ω ↦ ∑ m ∈ range (K n), Y n m ω]) /
        √Var[fun ω ↦ ∑ m ∈ range (K n), Y n m ω; Measure.infinitePi ν]) atTop Z
      (fun _ ↦ Measure.infinitePi ν) P' := by
  classical
  set μ := Measure.infinitePi ν with hμ
  choose S hSlev hSloc using hloc
  have hB : 0 ≤ B := (abs_nonneg _).trans (hYb 0 0 (fun _ ↦ Classical.arbitrary α))
  have hC : 0 ≤ C := by
    have h := htr 0 0 0
    rw [pow_zero, mul_one] at h
    exact (integral_nonneg fun ω ↦ sq_nonneg _).trans h
  -- block parameters
  set Lf : ℕ → ℕ := fun n ↦ 2 * (Nat.log 2 (K n) + 1) with hLf
  set pf : ℕ → ℕ := fun n ↦ Lf n ^ 3 with hpf
  set J : ℕ → ℕ := fun n ↦ K n / pf n + 1 with hJ
  have hL2 : ∀ n, 2 ≤ Lf n := fun n ↦ by simp only [hLf]; omega
  have hp : ∀ n, 0 < pf n := fun n ↦ pow_pos (by have := hL2 n; omega) 3
  have hLp : ∀ n, 2 * Lf n ≤ pf n := fun n ↦ by
    have h := hL2 n
    have e : pf n = Lf n * Lf n * Lf n := by simp only [hpf]; ring
    rw [e]
    have h1 : 2 * Lf n ≤ Lf n * Lf n := Nat.mul_le_mul_right _ h
    have h2 : Lf n * Lf n ≤ Lf n * Lf n * Lf n := Nat.le_mul_of_pos_right _ (by omega)
    omega
  set core : ℕ → ℕ → Prop := fun n m ↦ m % pf n + Lf n < pf n with hcore
  set X : ℕ → (ι → α) → ℝ := fun n ω ↦ ∑ m ∈ range (K n), Y n m ω with hX
  set FU : ℕ → ℕ → Finset ℕ := fun n b ↦
    ((range (K n)).filter (core n)).filter fun m ↦ m / pf n = b with hFU
  set FV : ℕ → ℕ → Finset ℕ := fun n b ↦
    ((range (K n)).filter fun m ↦ ¬ core n m).filter fun m ↦ m / pf n = b with hFV
  set U : ℕ → ℕ → (ι → α) → ℝ := fun n b ω ↦ ∑ m ∈ FU n b, Yt n m (Lf n) ω with hU
  set V : ℕ → ℕ → (ι → α) → ℝ := fun n b ω ↦ ∑ m ∈ FV n b, Yt n m (Lf n) ω with hV
  -- coordinate sets
  set SU : ℕ → ℕ → Finset ι := fun n b ↦ (FU n b).biUnion fun m ↦ S n m (Lf n) with hSU
  set SV : ℕ → ℕ → Finset ι := fun n b ↦ (FV n b).biUnion fun m ↦ S n m (Lf n) with hSV
  have hYtm : ∀ n m L, Measurable (Yt n m L) := fun n m L ↦ (hSloc n m L).measurable
  have hUloc : ∀ n b, IsLocal (U n b) (SU n b) := fun n b ↦
    isLocal_sum _ fun m hm ↦ (hSloc n m (Lf n)).mono
      (subset_biUnion_of_mem (fun m ↦ S n m (Lf n)) hm)
  have hVloc : ∀ n b, IsLocal (V n b) (SV n b) := fun n b ↦
    isLocal_sum _ fun m hm ↦ (hSloc n m (Lf n)).mono
      (subset_biUnion_of_mem (fun m ↦ S n m (Lf n)) hm)
  have hSUlev : ∀ n b, ∀ i ∈ SU n b, b * pf n ≤ lev i ∧ lev i < b * pf n + pf n := by
    intro n b i hi
    simp only [hSU, hFU, mem_biUnion, mem_filter, mem_range] at hi
    obtain ⟨m, ⟨⟨_, hcm⟩, hmb⟩, hiS⟩ := hi
    have h := hSlev n m (Lf n) i hiS
    have hw := Nat.div_add_mod' m (pf n)
    rw [hmb] at hw
    simp only [hcore] at hcm
    constructor
    · omega
    · omega
  have hSVlev : ∀ n b, ∀ i ∈ SV n b,
      b * pf n + pf n ≤ lev i + Lf n ∧ lev i < b * pf n + pf n + Lf n := by
    intro n b i hi
    simp only [hSV, hFV, mem_biUnion, mem_filter, mem_range] at hi
    obtain ⟨m, ⟨⟨_, hcm⟩, hmb⟩, hiS⟩ := hi
    have h := hSlev n m (Lf n) i hiS
    have hw := Nat.div_add_mod' m (pf n)
    have hlt := Nat.mod_lt m (hp n)
    rw [hmb] at hw
    simp only [hcore, not_lt] at hcm
    constructor
    · omega
    · omega
  -- cardinalities
  have hcardU : ∀ n b, (FU n b).card ≤ pf n := by
    intro n b
    refine (card_le_card (t := Finset.Ico (b * pf n) (b * pf n + pf n)) ?_).trans
      (by rw [Nat.card_Ico]; omega)
    intro m hm
    simp only [hFU, mem_filter] at hm
    have hw := div_mul_le_and_lt m (pf n) (hp n)
    rw [hm.2] at hw
    exact Finset.mem_Ico.2 hw
  have hcardV : ∀ n b, (FV n b).card ≤ Lf n := by
    intro n b
    refine (card_le_card (t := Finset.Ico (b * pf n + pf n - Lf n) (b * pf n + pf n)) ?_).trans
      (by rw [Nat.card_Ico]; have := hLp n; omega)
    intro m hm
    simp only [hFV, mem_filter, hcore, not_lt] at hm
    have hw := Nat.div_add_mod' m (pf n)
    have hlt := Nat.mod_lt m (hp n)
    rw [hm.2] at hw
    refine Finset.mem_Ico.2 ⟨?_, ?_⟩
    · have := hm.1.2
      omega
    · omega
  have hsum_le : ∀ (n : ℕ) (s : Finset ℕ) (ω : ι → α),
      |∑ m ∈ s, Yt n m (Lf n) ω| ≤ s.card * B := fun n s ω ↦ by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ s, |Yt n m (Lf n) ω| ≤ ∑ _m ∈ s, B := sum_le_sum fun m _ ↦ hYtb n m _ ω
      _ = s.card * B := by rw [sum_const, nsmul_eq_mul]
  have hUb : ∀ n b ω, |U n b ω| ≤ pf n * B := fun n b ω ↦
    (hsum_le n _ ω).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardU n b) hB)
  have hVb : ∀ n b ω, |V n b ω| ≤ Lf n * B := fun n b ω ↦
    (hsum_le n _ ω).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardV n b) hB)
  -- integrability
  have hYt2 : ∀ n m L, MemLp (Yt n m L) 2 μ := fun n m L ↦
    MemLp.of_bound (hYtm n m L).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYtb n m L ω)
  have hY2 : ∀ n m, MemLp (Y n m) 2 μ := fun n m ↦
    MemLp.of_bound (hYm n m).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYb n m ω)
  have hX2 : ∀ n, MemLp (X n) 2 μ := fun n ↦ memLp_finsetSum _ fun m _ ↦ hY2 n m
  have hUm : ∀ n b, Measurable (U n b) := fun n b ↦ (hUloc n b).measurable
  have hV2 : ∀ n b, MemLp (V n b) 2 μ := fun n b ↦ memLp_finsetSum _ fun m _ ↦ hYt2 n m _
  have hR2 : ∀ n m, MemLp (fun ω ↦ Y n m ω - Yt n m (Lf n) ω) 2 μ := fun n m ↦
    (hY2 n m).sub (hYt2 n m _)
  -- the decomposition `X = Σ_b U_b + Σ_b V_b + R`
  have hmaps : ∀ n, ∀ m ∈ range (K n), m / pf n ∈ range (J n) := fun n m hm ↦ by
    simp only [mem_range, hJ] at hm ⊢
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.le)
  have hdecomp : ∀ n ω, X n ω - ∑ b ∈ range (J n), U n b ω =
      ∑ b ∈ range (J n), V n b ω + ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω) := by
    intro n ω
    have h1 : ∑ b ∈ range (J n), U n b ω =
        ∑ m ∈ (range (K n)).filter (core n), Yt n m (Lf n) ω :=
      sum_fiberwise_of_maps_to (fun m hm ↦ hmaps n m (mem_filter.1 hm).1) _
    have h2 : ∑ b ∈ range (J n), V n b ω =
        ∑ m ∈ (range (K n)).filter (fun m ↦ ¬ core n m), Yt n m (Lf n) ω :=
      sum_fiberwise_of_maps_to (fun m hm ↦ hmaps n m (mem_filter.1 hm).1) _
    rw [h1, h2, sum_sub_distrib, hX]
    simp only
    rw [← sum_filter_add_sum_filter_not (range (K n)) (core n) (fun m ↦ Yt n m (Lf n) ω)]
    ring
  -- independence of the blocks
  have hind : ∀ n b, IndepFun (fun ω ↦ ∑ j ∈ range b, U n j ω) (U n b) μ := by
    intro n b
    refine IsLocal.indepFun ν (S := (range b).biUnion (SU n)) (T := SU n b)
      (isLocal_sum _ fun j hj ↦ (hUloc n j).mono (subset_biUnion_of_mem (SU n) hj))
      (hUloc n b) (disjoint_of_lev lev (a := b * pf n) (b := b * pf n) ?_ ?_ le_rfl)
    · intro i hi
      obtain ⟨j, hj, hij⟩ := mem_biUnion.1 hi
      have h := (hSUlev n j i hij).2
      have hjb : (j + 1) * pf n ≤ b * pf n := Nat.mul_le_mul_right _ (mem_range.1 hj)
      rw [add_mul, one_mul] at hjb
      omega
    · exact fun i hi ↦ (hSUlev n b i hi).1
  have hpairU : ∀ n b b', b < b' → IndepFun (U n b) (U n b') μ := by
    intro n b b' hbb'
    refine IsLocal.indepFun ν (hUloc n b) (hUloc n b')
      (disjoint_of_lev lev (a := b * pf n + pf n) (b := b' * pf n) (fun i hi ↦
        (hSUlev n b i hi).2) (fun i hi ↦ (hSUlev n b' i hi).1) ?_)
    have h : (b + 1) * pf n ≤ b' * pf n := Nat.mul_le_mul_right _ hbb'
    rw [add_mul, one_mul] at h
    exact h
  have hpairV : ∀ n b b', b < b' → IndepFun (V n b) (V n b') μ := by
    intro n b b' hbb'
    have h : (b + 1) * pf n ≤ b' * pf n := Nat.mul_le_mul_right _ hbb'
    rw [add_mul, one_mul] at h
    have hl := hLp n
    refine IsLocal.indepFun ν (hVloc n b) (hVloc n b')
      (disjoint_of_lev lev (a := b * pf n + pf n + Lf n) (b := b' * pf n + pf n - Lf n)
        (fun i hi ↦ (hSVlev n b i hi).2) (fun i hi ↦ ?_) (by omega))
    have := (hSVlev n b' i hi).1
    omega
  -- the variance of the discarded part
  have hVvar : ∀ n, Var[fun ω ↦ ∑ b ∈ range (J n), V n b ω; μ] ≤ J n * (Lf n * B) ^ 2 := by
    intro n
    have h := IndepFun.variance_sum (μ := μ) (X := V n) (s := range (J n))
      (fun b _ ↦ hV2 n b) (fun b _ b' _ hbb' ↦ by
        rcases lt_or_gt_of_ne hbb' with h | h
        · exact hpairV n b b' h
        · exact (hpairV n b' b h).symm)
    have e : (fun ω ↦ ∑ b ∈ range (J n), V n b ω) = ∑ b ∈ range (J n), V n b := by
      funext ω
      simp only [Finset.sum_apply]
    rw [e, h]
    calc ∑ b ∈ range (J n), Var[V n b; μ] ≤ ∑ _b ∈ range (J n), (Lf n * B) ^ 2 := by
          refine sum_le_sum fun b _ ↦ ?_
          have hb := variance_le_sq_of_bounded (μ := μ) (a := -(Lf n * B)) (b := Lf n * B)
            (Eventually.of_forall fun ω ↦ abs_le.1 (hVb n b ω))
            (hV2 n b).aestronglyMeasurable.aemeasurable
          refine hb.trans (le_of_eq ?_)
          ring
      _ = J n * (Lf n * B) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  have hRvar : ∀ n, √Var[fun ω ↦ ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω); μ] ≤ √C := by
    intro n
    refine (sqrt_variance_sum_le _ fun m _ ↦ hR2 n m).trans ?_
    have hterm : ∀ m, √Var[fun ω ↦ Y n m ω - Yt n m (Lf n) ω; μ] ≤
        √C * (1 / 2) ^ (Nat.log 2 (K n) + 1) := by
      intro m
      have h1 := variance_le_expectation_sq (μ := μ)
        (hR2 n m).aestronglyMeasurable
      have h2 := htr n m (Lf n)
      have e : (1 / 2 : ℝ) ^ Lf n = ((1 / 2) ^ (Nat.log 2 (K n) + 1)) ^ 2 := by
        rw [← pow_mul]
        simp only [hLf]
        ring_nf
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hC, ← e]
      refine h1.trans (le_of_eq_of_le ?_ h2)
      congr 1
    calc ∑ m ∈ range (K n), √Var[fun ω ↦ Y n m ω - Yt n m (Lf n) ω; μ]
        ≤ ∑ _m ∈ range (K n), √C * (1 / 2) ^ (Nat.log 2 (K n) + 1) := sum_le_sum fun m _ ↦ hterm m
      _ = √C * ((K n : ℝ) * (1 / 2) ^ (Nat.log 2 (K n) + 1)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
      _ ≤ √C * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have hk : (K n : ℝ) < 2 ^ (Nat.log 2 (K n) + 1) := by
            exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two (K n)
          rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
          exact hk.le
      _ = √C := mul_one _
  have hDvar : ∀ n, Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] ≤
      2 * (J n * (Lf n * B) ^ 2) + 2 * C := by
    intro n
    have e : (fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω) = fun ω ↦
        (∑ b ∈ range (J n), V n b ω) + ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω) :=
      funext (hdecomp n)
    rw [e]
    have h := sqrt_variance_add_le (μ := μ) (memLp_finsetSum (range (J n)) fun b _ ↦ hV2 n b)
      (memLp_finsetSum (range (K n)) fun m _ ↦ hR2 n m)
    have h1 := Real.sqrt_le_sqrt (hVvar n)
    have h2 := hRvar n
    have hs := Real.sq_sqrt (variance_nonneg (fun ω ↦ (∑ b ∈ range (J n), V n b ω) +
      ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω)) μ)
    have hJ0 : (0 : ℝ) ≤ J n * (Lf n * B) ^ 2 := by positivity
    have hs1 := Real.sq_sqrt hJ0
    have hs2 := Real.sq_sqrt hC
    have hn1 := Real.sqrt_nonneg (J n * (Lf n * B) ^ 2)
    have hn2 := Real.sqrt_nonneg C
    have hn3 := Real.sqrt_nonneg (Var[fun ω ↦ (∑ b ∈ range (J n), V n b ω) +
      ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω); μ])
    have hsle := h.trans (add_le_add h1 h2)
    rw [← hs, ← hs1, ← hs2]
    have hsq := pow_le_pow_left₀ hn3 hsle 2
    nlinarith [sq_nonneg (√(J n * (Lf n * B) ^ 2) - √C)]
  -- asymptotics
  have hKev : ∀ᶠ n in atTop, 1 ≤ K n := hK.eventually_ge_atTop 1
  have hpos : ∀ᶠ n in atTop, 0 < Var[X n; μ] := by
    filter_upwards [hvar, hKev] with n hn hk
    have : (1 : ℝ) ≤ K n := by exact_mod_cast hk
    exact lt_of_lt_of_le (by positivity) hn
  have hLR : ∀ n, (Lf n : ℝ) = 2 * ((Nat.log 2 (K n) : ℝ) + 1) := fun n ↦ by
    simp only [hLf]
    push_cast
    ring
  have hL1le : ∀ n, (1 : ℝ) ≤ Lf n := fun n ↦ by
    have := (Nat.log 2 (K n)).cast_nonneg (α := ℝ)
    rw [hLR]
    linarith
  have hL6 : Tendsto (fun n ↦ (Lf n : ℝ) ^ 6 / K n) atTop (𝓝 0) := by
    have h := (tendsto_natLog_pow_six_div.comp hK).const_mul 64
    rw [mul_zero] at h
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply, hLR]
    ring
  have hLtop : Tendsto (fun n ↦ (Lf n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_natLog_atTop.comp hK)
    rw [Function.comp_apply, hLR]
    have := (Nat.log 2 (K n)).cast_nonneg (α := ℝ)
    linarith
  have hL1 : Tendsto (fun n ↦ ((Lf n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hLtop
  have hK1 : Tendsto (fun n ↦ ((K n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hK)
  -- the blocks are small
  have hM : Tendsto (fun n ↦ ((pf n : ℕ) : ℝ) * B / √Var[X n; μ]) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp hL6).const_mul (B / √κ)
    rw [Real.sqrt_zero, mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ h
    filter_upwards [hvar, hKev] with n hn hk
    have hk0 : (0 : ℝ) < K n := by exact_mod_cast hk
    have hsq : √(κ * K n) ≤ √Var[X n; μ] := Real.sqrt_le_sqrt hn
    have hs0 : 0 < √(κ * K n) := Real.sqrt_pos.2 (by positivity)
    have hL0 : (0 : ℝ) ≤ Lf n := by linarith [hL1le n]
    calc ((pf n : ℕ) : ℝ) * B / √Var[X n; μ] ≤ ((pf n : ℕ) : ℝ) * B / √(κ * K n) :=
          div_le_div_of_nonneg_left (by positivity) hs0 hsq
      _ = B / √κ * √((Lf n : ℝ) ^ 6 / K n) := by
          rw [Real.sqrt_div' _ hk0.le, Real.sqrt_mul hκ.le,
            show (Lf n : ℝ) ^ 6 = ((Lf n : ℝ) ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
          simp only [hpf]
          push_cast
          field_simp
  -- the discarded part is negligible
  have hDlim : Tendsto (fun n ↦ (2 * B ^ 2 * (((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n) +
      2 * C * ((K n : ℝ))⁻¹) / κ) atTop (𝓝 0) := by
    have h := (((hL1.add hL6).const_mul (2 * B ^ 2)).add (hK1.const_mul (2 * C))).div_const κ
    rwa [add_zero, mul_zero, mul_zero, add_zero, zero_div] at h
  have hD : Tendsto (fun n ↦ Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] /
      Var[X n; μ]) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦
      div_nonneg (variance_nonneg _ _) (variance_nonneg _ _)) ?_ hDlim
    filter_upwards [hvar, hKev] with n hn hk
    have hk0 : (0 : ℝ) < K n := by exact_mod_cast hk
    have hL0 : (0 : ℝ) < Lf n := by linarith [hL1le n]
    have hJle : (J n : ℝ) ≤ K n / (Lf n : ℝ) ^ 3 + 1 := by
      have h := Nat.cast_div_le (m := K n) (n := pf n) (α := ℝ)
      simp only [hJ, hpf] at h ⊢
      push_cast at h ⊢
      linarith
    have hJL : (J n : ℝ) * (Lf n : ℝ) ^ 2 / K n ≤ ((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n := by
      have h1 : (J n : ℝ) * (Lf n : ℝ) ^ 2 / K n ≤
          (K n / (Lf n : ℝ) ^ 3 + 1) * (Lf n : ℝ) ^ 2 / K n := by gcongr
      have h2 : (K n / (Lf n : ℝ) ^ 3 + 1) * (Lf n : ℝ) ^ 2 / K n =
          ((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 2 / K n := by
        field_simp
      have h3 : (Lf n : ℝ) ^ 2 ≤ (Lf n : ℝ) ^ 6 := pow_le_pow_right₀ (hL1le n) (by norm_num)
      have h4 : (Lf n : ℝ) ^ 2 / K n ≤ (Lf n : ℝ) ^ 6 / K n :=
        div_le_div_of_nonneg_right h3 hk0.le
      linarith
    calc Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] / Var[X n; μ]
        ≤ (2 * (J n * (Lf n * B) ^ 2) + 2 * C) / (κ * K n) :=
          div_le_div₀ (by positivity) (hDvar n) (by positivity) hn
      _ = (2 * B ^ 2 * ((J n : ℝ) * (Lf n : ℝ) ^ 2 / K n) + 2 * C * ((K n : ℝ))⁻¹) / κ := by
          field_simp
      _ ≤ (2 * B ^ 2 * (((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n) + 2 * C * ((K n : ℝ))⁻¹) /
          κ := by gcongr
  exact tendstoInDistribution_of_blocks (M := fun n ↦ ((pf n : ℕ) : ℝ) * B) hX2 hUm hUb hind
    (fun n b b' hbb' ↦ by
      rcases lt_or_gt_of_ne hbb' with h | h
      · exact hpairU n b b' h
      · exact (hpairU n b' b h).symm) hpos hM hD hZ

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Path coins of a scrambled van der Corput stack (post #3, codes (ii) and (iii))

Post #3 drives a Markov chain by one scrambled Sobol (base-2 van der Corput) sequence per state,
randomised by a digital shift (code (ii)) or by Owen's nested scramble (code (iii)). For a
threshold `c ∈ [0,1)` (a cumulative transition probability) with binary digits `c_j`, the only
randomness that matters for the count `#{k < N : x_k ≤ c}` is carried by the **path coins**
`e_j = f j α_j`: the flips applied at the nodes `α_j` of the binary tree along the path of `c`
(`α_j` is the original `j`-digit prefix that the scramble sends to `c`'s first `j` digits).

## Main results

* `threshDigit c`: the binary digits of `c`; `digitPrefix_threshDigit` (`⌊2^m c⌋`),
  `binaryVal_threshDigit` (`= c`).
* `binaryVal_le_iff_of_firstDiff`, `binaryVal_le_iff_lexLeFrom`: comparing a binary expansion
  with `c` is lexicographic comparison of digits.
* `pathPrefix`, `pathCoin`; `tie_iff_mod_eq_pathPrefix`: the first `j` scrambled digits of point
  `k` equal `c`'s iff `k ≡ α_j (mod 2^j)`.
* `card_block_le_eq` (**per-block jump formula**, every flip table): in an aligned block of
  `2^m` indices, `#{x ≤ c} = ⌊2^m c⌋ + 1{x_{k*} ≤ c}` with `k* = a 2^m + α_m`.
* `LevelInd`, `scrambledVdc_levelPoint_le_iff`: the block term at level `m` is a fixed function
  of the path coins `e_m, e_{m+1}, …` and of the bits of `N` above `m` (tie cascades:
  `levelDigits N m e j = bit_j(levelBase N m) xor e_j`).
* `segErr_scrambledVdc_eq_sum_level` (**level decomposition**, every flip table):
  `#{k < N : x_k ≤ c} − N c = Σ_{m : bit m of N} (1{LevelInd} − {2^m c})` (`levelTerm`).
* `LexLeFromTrunc`, `LevelIndTrunc`, `levelValTrunc`, `LevelTie`,
  `levelVal_eq_trunc_of_not_tie`, `levelValTrunc_congr`: truncating every tie cascade at depth
  `L` changes the level term only on the tie event, and makes it a function of `e_m … e_{m+L-1}`.
* `levelInd_iff_binaryVal_le`: `LevelInd` holds iff the number formed by the level digits from
  depth `m` is `≤ {2^m c}` (so `P(LevelInd) = {2^m c}` under fair coins, `CltVariance`).
* `owenMeasure_pathCoins_cylinder`, `eq_shiftMeasure_of_cylinder` and `map_owenPathCoins`
  (**law equivalence**): the path coins of Owen-scrambled stacks are i.i.d. fair coins, i.e.
  have the law `shiftMeasure n` of the digital-shift flips (one threshold per state, any number
  of states); for the digital shift the path coins ARE the flips (`pathCoin_shiftTable`). Hence
  for chains with one jump per row (two states) the error of (ii) and (iii) is the same function
  of the same coin law, for every `T` (`CltVariance.IsPathCoinModel`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Digits of the threshold -/

/-- The binary digits of `c` (digit `j` is digit `j + 1` after the binary point). -/
noncomputable def threshDigit (c : ℝ) (j : ℕ) : Bool := decide (⌊2 ^ (j + 1) * c⌋₊ % 2 = 1)

/-- The first `m` digits of `c ∈ [0,1)` form `⌊2^m c⌋`. -/
theorem digitPrefix_threshDigit {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    digitPrefix (threshDigit c) m = ⌊2 ^ m * c⌋₊ := by
  induction m with
  | zero =>
      rw [pow_zero, one_mul, Nat.floor_eq_zero.2 hc1]
      rfl
  | succ m ih =>
      change 2 * digitPrefix (threshDigit c) m + (if threshDigit c m then 1 else 0) = _
      rw [ih]
      have hdiv : ⌊2 ^ m * c⌋₊ = ⌊2 ^ (m + 1) * c⌋₊ / 2 := by
        have e : (2 : ℝ) ^ m * c = 2 ^ (m + 1) * c / ((2 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [e, Nat.floor_div_natCast]
      rw [hdiv, threshDigit]
      have h := Nat.div_add_mod ⌊2 ^ (m + 1) * c⌋₊ 2
      rcases Nat.mod_two_eq_zero_or_one ⌊2 ^ (m + 1) * c⌋₊ with h2 | h2
      · simp only [h2, zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
        omega
      · simp only [h2, decide_true, ite_true]
        omega

/-- `⌊2^{m+1} c⌋ = 2⌊2^m c⌋ + c_m`. -/
theorem floor_two_pow_succ_mul {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    ⌊2 ^ (m + 1) * c⌋₊ = 2 * ⌊2 ^ m * c⌋₊ + if threshDigit c m then 1 else 0 := by
  rw [← digitPrefix_threshDigit hc1, ← digitPrefix_threshDigit hc1]
  rfl

/-- The binary expansion of the digits of `c ∈ [0,1)` is `c`. -/
theorem binaryVal_threshDigit {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    binaryVal (threshDigit c) = c := by
  have hb : ∀ m : ℕ, |binaryVal (threshDigit c) - c| ≤ 1 / 2 ^ m := by
    intro m
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have h1 := digitPrefix_div_le_binaryVal (threshDigit c) m
    have h2 := binaryVal_le_digitPrefix_add_one_div (threshDigit c) m
    rw [digitPrefix_threshDigit hc1] at h1 h2
    have h3 : (⌊2 ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
    have h4 : 2 ^ m * c < ⌊2 ^ m * c⌋₊ + 1 := Nat.lt_floor_add_one _
    have h3' : (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m ≤ c := by rw [div_le_iff₀ hp]; linarith
    have h4' : c < ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m := by rw [lt_div_iff₀ hp]; linarith
    rw [abs_le]
    constructor
    · have : ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m = (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m + 1 / 2 ^ m := by
        ring
      linarith
    · have : ((⌊2 ^ m * c⌋₊ : ℝ) + 1) / 2 ^ m = (⌊2 ^ m * c⌋₊ : ℝ) / 2 ^ m + 1 / 2 ^ m := by
        ring
      linarith
  by_contra hne
  have hpos : 0 < |binaryVal (threshDigit c) - c| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  have := hb m
  rw [one_div, ← inv_pow] at this
  rw [one_div] at hm
  linarith

/-- **First difference decides the comparison.** If the digits `d` agree with those of
`c ∈ [0,1)` before `τ` and differ at `τ`, then `binaryVal d ≤ c` iff `c`'s digit `τ` is `1`. -/
theorem binaryVal_le_iff_of_firstDiff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {d : ℕ → Bool}
    {τ : ℕ} (htie : ∀ i < τ, d i = threshDigit c i) (hne : d τ ≠ threshDigit c τ) :
    binaryVal d ≤ c ↔ threshDigit c τ = true := by
  have hp : (0 : ℝ) < 2 ^ (τ + 1) := by positivity
  set P := digitPrefix (threshDigit c) τ with hPdef
  have hP : digitPrefix d τ = P := digitPrefix_congr htie
  have hF : ⌊2 ^ (τ + 1) * c⌋₊ = 2 * P + if threshDigit c τ then 1 else 0 := by
    rw [floor_two_pow_succ_mul hc1, hPdef, digitPrefix_threshDigit hc1]
  have hdP : digitPrefix d (τ + 1) = 2 * P + if d τ then 1 else 0 := by
    rw [← hP]
    rfl
  have h3 : (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) ≤ 2 ^ (τ + 1) * c := Nat.floor_le (by positivity)
  have h4 : 2 ^ (τ + 1) * c < ⌊2 ^ (τ + 1) * c⌋₊ + 1 := Nat.lt_floor_add_one _
  cases hct : threshDigit c τ with
  | true =>
      have hdτ : d τ = false := by rw [hct] at hne; simpa using hne
      simp only [iff_true]
      have hu := binaryVal_le_digitPrefix_add_one_div d (τ + 1)
      rw [hdP, hdτ] at hu
      rw [hct] at hF
      simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at hu hF
      have e : ((2 * P : ℕ) : ℝ) + 1 = (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) := by
        rw [hF]
        push_cast
        ring
      rw [e] at hu
      refine hu.trans ?_
      rw [div_le_iff₀ hp]
      linarith
  | false =>
      have hdτ : d τ = true := by rw [hct] at hne; simpa using hne
      simp only [Bool.false_eq_true, iff_false, not_le]
      have hl := digitPrefix_div_le_binaryVal d (τ + 1)
      rw [hdP, hdτ] at hl
      rw [hct] at hF
      simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at hl hF
      have e : ((2 * P + 1 : ℕ) : ℝ) = (⌊2 ^ (τ + 1) * c⌋₊ : ℝ) + 1 := by
        rw [hF]
        push_cast
        ring
      rw [e] at hl
      refine lt_of_lt_of_le ?_ hl
      rw [lt_div_iff₀ hp]
      linarith

/-- **Lexicographic order from level `m`**: at the first disagreement (at or after `m`) of `d`
with the digits `cb`, the digit of `cb` is `1` (or there is no disagreement). -/
def LexLeFrom (d cb : ℕ → Bool) (m : ℕ) : Prop :=
  ∀ τ, m ≤ τ → (∀ i, m ≤ i → i < τ → d i = cb i) → d τ ≠ cb τ → cb τ = true

/-- **Comparison is lexicographic.** If `d` agrees with the digits of `c ∈ [0,1)` before `m`,
then `binaryVal d ≤ c` iff `d ≤ c` lexicographically from level `m`. -/
theorem binaryVal_le_iff_lexLeFrom {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {d : ℕ → Bool}
    {m : ℕ} (htie : ∀ i < m, d i = threshDigit c i) :
    binaryVal d ≤ c ↔ LexLeFrom d (threshDigit c) m := by
  classical
  by_cases h : ∃ τ, d τ ≠ threshDigit c τ
  · set τ := Nat.find h with hτ
    have hτne : d τ ≠ threshDigit c τ := Nat.find_spec h
    have hbelow : ∀ i < τ, d i = threshDigit c i := fun i hi ↦ by
      by_contra hc
      exact Nat.find_min h hi hc
    have hmτ : m ≤ τ := by
      by_contra hc
      exact hτne (htie τ (by omega))
    rw [binaryVal_le_iff_of_firstDiff hc0 hc1 hbelow hτne]
    constructor
    · intro hct τ' hmτ' htie' hne'
      have hττ' : τ ≤ τ' := Nat.find_min' h hne'
      rcases hττ'.lt_or_eq with hlt | heq
      · exact absurd (htie' τ hmτ hlt) hτne
      · rw [← heq]
        exact hct
    · intro hlex
      exact hlex τ hmτ (fun i _ hi ↦ hbelow i hi) hτne
  · push Not at h
    have hd : d = threshDigit c := funext h
    rw [hd, binaryVal_threshDigit hc0 hc1]
    exact ⟨fun _ τ _ _ hne ↦ absurd rfl hne, fun _ ↦ le_rfl⟩

/-- `LexLeFrom` only depends on the digits up to the first disagreement. -/
theorem lexLeFrom_congr {d d' cb : ℕ → Bool} {m : ℕ}
    (h : ∀ j, m ≤ j → (∀ i, m ≤ i → i < j → d i = cb i) → d j = d' j) :
    LexLeFrom d cb m ↔ LexLeFrom d' cb m := by
  have htie : ∀ j, (∀ i, m ≤ i → i < j → d i = cb i) ↔ (∀ i, m ≤ i → i < j → d' i = cb i) := by
    intro j
    induction j with
    | zero => exact ⟨fun _ i _ hi ↦ absurd hi (Nat.not_lt_zero _),
        fun _ i _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ j ih =>
        constructor
        · intro hd i hmi hij
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
          · exact (ih.1 fun i' hm' hi' ↦ hd i' hm' (by omega)) i hmi hlt
          · subst heq
            rw [← h i hmi fun i' hm' hi' ↦ hd i' hm' (by omega)]
            exact hd i hmi (by omega)
        · intro hd i hmi hij
          rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | heq
          · exact (ih.2 fun i' hm' hi' ↦ hd i' hm' (by omega)) i hmi hlt
          · subst heq
            have hprev : ∀ i', m ≤ i' → i' < i → d i' = cb i' :=
              ih.2 fun i' hm' hi' ↦ hd i' hm' (by omega)
            rw [h i hmi hprev]
            exact hd i hmi (by omega)
  constructor
  · intro hl τ hmτ ht hne
    have ht' := (htie τ).2 ht
    exact hl τ hmτ ht' (by rwa [h τ hmτ ht'])
  · intro hl τ hmτ ht hne
    exact hl τ hmτ ((htie τ).1 ht) (by rwa [← h τ hmτ ht])

/-! ### Path prefixes and path coins -/

/-- `k % 2^{j+1}` adds bit `j` of `k` to `k % 2^j`. -/
theorem mod_two_pow_succ_eq (k j : ℕ) :
    k % 2 ^ (j + 1) = k % 2 ^ j + 2 ^ j * (if k.testBit j then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ j) with h | h <;> simp [h]

/-- The **path prefix** `α_j`: the original `j`-digit prefix (as the residue `k % 2^j`) of the
indices whose first `j` scrambled digits are the digits `cb` of the threshold. -/
def pathPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0)

/-- The **path coin** `e_j = f j α_j`: the flip at depth `j` on the path of the threshold. -/
def pathCoin (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) : Bool := f j (pathPrefix f cb j)

/-- `α_j < 2^j`. -/
theorem pathPrefix_lt (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) : pathPrefix f cb j < 2 ^ j := by
  induction j with
  | zero => exact Nat.one_pos
  | succ j ih =>
      change pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0)
        < 2 ^ (j + 1)
      rw [pow_succ]
      split_ifs <;> omega

/-- **Ties along the path.** The first `j` scrambled digits of index `k` are the threshold's
digits iff `k ≡ α_j (mod 2^j)`. -/
theorem tie_iff_mod_eq_pathPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (k : ℕ) (j : ℕ) :
    (∀ i < j, scrambledDigit f k i = cb i) ↔ k % 2 ^ j = pathPrefix f cb j := by
  induction j with
  | zero => exact ⟨fun _ ↦ by rw [pow_zero, Nat.mod_one]; rfl, fun _ i hi ↦ absurd hi (by omega)⟩
  | succ j ih =>
      have hrec := mod_two_pow_succ_eq k j
      have hα := pathPrefix_lt f cb j
      have hsucc : pathPrefix f cb (j + 1) = pathPrefix f cb j +
          2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0) := rfl
      constructor
      · intro h
        have h1 := ih.1 fun i hi ↦ h i (by omega)
        have h2 := h j (by omega)
        rw [scrambledDigit, h1] at h2
        have h3 : k.testBit j = xor (cb j) (f j (pathPrefix f cb j)) := by
          rw [← h2]
          cases k.testBit j <;> cases f j (pathPrefix f cb j) <;> rfl
        rw [hrec, h1, h3, hsucc]
      · intro h
        have hmod : k % 2 ^ j = pathPrefix f cb j := by
          have e1 : k % 2 ^ (j + 1) % 2 ^ j = k % 2 ^ j :=
            Nat.mod_mod_of_dvd k (pow_dvd_pow 2 (Nat.le_succ j))
          rw [h, hsucc] at e1
          rw [← e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hα]
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
        · exact (ih.2 hmod) i hlt
        · subst heq
          rw [hrec, hmod, hsucc] at h
          have hb : (if k.testBit i then 1 else 0) =
              (if xor (cb i) (f i (pathPrefix f cb i)) then 1 else 0) := by
            have hp : 0 < 2 ^ i := Nat.two_pow_pos i
            have := Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h)
            exact this
          have hb' : k.testBit i = xor (cb i) (f i (pathPrefix f cb i)) := by
            revert hb
            cases k.testBit i <;> cases xor (cb i) (f i (pathPrefix f cb i)) <;> simp
          rw [scrambledDigit, hmod, hb']
          cases cb i <;> cases f i (pathPrefix f cb i) <;> rfl

/-- Points `a 2^m + α_m` lie on the path of the threshold to depth `m`. -/
theorem tie_of_mod {f : ℕ → ℕ → Bool} {cb : ℕ → Bool} {k m : ℕ}
    (hk : k % 2 ^ m = pathPrefix f cb m) : ∀ i < m, scrambledDigit f k i = cb i :=
  (tie_iff_mod_eq_pathPrefix f cb k m).2 hk

/-- `(2^m q + α) % 2^m = α` for `α < 2^m`. -/
theorem two_pow_mul_add_mod {m q α : ℕ} (hα : α < 2 ^ m) : (2 ^ m * q + α) % 2 ^ m = α := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hα]

/-- **Per-block jump formula** (every flip table). In the aligned block of indices
`a 2^m, …, a 2^m + 2^m − 1`, the number of points `≤ c` is `⌊2^m c⌋` plus the indicator of the
block's point `a 2^m + α_m` in the cell of `c`. -/
theorem card_block_le_eq (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (m : ℕ) :
    ∀ a : ℕ, ((range (2 ^ m)).filter fun r ↦ scrambledVdc f (a * 2 ^ m + r) ≤ c).card =
      ⌊2 ^ m * c⌋₊ +
        if scrambledVdc f (a * 2 ^ m + pathPrefix f (threshDigit c) m) ≤ c then 1 else 0 := by
  classical
  set cb := threshDigit c with hcb
  induction m with
  | zero =>
      intro a
      rw [show pathPrefix f cb 0 = 0 from rfl]
      simp only [pow_zero, one_mul, mul_one, Nat.floor_eq_zero.2 hc1, zero_add, range_one,
        filter_singleton, add_zero]
      split_ifs <;> rfl
  | succ m ih =>
      intro a
      set α := pathPrefix f cb m with hαdef
      have hα : α < 2 ^ m := pathPrefix_lt f cb m
      -- split the block into its two halves
      have hsplit : ((range (2 ^ (m + 1))).filter fun r ↦
            scrambledVdc f (a * 2 ^ (m + 1) + r) ≤ c).card =
            ((range (2 ^ m)).filter fun r ↦ scrambledVdc f ((2 * a) * 2 ^ m + r) ≤ c).card +
            ((range (2 ^ m)).filter fun r ↦ scrambledVdc f ((2 * a + 1) * 2 ^ m + r) ≤ c).card := by
        rw [card_filter, card_filter, card_filter, show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by ring,
          sum_range_add]
        congr 1
        · refine sum_congr rfl fun r _ ↦ ?_
          rw [show a * (2 ^ m + 2 ^ m) + r = 2 * a * 2 ^ m + r by ring]
        · refine sum_congr rfl fun r _ ↦ ?_
          rw [show a * (2 ^ m + 2 ^ m) + (2 ^ m + r) = (2 * a + 1) * 2 ^ m + r by ring]
      rw [hsplit, ih (2 * a), ih (2 * a + 1), floor_two_pow_succ_mul hc1, ← hcb]
      -- the two candidate points
      set k0 := 2 * a * 2 ^ m + α with hk0
      set k1 := (2 * a + 1) * 2 ^ m + α with hk1
      have hk0m : k0 % 2 ^ m = α := by
        rw [hk0, mul_comm (2 * a)]
        exact two_pow_mul_add_mod hα
      have hk1m : k1 % 2 ^ m = α := by
        rw [hk1, mul_comm (2 * a + 1)]
        exact two_pow_mul_add_mod hα
      have hb0 : k0.testBit m = false := by
        rw [hk0, mul_comm (2 * a), Nat.testBit_two_pow_mul_add _ hα]
        simp [Nat.testBit_zero]
      have hb1 : k1.testBit m = true := by
        rw [hk1, mul_comm (2 * a + 1), Nat.testBit_two_pow_mul_add _ hα]
        simp [Nat.testBit_zero]
      have hd0 : scrambledDigit f k0 m = f m α := by
        rw [scrambledDigit, hb0, hk0m, Bool.false_xor]
      have hd1 : scrambledDigit f k1 m = !f m α := by
        rw [scrambledDigit, hb1, hk1m, Bool.true_xor]
      have ht0 := tie_of_mod (f := f) (cb := cb) hk0m
      have ht1 := tie_of_mod (f := f) (cb := cb) hk1m
      have hsucc : pathPrefix f cb (m + 1) = α + 2 ^ m * (if xor (cb m) (f m α) then 1 else 0) :=
        rfl
      have hcb : ∀ k, (∀ i < m, scrambledDigit f k i = cb i) → scrambledDigit f k m ≠ cb m →
          (scrambledVdc f k ≤ c ↔ cb m = true) := fun k ht hne ↦
        binaryVal_le_iff_of_firstDiff hc0 hc1 ht hne
      cases hβ : xor (cb m) (f m α) with
      | false =>
          have hcm : cb m = f m α := by revert hβ; cases cb m <;> cases f m α <;> simp
          have hpt : a * 2 ^ (m + 1) + pathPrefix f cb (m + 1) = k0 := by
            rw [hsucc, hβ, hk0]
            simp only [Bool.false_eq_true, ite_false, mul_zero, add_zero]
            ring
          rw [hpt]
          have h1 := hcb k1 ht1 (by rw [hd1, hcm]; cases f m α <;> simp)
          by_cases hc : cb m = true
          · have hx : scrambledVdc f k1 ≤ c := h1.2 hc
            simp only [hx, hc, ite_true]
            omega
          · have hx : ¬ scrambledVdc f k1 ≤ c := fun h ↦ hc (h1.1 h)
            simp only [hx, hc, ite_false, Bool.false_eq_true]
            omega
      | true =>
          have hcm : cb m = !f m α := by revert hβ; cases cb m <;> cases f m α <;> simp
          have hpt : a * 2 ^ (m + 1) + pathPrefix f cb (m + 1) = k1 := by
            rw [hsucc, hβ, hk1]
            simp only [ite_true, mul_one]
            ring
          rw [hpt]
          have h0 := hcb k0 ht0 (by rw [hd0, hcm]; cases f m α <;> simp)
          by_cases hc : cb m = true
          · have hx : scrambledVdc f k0 ≤ c := h0.2 hc
            simp only [hx, hc, ite_true]
            omega
          · have hx : ¬ scrambledVdc f k0 ≤ c := fun h ↦ hc (h0.1 h)
            simp only [hx, hc, ite_false, Bool.false_eq_true]
            omega

/-! ### The level decomposition -/

/-- `N` with its bits `0, …, m` cleared: the start of the aligned block of bit `m` of `N`. -/
def levelBase (N m : ℕ) : ℕ := 2 ^ (m + 1) * (N / 2 ^ (m + 1))

/-- The digits of the level-`m` point beyond depth `m`, as long as it ties with the threshold:
the bits of `levelBase N m` flipped by the path coins `e`. -/
def levelDigits (N m : ℕ) (e : ℕ → Bool) (j : ℕ) : Bool := xor ((levelBase N m).testBit j) (e j)

/-- The level-`m` comparison as a function of the path coins: the block point of bit `m` of `N`
is `≤ c` iff its digits are lexicographically `≤` those of `c` from depth `m` on. -/
def LevelInd (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) : Prop := LexLeFrom (levelDigits N m e) cb m

open Classical in
/-- The indicator of `LevelInd`, as a real number. -/
noncomputable def levelVal (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if LevelInd cb N m e then 1 else 0

/-- The level term `1{LevelInd} − {2^m c}` of the local discrepancy. -/
noncomputable def levelTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  levelVal (threshDigit c) N m e - (2 ^ m * c - ⌊2 ^ m * c⌋₊)

/-- Bits at or above `m` of `levelBase N m + α`, `α < 2^m`, are those of `levelBase N m`. -/
theorem testBit_levelBase_add {N m α j : ℕ} (hα : α < 2 ^ m) (hj : m ≤ j) :
    (levelBase N m + α).testBit j = (levelBase N m).testBit j := by
  have e : levelBase N m = 2 ^ m * (2 * (N / 2 ^ (m + 1))) := by
    rw [levelBase, pow_succ]
    ring
  rw [e, Nat.testBit_two_pow_mul_add _ hα, ← add_zero (2 ^ m * (2 * (N / 2 ^ (m + 1)))),
    Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos m)]
  simp [Nat.not_lt.2 hj]

/-- `levelBase N m` is a multiple of `2^m`, so `(levelBase N m + α) % 2^m = α`. -/
theorem levelBase_add_mod {N m α : ℕ} (hα : α < 2 ^ m) : (levelBase N m + α) % 2 ^ m = α := by
  have e : levelBase N m = 2 ^ m * (2 * (N / 2 ^ (m + 1))) := by
    rw [levelBase, pow_succ]
    ring
  rw [e]
  exact two_pow_mul_add_mod hα

/-- **The level point and the path coins** (every flip table). The block point of bit `m` of `N`
is `≤ c` iff `LevelInd` holds for the path coins. -/
theorem scrambledVdc_levelPoint_le_iff (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (N m : ℕ) :
    scrambledVdc f (levelBase N m + pathPrefix f (threshDigit c) m) ≤ c ↔
      LevelInd (threshDigit c) N m (pathCoin f (threshDigit c)) := by
  set cb := threshDigit c with hcb
  set k := levelBase N m + pathPrefix f cb m with hk
  have hα := pathPrefix_lt f cb m
  have hkm : k % 2 ^ m = pathPrefix f cb m := levelBase_add_mod hα
  have htie := tie_of_mod (f := f) (cb := cb) hkm
  rw [scrambledVdc, binaryVal_le_iff_lexLeFrom hc0 hc1 htie]
  refine lexLeFrom_congr fun j hmj hj ↦ ?_
  have hall : ∀ i < j, scrambledDigit f k i = cb i := fun i hi ↦ by
    rcases lt_or_ge i m with h | h
    · exact htie i h
    · exact hj i h hi
  have hkj := (tie_iff_mod_eq_pathPrefix f cb k j).1 hall
  rw [scrambledDigit, hkj, levelDigits, hk, testBit_levelBase_add hα hmj]
  rfl

/-- `levelBase (2^M + N') m = 2^M + levelBase N' m` for `m < M`. -/
theorem levelBase_two_pow_add {M N' m : ℕ} (hm : m < M) :
    levelBase (2 ^ M + N') m = 2 ^ M + levelBase N' m := by
  have hM : 2 ^ M = 2 ^ (m + 1) * 2 ^ (M - (m + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  unfold levelBase
  rw [hM, Nat.mul_add_div (Nat.two_pow_pos _)]
  ring

/-- `levelBase N M = 0` for `N < 2^{M+1}`. -/
theorem levelBase_eq_zero {N M : ℕ} (hN : N < 2 ^ (M + 1)) : levelBase N M = 0 := by
  rw [levelBase, Nat.div_eq_of_lt hN, mul_zero]

/-- The level decomposition with a base point `B ≡ 0 (mod 2^M)`. -/
theorem segErr_eq_sum_levelPoint (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (M : ℕ) : ∀ B N : ℕ, 2 ^ M ∣ B → N < 2 ^ M →
      segErr (scrambledVdc f) c B N = ∑ m ∈ (range M).filter (fun m ↦ N.testBit m),
        ((if scrambledVdc f (B + levelBase N m + pathPrefix f (threshDigit c) m) ≤ c then 1 else 0)
          - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) := by
  classical
  induction M with
  | zero =>
      intro B N _ hN
      have : N = 0 := by rw [pow_zero] at hN; omega
      subst this
      rw [segErr_zero, range_zero, filter_empty, sum_empty]
  | succ M ih =>
      intro B N hB hN
      have hB' : 2 ^ M ∣ B := dvd_trans (pow_dvd_pow 2 (Nat.le_succ M)) hB
      by_cases hbit : N.testBit M
      · have hge : 2 ^ M ≤ N := by
          by_contra h
          push Not at h
          rw [Nat.testBit_lt_two_pow h] at hbit
          exact absurd hbit (by simp)
        obtain ⟨N', rfl⟩ : ∃ N', N = 2 ^ M + N' := ⟨N - 2 ^ M, by omega⟩
        have hN' : N' < 2 ^ M := by rw [pow_succ] at hN; omega
        rw [segErr_add, ih (B + 2 ^ M) N' (dvd_add hB' dvd_rfl) hN', range_add_one,
          filter_insert]
        simp only [hbit, ite_true]
        rw [sum_insert (by simp)]
        -- the block of the top bit
        have hblk := card_block_le_eq f hc0 hc1 M (B / 2 ^ M)
        rw [Nat.div_mul_cancel hB'] at hblk
        rw [segErr_eq_card, hblk, levelBase_eq_zero hN, add_zero]
        have hfilt : (range M).filter (fun m ↦ (2 ^ M + N').testBit m) =
            (range M).filter (fun m ↦ N'.testBit m) :=
          filter_congr fun m hm ↦ by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hm)]
        rw [hfilt]
        have hsum : ∑ m ∈ (range M).filter (fun m ↦ N'.testBit m),
            ((if scrambledVdc f (B + levelBase (2 ^ M + N') m + pathPrefix f (threshDigit c) m)
              ≤ c then (1 : ℝ) else 0) - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) =
            ∑ m ∈ (range M).filter (fun m ↦ N'.testBit m),
            ((if scrambledVdc f (B + 2 ^ M + levelBase N' m + pathPrefix f (threshDigit c) m)
              ≤ c then (1 : ℝ) else 0) - (2 ^ m * c - ⌊2 ^ m * c⌋₊)) :=
          sum_congr rfl fun m hm ↦ by
            rw [levelBase_two_pow_add (mem_range.1 (mem_filter.1 hm).1), ← add_assoc]
        rw [hsum]
        push_cast
        ring
      · have hlt : N < 2 ^ M := by
          by_contra h
          push Not at h
          obtain ⟨N', rfl⟩ : ∃ N', N = 2 ^ M + N' := ⟨N - 2 ^ M, by omega⟩
          have hN' : N' < 2 ^ M := by rw [pow_succ] at hN; omega
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hN'] at hbit
          exact hbit rfl
        rw [ih B N hB' hlt, range_add_one, filter_insert]
        simp only [hbit, Bool.false_eq_true, ite_false]

/-- **Level decomposition of the local discrepancy** (every flip table). For `N < 2^M`,
`#{k < N : x_k ≤ c} − N c = Σ_{m < M, bit m of N} levelTerm c N m e`, where `e` are the path
coins of the flip table. -/
theorem segErr_scrambledVdc_eq_sum_level (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) {N M : ℕ} (hN : N < 2 ^ M) :
    segErr (scrambledVdc f) c 0 N = ∑ m ∈ (range M).filter (fun m ↦ N.testBit m),
      levelTerm c N m (pathCoin f (threshDigit c)) := by
  rw [segErr_eq_sum_levelPoint f hc0 hc1 M 0 N (dvd_zero _) hN]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [levelTerm, levelVal, zero_add]
  congr 1
  have hiff := scrambledVdc_levelPoint_le_iff f hc0 hc1 N m
  by_cases h : LevelInd (threshDigit c) N m (pathCoin f (threshDigit c))
  · simp only [h, hiff.2 h, ite_true]
  · have h' : ¬ scrambledVdc f (levelBase N m + pathPrefix f (threshDigit c) m) ≤ c :=
      fun h'' ↦ h (hiff.1 h'')
    simp only [h, h', ite_false]

/-! ### Truncated tie cascades -/

/-- `LexLeFrom` truncated at depth `L`: only disagreements in `[m, m + L)` count (no
disagreement there counts as `≤`). -/
def LexLeFromTrunc (d cb : ℕ → Bool) (m L : ℕ) : Prop :=
  ∀ τ, m ≤ τ → τ < m + L → (∀ i, m ≤ i → i < τ → d i = cb i) → d τ ≠ cb τ → cb τ = true

/-- At the first disagreement `τ₀ ≥ m`, `LexLeFrom` is decided by `cb τ₀`. -/
theorem lexLeFrom_iff_of_firstBreak {d cb : ℕ → Bool} {m τ₀ : ℕ} (hm : m ≤ τ₀)
    (ht : ∀ i, m ≤ i → i < τ₀ → d i = cb i) (hb : d τ₀ ≠ cb τ₀) :
    LexLeFrom d cb m ↔ cb τ₀ = true := by
  constructor
  · intro h
    exact h τ₀ hm ht hb
  · intro h τ hmτ htτ hbτ
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · exact absurd (ht τ hmτ hlt) hbτ
    · rwa [heq]
    · exact absurd (htτ τ₀ hm hgt) hb

/-- At the first disagreement `τ₀ ∈ [m, m + L)`, the truncation is decided by `cb τ₀`. -/
theorem lexLeFromTrunc_iff_of_firstBreak {d cb : ℕ → Bool} {m τ₀ L : ℕ} (hm : m ≤ τ₀)
    (hL : τ₀ < m + L) (ht : ∀ i, m ≤ i → i < τ₀ → d i = cb i) (hb : d τ₀ ≠ cb τ₀) :
    LexLeFromTrunc d cb m L ↔ cb τ₀ = true := by
  constructor
  · intro h
    exact h τ₀ hm hL ht hb
  · intro h τ hmτ _ htτ hbτ
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · exact absurd (ht τ hmτ hlt) hbτ
    · rwa [heq]
    · exact absurd (htτ τ₀ hm hgt) hb

/-- A disagreement in `[m, m + L)` has a first one. -/
theorem exists_firstBreak {d cb : ℕ → Bool} {m L : ℕ}
    (h : ¬ ∀ j, m ≤ j → j < m + L → d j = cb j) :
    ∃ τ₀, m ≤ τ₀ ∧ τ₀ < m + L ∧ (∀ i, m ≤ i → i < τ₀ → d i = cb i) ∧ d τ₀ ≠ cb τ₀ := by
  classical
  have hex : ∃ τ, m ≤ τ ∧ τ < m + L ∧ d τ ≠ cb τ := by
    by_contra hc
    push Not at hc
    exact h fun j hm hj ↦ hc j hm hj
  have hex' : ∃ τ, m ≤ τ ∧ d τ ≠ cb τ := let ⟨τ, h1, _, h3⟩ := hex; ⟨τ, h1, h3⟩
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, ?_, fun i hmi hi ↦ ?_, (Nat.find_spec hex').2⟩
  · obtain ⟨τ, h1, h2, h3⟩ := hex
    exact lt_of_le_of_lt (Nat.find_min' hex' ⟨h1, h3⟩) h2
  · by_contra hc
    exact Nat.find_min hex' hi ⟨hmi, hc⟩

/-- **Truncation is exact off the tie event**: if `d` disagrees with `cb` somewhere in
`[m, m + L)`, then `LexLeFrom` and its depth-`L'` truncation agree for every `L' ≥ L`. -/
theorem lexLeFrom_iff_trunc {d cb : ℕ → Bool} {m L L' : ℕ} (hLL : L ≤ L')
    (h : ¬ ∀ j, m ≤ j → j < m + L → d j = cb j) :
    (LexLeFrom d cb m ↔ LexLeFromTrunc d cb m L') ∧
      (LexLeFromTrunc d cb m L ↔ LexLeFromTrunc d cb m L') := by
  obtain ⟨τ₀, hm, hL, ht, hb⟩ := exists_firstBreak h
  rw [lexLeFrom_iff_of_firstBreak hm ht hb, lexLeFromTrunc_iff_of_firstBreak hm (by omega) ht hb,
    lexLeFromTrunc_iff_of_firstBreak hm hL ht hb]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The level comparison truncated at depth `L`. -/
def LevelIndTrunc (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : Prop :=
  LexLeFromTrunc (levelDigits N m e) cb m L

open Classical in
/-- The indicator of `LevelIndTrunc`. -/
noncomputable def levelValTrunc (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if LevelIndTrunc cb N m L e then 1 else 0

/-- The level tie event: the level-`m` point ties with the threshold on `[m, m + L)`. -/
def LevelTie (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) : Prop :=
  ∀ j, m ≤ j → j < m + L → levelDigits N m e j = cb j

/-- Off the tie event the truncated and full indicators agree. -/
theorem levelVal_eq_trunc_of_not_tie {cb : ℕ → Bool} {N m L L' : ℕ} {e : ℕ → Bool}
    (hLL : L ≤ L') (h : ¬ LevelTie cb N m L e) :
    levelVal cb N m e = levelValTrunc cb N m L' e ∧
      levelValTrunc cb N m L e = levelValTrunc cb N m L' e := by
  have hh := lexLeFrom_iff_trunc hLL h
  constructor
  · unfold levelVal levelValTrunc LevelInd LevelIndTrunc
    by_cases h1 : LexLeFromTrunc (levelDigits N m e) cb m L'
    · simp only [h1, hh.1.2 h1, ite_true]
    · have h2 : ¬ LexLeFrom (levelDigits N m e) cb m := fun h' ↦ h1 (hh.1.1 h')
      simp only [h1, h2, ite_false]
  · unfold levelValTrunc LevelIndTrunc
    by_cases h1 : LexLeFromTrunc (levelDigits N m e) cb m L'
    · simp only [h1, hh.2.2 h1, ite_true]
    · have h2 : ¬ LexLeFromTrunc (levelDigits N m e) cb m L := fun h' ↦ h1 (hh.2.1 h')
      simp only [h1, h2, ite_false]

/-- The truncated indicator depends only on the coins in `[m, m + L)`. -/
theorem levelValTrunc_congr (cb : ℕ → Bool) (N m L : ℕ) {e e' : ℕ → Bool}
    (h : ∀ j, m ≤ j → j < m + L → e j = e' j) :
    levelValTrunc cb N m L e = levelValTrunc cb N m L e' := by
  have hd : ∀ j, m ≤ j → j < m + L → levelDigits N m e j = levelDigits N m e' j :=
    fun j hm hj ↦ by rw [levelDigits, levelDigits, h j hm hj]
  have hiff : LevelIndTrunc cb N m L e ↔ LevelIndTrunc cb N m L e' := by
    unfold LevelIndTrunc LexLeFromTrunc
    constructor
    · intro h' τ hm hL ht hb
      refine h' τ hm hL (fun i hmi hi ↦ ?_) (by rwa [hd τ hm hL])
      rw [hd i hmi (by omega)]
      exact ht i hmi hi
    · intro h' τ hm hL ht hb
      refine h' τ hm hL (fun i hmi hi ↦ ?_) (by rwa [← hd τ hm hL])
      rw [← hd i hmi (by omega)]
      exact ht i hmi hi
  unfold levelValTrunc
  by_cases h1 : LevelIndTrunc cb N m L e
  · simp only [h1, hiff.1 h1, ite_true]
  · have h2 : ¬ LevelIndTrunc cb N m L e' := fun h' ↦ h1 (hiff.2 h')
    simp only [h1, h2, ite_false]

/-- The level indicator through the value of the shifted digits: `LevelInd` holds iff the
binary number formed by the level digits from depth `m` on is `≤ {2^m c}`. -/
theorem levelInd_iff_binaryVal_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (e : ℕ → Bool) :
    LevelInd (threshDigit c) N m e ↔
      binaryVal (fun j ↦ levelDigits N m e (j + m)) ≤ 2 ^ m * c - ⌊2 ^ m * c⌋₊ := by
  classical
  set d : ℕ → Bool := fun j ↦ if j < m then threshDigit c j else levelDigits N m e j with hd
  have htie : ∀ i < m, d i = threshDigit c i := fun i hi ↦ by simp [hd, hi]
  have h1 := binaryVal_le_iff_lexLeFrom hc0 hc1 htie
  have h2 : LexLeFrom d (threshDigit c) m ↔ LevelInd (threshDigit c) N m e :=
    lexLeFrom_congr fun j hj _ ↦ by simp [hd, Nat.not_lt.2 hj]
  have h3 := binaryVal_eq_digitPrefix_add d m
  have h4 : digitPrefix d m = ⌊2 ^ m * c⌋₊ := by
    rw [digitPrefix_congr htie, digitPrefix_threshDigit hc1]
  have h5 : (fun j ↦ d (j + m)) = fun j ↦ levelDigits N m e (j + m) := by
    funext j
    simp [hd]
  rw [h4, h5] at h3
  rw [← h2, ← h1, h3, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-! ### The law of the path coins -/

/-- The path prefix recomputed from the path coins. -/
def coinPrefix (cb e : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => coinPrefix cb e j + 2 ^ j * (if xor (cb j) (e j) then 1 else 0)

/-- The path prefix is determined by the earlier path coins. -/
theorem pathPrefix_eq_coinPrefix (f : ℕ → ℕ → Bool) (cb : ℕ → Bool) (j : ℕ) :
    pathPrefix f cb j = coinPrefix cb (pathCoin f cb) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change pathPrefix f cb j + 2 ^ j * (if xor (cb j) (f j (pathPrefix f cb j)) then 1 else 0) =
        coinPrefix cb (pathCoin f cb) j + 2 ^ j * (if xor (cb j) (pathCoin f cb j) then 1 else 0)
      rw [← ih]
      rfl

/-- `coinPrefix cb e j` depends only on `e` below `j`. -/
theorem coinPrefix_congr (cb : ℕ → Bool) {e e' : ℕ → Bool} {j : ℕ} (h : ∀ i < j, e i = e' i) :
    coinPrefix cb e j = coinPrefix cb e' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change coinPrefix cb e j + 2 ^ j * (if xor (cb j) (e j) then 1 else 0) =
        coinPrefix cb e' j + 2 ^ j * (if xor (cb j) (e' j) then 1 else 0)
      rw [ih fun i hi ↦ h i (by omega), h j (by omega)]

/-- **Digital shift: the path coins are the flips.** -/
theorem pathCoin_shiftTable (e cb : ℕ → Bool) : pathCoin (shiftTable e) cb = e := rfl

variable {n : ℕ}

/-- The path coins of Owen-scrambled stacks, state `i` with threshold digits `cb i`. -/
def owenPathCoins (cb : Fin n → ℕ → Bool) (ω : Fin n × ℕ × ℕ → Bool) : Fin n × ℕ → Bool :=
  fun p ↦ pathCoin (owenTable ω p.1) (cb p.1) p.2

/-- The Owen coordinates of depth `< M` and prefix `< 2^M`. -/
def owenBox (n M : ℕ) : Finset (Fin n × ℕ × ℕ) := univ ×ˢ (range M ×ˢ range (2 ^ M))

/-- Path prefixes to depth `M` only use coordinates in `owenBox n M`. -/
theorem pathPrefix_owen_congr (cb : ℕ → Bool) (i : Fin n) {M : ℕ} {ω ω' : Fin n × ℕ × ℕ → Bool}
    (h : ∀ q ∈ owenBox n M, ω q = ω' q) :
    ∀ j ≤ M, pathPrefix (owenTable ω i) cb j = pathPrefix (owenTable ω' i) cb j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj' := ih (by omega)
      change pathPrefix (owenTable ω i) cb j +
          2 ^ j * (if xor (cb j) (ω (i, j, pathPrefix (owenTable ω i) cb j)) then 1 else 0) =
        pathPrefix (owenTable ω' i) cb j +
          2 ^ j * (if xor (cb j) (ω' (i, j, pathPrefix (owenTable ω' i) cb j)) then 1 else 0)
      rw [← hj', h (i, j, pathPrefix (owenTable ω i) cb j)]
      simp only [owenBox, mem_product, mem_univ, mem_range, true_and]
      refine ⟨by omega, lt_of_lt_of_le (pathPrefix_lt _ cb j) ?_⟩
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Path coins of depth `< M` only use coordinates in `owenBox n M`. -/
theorem owenPathCoins_congr (cb : Fin n → ℕ → Bool) {M : ℕ} {ω ω' : Fin n × ℕ × ℕ → Bool}
    (h : ∀ q ∈ owenBox n M, ω q = ω' q) (i : Fin n) {j : ℕ} (hj : j < M) :
    owenPathCoins cb ω (i, j) = owenPathCoins cb ω' (i, j) := by
  change ω (i, j, pathPrefix (owenTable ω i) (cb i) j) =
    ω' (i, j, pathPrefix (owenTable ω' i) (cb i) j)
  rw [pathPrefix_owen_congr (cb i) i h j hj.le, h]
  simp only [owenBox, mem_product, mem_univ, mem_range, true_and]
  exact ⟨hj, lt_of_lt_of_le (pathPrefix_lt _ _ j) (Nat.pow_le_pow_right (by norm_num) hj.le)⟩

/-- The Owen path coins are measurable. -/
theorem measurable_owenPathCoins (cb : Fin n → ℕ → Bool) : Measurable (owenPathCoins cb) := by
  refine measurable_pi_iff.2 fun p ↦ ?_
  have hloc : IsLocal (fun ω ↦ owenPathCoins cb ω p) (owenBox n (p.2 + 1)) :=
    fun ω ω' h ↦ owenPathCoins_congr cb h p.1 (Nat.lt_succ_self p.2)
  exact hloc.measurable

/-- Sets depending on disjoint finite sets of coordinates are independent under a product of
probability measures. -/
theorem infinitePi_inter_of_local {ι α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] [Nonempty α] (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    {A B : Set (ι → α)} {S T : Finset ι}
    (hA : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω', (∀ i ∈ T, ω i = ω' i) → (ω ∈ B ↔ ω' ∈ B)) (hST : Disjoint S T) :
    Measure.infinitePi ν (A ∩ B) = Measure.infinitePi ν A * Measure.infinitePi ν B := by
  classical
  have hF : IsLocal (fun ω ↦ decide (ω ∈ A)) S := fun ω ω' h ↦ by
    simp only [decide_eq_decide]
    exact hA ω ω' h
  have hG : IsLocal (fun ω ↦ decide (ω ∈ B)) T := fun ω ω' h ↦ by
    simp only [decide_eq_decide]
    exact hB ω ω' h
  have hind := IsLocal.indepFun ν hF hG hST
  have h := hind.measure_inter_preimage_eq_mul {true} {true} (measurableSet_singleton _)
    (measurableSet_singleton _)
  have eA : (fun ω ↦ decide (ω ∈ A)) ⁻¹' {true} = A := by ext ω; simp
  have eB : (fun ω ↦ decide (ω ∈ B)) ⁻¹' {true} = B := by ext ω; simp
  rwa [eA, eB] at h

/-- **Owen path coins: cylinder probabilities.** The first `M` path coins of every state take
any prescribed values with probability `2^{-nM}`. -/
theorem owenMeasure_pathCoins_cylinder (cb : Fin n → ℕ → Bool) (b : Fin n × ℕ → Bool) (M : ℕ) :
    owenMeasure n {ω | ∀ i, ∀ j < M, owenPathCoins cb ω (i, j) = b (i, j)} = 2⁻¹ ^ (n * M) := by
  classical
  induction M with
  | zero =>
      have : {ω : Fin n × ℕ × ℕ → Bool | ∀ i, ∀ j < 0, owenPathCoins cb ω (i, j) = b (i, j)} =
          Set.univ := by
        ext ω
        simp
      rw [this, measure_univ, mul_zero, pow_zero]
  | succ M ih =>
      set a : Fin n → ℕ := fun i ↦ coinPrefix (cb i) (fun j ↦ b (i, j)) M with ha
      set E := {ω : Fin n × ℕ × ℕ → Bool | ∀ i, ∀ j < M, owenPathCoins cb ω (i, j) = b (i, j)}
        with hE
      set T : Finset (Fin n × ℕ × ℕ) := univ.image fun i ↦ (i, M, a i) with hT
      set F := Set.pi (T : Set (Fin n × ℕ × ℕ)) fun q ↦ ({b (q.1, M)} : Set Bool) with hF
      have hsplit : {ω : Fin n × ℕ × ℕ → Bool |
          ∀ i, ∀ j < M + 1, owenPathCoins cb ω (i, j) = b (i, j)} = E ∩ F := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE, hF, Set.mem_pi, hT, coe_image,
          coe_univ, Set.image_univ, Set.mem_range, forall_exists_index, Set.mem_singleton_iff]
        constructor
        · intro h
          refine ⟨fun i j hj ↦ h i j (by omega), ?_⟩
          rintro q i rfl
          have hpre : pathPrefix (owenTable ω i) (cb i) M = a i := by
            rw [pathPrefix_eq_coinPrefix, ha]
            exact coinPrefix_congr (cb i) fun j hj ↦ h i j (by omega)
          have := h i M (by omega)
          change ω (i, M, pathPrefix (owenTable ω i) (cb i) M) = b (i, M) at this
          rw [hpre] at this
          exact this
        · rintro ⟨hE', hF'⟩ i j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
          · exact hE' i j hlt
          · have hpre : pathPrefix (owenTable ω i) (cb i) j = a i := by
              rw [pathPrefix_eq_coinPrefix, ha]
              exact coinPrefix_congr (cb i) fun j' hj' ↦ hE' i j' hj'
            change ω (i, j, pathPrefix (owenTable ω i) (cb i) j) = b (i, j)
            rw [hpre]
            exact hF' _ i rfl
      have hEloc : ∀ ω ω', (∀ q ∈ owenBox n M, ω q = ω' q) → (ω ∈ E ↔ ω' ∈ E) := by
        intro ω ω' h
        simp only [hE, Set.mem_ofPred_eq]
        constructor
        · intro h' i j hj
          rw [← owenPathCoins_congr cb h i hj]
          exact h' i j hj
        · intro h' i j hj
          rw [owenPathCoins_congr cb h i hj]
          exact h' i j hj
      have hFloc : ∀ ω ω', (∀ q ∈ T, ω q = ω' q) → (ω ∈ F ↔ ω' ∈ F) := by
        intro ω ω' h
        simp only [hF, Set.mem_pi]
        constructor
        · intro h' q hq
          rw [← h q hq]
          exact h' q hq
        · intro h' q hq
          rw [h q hq]
          exact h' q hq
      have hdisj : Disjoint (owenBox n M) T := by
        refine Finset.disjoint_left.2 fun q hq hqT ↦ ?_
        simp only [owenBox, mem_product, mem_univ, mem_range, true_and] at hq
        obtain ⟨i, _, rfl⟩ := mem_image.1 hqT
        exact absurd hq.1 (lt_irrefl M)
      have hFm : owenMeasure n F = 2⁻¹ ^ n := by
        rw [hF, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
        simp only [fairCoin_singleton, prod_const]
        rw [hT, card_image_of_injective _ fun i i' h ↦ by simpa using congrArg Prod.fst h,
          card_univ, Fintype.card_fin]
      have hmul := infinitePi_inter_of_local (fun _ : Fin n × ℕ × ℕ ↦ fairCoin) hEloc hFloc hdisj
      change owenMeasure n _ = _
      rw [hsplit, hmul]
      change owenMeasure n E * owenMeasure n F = _
      rw [ih, hFm, ← pow_add, mul_add, mul_one]

/-- A depth-`M` cylinder of `Fin n × ℕ → Bool` as a box. -/
theorem cylinder_eq_pi (b : Fin n × ℕ → Bool) (M : ℕ) :
    {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} =
      Set.pi ((univ ×ˢ range M : Finset (Fin n × ℕ)) : Set (Fin n × ℕ))
        fun q ↦ ({b q} : Set Bool) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_pi, coe_product, coe_univ, coe_range, Set.mem_prod,
    Set.mem_univ, Set.mem_Iio, true_and, Set.mem_singleton_iff, Prod.forall]

/-- Cylinders are measurable. -/
theorem measurableSet_cylinder (b : Fin n × ℕ → Bool) (M : ℕ) :
    MeasurableSet {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} := by
  rw [cylinder_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) fun _ _ ↦ measurableSet_singleton _

/-- Cylinder probabilities of the digital-shift flips. -/
theorem shiftMeasure_cylinder (b : Fin n × ℕ → Bool) (M : ℕ) :
    shiftMeasure n {w | ∀ i, ∀ j < M, w (i, j) = b (i, j)} = 2⁻¹ ^ (n * M) := by
  classical
  rw [cylinder_eq_pi, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const, card_product, card_univ, Fintype.card_fin,
    card_range]

/-- A probability measure on `Fin n × ℕ → Bool` whose depth-`M` cylinders all have probability
`2^{-nM}` is the product of fair coins `shiftMeasure n`. -/
theorem eq_shiftMeasure_of_cylinder {μ : Measure (Fin n × ℕ → Bool)} [IsProbabilityMeasure μ]
    (h : ∀ (b : Fin n × ℕ → Bool) (M : ℕ),
      μ {w | ∀ i, ∀ j < M, w (i, j) = b (i, j)} = 2⁻¹ ^ (n * M)) :
    μ = shiftMeasure n := by
  classical
  have hmap : ∀ M, μ.map (Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M)) =
      (shiftMeasure n).map (Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M)) := by
    intro M
    refine Measure.ext_of_singleton fun g ↦ ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g)]
    set b : Fin n × ℕ → Bool := fun q ↦
      if hq : q ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) then g ⟨q, hq⟩ else false with hb
    have e : Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M) ⁻¹'
        ({g} : Set ((univ ×ˢ range M : Finset (Fin n × ℕ)) → Bool)) =
        {w : Fin n × ℕ → Bool | ∀ i, ∀ j < M, w (i, j) = b (i, j)} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl i j hj
        have hq : (i, j) ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) := by simp [hj]
        simp only [hb, hq, dite_true, Finset.restrict]
      · intro hw
        funext q
        have hq := q.2
        simp only [mem_product, mem_univ, mem_range, true_and] at hq
        have := hw q.1.1 q.1.2 hq
        simp only [hb, q.2, dite_true] at this
        exact this
    rw [e, h b M, shiftMeasure_cylinder]
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  set M := s.sup (fun q ↦ q.2) + 1 with hM
  have hsS : ∀ q ∈ s, q ∈ (univ ×ˢ range M : Finset (Fin n × ℕ)) := fun q hq ↦ by
    simp only [mem_product, mem_univ, mem_range, true_and, hM]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun q : Fin n × ℕ ↦ q.2) hq)
  set E : Set ((univ ×ˢ range M : Finset (Fin n × ℕ)) → Bool) :=
    {g | ∀ q (hq : q ∈ s), g ⟨q, hsS q hq⟩ ∈ t q} with hE
  have hpre : Finset.restrict (π := fun _ : Fin n × ℕ ↦ Bool) (univ ×ˢ range M) ⁻¹' E =
      Set.pi (s : Set (Fin n × ℕ)) t := by
    ext w
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, Set.mem_pi, mem_coe, Finset.restrict]
  have hEm : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← hpre, ← Measure.map_apply (Finset.measurable_restrict _) hEm, hmap M,
    Measure.map_apply (Finset.measurable_restrict _) hEm, hpre,
    Measure.infinitePi_pi _ fun q _ ↦ ht q]

/-- **Law equivalence of the path coins.** Under Owen's measure the path coins
`e_{i,j} = f_i j α_{i,j}` of all states form i.i.d. fair coins: their law is the law
`shiftMeasure n` of the digital-shift flips. -/
theorem map_owenPathCoins (cb : Fin n → ℕ → Bool) :
    (owenMeasure n).map (owenPathCoins cb) = shiftMeasure n := by
  refine eq_shiftMeasure_of_cylinder fun b M ↦ ?_
  rw [Measure.map_apply (measurable_owenPathCoins cb) (measurableSet_cylinder b M)]
  exact owenMeasure_pathCoins_cylinder cb b M

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Variance of the error of two-state scrambled-stack chains (post #3)

Post #3 finds that "normality cannot be rejected" for the per-state Sobol stacks in some runs.
The CLT of `CltStacks` normalises by the standard deviation and needs the variance to grow like
`log T`; this module shows that the hypothesis is not vacuous and that `log T` is the right
order.

By `CltPathBits`, for either randomisation the main term of the two-state chain is
`q · mainTerm = Σ_i Σ_{m : bit m of n_i} (1{LevelInd_{i,m}} − θ_{i,m})`, a function of i.i.d.
fair path coins (`coinSum`), where `θ_{i,m} = {2^m c_i}`. Each term is a centred Bernoulli
(`integral_levelVal`: `P(LevelInd) = {2^m c}`, as the digits beyond depth `m` form a uniform
number), terms of different states are uncorrelated, and two terms of the same state at levels
`m < m'` have covariance at most `2^{-(m'-m)}` (the tie cascade from `m` must survive to `m'`).

## Main results

* `covariance_eq_zero_of_approx`: two variables approximated in `L²` by independent ones are
  uncorrelated.
* `variance_sum_ge_of_cov`, `variance_sum_le_of_cov`: diagonal-dominance bounds.
* `integral_levelVal`, `variance_coinTerm`, `abs_covariance_coinTerm_le`,
  `covariance_coinTerm_eq_zero`: moments of the level terms on the coin space.
* `variance_coinSum_le`: `Var ≤ 5 K` for `K` levels (upper bound, every two-state chain).
* `variance_coinSum_pattern_ge` (**variance lower bound**): for `n₀ = n₁ = Σ_{i<k} 16^i` and
  thresholds whose fractional parts `{2^m c}` stay in `[1/3, 2/3]`, `Var ≥ 8k/45`.
* `IsPathCoinModel` (`isPathCoinModel_owen`, `isPathCoinModel_shift`): randomisations whose
  path coins are i.i.d. fair; `IsPathCoinModel.mainTerm_eq`, `.variance_mainTerm`,
  `.integral_mainTerm`: the main term is the coin sum of the path coins, centred, with variance
  `Var(coin sum)/q²` — the same for Owen and the digital shift.
* `IsPathCoinModel.abs_sqrt_variance_occErr_sub_le`: the standard deviations of the occupation
  error and of the main term differ by at most `anscBound = O(log log T)`.
* `exampleChain` (`p₁₁ = p₂₂ = 2/3`), `exampleTime k = 2 Σ_{i<k} 16^i`,
  `IsPathCoinModel.variance_mainTerm_example_ge` (`Var(main term) ≥ 2k/5`, every `k`) and
  `IsPathCoinModel.eventually_variance_occErr_example_ge`: for Owen-scrambled AND digitally
  shifted stacks, `Var(N₀(T_k) − T_k/2) ≥ k/12` eventually, while `log₂ T_k ≤ 4k + 1` — the
  variance does grow like `log T` (the REQUIRED non-vacuity of the CLT hypothesis).

Numerically (coin-space simulation, 2·10⁵ replications) the per-block variance at this pattern
is `≈ 0.209`, close to the diagonal value `2/9`; the bound `8k/45` uses `2/9 − 2/15`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Model-free covariance tools -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Uncorrelated by approximation.** If `X` and `Y` are `L²`-limits (in variance) of
independent pairs `(X_L, Y_L)`, then `cov[X, Y] = 0`. -/
theorem covariance_eq_zero_of_approx [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {Xa Ya : ℕ → Ω → ℝ} (hXa : ∀ L, MemLp (Xa L) 2 μ)
    (hYa : ∀ L, MemLp (Ya L) 2 μ) (hind : ∀ L, IndepFun (Xa L) (Ya L) μ)
    (hXe : Tendsto (fun L ↦ Var[X - Xa L; μ]) atTop (𝓝 0))
    (hYe : Tendsto (fun L ↦ Var[Y - Ya L; μ]) atTop (𝓝 0)) : cov[X, Y; μ] = 0 := by
  have hbound : ∀ L, |cov[X, Y; μ]| ≤ √Var[X - Xa L; μ] * √Var[Y; μ] +
      (√Var[X; μ] + √Var[X - Xa L; μ]) * √Var[Y - Ya L; μ] := by
    intro L
    have e : cov[X, Y; μ] = cov[X - Xa L, Y; μ] + cov[Xa L, Y - Ya L; μ] := by
      rw [covariance_sub_left hX (hXa L) hY, covariance_sub_right (hXa L) hY (hYa L),
        (hind L).covariance_eq_zero (hXa L) (hYa L)]
      ring
    have h1 := abs_covariance_le_sqrt (hX.sub (hXa L)) hY
    have h2 := abs_covariance_le_sqrt (hXa L) (hY.sub (hYa L))
    have h3 : √Var[Xa L; μ] ≤ √Var[X; μ] + √Var[X - Xa L; μ] := by
      have := abs_sqrt_variance_sub_le (μ := μ) hX (hXa L)
      have e' : (fun ω ↦ X ω - Xa L ω) = X - Xa L := rfl
      rw [e'] at this
      linarith [le_abs_self (√Var[Xa L; μ] - √Var[X; μ])]
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add h1 (h2.trans ?_))
    exact mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  have hlim : Tendsto (fun L ↦ √Var[X - Xa L; μ] * √Var[Y; μ] +
      (√Var[X; μ] + √Var[X - Xa L; μ]) * √Var[Y - Ya L; μ]) atTop (𝓝 0) := by
    have hs1 := (Real.continuous_sqrt.tendsto 0).comp hXe
    have hs2 := (Real.continuous_sqrt.tendsto 0).comp hYe
    rw [Real.sqrt_zero] at hs1 hs2
    have := (hs1.mul_const (√Var[Y; μ])).add
      (((tendsto_const_nhds (x := √Var[X; μ])).add hs1).mul hs2)
    rw [zero_mul, add_zero, mul_zero, add_zero] at this
    exact this
  have h0 : |cov[X, Y; μ]| ≤ 0 := ge_of_tendsto' hlim hbound
  exact abs_nonpos_iff.1 h0

/-- **Covariance with a small perturbation.** If `Z` takes values in an interval of length one,
then `|cov[R, Z]| ≤ E|R|`. -/
theorem abs_covariance_le_integral_abs [IsProbabilityMeasure μ] {R Z : Ω → ℝ}
    (hR : MemLp R 2 μ) (hZm : Measurable Z) {a : ℝ} (hZ : ∀ ω, Z ω ∈ Set.Icc a (a + 1)) :
    |cov[R, Z; μ]| ≤ ∫ ω, |R ω| ∂μ := by
  have hZi : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable (|a| + 1)
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_le]
      have := hZ ω
      constructor <;> linarith [abs_nonneg a, neg_abs_le a, le_abs_self a, this.1, this.2])
  have hRi : Integrable R μ := hR.integrable one_le_two
  have hEZ : μ[Z] ∈ Set.Icc a (a + 1) := by
    constructor
    · have := integral_mono (integrable_const a) hZi fun ω ↦ (hZ ω).1
      rwa [integral_const, probReal_univ, one_smul] at this
    · have := integral_mono hZi (integrable_const (a + 1)) fun ω ↦ (hZ ω).2
      rwa [integral_const, probReal_univ, one_smul] at this
  have hdev : ∀ ω, |Z ω - μ[Z]| ≤ 1 := fun ω ↦ by
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hZ ω
    obtain ⟨h3, h4⟩ := hEZ
    constructor <;> linarith
  have hint : Integrable (fun ω ↦ R ω * (Z ω - μ[Z])) μ := by
    refine Integrable.mono' hRi.abs ((hRi.aestronglyMeasurable).mul
      (hZm.sub measurable_const).aestronglyMeasurable) (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hdev ω)
  have e : cov[R, Z; μ] = ∫ ω, R ω * (Z ω - μ[Z]) ∂μ := by
    rw [covariance]
    have h1 : (fun ω ↦ (R ω - μ[R]) * (Z ω - μ[Z])) =
        fun ω ↦ R ω * (Z ω - μ[Z]) - μ[R] * (Z ω - μ[Z]) := funext fun ω ↦ by ring
    have hc : Integrable (fun ω ↦ μ[R] * (Z ω - μ[Z])) μ :=
      (hZi.sub (integrable_const (μ[Z]))).const_mul (μ[R])
    rw [h1, integral_sub hint hc, integral_const_mul, integral_sub hZi (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero]
  rw [e]
  refine (abs_integral_le_integral_abs).trans (integral_mono hint.abs hRi.abs fun ω ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hdev ω)

/-- **Diagonal dominance, lower bound.** If each variance is at least `a` and, for each index,
the absolute covariances with the others sum to at most `β`, then
`Var (Σ_{p∈s} Z p) ≥ |s| (a − β)`. -/
theorem variance_sum_ge_of_cov [IsFiniteMeasure μ] {κ : Type*} [DecidableEq κ] (s : Finset κ)
    {Z : κ → Ω → ℝ} (hZ : ∀ p ∈ s, MemLp (Z p) 2 μ) {a β : ℝ}
    (hdiag : ∀ p ∈ s, a ≤ Var[Z p; μ])
    (hrow : ∀ p ∈ s, ∑ p' ∈ s.erase p, |cov[Z p, Z p'; μ]| ≤ β) :
    s.card * (a - β) ≤ Var[fun ω ↦ ∑ p ∈ s, Z p ω; μ] := by
  rw [variance_fun_sum' hZ]
  have hp : ∀ p ∈ s, a - β ≤ ∑ p' ∈ s, cov[Z p, Z p'; μ] := by
    intro p hp
    rw [← add_sum_erase s _ hp, covariance_self (hZ p hp).aemeasurable]
    have h1 := hdiag p hp
    have h2 : -β ≤ ∑ p' ∈ s.erase p, cov[Z p, Z p'; μ] := by
      have := (abs_sum_le_sum_abs (fun p' ↦ cov[Z p, Z p'; μ]) (s.erase p)).trans (hrow p hp)
      linarith [neg_abs_le (∑ p' ∈ s.erase p, cov[Z p, Z p'; μ])]
    linarith
  calc (s.card : ℝ) * (a - β) = ∑ _p ∈ s, (a - β) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum hp

/-- **Diagonal dominance, upper bound.** -/
theorem variance_sum_le_of_cov [IsFiniteMeasure μ] {κ : Type*} [DecidableEq κ] (s : Finset κ)
    {Z : κ → Ω → ℝ} (hZ : ∀ p ∈ s, MemLp (Z p) 2 μ) {A β : ℝ}
    (hdiag : ∀ p ∈ s, Var[Z p; μ] ≤ A)
    (hrow : ∀ p ∈ s, ∑ p' ∈ s.erase p, |cov[Z p, Z p'; μ]| ≤ β) :
    Var[fun ω ↦ ∑ p ∈ s, Z p ω; μ] ≤ s.card * (A + β) := by
  rw [variance_fun_sum' hZ]
  have hp : ∀ p ∈ s, ∑ p' ∈ s, cov[Z p, Z p'; μ] ≤ A + β := by
    intro p hp
    rw [← add_sum_erase s _ hp, covariance_self (hZ p hp).aemeasurable]
    have h1 := hdiag p hp
    have h2 : ∑ p' ∈ s.erase p, cov[Z p, Z p'; μ] ≤ β :=
      (le_abs_self _).trans ((abs_sum_le_sum_abs _ _).trans (hrow p hp))
    linarith
  calc ∑ p ∈ s, ∑ p' ∈ s, cov[Z p, Z p'; μ] ≤ ∑ _p ∈ s, (A + β) := sum_le_sum hp
    _ = s.card * (A + β) := by rw [sum_const, nsmul_eq_mul]

/-! ### Level terms on the coin space -/

/-- The coins of state `i`. -/
def stateCoins (w : Fin 2 × ℕ → Bool) (i : Fin 2) : ℕ → Bool := fun j ↦ w (i, j)

/-- The fractional part `{2^m c}`. -/
noncomputable def fracPow (c : ℝ) (m : ℕ) : ℝ := 2 ^ m * c - ⌊2 ^ m * c⌋₊

/-- The level-`m` term of a stack with threshold `c` at index `N` (zero unless bit `m` of `N`
is set). -/
noncomputable def coinTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if N.testBit m then levelTerm c N m e else 0

/-- The level-`m` term truncated at depth `L`. -/
noncomputable def coinTermTrunc (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if N.testBit m then levelValTrunc (threshDigit c) N m L e - fracPow c m else 0

/-- **The coin sum** of a two-state chain with thresholds `c i` at indices `n i`, over the
levels `m < K`. -/
noncomputable def coinSum (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (K : ℕ) (w : Fin 2 × ℕ → Bool) : ℝ :=
  ∑ m ∈ range K, ∑ i, coinTerm (c i) (n i) m (stateCoins w i)

theorem fracPow_mem_Ico {c : ℝ} (hc0 : 0 ≤ c) (m : ℕ) : fracPow c m ∈ Set.Ico (0 : ℝ) 1 := by
  rw [fracPow]
  have h1 : (⌊2 ^ m * c⌋₊ : ℝ) ≤ 2 ^ m * c := Nat.floor_le (by positivity)
  have h2 := Nat.lt_floor_add_one (2 ^ m * c)
  constructor <;> linarith

theorem levelVal_mem (cb : ℕ → Bool) (N m : ℕ) (e : ℕ → Bool) :
    levelVal cb N m e = 0 ∨ levelVal cb N m e = 1 := by
  unfold levelVal
  split_ifs <;> simp

theorem levelValTrunc_mem (cb : ℕ → Bool) (N m L : ℕ) (e : ℕ → Bool) :
    levelValTrunc cb N m L e = 0 ∨ levelValTrunc cb N m L e = 1 := by
  unfold levelValTrunc
  split_ifs <;> simp

/-- The level term lies in `[-θ, 1 - θ]`, an interval of length one. -/
theorem coinTerm_mem {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    coinTerm c N m e ∈ Set.Icc (-(if N.testBit m then fracPow c m else 0))
      (-(if N.testBit m then fracPow c m else 0) + 1) := by
  have hf := fracPow_mem_Ico hc0 m
  unfold coinTerm levelTerm
  split_ifs
  · rcases levelVal_mem (threshDigit c) N m e with h | h <;>
      · rw [h]; constructor <;> simp only [fracPow] at hf ⊢ <;> linarith [hf.1, hf.2]
  · constructor <;> norm_num

/-- `|coinTerm| ≤ 1`. -/
theorem abs_coinTerm_le {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    |coinTerm c N m e| ≤ 1 := by
  have h := coinTerm_mem hc0 N m e
  have hf := fracPow_mem_Ico hc0 m
  rw [abs_le]
  split_ifs at h
  · constructor <;> linarith [h.1, h.2, hf.1, hf.2]
  · constructor <;> linarith [h.1, h.2]

/-- `|coinTermTrunc| ≤ 1`. -/
theorem abs_coinTermTrunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (e : ℕ → Bool) :
    |coinTermTrunc c N m L e| ≤ 1 := by
  have hf := fracPow_mem_Ico hc0 m
  unfold coinTermTrunc
  split_ifs
  · rw [abs_le]
    rcases levelValTrunc_mem (threshDigit c) N m L e with h | h <;> rw [h] <;>
      constructor <;> linarith [hf.1, hf.2]
  · simp

open Classical in
/-- The difference of the full and truncated level terms is at most the tie indicator. -/
theorem abs_coinTerm_sub_trunc_le (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) :
    |coinTerm c N m e - coinTermTrunc c N m L e| ≤
      (if LevelTie (threshDigit c) N m L e then 1 else 0) := by
  unfold coinTerm coinTermTrunc levelTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    have e1 : levelVal (threshDigit c) N m e - (2 ^ m * c - ⌊2 ^ m * c⌋₊) -
        (levelValTrunc (threshDigit c) N m L e - fracPow c m) =
        levelVal (threshDigit c) N m e - levelValTrunc (threshDigit c) N m L e := by
      rw [fracPow]
      ring
    rw [e1]
    by_cases ht : LevelTie (threshDigit c) N m L e
    · simp only [ht, ite_true]
      rcases levelVal_mem (threshDigit c) N m e with h | h <;>
        rcases levelValTrunc_mem (threshDigit c) N m L e with h' | h' <;> rw [h, h'] <;> norm_num
    · simp only [ht, ite_false]
      rw [(levelVal_eq_trunc_of_not_tie le_rfl ht).1, sub_self, abs_zero]
  · simp only [hb, Bool.false_eq_true, ite_false, sub_self, abs_zero]
    split_ifs <;> norm_num

/-- The truncated coin term of state `i` depends only on the coins `(i, j)`, `j ∈ [m, m+L)`. -/
theorem isLocal_coinTermTrunc (c : ℝ) (N m L : ℕ) (i : Fin 2) :
    IsLocal (fun w ↦ coinTermTrunc c N m L (stateCoins w i))
      ((({i} : Finset (Fin 2)) ×ˢ Finset.Ico m (m + L))) := by
  intro w w' h
  change coinTermTrunc c N m L (stateCoins w i) = coinTermTrunc c N m L (stateCoins w' i)
  unfold coinTermTrunc
  rw [levelValTrunc_congr (threshDigit c) N m L (e := stateCoins w i) (e' := stateCoins w' i)
    fun j hm hj ↦ h (i, j) (by simp [hm, hj])]

/-- The level indicator as a binary comparison of coins. -/
theorem levelInd_stateCoins_iff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (w : Fin 2 × ℕ → Bool) (i : Fin 2) :
    LevelInd (threshDigit c) N m (stateCoins w i) ↔
      binaryVal (fun j ↦ xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) ≤ fracPow c m :=
  levelInd_iff_binaryVal_le hc0 hc1 N m (stateCoins w i)

theorem measurableSet_levelInd {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    MeasurableSet {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} := by
  have e : {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} =
      (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (w ((fun j ↦ (i, j + m)) j))) ⁻¹'
          Set.Iic (fracPow c m) := by
    ext w
    exact levelInd_stateCoins_iff hc0 hc1 N m w i
  rw [e]
  exact (measurable_binaryVal.comp (measurable_xor_digits _ _)) measurableSet_Iic

theorem measurable_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    Measurable fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i) := by
  classical
  unfold coinTerm levelTerm levelVal
  split_ifs
  · exact (Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const
      measurable_const).sub measurable_const
  · exact measurable_const

/-- `P(LevelInd) = {2^m c}` under fair coins: the digits beyond depth `m` form a uniform
number. -/
theorem measureReal_levelInd {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    (shiftMeasure 2).real {w | LevelInd (threshDigit c) N m (stateCoins w i)} = fracPow c m := by
  have hg : Function.Injective fun j : ℕ ↦ ((i, j + m) : Fin 2 × ℕ) :=
    fun j j' h ↦ by simpa using congrArg Prod.snd h
  have hmap := map_binaryVal_xor_eq_uniformIco hg fun j ↦ (levelBase N m).testBit (j + m)
  have e : {w : Fin 2 × ℕ → Bool | LevelInd (threshDigit c) N m (stateCoins w i)} =
      (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) ⁻¹' Set.Iic (fracPow c m) := by
    ext w
    exact levelInd_stateCoins_iff hc0 hc1 N m w i
  have hXm : Measurable (fun w : Fin 2 × ℕ → Bool ↦ binaryVal fun j ↦
      xor ((levelBase N m).testBit (j + m)) (w (i, j + m))) :=
    measurable_binaryVal.comp (measurable_xor_digits (fun j ↦ ((i, j + m) : Fin 2 × ℕ)) _)
  have hf := fracPow_mem_Ico hc0 m
  rw [e, measureReal_def, ← Measure.map_apply hXm measurableSet_Iic, hmap,
    Measure.restrict_apply measurableSet_Iic]
  have hI : Set.Iic (fracPow c m) ∩ Set.Ico 0 1 = Set.Icc 0 (fracPow c m) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, lt_of_le_of_lt h2 hf.2⟩
  rw [hI, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hf.1]

/-- The level indicator has mean `{2^m c}`. -/
theorem integral_levelVal {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    ∫ w, levelVal (threshDigit c) N m (stateCoins w i) ∂(shiftMeasure 2) = fracPow c m := by
  classical
  have e : (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) =
      Set.indicator {w | LevelInd (threshDigit c) N m (stateCoins w i)} 1 := by
    funext w
    unfold levelVal
    by_cases h : LevelInd (threshDigit c) N m (stateCoins w i)
    · simp only [h, ite_true, Set.indicator_of_mem (show w ∈ {w |
        LevelInd (threshDigit c) N m (stateCoins w i)} from h), Pi.one_apply]
    · simp only [h, ite_false, Set.indicator_of_notMem (show w ∉ {w |
        LevelInd (threshDigit c) N m (stateCoins w i)} from h)]
  rw [e, integral_indicator_one (measurableSet_levelInd hc0 hc1 N m i),
    measureReal_levelInd hc0 hc1 N m i]

/-- The tie event as a cylinder of `L` coins. -/
theorem setOf_levelTie_eq (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    {w : Fin 2 × ℕ → Bool | LevelTie cb N m L (stateCoins w i)} =
      {w | ∀ j < L, xor ((levelBase N m).testBit (m + j)) (w ((fun j ↦ (i, m + j)) j)) =
        cb (m + j)} := by
  ext w
  simp only [Set.mem_ofPred_eq, LevelTie, levelDigits, stateCoins]
  constructor
  · intro h j hj
    exact h (m + j) (by omega) (by omega)
  · intro h j hm hj
    have := h (j - m) (by omega)
    rwa [show m + (j - m) = j by omega] at this

theorem measurableSet_levelTie (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    MeasurableSet {w : Fin 2 × ℕ → Bool | LevelTie cb N m L (stateCoins w i)} := by
  rw [setOf_levelTie_eq]
  exact measurableSet_xor_cylinder _ _ _ L

/-- **The tie cascade survives `L` levels with probability `2^{-L}`.** -/
theorem measureReal_levelTie (cb : ℕ → Bool) (N m L : ℕ) (i : Fin 2) :
    (shiftMeasure 2).real {w | LevelTie cb N m L (stateCoins w i)} = (1 / 2) ^ L := by
  have hg : Function.Injective fun j : ℕ ↦ ((i, m + j) : Fin 2 × ℕ) :=
    fun j j' h ↦ by simpa using congrArg Prod.snd h
  rw [setOf_levelTie_eq, measureReal_def, infinitePi_xor_cylinder hg, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- Level terms of the coin space are in `L²`. -/
theorem memLp_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    MemLp (fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i)) 2 (shiftMeasure 2) :=
  MemLp.of_bound (measurable_coinTerm hc0 hc1 N m i).aestronglyMeasurable 1
    (Eventually.of_forall fun w ↦ by rw [Real.norm_eq_abs]; exact abs_coinTerm_le hc0 N m _)

theorem memLp_coinTermTrunc {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (i : Fin 2) :
    MemLp (fun w : Fin 2 × ℕ → Bool ↦ coinTermTrunc c N m L (stateCoins w i)) 2
      (shiftMeasure 2) :=
  MemLp.of_bound (isLocal_coinTermTrunc c N m L i).measurable.aestronglyMeasurable 1
    (Eventually.of_forall fun w ↦ by rw [Real.norm_eq_abs]; exact abs_coinTermTrunc_le hc0 N m L _)

/-- **Truncation error in `L²`**: `E[(Y − Y_L)²] ≤ 2^{-L}`. -/
theorem integral_sq_coinTerm_sub_trunc_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m L : ℕ)
    (i : Fin 2) :
    ∫ w, (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2
      ∂(shiftMeasure 2) ≤ (1 / 2) ^ L := by
  classical
  set S := {w : Fin 2 × ℕ → Bool | LevelTie (threshDigit c) N m L (stateCoins w i)} with hS
  have hSm : MeasurableSet S := measurableSet_levelTie _ N m L i
  have hpt : ∀ w, (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2
      ≤ S.indicator 1 w := by
    intro w
    have h1 := abs_coinTerm_sub_trunc_le c N m L (stateCoins w i)
    have h2 : |coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)| ≤ 1 :=
      h1.trans (by split_ifs <;> norm_num)
    have h3 : (coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)) ^ 2 ≤
        |coinTerm c N m (stateCoins w i) - coinTermTrunc c N m L (stateCoins w i)| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (coinTerm c N m (stateCoins w i) -
        coinTermTrunc c N m L (stateCoins w i))]
    refine h3.trans (h1.trans (le_of_eq ?_))
    by_cases ht : LevelTie (threshDigit c) N m L (stateCoins w i)
    · simp only [ht, ite_true, Set.indicator_of_mem (show w ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show w ∉ S from ht)]
  have hint : Integrable (fun w ↦ (coinTerm c N m (stateCoins w i) -
      coinTermTrunc c N m L (stateCoins w i)) ^ 2) (shiftMeasure 2) :=
    ((memLp_coinTerm hc0 hc1 N m i).sub (memLp_coinTermTrunc hc0 N m L i)).integrable_sq
  have hind : Integrable (S.indicator (1 : (Fin 2 × ℕ → Bool) → ℝ)) (shiftMeasure 2) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono hint hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie]

/-- The variance of `Y - Y_L` tends to zero. -/
theorem tendsto_variance_coinTerm_sub_trunc {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (i : Fin 2) :
    Tendsto (fun L ↦ Var[(fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i)) -
      (fun w ↦ coinTermTrunc c N m L (stateCoins w i)); shiftMeasure 2]) atTop (𝓝 0) := by
  refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine (variance_le_expectation_sq ((memLp_coinTerm hc0 hc1 N m i).sub
    (memLp_coinTermTrunc hc0 N m L i)).aestronglyMeasurable).trans ?_
  exact le_of_eq_of_le rfl (integral_sq_coinTerm_sub_trunc_le hc0 hc1 N m L i)

/-- **Variance of a level term**: `θ(1 − θ)` with `θ = {2^m c}` if bit `m` of `N` is set. -/
theorem variance_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    Var[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i); shiftMeasure 2] =
      if N.testBit m then fracPow c m * (1 - fracPow c m) else 0 := by
  classical
  unfold coinTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    unfold levelTerm
    have hm : Measurable fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i) :=
      Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const measurable_const
    rw [variance_sub_const hm.aestronglyMeasurable]
    have hL2 : MemLp (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) 2
        (shiftMeasure 2) :=
      MemLp.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun w ↦ by
        rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> simp)
    rw [variance_eq_sub hL2]
    have hsq : (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i)) ^ 2 =
        fun w ↦ levelVal (threshDigit c) N m (stateCoins w i) := by
      funext w
      simp only [Pi.pow_apply]
      rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> norm_num
    rw [hsq, integral_levelVal hc0 hc1 N m i]
    ring
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact variance_zero _

/-! ### Covariances of level terms -/

/-- **Different states are uncorrelated.** -/
theorem covariance_coinTerm_eq_zero {c c' : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hc0' : 0 ≤ c')
    (hc1' : c' < 1) (N N' m m' : ℕ) {i i' : Fin 2} (hii' : i ≠ i') :
    cov[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i),
      fun w ↦ coinTerm c' N' m' (stateCoins w i'); shiftMeasure 2] = 0 := by
  refine covariance_eq_zero_of_approx (memLp_coinTerm hc0 hc1 N m i)
    (memLp_coinTerm hc0' hc1' N' m' i') (fun L ↦ memLp_coinTermTrunc hc0 N m L i)
    (fun L ↦ memLp_coinTermTrunc hc0' N' m' L i') (fun L ↦ ?_)
    (tendsto_variance_coinTerm_sub_trunc hc0 hc1 N m i)
    (tendsto_variance_coinTerm_sub_trunc hc0' hc1' N' m' i')
  refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_coinTermTrunc c N m L i)
    (isLocal_coinTermTrunc c' N' m' L i') (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
  simp only [mem_product, mem_singleton] at hq hq'
  exact hii' (hq.1.symm.trans hq'.1)

/-- **Same state: covariance decays geometrically.** For `m < m'` the cascade from level `m`
must tie on `[m, m')` to reach level `m'`, so `|cov| ≤ 2^{-(m'-m)}`. -/
theorem abs_covariance_coinTerm_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N N' m m' : ℕ)
    (i : Fin 2) (hmm' : m < m') :
    |cov[fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i),
      fun w ↦ coinTerm c N' m' (stateCoins w i); shiftMeasure 2]| ≤ (1 / 2) ^ (m' - m) := by
  classical
  set Y := fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N m (stateCoins w i) with hY
  set Y' := fun w : Fin 2 × ℕ → Bool ↦ coinTerm c N' m' (stateCoins w i) with hY'
  set Yh := fun w : Fin 2 × ℕ → Bool ↦ coinTermTrunc c N m (m' - m) (stateCoins w i) with hYh
  have hY2 := memLp_coinTerm hc0 hc1 N m i
  have hY'2 := memLp_coinTerm hc0 hc1 N' m' i
  have hYh2 := memLp_coinTermTrunc hc0 N m (m' - m) i
  -- the truncated part is uncorrelated with the higher level
  have h0 : cov[Yh, Y'; shiftMeasure 2] = 0 := by
    refine covariance_eq_zero_of_approx hYh2 hY'2 (Xa := fun _ ↦ Yh) (fun _ ↦ hYh2)
      (fun L ↦ memLp_coinTermTrunc hc0 N' m' L i) (fun L ↦ ?_) ?_
      (tendsto_variance_coinTerm_sub_trunc hc0 hc1 N' m' i)
    · refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_coinTermTrunc c N m (m' - m) i)
        (isLocal_coinTermTrunc c N' m' L i) (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
      simp only [mem_product, mem_singleton, Finset.mem_Ico] at hq hq'
      omega
    · simp only [sub_self, variance_zero, tendsto_const_nhds]
  -- the remainder
  have e : cov[Y, Y'; shiftMeasure 2] = cov[Y - Yh, Y'; shiftMeasure 2] := by
    rw [covariance_sub_left hY2 hYh2 hY'2, h0, sub_zero]
  rw [e]
  have hY'm : Measurable Y' := measurable_coinTerm hc0 hc1 N' m' i
  refine (abs_covariance_le_integral_abs (hY2.sub hYh2) hY'm
    (fun w ↦ coinTerm_mem hc0 N' m' (stateCoins w i))).trans ?_
  set S := {w : Fin 2 × ℕ → Bool | LevelTie (threshDigit c) N m (m' - m) (stateCoins w i)}
    with hS
  have hSm : MeasurableSet S := measurableSet_levelTie _ N m _ i
  have hpt : ∀ w, |(Y - Yh) w| ≤ S.indicator 1 w := by
    intro w
    have h1 := abs_coinTerm_sub_trunc_le c N m (m' - m) (stateCoins w i)
    refine h1.trans (le_of_eq ?_)
    by_cases ht : LevelTie (threshDigit c) N m (m' - m) (stateCoins w i)
    · simp only [ht, ite_true, Set.indicator_of_mem (show w ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show w ∉ S from ht)]
  have hind : Integrable (S.indicator (1 : (Fin 2 × ℕ → Bool) → ℝ)) (shiftMeasure 2) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono ((hY2.sub hYh2).integrable one_le_two).abs hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie]

/-- **Geometric row sums.** `Σ_{m' ≠ m, m' < K} r^{|m - m'|} ≤ 2 r/(1 - r)`. -/
theorem sum_erase_pow_dist_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m K : ℕ) :
    ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)) ≤ 2 * (r / (1 - r)) := by
  classical
  rw [← sum_filter_add_sum_filter_not ((range K).erase m) (fun m' ↦ m' < m)]
  have hA : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ m' < m), r ^ (m - m' + (m' - m)) ≤
      r / (1 - r) := by
    have e : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ m' < m), r ^ (m - m' + (m' - m)) =
        ∑ d ∈ (((range K).erase m).filter (fun m' ↦ m' < m)).image (fun m' ↦ m - m'), r ^ d := by
      rw [sum_image]
      · refine sum_congr rfl fun m' hm' ↦ ?_
        have := (mem_filter.1 hm').2
        rw [show m' - m = 0 by omega, add_zero]
      · intro a ha b hb h
        have := (mem_filter.1 ha).2
        have := (mem_filter.1 hb).2
        simp only at h
        omega
    rw [e]
    refine (sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 1 (m + 1)) ?_
      fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
    · intro d hd
      obtain ⟨m', hm', rfl⟩ := mem_image.1 hd
      have := (mem_filter.1 hm').2
      exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
    · have := geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) hr0 hr1
      rwa [pow_one] at this
  have hB : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ ¬ m' < m), r ^ (m - m' + (m' - m)) ≤
      r / (1 - r) := by
    have e : ∑ m' ∈ ((range K).erase m).filter (fun m' ↦ ¬ m' < m), r ^ (m - m' + (m' - m)) =
        ∑ d ∈ (((range K).erase m).filter (fun m' ↦ ¬ m' < m)).image (fun m' ↦ m' - m),
          r ^ d := by
      rw [sum_image]
      · refine sum_congr rfl fun m' hm' ↦ ?_
        have := (mem_filter.1 hm').2
        rw [show m - m' = 0 by omega, zero_add]
      · intro a ha b hb h
        have h1 := (mem_filter.1 ha).2
        have h2 := (mem_filter.1 hb).2
        simp only at h
        omega
    rw [e]
    refine (sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 1 (K + 1)) ?_
      fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
    · intro d hd
      obtain ⟨m', hm', rfl⟩ := mem_image.1 hd
      have h1 := (mem_filter.1 hm').2
      have h2 := (mem_filter.1 hm').1
      rw [mem_erase, mem_range] at h2
      exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
    · have := geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) hr0 hr1
      rwa [pow_one] at this
  linarith

/-! ### Variance of the coin sum -/

/-- The level term at coordinate `p = (state, level)`. -/
noncomputable def coinZ (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (p : Fin 2 × ℕ) (w : Fin 2 × ℕ → Bool) :
    ℝ :=
  coinTerm (c p.1) (n p.1) p.2 (stateCoins w p.1)

theorem coinSum_eq_sum_coinZ (c : Fin 2 → ℝ) (n : Fin 2 → ℕ) (K : ℕ) (w : Fin 2 × ℕ → Bool) :
    coinSum c n K w = ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w := by
  rw [coinSum, sum_product, sum_comm]
  rfl

/-- The covariance bound between two coordinates. -/
noncomputable def covBound (r : ℝ) (p p' : Fin 2 × ℕ) : ℝ :=
  if p.1 = p'.1 ∧ p.2 ≠ p'.2 then r ^ (p.2 - p'.2 + (p'.2 - p.2)) else 0

theorem abs_covariance_coinZ_le {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    {p p' : Fin 2 × ℕ} (hpp' : p ≠ p') :
    |cov[coinZ c n p, coinZ c n p'; shiftMeasure 2]| ≤ covBound (1 / 2) p p' := by
  obtain ⟨i, m⟩ := p
  obtain ⟨i', m'⟩ := p'
  unfold covBound
  by_cases hi : i = i'
  · subst hi
    have hm : m ≠ m' := fun h ↦ hpp' (by rw [h])
    simp only [hm, ne_eq, not_false_eq_true, and_self, ite_true]
    rcases lt_or_gt_of_ne hm with h | h
    · have := abs_covariance_coinTerm_le (hc i).1 (hc i).2 (n i) (n i) m m' i h
      rw [show m - m' + (m' - m) = m' - m by omega]
      exact this
    · have := abs_covariance_coinTerm_le (hc i).1 (hc i).2 (n i) (n i) m' m i h
      rw [covariance_comm] at this
      rw [show m - m' + (m' - m) = m - m' by omega]
      exact this
  · simp only [hi, false_and, ite_false]
    rw [show coinZ c n (i, m) = fun w ↦ coinTerm (c i) (n i) m (stateCoins w i) from rfl,
      show coinZ c n (i', m') = fun w ↦ coinTerm (c i') (n i') m' (stateCoins w i') from rfl,
      covariance_coinTerm_eq_zero (hc i).1 (hc i).2 (hc i').1 (hc i').2 _ _ _ _ hi, abs_zero]

/-- Row sums of `covBound` over `Fin 2 × range K`. -/
theorem sum_erase_covBound_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) (p : Fin 2 × ℕ) :
    ∑ p' ∈ ((univ : Finset (Fin 2)) ×ˢ range K).erase p, covBound r p p' ≤ 2 * (r / (1 - r)) := by
  classical
  obtain ⟨i, m⟩ := p
  rw [sum_erase _ (by simp [covBound]), sum_product]
  have h : ∀ i' : Fin 2, ∑ m' ∈ range K, covBound r (i, m) (i', m') =
      if i = i' then ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)) else 0 := by
    intro i'
    by_cases hi : i = i'
    · subst hi
      simp only [covBound, true_and, ite_true]
      rw [← sum_filter, filter_ne]
    · simp [covBound, hi]
  simp only [h]
  rw [sum_ite_eq univ i (fun _ ↦ ∑ m' ∈ (range K).erase m, r ^ (m - m' + (m' - m)))]
  simp only [mem_univ, ite_true]
  exact sum_erase_pow_dist_le hr0 hr1 m K

theorem memLp_coinZ {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    (p : Fin 2 × ℕ) : MemLp (coinZ c n p) 2 (shiftMeasure 2) :=
  memLp_coinTerm (hc p.1).1 (hc p.1).2 (n p.1) p.2 p.1

theorem memLp_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) (K : ℕ) :
    MemLp (coinSum c n K) 2 (shiftMeasure 2) := by
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e]
  exact memLp_finsetSum _ fun p _ ↦ memLp_coinZ hc n p

/-- **Variance upper bound** for every two-state chain: `Var(coin sum over K levels) ≤ 5K`. -/
theorem variance_coinSum_le {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ)
    (K : ℕ) : Var[coinSum c n K; shiftMeasure 2] ≤ 5 * K := by
  classical
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e]
  have h := variance_sum_le_of_cov (μ := shiftMeasure 2) ((univ : Finset (Fin 2)) ×ˢ range K)
    (Z := coinZ c n) (fun p _ ↦ memLp_coinZ hc n p) (A := 1 / 4) (β := 2)
    (fun p _ ↦ ?_) (fun p _ ↦ ?_)
  · refine h.trans ?_
    rw [card_product, card_univ, Fintype.card_fin, card_range]
    push_cast
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  · rw [show coinZ c n p = fun w ↦ coinTerm (c p.1) (n p.1) p.2 (stateCoins w p.1) from rfl,
      variance_coinTerm (hc p.1).1 (hc p.1).2]
    split_ifs
    · nlinarith [sq_nonneg (fracPow (c p.1) p.2 - 1 / 2)]
    · norm_num
  · refine (sum_le_sum fun p' hp' ↦ abs_covariance_coinZ_le hc n (ne_of_mem_erase hp').symm).trans
      ?_
    have := sum_erase_covBound_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) K p
    refine this.trans (le_of_eq ?_)
    norm_num

/-! ### A concrete lower bound -/

/-- The index `N_k = Σ_{a<k} 16^a`, binary digits `0001` repeated `k` times. -/
def patternN (k : ℕ) : ℕ := ∑ a ∈ range k, 16 ^ a

theorem patternN_lt (k : ℕ) : patternN k < 2 ^ (4 * k) := by
  induction k with
  | zero => simp [patternN]
  | succ k ih =>
      rw [patternN, sum_range_succ, ← patternN, show 4 * (k + 1) = 4 * k + 4 by ring, pow_add,
        show (16 : ℕ) ^ k = 2 ^ (4 * k) by rw [pow_mul]; norm_num]
      have : 0 < 2 ^ (4 * k) := Nat.two_pow_pos _
      omega

/-- The bits of `N_k` are exactly the levels `4a`, `a < k`. -/
theorem testBit_patternN (k m : ℕ) :
    (patternN k).testBit m = true ↔ m % 4 = 0 ∧ m / 4 < k := by
  induction k generalizing m with
  | zero => simp [patternN]
  | succ k ih =>
      have e : patternN (k + 1) = 2 ^ (4 * k) * 1 + patternN k := by
        rw [patternN, sum_range_succ, ← patternN, show (16 : ℕ) ^ k = 2 ^ (4 * k) by
          rw [pow_mul]; norm_num]
        ring
      rw [e, Nat.testBit_two_pow_mul_add _ (patternN_lt k)]
      by_cases hm : m < 4 * k
      · simp only [hm, ite_true]
        rw [ih]
        omega
      · simp only [hm, ite_false, Nat.testBit_one_eq_true_iff_self_eq_zero]
        omega

/-- A fraction `M/3` with `3 ∤ M` has fractional part `1/3` or `2/3`. -/
theorem frac_div_three_mem {M : ℕ} (hM : ¬ 3 ∣ M) :
    (M : ℝ) / 3 - ⌊(M : ℝ) / 3⌋₊ ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h1 : ⌊(M : ℝ) / 3⌋₊ = M / 3 := by
    have := Nat.floor_div_eq_div (K := ℝ) M 3
    rwa [Nat.cast_ofNat] at this
  rw [h1]
  have h2 : (M : ℝ) = 3 * ((M / 3 : ℕ) : ℝ) + ((M % 3 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod M 3).symm
  have h3 : M % 3 = 1 ∨ M % 3 = 2 := by omega
  rw [h2]
  rcases h3 with h | h <;> rw [h] <;> constructor <;> norm_num <;> ring_nf <;> norm_num

theorem not_three_dvd_two_pow (k : ℕ) : ¬ 3 ∣ 2 ^ k := fun h ↦ by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- `{2^m · 2/3} ∈ {1/3, 2/3}`. -/
theorem fracPow_two_thirds_mem (m : ℕ) : fracPow (2 / 3) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h := frac_div_three_mem (not_three_dvd_two_pow (m + 1))
  have e : (2 : ℝ) ^ m * (2 / 3) = ((2 ^ (m + 1) : ℕ) : ℝ) / 3 := by
    push_cast
    ring
  rw [fracPow, e]
  exact h

/-- `{2^m · 1/3} ∈ {1/3, 2/3}`. -/
theorem fracPow_one_third_mem (m : ℕ) : fracPow (1 / 3) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have h := frac_div_three_mem (not_three_dvd_two_pow m)
  have e : (2 : ℝ) ^ m * (1 / 3) = ((2 ^ m : ℕ) : ℝ) / 3 := by
    push_cast
    ring
  rw [fracPow, e]
  exact h

/-- The coin sum at `N_k` only has the levels `4a`, `a < k`. -/
theorem coinSum_patternN (c : Fin 2 → ℝ) (k : ℕ) (w : Fin 2 × ℕ → Bool) :
    coinSum c (fun _ ↦ patternN k) (4 * k) w =
      ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range k, coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2) w := by
  classical
  rw [sum_product, sum_comm, coinSum]
  have himg : (range k).image (fun a ↦ 4 * a) ⊆ range (4 * k) := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hm
    rw [mem_range] at ha ⊢
    omega
  rw [← sum_subset himg, sum_image (fun a _ b _ h ↦ by omega)]
  · rfl
  · intro m _ hm
    refine sum_eq_zero fun i _ ↦ ?_
    have hb : (patternN k).testBit m = false := by
      by_contra hc
      rw [Bool.not_eq_false, testBit_patternN] at hc
      exact hm (mem_image.2 ⟨m / 4, mem_range.2 hc.2, by omega⟩)
    simp [coinTerm, hb]

/-- **Variance lower bound on the coin space.** If all the fractional parts `{2^m c_i}` lie in
`[1/3, 2/3]`, then at `n₀ = n₁ = N_k = Σ_{a<k} 16^a` the coin sum has variance `≥ 8k/45`. -/
theorem variance_coinSum_pattern_ge {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1)
    (hfrac : ∀ i m, fracPow (c i) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)) (k : ℕ) :
    8 * k / 45 ≤ Var[coinSum c (fun _ ↦ patternN k) (4 * k); shiftMeasure 2] := by
  classical
  have e : coinSum c (fun _ ↦ patternN k) (4 * k) = fun w ↦
      ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range k, coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2) w :=
    funext (coinSum_patternN c k)
  rw [e]
  have h := variance_sum_ge_of_cov (μ := shiftMeasure 2) ((univ : Finset (Fin 2)) ×ˢ range k)
    (Z := fun p ↦ coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2))
    (fun p _ ↦ memLp_coinZ hc _ _) (a := 2 / 9) (β := 2 / 15) (fun p hp ↦ ?_) (fun p _ ↦ ?_)
  · refine le_of_eq_of_le ?_ h
    rw [card_product, card_univ, Fintype.card_fin, card_range]
    push_cast
    ring
  · have hb : (patternN k).testBit (4 * p.2) = true := by
      rw [testBit_patternN]
      simp only [mem_product, mem_univ, mem_range, true_and] at hp
      omega
    change 2 / 9 ≤ Var[fun w ↦ coinTerm (c p.1) (patternN k) (4 * p.2) (stateCoins w p.1);
      shiftMeasure 2]
    rw [variance_coinTerm (hc p.1).1 (hc p.1).2]
    simp only [hb, ↓reduceIte]
    have := hfrac p.1 (4 * p.2)
    nlinarith [this.1, this.2]
  · have hrow : ∀ p' ∈ ((univ : Finset (Fin 2)) ×ˢ range k).erase p,
        |cov[coinZ c (fun _ ↦ patternN k) (p.1, 4 * p.2),
          coinZ c (fun _ ↦ patternN k) (p'.1, 4 * p'.2); shiftMeasure 2]| ≤
          covBound (1 / 16) p p' := by
      intro p' hp'
      have hne : p' ≠ p := ne_of_mem_erase hp'
      have hne' : (p.1, 4 * p.2) ≠ (p'.1, 4 * p'.2) := fun h ↦ hne (by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext h1.symm (by omega))
      refine (abs_covariance_coinZ_le hc _ hne').trans (le_of_eq ?_)
      unfold covBound
      have hiff : (p.1 = p'.1 ∧ 4 * p.2 ≠ 4 * p'.2) ↔ (p.1 = p'.1 ∧ p.2 ≠ p'.2) :=
        and_congr_right fun _ ↦ by omega
      simp only [hiff]
      split_ifs
      · rw [show 4 * p.2 - 4 * p'.2 + (4 * p'.2 - 4 * p.2) = 4 * (p.2 - p'.2 + (p'.2 - p.2)) by
          omega, pow_mul]
        norm_num
      · rfl
    refine (sum_le_sum hrow).trans ?_
    have := sum_erase_covBound_le (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num) k p
    refine this.trans (le_of_eq ?_)
    norm_num

/-- The mean of a level term is zero. -/
theorem integral_coinTerm {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (i : Fin 2) :
    ∫ w, coinTerm c N m (stateCoins w i) ∂(shiftMeasure 2) = 0 := by
  classical
  unfold coinTerm
  by_cases hb : N.testBit m = true
  · simp only [hb, ite_true]
    unfold levelTerm
    have hm : Measurable fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i) :=
      Measurable.ite (measurableSet_levelInd hc0 hc1 N m i) measurable_const measurable_const
    have hi : Integrable (fun w : Fin 2 × ℕ → Bool ↦ levelVal (threshDigit c) N m (stateCoins w i))
        (shiftMeasure 2) :=
      Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun w ↦ by
        rcases levelVal_mem (threshDigit c) N m (stateCoins w i) with h | h <;> rw [h] <;> simp)
    rw [integral_sub hi (integrable_const _), integral_levelVal hc0 hc1, integral_const,
      probReal_univ, one_smul, fracPow, sub_self]
  · simp only [hb, Bool.false_eq_true, ite_false, integral_zero]

/-- The coin sum has mean zero. -/
theorem integral_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) (K : ℕ) :
    ∫ w, coinSum c n K w ∂(shiftMeasure 2) = 0 := by
  have e : coinSum c n K = fun w ↦ ∑ p ∈ (univ : Finset (Fin 2)) ×ˢ range K, coinZ c n p w :=
    funext (coinSum_eq_sum_coinZ c n K)
  rw [e, integral_finsetSum _ fun p _ ↦ (memLp_coinZ hc n p).integrable one_le_two]
  exact sum_eq_zero fun p _ ↦ integral_coinTerm (hc p.1).1 (hc p.1).2 _ _ _

/-! ### Connection with the chain -/

/-- The thresholds `c_i = p_{i0}` of a two-state chain. -/
def chainThresh (P : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦ P i 0

/-- The deterministic indices `n₀ = ⌊T π₀⌋`, `n₁ = ⌊T π₁⌋`. -/
noncomputable def chainIdx (P : Fin 2 → Fin 2 → ℝ) (T : ℕ) : Fin 2 → ℕ :=
  fun i ↦ if i = 0 then ⌊T * piZero P⌋₊ else ⌊T * piOne P⌋₊

/-- The threshold digits of the two rows. -/
noncomputable def chainDigits (P : Fin 2 → Fin 2 → ℝ) : Fin 2 → ℕ → Bool :=
  fun i ↦ threshDigit (P i 0)

/-- **The level decomposition of both stacks** (every flip table). -/
theorem sum_segErr_eq_coinSum (f : Fin 2 → ℕ → ℕ → Bool) {c : Fin 2 → ℝ}
    (hc : ∀ i, 0 ≤ c i ∧ c i < 1) (n : Fin 2 → ℕ) {K : ℕ} (hn : ∀ i, n i < 2 ^ K) :
    ∑ i, segErr (scrambledVdc (f i)) (c i) 0 (n i) =
      coinSum c n K (fun p ↦ pathCoin (f p.1) (threshDigit (c p.1)) p.2) := by
  rw [coinSum, sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [segErr_scrambledVdc_eq_sum_level (f i) (hc i).1 (hc i).2 (hn i), sum_filter]
  rfl

/-- `n_i ≤ T`. -/
theorem chainIdx_le {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0)
    (T : ℕ) (i : Fin 2) : chainIdx P T i ≤ T := by
  have hz : piZero P ≤ 1 := by
    rw [piZero, div_le_one hq]
    linarith [hP.nonneg 0 1]
  have ho : piOne P ≤ 1 := by
    rw [piOne, div_le_one hq]
    linarith [hP.nonneg 1 0]
  have h : ∀ x : ℝ, x ≤ 1 → ⌊(T : ℝ) * x⌋₊ ≤ T := fun x hx ↦ by
    refine Nat.floor_le_of_le ?_
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  unfold chainIdx
  split_ifs
  · exact h _ hz
  · exact h _ ho

/-- The thresholds `p_{00}, p_{10}` are in `[0,1)` when `p_{01}, p_{11} > 0`. -/
theorem chainThresh_mem {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (i : Fin 2) : 0 ≤ chainThresh P i ∧ chainThresh P i < 1 := by
  refine ⟨hP.nonneg i 0, ?_⟩
  have h := hP.sum_eq_one i
  rw [Fin.sum_univ_two] at h
  have hi1 : 0 < P i 1 := by
    fin_cases i
    exacts [h01, h11]
  change P i 0 < 1
  linarith

/-- **The main term as a coin sum** (every flip table). -/
theorem mul_mainTerm_eq_coinSum {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (f : Fin 2 → ℕ → ℕ → Bool) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    (P 0 1 + P 1 0) * mainTerm P f T = coinSum (chainThresh P) (chainIdx P T) K
      (fun p ↦ pathCoin (f p.1) (threshDigit (P p.1 0)) p.2) := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have h := sum_segErr_eq_coinSum f (chainThresh_mem hP h01 h11) (chainIdx P T) hT
  rw [show (fun p : Fin 2 × ℕ ↦ pathCoin (f p.1) (threshDigit (P p.1 0)) p.2) =
    (fun p ↦ pathCoin (f p.1) (threshDigit (chainThresh P p.1)) p.2) from rfl, ← h,
    Fin.sum_univ_two, mainTerm, mul_div_cancel₀ _ hq.ne']
  rfl

/-- For Owen's scramble the path-coin map is `owenPathCoins`. -/
theorem owenPathCoins_chainDigits (P : Fin 2 → Fin 2 → ℝ) (ω : Fin 2 × ℕ × ℕ → Bool) :
    owenPathCoins (chainDigits P) ω =
      fun p ↦ pathCoin (owenTable ω p.1) (threshDigit (P p.1 0)) p.2 := rfl

/-- For the digital shift the path coins are the flips. -/
theorem shiftPathCoins_eq (P : Fin 2 → Fin 2 → ℝ) (ω : Fin 2 × ℕ → Bool) :
    (fun p : Fin 2 × ℕ ↦ pathCoin (shiftFlips ω p.1) (threshDigit (P p.1 0)) p.2) = ω := rfl

/-! ### Randomisations through the path coins -/

variable {Ω : Type*} [MeasurableSpace Ω] (P : Fin 2 → Fin 2 → ℝ) (μ : Measure Ω)
  (F : Ω → Fin 2 → ℕ → ℕ → Bool) (Ψ : Ω → Fin 2 × ℕ → Bool) in
/-- A randomisation of the two flip tables (`F ω`) whose path coins along the two thresholds
are a measure-preserving map `Ψ` to the fair coins `shiftMeasure 2`. Owen's scramble and the
digital shift are both of this kind (`isPathCoinModel_owen`, `isPathCoinModel_shift`). -/
structure IsPathCoinModel : Prop where
  /-- The path coins are i.i.d. fair. -/
  measurePreserving : MeasurePreserving Ψ μ (shiftMeasure 2)
  /-- The path coins of the flip tables. -/
  pathCoin_eq : ∀ ω p, pathCoin (F ω p.1) (threshDigit (P p.1 0)) p.2 = Ψ ω p
  /-- The stack points are measurable. -/
  measurable_stack : ∀ i k, Measurable fun ω ↦ scrambledStack (F ω) i k

/-- **Owen's scramble is a path-coin model** (`map_owenPathCoins`). -/
theorem isPathCoinModel_owen (P : Fin 2 → Fin 2 → ℝ) :
    IsPathCoinModel P (owenMeasure 2) owenTable (owenPathCoins (chainDigits P)) where
  measurePreserving := ⟨measurable_owenPathCoins _, map_owenPathCoins _⟩
  pathCoin_eq _ _ := rfl
  measurable_stack := measurable_scrambledStack_owen

/-- **The digital shift is a path-coin model**: the path coins are the flips. -/
theorem isPathCoinModel_shift (P : Fin 2 → Fin 2 → ℝ) :
    IsPathCoinModel P (shiftMeasure 2) shiftFlips id where
  measurePreserving := MeasurePreserving.id _
  pathCoin_eq _ _ := rfl
  measurable_stack := measurable_scrambledStack_shift

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- In a path-coin model the main term is the coin sum of the path coins over `q`. -/
theorem IsPathCoinModel.mainTerm_eq (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    (fun ω ↦ mainTerm P (F ω) T) =
      fun ω ↦ coinSum (chainThresh P) (chainIdx P T) K (Ψ ω) / (P 0 1 + P 1 0) := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  funext ω
  rw [eq_div_iff hq.ne', mul_comm, mul_mainTerm_eq_coinSum hP h01 h11 (F ω) hT]
  congr 1
  funext p
  exact hM.pathCoin_eq ω p

/-- Variance of the main term in a path-coin model. -/
theorem IsPathCoinModel.variance_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    Var[fun ω ↦ mainTerm P (F ω) T; μ] =
      Var[coinSum (chainThresh P) (chainIdx P T) K; shiftMeasure 2] / (P 0 1 + P 1 0) ^ 2 := by
  rw [hM.mainTerm_eq hP h01 h11 hT]
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const, hM.measurePreserving.variance_fun_comp
    (memLp_coinSum (chainThresh_mem hP h01 h11) _ K).aestronglyMeasurable.aemeasurable, inv_pow]

/-- The main term has mean zero in a path-coin model. -/
theorem IsPathCoinModel.integral_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    ∫ ω, mainTerm P (F ω) T ∂μ = 0 := by
  have h := congrFun (hM.mainTerm_eq hP h01 h11 hT)
  simp_rw [h]
  rw [integral_div, ← integral_map hM.measurePreserving.aemeasurable, hM.measurePreserving.map_eq,
    integral_coinSum (chainThresh_mem hP h01 h11), zero_div]
  rw [hM.measurePreserving.map_eq]
  exact (memLp_coinSum (chainThresh_mem hP h01 h11) _ K).aestronglyMeasurable

/-- The main term is in `L²` in a path-coin model. -/
theorem IsPathCoinModel.memLp_mainTerm (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (h01 : 0 < P 0 1) (h11 : 0 < P 1 1) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    MemLp (fun ω ↦ mainTerm P (F ω) T) 2 μ := by
  rw [hM.mainTerm_eq hP h01 h11 hT]
  simp_rw [div_eq_mul_inv]
  exact ((memLp_coinSum (chainThresh_mem hP h01 h11) _ K).comp_measurePreserving
    hM.measurePreserving).mul_const _

/-- The occupation error is measurable and bounded, hence in `L²`. -/
theorem IsPathCoinModel.memLp_occErr (hM : IsPathCoinModel P μ F Ψ) [IsFiniteMeasure μ]
    (hP : IsStochastic P) (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2) (T : ℕ) :
    MemLp (fun ω ↦ occErr P x₀ (F ω) T) 2 μ := by
  have hm : Measurable fun ω ↦ occErr P x₀ (F ω) T := by
    unfold occErr
    exact ((measurable_from_nat (f := fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_occCount_of (V := fun ω ↦ scrambledStack (F ω)) hM.measurable_stack P x₀ 0
        T)).sub measurable_const
  refine MemLp.of_bound hm.aestronglyMeasurable (2 * T) (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, occErr]
  have h1 : (occCount (stackPath P x₀ (scrambledStack (F ω))) 0 T : ℝ) ≤ T := by
    exact_mod_cast occCount_le (stackPath P x₀ (scrambledStack (F ω))) 0 T
  have hz0 : 0 ≤ piZero P := div_nonneg (hP.nonneg 1 0) hq.le
  have hz1 : piZero P ≤ 1 := by
    rw [piZero, div_le_one hq]
    linarith [hP.nonneg 0 1]
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  rw [abs_le]
  constructor <;> nlinarith [(Nat.cast_nonneg (occCount (stackPath P x₀ (scrambledStack (F ω))) 0
    T) : (0 : ℝ) ≤ _)]

/-- **Variance of the occupation error vs the main term.** -/
theorem IsPathCoinModel.abs_sqrt_variance_occErr_sub_le (hM : IsPathCoinModel P μ F Ψ)
    [IsProbabilityMeasure μ] (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {T K : ℕ} (hT : ∀ i, chainIdx P T i < 2 ^ K) :
    |√Var[fun ω ↦ mainTerm P (F ω) T; μ] - √Var[fun ω ↦ occErr P x₀ (F ω) T; μ]| ≤
      anscBound P T := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  refine (abs_sqrt_variance_sub_le (hM.memLp_occErr hP hq x₀ T)
    (hM.memLp_mainTerm hP h01 h11 hT)).trans ?_
  have hb : 0 ≤ anscBound P T := (abs_nonneg _).trans
    (abs_occErr_sub_mainTerm_le hP hq x₀ (F (Classical.arbitrary Ω)) T)
  refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -anscBound P T) (b := anscBound P T)
    (Eventually.of_forall fun ω ↦ abs_le.1 (abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) T))
    ((hM.memLp_occErr hP hq x₀ T).sub
      (hM.memLp_mainTerm hP h01 h11 hT)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
  rw [show (anscBound P T - -anscBound P T) / 2 = anscBound P T by ring, Real.sqrt_sq hb]

/-! ### The example `p₁₁ = p₂₂ = 2/3` along `T_k = 2 Σ_{a<k} 16^a` -/

/-- The symmetric two-state chain with stay probability `2/3`. -/
noncomputable def exampleChain : Fin 2 → Fin 2 → ℝ := fun i j ↦ if i = j then 2 / 3 else 1 / 3

theorem isStochastic_exampleChain : IsStochastic exampleChain where
  nonneg i j := by unfold exampleChain; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [exampleChain] <;> norm_num

theorem exampleChain_01 : exampleChain 0 1 = 1 / 3 := by simp [exampleChain]
theorem exampleChain_10 : exampleChain 1 0 = 1 / 3 := by simp [exampleChain]
theorem exampleChain_11 : exampleChain 1 1 = 2 / 3 := by simp [exampleChain]
theorem exampleChain_00 : exampleChain 0 0 = 2 / 3 := by simp [exampleChain]

/-- The times `T_k = 2 Σ_{a<k} 16^a` (so that `T_k/2` has binary digits `0001` repeated). -/
def exampleTime (k : ℕ) : ℕ := 2 * patternN k

theorem chainIdx_exampleTime (k : ℕ) :
    chainIdx exampleChain (exampleTime k) = fun _ ↦ patternN k := by
  have hz : piZero exampleChain = 1 / 2 := by
    rw [piZero, exampleChain_01, exampleChain_10]
    norm_num
  have ho : piOne exampleChain = 1 / 2 := by
    rw [piOne, exampleChain_01, exampleChain_10]
    norm_num
  have h : ⌊((exampleTime k : ℕ) : ℝ) * (1 / 2)⌋₊ = patternN k := by
    rw [exampleTime]
    push_cast
    rw [show (2 : ℝ) * patternN k * (1 / 2) = patternN k by ring, Nat.floor_natCast]
  funext i
  unfold chainIdx
  split_ifs
  · rw [hz, h]
  · rw [ho, h]

theorem fracPow_exampleChain_mem (i : Fin 2) (m : ℕ) :
    fracPow (chainThresh exampleChain i) m ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  fin_cases i
  · change fracPow (exampleChain 0 0) m ∈ _
    rw [exampleChain_00]
    exact fracPow_two_thirds_mem m
  · change fracPow (exampleChain 1 0) m ∈ _
    rw [exampleChain_10]
    exact fracPow_one_third_mem m

/-- **The main term's variance grows linearly in `k`** for the example chain, for every
path-coin model (Owen's scramble and the digital shift): `Var ≥ 2k/5`. -/
theorem IsPathCoinModel.variance_mainTerm_example_ge (hM : IsPathCoinModel exampleChain μ F Ψ)
    (k : ℕ) : 2 * k / 5 ≤ Var[fun ω ↦ mainTerm exampleChain (F ω) (exampleTime k); μ] := by
  have hT : ∀ i, chainIdx exampleChain (exampleTime k) i < 2 ^ (4 * k) := fun i ↦ by
    rw [chainIdx_exampleTime]
    exact patternN_lt k
  rw [hM.variance_mainTerm isStochastic_exampleChain (by rw [exampleChain_01]; norm_num)
    (by rw [exampleChain_11]; norm_num) hT, chainIdx_exampleTime, exampleChain_01,
    exampleChain_10]
  have h := variance_coinSum_pattern_ge (chainThresh_mem isStochastic_exampleChain
    (by rw [exampleChain_01]; norm_num) (by rw [exampleChain_11]; norm_num))
    fracPow_exampleChain_mem k
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- The Anscombe bound along `T_k` is `O(log k)`. -/
theorem anscBound_exampleTime_le {k : ℕ} (hk : 1 ≤ k) :
    anscBound exampleChain (exampleTime k) ≤ 41 * ((Nat.log 2 k : ℝ) + 1) := by
  have hA : anscConst exampleChain ≤ 6 := by
    rw [anscConst, exampleChain_01, exampleChain_10]
    have : ⌈(3 : ℝ) / (1 / 3 + 1 / 3)⌉₊ ≤ 5 := Nat.ceil_le.2 (by norm_num)
    omega
  have hT : Nat.log 2 (exampleTime k) ≤ 4 * k := by
    have h1 : exampleTime k < 2 ^ (4 * k + 1) := by
      rw [exampleTime, pow_succ]
      have := patternN_lt k
      omega
    rcases Nat.eq_zero_or_pos (exampleTime k) with h0 | hpos
    · rw [h0, Nat.log_zero_right]
      omega
    · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' h1)
  have hprod : anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1) ≤ 2 ^ 5 * k := by
    have := Nat.mul_le_mul hA (Nat.add_le_add_right hT 1)
    omega
  have hlog : Nat.log 2 (anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1)) ≤
      Nat.log 2 k + 5 := by
    refine (Nat.log_mono_right hprod).trans (Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow
      (by positivity) ?_))
    have := Nat.lt_pow_succ_log_self one_lt_two k
    rw [Nat.succ_eq_add_one] at this ⊢
    rw [show Nat.log 2 k + 5 + 1 = 5 + (Nat.log 2 k + 1) by ring, pow_add]
    exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
  have hlog' : (Nat.log 2 (anscConst exampleChain * (Nat.log 2 (exampleTime k) + 1)) : ℝ) ≤
      Nat.log 2 k + 5 := by exact_mod_cast hlog
  rw [anscBound, exampleChain_01, exampleChain_10, div_le_iff₀ (by norm_num)]
  have := (Nat.log 2 k).cast_nonneg (α := ℝ)
  nlinarith

/-- **The variance of the occupation error grows like `log T`** (example chain, every
path-coin model, so Owen-scrambled and digitally shifted stacks):
eventually `Var(N₀(T_k) − T_k/2) ≥ k/12`, and `log₂ T_k ≤ 4k + 1`. -/
theorem IsPathCoinModel.eventually_variance_occErr_example_ge [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2) :
    ∀ᶠ k : ℕ in atTop,
      (k : ℝ) / 12 ≤ Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
  have hlim := tendsto_natLog_pow_six_div
  have hev : ∀ᶠ k : ℕ in atTop, ((Nat.log 2 k : ℝ) + 1) ^ 6 / k ≤ 1 / (16 * 41 ^ 2) :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hT : ∀ i, chainIdx exampleChain (exampleTime k) i < 2 ^ (4 * k) := fun i ↦ by
    rw [chainIdx_exampleTime]
    exact patternN_lt k
  have hd := hM.abs_sqrt_variance_occErr_sub_le isStochastic_exampleChain
    (by rw [exampleChain_01]; norm_num) (by rw [exampleChain_11]; norm_num) x₀ hT
  have hmain := hM.variance_mainTerm_example_ge k
  have hb := anscBound_exampleTime_le hk1
  set b := anscBound exampleChain (exampleTime k) with hbdef
  set L := (Nat.log 2 k : ℝ) + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [(Nat.log 2 k).cast_nonneg (α := ℝ)]
  -- `b ≤ √k / 4`
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hd.trans le_rfl) |>.trans le_rfl
  have hL6 : L ^ 6 ≤ k / (16 * 41 ^ 2) := by
    rw [div_le_iff₀ hk0] at hk
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hL2 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hbk : b ^ 2 ≤ k / 16 := by
    have h1 : b ^ 2 ≤ (41 * L) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    nlinarith
  have hsk := Real.sq_sqrt hk0.le
  have hbs : b ≤ √k / 4 := by
    rw [← Real.sqrt_sq hb0, show √(k : ℝ) / 4 = √(k / 16) by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hbk
  -- `√Var(main) ≥ 3√k/5`
  have hsm : 3 * √k / 5 ≤ √Var[fun ω ↦ mainTerm exampleChain (F ω) (exampleTime k); μ] := by
    have : 3 * √(k : ℝ) / 5 = √(9 * k / 25) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 25), Real.sqrt_mul (by norm_num),
        show (9 : ℝ) = 3 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hso : 7 * √k / 20 ≤ √Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
    have := (abs_le.1 hd).2
    linarith
  have hs0 : 0 ≤ 7 * √(k : ℝ) / 20 := by positivity
  have := pow_le_pow_left₀ hs0 hso 2
  rw [Real.sq_sqrt (variance_nonneg _ _), div_pow, mul_pow, hsk] at this
  linarith

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The CLT for two-state chains driven by scrambled van der Corput stacks (post #3)

Post #3, codes (ii) (one Sobol sequence per state, random digital shift) and (iii) (Owen
scrambling), two-state chain: "in the five-state chain normality cannot be rejected for the
per-state Sobol sequences ((ii) and (iii))", while "as in the i.i.d. case, the RQMC estimators
are typically not normally distributed".

**Reading.** We prove a central limit theorem along time sequences whose variance grows like
`log T`, for both randomisations at once (any `IsPathCoinModel`):

  if `T_k → ∞` and `Var(N₀(T_k) − T_k π₀) ≥ κ log₂ T_k` eventually, then
  `(N₀(T_k) − T_k π₀) / √Var ⇒ N(0,1)`.

The proof: the error is `(D₀(⌊T π₀⌋) + D₁(⌊T π₁⌋))/q + O(log log T)` for every flip table
(`CltAnscombe`); the main term is a sum over binary levels of bounded functions of i.i.d. fair
path coins with geometrically decaying dependence (`CltPathBits`, `CltVariance`); the truncation
CLT (`CltMDependent`) gives its normality; Slutsky's theorem removes the `O(log log T)`.

The hypothesis is not vacuous: for `p₁₁ = p₂₂ = 2/3` and `T_k = 2 Σ_{a<k} 16^a` the variance is
`≥ k/12` (`CltVariance`), so `occErr_example_tendstoInDistribution` holds.

**Correction** (with `StackDyadic` and `StackPowerOfTwo`). (ii)/(iii) are not
asymptotically normal along all `T`: the CLT holds at the scale `√log T` along times with
`Var ≥ κ log T`; for non-dyadic chains the variance stays bounded along `T = 2^k`. And unlike the
i.i.d. case of post #2 (where the digital shift is not normal), for two-state Markov stacks the
digital shift and Owen's scramble give path coins with the same law (`map_owenPathCoins`),
hence main terms with the same law, and both are normal along such times.

**RMSE.** `E[(N₀(T) − T π₀)²] = O(log T)`, so the occupation frequency has RMSE
`O(√log T / T)` (`IsPathCoinModel.integral_sq_occErr_le`,
`IsPathCoinModel.isBigO_meanSq_occFreq`), against `O(1/√T)` for MC.

**Hypotheses added.** `p₀₁ > 0` and `p₁₁ > 0` (the thresholds `p₀₀`, `p₁₀` lie in `[0,1)`, where
their binary digits are defined; `p₀₁ > 0` also gives `q > 0`). The variance hypothesis is stated
along the given times (`∀ᶠ k`), as the CLT is about such subsequences.

## Main results

* `TendstoInDistribution.comp_measurePreserving`, `TendstoInDistribution.of_map_eq`:
  convergence in distribution only depends on laws.
* `tendstoInDistribution_coinSum`: the CLT for the coin sums on the fair-coin space.
* `tendstoInDistribution_of_abs_sub_le`: Slutsky's theorem for a bounded perturbation
  `b_k = o(σ_k)`; `anscBound_le_log`, `tendsto_anscBound_sq_div`: `anscBound(T)² = o(log T)`.
* `IsPathCoinModel.tendstoInDistribution_occErr` (**main theorem**), with
  `tendstoInDistribution_occErr_owen` (code (iii)) and `tendstoInDistribution_occErr_shift`
  (code (ii)).
* `chainSumErr`, `chainSumErr_eq` (`E_T(g) = (g 0 − g 1)(N₀(T) − T π₀)`) and
  `IsPathCoinModel.tendstoInDistribution_chainSumErr`: the CLT for every `g` with `g 0 ≠ g 1`.
* `occErr_example_tendstoInDistribution` (+ `_owen`, `_shift`): the CLT on the concrete
  sequence of `CltVariance` (the hypothesis holds: `IsPathCoinModel.eventually_variance_example`).
* `IsPathCoinModel.integral_sq_occErr_le`, `IsPathCoinModel.isBigO_meanSq_occFreq`: RMSE.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-- **Convergence in distribution depends only on laws**: it transfers through a
measure-preserving map. -/
theorem TendstoInDistribution.comp_measurePreserving {Ω Ω'' Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω''] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω''}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ψ : Ω → Ω''} (hΨ : MeasurePreserving Ψ μ ν) {G : ℕ → Ω'' → ℝ}
    {Z : Ω' → ℝ} (h : TendstoInDistribution G atTop Z (fun _ ↦ ν) P') :
    TendstoInDistribution (fun k ω ↦ G k (Ψ ω)) atTop Z (fun _ ↦ μ) P' where
  forall_aemeasurable k := by
    have h1 := h.forall_aemeasurable k
    rw [← hΨ.map_eq] at h1
    exact h1.comp_aemeasurable hΨ.aemeasurable
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    have e : ∀ k, μ.map (fun ω ↦ G k (Ψ ω)) = ν.map (G k) := fun k ↦ by
      have h1 := h.forall_aemeasurable k
      rw [← hΨ.map_eq] at h1 ⊢
      rw [AEMeasurable.map_map_of_aemeasurable h1 hΨ.aemeasurable]
      rfl
    exact Tendsto.congr (fun k ↦ Subtype.ext (e k).symm) h.tendsto

/-- **The CLT on the coin space.** For thresholds in `[0,1)`, indices `n k`, and `K k → ∞`
levels, if `Var(coin sum) ≥ κ K k` eventually, the normalised coin sums are asymptotically
`N(0,1)`. (`tendstoInDistribution_of_truncations` with `B = 2`, `C = 4`.) -/
theorem tendstoInDistribution_coinSum {c : Fin 2 → ℝ} (hc : ∀ i, 0 ≤ c i ∧ c i < 1)
    {n : ℕ → Fin 2 → ℕ} {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * K k ≤ Var[coinSum c (n k) (K k); shiftMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k w ↦ coinSum c (n k) (K k) w /
      √Var[coinSum c (n k) (K k); shiftMeasure 2]) atTop Z (fun _ ↦ shiftMeasure 2) P' := by
  set Y : ℕ → ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k m w ↦
    ∑ i, coinTerm (c i) (n k i) m (stateCoins w i) with hY
  set Yt : ℕ → ℕ → ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k m L w ↦
    ∑ i, coinTermTrunc (c i) (n k i) m L (stateCoins w i) with hYt
  have h := tendstoInDistribution_of_truncations (fun _ : Fin 2 × ℕ ↦ fairCoin) Prod.snd hK
    (Y := Y) (Yt := Yt) (B := 2) (C := 4)
    (fun k m ↦ Finset.measurable_fun_sum _ fun i _ ↦ measurable_coinTerm (hc i).1 (hc i).2 _ _ i)
    (fun k m w ↦ ?_) (fun k m L w ↦ ?_) (fun k m L ↦ ?_) (fun k m L ↦ ?_) hκ hvar hZ
  · have e : (fun k w ↦ coinSum c (n k) (K k) w /
        √Var[coinSum c (n k) (K k); shiftMeasure 2]) =
        fun k w ↦ ((∑ m ∈ range (K k), Y k m w) -
          (shiftMeasure 2)[fun ω ↦ ∑ m ∈ range (K k), Y k m ω]) /
          √Var[fun ω ↦ ∑ m ∈ range (K k), Y k m ω; shiftMeasure 2] := by
      funext k w
      have h0 := integral_coinSum hc (n k) (K k)
      change coinSum c (n k) (K k) w / √Var[coinSum c (n k) (K k); shiftMeasure 2] =
        (coinSum c (n k) (K k) w - ∫ ω, coinSum c (n k) (K k) ω ∂(shiftMeasure 2)) /
          √Var[coinSum c (n k) (K k); shiftMeasure 2]
      rw [h0, sub_zero]
    rw [e]
    exact h
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Fin.sum_univ_two]
    linarith [abs_coinTerm_le (hc 0).1 (n k 0) m (stateCoins w 0),
      abs_coinTerm_le (hc 1).1 (n k 1) m (stateCoins w 1)]
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Fin.sum_univ_two]
    linarith [abs_coinTermTrunc_le (hc 0).1 (n k 0) m L (stateCoins w 0),
      abs_coinTermTrunc_le (hc 1).1 (n k 1) m L (stateCoins w 1)]
  · refine ⟨(univ : Finset (Fin 2)) ×ˢ Finset.Ico m (m + L), fun q hq ↦ ?_, ?_⟩
    · simp only [mem_product, mem_univ, Finset.mem_Ico, true_and] at hq
      exact hq
    · exact isLocal_sum _ fun i _ ↦ (isLocal_coinTermTrunc (c i) (n k i) m L i).mono
        (product_subset_product (subset_univ _) subset_rfl)
  · have h0 := integral_sq_coinTerm_sub_trunc_le (hc 0).1 (hc 0).2 (n k 0) m L 0
    have h1 := integral_sq_coinTerm_sub_trunc_le (hc 1).1 (hc 1).2 (n k 1) m L 1
    set d0 := fun w : Fin 2 × ℕ → Bool ↦
      coinTerm (c 0) (n k 0) m (stateCoins w 0) - coinTermTrunc (c 0) (n k 0) m L (stateCoins w 0)
    set d1 := fun w : Fin 2 × ℕ → Bool ↦
      coinTerm (c 1) (n k 1) m (stateCoins w 1) - coinTermTrunc (c 1) (n k 1) m L (stateCoins w 1)
    have hd0 : MemLp d0 2 (shiftMeasure 2) :=
      (memLp_coinTerm (hc 0).1 (hc 0).2 _ m 0).sub (memLp_coinTermTrunc (hc 0).1 _ m L 0)
    have hd1 : MemLp d1 2 (shiftMeasure 2) :=
      (memLp_coinTerm (hc 1).1 (hc 1).2 _ m 1).sub (memLp_coinTermTrunc (hc 1).1 _ m L 1)
    have hpt : ∀ w, (Y k m w - Yt k m L w) ^ 2 ≤ 2 * d0 w ^ 2 + 2 * d1 w ^ 2 := by
      intro w
      have e : Y k m w - Yt k m L w = d0 w + d1 w := by
        simp only [hY, hYt, Fin.sum_univ_two, d0, d1]
        ring
      rw [e]
      nlinarith [sq_nonneg (d0 w - d1 w)]
    have hint : Integrable (fun w ↦ (Y k m w - Yt k m L w) ^ 2) (shiftMeasure 2) := by
      have e : (fun w ↦ (Y k m w - Yt k m L w) ^ 2) = fun w ↦ (d0 w + d1 w) ^ 2 := by
        funext w
        simp only [hY, hYt, Fin.sum_univ_two, d0, d1]
        ring
      rw [e]
      exact (hd0.add hd1).integrable_sq
    calc ∫ w, (Y k m w - Yt k m L w) ^ 2 ∂(shiftMeasure 2)
        ≤ ∫ w, (2 * d0 w ^ 2 + 2 * d1 w ^ 2) ∂(shiftMeasure 2) :=
          integral_mono hint ((hd0.integrable_sq.const_mul 2).add (hd1.integrable_sq.const_mul 2))
            hpt
      _ = 2 * ∫ w, d0 w ^ 2 ∂(shiftMeasure 2) + 2 * ∫ w, d1 w ^ 2 ∂(shiftMeasure 2) := by
          rw [integral_add (hd0.integrable_sq.const_mul 2) (hd1.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 4 * (1 / 2) ^ L := by linarith

/-- **Slutsky for a bounded perturbation.** If `|E k − M k| ≤ b k` with `b k² = o(Var E k)`,
`M k` centred, and `M k / √Var(M k) ⇒ Z`, then `E k / √Var(E k) ⇒ Z`. -/
theorem tendstoInDistribution_of_abs_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {b : ℕ → ℝ}
    (hE : ∀ k, MemLp (E k) 2 μ) (hM : ∀ k, MemLp (M k) 2 μ) (hM0 : ∀ k, μ[M k] = 0)
    (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k)
    (hb : Tendsto (fun k ↦ b k ^ 2 / Var[E k; μ]) atTop (𝓝 0))
    (hpos : ∀ᶠ k in atTop, 0 < Var[E k; μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hlim : TendstoInDistribution (fun k ω ↦ M k ω / √Var[M k; μ]) atTop Z (fun _ ↦ μ) P') :
    TendstoInDistribution (fun k ω ↦ E k ω / √Var[E k; μ]) atTop Z (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  -- the standard deviations are close
  have hσ : ∀ k, |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    intro k
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  -- eventually `b ≤ σ_E / 2`
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / Var[E k; μ] ≤ 1 / 4 :=
    hb.eventually (ge_mem_nhds (by norm_num))
  set D : ℕ → Ω → ℝ := fun k ω ↦ E k ω / √Var[E k; μ] - M k ω / √Var[M k; μ] with hD
  have hDm : ∀ k, MemLp (D k) 2 μ := fun k ↦ by
    simp_rw [hD, div_eq_mul_inv]
    exact ((hE k).mul_const _).sub ((hM k).mul_const _)
  have hbound : ∀ᶠ k in atTop, ∫ ω, D k ω ^ 2 ∂μ ≤ 4 * (b k ^ 2 / Var[E k; μ]) := by
    filter_upwards [hpos, hsmall] with k hk hs
    set sE := √Var[E k; μ] with hsE
    set sM := √Var[M k; μ] with hsM
    have hsE0 : 0 < sE := Real.sqrt_pos.2 hk
    have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt hk.le
    have hbE : b k ≤ sE / 2 := by
      rw [div_le_iff₀ hk, ← hsE2] at hs
      nlinarith [hb0 k]
    have hsM0 : 0 < sM := by
      have := (abs_le.1 (hσ k)).1
      linarith
    have hMvar : ∫ ω, M k ω ^ 2 ∂μ = sM ^ 2 := by
      rw [hsM, Real.sq_sqrt (variance_nonneg _ _),
        variance_of_integral_eq_zero (hM k).aestronglyMeasurable.aemeasurable (hM0 k)]
    have hpt : ∀ ω, D k ω ^ 2 ≤ 2 * ((E k ω - M k ω) / sE) ^ 2 +
        2 * ((sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2) := by
      intro ω
      have e : D k ω = (E k ω - M k ω) / sE + M k ω * (sE⁻¹ - sM⁻¹) := by
        simp only [hD]
        rw [← hsE, ← hsM]
        field_simp
        ring
      rw [e]
      nlinarith [sq_nonneg ((E k ω - M k ω) / sE - M k ω * (sE⁻¹ - sM⁻¹))]
    have hpt1 : ∀ ω, ((E k ω - M k ω) / sE) ^ 2 ≤ b k ^ 2 / sE ^ 2 := fun ω ↦ by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hclose k ω) 2) (by positivity)
    have hi1 : Integrable (fun ω ↦ ((E k ω - M k ω) / sE) ^ 2) μ := by
      simp_rw [div_eq_mul_inv]
      exact (((hE k).sub (hM k)).mul_const _).integrable_sq
    have hi2 : Integrable (fun ω ↦ (sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2) μ :=
      (hM k).integrable_sq.const_mul _
    calc ∫ ω, D k ω ^ 2 ∂μ
        ≤ ∫ ω, (2 * ((E k ω - M k ω) / sE) ^ 2 + 2 * ((sE⁻¹ - sM⁻¹) ^ 2 * M k ω ^ 2)) ∂μ :=
          integral_mono (hDm k).integrable_sq ((hi1.const_mul 2).add (hi2.const_mul 2)) hpt
      _ = 2 * ∫ ω, ((E k ω - M k ω) / sE) ^ 2 ∂μ + 2 * ((sE⁻¹ - sM⁻¹) ^ 2 * sM ^ 2) := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul, integral_const_mul, hMvar]
      _ ≤ 2 * (b k ^ 2 / sE ^ 2) + 2 * (b k ^ 2 / sE ^ 2) := by
          gcongr
          · have := integral_mono hi1 (integrable_const (b k ^ 2 / sE ^ 2)) hpt1
            rwa [integral_const, probReal_univ, one_smul] at this
          · have e : (sE⁻¹ - sM⁻¹) ^ 2 * sM ^ 2 = ((sM - sE) / sE) ^ 2 := by
              field_simp
            rw [e, div_pow]
            exact div_le_div_of_nonneg_right (by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hσ k) 2) (by positivity)
      _ = 4 * (b k ^ 2 / Var[E k; μ]) := by rw [hsE2]; ring
  have hlimD : Tendsto (fun k ↦ ∫ ω, D k ω ^ 2 ∂μ) atTop (𝓝 0) := by
    have h4 := hb.const_mul 4
    rw [mul_zero] at h4
    exact squeeze_zero' (Eventually.of_forall fun k ↦ integral_nonneg fun ω ↦ sq_nonneg _)
      hbound h4
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hlim ?_ fun k ↦
    ((hE k).aestronglyMeasurable.aemeasurable).div_const _
  exact tendstoInMeasure_of_integral_sq hDm hlimD

/-- The Anscombe bound is `O(log log T)`: `anscBound P T ≤ C (⌊log₂(⌊log₂ T⌋ + 1)⌋ + 1)`. -/
theorem anscBound_le_log {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) (T : ℕ) :
    anscBound P T ≤ (11 + 4 * (Nat.log 2 (anscConst P) : ℝ)) / (P 0 1 + P 1 0) *
      ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hA : 1 ≤ anscConst P := by rw [anscConst]; omega
  have hmul : Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) ≤
      Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    refine Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by positivity) ?_)
    have h1 := Nat.lt_pow_succ_log_self one_lt_two (anscConst P)
    have h2 := Nat.lt_pow_succ_log_self one_lt_two (Nat.log 2 T + 1)
    rw [Nat.succ_eq_add_one] at h1 h2 ⊢
    rw [show Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 + 1 =
      (Nat.log 2 (anscConst P) + 1) + (Nat.log 2 (Nat.log 2 T + 1) + 1) by ring, pow_add]
    exact Nat.mul_lt_mul'' h1 h2
  have hmul' : (Nat.log 2 (anscConst P * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConst P) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by exact_mod_cast hmul
  rw [anscBound, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq]
  have h0 := (Nat.log 2 (anscConst P)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  nlinarith

/-- `anscBound(T_k)² / log₂ T_k → 0` along `T_k → ∞`. -/
theorem tendsto_anscBound_sq_div {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) {T : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) :
    Tendsto (fun k ↦ anscBound P (T k) ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0) := by
  set C := (11 + 4 * (Nat.log 2 (anscConst P) : ℝ)) / (P 0 1 + P 1 0) with hC
  have hC0 : 0 ≤ C := by positivity
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hx : Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlim := (tendsto_natLog_pow_six_div.comp hx).const_mul (2 * C ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hlim
  have hev : ∀ᶠ k in atTop, 2 ≤ Nat.log 2 (T k) + 1 := hx.eventually_ge_atTop 2
  filter_upwards [hev] with k hk
  have hb0 : 0 ≤ anscBound P (T k) := by
    rw [anscBound]
    positivity
  have hb := anscBound_le_log hq (T k)
  set y := (Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1 with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [(Nat.log 2 (Nat.log 2 (T k) + 1)).cast_nonneg (α := ℝ)]
  have hlog : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast (show 1 ≤ Nat.log 2 (T k) by omega)
  have hx2 : ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ 2 * Nat.log 2 (T k) := by push_cast; linarith
  have hy6 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have hb2 : anscBound P (T k) ^ 2 ≤ C ^ 2 * y ^ 6 := by
    have := pow_le_pow_left₀ hb0 hb 2
    rw [mul_pow] at this
    nlinarith
  simp only [Function.comp_apply]
  rw [div_le_iff₀ (by linarith), ← hy]
  have hpos : (0 : ℝ) < ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) := by positivity
  calc anscBound P (T k) ^ 2 ≤ C ^ 2 * y ^ 6 := hb2
    _ = 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) *
        (((Nat.log 2 (T k) + 1 : ℕ) : ℝ) / 2) := by field_simp
    _ ≤ 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) * Nat.log 2 (T k) := by
        gcongr
        linarith

/-- `n_i(T) < 2^{⌊log₂ T⌋ + 1}`. -/
theorem chainIdx_lt_two_pow {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P)
    (hq : 0 < P 0 1 + P 1 0) (T : ℕ) (i : Fin 2) : chainIdx P T i < 2 ^ (Nat.log 2 T + 1) :=
  lt_of_le_of_lt (chainIdx_le hP hq T i) (Nat.lt_pow_succ_log_self one_lt_two T)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- **The CLT for two-state scrambled-stack chains** (any path-coin model, in particular Owen's
scramble and the digital shift). Let `p₀₁, p₁₁ > 0` and `T_k → ∞` with
`Var(N₀(T_k) − T_k π₀) ≥ κ log₂ T_k` eventually. Then
`(N₀(T_k) − T_k π₀) / √Var(N₀(T_k) − T_k π₀) ⇒ N(0,1)`. -/
theorem IsPathCoinModel.tendstoInDistribution_occErr [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (F ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) atTop Z (fun _ ↦ μ) P' := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  set q := P 0 1 + P 1 0 with hqdef
  set K : ℕ → ℕ := fun k ↦ Nat.log 2 (T k) + 1 with hK
  have hTK : ∀ k i, chainIdx P (T k) i < 2 ^ K k := fun k i ↦ chainIdx_lt_two_pow hP hq (T k) i
  set X : ℕ → (Fin 2 × ℕ → Bool) → ℝ := fun k ↦
    coinSum (chainThresh P) (chainIdx P (T k)) (K k) with hX
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hKt : Tendsto K atTop atTop := tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlog1 : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (T k) := hlogT.eventually_ge_atTop 1
  have hb := tendsto_anscBound_sq_div hq hT
  -- `b² / Var E → 0`
  have hbE : Tendsto (fun k ↦ anscBound P (T k) ^ 2 /
      Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) atTop (𝓝 0) := by
    have h := hb.div_const κ
    rw [zero_div] at h
    refine squeeze_zero' (Eventually.of_forall fun k ↦ by
      have := variance_nonneg (fun ω ↦ occErr P x₀ (F ω) (T k)) μ
      positivity) ?_ h
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (0 : ℝ) < Nat.log 2 (T k) := by exact_mod_cast hl
    rw [div_div, mul_comm (Nat.log 2 (T k) : ℝ) κ]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk
  have hpos : ∀ᶠ k in atTop, 0 < Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    nlinarith
  refine tendstoInDistribution_of_abs_sub_le (b := fun k ↦ anscBound P (T k))
    (fun k ↦ hM.memLp_occErr hP hq x₀ (T k)) (fun k ↦ hM.memLp_mainTerm hP h01 h11 (hTK k))
    (fun k ↦ hM.integral_mainTerm hP h01 h11 (hTK k))
    (fun k ω ↦ abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) (T k)) hbE hpos ?_
  -- the main term is asymptotically normal
  have hvarX : ∀ᶠ k in atTop, q ^ 2 * κ / 8 * K k ≤ Var[X k; shiftMeasure 2] := by
    have hsmall : ∀ᶠ k in atTop, anscBound P (T k) ^ 2 /
        Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] ≤ 1 / 4 :=
      hbE.eventually (ge_mem_nhds (by norm_num))
    filter_upwards [hvar, hlog1, hsmall, hpos] with k hk hl hs hp
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    have hσ := hM.abs_sqrt_variance_occErr_sub_le hP h01 h11 x₀ (hTK k)
    set sE := √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] with hsE
    set sM := √Var[fun ω ↦ mainTerm P (F ω) (T k); μ] with hsM
    have hsE2 : sE ^ 2 = Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := Real.sq_sqrt hp.le
    have hb0 : 0 ≤ anscBound P (T k) := by rw [anscBound]; positivity
    have hbsE : anscBound P (T k) ≤ sE / 2 := by
      rw [div_le_iff₀ hp, ← hsE2] at hs
      have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
      by_contra hc
      push Not at hc
      nlinarith
    have hsMge : sE / 2 ≤ sM := by
      have := (abs_le.1 hσ).1
      linarith
    have hsE0 : 0 ≤ sE / 2 := by positivity
    have hVM : sE ^ 2 / 4 ≤ Var[fun ω ↦ mainTerm P (F ω) (T k); μ] := by
      have := pow_le_pow_left₀ hsE0 hsMge 2
      rw [hsM, Real.sq_sqrt (variance_nonneg _ _), div_pow] at this
      linarith
    have hVX := hM.variance_mainTerm hP h01 h11 (hTK k)
    rw [eq_div_iff (by positivity)] at hVX
    have hK2 : (K k : ℝ) ≤ 2 * Nat.log 2 (T k) := by
      change ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ _
      push_cast
      linarith
    change q ^ 2 * κ / 8 * K k ≤ Var[coinSum (chainThresh P) (chainIdx P (T k)) (K k);
      shiftMeasure 2]
    rw [← hVX]
    have hq2 : 0 < q ^ 2 := by positivity
    have h1 : κ * Nat.log 2 (T k) ≤ sE ^ 2 := by rw [hsE2]; exact hk
    calc q ^ 2 * κ / 8 * K k ≤ q ^ 2 * κ / 8 * (2 * Nat.log 2 (T k)) := by gcongr
      _ = q ^ 2 * (κ * Nat.log 2 (T k) / 4) := by ring
      _ ≤ q ^ 2 * (sE ^ 2 / 4) := by gcongr
      _ ≤ q ^ 2 * Var[fun ω ↦ mainTerm P (F ω) (T k); μ] := by gcongr
      _ = Var[fun ω ↦ mainTerm P (F ω) (T k); μ] * (P 0 1 + P 1 0) ^ 2 := by rw [hqdef]; ring
  have hcoin := tendstoInDistribution_coinSum (chainThresh_mem hP h01 h11)
    (n := fun k ↦ chainIdx P (T k)) hKt (by positivity : 0 < q ^ 2 * κ / 8) hvarX hZ
  have htr := TendstoInDistribution.comp_measurePreserving hM.measurePreserving hcoin
  have e : (fun k ω ↦ mainTerm P (F ω) (T k) / √Var[fun ω ↦ mainTerm P (F ω) (T k); μ]) =
      fun k ω ↦ X k (Ψ ω) / √Var[X k; shiftMeasure 2] := by
    funext k ω
    have h1 := congrFun (hM.mainTerm_eq hP h01 h11 (hTK k)) ω
    rw [h1, hM.variance_mainTerm hP h01 h11 (hTK k), Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hq.le, div_div_div_cancel_right₀ hq.ne']
  rw [e]
  exact htr

/-- **The CLT for Owen-scrambled stacks** (post #3, code (iii), two states). -/
theorem tendstoInDistribution_occErr_owen (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ}
    (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (owenTable ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2]) atTop Z
      (fun _ ↦ owenMeasure 2) P' :=
  (isPathCoinModel_owen P).tendstoInDistribution_occErr hP h01 h11 x₀ hT hκ hvar hZ

/-- **The CLT for digitally shifted stacks** (post #3, code (ii), two states). -/
theorem tendstoInDistribution_occErr_shift (hP : IsStochastic P) (h01 : 0 < P 0 1)
    (h11 : 0 < P 1 1) (x₀ : Fin 2) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ}
    (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (shiftFlips ω) (T k) /
      √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2]) atTop Z
      (fun _ ↦ shiftMeasure 2) P' :=
  (isPathCoinModel_shift P).tendstoInDistribution_occErr hP h01 h11 x₀ hT hκ hvar hZ

/-- `T_k → ∞` for the example times. -/
theorem tendsto_exampleTime : Tendsto exampleTime atTop atTop := by
  refine tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
  have h : k ≤ patternN k := by
    rw [patternN]
    calc k = ∑ _a ∈ range k, 1 := by simp
      _ ≤ ∑ a ∈ range k, 16 ^ a := sum_le_sum fun a _ ↦ Nat.one_le_pow _ _ (by norm_num)
  change k ≤ 2 * patternN k
  omega

/-- The variance hypothesis holds along the example times. -/
theorem IsPathCoinModel.eventually_variance_example [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2) :
    ∀ᶠ k in atTop, (1 / 60 : ℝ) * Nat.log 2 (exampleTime k) ≤
      Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ] := by
  filter_upwards [hM.eventually_variance_occErr_example_ge x₀, eventually_ge_atTop 1] with k hk hk1
  have hT : Nat.log 2 (exampleTime k) ≤ 4 * k := by
    have h1 : exampleTime k < 2 ^ (4 * k + 1) := by
      rw [exampleTime, pow_succ]
      have := patternN_lt k
      omega
    rcases Nat.eq_zero_or_pos (exampleTime k) with h0 | hpos
    · rw [h0, Nat.log_zero_right]
      omega
    · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' h1)
  have hT' : (Nat.log 2 (exampleTime k) : ℝ) ≤ 4 * k := by exact_mod_cast hT
  linarith

/-- **The CLT on the concrete sequence** (non-vacuity): for `p₁₁ = p₂₂ = 2/3` and
`T_k = 2 Σ_{a<k} 16^a`, the normalised occupation error of Owen-scrambled (and of digitally
shifted) stacks is asymptotically `N(0,1)`. -/
theorem occErr_example_tendstoInDistribution [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel exampleChain μ F Ψ) (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (F ω) (exampleTime k); μ]) atTop Z
      (fun _ ↦ μ) P' :=
  hM.tendstoInDistribution_occErr isStochastic_exampleChain (by rw [exampleChain_01]; norm_num)
    (by rw [exampleChain_11]; norm_num) x₀ tendsto_exampleTime (by norm_num)
    (hM.eventually_variance_example x₀) hZ

/-- The concrete CLT for Owen's scramble. -/
theorem occErr_example_tendstoInDistribution_owen (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (owenTable ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (owenTable ω) (exampleTime k); owenMeasure 2]) atTop
      Z (fun _ ↦ owenMeasure 2) P' :=
  occErr_example_tendstoInDistribution (isPathCoinModel_owen exampleChain) x₀ hZ

/-- The concrete CLT for the digital shift. -/
theorem occErr_example_tendstoInDistribution_shift (x₀ : Fin 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErr exampleChain x₀ (shiftFlips ω) (exampleTime k) /
      √Var[fun ω ↦ occErr exampleChain x₀ (shiftFlips ω) (exampleTime k); shiftMeasure 2]) atTop
      Z (fun _ ↦ shiftMeasure 2) P' :=
  occErr_example_tendstoInDistribution (isPathCoinModel_shift exampleChain) x₀ hZ

/-- **Mean-square error** (every two-state chain, every path-coin model, every `T`):
`E[(N₀(T) − T π₀)²] ≤ 10 (⌊log₂ T⌋ + 1)/q² + 2 anscBound(T)²`. -/
theorem IsPathCoinModel.integral_sq_occErr_le [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) (T : ℕ) :
    ∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ ≤
      10 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 + 2 * anscBound P T ^ 2 := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have hTK : ∀ i, chainIdx P T i < 2 ^ (Nat.log 2 T + 1) := chainIdx_lt_two_pow hP hq T
  have hE := hM.memLp_occErr hP hq x₀ T
  have hMm := hM.memLp_mainTerm hP h01 h11 hTK
  have hpt : ∀ ω, occErr P x₀ (F ω) T ^ 2 ≤
      2 * mainTerm P (F ω) T ^ 2 + 2 * anscBound P T ^ 2 := by
    intro ω
    have h := abs_occErr_sub_mainTerm_le hP hq x₀ (F ω) T
    have h2 : (occErr P x₀ (F ω) T - mainTerm P (F ω) T) ^ 2 ≤ anscBound P T ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    nlinarith [sq_nonneg (occErr P x₀ (F ω) T - 2 * mainTerm P (F ω) T)]
  have hvarM : ∫ ω, mainTerm P (F ω) T ^ 2 ∂μ ≤ 5 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 := by
    rw [← variance_of_integral_eq_zero hMm.aestronglyMeasurable.aemeasurable
      (hM.integral_mainTerm hP h01 h11 hTK), hM.variance_mainTerm hP h01 h11 hTK]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := variance_coinSum_le (chainThresh_mem hP h01 h11) (chainIdx P T) (Nat.log 2 T + 1)
    push_cast at this
    exact this
  calc ∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ
      ≤ ∫ ω, (2 * mainTerm P (F ω) T ^ 2 + 2 * anscBound P T ^ 2) ∂μ :=
        integral_mono hE.integrable_sq ((hMm.integrable_sq.const_mul 2).add (integrable_const _))
          hpt
    _ = 2 * ∫ ω, mainTerm P (F ω) T ^ 2 ∂μ + 2 * anscBound P T ^ 2 := by
        rw [integral_add (hMm.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 10 * (Nat.log 2 T + 1) / (P 0 1 + P 1 0) ^ 2 + 2 * anscBound P T ^ 2 := by
        have := hvarM
        rw [div_eq_mul_inv] at this ⊢
        nlinarith

/-- **RMSE of the occupation frequency is `O(√log T / T)`**: `E[(N₀(T)/T − π₀)²] = O(log T / T²)`
(against `1/T` for i.i.d. MC driving). -/
theorem IsPathCoinModel.isBigO_meanSq_occFreq [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) :
    (fun T : ℕ ↦ ∫ ω, (occErr P x₀ (F ω) T / T) ^ 2 ∂μ) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  have hb := tendsto_anscBound_sq_div hq (T := id) tendsto_id
  have hev : ∀ᶠ T : ℕ in atTop, anscBound P T ^ 2 / Nat.log 2 T ≤ 1 :=
    hb.eventually (ge_mem_nhds one_pos)
  have hlog : ∀ᶠ T : ℕ in atTop, 1 ≤ Nat.log 2 T :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      tendsto_id).eventually_ge_atTop 1
  refine Asymptotics.IsBigO.of_bound (20 / (P 0 1 + P 1 0) ^ 2 + 2) ?_
  filter_upwards [hev, hlog, eventually_ge_atTop 1] with T h1 h2 h3
  have hT0 : (0 : ℝ) < T := by exact_mod_cast h3
  have hl : (1 : ℝ) ≤ Nat.log 2 T := by exact_mod_cast h2
  have hbT : anscBound P T ^ 2 ≤ Nat.log 2 T := by
    rw [div_le_one (by linarith)] at h1
    exact h1
  have hsq := hM.integral_sq_occErr_le hP h01 h11 x₀ T
  have e : ∫ ω, (occErr P x₀ (F ω) T / T) ^ 2 ∂μ = (∫ ω, occErr P x₀ (F ω) T ^ 2 ∂μ) / T ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (div_nonneg
    (integral_nonneg fun ω ↦ sq_nonneg _) (by positivity)), abs_of_nonneg (by positivity),
    mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have hq2 : 0 < (P 0 1 + P 1 0) ^ 2 := by positivity
  have h10 : 10 * ((Nat.log 2 T : ℝ) + 1) / (P 0 1 + P 1 0) ^ 2 ≤
      20 / (P 0 1 + P 1 0) ^ 2 * Nat.log 2 T := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq2]
    linarith
  nlinarith

/-! ### General functions of the state -/

/-- The error `E_T(g) = Σ_{t<T} g(x_t) − T π(g)` of the time average of `g`. -/
noncomputable def chainSumErr (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (f : Fin 2 → ℕ → ℕ → Bool)
    (g : Fin 2 → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, g (stackPath P x₀ (scrambledStack f) t) - T * (piZero P * g 0 + piOne P * g 1)

/-- For two states, `E_T(g) = (g 0 − g 1) (N₀(T) − T π₀)`. -/
theorem chainSumErr_eq {P : Fin 2 → Fin 2 → ℝ} (hq : 0 < P 0 1 + P 1 0) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (g : Fin 2 → ℝ) (T : ℕ) :
    chainSumErr P x₀ f g T = (g 0 - g 1) * occErr P x₀ f T := by
  classical
  set x := stackPath P x₀ (scrambledStack f) with hx
  have hfib : ∑ t ∈ range T, g (x t) = ∑ i, (occCount x i T : ℝ) * g i := by
    rw [← sum_fiberwise_of_maps_to (s := range T) (t := univ) (g := x) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_congr rfl fun t ht ↦ by rw [(mem_filter.1 ht).2], sum_const, nsmul_eq_mul]
    rfl
  have hsum : (occCount x 0 T : ℝ) + occCount x 1 T = T := by
    have := sum_occCount x T
    rw [Fin.sum_univ_two] at this
    exact_mod_cast this
  have h1 := piZero_add_piOne hq
  rw [chainSumErr, ← hx, hfib, Fin.sum_univ_two, occErr, ← hx]
  have e1 : piOne P = 1 - piZero P := by linarith
  rw [e1, ← hsum]
  ring

/-- Convergence in distribution only depends on the law of the limit. -/
theorem TendstoInDistribution.of_map_eq {Ω'' Ω' : Type*} [MeasurableSpace Ω'']
    [MeasurableSpace Ω'] {ν : Measure Ω''} [IsProbabilityMeasure ν] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : ℕ → Ω'' → ℝ} {Z Z' : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z' (fun _ ↦ ν) P') (hZ : AEMeasurable Z P')
    (hmap : P'.map Z' = P'.map Z) : TendstoInDistribution X atTop Z (fun _ ↦ ν) P' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ
  tendsto := by
    have e : (⟨P'.map Z', inferInstance⟩ : ProbabilityMeasure ℝ) = ⟨P'.map Z, inferInstance⟩ :=
      Subtype.ext hmap
    rw [← e]
    exact h.tendsto

/-- **The CLT for any function of the state** (two states, any path-coin model). If
`g 0 ≠ g 1`, `T_k → ∞` and `Var(E_{T_k}(g)) ≥ κ log₂ T_k` eventually, then
`E_{T_k}(g) / √Var(E_{T_k}(g)) ⇒ N(0,1)`. -/
theorem IsPathCoinModel.tendstoInDistribution_chainSumErr [IsProbabilityMeasure μ]
    (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P) (h01 : 0 < P 0 1) (h11 : 0 < P 1 1)
    (x₀ : Fin 2) {g : Fin 2 → ℝ} (hg : g 0 ≠ g 1) {T : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
      √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) atTop Z (fun _ ↦ μ) P' := by
  have hq : 0 < P 0 1 + P 1 0 := by linarith [hP.nonneg 1 0]
  set c := g 0 - g 1 with hc
  have hc0 : c ≠ 0 := sub_ne_zero.2 hg
  have hc2 : 0 < c ^ 2 := by positivity
  have hE : ∀ k, (fun ω ↦ chainSumErr P x₀ (F ω) g (T k)) =
      fun ω ↦ c * occErr P x₀ (F ω) (T k) := fun k ↦ funext fun ω ↦ chainSumErr_eq hq x₀ _ g _
  have hV : ∀ k, Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ] =
      c ^ 2 * Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := fun k ↦ by
    rw [hE k, variance_const_mul]
  have hvar' : ∀ᶠ k in atTop,
      κ / c ^ 2 * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
    filter_upwards [hvar] with k hk
    rw [hV k] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hc2]
    linarith
  have hclt := hM.tendstoInDistribution_occErr hP h01 h11 x₀ hT (by positivity) hvar' hZ
  have hval : ∀ k ω, chainSumErr P x₀ (F ω) g (T k) /
      √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ] =
      c / |c| * (occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ]) := by
    intro k ω
    rw [hV k, chainSumErr_eq hq x₀ _ g _, Real.sqrt_mul hc2.le, Real.sqrt_sq_eq_abs,
      mul_div_mul_comm]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have hcc : c / |c| = -1 := by rw [abs_of_neg hneg, div_neg, div_self hc0]
    have e : (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
        √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) = fun k ↦ (fun x : ℝ ↦ -1 * x) ∘
          fun ω ↦ occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
      funext k ω
      rw [hval k ω, hcc]
      rfl
    rw [e]
    have hneg' := hclt.continuous_comp (g := fun x : ℝ ↦ -1 * x) (by fun_prop)
    refine TendstoInDistribution.of_map_eq hneg' hZ.aemeasurable ?_
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable, hZ.map_eq]
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    simp only [neg_zero] at this
    rw [← this]
    congr 1
    funext x
    ring
  · have hcc : c / |c| = 1 := by rw [abs_of_pos hpos, div_self hc0]
    have e : (fun k ω ↦ chainSumErr P x₀ (F ω) g (T k) /
        √Var[fun ω ↦ chainSumErr P x₀ (F ω) g (T k); μ]) = fun k ω ↦
          occErr P x₀ (F ω) (T k) / √Var[fun ω ↦ occErr P x₀ (F ω) (T k); μ] := by
      funext k ω
      rw [hval k ω, hcc, one_mul]
    rw [e]
    exact hclt

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two states: Owen's scramble and the digital shift give the same path law (post #3)

Post #3 treats codes (ii) (one Sobol sequence per state with a random digital shift) and (iii)
(Owen scrambling) side by side. `CltPathBits` showed that, for one threshold per row, the path
coins of Owen's scramble have the law of the digital-shift flips (`map_owenPathCoins`), so the
main term of the occupation error has the same law under both. Here the whole stack path is
shown to have the same law.

**Every decision is read off the path coins.** For every flip table `f`, every index `k` and
every threshold `c ∈ [0,1)`, `x_k ≤ c` iff the digits `bit_j(k) xor e_j` (the bits of `k`
flipped by the path coins `e_j = pathCoin f (threshDigit c) j`) are lexicographically `≤` the
digits of `c` (`scrambledVdc_le_iff_lexLeFrom_pathCoin`): while point `k` ties with `c` it sits
on the path of `c`, so its next digit is flipped by the next path coin, and after the first
disagreement nothing matters. So the comparison under `f` is the comparison under the digital
shift by the path coins (`scrambledVdc_le_iff_shiftTable`), for every real `c` (for `c < 0` and
`c ≥ 1` both sides are constant). There is no exceptional set: a point equal to `c`, and a
point whose digits are the second expansion of a dyadic `c` (`threshDigit` picks the terminating
one), are decided correctly by the lexicographic rule (`binaryVal_le_iff_lexLeFrom`).

For two states the update `step P i u` only compares `u` with `p_{i0}` and `p_{i0} + p_{i1} = 1`
(`step_congr_of_le_iff`), and a stack path only depends on the updates of its stack points
(`stackDrive_congr_of_forall`). Hence, for every flip table `f`, the path is the path of the
digitally shifted stacks with flips the path coins of `f` (`stackPath_eq_pathShift`). For any
path-coin model, in particular Owen's scramble and the digital shift, the path is
`coinPath P x₀` of the path coins (`IsPathCoinModel.stackPath_eq_coinPath`,
`stackPath_owen_eq_coinPath`), a measurable function (`measurable_coinPath`) of i.i.d. fair
coins. So the path laws on `ℕ → Fin 2` (product σ-algebra) coincide.

## Main results

* `scrambledVdc_le_iff_lexLeFrom_pathCoin`, `scrambledVdc_le_iff_shiftTable`,
  `scrambledVdc_le_congr_pathCoin`: the comparison with a threshold is a function of the path
  coins, for every flip table.
* `stackPath_eq_pathShift`: every pair of flip tables acts on a two-state chain as the digital
  shift by its path coins (every stochastic `P`, every flip table).
* `IsPathCoinModel.map_stackPath`, `map_stackPath_owen_eq_shift` (**law of the path**):
  `(owenMeasure 2).map (owen path) = (shiftMeasure 2).map (shift path)`;
  `identDistrib_stackPath_owen_shift`; `owenMeasure_stackPath_cylinder` (all cylinder
  probabilities agree).
* `identDistrib_comp_stackPath_owen_shift`: every measurable path functional has the same law;
  `measurable_occCount_path`, `measurable_transCount_path`; `identDistrib_occCount_owen_shift`,
  `identDistrib_transCount_owen_shift`.
* `identDistrib_occErr_owen_shift`, `variance_occErr_owen_eq_shift`: the occupation error has
  the same law, hence the same variance, for every `T`.
* `tendstoInDistribution_congr_identDistrib`, `tendstoInDistribution_occErr_owen_iff_shift`,
  `tendstoInDistribution_normalised_occErr_owen_iff_shift`: every limit theorem in distribution
  for the occupation error holds for Owen's scramble iff it holds for the digital shift; in
  particular the CLTs `tendstoInDistribution_occErr_owen` and `tendstoInDistribution_occErr_shift`
  are equivalent statements, with equivalent variance hypotheses.

**Hypotheses.** Only `IsStochastic P` (the positivity conditions `0 < p₀₁`, `0 < p₁₁` of
`CltStacks` are not needed here: thresholds `0` or `1` are handled directly).

**Correction** (of the "law equivalence" convention in `CltPathBits`, `CltVariance` and
`CltStacks`, which stated the same law of the main term only). For two-state chains the claim
is upgraded from "the main term has the same law under Owen's scramble and the digital shift"
to "the whole stack path has the same law", and with it the occupation error `occErr`, the
counts `occCount`, `transCount` and every measurable path functional, for every `T`. For three
states the path laws differ (`owen_ne_shift_stayThenMove`, `CltThreeState`): with two
thresholds in a row the two jump paths share digital-shift flips but use independent Owen flips
after they split.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Comparisons with a threshold through the path coins -/

/-- **Every comparison is decided along the path of the threshold** (every flip table). For
`c ∈ [0,1)`, point `k` is `≤ c` iff the bits of `k` flipped by the path coins of `c` are
lexicographically `≤` the digits of `c`. -/
theorem scrambledVdc_le_iff_lexLeFrom_pathCoin (f : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (k : ℕ) :
    scrambledVdc f k ≤ c ↔
      LexLeFrom (fun j ↦ xor (k.testBit j) (pathCoin f (threshDigit c) j)) (threshDigit c) 0 := by
  rw [scrambledVdc, binaryVal_le_iff_lexLeFrom hc0 hc1 (m := 0)
    fun i hi ↦ absurd hi (Nat.not_lt_zero i)]
  refine lexLeFrom_congr fun j _ hj ↦ ?_
  have hall : ∀ i < j, scrambledDigit f k i = threshDigit c i :=
    fun i hi ↦ hj i (Nat.zero_le i) hi
  have hkj := (tie_iff_mod_eq_pathPrefix f (threshDigit c) k j).1 hall
  rw [scrambledDigit, hkj]
  rfl

/-- **A flip table acts on one threshold as the digital shift by its path coins** (every flip
table, every real threshold). -/
theorem scrambledVdc_le_iff_shiftTable (f : ℕ → ℕ → Bool) (c : ℝ) (k : ℕ) :
    scrambledVdc f k ≤ c ↔ scrambledVdc (shiftTable (pathCoin f (threshDigit c))) k ≤ c := by
  have h1 := scrambledVdc_mem_Icc f k
  have h2 := scrambledVdc_mem_Icc (shiftTable (pathCoin f (threshDigit c))) k
  rcases lt_or_ge c 0 with hc | hc0
  · constructor <;> intro h
    · linarith [h1.1]
    · linarith [h2.1]
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [scrambledVdc_le_iff_lexLeFrom_pathCoin f hc0 hc1,
      scrambledVdc_le_iff_lexLeFrom_pathCoin _ hc0 hc1, pathCoin_shiftTable]
  · exact ⟨fun _ ↦ h2.2.trans hc1, fun _ ↦ h1.2.trans hc1⟩

/-- The comparison with a threshold is a function of the path coins: two flip tables with the
same path coins give the same comparisons, at every index. -/
theorem scrambledVdc_le_congr_pathCoin {f f' : ℕ → ℕ → Bool} (c : ℝ)
    (h : pathCoin f (threshDigit c) = pathCoin f' (threshDigit c)) (k : ℕ) :
    scrambledVdc f k ≤ c ↔ scrambledVdc f' k ≤ c := by
  rw [scrambledVdc_le_iff_shiftTable f, scrambledVdc_le_iff_shiftTable f', h]

/-! ### Stack paths through their decisions -/

/-- The inverse-CDF update only sees the comparisons of `u` with the cumulative sums. -/
theorem step_congr_of_le_iff {n : ℕ} (P : Fin n → Fin n → ℝ) (i : Fin n) {u u' : ℝ}
    (h : ∀ j : Fin n, u ≤ cumProb P i ((j : ℕ) + 1) ↔ u' ≤ cumProb P i ((j : ℕ) + 1)) :
    step P i u = step P i u' := by
  have e : (univ.filter fun j : Fin n ↦ u ≤ cumProb P i ((j : ℕ) + 1)) =
      univ.filter fun j : Fin n ↦ u' ≤ cumProb P i ((j : ℕ) + 1) :=
    Finset.filter_congr fun j _ ↦ h j
  unfold step
  simp only [e]

/-- A stack-driven path only depends on the updates of the stack entries. -/
theorem stackDrive_congr_of_forall {S α : Type*} [DecidableEq S] (G : S → α → S) (x₀ : S)
    {v v' : S → ℕ → α} (h : ∀ i k, G i (v i k) = G i (v' i k)) :
    stackDrive G x₀ v = stackDrive G x₀ v' := by
  have key : ∀ T, ∀ t ≤ T, stackDrive G x₀ v t = stackDrive G x₀ v' t := by
    intro T
    induction T with
    | zero =>
        intro t ht
        rw [Nat.le_zero.1 ht]
        rfl
    | succ T ih =>
        intro t ht
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with hlt | heq
        · exact ih t (Nat.lt_succ_iff.1 hlt)
        · rw [heq, stackDrive_succ, stackDrive_succ, h,
            departureIndex_congr (fun t' ht' ↦ ih t' ht'), ih T le_rfl]
  funext t
  exact key t t le_rfl

/-- `cumProb P i 1 = p_{i0}`. -/
theorem cumProb_one_eq_two_state (P : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : cumProb P i 1 = P i 0 := by
  have h := cumProb_succ P i 0
  rw [Fin.val_zero, zero_add, cumProb_zero, zero_add] at h
  exact h

/-- `cumProb P i 2 = 1` for a stochastic two-state `P`. -/
theorem cumProb_two_eq_two_state {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (i : Fin 2) :
    cumProb P i 2 = 1 := by
  have h := cumProb_succ P i 1
  change cumProb P i 2 = cumProb P i 1 + P i 1 at h
  rw [h, cumProb_one_eq_two_state, ← Fin.sum_univ_two (fun j ↦ P i j), hP.sum_eq_one i]

/-- The digital-shift tables given by the path coins of `f` along the thresholds `p₀₀`, `p₁₀`. -/
noncomputable def pathShift (P : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → ℕ → ℕ → Bool) :
    Fin 2 → ℕ → ℕ → Bool :=
  fun i ↦ shiftTable (pathCoin (f i) (threshDigit (P i 0)))

/-- **Every flip table acts on a two-state chain as a digital shift** (every stochastic `P`,
every flip table): the stack path is the path of the digitally shifted stacks whose flips are
the path coins of `f`. -/
theorem stackPath_eq_pathShift {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) :
    stackPath P x₀ (scrambledStack f) = stackPath P x₀ (scrambledStack (pathShift P f)) := by
  refine stackDrive_congr_of_forall _ _ fun i k ↦ step_congr_of_le_iff P i
    (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · change scrambledVdc (f i) k ≤ cumProb P i 1 ↔ scrambledVdc (pathShift P f i) k ≤ cumProb P i 1
    rw [cumProb_one_eq_two_state]
    exact scrambledVdc_le_iff_shiftTable (f i) (P i 0) k
  · change scrambledVdc (f i) k ≤ cumProb P i 2 ↔ scrambledVdc (pathShift P f i) k ≤ cumProb P i 2
    rw [cumProb_two_eq_two_state hP]
    exact ⟨fun _ ↦ (scrambledVdc_mem_Icc _ k).2, fun _ ↦ (scrambledVdc_mem_Icc _ k).2⟩

/-! ### The path as a function of the path coins -/

/-- The stack path of the digitally shifted stacks with flips `w`: the two-state path as a
function of the path coins. -/
noncomputable def coinPath (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) (w : Fin 2 × ℕ → Bool) :
    ℕ → Fin 2 :=
  stackPath P x₀ (scrambledStack (shiftFlips w))

/-- `coinPath` is measurable (product σ-algebra on paths). -/
theorem measurable_coinPath (P : Fin 2 → Fin 2 → ℝ) (x₀ : Fin 2) :
    Measurable (coinPath P x₀) :=
  measurable_pi_iff.2 fun t ↦
    measurable_stackPath_of (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ t

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Fin 2 → Fin 2 → ℝ}
  {F : Ω → Fin 2 → ℕ → ℕ → Bool} {Ψ : Ω → Fin 2 × ℕ → Bool}

/-- In a path-coin model the shift tables of the path coins are the digital shift by `Ψ ω`. -/
theorem IsPathCoinModel.pathShift_eq (hM : IsPathCoinModel P μ F Ψ) (ω : Ω) :
    pathShift P (F ω) = shiftFlips (Ψ ω) := by
  funext i
  change shiftTable (pathCoin (F ω i) (threshDigit (P i 0))) = shiftTable fun j ↦ Ψ ω (i, j)
  congr 1
  funext j
  exact hM.pathCoin_eq ω (i, j)

/-- **The path is a function of the path coins** in every path-coin model. -/
theorem IsPathCoinModel.stackPath_eq_coinPath (hM : IsPathCoinModel P μ F Ψ)
    (hP : IsStochastic P) (x₀ : Fin 2) (ω : Ω) :
    stackPath P x₀ (scrambledStack (F ω)) = coinPath P x₀ (Ψ ω) := by
  rw [stackPath_eq_pathShift hP, hM.pathShift_eq]
  rfl

/-- The stack path is measurable in every path-coin model. -/
theorem IsPathCoinModel.measurable_stackPath (hM : IsPathCoinModel P μ F Ψ) (x₀ : Fin 2) :
    Measurable fun ω ↦ stackPath P x₀ (scrambledStack (F ω)) :=
  measurable_pi_iff.2 fun t ↦ measurable_stackPath_of hM.measurable_stack P x₀ t

/-- **The law of the path in a path-coin model** is the image of the fair coins under
`coinPath`. -/
theorem IsPathCoinModel.map_stackPath (hM : IsPathCoinModel P μ F Ψ) (hP : IsStochastic P)
    (x₀ : Fin 2) :
    μ.map (fun ω ↦ stackPath P x₀ (scrambledStack (F ω))) =
      (shiftMeasure 2).map (coinPath P x₀) := by
  have e : (fun ω ↦ stackPath P x₀ (scrambledStack (F ω))) = coinPath P x₀ ∘ Ψ :=
    funext fun ω ↦ hM.stackPath_eq_coinPath hP x₀ ω
  rw [e, ← Measure.map_map (measurable_coinPath P x₀) hM.measurePreserving.measurable,
    hM.measurePreserving.map_eq]

/-- Any two path-coin models give identically distributed paths. -/
theorem IsPathCoinModel.identDistrib_stackPath {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} {F' : Ω' → Fin 2 → ℕ → ℕ → Bool} {Ψ' : Ω' → Fin 2 × ℕ → Bool}
    (hM : IsPathCoinModel P μ F Ψ) (hM' : IsPathCoinModel P μ' F' Ψ') (hP : IsStochastic P)
    (x₀ : Fin 2) :
    IdentDistrib (fun ω ↦ stackPath P x₀ (scrambledStack (F ω)))
      (fun ω ↦ stackPath P x₀ (scrambledStack (F' ω))) μ μ' where
  aemeasurable_fst := (hM.measurable_stackPath x₀).aemeasurable
  aemeasurable_snd := (hM'.measurable_stackPath x₀).aemeasurable
  map_eq := by rw [hM.map_stackPath hP, hM'.map_stackPath hP]

/-! ### Owen's scramble and the digital shift -/

/-- **Owen's path is the digital-shift path of the Owen path coins**, for every `ω`. -/
theorem stackPath_owen_eq_coinPath (hP : IsStochastic P) (x₀ : Fin 2)
    (ω : Fin 2 × ℕ × ℕ → Bool) :
    stackPath P x₀ (scrambledStack (owenTable ω)) =
      coinPath P x₀ (owenPathCoins (chainDigits P) ω) :=
  (isPathCoinModel_owen P).stackPath_eq_coinPath hP x₀ ω

/-- The digital-shift path is `coinPath` of the flips. -/
theorem stackPath_shift_eq_coinPath (x₀ : Fin 2) (ω : Fin 2 × ℕ → Bool) :
    stackPath P x₀ (scrambledStack (shiftFlips ω)) = coinPath P x₀ ω := rfl

/-- **Law equivalence of the paths** (post #3, codes (ii) and (iii), two states): the stack path
driven by Owen-scrambled stacks and the one driven by digitally shifted stacks have the same
law on `ℕ → Fin 2`. -/
theorem map_stackPath_owen_eq_shift (hP : IsStochastic P) (x₀ : Fin 2) :
    (owenMeasure 2).map (fun ω ↦ stackPath P x₀ (scrambledStack (owenTable ω))) =
      (shiftMeasure 2).map (fun ω ↦ stackPath P x₀ (scrambledStack (shiftFlips ω))) := by
  rw [(isPathCoinModel_owen P).map_stackPath hP, (isPathCoinModel_shift P).map_stackPath hP]

/-- The Owen and digital-shift paths are identically distributed. -/
theorem identDistrib_stackPath_owen_shift (hP : IsStochastic P) (x₀ : Fin 2) :
    IdentDistrib (fun ω ↦ stackPath P x₀ (scrambledStack (owenTable ω)))
      (fun ω ↦ stackPath P x₀ (scrambledStack (shiftFlips ω))) (owenMeasure 2)
      (shiftMeasure 2) :=
  (isPathCoinModel_owen P).identDistrib_stackPath (isPathCoinModel_shift P) hP x₀

/-- **Cylinder probabilities agree**: for every horizon `T` and every finite path `s`,
`P(x_t = s_t, t ≤ T)` is the same under Owen's scramble and under the digital shift. -/
theorem owenMeasure_stackPath_cylinder (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ)
    (s : ℕ → Fin 2) :
    owenMeasure 2 {ω | ∀ t ≤ T, stackPath P x₀ (scrambledStack (owenTable ω)) t = s t} =
      shiftMeasure 2 {ω | ∀ t ≤ T, stackPath P x₀ (scrambledStack (shiftFlips ω)) t = s t} := by
  have hs : MeasurableSet {p : ℕ → Fin 2 | ∀ t ≤ T, p t = s t} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun t ↦ ?_
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun _ ↦ ?_
    change MeasurableSet ((fun p : ℕ → Fin 2 ↦ p t) ⁻¹' {s t})
    exact (measurableSet_singleton (s t)).preimage (measurable_pi_apply t)
  exact (identDistrib_stackPath_owen_shift hP x₀).measure_mem_eq hs

/-- **Every measurable path functional has the same law** under Owen's scramble and the
digital shift. -/
theorem identDistrib_comp_stackPath_owen_shift {β : Type*} [MeasurableSpace β]
    (hP : IsStochastic P) (x₀ : Fin 2) {G : (ℕ → Fin 2) → β} (hG : Measurable G) :
    IdentDistrib (fun ω ↦ G (stackPath P x₀ (scrambledStack (owenTable ω))))
      (fun ω ↦ G (stackPath P x₀ (scrambledStack (shiftFlips ω)))) (owenMeasure 2)
      (shiftMeasure 2) :=
  (identDistrib_stackPath_owen_shift hP x₀).comp hG

/-! ### Counts and the occupation error -/

/-- The occupation count is a measurable path functional. -/
theorem measurable_occCount_path (i : Fin 2) (T : ℕ) :
    Measurable fun p : ℕ → Fin 2 ↦ occCount p i T := by
  have hloc : IsLocal (fun p : ℕ → Fin 2 ↦ occCount p i T) (range T) :=
    fun p q h ↦ occCount_congr (fun t ht ↦ h t (mem_range.2 ht)) i
  exact hloc.measurable

/-- The transition count is a measurable path functional. -/
theorem measurable_transCount_path (i j : Fin 2) (T : ℕ) :
    Measurable fun p : ℕ → Fin 2 ↦ transCount p i j T := by
  have hloc : IsLocal (fun p : ℕ → Fin 2 ↦ transCount p i j T) (range (T + 1)) :=
    fun p q h ↦ transCount_congr (fun t ht ↦ h t (mem_range.2 (Nat.lt_succ_of_le ht))) i j
  exact hloc.measurable

/-- The occupation counts have the same law under Owen's scramble and the digital shift. -/
theorem identDistrib_occCount_owen_shift (hP : IsStochastic P) (x₀ i : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ occCount (stackPath P x₀ (scrambledStack (owenTable ω))) i T)
      (fun ω ↦ occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i T) (owenMeasure 2)
      (shiftMeasure 2) :=
  identDistrib_comp_stackPath_owen_shift hP x₀ (measurable_occCount_path i T)

/-- The transition counts have the same law under Owen's scramble and the digital shift. -/
theorem identDistrib_transCount_owen_shift (hP : IsStochastic P) (x₀ i j : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ transCount (stackPath P x₀ (scrambledStack (owenTable ω))) i j T)
      (fun ω ↦ transCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) i j T)
      (owenMeasure 2) (shiftMeasure 2) :=
  identDistrib_comp_stackPath_owen_shift hP x₀ (measurable_transCount_path i j T)

/-- **The occupation error has the same law** under Owen's scramble and the digital shift, for
every `T`. -/
theorem identDistrib_occErr_owen_shift (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ) :
    IdentDistrib (fun ω ↦ occErr P x₀ (owenTable ω) T) (fun ω ↦ occErr P x₀ (shiftFlips ω) T)
      (owenMeasure 2) (shiftMeasure 2) := by
  have hG : Measurable fun p : ℕ → Fin 2 ↦ (occCount p 0 T : ℝ) - T * piZero P :=
    ((measurable_from_nat (f := fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_occCount_path 0 T)).sub measurable_const
  exact identDistrib_comp_stackPath_owen_shift hP x₀ hG

/-- **Equal variances** of the occupation error under Owen's scramble and the digital shift. -/
theorem variance_occErr_owen_eq_shift (hP : IsStochastic P) (x₀ : Fin 2) (T : ℕ) :
    Var[fun ω ↦ occErr P x₀ (owenTable ω) T; owenMeasure 2] =
      Var[fun ω ↦ occErr P x₀ (shiftFlips ω) T; shiftMeasure 2] :=
  (identDistrib_occErr_owen_shift hP x₀ T).variance_eq

/-! ### Limit theorems transfer -/

/-- Convergence in distribution only depends on the laws of the terms. -/
theorem tendstoInDistribution_congr_identDistrib {Ω₁ Ω₂ Ω' : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω'] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {l : Filter ℕ} {X : ℕ → Ω₁ → ℝ} {Y : ℕ → Ω₂ → ℝ} {Z : Ω' → ℝ}
    (h : ∀ k, IdentDistrib (X k) (Y k) μ₁ μ₂) :
    TendstoInDistribution X l Z (fun _ ↦ μ₁) P' ↔ TendstoInDistribution Y l Z (fun _ ↦ μ₂) P' := by
  constructor
  · intro hX
    exact ⟨fun k ↦ (h k).aemeasurable_snd, hX.aemeasurable_limit,
      Tendsto.congr (fun k ↦ Subtype.ext (h k).map_eq) hX.tendsto⟩
  · intro hY
    exact ⟨fun k ↦ (h k).aemeasurable_fst, hY.aemeasurable_limit,
      Tendsto.congr (fun k ↦ Subtype.ext (h k).map_eq.symm) hY.tendsto⟩

/-- **Limit laws of the occupation error transfer** between Owen's scramble and the digital
shift: for every time sequence `T_k`, every sequence of measurable maps `u_k` (e.g.
normalisations) and every limit `Z`, `u_k(N₀(T_k) − T_k π₀)` converges in distribution to `Z`
under Owen's scramble iff it does under the digital shift. -/
theorem tendstoInDistribution_occErr_owen_iff_shift (hP : IsStochastic P) (x₀ : Fin 2)
    (T : ℕ → ℕ) {u : ℕ → ℝ → ℝ} (hu : ∀ k, Measurable (u k)) {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ} :
    TendstoInDistribution (fun k ω ↦ u k (occErr P x₀ (owenTable ω) (T k))) atTop Z
        (fun _ ↦ owenMeasure 2) P' ↔
      TendstoInDistribution (fun k ω ↦ u k (occErr P x₀ (shiftFlips ω) (T k))) atTop Z
        (fun _ ↦ shiftMeasure 2) P' :=
  tendstoInDistribution_congr_identDistrib fun k ↦
    (identDistrib_occErr_owen_shift hP x₀ (T k)).comp (hu k)

/-- **The two CLTs are the same statement**: the occupation error normalised by its own
standard deviation converges in distribution to `Z` under Owen's scramble iff it does under the
digital shift (and the variances, hence the variance hypotheses of
`tendstoInDistribution_occErr_owen` and `tendstoInDistribution_occErr_shift`, agree:
`variance_occErr_owen_eq_shift`). -/
theorem tendstoInDistribution_normalised_occErr_owen_iff_shift (hP : IsStochastic P)
    (x₀ : Fin 2) (T : ℕ → ℕ) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} :
    TendstoInDistribution (fun k ω ↦ occErr P x₀ (owenTable ω) (T k) /
        √Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2]) atTop Z
        (fun _ ↦ owenMeasure 2) P' ↔
      TendstoInDistribution (fun k ω ↦ occErr P x₀ (shiftFlips ω) (T k) /
        √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2]) atTop Z
        (fun _ ↦ shiftMeasure 2) P' := by
  have hv : ∀ k, Var[fun ω ↦ occErr P x₀ (owenTable ω) (T k); owenMeasure 2] =
      Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2] :=
    fun k ↦ variance_occErr_owen_eq_shift hP x₀ (T k)
  simp only [hv]
  exact tendstoInDistribution_occErr_owen_iff_shift hP x₀ T
    (u := fun k x ↦ x / √Var[fun ω ↦ occErr P x₀ (shiftFlips ω) (T k); shiftMeasure 2])
    fun k ↦ measurable_id.div_const _

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Three states: Owen's scramble and the digital shift give different path laws (post #3)

Post #3 treats codes (ii) (one Sobol sequence per state with a random digital shift) and (iii)
(Owen scrambling) together. For two-state chains their path laws coincide (`CltPathBits`,
`map_owenPathCoins`: one threshold per row, and the path coins of Owen's scramble are i.i.d.
fair). With two thresholds in a row this fails: the two jump paths of the binary tree share the
digital-shift flips at every depth, but use independent Owen flips once they split.

**Counterexample.** The three-state chain with every row `(1/4, 1/2, 1/4)` (`threeChain`),
started in state `0`. The cylinder "stay in `0`, then move to `1`" (`StayThenMove`) uses the
first two points of stack `0`: `x₀ ≤ 1/4` and `1/4 < x₁ ≤ 3/4`.
* Digital shift: `x₁ = x₀ + 1/2` whenever `x₀ < 1/2`, so the event is `{x₀ ≤ 1/4}`:
  probability `1/4` (`shiftMeasure_stayThenMove`).
* Owen: `x₁`'s first digit is the complement of `x₀`'s, its other digits are fresh flips, so the
  event is three fair coins: probability `1/8` (`owenMeasure_stayThenMove`), which is also the
  Markov (MC) probability `p₀₀ p₀₁`.
Hence `owen_ne_shift_stayThenMove`: the path laws of (ii) and (iii) differ for three states.
The values were checked by simulation (4·10⁵ replications: `0.2501` vs `0.1253`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-- The three-state chain whose rows are all `(1/4, 1/2, 1/4)`. -/
noncomputable def threeChain : Fin 3 → Fin 3 → ℝ := fun _ j ↦ if j = 1 then 1 / 2 else 1 / 4

theorem isStochastic_threeChain : IsStochastic threeChain where
  nonneg i j := by unfold threeChain; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_three]
    simp [threeChain]
    norm_num

/-- `step` for the rows `(1/4, 1/2, 1/4)`: state `0` iff `u ≤ 1/4`. -/
theorem threeChain_step_eq_zero_iff (i : Fin 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    step threeChain i u = 0 ↔ u ≤ 1 / 4 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero isStochastic_threeChain.nonneg i
    exact ⟨fun _ ↦ by norm_num, fun _ ↦ Fin.ext h⟩
  · have h := step_eq_iff isStochastic_threeChain i 0 ⟨hpos, hu.2⟩
    have h1 : cumProb threeChain i ((0 : Fin 3) : ℕ) = 0 := cumProb_zero threeChain i
    have h2 : cumProb threeChain i (((0 : Fin 3) : ℕ) + 1) = 1 / 4 := by
      rw [cumProb_succ, h1, zero_add]
      simp [threeChain]
    rw [h1, h2] at h
    exact h.trans ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hpos, h'⟩⟩

/-- `step` for the rows `(1/4, 1/2, 1/4)`: state `1` iff `1/4 < u ≤ 3/4`. -/
theorem threeChain_step_eq_one_iff (i : Fin 3) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    step threeChain i u = 1 ↔ 1 / 4 < u ∧ u ≤ 3 / 4 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h := step_zero isStochastic_threeChain.nonneg i
    constructor
    · intro h1
      rw [h1] at h
      exact absurd h (by decide)
    · intro h1
      norm_num at h1
  · have h := step_eq_iff isStochastic_threeChain i 1 ⟨hpos, hu.2⟩
    have h1 : cumProb threeChain i ((1 : Fin 3) : ℕ) = 1 / 4 := by
      have := cumProb_succ threeChain i 0
      simp only [Fin.val_zero, zero_add, cumProb_zero] at this
      change cumProb threeChain i 1 = 1 / 4
      rw [this]
      simp [threeChain]
    have h2 : cumProb threeChain i (((1 : Fin 3) : ℕ) + 1) = 3 / 4 := by
      rw [cumProb_succ, h1]
      simp [threeChain]
      norm_num
    rw [h1, h2] at h
    exact h

/-- The cylinder "start in `0`, stay in `0`, then move to `1`". -/
def StayThenMove (f : Fin 3 → ℕ → ℕ → Bool) : Prop :=
  stackPath threeChain 0 (scrambledStack f) 1 = 0 ∧ stackPath threeChain 0 (scrambledStack f) 2 = 1

/-- The cylinder in terms of the first two points of stack `0`. -/
theorem stayThenMove_iff (f : Fin 3 → ℕ → ℕ → Bool) :
    StayThenMove f ↔ scrambledVdc (f 0) 0 ≤ 1 / 4 ∧
      1 / 4 < scrambledVdc (f 0) 1 ∧ scrambledVdc (f 0) 1 ≤ 3 / 4 := by
  set x := stackPath threeChain 0 (scrambledStack f) with hx
  have hv : ∀ i k, scrambledStack f i k ∈ Set.Icc (0 : ℝ) 1 := scrambledStack_mem_Icc f
  have h1 : x 1 = step threeChain 0 (scrambledStack f 0 0) := by
    rw [hx]
    change stackDrive (step threeChain) 0 (scrambledStack f) (0 + 1) = _
    rw [stackDrive_succ, stackDrive_zero]
    rfl
  have hd1 : x 1 = 0 → departureIndex x 1 = 1 := fun h ↦ by
    unfold departureIndex
    rw [h, occCount_succ, occCount_zero]
    simp [hx, stackDrive_zero]
  have h2 : x 2 = step threeChain (x 1) (scrambledStack f (x 1) (departureIndex x 1)) := by
    rw [hx]
    change stackDrive (step threeChain) 0 (scrambledStack f) (1 + 1) = _
    rw [stackDrive_succ]
  unfold StayThenMove
  rw [← hx, h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]
  constructor
  · rintro ⟨ha, hb⟩
    have hx1 : x 1 = 0 := by rw [h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]; exact ha
    rw [h2, hx1, hd1 hx1, threeChain_step_eq_one_iff 0 (hv 0 1)] at hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    have hx1 : x 1 = 0 := by rw [h1, threeChain_step_eq_zero_iff 0 (hv 0 0)]; exact ha
    refine ⟨ha, ?_⟩
    rw [h2, hx1, hd1 hx1, threeChain_step_eq_one_iff 0 (hv 0 1)]
    exact hb

/-- For digits that are not eventually constant, `binaryVal d ≤ 1/4` iff the first two digits
are `0`. -/
theorem binaryVal_le_quarter_iff {d : ℕ → Bool} (hd : NotEventuallyConst d) :
    binaryVal d ≤ 1 / 4 ↔ d 0 = false ∧ d 1 = false := by
  have h1 := digitPrefix_div_lt_binaryVal hd 2
  have h2 := binaryVal_lt_digitPrefix_add_one_div hd 2
  have e : digitPrefix d 2 = 2 * (if d 0 then 1 else 0) + (if d 1 then 1 else 0) := by
    change 2 * (2 * 0 + (if d 0 then 1 else 0)) + (if d 1 then 1 else 0) = _
    ring
  rw [e] at h1 h2
  cases h0 : d 0 <;> cases h1' : d 1 <;> simp only [h0, h1'] at h1 h2 <;> norm_num at h1 h2 ⊢ <;>
    linarith

/-- For digits that are not eventually constant with first digit `1`,
`1/4 < binaryVal d ≤ 3/4` iff the second digit is `0`. -/
theorem binaryVal_mem_middle_iff {d : ℕ → Bool} (hd : NotEventuallyConst d) (h0 : d 0 = true) :
    (1 / 4 < binaryVal d ∧ binaryVal d ≤ 3 / 4) ↔ d 1 = false := by
  have h1 := digitPrefix_div_lt_binaryVal hd 2
  have h2 := binaryVal_lt_digitPrefix_add_one_div hd 2
  have e : digitPrefix d 2 = 2 * (if d 0 then 1 else 0) + (if d 1 then 1 else 0) := by
    change 2 * (2 * 0 + (if d 0 then 1 else 0)) + (if d 1 then 1 else 0) = _
    ring
  rw [e, h0] at h1 h2
  cases h1' : d 1
  · simp only [h1', ite_true, Bool.false_eq_true, ite_false] at h1 h2
    norm_num at h1 h2
    simp only [iff_true]
    exact ⟨by linarith, by linarith⟩
  · simp only [h1', ite_true] at h1 h2
    norm_num at h1 h2
    simp only [Bool.true_eq_false, iff_false, not_and, not_le]
    intro _
    linarith

/-- The first digit of point `1` is the complement of that of point `0` (same node), its other
digits use the nodes of prefix `1`. -/
theorem scrambledDigit_one (f : ℕ → ℕ → Bool) (j : ℕ) :
    scrambledDigit f 1 j = if j = 0 then !f 0 0 else f j 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [scrambledDigit]
  · have h1 : (1 : ℕ).testBit j = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hj.ne')
    have h2 : 1 % 2 ^ j = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow hj.ne')
    simp [scrambledDigit, h1, h2, hj.ne']

/-- Point `0` of a stack has the flips at prefix `0` as digits. -/
theorem scrambledDigit_zero (f : ℕ → ℕ → Bool) (j : ℕ) : scrambledDigit f 0 j = f j 0 := by
  simp [scrambledDigit]

/-- On the good event the cylinder is: the digits `0, 1` of point `0` and the digit `1` of
point `1` are `0`, the digit `0` of point `1` being the complement of that of point `0`. -/
theorem stayThenMove_iff_digits {f : Fin 3 → ℕ → ℕ → Bool} (hf : IsGoodTable f) :
    StayThenMove f ↔ f 0 0 0 = false ∧ f 0 1 0 = false ∧ f 0 1 1 = false := by
  rw [stayThenMove_iff]
  have hg0 := hf 0 0
  have hg1 := hf 0 1
  rw [scrambledVdc, binaryVal_le_quarter_iff hg0, scrambledDigit_zero, scrambledDigit_zero]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have h0 : scrambledDigit (f 0) 1 0 = true := by rw [scrambledDigit_one]; simp [ha]
    have := (binaryVal_mem_middle_iff hg1 h0).1 hc
    rw [scrambledDigit_one] at this
    exact ⟨ha, hb, by simpa using this⟩
  · rintro ⟨ha, hb, hc⟩
    have h0 : scrambledDigit (f 0) 1 0 = true := by rw [scrambledDigit_one]; simp [ha]
    refine ⟨⟨ha, hb⟩, (binaryVal_mem_middle_iff hg1 h0).2 ?_⟩
    rw [scrambledDigit_one]
    simpa using hc

/-- **Owen's scramble**: the cylinder has probability `1/8` (`= p₀₀ p₀₁`, as for i.i.d.
driving). -/
theorem owenMeasure_stayThenMove :
    owenMeasure 3 {ω | StayThenMove (owenTable ω)} = 1 / 8 := by
  classical
  have hae : {ω : Fin 3 × ℕ × ℕ → Bool | StayThenMove (owenTable ω)} =ᵐ[owenMeasure 3]
      Set.pi (({(0, 0, 0), (0, 1, 0), (0, 1, 1)} : Finset (Fin 3 × ℕ × ℕ)) : Set _)
        fun _ ↦ ({false} : Set Bool) := by
    filter_upwards [ae_isGoodTable_owen 3] with ω hω
    simp only [eq_iff_iff]
    rw [stayThenMove_iff_digits hω]
    simp [owenTable]
  rw [measure_congr hae, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const]
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp), card_singleton, one_div,
    ← ENNReal.inv_pow]
  norm_num

/-- **Digital shift**: the cylinder has probability `1/4`. -/
theorem shiftMeasure_stayThenMove :
    shiftMeasure 3 {ω | StayThenMove (shiftFlips ω)} = 1 / 4 := by
  classical
  have hae : {ω : Fin 3 × ℕ → Bool | StayThenMove (shiftFlips ω)} =ᵐ[shiftMeasure 3]
      Set.pi (({(0, 0), (0, 1)} : Finset (Fin 3 × ℕ)) : Set _)
        fun _ ↦ ({false} : Set Bool) := by
    filter_upwards [ae_isGoodTable_shift 3] with ω hω
    simp only [eq_iff_iff]
    rw [stayThenMove_iff_digits hω]
    simp [shiftFlips, shiftTable]
  rw [measure_congr hae, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const]
  rw [card_insert_of_notMem (by simp), card_singleton, one_div, ← ENNReal.inv_pow]
  norm_num

/-- **Correction**: for three states the path laws of codes (ii) and (iii) differ. -/
theorem owen_ne_shift_stayThenMove :
    owenMeasure 3 {ω | StayThenMove (owenTable ω)} ≠
      shiftMeasure 3 {ω | StayThenMove (shiftFlips ω)} := by
  rw [owenMeasure_stayThenMove, shiftMeasure_stayThenMove, one_div, one_div, Ne,
    inv_inj]
  norm_num

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Dyadic transition probabilities: bounded errors, no CLT (post #3, codes (ii) and (iii))

Post #3 reports for the per-state Sobol stacks with a random digital shift (ii) or Owen
scrambling (iii) that "in the two-state chain every spell lasts exactly 8 periods" and that, "as
in the i.i.d. case, the RQMC estimators are typically not normally distributed". For **dyadic**
transition probabilities this is exact and holds for every realisation.

**Dyadic thresholds.** If `x = a / 2^L ∈ [0,1]` and the digits of every point are not eventually
constant (the good event, probability one), then an aligned `2^m`-block with `m ≥ L` has counting
error exactly `0` at `x` (`segErr_scrambledVdc_block_dyadic`): a point lies below `x` iff its
first `m` scrambled digits do. Hence every initial segment has error `≤ L`
(`abs_segErr_scrambledVdc_dyadic_le`), uniformly in its length.

**Chains** (`DyadicCumProb P L`: every `cs_{ij} ∈ 2^{-L} ℕ`; `dyadicCumProb_of_entries`). On the
good event, for every `T`:
* `abs_transCount_dyadic_sub_le`: `|N_ij(T) − p_ij N_i(T)| ≤ 2L`;
* `abs_departureDiscrepancy_dyadic_le`: `|D_i(g, T)| ≤ V(g) L`;
* `abs_occCount_dyadic_sub_le`: `|N_s(T) − T π_s| ≤ 2M + n V(h) L`;
* `ae_abs_occCount_dyadic_owen_le`, `ae_abs_occCount_dyadic_shift_le`: almost surely, for all `T`.

**No CLT.** `not_tendstoInDistribution_of_card_le`: random variables taking, almost surely, at
most `K` values (a set that may depend on `T`) do not converge in distribution to any law
without atoms (portmanteau on `K + 1` disjoint intervals of positive limit mass, chosen by the
intermediate value theorem for the continuous CDF). `not_tendstoInDistribution_occCount_owen`,
`not_tendstoInDistribution_occCount_shift`: for a dyadic chain no normalisation
`(N_s(T) − T π_s − b_T) / a_T` converges in distribution to a law without atoms, in particular
not to `N(0,1)` (`not_tendstoInDistribution_occCount_owen_gaussian`).

**The post's two-state chain** `stackChain78` (`p₁₁ = p₂₂ = 7/8`): `h = (2, −2)` solves Poisson's
equation for `π = (1/2, 1/2)`; on the good event `|N_0(T) − T/2| ≤ 28` for all `T`
(`abs_occCount_stackChain78_le`), so `N_0(T) − T/2` lies in the fixed finite set
`{k/2 : |k| ≤ 56}` (`occCount_stackChain78_mem`), and there is no CLT under either randomisation
(`not_tendstoInDistribution_stackChain78_owen`, `not_tendstoInDistribution_stackChain78_shift`).

**Correction** (post #3, "normality cannot be rejected" / "typically not normally
distributed"): for codes (ii) and (iii) with dyadic transition probabilities, as in the post's
two-state chain, the occupation error is bounded and takes finitely many values, so it is not
asymptotically normal under any normalisation, for the digital shift *and* for Owen scrambling
(post #2's CLT for Owen-scrambled nets does not transfer to the Markov stack setting).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Finset Matrix Filter Topology

variable {n : ℕ}

/-! ### Finitely many values: no convergence to an atomless law -/

/-- The CDF of an atomless probability measure is continuous. -/
theorem continuous_cdf_of_noAtoms {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} = 0) : Continuous (cdf ν) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [(monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim, (cdf ν).rightLim_eq]
  have h := (cdf ν).measure_singleton x
  rw [measure_cdf, hν x] at h
  have h1 : cdf ν x - Function.leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.1 h.symm
  have h2 : Function.leftLim (cdf ν) x ≤ cdf ν x := (monotone_cdf ν).leftLim_le le_rfl
  linarith

/-- An atomless probability measure on `ℝ` attains every CDF value in `(0,1)`. -/
theorem exists_cdf_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} = 0) {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) : ∃ t, cdf ν t = y := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hy0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hy1)).exists
  have hab : a ≤ b := by
    by_contra h
    linarith [monotone_cdf ν (not_le.1 h).le]
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hab
    (continuous_cdf_of_noAtoms hν).continuousOn ⟨ha.le, hb.le⟩
  exact ⟨t, ht⟩

/-- **Finitely many values rule out an atomless limit.** If, for every `T`, `W T` lies almost
surely in a finite set `S T` with at most `K` elements, then `W T` does not converge in
distribution to any `Z` whose law has no atoms. -/
theorem not_tendstoInDistribution_of_card_le {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {K : ℕ} (S : ℕ → Finset ℝ)
    (hS : ∀ T, (S T).card ≤ K) (hW : ∀ T, ∀ᵐ ω ∂μ, W T ω ∈ S T)
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution W atTop Z (fun _ => μ) μ' := by
  intro h
  set ν := μ'.map Z with hνdef
  -- quantiles `q l` with `F(q l) = (l + 1)/(K + 3)` for `l ≤ K + 1`
  have hq : ∀ l : ℕ, ∃ t, cdf ν t = ((min l (K + 1) : ℕ) + 1 : ℝ) / (K + 3) := by
    intro l
    have h1 : ((min l (K + 1) : ℕ) : ℝ) ≤ K + 1 := by exact_mod_cast min_le_right _ _
    refine exists_cdf_eq hZ (by positivity) ?_
    rw [div_lt_one (by positivity)]
    linarith
  choose q hq using hq
  have hqval : ∀ l ≤ K + 1, cdf ν (q l) = ((l : ℝ) + 1) / (K + 3) := by
    intro l hl
    rw [hq l, min_eq_left hl]
  have hqlt : ∀ l l', l < l' → l' ≤ K + 1 → q l < q l' := by
    intro l l' hll' hl'
    by_contra hcon
    have := monotone_cdf ν (not_lt.1 hcon)
    rw [hqval l (by omega), hqval l' hl'] at this
    have h2 : ((l : ℝ) + 1) < (l' : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hll' 1
    have h3 : ((l' : ℝ) + 1) / (K + 3) ≤ ((l : ℝ) + 1) / (K + 3) := this
    rw [div_le_div_iff_of_pos_right (by positivity)] at h3
    linarith
  -- each piece `(q l, q (l+1)]`, `l ≤ K`, has limit mass `1/(K+3) > 0` and a null frontier
  have hpiece : ∀ l ∈ range (K + 1), ∀ᶠ T in atTop,
      0 < (μ.map (W T)) (Set.Ioc (q l) (q (l + 1))) := by
    intro l hl
    have hl' := mem_range.1 hl
    have hfr : ν (frontier (Set.Ioc (q l) (q (l + 1)))) = 0 := by
      rw [frontier_Ioc (hqlt l (l + 1) (by omega) (by omega))]
      refine measure_mono_null (Set.insert_subset_iff.2 ⟨Set.mem_insert _ _, ?_⟩)
        (measure_union_null (hZ (q l)) (hZ (q (l + 1))))
      simp
    have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hfr
    have hpos : 0 < ν (Set.Ioc (q l) (q (l + 1))) := by
      have e := (cdf ν).measure_Ioc (q l) (q (l + 1))
      rw [measure_cdf, hqval l (by omega), hqval (l + 1) (by omega)] at e
      change 0 < ν (Set.Ioc (q l) (q (l + 1)))
      rw [e, ENNReal.ofReal_pos, ← sub_div, div_pos_iff_of_pos_right (by positivity)]
      push_cast
      linarith
    exact (tendsto_order.1 hlim).1 0 hpos
  obtain ⟨T, hT⟩ := ((eventually_all_finset (range (K + 1))).2 hpiece).exists
  -- each piece contains a point of `S T`
  have hpt : ∀ l ∈ range (K + 1), ∃ x ∈ S T, x ∈ Set.Ioc (q l) (q (l + 1)) := by
    intro l hl
    by_contra hcon
    push Not at hcon
    have hnull : μ (W T ⁻¹' Set.Ioc (q l) (q (l + 1))) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hW T))
      intro hmem
      exact hcon _ hmem hω
    have := hT l hl
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable T) measurableSet_Ioc,
      hnull] at this
    exact lt_irrefl _ this
  choose! x hxS hxI using hpt
  -- distinct pieces give distinct points
  have hinj : Set.InjOn x (range (K + 1) : Set ℕ) := by
    intro l hl l' hl' hll'
    have hl1 := mem_range.1 hl
    have hl1' := mem_range.1 hl'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (hxI l hl).2
      have h2 := (hxI l' hl').1
      have h3 : q (l + 1) ≤ q l' := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | he
        · exact le_of_eq (congrArg q he)
        · exact (hqlt _ _ he (by omega)).le
      rw [hll'] at h1
      linarith
    · have h1 := (hxI l' hl').2
      have h2 := (hxI l hl).1
      have h3 : q (l' + 1) ≤ q l := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with he | he
        · exact le_of_eq (congrArg q he)
        · exact (hqlt _ _ he (by omega)).le
      rw [← hll'] at h1
      linarith
  have hcard := card_le_card_of_injOn x (fun l hl => hxS l hl) hinj
  rw [card_range] at hcard
  linarith [hS T]

/-- An integer within `C` of `y` is `⌈y − C⌉ + r` for some `r ≤ ⌊2C⌋`. -/
theorem exists_eq_ceil_add_of_abs_le {y C : ℝ} {z : ℤ} (hz : |(z : ℝ) - y| ≤ C) :
    ∃ r < ⌊2 * C⌋₊ + 1, z = ⌈y - C⌉ + r := by
  have h1 := (abs_le.1 hz).1
  have h2 := (abs_le.1 hz).2
  have hc : ⌈y - C⌉ ≤ z := Int.ceil_le.2 (by linarith)
  have hc2 : ((⌈y - C⌉ : ℤ) : ℝ) ≥ y - C := Int.le_ceil _
  refine ⟨(z - ⌈y - C⌉).toNat, ?_, by omega⟩
  have hr : ((z - ⌈y - C⌉ : ℤ) : ℝ) ≤ 2 * C := by push_cast; linarith
  have hr0 : 0 ≤ z - ⌈y - C⌉ := by omega
  have : (z - ⌈y - C⌉).toNat ≤ ⌊2 * C⌋₊ := by
    refine Nat.le_floor ?_
    rw [show (((z - ⌈y - C⌉).toNat : ℕ) : ℝ) = ((z - ⌈y - C⌉ : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]]
    exact hr
  omega

/-- **Bounded integer errors rule out an atomless limit**: if `|Y T − y T| ≤ C` almost surely
with `Y T` integer-valued, no normalisation `(Y T − y T − b T) / a T` converges in distribution
to a law without atoms. -/
theorem not_tendstoInDistribution_of_abs_sub_le {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω → ℤ} {y : ℕ → ℝ} {C : ℝ}
    (hY : ∀ T, ∀ᵐ ω ∂μ, |(Y T ω : ℝ) - y T| ≤ C) (a b : ℕ → ℝ) {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω => ((Y T ω : ℝ) - y T - b T) / a T) atTop Z
      (fun _ => μ) μ' := by
  refine not_tendstoInDistribution_of_card_le (K := ⌊2 * C⌋₊ + 1)
    (fun T => (range (⌊2 * C⌋₊ + 1)).image fun r : ℕ =>
      (((⌈y T - C⌉ + r : ℤ) : ℝ) - y T - b T) / a T)
    (fun T => card_image_le.trans (card_range _).le) (fun T => ?_) hZ
  filter_upwards [hY T] with ω hω
  obtain ⟨r, hr, hz⟩ := exists_eq_ceil_add_of_abs_le hω
  exact mem_image.2 ⟨r, mem_range.2 hr, by rw [hz]⟩

/-! ### Dyadic thresholds -/

/-- **Dyadic thresholds split aligned blocks exactly**: if no digit sequence of the points is
eventually constant, then at a threshold `a' / 2^L ≤ 1` every aligned `2^m`-block with `m ≥ L`
has counting error `0`. -/
theorem segErr_scrambledVdc_block_dyadic {f : ℕ → ℕ → Bool}
    (hf : ∀ k, NotEventuallyConst (scrambledDigit f k)) {L a' m : ℕ} (hm : L ≤ m)
    (hx1 : (a' : ℝ) / 2 ^ L ≤ 1) (a : ℕ) :
    segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) (a * 2 ^ m) (2 ^ m) = 0 := by
  rw [segErr_eq_card]
  set c := a' * 2 ^ (m - L) with hc
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hpL : (0 : ℝ) < 2 ^ L := by positivity
  have hcx : (c : ℝ) = 2 ^ m * ((a' : ℝ) / 2 ^ L) := by
    have h2 : (2 : ℝ) ^ m = 2 ^ (m - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel hm]
    rw [hc, h2]
    push_cast
    field_simp
  have hcm : c ≤ 2 ^ m := by
    have : (c : ℝ) ≤ 2 ^ m := by rw [hcx]; nlinarith
    exact_mod_cast this
  have hxc : (a' : ℝ) / 2 ^ L * 2 ^ m = c := by rw [hcx]; ring
  have hset : (range (2 ^ m)).filter
      (fun k => scrambledVdc f (a * 2 ^ m + k) ≤ (a' : ℝ) / 2 ^ L) =
      (range (2 ^ m)).filter (fun k => digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m < c) := by
    refine filter_congr fun k _ => ?_
    constructor
    · intro hle
      by_contra hcon
      have hk : (c : ℝ) ≤ (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℕ) := by
        exact_mod_cast not_lt.1 hcon
      have h := digitPrefix_div_lt_binaryVal (hf (a * 2 ^ m + k)) m
      rw [div_lt_iff₀ hp] at h
      have h3 : scrambledVdc f (a * 2 ^ m + k) * 2 ^ m ≤ (a' : ℝ) / 2 ^ L * 2 ^ m :=
        mul_le_mul_of_nonneg_right hle hp.le
      change (digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℝ) <
        scrambledVdc f (a * 2 ^ m + k) * 2 ^ m at h
      linarith
    · intro hlt
      have hk : ((digitPrefix (scrambledDigit f (a * 2 ^ m + k)) m : ℕ) : ℝ) + 1 ≤ c := by
        exact_mod_cast hlt
      have h := binaryVal_le_digitPrefix_add_one_div (scrambledDigit f (a * 2 ^ m + k)) m
      refine h.trans ?_
      rw [div_le_iff₀ hp]
      linarith
  have hcard := card_filter_digitPrefix_block f a m (· < c)
  rw [hset, hcard, card_filter_lt_range, min_eq_left hcm]
  push_cast
  rw [hcx]
  ring

/-- **Dyadic thresholds: bounded error for every initial segment** (on the good event):
`|#{k < N : u k ≤ a'/2^L} − N a'/2^L| ≤ L`, uniformly in `N`. -/
theorem abs_segErr_scrambledVdc_dyadic_le {f : ℕ → ℕ → Bool}
    (hf : ∀ k, NotEventuallyConst (scrambledDigit f k)) {L a' : ℕ}
    (hx1 : (a' : ℝ) / 2 ^ L ≤ 1) (N : ℕ) :
    |segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) 0 N| ≤ L := by
  have hx0 : (0 : ℝ) ≤ (a' : ℝ) / 2 ^ L := by positivity
  have hβ : ∀ m a, |segErr (scrambledVdc f) ((a' : ℝ) / 2 ^ L) (a * 2 ^ m) (2 ^ m)| ≤
      (if m < L then (1 : ℝ) else 0) := by
    intro m a
    split_ifs with hm
    · exact abs_segErr_scrambledVdc_block_le f m a hx0 hx1
    · rw [segErr_scrambledVdc_block_dyadic hf (not_lt.1 hm) hx1 a, abs_zero]
  set m := max L (Nat.log 2 N + 1)
  have hN : N < 2 ^ m := (Nat.lt_pow_succ_log_self (by norm_num) N).trans_le
    (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have h := abs_segErr_prefix_le hβ m 0 N hN
  rw [zero_mul] at h
  refine h.trans ?_
  rw [sum_boole]
  have : ((range m).filter fun j => j < L).card ≤ L := by
    calc ((range m).filter fun j => j < L).card ≤ (range L).card :=
          card_le_card fun j hj => by
            simp only [mem_filter, mem_range] at hj ⊢
            exact hj.2
      _ = L := card_range L
  exact_mod_cast this

/-! ### Chains with dyadic transition probabilities -/

/-- **Dyadic cumulative sums**: every `cs_{i,m}` is in `2^{-L} ℕ`. -/
def DyadicCumProb (P : Fin n → Fin n → ℝ) (L : ℕ) : Prop :=
  ∀ i (m : ℕ), ∃ a : ℕ, cumProb P i m = a / 2 ^ L

/-- Dyadic entries give dyadic cumulative sums. -/
theorem dyadicCumProb_of_entries {P : Fin n → Fin n → ℝ} {L : ℕ}
    (h : ∀ i j, ∃ a : ℕ, P i j = a / 2 ^ L) : DyadicCumProb P L := by
  intro i m
  choose A hA using h
  refine ⟨∑ k ∈ univ.filter (fun k : Fin n => (k : ℕ) < m), A i k, ?_⟩
  unfold cumProb
  push_cast
  rw [sum_div]
  exact sum_congr rfl fun k _ => hA i k

variable {P : Fin n → Fin n → ℝ}

/-- One dyadic threshold of a stack: `|#{k < N : step < m} − N cs_{i,m}| ≤ L` on the good
event. -/
theorem abs_departuresBelow_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (i : Fin n) {f : ℕ → ℕ → Bool} (hf : ∀ k, NotEventuallyConst (scrambledDigit f k))
    (N m : ℕ) :
    |(departuresBelow P i (scrambledVdc f) N m : ℝ) - N * cumProb P i m| ≤ L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : departuresBelow P i (scrambledVdc f) N 0 = 0 := by
      unfold departuresBelow
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _ hk
      exact Nat.not_lt_zero _ hk
    rw [h0, cumProb_zero, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    positivity
  have e : departuresBelow P i (scrambledVdc f) N m =
      ((range N).filter fun k => scrambledVdc f (0 + k) ≤ cumProb P i m).card := by
    unfold departuresBelow
    congr 1
    refine filter_congr fun k _ => ?_
    rw [zero_add]
    exact step_lt_iff hP i (scrambledVdc_mem_Icc f k).2 hm
  rw [e]
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc f) (cumProb P i m) 0 N
  rw [card_range] at h
  rw [h]
  obtain ⟨a', ha'⟩ := hdy i m
  have hx1 := (cumProb_mem_Icc hP i m).2
  rw [ha'] at hx1 ⊢
  exact abs_segErr_scrambledVdc_dyadic_le hf hx1 N

/-- **Dyadic chains: bounded transition errors** (on the good event, every `T`):
`|N_ij(T) − p_ij N_i(T)| ≤ 2L`. -/
theorem abs_transCount_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i j : Fin n) (T : ℕ) :
    |(transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
        P i j * occCount (stackPath P x₀ (scrambledStack f)) i T| ≤ 2 * L := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) i T
  rw [transCount_stackDrive]
  have hv : scrambledStack f i = scrambledVdc (f i) := rfl
  rw [hv, card_step_eq_eq_sub]
  have e : (departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) -
        departuresBelow P i (scrambledVdc (f i)) N j - P i j * N =
      ((departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)) -
        ((departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j) := by
    rw [cumProb_succ]
    ring
  rw [e]
  have h1 := abs_departuresBelow_dyadic_sub_le hP hdy i (hf i) N (j + 1)
  have h2 := abs_departuresBelow_dyadic_sub_le hP hdy i (hf i) N j
  calc _ ≤ |(departuresBelow P i (scrambledVdc (f i)) N (j + 1) : ℝ) - N * cumProb P i (j + 1)| +
        |(departuresBelow P i (scrambledVdc (f i)) N j : ℝ) - N * cumProb P i j| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Dyadic chains: bounded departure discrepancy**: `|D_i(g, T)| ≤ V(g) L` on the good
event. -/
theorem abs_departureDiscrepancy_dyadic_le (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f)
    (g : Fin n → ℝ) (i : Fin n) (T : ℕ) :
    |departureDiscrepancy P g (stackPath P x₀ (scrambledStack f)) i T| ≤ stateVariation g * L := by
  refine (congrArg abs (departureDiscrepancy_stackDrive P g (step P) x₀ (scrambledStack f) i
    T)).trans_le ?_
  refine abs_sum_step_sub_le_of_count hP i (fun k _ => (scrambledVdc_mem_Icc (f i) k).2)
    (fun m _ => ?_) g
  have h := card_filter_segment_sub_eq_segErr (scrambledVdc (f i)) (cumProb P i m) 0
    (occCount (stackPath P x₀ (scrambledStack f)) i T)
  simp only [zero_add] at h
  change |(((range (occCount (stackPath P x₀ (scrambledStack f)) i T)).filter
    fun k => scrambledVdc (f i) k ≤ cumProb P i m).card : ℝ) -
      (range (occCount (stackPath P x₀ (scrambledStack f)) i T)).card * cumProb P i m| ≤ L
  rw [h]
  obtain ⟨a', ha'⟩ := hdy i m
  have hx1 := (cumProb_mem_Icc hP i m).2
  rw [ha'] at hx1 ⊢
  exact abs_segErr_scrambledVdc_dyadic_le (hf i) hx1 _

/-- **Dyadic chains: bounded occupation error** (on the good event, uniformly in `T`):
`|N_s(T) − T π_s| ≤ 2M + n V(h) L`. -/
theorem abs_occCount_dyadic_sub_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {f : Fin n → ℕ → ℕ → Bool} (hf : IsGoodTable f) {h : Fin n → ℝ} {s : Fin n}
    {c M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c)
    (hM : ∀ i, |h i| ≤ M) (T : ℕ) :
    |(occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c| ≤
      2 * M + n * stateVariation h * L := by
  refine (abs_occCount_sub_le P hh hM _ T).trans (add_le_add le_rfl ?_)
  calc ∑ i, |departureDiscrepancy P h (stackPath P x₀ (scrambledStack f)) i T|
      ≤ ∑ _i : Fin n, stateVariation h * L :=
        sum_le_sum fun i _ => abs_departureDiscrepancy_dyadic_le hP hdy x₀ hf h i T
    _ = n * stateVariation h * L := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Under Owen scrambling, almost surely the occupation error of a dyadic chain is bounded by
`2M + n V(h) L` for all `T`. -/
theorem ae_abs_occCount_dyadic_owen_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂owenMeasure n, ∀ T,
      |(occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c| ≤
        2 * M + n * stateVariation h * L :=
  (ae_isGoodTable_owen n).mono fun _ hω T => abs_occCount_dyadic_sub_le hP hdy x₀ hω hh hM T

/-- Under the digital shift, almost surely the occupation error of a dyadic chain is bounded
by `2M + n V(h) L` for all `T`. -/
theorem ae_abs_occCount_dyadic_shift_le (hP : IsStochastic P) {L : ℕ} (hdy : DyadicCumProb P L)
    (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ ω ∂shiftMeasure n, ∀ T,
      |(occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c| ≤
        2 * M + n * stateVariation h * L :=
  (ae_isGoodTable_shift n).mono fun _ hω T => abs_occCount_dyadic_sub_le hP hdy x₀ hω hh hM T

/-- **No CLT for a dyadic chain under Owen scrambling**: no normalisation
`(N_s(T) − T π_s − b_T) / a_T` converges in distribution to a law without atoms. -/
theorem not_tendstoInDistribution_occCount_owen (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c - b T) / a T)
      atTop Z (fun _ => owenMeasure n) μ' := by
  have := not_tendstoInDistribution_of_abs_sub_le (μ := owenMeasure n)
    (Y := fun T ω => (occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℤ))
    (y := fun T => T * c) (C := 2 * M + n * stateVariation h * L)
    (fun T => (ae_abs_occCount_dyadic_owen_le hP hdy x₀ hh hM).mono fun ω hω => by
      simpa only [Int.cast_natCast] using hω T) a b hZ
  simpa only [Int.cast_natCast] using this

/-- **No CLT for a dyadic chain under the digital shift.** -/
theorem not_tendstoInDistribution_occCount_shift (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℝ) - T * c - b T) / a T)
      atTop Z (fun _ => shiftMeasure n) μ' := by
  have := not_tendstoInDistribution_of_abs_sub_le (μ := shiftMeasure n)
    (Y := fun T ω => (occCount (stackPath P x₀ (scrambledStack (shiftFlips ω))) s T : ℤ))
    (y := fun T => T * c) (C := 2 * M + n * stateVariation h * L)
    (fun T => (ae_abs_occCount_dyadic_shift_le hP hdy x₀ hh hM).mono fun ω hω => by
      simpa only [Int.cast_natCast] using hω T) a b hZ
  simpa only [Int.cast_natCast] using this

/-- The standard normal law has no atoms. -/
theorem map_id_gaussianReal_singleton (x : ℝ) : (gaussianReal 0 1).map id {x} = 0 := by
  rw [Measure.map_id]
  exact (nullSingletonClass_gaussianReal one_ne_zero).measure_singleton x

/-- **No normalisation of a dyadic chain's occupation error is asymptotically `N(0,1)`** under
Owen scrambling. -/
theorem not_tendstoInDistribution_occCount_owen_gaussian (hP : IsStochastic P) {L : ℕ}
    (hdy : DyadicCumProb P L) (x₀ : Fin n) {h : Fin n → ℝ} {s : Fin n} {c M : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (hM : ∀ i, |h i| ≤ M)
    (a b : ℕ → ℝ) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath P x₀ (scrambledStack (owenTable ω))) s T : ℝ) - T * c - b T) / a T)
      atTop id (fun _ => owenMeasure n) (gaussianReal 0 1) :=
  not_tendstoInDistribution_occCount_owen hP hdy x₀ hh hM a b map_id_gaussianReal_singleton

/-! ### The post's two-state chain, `p₁₁ = p₂₂ = 7/8` -/

/-- The two-state chain of post #3 with `p₁₁ = p₂₂ = 7/8` (mean spell length `8`). -/
noncomputable def stackChain78 : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 7 / 8 else 1 / 8

/-- `stackChain78` is stochastic. -/
theorem isStochastic_stackChain78 : IsStochastic stackChain78 where
  nonneg i j := by unfold stackChain78; split_ifs <;> norm_num
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [stackChain78] <;> norm_num

/-- Its entries are multiples of `2^{-3}`. -/
theorem dyadicCumProb_stackChain78 : DyadicCumProb stackChain78 3 :=
  dyadicCumProb_of_entries fun i j => ⟨if i = j then 7 else 1, by
    unfold stackChain78
    split_ifs <;> norm_num⟩

/-- The solution `h = (2, −2)` of Poisson's equation `h − Ph = 1_{0} − 1/2`. -/
noncomputable def poisson78 : Fin 2 → ℝ := fun i => if i = 0 then 2 else -2

/-- `h = (2, −2)` solves `h − Ph = 1_{0} − 1/2`. -/
theorem poisson78_spec (i : Fin 2) :
    poisson78 i - (stackChain78 *ᵥ poisson78) i = (if i = 0 then 1 else 0) - 1 / 2 := by
  fin_cases i <;> simp [poisson78, stackChain78, mulVec, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- `|h| ≤ 2`. -/
theorem abs_poisson78_le (i : Fin 2) : |poisson78 i| ≤ 2 := by
  unfold poisson78
  split_ifs <;> norm_num

/-- `V(h) = 4`. -/
theorem stateVariation_poisson78 : stateVariation poisson78 = 4 := by
  simp [stateVariation, extendNat, poisson78]
  norm_num

/-- **The two-state 7/8 chain: bounded occupation error** for every good flip table:
`|N_0(T) − T/2| ≤ 28` for all `T` (Owen scrambling and digital shift alike). -/
theorem abs_occCount_stackChain78_le (x₀ : Fin 2) {f : Fin 2 → ℕ → ℕ → Bool}
    (hf : IsGoodTable f) (T : ℕ) :
    |(occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T : ℝ) - T / 2| ≤ 28 := by
  have h := abs_occCount_dyadic_sub_le isStochastic_stackChain78 dyadicCumProb_stackChain78 x₀
    hf poisson78_spec abs_poisson78_le T
  rw [stateVariation_poisson78] at h
  rw [div_eq_mul_one_div (T : ℝ) 2]
  norm_num at h ⊢
  linarith

/-- **A fixed finite set of values** (post #3, "every spell lasts exactly 8 periods"): on the
good event, `N_0(T) − T/2 ∈ {k/2 : |k| ≤ 56}` for every `T`. -/
theorem occCount_stackChain78_mem (x₀ : Fin 2) {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f)
    (T : ℕ) : (occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T : ℝ) - T / 2 ∈
      (Finset.Icc (-56 : ℤ) 56).image fun k : ℤ => (k : ℝ) / 2 := by
  set N := occCount (stackPath stackChain78 x₀ (scrambledStack f)) 0 T
  have h := abs_occCount_stackChain78_le x₀ hf T
  refine mem_image.2 ⟨2 * N - T, ?_, by push_cast; ring⟩
  have h2 : |((2 * N - T : ℤ) : ℝ)| ≤ 56 := by
    push_cast
    rw [show (2 : ℝ) * N - T = 2 * ((N : ℝ) - T / 2) by ring, abs_mul, abs_two]
    linarith
  rw [abs_le] at h2
  have h3 : (-56 : ℤ) ≤ 2 * N - T := by exact_mod_cast h2.1
  have h4 : (2 * N - T : ℤ) ≤ 56 := by exact_mod_cast h2.2
  exact Finset.mem_Icc.2 ⟨h3, h4⟩

/-- **No CLT for the 7/8 chain under Owen scrambling** (post #3, code (iii)). -/
theorem not_tendstoInDistribution_stackChain78_owen (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath stackChain78 x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) -
        T * (1 / 2) - b T) / a T) atTop Z (fun _ => owenMeasure 2) μ' :=
  not_tendstoInDistribution_occCount_owen isStochastic_stackChain78 dyadicCumProb_stackChain78
    x₀ poisson78_spec abs_poisson78_le a b hZ

/-- **No CLT for the 7/8 chain under the digital shift** (post #3, code (ii)). -/
theorem not_tendstoInDistribution_stackChain78_shift (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ}
    (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath stackChain78 x₀ (scrambledStack (shiftFlips ω))) 0 T : ℝ) -
        T * (1 / 2) - b T) / a T) atTop Z (fun _ => shiftMeasure 2) μ' :=
  not_tendstoInDistribution_occCount_shift isStochastic_stackChain78 dyadicCumProb_stackChain78
    x₀ poisson78_spec abs_poisson78_le a b hZ

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # The symmetric two-state chain at `T = 2^k`: bounded error for every scramble

Post #3 reports that "in the five-state chain normality cannot be rejected for the per-state
Sobol sequences ((ii) and (iii))", while "the RQMC estimators are typically not normally
distributed". For the symmetric two-state chain `p₁₁ = p₂₂ = p` (`symChain p`, `π = (1/2, 1/2)`)
and **any** `p ∈ [0, 1)`, dyadic or not, the occupation error is bounded along `T = 2^k`, for
every flip table (Owen scrambling and digital shift alike, no good event needed).

**Self-consistent bound** (`abs_occCount_symChain_pow_two_le`). Write `N_0 + N_1 = T = 2H`,
`H = 2^{k-1}`, `N_0 = H ± d`. The departures from `0` going to `1` and from `1` going to `0`
are threshold counts (`transCount_zero_one_eq`, `transCount_one_zero_eq`):
`N_{01} = N_0 − (N_0 p + E_0(N_0))`, `N_{10} = N_1 (1−p) + E_1(N_1)`, where `E_i(N)` is the
counting error of the first `N` points of stack `i`. Flow balance gives `|N_{01} − N_{10}| ≤ 1`,
so `2(1−p) d ≤ 1 + |E_0(N_0)| + |E_1(N_1)|`. Each `E_i(H)` is one aligned block (error `≤ 1`),
and `N_i` differs from `H` by a segment of length `d` (segment lemma, error `≤ 2⌊log₂ d⌋ + 3`):
`2(1−p) d ≤ 9 + 4 ⌊log₂ d⌋`, which bounds `d` (`exists_le_of_mul_le_log`).

**No CLT along all `T`** (`not_tendstoInDistribution_symChain_owen`,
`not_tendstoInDistribution_symChain_shift`, and for the post's style of non-dyadic chain
`not_tendstoInDistribution_symChain_twoThirds_owen`): along `T = 2^k` the error takes at most
`⌊2C⌋ + 1` values, so no normalisation `(N_0(T) − T/2 − b_T)/a_T` converges in distribution to a
law without atoms along all `T`.

**Correction** (post #3, "normality cannot be rejected"): for the per-state Sobol stacks the
error law does not converge along all `T`, even for non-dyadic transition probabilities such
as `p = 2/3`; normality can only hold along sequences of `T` with growing variance (in
simulations, not formalised: variance `≈ 1.9` at every `T = 2^k`, growing like `log T` at
`T = ⌊0.6 · 2^k⌋ + 1`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Finset Matrix Filter Topology

/-! ### A self-consistent logarithmic bound -/

/-- **`c d ≤ A + B ⌊log₂ d⌋` bounds `d`**: for `c > 0`, `B ≥ 0` there is `D` with `d ≤ D`
whenever `c d ≤ A + B ⌊log₂ d⌋`. -/
theorem exists_le_of_mul_le_log {c A B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ D : ℝ, ∀ d : ℕ, c * d ≤ A + B * Nat.log 2 d → (d : ℝ) ≤ D := by
  have hε : 0 < c / (4 * (B + 1)) := by positivity
  obtain ⟨d₀, hd₀⟩ := (tendsto_natCast_atTop_atTop.eventually
    (Real.isLittleO_log_id_atTop.bound hε)).exists_forall_of_atTop
  refine ⟨max d₀ (2 * (A + B) / c), fun d hd => ?_⟩
  rcases lt_or_ge d (max d₀ 1) with hsmall | hlarge
  · have : (d : ℝ) ≤ d₀ ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · exact Or.inr h0
      · left
        have : d < d₀ := by omega
        exact_mod_cast this.le
    rcases this with h | h
    · exact h.trans (le_max_left _ _)
    · rw [h, Nat.cast_zero]
      exact (Nat.cast_nonneg d₀).trans (le_max_left _ _)
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog := hd₀ d (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hdR),
    abs_of_nonneg (by linarith)] at hlog
  have h2 := natLog_two_add_one_le (by omega : 0 < d)
  have h3 : B * Nat.log 2 d ≤ B * (2 * Real.log d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  have h4 : B * (2 * Real.log d) ≤ c / 2 * d := by
    have h5 : B * (2 * Real.log d) ≤ (B + 1) * (2 * (c / (4 * (B + 1)) * d)) := by
      have := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * (B + 1))
      nlinarith [Real.log_nonneg hdR]
    have h6 : (B + 1) * (2 * (c / (4 * (B + 1)) * d)) = c / 2 * d := by
      field_simp
      ring
    linarith
  have : c / 2 * d ≤ A + B := by nlinarith
  refine le_trans ?_ (le_max_right _ _)
  rw [le_div_iff₀ hc]
  linarith

/-! ### The symmetric two-state chain -/

/-- The symmetric two-state chain `p₁₁ = p₂₂ = p`. -/
noncomputable def symChain (p : ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then p else 1 - p

/-- `symChain p` is stochastic for `p ∈ [0,1]`. -/
theorem isStochastic_symChain {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsStochastic (symChain p) where
  nonneg i j := by unfold symChain; split_ifs <;> linarith
  sum_eq_one i := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [symChain]

/-- The first cumulative sum of a row of a two-state matrix is its first entry. -/
theorem cumProb_one_fin_two (P : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : cumProb P i 1 = P i 0 := by
  have h := cumProb_succ P i 0
  simp only [Fin.val_zero, zero_add, cumProb_zero] at h
  exact h

/-- Threshold counts as counting errors: `#{k < N : u k ≤ x} = N x + segErr u x 0 N`. -/
theorem card_filter_le_eq_add_segErr (u : ℕ → ℝ) (x : ℝ) (N : ℕ) :
    (((range N).filter fun k => u k ≤ x).card : ℝ) = N * x + segErr u x 0 N := by
  rw [segErr_eq_card]
  simp only [zero_add]
  ring

/-- **Departures `0 → 1` of a two-state stack path**: `N_{01}(T) = N_0 − #{k < N_0 : u k ≤
cs_{0,1}}`. -/
theorem transCount_zero_one_eq {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    (transCount (stackPath P x₀ (scrambledStack f)) 0 1 T : ℝ) =
      occCount (stackPath P x₀ (scrambledStack f)) 0 T -
        (((range (occCount (stackPath P x₀ (scrambledStack f)) 0 T)).filter
          fun k => scrambledVdc (f 0) k ≤ cumProb P 0 1).card : ℝ) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) 0 T
  rw [transCount_stackDrive]
  have h := card_filter_step_eq_eq_sub P 0 (scrambledStack f 0) (range N) 1
  have h2 : (range N).filter (fun k => (step P 0 (scrambledStack f 0 k) : ℕ) < (1 : Fin 2) + 1) =
      range N := filter_true_of_mem fun k _ => (step P 0 (scrambledStack f 0 k)).isLt
  have h1 : (range N).filter (fun k => (step P 0 (scrambledStack f 0 k) : ℕ) < (1 : Fin 2)) =
      (range N).filter fun k => scrambledVdc (f 0) k ≤ cumProb P 0 1 :=
    filter_congr fun k _ => step_lt_iff hP 0 (scrambledVdc_mem_Icc (f 0) k).2 le_rfl
  rw [h2, h1, card_range] at h
  exact h

/-- **Departures `1 → 0` of a two-state stack path**: `N_{10}(T) = #{k < N_1 : u k ≤
cs_{1,1}}`. -/
theorem transCount_one_zero_eq {P : Fin 2 → Fin 2 → ℝ} (hP : IsStochastic P) (x₀ : Fin 2)
    (f : Fin 2 → ℕ → ℕ → Bool) (T : ℕ) :
    (transCount (stackPath P x₀ (scrambledStack f)) 1 0 T : ℝ) =
        (((range (occCount (stackPath P x₀ (scrambledStack f)) 1 T)).filter
          fun k => scrambledVdc (f 1) k ≤ cumProb P 1 1).card : ℝ) := by
  set N := occCount (stackPath P x₀ (scrambledStack f)) 1 T
  rw [transCount_stackDrive]
  have h := card_filter_step_eq_eq_sub P 1 (scrambledStack f 1) (range N) 0
  have h0 : (range N).filter (fun k => (step P 1 (scrambledStack f 1 k) : ℕ) < (0 : Fin 2)) =
      ∅ := filter_eq_empty_iff.2 fun k _ hk => Nat.not_lt_zero _ hk
  have h1 : (range N).filter (fun k => (step P 1 (scrambledStack f 1 k) : ℕ) < (0 : Fin 2) + 1) =
      (range N).filter fun k => scrambledVdc (f 1) k ≤ cumProb P 1 1 :=
    filter_congr fun k _ => step_lt_iff hP 1 (scrambledVdc_mem_Icc (f 1) k).2 le_rfl
  rw [h0, h1, card_empty, Nat.cast_zero, sub_zero] at h
  exact h

/-- **Initial segments of different lengths** differ by a segment:
`|E(N) − E(H)| ≤ 2 ⌊log₂ |N − H|⌋ + 3`. -/
theorem abs_segErr_zero_sub_le (f : ℕ → ℕ → Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N H : ℕ) : |segErr (scrambledVdc f) x 0 N - segErr (scrambledVdc f) x 0 H| ≤
      2 * (Nat.log 2 (N - H + (H - N)) : ℝ) + 3 := by
  rcases le_total H N with hHN | hNH
  · have e : N = H + (N - H) := by omega
    have hd : N - H + (H - N) = N - H := by omega
    rw [hd, e, segErr_add, zero_add, add_sub_cancel_left]
    have := abs_segErr_scrambledVdc_log_le f hx0 hx1 H (N - H)
    simpa only [Nat.add_sub_cancel_left] using this
  · have e : H = N + (H - N) := by omega
    have hd : N - H + (H - N) = H - N := by omega
    rw [hd, e, segErr_add, zero_add, sub_add_cancel_left, abs_neg]
    have := abs_segErr_scrambledVdc_log_le f hx0 hx1 N (H - N)
    simpa only [Nat.add_sub_cancel_left] using this

/-- **The occupation error at `T = 2^k` is bounded, for every flip table** (any `p ∈ [0,1)`):
there is `C` (depending only on `p`) with `|N_0(2^k) − 2^k/2| ≤ C` for all `k`, all flip
tables and both starting states. -/
theorem abs_occCount_symChain_pow_two_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ C : ℝ, ∀ (f : Fin 2 → ℕ → ℕ → Bool) (x₀ : Fin 2) (k : ℕ),
      |(occCount (stackPath (symChain p) x₀ (scrambledStack f)) 0 (2 ^ k) : ℝ) - 2 ^ k / 2| ≤
        C := by
  obtain ⟨D, hD⟩ := exists_le_of_mul_le_log (c := 2 * (1 - p)) (A := 9) (B := 4)
    (by linarith) (by norm_num)
  refine ⟨max D 1, fun f x₀ k => ?_⟩
  have hP := isStochastic_symChain hp0 hp1.le
  set path := stackPath (symChain p) x₀ (scrambledStack f) with hpath
  set N0 := occCount path 0 (2 ^ k) with hN0
  set N1 := occCount path 1 (2 ^ k) with hN1
  have hsum : N0 + N1 = 2 ^ k := by
    have := sum_occCount path (2 ^ k)
    rwa [Fin.sum_univ_two] at this
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `T = 1`
    have h1 : N0 ≤ 1 := by rw [pow_zero] at hsum; omega
    refine le_trans ?_ (le_max_right _ _)
    rw [pow_zero, abs_le]
    have : (N0 : ℝ) ≤ 1 := by exact_mod_cast h1
    constructor <;> [linarith [Nat.cast_nonneg (α := ℝ) N0]; linarith]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set H := 2 ^ m with hH
  have hsum' : N0 + N1 = 2 * H := by rw [hsum, pow_succ, mul_comm]
  set d := N0 - H + (H - N0) with hd
  have hd1 : N1 - H + (H - N1) = d := by omega
  -- flow balance
  have hflow :
      |(transCount path 0 1 (2 ^ (m + 1)) : ℝ) - transCount path 1 0 (2 ^ (m + 1))| ≤ 1 := by
    have h := abs_flowBalance_le path 0 (2 ^ (m + 1))
    rw [Fin.sum_univ_two, Fin.sum_univ_two, abs_le] at h
    push_cast at h
    have hz1 : -1 ≤ (transCount path 0 1 (2 ^ (m + 1)) : ℤ) - transCount path 1 0 (2 ^ (m + 1)) :=
      by omega
    have hz2 : (transCount path 0 1 (2 ^ (m + 1)) : ℤ) - transCount path 1 0 (2 ^ (m + 1)) ≤ 1 :=
      by omega
    rw [abs_le]
    constructor
    · exact_mod_cast hz1
    · exact_mod_cast hz2
  -- the two threshold identities
  have hc0 : cumProb (symChain p) 0 1 = p := by rw [cumProb_one_fin_two]; simp [symChain]
  have hc1 : cumProb (symChain p) 1 1 = 1 - p := by rw [cumProb_one_fin_two]; simp [symChain]
  have h01 := transCount_zero_one_eq hP x₀ f (2 ^ (m + 1))
  have h10 := transCount_one_zero_eq hP x₀ f (2 ^ (m + 1))
  rw [hc0, card_filter_le_eq_add_segErr] at h01
  rw [hc1, card_filter_le_eq_add_segErr] at h10
  set E0 := segErr (scrambledVdc (f 0)) p 0 N0
  set E1 := segErr (scrambledVdc (f 1)) (1 - p) 0 N1
  -- the errors at `H` (one aligned block) and the segments of length `d`
  have hB0 : |segErr (scrambledVdc (f 0)) p 0 H| ≤ 1 := by
    have := abs_segErr_scrambledVdc_block_le (f 0) m 0 hp0 hp1.le
    rwa [zero_mul] at this
  have hB1 : |segErr (scrambledVdc (f 1)) (1 - p) 0 H| ≤ 1 := by
    have := abs_segErr_scrambledVdc_block_le (f 1) m 0 (x := 1 - p) (by linarith)
      (by linarith)
    rwa [zero_mul] at this
  have hS0 := abs_segErr_zero_sub_le (f 0) hp0 hp1.le N0 H
  have hS1 := abs_segErr_zero_sub_le (f 1) (x := 1 - p) (by linarith) (by linarith) N1 H
  rw [← hd] at hS0
  rw [hd1] at hS1
  have hE0 : |E0| ≤ 1 + (2 * (Nat.log 2 d : ℝ) + 3) := by
    have := abs_sub_abs_le_abs_sub E0 (segErr (scrambledVdc (f 0)) p 0 H)
    linarith
  have hE1 : |E1| ≤ 1 + (2 * (Nat.log 2 d : ℝ) + 3) := by
    have := abs_sub_abs_le_abs_sub E1 (segErr (scrambledVdc (f 1)) (1 - p) 0 H)
    linarith
  -- `|N0 − N1| = 2 d` and `|N0 − H| = d`
  have hdabs : |(N0 : ℝ) - H| = d := by
    rcases le_total H N0 with h | h
    · have e : (d : ℝ) = N0 - H := by
        rw [hd, show H - N0 = 0 by omega, add_zero, Nat.cast_sub h]
      rw [e, abs_of_nonneg (by linarith)]
    · have e : (d : ℝ) = H - N0 := by
        rw [hd, show N0 - H = 0 by omega, zero_add, Nat.cast_sub h]
      rw [e, abs_of_nonpos (by linarith), neg_sub]
  have hN1R : (N1 : ℝ) = 2 * H - N0 := by
    have : ((N0 + N1 : ℕ) : ℝ) = ((2 * H : ℕ) : ℝ) := by rw [hsum']
    push_cast at this
    linarith
  -- the self-consistent inequality
  have key : (1 - p) * ((N0 : ℝ) - N1) =
      ((transCount path 0 1 (2 ^ (m + 1)) : ℝ) - transCount path 1 0 (2 ^ (m + 1))) + E0 + E1 := by
    rw [h01, h10]
    ring
  have hineq : 2 * (1 - p) * d ≤ 9 + 4 * Nat.log 2 d := by
    have h1 : |(1 - p) * ((N0 : ℝ) - N1)| = 2 * (1 - p) * d := by
      rw [hN1R, show (N0 : ℝ) - (2 * H - N0) = 2 * ((N0 : ℝ) - H) by ring, abs_mul, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < 1 - p), abs_two, hdabs]
      ring
    have h2 := abs_add_le (((transCount path 0 1 (2 ^ (m + 1)) : ℝ) -
      transCount path 1 0 (2 ^ (m + 1))) + E0) E1
    have h3 := abs_add_le ((transCount path 0 1 (2 ^ (m + 1)) : ℝ) -
      transCount path 1 0 (2 ^ (m + 1))) E0
    rw [← key, h1] at h2
    linarith
  have hdD := hD d hineq
  rw [show ((2 : ℝ) ^ (m + 1)) / 2 = H by rw [hH, pow_succ]; push_cast; ring, hdabs]
  exact hdD.trans (le_max_left _ _)

/-- Along a subsequence `T = 2^k`, convergence in distribution is inherited. -/
theorem tendstoInDistribution_comp_pow_two {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {W : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution W atTop Z (fun _ => μ) μ') :
    TendstoInDistribution (fun k => W (2 ^ k)) atTop Z (fun _ => μ) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (2 ^ k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **No CLT along all `T` for the symmetric chain**, under any randomisation of the flip
tables: if every realisation of `ω ↦ f ω` is a flip table, no normalisation
`(N_0(T) − T/2 − b_T)/a_T` converges in distribution to a law without atoms. -/
theorem not_tendstoInDistribution_symChain {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (x₀ : Fin 2)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (F : Ω → Fin 2 → ℕ → ℕ → Bool) (a b : ℕ → ℝ) {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (F ω))) 0 T : ℝ) - T / 2 - b T) /
        a T) atTop Z (fun _ => μ) μ' := by
  intro h
  obtain ⟨C, hC⟩ := abs_occCount_symChain_pow_two_le hp0 hp1
  have h2 := tendstoInDistribution_comp_pow_two h
  refine not_tendstoInDistribution_of_abs_sub_le (μ := μ)
    (Y := fun k ω => (occCount (stackPath (symChain p) x₀ (scrambledStack (F ω))) 0 (2 ^ k) : ℤ))
    (y := fun k => (2 : ℝ) ^ k / 2) (C := C)
    (fun k => Eventually.of_forall fun ω => by simpa only [Int.cast_natCast] using hC (F ω) x₀ k)
    (fun k => a (2 ^ k)) (fun k => b (2 ^ k)) hZ ?_
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] using h2

/-- **No CLT along all `T`, Owen scrambling** (post #3, code (iii)), for any `p ∈ [0,1)`. -/
theorem not_tendstoInDistribution_symChain_owen {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) - T / 2 -
        b T) / a T) atTop Z (fun _ => owenMeasure 2) μ' :=
  not_tendstoInDistribution_symChain hp0 hp1 x₀ owenTable a b hZ

/-- **No CLT along all `T`, digital shift** (post #3, code (ii)), for any `p ∈ [0,1)`. -/
theorem not_tendstoInDistribution_symChain_shift {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (x₀ : Fin 2) (a b : ℕ → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} (hZ : ∀ x, μ'.map Z {x} = 0) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain p) x₀ (scrambledStack (shiftFlips ω))) 0 T : ℝ) - T / 2 -
        b T) / a T) atTop Z (fun _ => shiftMeasure 2) μ' :=
  not_tendstoInDistribution_symChain hp0 hp1 x₀ shiftFlips a b hZ

/-- **The non-dyadic chain `p = 2/3`**: no normalisation of `N_0(T) − T/2` is asymptotically
`N(0,1)` along all `T` under Owen scrambling. -/
theorem not_tendstoInDistribution_symChain_twoThirds_owen (x₀ : Fin 2) (a b : ℕ → ℝ) :
    ¬ TendstoInDistribution (fun T ω =>
      ((occCount (stackPath (symChain (2 / 3)) x₀ (scrambledStack (owenTable ω))) 0 T : ℝ) -
        T / 2 - b T) / a T) atTop id (fun _ => owenMeasure 2) (gaussianReal 0 1) :=
  not_tendstoInDistribution_symChain_owen (by norm_num) (by norm_num) x₀ a b
    map_id_gaussianReal_singleton

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-! # Spells of the 7/8 chain driven by scrambled stacks (post #3, codes (ii) and (iii))

Post #3: with per-state Sobol stacks, digitally shifted (ii) or Owen-scrambled (iii), "in the
two-state chain every spell lasts exactly 8 periods, rather than being geometric with mean 8".
`MarkovDriving` proved this only for rotors (`rotor78_spells_not_geometric`). Here it is proved
for both randomisations, on the good event (probability one), in the corrected form below.

**Mechanism.** For `stackChain78` the departure `k` from state `0` leaves iff the stack point
exceeds `7/8`, i.e. (on the good event) iff its first 3 scrambled digits are `111`; from state
`1` it leaves iff the point is `≤ 1/8`, i.e. iff they are `000` (`stay78_iff`). The first 3
scrambled digits depend only on `k mod 8` and run over all of `{0,1}^3` on each aligned block of
8 (`StackNet`), so there is one residue `r_i < 8` such that departure `k` from `i` leaves iff
`k ≡ r_i (mod 8)` (`exists_leaveResidue78`), the same in every block.

**Spells.** In a stack path, a stay in state `i` uses consecutive entries of stack `i`
(`stackPath_stay_iff`), and a spell after the first one in `i` starts right after a leaving
departure (`not_stay_prev_of_spellStart`). Hence (`spells_stackChain78`), for every good flip
table, every starting state and every state `i`, there is `r < 8` with
* the first spell in `i` lasting exactly `r + 1` periods (`runLength = r + 1`), and
* every later spell in `i` lasting exactly `8` periods.
**Law of `r`** (`owen_firstSpell78`, `shift_firstSpell78`, and for a chain started in `i`
`owen_runLength_first78`, `shift_runLength_first78`): `r` is uniform on `{0, …, 7}` under Owen
scrambling and under the digital shift: the first spell length is uniform on `{1, …, 8}`, with
mean `4.5`, not geometric with mean `8`.

**Correction** (post #3, "every spell lasts exactly 8 periods"): every spell *except the first
one in each state* lasts exactly 8 periods; the first spell in state `i` lasts `r_i + 1` periods
with `r_i` uniform on `{0, …, 7}`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory Finset

/-! ### Dyadic comparisons and the leaving residue -/

/-- On non-eventually-constant digits, `x ≤ a / 2^m` iff the first `m` digits are below `a`. -/
theorem binaryVal_le_div_iff {b : ℕ → Bool} (hb : NotEventuallyConst b) (a m : ℕ) :
    binaryVal b ≤ (a : ℝ) / 2 ^ m ↔ digitPrefix b m < a := by
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  constructor
  · intro h
    by_contra hcon
    have hk : (a : ℝ) ≤ (digitPrefix b m : ℕ) := by exact_mod_cast not_lt.1 hcon
    have h2 := digitPrefix_div_lt_binaryVal hb m
    have h3 : (a : ℝ) / 2 ^ m ≤ (digitPrefix b m : ℝ) / 2 ^ m :=
      div_le_div_of_nonneg_right hk hp.le
    linarith
  · intro h
    have hk : ((digitPrefix b m : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast h
    exact (binaryVal_le_digitPrefix_add_one_div b m).trans
      (div_le_div_of_nonneg_right hk hp.le)

/-- The scrambled digit prefix that makes a departure from `i` leave: `111` (`= 7`) from
state `0`, `000` (`= 0`) from state `1`. -/
def leaveTarget78 (i : Fin 2) : ℕ := if i = 0 then 7 else 0

/-- `cs_{0,1} = 7/8` and `cs_{1,1} = 1/8` for `stackChain78`. -/
theorem cumProb_stackChain78_one (i : Fin 2) :
    cumProb stackChain78 i 1 = ((if i = 0 then 7 else 1 : ℕ) : ℝ) / 2 ^ 3 := by
  have h := cumProb_succ stackChain78 i 0
  simp only [Fin.val_zero, zero_add, cumProb_zero] at h
  rw [h]
  fin_cases i <;> simp [stackChain78] <;> norm_num

/-- From state `0` of the 7/8 chain a departure stays iff its first 3 scrambled digits are not
`111` (good event). -/
theorem stay78_zero_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (k : ℕ) :
    step stackChain78 0 (scrambledStack f 0 k) = 0 ↔
      digitPrefix (scrambledDigit (f 0) k) 3 ≠ 7 := by
  have hlt := step_lt_iff isStochastic_stackChain78 0 (scrambledStack_mem_Icc f 0 k).2
    (le_refl 1)
  have hc : cumProb stackChain78 0 1 = ((7 : ℕ) : ℝ) / 2 ^ 3 := by
    rw [cumProb_stackChain78_one]
    rfl
  rw [hc] at hlt
  have hb := binaryVal_le_div_iff (hf 0 k) 7 3
  have h8 : digitPrefix (scrambledDigit (f 0) k) 3 < 8 := digitPrefix_lt _ 3
  change ((step stackChain78 0 (binaryVal (scrambledDigit (f 0) k)) : ℕ) < 1 ↔
    binaryVal (scrambledDigit (f 0) k) ≤ ((7 : ℕ) : ℝ) / 2 ^ 3) at hlt
  change step stackChain78 0 (binaryVal (scrambledDigit (f 0) k)) = 0 ↔ _
  have key := hlt.trans hb
  rw [Fin.ext_iff, Fin.val_zero]
  omega

/-- From state `1` of the 7/8 chain a departure stays iff its first 3 scrambled digits are not
`000` (good event). -/
theorem stay78_one_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (k : ℕ) :
    step stackChain78 1 (scrambledStack f 1 k) = 1 ↔
      digitPrefix (scrambledDigit (f 1) k) 3 ≠ 0 := by
  have hlt := step_lt_iff isStochastic_stackChain78 1 (scrambledStack_mem_Icc f 1 k).2
    (le_refl 1)
  have hc : cumProb stackChain78 1 1 = ((1 : ℕ) : ℝ) / 2 ^ 3 := by
    rw [cumProb_stackChain78_one]
    rfl
  rw [hc] at hlt
  have hb := binaryVal_le_div_iff (hf 1 k) 1 3
  change ((step stackChain78 1 (binaryVal (scrambledDigit (f 1) k)) : ℕ) < 1 ↔
    binaryVal (scrambledDigit (f 1) k) ≤ ((1 : ℕ) : ℝ) / 2 ^ 3) at hlt
  change step stackChain78 1 (binaryVal (scrambledDigit (f 1) k)) = 1 ↔ _
  have key := hlt.trans hb
  have h2 := (step stackChain78 1 (binaryVal (scrambledDigit (f 1) k))).isLt
  rw [Fin.ext_iff, Fin.val_one]
  omega

/-- **When a departure stays** (good event): departure `k` from `i` stays in `i` iff the first
3 scrambled digits of stack point `k` differ from `leaveTarget78 i`. -/
theorem stay78_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) (k : ℕ) :
    step stackChain78 i (scrambledStack f i k) = i ↔
      digitPrefix (scrambledDigit (f i) k) 3 ≠ leaveTarget78 i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · exact stay78_zero_iff hf k
  · exact stay78_one_iff hf k

/-- **The leaving residue** (good event): there is `r < 8` such that departure `k` from `i`
leaves iff `k ≡ r (mod 8)`. -/
theorem exists_leaveResidue78 {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) :
    ∃ r < 8, ∀ k, step stackChain78 i (scrambledStack f i k) ≠ i ↔ k % 8 = r := by
  have himg := image_digitPrefix_scrambledDigit_block (f i) 0 3
  have ht : leaveTarget78 i ∈ range (2 ^ 3) := by
    rw [mem_range]
    unfold leaveTarget78
    split_ifs <;> norm_num
  rw [← himg] at ht
  obtain ⟨r, hr, hrt⟩ := mem_image.1 ht
  simp only [zero_mul, zero_add] at hrt
  refine ⟨r, by simpa using hr, fun k => ?_⟩
  rw [Ne, stay78_iff hf i k, not_not, ← digitPrefix_scrambledDigit_mod (f i) k 3, ← hrt]
  constructor
  · intro h
    have := injOn_digitPrefix_scrambledDigit (f i) 3
      (mem_range.2 (Nat.mod_lt k (by norm_num))) hr h
    simpa using this
  · intro h
    rw [show 2 ^ 3 = 8 by norm_num, h]

/-! ### Runs in a stack path -/

variable {n : ℕ}

/-- While the path stays in `i`, its occupation count of `i` grows by one per period. -/
theorem occCount_add_of_forall_eq {S : Type*} [DecidableEq S] (path : ℕ → S) {i : S} {t : ℕ} :
    ∀ m, (∀ m' < m, path (t + m') = i) → occCount path i (t + m) = occCount path i t + m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [← add_assoc, occCount_succ, ih fun m' hm' => h m' (by omega), h m (by omega)]
    simp only [ite_true]
    ring

/-- **A stay uses consecutive stack entries**: from `path t = i`, the path stays in `i` at
`t, …, t + m` iff the departures `N_i(t), …, N_i(t) + m − 1` from `i` all stay. -/
theorem stackPath_stay_iff (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) {i : Fin n}
    {t : ℕ} (ht : stackPath P x₀ v t = i) (m : ℕ) :
    (∀ m' ≤ m, stackPath P x₀ v (t + m') = i) ↔
      ∀ m' < m, step P i (v i (occCount (stackPath P x₀ v) i t + m')) = i := by
  induction m with
  | zero =>
    simp only [Nat.le_zero, forall_eq, add_zero, ht, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true]
  | succ m ih =>
    constructor
    · intro h m' hm'
      have hrun : ∀ m'' < m + 1, stackPath P x₀ v (t + m'') = i := fun m'' h'' => h m'' (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with hm' | rfl
      · exact (ih.1 fun m'' h'' => h m'' (by omega)) m' hm'
      · have hsucc := stackDrive_succ_of_eq (step P) x₀ v (h m' (by omega))
        rw [occCount_add_of_forall_eq _ m' fun m'' h'' => hrun m'' (by omega)] at hsucc
        rw [← hsucc]
        exact h (m' + 1) le_rfl
    · intro h m' hm'
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hm') with hm' | rfl
      · exact (ih.2 fun m'' h'' => h m'' (by omega)) m' (by omega)
      · have hprev := ih.2 fun m'' h'' => h m'' (by omega)
        have hsucc := stackDrive_succ_of_eq (step P) x₀ v (hprev m le_rfl)
        rw [occCount_add_of_forall_eq _ m fun m'' h'' => hprev m'' (by omega)] at hsucc
        rw [← add_assoc]
        exact hsucc.trans (h m (by omega))

/-- The exit step of a run: if the path is in `i` at `t, …, t + m`, then
`path (t + m + 1) = step P i (v i (N_i(t) + m))`. -/
theorem stackPath_exit_eq (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ) {i : Fin n}
    {t m : ℕ} (h : ∀ m' ≤ m, stackPath P x₀ v (t + m') = i) :
    stackPath P x₀ v (t + m + 1) = step P i (v i (occCount (stackPath P x₀ v) i t + m)) := by
  have hsucc := stackDrive_succ_of_eq (step P) x₀ v (h m le_rfl)
  rwa [occCount_add_of_forall_eq _ m fun m'' h'' => h m'' (by omega)] at hsucc

/-- The visit with index `k` exists before any time with `N_i(t) = k + 1`. -/
theorem exists_lt_occCount_eq {S : Type*} [DecidableEq S] (path : ℕ → S) (i : S) {k : ℕ} :
    ∀ t, occCount path i t = k + 1 → ∃ t' < t, path t' = i ∧ occCount path i t' = k := by
  intro t
  induction t with
  | zero => intro h; simp [occCount_zero] at h
  | succ t ih =>
    intro h
    rw [occCount_succ] at h
    by_cases hp : path t = i
    · simp only [hp, ite_true] at h
      exact ⟨t, by omega, hp, by omega⟩
    · simp only [hp, ite_false, add_zero] at h
      obtain ⟨t', ht', h1, h2⟩ := ih h
      exact ⟨t', by omega, h1, h2⟩

/-- **A spell starts right after a leaving departure**: if `t` starts a spell and `i` was
visited before `t`, the previous departure from `i` (index `N_i(t) − 1`) left `i`. -/
theorem not_stay_prev_of_spellStart (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (v : Fin n → ℕ → ℝ)
    {i : Fin n} {t : ℕ} (hs : IsSpellStart (stackPath P x₀ v) t)
    (hk : occCount (stackPath P x₀ v) i t ≠ 0) :
    step P i (v i (occCount (stackPath P x₀ v) i t - 1)) ≠ i := by
  set path := stackPath P x₀ v with hpath
  obtain ⟨k, hk1⟩ : ∃ k, occCount path i t = k + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hk).symm⟩
  obtain ⟨t', ht't, ht'i, ht'k⟩ := exists_lt_occCount_eq path i t hk1
  rw [hk1, Nat.add_sub_cancel, ← ht'k]
  intro hstay
  have hnext : path (t' + 1) = i := (stackDrive_succ_of_eq (step P) x₀ v ht'i).trans hstay
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt ht't) with hlt | heq
  · have h1 : occCount path i (t' + 2) ≤ occCount path i t := occCount_mono path i hlt
    have h2 : occCount path i (t' + 2) = k + 2 := by
      rw [occCount_succ, occCount_succ, ht'k, ht'i, hnext]
      simp
    omega
  · rcases hs with h0 | hprev
    · omega
    · apply hprev
      rw [← heq, Nat.succ_sub_one, ht'i]
      exact hnext.symm

/-! ### The spells of the 7/8 chain -/

/-- **Spells of the 7/8 chain driven by scrambled stacks** (post #3, codes (ii) and (iii)):
for every good flip table, starting state and state `i` there is `r < 8` such that the first
spell in `i` lasts exactly `r + 1` periods and every later spell in `i` lasts exactly `8`
periods (`runLength` censored at any `T` beyond the exit). -/
theorem spells_stackChain78 {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (x₀ i : Fin 2) :
    ∃ r < 8, (∀ k, step stackChain78 i (scrambledStack f i k) ≠ i ↔ k % 8 = r) ∧
      (∀ t T, stackPath stackChain78 x₀ (scrambledStack f) t = i →
        occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t = 0 → t + (r + 1) < T →
          runLength (stackPath stackChain78 x₀ (scrambledStack f)) t T = r + 1) ∧
      (∀ t T, IsSpellStart (stackPath stackChain78 x₀ (scrambledStack f)) t →
        stackPath stackChain78 x₀ (scrambledStack f) t = i →
        occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t ≠ 0 → t + 8 < T →
          runLength (stackPath stackChain78 x₀ (scrambledStack f)) t T = 8) := by
  obtain ⟨r, hr8, hr⟩ := exists_leaveResidue78 hf i
  set path := stackPath stackChain78 x₀ (scrambledStack f) with hpath
  refine ⟨r, hr8, hr, fun t T ht hk hT => ?_, fun t T hs ht hk hT => ?_⟩
  · -- first spell: departures `0, …, r − 1` stay, departure `r` leaves
    have hstay : ∀ m' ≤ r, path (t + m') = i := by
      refine (stackPath_stay_iff stackChain78 x₀ (scrambledStack f) ht r).2 fun m' hm' => ?_
      rw [hk, zero_add]
      by_contra hcon
      have := (hr m').1 hcon
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hexit : path (t + r + 1) ≠ i := by
      rw [hpath, stackPath_exit_eq stackChain78 x₀ (scrambledStack f) hstay, ← hpath, hk,
        zero_add]
      exact (hr r).2 (Nat.mod_eq_of_lt hr8)
    refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [hstay m (by omega), ← ht]
    · rw [ht, ← add_assoc]
      exact hexit
  · -- later spell: the previous departure left, so the next 7 stay and the 8th leaves
    have hprev := not_stay_prev_of_spellStart stackChain78 x₀ (scrambledStack f) hs hk
    have hres := (hr _).1 hprev
    set k := occCount path i t with hkdef
    have hkk : occCount (stackPath stackChain78 x₀ (scrambledStack f)) i t = k := rfl
    have hstay : ∀ m' ≤ 7, path (t + m') = i := by
      refine (stackPath_stay_iff stackChain78 x₀ (scrambledStack f) ht 7).2 fun m' hm' => ?_
      by_contra hcon
      have := (hr _).1 hcon
      omega
    have hexit : path (t + 7 + 1) ≠ i := by
      rw [hpath, stackPath_exit_eq stackChain78 x₀ (scrambledStack f) hstay, ← hpath]
      refine (hr _).2 ?_
      omega
    refine runLength_eq_of_exit hT (fun m hm => ?_) ?_
    · rw [hstay m (by omega), ht]
    · rw [ht]
      exact hexit

/-! ### The law of the first spell -/

/-- On the good event, "departures `0, …, r − 1` from `i` stay and departure `r` leaves" iff the
first 3 scrambled digits of stack point `r` are `leaveTarget78 i` (for `r < 8`). -/
theorem firstSpell78_iff {f : Fin 2 → ℕ → ℕ → Bool} (hf : IsGoodTable f) (i : Fin 2) {r : ℕ}
    (hr8 : r < 8) :
    ((∀ m < r, step stackChain78 i (scrambledStack f i m) = i) ∧
        step stackChain78 i (scrambledStack f i r) ≠ i) ↔
      digitPrefix (scrambledDigit (f i) r) 3 = leaveTarget78 i := by
  obtain ⟨r₀, hr₀8, hr₀⟩ := exists_leaveResidue78 hf i
  constructor
  · rintro ⟨-, h⟩
    rw [Ne, stay78_iff hf i r, not_not] at h
    exact h
  · intro h
    have hleave : step stackChain78 i (scrambledStack f i r) ≠ i := by
      rw [Ne, stay78_iff hf i r, not_not]
      exact h
    have hrr : r = r₀ := by
      have := (hr₀ r).1 hleave
      rwa [Nat.mod_eq_of_lt hr8] at this
    refine ⟨fun m hm => ?_, hleave⟩
    by_contra hcon
    have := (hr₀ m).1 hcon
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- `2^{-3} = 1/8` in `ℝ≥0∞`. -/
theorem two_inv_pow_three : (2⁻¹ : ENNReal) ^ 3 = 8⁻¹ := by
  rw [← ENNReal.inv_pow]
  norm_num

/-- **The first spell under Owen scrambling is uniform** (post #3, code (iii)): for `r < 8`,
the probability that departures `0, …, r − 1` from `i` stay and departure `r` leaves is
`1/8`. -/
theorem owen_firstSpell78 (i : Fin 2) {r : ℕ} (hr8 : r < 8) :
    owenMeasure 2 {ω | (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
      step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} = 8⁻¹ := by
  have hae : {ω : Fin 2 × ℕ × ℕ → Bool |
      (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} =ᵐ[owenMeasure 2]
      {ω | digitPrefix (scrambledDigit (owenTable ω i) r) 3 = leaveTarget78 i} :=
    (ae_isGoodTable_owen 2).mono fun ω hω => propext (firstSpell78_iff hω i hr8)
  rw [measure_congr hae, owen_digitPrefix_eq i r (by unfold leaveTarget78; split_ifs <;> norm_num),
    two_inv_pow_three]

/-- **The first spell under the digital shift is uniform** (post #3, code (ii)). -/
theorem shift_firstSpell78 (i : Fin 2) {r : ℕ} (hr8 : r < 8) :
    shiftMeasure 2 {ω | (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
      step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} = 8⁻¹ := by
  have hae : {ω : Fin 2 × ℕ → Bool |
      (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} =ᵐ[shiftMeasure 2]
      {ω | digitPrefix (scrambledDigit (shiftFlips ω i) r) 3 = leaveTarget78 i} :=
    (ae_isGoodTable_shift 2).mono fun ω hω => propext (firstSpell78_iff hω i hr8)
  rw [measure_congr hae, shift_digitPrefix_eq i r (by unfold leaveTarget78; split_ifs <;> norm_num),
    two_inv_pow_three]

/-- For a chain started in `i`, the first spell has length `r + 1` iff departures
`0, …, r − 1` stay and departure `r` leaves. -/
theorem runLength_zero_stackPath_iff (P : Fin n → Fin n → ℝ) (i : Fin n) (v : Fin n → ℕ → ℝ)
    {r T : ℕ} (hT : r + 1 < T) :
    runLength (stackPath P i v) 0 T = r + 1 ↔
      (∀ m < r, step P i (v i m) = i) ∧ step P i (v i r) ≠ i := by
  have h0 : stackPath P i v 0 = i := stackDrive_zero _ _ _
  have hocc : occCount (stackPath P i v) i 0 = 0 := occCount_zero _ _
  rw [runLength_eq_iff (by omega), h0]
  simp only [zero_add]
  have hst := stackPath_stay_iff P i v h0 r
  simp only [hocc, zero_add] at hst
  constructor
  · rintro ⟨h1, h2⟩
    have hrun : ∀ m' ≤ r, stackPath P i v m' = i := fun m' hm' => h1 m' (by omega)
    refine ⟨hst.1 hrun, ?_⟩
    have := stackPath_exit_eq P i v (t := 0) (m := r) (by simpa using hrun)
    simp only [zero_add, hocc] at this
    rw [← this]
    exact h2
  · rintro ⟨h1, h2⟩
    have hrun := hst.2 h1
    refine ⟨fun m hm => hrun m (by omega), ?_⟩
    have := stackPath_exit_eq P i v (t := 0) (m := r) (by simpa using hrun)
    simp only [zero_add, hocc] at this
    rw [this]
    exact h2

/-- **First spell of the 7/8 chain started in `i`, Owen scrambling**: its length is uniform on
`{1, …, 8}`: `P(runLength = r + 1) = 1/8` for `r < 8` (censoring `T > r + 1`). -/
theorem owen_runLength_first78 (i : Fin 2) {r T : ℕ} (hr8 : r < 8) (hT : r + 1 < T) :
    owenMeasure 2 {ω | runLength (stackPath stackChain78 i (scrambledStack (owenTable ω))) 0 T =
      r + 1} = 8⁻¹ := by
  have e : {ω : Fin 2 × ℕ × ℕ → Bool |
      runLength (stackPath stackChain78 i (scrambledStack (owenTable ω))) 0 T = r + 1} =
      {ω | (∀ m < r, step stackChain78 i (scrambledStack (owenTable ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (owenTable ω) i r) ≠ i} := by
    ext ω
    exact runLength_zero_stackPath_iff stackChain78 i _ hT
  rw [e]
  exact owen_firstSpell78 i hr8

/-- **First spell of the 7/8 chain started in `i`, digital shift**: uniform on `{1, …, 8}`. -/
theorem shift_runLength_first78 (i : Fin 2) {r T : ℕ} (hr8 : r < 8) (hT : r + 1 < T) :
    shiftMeasure 2 {ω | runLength (stackPath stackChain78 i (scrambledStack (shiftFlips ω))) 0 T =
      r + 1} = 8⁻¹ := by
  have e : {ω : Fin 2 × ℕ → Bool |
      runLength (stackPath stackChain78 i (scrambledStack (shiftFlips ω))) 0 T = r + 1} =
      {ω | (∀ m < r, step stackChain78 i (scrambledStack (shiftFlips ω) i m) = i) ∧
        step stackChain78 i (scrambledStack (shiftFlips ω) i r) ≠ i} := by
    ext ω
    exact runLength_zero_stackPath_iff stackChain78 i _ hT
  rw [e]
  exact shift_firstSpell78 i hr8

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# n-state stack chains: the occupation error as a sum of level terms (post #3)

Post #3, codes (ii) and (iii), with any number `n` of states: "in the five-state chain
normality cannot be rejected for the per-state Sobol sequences ((ii) and (iii))". This module is
randomisation-free: everything holds for EVERY flip table `f`.

Let `P` be stochastic on `Fin n`, `s` a target state and `h − Ph = 1_{s} − c` (Poisson's
equation). Along the chain driven by the scrambled van der Corput stacks of `f`, the occupation
error `E_T = N_s(T) − T c` is `h(X₀) − h(X_T) + Σ_i D_i(N_i(T))` (`OccupationDiscrepancy`), and by
Abel summation the departure discrepancy of row `i` is a weighted sum of local discrepancies at
the **cut points** `c_{ij} = cumProb P i (j+1)`, `j < n − 1`, with weights `h_j − h_{j+1}`
(`step_sub_mulVec_eq_sum_cut`, `sum_step_sub_eq_sum_segErr`, `occCount_sub_eq_boundary_add_cuts`).

**Reading of `π`.** We take Poisson data for EVERY target (`IsPoissonFamily P H π`:
`H t − P H t = 1_{t} − π_t` for all `t`), which is satisfiable (e.g. `H t = 1_{t} − 1/n`, `π = 1/n`
for the uniform chain, `CltNExample`), and forces `π_t ∈ [0,1]` (`IsPoissonFamily.mem_Icc`).
The occupation error of target `s` is `occErrN = N_s(T) − T π_s`, its Poisson function `H s`.

**Cut points equal to `1`** contribute nothing (all points are `≤ 1`): they are handled, not
assumed away (`cutTerm` is `0` there, `segErr_scrambledVdc_one`).

## Main results

* `cutWeight h j = h_j − h_{j+1}`, `cutPoint P i j = cumProb P i (j + 1)`.
* `occCount_sub_eq_boundary_add_cuts` (**decomposition**):
  `N_s(T) − T c = h(x₀) − h(X_T) + Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, N_i(T))`.
* `IsPoissonFamily`, `IsPoissonFamily.mem_Icc`, `abs_occCount_sub_pi_le`.
* `abs_occErrN_sub_mainTermN_le` (**n-state deterministic Anscombe**): with
  `mainTermN = Σ_i Σ_j (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, ⌊T π_i⌋)`,
  `|E_T − mainTermN| ≤ ansBoundN = O(log log T)` for every flip table; `ansBoundN_le_log`.
* `tendsto_sq_div_natLog_of_le`: such bounds are `o(√log T)`.
* `segErr_scrambledVdc_eq_sum_cutTerm`, `mainTermN_eq_levelSumN` (**level decomposition**):
  `mainTermN = Σ_{m<K} Σ_i rowTerm … m … i`, where the row term of level `m` collects, over the
  cut points `j`, the terms `w_j 1{bit m of n_i} (1{LevelInd} − {2^m c_{ij}})` of
  `segErr_scrambledVdc_eq_sum_level`, as functions of the path coins of the cut points.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### Abel summation over the cut points -/

/-- The weight `h_j − h_{j+1}` of cut point `j` (the states extended by `0` beyond `n − 1`). -/
noncomputable def cutWeight (h : Fin n → ℝ) (j : ℕ) : ℝ := extendNat h j - extendNat h (j + 1)

/-- Cut point `j` of row `i`: the cumulative probability `cumProb P i (j + 1)`. -/
noncomputable def cutPoint (P : Fin n → Fin n → ℝ) (i : Fin n) (j : ℕ) : ℝ :=
  cumProb P i (j + 1)

/-- Cut points of a stochastic matrix lie in `[0, 1]`. -/
theorem cutPoint_mem_Icc {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i : Fin n) (j : ℕ) :
    cutPoint P i j ∈ Set.Icc (0 : ℝ) 1 :=
  cumProb_mem_Icc hP i (j + 1)

/-- `extendNat h k = h k` on states. -/
theorem extendNat_fin (h : Fin n → ℝ) (k : Fin n) : extendNat h k = h k := by
  unfold extendNat
  simp [k.isLt]

/-- Summation by parts over the states: if `B 0 = 0`, then
`Σ_{j<n} h_j (B_{j+1} − B_j) = h_{n−1} B_n + Σ_{j<n−1} (h_j − h_{j+1}) B_{j+1}`. -/
theorem sum_extendNat_mul_sub_eq (hn : 1 ≤ n) (h : Fin n → ℝ) (B : ℕ → ℝ) (hB : B 0 = 0) :
    ∑ j ∈ range n, extendNat h j * (B (j + 1) - B j) =
      extendNat h (n - 1) * B n + ∑ j ∈ range (n - 1), cutWeight h j * B (j + 1) := by
  have e := sum_mul_sub_eq_abel (extendNat h) B hB (n - 1)
  rw [Nat.sub_add_cancel hn] at e
  rw [e, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  rw [cutWeight]
  ring

/-- **Abel summation for one departure.** For `u ≤ 1`,
`h(step P i u) − (Ph)(i) = Σ_{j<n−1} (h_j − h_{j+1}) (1{u ≤ c_{ij}} − c_{ij})`. -/
theorem step_sub_mulVec_eq_sum_cut {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (h : Fin n → ℝ) (i : Fin n) {u : ℝ} (hu : u ≤ 1) :
    h (step P i u) - (P *ᵥ h) i = ∑ j ∈ range (n - 1),
      cutWeight h j * ((if u ≤ cutPoint P i j then 1 else 0) - cutPoint P i j) := by
  have hn : 1 ≤ n := by have := i.isLt; omega
  set B : ℕ → ℝ := fun m ↦ if (step P i u : ℕ) < m then 1 else 0 with hBdef
  set C : ℕ → ℝ := fun m ↦ cumProb P i m with hCdef
  have hB0 : B 0 = 0 := by simp [hBdef]
  have hC0 : C 0 = 0 := cumProb_zero P i
  have hBn : B n = 1 := by simp [hBdef, (step P i u).isLt]
  have hCn : C n = 1 := by
    change cumProb P i n = 1
    rw [cumProb_of_le P i le_rfl, hP.sum_eq_one i]
  -- the value as a telescoping sum
  have h1 : h (step P i u) = ∑ j ∈ range n, extendNat h j * (B (j + 1) - B j) := by
    rw [sum_eq_single (step P i u : ℕ)]
    · simp only [hBdef, Nat.lt_succ_self, ite_true, lt_irrefl, ite_false, sub_zero, mul_one]
      rw [extendNat_fin]
    · intro j _ hj
      have : B (j + 1) - B j = 0 := by
        simp only [hBdef]
        rcases lt_or_gt_of_ne hj with h' | h'
        · have h2 : ¬ (step P i u : ℕ) < j + 1 := by omega
          have h3 : ¬ (step P i u : ℕ) < j := by omega
          simp [h2, h3]
        · have h2 : (step P i u : ℕ) < j + 1 := by omega
          have h3 : (step P i u : ℕ) < j := h'
          simp [h2, h3]
      rw [this, mul_zero]
    · intro h'
      exact absurd (mem_range.2 (step P i u).isLt) h'
  have h2 : (P *ᵥ h) i = ∑ j ∈ range n, extendNat h j * (C (j + 1) - C j) := by
    change ∑ k, P i k * h k = _
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ extendNat h j * (C (j + 1) - C j)) n]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [hCdef]
    rw [cumProb_succ, extendNat_fin]
    ring
  rw [h1, h2, sum_extendNat_mul_sub_eq hn h B hB0, sum_extendNat_mul_sub_eq hn h C hC0, hBn, hCn,
    add_sub_add_left_eq_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  have hstep := step_lt_iff hP i hu (m := j + 1) (by omega)
  simp only [hBdef, hCdef, cutPoint]
  by_cases hj : u ≤ cumProb P i (j + 1)
  · have h' := hstep.2 hj
    simp only [h', hj, ite_true]
    ring
  · have h' : ¬ (step P i u : ℕ) < j + 1 := fun h' ↦ hj (hstep.1 h')
    simp only [h', hj, ite_false]
    ring

/-- **Abel summation for a stack**: the departure error of `N` points of a sequence `v ≤ 1` is
`Σ_{j<n−1} (h_j − h_{j+1}) segErr(v, c_{ij}, 0, N)`. -/
theorem sum_step_sub_eq_sum_segErr {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (h : Fin n → ℝ) (i : Fin n) {v : ℕ → ℝ} (hv : ∀ k, v k ≤ 1) (N : ℕ) :
    ∑ k ∈ range N, (h (step P i (v k)) - (P *ᵥ h) i) =
      ∑ j ∈ range (n - 1), cutWeight h j * segErr v (cutPoint P i j) 0 N := by
  rw [sum_congr rfl fun k _ ↦ step_sub_mulVec_eq_sum_cut hP h i (hv k), sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [segErr, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [zero_add]

/-- **Decomposition of the occupation error** (every flip table): if `h − Ph = 1_{s} − c`, then
`N_s(T) − T c = h(x₀) − h(X_T) + Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, N_i(T))`. -/
theorem occCount_sub_eq_boundary_add_cuts {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool) {h : Fin n → ℝ} {s : Fin n} {c : ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - c) (T : ℕ) :
    (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) - T * c =
      h x₀ - h (stackPath P x₀ (scrambledStack f) T) + ∑ i, ∑ j ∈ range (n - 1),
        cutWeight h j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0
          (occCount (stackPath P x₀ (scrambledStack f)) i T) := by
  rw [occCount_sub_eq_boundary_add P hh (stackPath P x₀ (scrambledStack f)) T]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  refine (departureDiscrepancy_stackDrive P h (step P) x₀ (scrambledStack f) i T).trans ?_
  exact sum_step_sub_eq_sum_segErr hP h i (fun k ↦ (scrambledVdc_mem_Icc (f i) k).2) _

/-! ### Poisson data for every target -/

/-- **Poisson data for every target**: `H t − P H t = 1_{t} − π_t` for every state `t`. -/
def IsPoissonFamily (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) : Prop :=
  ∀ t i, H t i - (P *ᵥ H t) i = (if i = t then 1 else 0) - pi t

/-- For a stochastic row, `(P g)(i)` lies between the minimum and maximum of `g`. -/
theorem mulVec_le_of_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {g : Fin n → ℝ} {a : ℝ}
    (hg : ∀ k, g k ≤ a) (i : Fin n) : (P *ᵥ g) i ≤ a := by
  change ∑ k, P i k * g k ≤ a
  calc ∑ k, P i k * g k ≤ ∑ k, P i k * a :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hg k) (hP.nonneg i k)
    _ = a := by rw [← sum_mul, hP.sum_eq_one i, one_mul]

/-- For a stochastic row, `(P g)(i) ≥ a` when `g ≥ a`. -/
theorem le_mulVec_of_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {g : Fin n → ℝ} {a : ℝ}
    (hg : ∀ k, a ≤ g k) (i : Fin n) : a ≤ (P *ᵥ g) i := by
  change a ≤ ∑ k, P i k * g k
  calc a = ∑ k, P i k * a := by rw [← sum_mul, hP.sum_eq_one i, one_mul]
    _ ≤ ∑ k, P i k * g k :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hg k) (hP.nonneg i k)

/-- **Poisson data force `π_t ∈ [0, 1]`** (at a maximiser of `H t`, `H t − P H t ≥ 0`; at a
minimiser, `≤ 0`). -/
theorem IsPoissonFamily.mem_Icc {P : Fin n → Fin n → ℝ} {H : Fin n → Fin n → ℝ}
    {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (hP : IsStochastic P) (t : Fin n) :
    pi t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ (H t) ⟨t, mem_univ t⟩
  obtain ⟨i₁, -, hmin⟩ := exists_min_image univ (H t) ⟨t, mem_univ t⟩
  have h0 := mulVec_le_of_le hP (fun k ↦ hmax k (mem_univ k)) i₀
  have h1 := le_mulVec_of_le hP (fun k ↦ hmin k (mem_univ k)) i₁
  have e0 := hH t i₀
  have e1 := hH t i₁
  have hi0 : (if i₀ = t then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hi1 : (0 : ℝ) ≤ if i₁ = t then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  constructor <;> linarith

/-- A bound `Σ_t Σ_i |H t i|` for all the Poisson functions. -/
noncomputable def poissonSup (H : Fin n → Fin n → ℝ) : ℝ := ∑ t, ∑ i, |H t i|

/-- `|H t i| ≤ poissonSup H`. -/
theorem abs_le_poissonSup (H : Fin n → Fin n → ℝ) (t i : Fin n) : |H t i| ≤ poissonSup H := by
  have h1 : |H t i| ≤ ∑ i', |H t i'| :=
    single_le_sum (f := fun i' ↦ |H t i'|) (fun _ _ ↦ abs_nonneg _) (mem_univ i)
  have h2 : ∑ i', |H t i'| ≤ poissonSup H :=
    single_le_sum (f := fun t' ↦ ∑ i', |H t' i'|) (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
      (mem_univ t)
  exact h1.trans h2

/-- `0 ≤ poissonSup H`. -/
theorem poissonSup_nonneg (H : Fin n → Fin n → ℝ) : 0 ≤ poissonSup H :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The constant `A = ⌈2 M (1 + n²)⌉ + 2` of the occupation bound. -/
noncomputable def anscConstN (H : Fin n → Fin n → ℝ) : ℕ :=
  ⌈2 * poissonSup H * (1 + (n : ℝ) ^ 2)⌉₊ + 2

/-- **Occupation of every state** (every flip table):
`|N_i(T) − T π_i| ≤ A (⌊log₂ T⌋ + 1) − 1`. -/
theorem abs_occCount_sub_pi_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i : Fin n) (T : ℕ) :
    |(occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) - T * pi i| ≤
      (anscConstN H : ℝ) * (Nat.log 2 T + 1) - 1 := by
  set M := poissonSup H with hM
  have hM0 : 0 ≤ M := poissonSup_nonneg H
  have h1 := abs_occCount_scrambled_sub_le hP x₀ f (h := H i) (s := i) (c := pi i) (M := M)
    (hH i) (fun k ↦ abs_le_poissonSup H i k) T
  have hV : stateVariation (H i) ≤ 2 * (n - 1 : ℕ) * M :=
    stateVariation_le fun k ↦ abs_le_poissonSup H i k
  have hL : (0 : ℝ) ≤ Nat.log 2 T := Nat.cast_nonneg _
  have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hV' : (n : ℝ) * stateVariation (H i) ≤ 2 * (n : ℝ) ^ 2 * M := by
    have := mul_le_mul_of_nonneg_left hV hn0
    have h3 : (n : ℝ) * (2 * ((n - 1 : ℕ) : ℝ) * M) ≤ 2 * (n : ℝ) ^ 2 * M := by
      have : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hA : 2 * M * (1 + (n : ℝ) ^ 2) + 2 ≤ (anscConstN H : ℝ) := by
    rw [anscConstN]
    push_cast
    linarith [Nat.le_ceil (2 * M * (1 + (n : ℝ) ^ 2))]
  have hVn := stateVariation_nonneg (H i)
  calc |(occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) - T * pi i|
      ≤ 2 * M + n * stateVariation (H i) * ((Nat.log 2 T : ℝ) + 1) := h1
    _ ≤ 2 * M * (Nat.log 2 T + 1) + 2 * (n : ℝ) ^ 2 * M * (Nat.log 2 T + 1) := by
        have : 2 * M ≤ 2 * M * (Nat.log 2 T + 1) := by nlinarith
        have : n * stateVariation (H i) * ((Nat.log 2 T : ℝ) + 1) ≤
            2 * (n : ℝ) ^ 2 * M * (Nat.log 2 T + 1) :=
          mul_le_mul_of_nonneg_right hV' (by linarith)
        linarith
    _ ≤ (anscConstN H : ℝ) * (Nat.log 2 T + 1) - 1 := by nlinarith

/-! ### The deterministic Anscombe theorem -/

/-- The occupation error `N_s(T) − T π_s` of the chain driven by the scrambled stacks of `f`. -/
noncomputable def occErrN (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) : ℝ :=
  occCount (stackPath P x₀ (scrambledStack f)) s T - T * pi s

/-- The deterministic indices `n_i(T) = ⌊T π_i⌋`. -/
noncomputable def chainIdxN (pi : Fin n → ℝ) (T : ℕ) (i : Fin n) : ℕ := ⌊T * pi i⌋₊

/-- **The main term**: `Σ_i Σ_{j<n−1} (h_j − h_{j+1}) segErr(v_i, c_{ij}, 0, ⌊T π_i⌋)`, the
departure discrepancies at the deterministic indices. -/
noncomputable def mainTermN (P : Fin n → Fin n → ℝ) (h : Fin n → ℝ) (pi : Fin n → ℝ)
    (f : Fin n → ℕ → ℕ → Bool) (T : ℕ) : ℝ :=
  ∑ i, ∑ j ∈ range (n - 1), cutWeight h j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0
    (chainIdxN pi T i)

/-- The total absolute weight `Σ_{j<n−1} |h_j − h_{j+1}|`. -/
noncomputable def cutWeightSum (h : Fin n → ℝ) : ℝ := ∑ j ∈ range (n - 1), |cutWeight h j|

/-- `0 ≤ cutWeightSum h`. -/
theorem cutWeightSum_nonneg (h : Fin n → ℝ) : 0 ≤ cutWeightSum h :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The Anscombe bound `2M + n W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)`. -/
noncomputable def ansBoundN (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) : ℝ :=
  2 * poissonSup H + n * cutWeightSum (H s) *
    (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3)

/-- `n_i(T) ≤ T` (as `π_i ≤ 1`). -/
theorem chainIdxN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {H : Fin n → Fin n → ℝ}
    {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (T : ℕ) (i : Fin n) : chainIdxN pi T i ≤ T := by
  have h1 := (hH.mem_Icc hP i).2
  have h0 := (hH.mem_Icc hP i).1
  unfold chainIdxN
  refine Nat.floor_le_of_le ?_
  nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

/-- `n_i(T) < 2^{⌊log₂ T⌋ + 1}`. -/
theorem chainIdxN_lt_two_pow {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (T : ℕ) (i : Fin n) :
    chainIdxN pi T i < 2 ^ (Nat.log 2 T + 1) :=
  lt_of_le_of_lt (chainIdxN_le hP hH T i) (Nat.lt_pow_succ_log_self one_lt_two T)

/-- **Deterministic Anscombe theorem for n-state stack chains** (every flip table):
`|E_T − mainTermN(T)| ≤ ansBoundN = 2M + n W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)`. -/
theorem abs_occErrN_sub_mainTermN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) :
    |occErrN P pi x₀ f s T - mainTermN P (H s) pi f T| ≤ ansBoundN H s T := by
  have hid := occCount_sub_eq_boundary_add_cuts hP x₀ f (hH s) T
  set path := stackPath P x₀ (scrambledStack f) with hpath
  set L := (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) with hL
  have hseg : ∀ i, ∀ j ∈ range (n - 1),
      |cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i)| ≤
        |cutWeight (H s) j| * (2 * L + 3) := by
    intro i j _
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hc := cutPoint_mem_Icc hP i j
    refine (abs_segErr_sub_segErr_le (f i) hc.1 hc.2 _ _).trans ?_
    have hpi := hH.mem_Icc hP i
    have hfl : |T * pi i - (chainIdxN pi T i : ℝ)| < 1 := by
      have hy : 0 ≤ (T : ℝ) * pi i := mul_nonneg (Nat.cast_nonneg T) hpi.1
      rw [chainIdxN, abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
      linarith [Nat.lt_floor_add_one ((T : ℝ) * pi i)]
    have hd := natLog_dist_le (abs_occCount_sub_pi_le hP hH x₀ f i T) hfl
    rw [← hpath] at hd
    have hd' : (Nat.log 2 (occCount path i T - chainIdxN pi T i +
        (chainIdxN pi T i - occCount path i T)) : ℝ) ≤ L := by
      rw [hL]
      exact_mod_cast hd
    linarith
  have hsum : |∑ i, ∑ j ∈ range (n - 1),
      (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i))| ≤
      n * cutWeightSum (H s) * (2 * L + 3) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j ∈ range (n - 1),
          (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
          cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i))|
        ≤ ∑ _i : Fin n, cutWeightSum (H s) * (2 * L + 3) := by
          refine sum_le_sum fun i _ ↦ (abs_sum_le_sum_abs _ _).trans ?_
          rw [cutWeightSum, sum_mul]
          exact sum_le_sum (hseg i)
      _ = n * cutWeightSum (H s) * (2 * L + 3) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hb : |H s x₀ - H s (path T)| ≤ 2 * poissonSup H := by
    have := abs_sub (H s x₀) (H s (path T))
    linarith [abs_le_poissonSup H s x₀, abs_le_poissonSup H s (path T)]
  have e : occErrN P pi x₀ f s T - mainTermN P (H s) pi f T =
      (H s x₀ - H s (path T)) + ∑ i, ∑ j ∈ range (n - 1),
      (cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (occCount path i T) -
        cutWeight (H s) j * segErr (scrambledVdc (f i)) (cutPoint P i j) 0 (chainIdxN pi T i)) := by
    rw [occErrN, hid, mainTermN]
    simp only [sum_sub_distrib]
    ring
  rw [e, ansBoundN]
  exact (abs_add_le _ _).trans (add_le_add hb hsum)

/-- `⌊log₂ (A x)⌋ ≤ ⌊log₂ A⌋ + ⌊log₂ x⌋ + 1`. -/
theorem natLog_mul_le (A x : ℕ) : Nat.log 2 (A * x) ≤ Nat.log 2 A + Nat.log 2 x + 1 := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  refine Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow (by positivity) ?_)
  have h1 := Nat.lt_pow_succ_log_self one_lt_two A
  have h2 := Nat.lt_pow_succ_log_self one_lt_two x
  rw [Nat.succ_eq_add_one] at h1 h2 ⊢
  rw [show Nat.log 2 A + Nat.log 2 x + 1 + 1 = (Nat.log 2 A + 1) + (Nat.log 2 x + 1) by ring,
    pow_add]
  exact Nat.mul_lt_mul'' h1 h2

/-- The constant `C` of `ansBoundN ≤ C (⌊log₂(⌊log₂ T⌋ + 1)⌋ + 1)`. -/
noncomputable def ansConstN (H : Fin n → Fin n → ℝ) (s : Fin n) : ℝ :=
  2 * poissonSup H + n * cutWeightSum (H s) * (2 * Nat.log 2 (anscConstN H) + 5)

/-- `0 ≤ ansBoundN`. -/
theorem ansBoundN_nonneg (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) : 0 ≤ ansBoundN H s T := by
  have := poissonSup_nonneg H
  have := cutWeightSum_nonneg (H s)
  rw [ansBoundN]
  positivity

/-- `0 ≤ ansConstN`. -/
theorem ansConstN_nonneg (H : Fin n → Fin n → ℝ) (s : Fin n) : 0 ≤ ansConstN H s := by
  have := poissonSup_nonneg H
  have := cutWeightSum_nonneg (H s)
  rw [ansConstN]
  positivity

/-- **The Anscombe bound is `O(log log T)`.** -/
theorem ansBoundN_le_log (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) :
    ansBoundN H s T ≤ ansConstN H s * ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hmul : (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConstN H) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    exact_mod_cast natLog_mul_le _ _
  have hM := poissonSup_nonneg H
  have hW := cutWeightSum_nonneg (H s)
  have hnW : 0 ≤ (n : ℝ) * cutWeightSum (H s) := mul_nonneg (Nat.cast_nonneg n) hW
  have h0 := (Nat.log 2 (anscConstN H)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  rw [ansBoundN, ansConstN]
  have k1 : (n : ℝ) * cutWeightSum (H s) *
      (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3) ≤
      (n : ℝ) * cutWeightSum (H s) *
        (2 * (Nat.log 2 (anscConstN H) : ℝ) + 2 * Nat.log 2 (Nat.log 2 T + 1) + 5) :=
    mul_le_mul_of_nonneg_left (by linarith) hnW
  have k2 : (n : ℝ) * cutWeightSum (H s) *
      (2 * (Nat.log 2 (anscConstN H) : ℝ) + 2 * Nat.log 2 (Nat.log 2 T + 1) + 5) ≤
      (n : ℝ) * cutWeightSum (H s) * ((2 * (Nat.log 2 (anscConstN H) : ℝ) + 5) *
        ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hnW
  nlinarith

/-- **`O(log log T)` is `o(√log T)`.** If `0 ≤ b k ≤ C (⌊log₂(⌊log₂ T_k⌋ + 1)⌋ + 1)` and
`T_k → ∞`, then `b_k² / log₂ T_k → 0`. -/
theorem tendsto_sq_div_natLog_of_le {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {b : ℕ → ℝ}
    {C : ℝ} (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k, b k ≤ C * ((Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1)) :
    Tendsto (fun k ↦ b k ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0) := by
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hx : Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ _) hlogT
  have hlim := (tendsto_natLog_pow_six_div.comp hx).const_mul (2 * C ^ 2)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by have := hb0 k; positivity) ?_ hlim
  have hev : ∀ᶠ k in atTop, 2 ≤ Nat.log 2 (T k) + 1 := hx.eventually_ge_atTop 2
  filter_upwards [hev] with k hk
  set y := (Nat.log 2 (Nat.log 2 (T k) + 1) : ℝ) + 1 with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [(Nat.log 2 (Nat.log 2 (T k) + 1)).cast_nonneg (α := ℝ)]
  have hlog : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast (show 1 ≤ Nat.log 2 (T k) by omega)
  have hy6 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have hb2 : b k ^ 2 ≤ C ^ 2 * y ^ 6 := by
    have := pow_le_pow_left₀ (hb0 k) (hb k) 2
    rw [mul_pow] at this
    nlinarith
  simp only [Function.comp_apply]
  rw [div_le_iff₀ (by linarith), ← hy]
  have hpos : (0 : ℝ) < ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) := by positivity
  calc b k ^ 2 ≤ C ^ 2 * y ^ 6 := hb2
    _ = 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) *
        (((Nat.log 2 (T k) + 1 : ℕ) : ℝ) / 2) := by field_simp
    _ ≤ 2 * C ^ 2 * (y ^ 6 / ((Nat.log 2 (T k) + 1 : ℕ) : ℝ)) * Nat.log 2 (T k) := by
        gcongr
        push_cast
        linarith

/-! ### The level decomposition -/

/-- The level-`m` term of the local discrepancy at a cut point `c` (zero if `c ≥ 1`, where the
local discrepancy vanishes). -/
noncomputable def cutTerm (c : ℝ) (N m : ℕ) (e : ℕ → Bool) : ℝ :=
  if c < 1 then coinTerm c N m e else 0

/-- The level-`m` term truncated at depth `L`. -/
noncomputable def cutTermTrunc (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) : ℝ :=
  if c < 1 then coinTermTrunc c N m L e else 0

/-- At the cut point `1` the local discrepancy of points in `[0,1]` vanishes. -/
theorem segErr_scrambledVdc_one (g : ℕ → ℕ → Bool) (N : ℕ) :
    segErr (scrambledVdc g) 1 0 N = 0 := by
  rw [segErr]
  refine sum_eq_zero fun k _ ↦ ?_
  simp only [(scrambledVdc_mem_Icc g _).2, ite_true, sub_self]

/-- **Level decomposition at a cut point in `[0,1]`** (every flip table): for `N < 2^K`,
`segErr(v, c, 0, N) = Σ_{m<K} cutTerm c N m e` with `e` the path coins of `c`. -/
theorem segErr_scrambledVdc_eq_sum_cutTerm (g : ℕ → ℕ → Bool) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {N K : ℕ} (hN : N < 2 ^ K) :
    segErr (scrambledVdc g) c 0 N =
      ∑ m ∈ range K, cutTerm c N m (pathCoin g (threshDigit c)) := by
  rcases hc1.lt_or_eq with hlt | heq
  · rw [segErr_scrambledVdc_eq_sum_level g hc0 hlt hN, sum_filter]
    refine sum_congr rfl fun m _ ↦ ?_
    simp only [cutTerm, hlt, ite_true, coinTerm]
  · subst heq
    rw [segErr_scrambledVdc_one]
    refine (sum_eq_zero fun m _ ↦ ?_).symm
    simp only [cutTerm, lt_irrefl, ite_false]

/-- The **row term** of level `m`: `Σ_{j<n−1} w_j · cutTerm (c_{ij}) (N_i) m (e_{ij})`, for cut
points `cp`, weights `w`, indices `N` and coin sequences `e i j`. -/
noncomputable def rowTerm (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * cutTerm (cp i j) (N i) m (e i j)

/-- The row term truncated at depth `L`. -/
noncomputable def rowTermTrunc (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * cutTermTrunc (cp i j) (N i) m L (e i j)

/-- The **level sum** `Σ_{m<K} Σ_i rowTerm … m … i`. -/
noncomputable def levelSumN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ m ∈ range K, ∑ i, rowTerm w cp N m e i

/-- **Level decomposition of the main term** (every flip table): for `n_i(T) < 2^K`,
`mainTermN = levelSumN` with the path coins of the cut points of every row. -/
theorem mainTermN_eq_levelSumN {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (h : Fin n → ℝ)
    (pi : Fin n → ℝ) (f : Fin n → ℕ → ℕ → Bool) (T : ℕ) {K : ℕ}
    (hK : ∀ i, chainIdxN pi T i < 2 ^ K) :
    mainTermN P h pi f T = levelSumN (cutWeight h) (cutPoint P) (chainIdxN pi T) K
      (fun i j ↦ pathCoin (f i) (threshDigit (cutPoint P i j))) := by
  rw [mainTermN, levelSumN]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [rowTerm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  have hc := cutPoint_mem_Icc hP i j
  rw [segErr_scrambledVdc_eq_sum_cutTerm (f i) hc.1 hc.2 (hK i), mul_sum]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Level sums of fair coins: moments and the CLT (for post #3, n states)

The main term of an n-state scrambled-stack chain is a level sum `levelSumN` (`CltNDecomp`):
over levels `m`, rows `i` and cut points `j`, bounded level terms of coin sequences
`e i j = (ω (γ i j d))_d`. This module works on an arbitrary product of fair coins
`coinMeasure ι = ⊗_{q : ι} fairCoin`, with a **coin layout** `γ : Fin n → ℕ → ℕ → ι` whose
coordinate `γ i j d` has level `lev (γ i j d) = d`. Different cut points may share coordinates
(for the digital shift all cut points of a row share them, `CltNShift`; for Owen's scramble two
cut points share the nodes of their common binary prefix, `CltNOwen`): no independence between
cut points is assumed. The two randomisations are then treated by two instantiations.

## Main results

* `coinMeasure`, `coinsOf`, `absWeightSum`.
* One cut point (any injective `g : ℕ → ι`): `measureReal_levelInd_coins` (`{2^m c}`),
  `integral_cutTerm_coins` (`0`), `measureReal_levelTie_coins` (`2^{-L}`),
  `integral_abs_cutTerm_sub_trunc_le`, `isLocal_cutTermTrunc_coins`.
* Rows: `abs_rowTerm_le`, `integral_rowTerm_coins`, `integral_abs_rowTerm_sub_trunc_le`,
  `isLocal_rowTermTrunc_coins`; levels: `levelYN`, `abs_levelYN_le`, `integral_levelSumN_coins`.
* `tendstoInDistribution_levelSumN` (**CLT for level sums**): if `K_k → ∞` and
  `Var(levelSumN) ≥ κ K_k` eventually, the normalised level sums are asymptotically `N(0,1)`
  (`tendstoInDistribution_of_truncations`, with `B = nW`, `C = (nW)²`).
* `tendstoInDistribution_of_close_main` (**Slutsky assembly**): an error within `b_k` of a
  centred main term, `b_k² = o(log T_k)`, `Var ≥ κ log T_k`, inherits the main term's CLT.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {ι : Type*} {n : ℕ}

/-- The product of fair coins on the coordinates `ι`. -/
noncomputable abbrev coinMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι ↦ fairCoin

/-- The coin sequences `e i j = (ω (γ i j d))_d` of a coin layout `γ`. -/
def coinsOf (γ : Fin n → ℕ → ℕ → ι) (ω : ι → Bool) : Fin n → ℕ → ℕ → Bool :=
  fun i j d ↦ ω (γ i j d)

/-- The total absolute weight `Σ_{j<n−1} |w_j|`. -/
noncomputable def absWeightSum (n : ℕ) (w : ℕ → ℝ) : ℝ := ∑ j ∈ range (n - 1), |w j|

/-- `0 ≤ absWeightSum n w`. -/
theorem absWeightSum_nonneg (n : ℕ) (w : ℕ → ℝ) : 0 ≤ absWeightSum n w :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-! ### One cut point -/

/-- The level indicator of a coin sequence as a binary comparison. -/
theorem measurableSet_levelInd_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ)
    (g : ℕ → ι) :
    MeasurableSet {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} := by
  have e : {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} =
      (fun ω : ι → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (ω ((fun j ↦ g (j + m)) j))) ⁻¹'
          Set.Iic (fracPow c m) := by
    ext ω
    exact levelInd_iff_binaryVal_le hc0 hc1 N m _
  rw [e]
  exact (measurable_binaryVal.comp (measurable_xor_digits _ _)) measurableSet_Iic

/-- `P(LevelInd) = {2^m c}` for an injective coin sequence. -/
theorem measureReal_levelInd_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    (coinMeasure ι).real {ω | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} = fracPow c m := by
  have hg' : Function.Injective fun j : ℕ ↦ g (j + m) :=
    fun j j' h ↦ by simpa using hg h
  have hmap := map_binaryVal_xor_eq_uniformIco hg' fun j ↦ (levelBase N m).testBit (j + m)
  have e : {ω : ι → Bool | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} =
      (fun ω : ι → Bool ↦ binaryVal fun j ↦
        xor ((levelBase N m).testBit (j + m)) (ω (g (j + m)))) ⁻¹' Set.Iic (fracPow c m) := by
    ext ω
    exact levelInd_iff_binaryVal_le hc0 hc1 N m _
  have hXm : Measurable (fun ω : ι → Bool ↦ binaryVal fun j ↦
      xor ((levelBase N m).testBit (j + m)) (ω (g (j + m)))) :=
    measurable_binaryVal.comp (measurable_xor_digits (fun j ↦ g (j + m)) _)
  have hf := fracPow_mem_Ico hc0 m
  rw [e, measureReal_def, ← Measure.map_apply hXm measurableSet_Iic, hmap,
    Measure.restrict_apply measurableSet_Iic]
  have hI : Set.Iic (fracPow c m) ∩ Set.Ico 0 1 = Set.Icc 0 (fracPow c m) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, lt_of_le_of_lt h2 hf.2⟩
  rw [hI, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hf.1]

/-- The level indicator of a coin sequence is measurable. -/
theorem measurable_levelVal_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d)) := by
  classical
  unfold levelVal
  exact Measurable.ite (measurableSet_levelInd_coins hc0 hc1 N m g) measurable_const
    measurable_const

/-- The level indicator has mean `{2^m c}`. -/
theorem integral_levelVal_coins {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, levelVal (threshDigit c) N m (fun d ↦ ω (g d)) ∂(coinMeasure ι) = fracPow c m := by
  classical
  have e : (fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d))) =
      Set.indicator {ω | LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} 1 := by
    funext ω
    unfold levelVal
    by_cases h : LevelInd (threshDigit c) N m (fun d ↦ ω (g d))
    · simp only [h, ite_true, Set.indicator_of_mem (show ω ∈ {ω : ι → Bool |
        LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} from h), Pi.one_apply]
    · simp only [h, ite_false, Set.indicator_of_notMem (show ω ∉ {ω : ι → Bool |
        LevelInd (threshDigit c) N m (fun d ↦ ω (g d))} from h)]
  rw [e, integral_indicator_one (measurableSet_levelInd_coins hc0 hc1 N m g),
    measureReal_levelInd_coins hc0 hc1 N m hg]

/-- The level term of a coin sequence is measurable. -/
theorem measurable_cutTerm_coins {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ cutTerm c N m (fun d ↦ ω (g d)) := by
  unfold cutTerm
  by_cases hc1 : c < 1
  · simp only [hc1, ite_true]
    unfold coinTerm levelTerm
    by_cases hb : N.testBit m = true
    · simp only [hb, ite_true]
      exact (measurable_levelVal_coins hc0 hc1 N m g).sub measurable_const
    · simp only [hb, Bool.false_eq_true, ite_false]
      exact measurable_const
  · simp only [hc1, ite_false]
    exact measurable_const

/-- `|cutTerm| ≤ 1`. -/
theorem abs_cutTerm_le {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) (e : ℕ → Bool) :
    |cutTerm c N m e| ≤ 1 := by
  unfold cutTerm
  split_ifs
  · exact abs_coinTerm_le hc0 N m e
  · simp

/-- `|cutTermTrunc| ≤ 1`. -/
theorem abs_cutTermTrunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) (e : ℕ → Bool) :
    |cutTermTrunc c N m L e| ≤ 1 := by
  unfold cutTermTrunc
  split_ifs
  · exact abs_coinTermTrunc_le hc0 N m L e
  · simp

open Classical in
/-- The truncation error of a level term is at most the tie indicator. -/
theorem abs_cutTerm_sub_trunc_le (c : ℝ) (N m L : ℕ) (e : ℕ → Bool) :
    |cutTerm c N m e - cutTermTrunc c N m L e| ≤
      (if LevelTie (threshDigit c) N m L e then 1 else 0) := by
  unfold cutTerm cutTermTrunc
  by_cases hc : c < 1
  · simp only [hc, ite_true]
    exact abs_coinTerm_sub_trunc_le c N m L e
  · simp only [hc, ite_false, sub_self, abs_zero]
    split_ifs <;> norm_num

/-- The tie event of a coin sequence as a cylinder. -/
theorem setOf_levelTie_coins_eq (cb : ℕ → Bool) (N m L : ℕ) (g : ℕ → ι) :
    {ω : ι → Bool | LevelTie cb N m L (fun d ↦ ω (g d))} =
      {ω | ∀ j < L, xor ((levelBase N m).testBit (m + j)) (ω ((fun j ↦ g (m + j)) j)) =
        cb (m + j)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, LevelTie, levelDigits]
  constructor
  · intro h j hj
    exact h (m + j) (by omega) (by omega)
  · intro h j hm hj
    have := h (j - m) (by omega)
    rwa [show m + (j - m) = j by omega] at this

/-- The tie event is measurable. -/
theorem measurableSet_levelTie_coins (cb : ℕ → Bool) (N m L : ℕ) (g : ℕ → ι) :
    MeasurableSet {ω : ι → Bool | LevelTie cb N m L (fun d ↦ ω (g d))} := by
  rw [setOf_levelTie_coins_eq]
  exact measurableSet_xor_cylinder _ _ _ L

/-- **The tie cascade survives `L` levels with probability `2^{-L}`.** -/
theorem measureReal_levelTie_coins (cb : ℕ → Bool) (N m L : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    (coinMeasure ι).real {ω | LevelTie cb N m L (fun d ↦ ω (g d))} = (1 / 2) ^ L := by
  have hg' : Function.Injective fun j : ℕ ↦ g (m + j) :=
    fun j j' h ↦ by simpa using hg h
  rw [setOf_levelTie_coins_eq, measureReal_def, infinitePi_xor_cylinder hg', ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- The truncated level term depends only on the coins of depths `[m, m + L)`. -/
theorem isLocal_cutTermTrunc_coins [DecidableEq ι] (c : ℝ) (N m L : ℕ) (g : ℕ → ι) :
    IsLocal (fun ω : ι → Bool ↦ cutTermTrunc c N m L (fun d ↦ ω (g d)))
      ((Finset.Ico m (m + L)).image g) := by
  intro ω ω' h
  change cutTermTrunc c N m L (fun d ↦ ω (g d)) = cutTermTrunc c N m L (fun d ↦ ω' (g d))
  unfold cutTermTrunc coinTermTrunc
  rw [levelValTrunc_congr (threshDigit c) N m L (e := fun d ↦ ω (g d)) (e' := fun d ↦ ω' (g d))
    fun j hm hj ↦ h (g j) (mem_image_of_mem g (Finset.mem_Ico.2 ⟨hm, hj⟩))]

/-- The truncated level term is measurable. -/
theorem measurable_cutTermTrunc_coins (c : ℝ) (N m L : ℕ) (g : ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ cutTermTrunc c N m L (fun d ↦ ω (g d)) := by
  classical
  exact (isLocal_cutTermTrunc_coins c N m L g).measurable

/-- **Truncation error in `L¹`**: `E|Y − Y_L| ≤ 2^{-L}`. -/
theorem integral_abs_cutTerm_sub_trunc_le {c : ℝ} (hc0 : 0 ≤ c) (N m L : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))|
      ∂(coinMeasure ι) ≤ (1 / 2) ^ L := by
  classical
  set S := {ω : ι → Bool | LevelTie (threshDigit c) N m L (fun d ↦ ω (g d))} with hS
  have hSm : MeasurableSet S := measurableSet_levelTie_coins _ N m L g
  have hpt : ∀ ω, |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))| ≤
      S.indicator 1 ω := by
    intro ω
    refine (abs_cutTerm_sub_trunc_le c N m L _).trans (le_of_eq ?_)
    by_cases ht : LevelTie (threshDigit c) N m L (fun d ↦ ω (g d))
    · simp only [ht, ite_true, Set.indicator_of_mem (show ω ∈ S from ht), Pi.one_apply]
    · simp only [ht, ite_false, Set.indicator_of_notMem (show ω ∉ S from ht)]
  have hm : Measurable fun ω : ι → Bool ↦
      |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))| :=
    continuous_abs.measurable.comp
      ((measurable_cutTerm_coins hc0 N m g).sub (measurable_cutTermTrunc_coins c N m L g))
  have hint : Integrable (fun ω : ι → Bool ↦
      |cutTerm c N m (fun d ↦ ω (g d)) - cutTermTrunc c N m L (fun d ↦ ω (g d))|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 2 (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_cutTerm_le hc0 N m (fun d ↦ ω (g d))
    have h2 := abs_cutTermTrunc_le hc0 N m L (fun d ↦ ω (g d))
    have := abs_sub (cutTerm c N m (fun d ↦ ω (g d))) (cutTermTrunc c N m L (fun d ↦ ω (g d)))
    linarith
  have hind : Integrable (S.indicator (1 : (ι → Bool) → ℝ)) (coinMeasure ι) :=
    (integrable_const (1 : ℝ)).indicator hSm
  refine (integral_mono hint hind hpt).trans (le_of_eq ?_)
  rw [integral_indicator_one hSm, measureReal_levelTie_coins _ N m L hg]

/-- **Level terms are centred.** -/
theorem integral_cutTerm_coins {c : ℝ} (hc0 : 0 ≤ c) (N m : ℕ) {g : ℕ → ι}
    (hg : Function.Injective g) :
    ∫ ω, cutTerm c N m (fun d ↦ ω (g d)) ∂(coinMeasure ι) = 0 := by
  unfold cutTerm
  by_cases hc1 : c < 1
  · simp only [hc1, ite_true]
    unfold coinTerm levelTerm
    by_cases hb : N.testBit m = true
    · simp only [hb, ite_true]
      have hi : Integrable (fun ω : ι → Bool ↦ levelVal (threshDigit c) N m (fun d ↦ ω (g d)))
          (coinMeasure ι) := by
        refine Integrable.of_bound (measurable_levelVal_coins hc0 hc1 N m g).aestronglyMeasurable
          1 (Eventually.of_forall fun ω ↦ ?_)
        rcases levelVal_mem (threshDigit c) N m (fun d ↦ ω (g d)) with h | h <;> rw [h] <;> simp
      rw [integral_sub hi (integrable_const _), integral_levelVal_coins hc0 hc1 N m hg,
        integral_const, probReal_univ, one_smul, fracPow, sub_self]
    · simp only [hb, Bool.false_eq_true, ite_false, integral_zero]
  · simp only [hc1, ite_false, integral_zero]

/-! ### Rows and levels -/

variable {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ}

/-- `|rowTerm| ≤ W = Σ_j |w_j|`. -/
theorem abs_rowTerm_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) : |rowTerm w cp N m e i| ≤ absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutTerm_le (hcp i j) _ m _)

/-- `|rowTermTrunc| ≤ W`. -/
theorem abs_rowTermTrunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) (i : Fin n) :
    |rowTermTrunc w cp N m L e i| ≤ absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutTermTrunc_le (hcp i j) _ m L _)

/-- `|rowTerm − rowTermTrunc| ≤ W`. -/
theorem abs_rowTerm_sub_trunc_le (N : Fin n → ℕ) (m L : ℕ) (e : Fin n → ℕ → ℕ → Bool)
    (i : Fin n) : |rowTerm w cp N m e i - rowTermTrunc w cp N m L e i| ≤ absWeightSum n w := by
  classical
  rw [rowTerm, rowTermTrunc, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  rw [← mul_sub, abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ((abs_cutTerm_sub_trunc_le _ _ m L _).trans ?_)
  split_ifs <;> norm_num

/-- The row term of a coin layout is measurable. -/
theorem measurable_rowTerm_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) :
    Measurable fun ω : ι → Bool ↦ rowTerm w cp N m (coinsOf γ ω) i :=
  Finset.measurable_fun_sum _ fun j _ ↦
    (measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).const_mul (w j)

/-- The truncated row term depends only on coordinates `γ i j d`, `d ∈ [m, m + L)`. -/
theorem isLocal_rowTermTrunc_coins [DecidableEq ι] (N : Fin n → ℕ) (m L : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) :
    IsLocal (fun ω : ι → Bool ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)
      ((range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)) :=
  isLocal_sum _ fun j hj ↦ ((isLocal_cutTermTrunc_coins (cp i j) (N i) m L (γ i j)).comp
    (fun x ↦ w j * x)).mono
      (subset_biUnion_of_mem (fun j ↦ (Finset.Ico m (m + L)).image (γ i j)) hj)

/-- The truncated row term is measurable. -/
theorem measurable_rowTermTrunc_coins (N : Fin n → ℕ) (m L : ℕ) (γ : Fin n → ℕ → ℕ → ι)
    (i : Fin n) : Measurable fun ω : ι → Bool ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i := by
  classical
  exact (isLocal_rowTermTrunc_coins N m L γ i).measurable

/-- **Row truncation error in `L¹`**: `E|row − row_L| ≤ W 2^{-L}`. -/
theorem integral_abs_rowTerm_sub_trunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
      ∂(coinMeasure ι) ≤ absWeightSum n w * (1 / 2) ^ L := by
  have hint : ∀ j, Integrable (fun ω : ι → Bool ↦ |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
      cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)|) (coinMeasure ι) := by
    intro j
    refine Integrable.of_bound (continuous_abs.measurable.comp
      ((measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).sub
      (measurable_cutTermTrunc_coins (cp i j) (N i) m L (γ i j)))).aestronglyMeasurable 2
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_cutTerm_le (hcp i j) (N i) m (coinsOf γ ω i j)
    have h2 := abs_cutTermTrunc_le (hcp i j) (N i) m L (coinsOf γ ω i j)
    have := abs_sub (cutTerm (cp i j) (N i) m (coinsOf γ ω i j))
      (cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j))
    linarith
  have hpt : ∀ ω : ι → Bool,
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i| ≤
      ∑ j ∈ range (n - 1), |w j| * |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
        cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)| := by
    intro ω
    rw [rowTerm, rowTermTrunc, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ ↦ ?_))
    rw [← mul_sub, abs_mul]
  have hm : Measurable fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i| :=
    continuous_abs.measurable.comp
      ((measurable_rowTerm_coins hcp N m γ i).sub (measurable_rowTermTrunc_coins N m L γ i))
  have hi1 : Integrable (fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (absWeightSum n w)
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_rowTerm_sub_trunc_le N m L _ i
  have hi2 : Integrable (fun ω : ι → Bool ↦ ∑ j ∈ range (n - 1),
      |w j| * |cutTerm (cp i j) (N i) m (coinsOf γ ω i j) -
        cutTermTrunc (cp i j) (N i) m L (coinsOf γ ω i j)|) (coinMeasure ι) :=
    integrable_finsetSum _ fun j _ ↦ (hint j).const_mul _
  refine (integral_mono hi1 hi2 hpt).trans ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint j).const_mul _, absWeightSum, sum_mul]
  refine sum_le_sum fun j _ ↦ ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_abs_cutTerm_sub_trunc_le (hcp i j) (N i) m L (hγ i j)) (abs_nonneg _)

/-- **Row terms are centred.** -/
theorem integral_rowTerm_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    ∫ ω, rowTerm w cp N m (coinsOf γ ω) i ∂(coinMeasure ι) = 0 := by
  have hint : ∀ j, Integrable (fun ω : ι → Bool ↦ w j * cutTerm (cp i j) (N i) m
      (coinsOf γ ω i j)) (coinMeasure ι) := fun j ↦
    (Integrable.of_bound (measurable_cutTerm_coins (hcp i j) (N i) m (γ i j)).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_cutTerm_le (hcp i j) _ m _)).const_mul _
  unfold rowTerm
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  refine sum_eq_zero fun j _ ↦ ?_
  rw [integral_const_mul]
  change w j * ∫ ω, cutTerm (cp i j) (N i) m (fun d ↦ ω (γ i j d)) ∂(coinMeasure ι) = 0
  rw [integral_cutTerm_coins (hcp i j) (N i) m (hγ i j), mul_zero]

/-- The level-`m` term `Σ_i rowTerm … m … i`. -/
noncomputable def levelYN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ i, rowTerm w cp N m e i

/-- The truncated level term. -/
noncomputable def levelYNTrunc (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : ℝ :=
  ∑ i, rowTermTrunc w cp N m L e i

/-- `levelSumN = Σ_{m<K} levelYN`. -/
theorem levelSumN_eq_sum_levelYN (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) :
    levelSumN w cp N K e = ∑ m ∈ range K, levelYN w cp N m e := rfl

/-- `|levelYN| ≤ n W`. -/
theorem abs_levelYN_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelYN w cp N m e| ≤ n * absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |rowTerm w cp N m e i| ≤ ∑ _i : Fin n, absWeightSum n w :=
        sum_le_sum fun i _ ↦ abs_rowTerm_le hcp N m e i
    _ = n * absWeightSum n w := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|levelYNTrunc| ≤ n W`. -/
theorem abs_levelYNTrunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelYNTrunc w cp N m L e| ≤ n * absWeightSum n w := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |rowTermTrunc w cp N m L e i| ≤ ∑ _i : Fin n, absWeightSum n w :=
        sum_le_sum fun i _ ↦ abs_rowTermTrunc_le hcp N m L e i
    _ = n * absWeightSum n w := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `|levelYN − levelYNTrunc| ≤ Σ_i |row_i − row_{i,L}|`. -/
theorem abs_levelYN_sub_trunc_le (N : Fin n → ℕ) (m L : ℕ) (e : Fin n → ℕ → ℕ → Bool) :
    |levelYN w cp N m e - levelYNTrunc w cp N m L e| ≤
      ∑ i, |rowTerm w cp N m e i - rowTermTrunc w cp N m L e i| := by
  rw [levelYN, levelYNTrunc, ← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-- The level term of a coin layout is measurable. -/
theorem measurable_levelYN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) : Measurable fun ω : ι → Bool ↦ levelYN w cp N m (coinsOf γ ω) :=
  Finset.measurable_fun_sum _ fun i _ ↦ measurable_rowTerm_coins hcp N m γ i

/-- The coordinates of levels `[m, m + L)` used by the truncated level term. -/
def levelCoords [DecidableEq ι] (n : ℕ) (γ : Fin n → ℕ → ℕ → ι) (m L : ℕ) : Finset ι :=
  univ.biUnion fun i ↦ (range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)

/-- The coordinates of `levelCoords` have levels in `[m, m + L)`. -/
theorem lev_mem_of_mem_levelCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {m L : ℕ} {q : ι} (hq : q ∈ levelCoords n γ m L) :
    m ≤ lev q ∧ lev q < m + L := by
  simp only [levelCoords, mem_biUnion, mem_univ, true_and, mem_image, Finset.mem_Ico] at hq
  obtain ⟨i, j, _, d, hd, rfl⟩ := hq
  rw [hlev]
  exact hd

/-- The truncated level term is local on `levelCoords`. -/
theorem isLocal_levelYNTrunc_coins [DecidableEq ι] (N : Fin n → ℕ) (m L : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    IsLocal (fun ω : ι → Bool ↦ levelYNTrunc w cp N m L (coinsOf γ ω)) (levelCoords n γ m L) :=
  isLocal_sum _ fun i _ ↦ (isLocal_rowTermTrunc_coins N m L γ i).mono
    (subset_biUnion_of_mem (fun i ↦ (range (n - 1)).biUnion fun j ↦
      (Finset.Ico m (m + L)).image (γ i j)) (mem_univ i))

/-- **Level truncation error in `L¹`**: `E|Y − Y_L| ≤ n W 2^{-L}`. -/
theorem integral_abs_levelYN_sub_trunc_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m L : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) :
    ∫ ω, |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)|
      ∂(coinMeasure ι) ≤ n * absWeightSum n w * (1 / 2) ^ L := by
  classical
  have hi : ∀ i, Integrable (fun ω : ι → Bool ↦
      |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|)
      (coinMeasure ι) := fun i ↦
    Integrable.of_bound (continuous_abs.measurable.comp ((measurable_rowTerm_coins hcp N m γ i).sub
      (measurable_rowTermTrunc_coins N m L γ i))).aestronglyMeasurable (absWeightSum n w)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]; exact abs_rowTerm_sub_trunc_le N m L _ i)
  have hm : Measurable fun ω : ι → Bool ↦
      |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)| :=
    continuous_abs.measurable.comp ((measurable_levelYN_coins hcp N m γ).sub
      (isLocal_levelYNTrunc_coins N m L γ).measurable)
  have hi1 : Integrable (fun ω : ι → Bool ↦
      |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m L (coinsOf γ ω)|)
      (coinMeasure ι) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (2 * (n * absWeightSum n w))
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_levelYN_le (w := w) hcp N m (coinsOf γ ω)
    have h2 := abs_levelYNTrunc_le (w := w) hcp N m L (coinsOf γ ω)
    have := abs_sub (levelYN w cp N m (coinsOf γ ω)) (levelYNTrunc w cp N m L (coinsOf γ ω))
    linarith
  refine (integral_mono hi1 (integrable_finsetSum _ fun i _ ↦ hi i)
    fun ω ↦ abs_levelYN_sub_trunc_le N m L _).trans ?_
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  calc ∑ i, ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
        ∂(coinMeasure ι) ≤ ∑ _i : Fin n, absWeightSum n w * (1 / 2) ^ L :=
        sum_le_sum fun i _ ↦ integral_abs_rowTerm_sub_trunc_le hcp N m L hγ i
    _ = n * absWeightSum n w * (1 / 2) ^ L := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Level sums are centred.** -/
theorem integral_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) :
    ∫ ω, levelSumN w cp N K (coinsOf γ ω) ∂(coinMeasure ι) = 0 := by
  have hint : ∀ m i, Integrable (fun ω : ι → Bool ↦ rowTerm w cp N m (coinsOf γ ω) i)
      (coinMeasure ι) := fun m i ↦
    Integrable.of_bound (measurable_rowTerm_coins hcp N m γ i).aestronglyMeasurable
      (absWeightSum n w) (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N m _ i)
  unfold levelSumN
  rw [integral_finsetSum _ fun m _ ↦ integrable_finsetSum _ fun i _ ↦ hint m i]
  refine sum_eq_zero fun m _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ hint m i]
  exact sum_eq_zero fun i _ ↦ integral_rowTerm_coins hcp N m hγ i

/-- Level sums of a coin layout are measurable. -/
theorem measurable_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    Measurable fun ω : ι → Bool ↦ levelSumN w cp N K (coinsOf γ ω) :=
  Finset.measurable_fun_sum _ fun m _ ↦ measurable_levelYN_coins hcp N m γ

/-- Level sums are bounded by `K n W`. -/
theorem abs_levelSumN_le (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (e : Fin n → ℕ → ℕ → Bool) : |levelSumN w cp N K e| ≤ K * (n * absWeightSum n w) := by
  rw [levelSumN_eq_sum_levelYN]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ range K, |levelYN w cp N m e| ≤ ∑ _m ∈ range K, (n * absWeightSum n w) :=
        sum_le_sum fun m _ ↦ abs_levelYN_le hcp N m e
    _ = K * (n * absWeightSum n w) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Level sums of a coin layout are in `L²`. -/
theorem memLp_levelSumN_coins (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ)
    (γ : Fin n → ℕ → ℕ → ι) :
    MemLp (fun ω : ι → Bool ↦ levelSumN w cp N K (coinsOf γ ω)) 2 (coinMeasure ι) :=
  MemLp.of_bound (measurable_levelSumN_coins hcp N K γ).aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_levelSumN_le hcp N K _)

/-! ### The CLT for level sums -/

/-- **The CLT for level sums of a coin layout.** Let `lev (γ i j d) = d`, the cut points be
nonnegative, `K_k → ∞` and `Var(levelSumN) ≥ κ K_k` eventually. Then the normalised level sums
are asymptotically `N(0,1)`. -/
theorem tendstoInDistribution_levelSumN (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) {N : ℕ → Fin n → ℕ}
    {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * K k ≤ Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω) /
      √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]) atTop Z
      (fun _ ↦ coinMeasure ι) P' := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  set Y : ℕ → ℕ → (ι → Bool) → ℝ := fun k m ω ↦ levelYN w cp (N k) m (coinsOf γ ω) with hY
  set Yt : ℕ → ℕ → ℕ → (ι → Bool) → ℝ := fun k m L ω ↦
    levelYNTrunc w cp (N k) m L (coinsOf γ ω) with hYt
  have h := tendstoInDistribution_of_truncations (fun _ : ι ↦ fairCoin) lev hK
    (Y := Y) (Yt := Yt) (B := B) (C := B ^ 2)
    (fun k m ↦ measurable_levelYN_coins hcp (N k) m γ)
    (fun k m ω ↦ abs_levelYN_le hcp (N k) m _) (fun k m L ω ↦ abs_levelYNTrunc_le hcp (N k) m L _)
    (fun k m L ↦ ⟨levelCoords n γ m L, fun q hq ↦ lev_mem_of_mem_levelCoords hlev hq,
      isLocal_levelYNTrunc_coins (N k) m L γ⟩) (fun k m L ↦ ?_) hκ hvar hZ
  · have e : (fun k ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω) /
        √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]) =
        fun k ω ↦ ((∑ m ∈ range (K k), Y k m ω) -
          (coinMeasure ι)[fun ω ↦ ∑ m ∈ range (K k), Y k m ω]) /
          √Var[fun ω ↦ ∑ m ∈ range (K k), Y k m ω; coinMeasure ι] := by
      funext k ω
      have h0 := integral_levelSumN_coins (w := w) hcp (N k) (K k) hγ
      change levelSumN w cp (N k) (K k) (coinsOf γ ω) /
          √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι] =
        (levelSumN w cp (N k) (K k) (coinsOf γ ω) -
          ∫ ω, levelSumN w cp (N k) (K k) (coinsOf γ ω) ∂(coinMeasure ι)) /
          √Var[fun ω ↦ levelSumN w cp (N k) (K k) (coinsOf γ ω); coinMeasure ι]
      rw [h0, sub_zero]
    rw [e]
    exact h
  · -- the `L²` truncation error
    have hd : ∀ ω, |Y k m ω - Yt k m L ω| ≤ 2 * B := fun ω ↦ by
      have h1 := abs_levelYN_le (w := w) hcp (N k) m (coinsOf γ ω)
      have h2 := abs_levelYNTrunc_le (w := w) hcp (N k) m L (coinsOf γ ω)
      have := abs_sub (Y k m ω) (Yt k m L ω)
      simp only [hY, hYt] at this ⊢
      linarith
    have hpt : ∀ ω, (Y k m ω - Yt k m L ω) ^ 2 ≤ B * |Y k m ω - Yt k m L ω| := by
      intro ω
      have h1 : |Y k m ω - Yt k m L ω| ≤ B := by
        refine (abs_levelYN_sub_trunc_le (N k) m L _).trans ?_
        calc ∑ i, |rowTerm w cp (N k) m (coinsOf γ ω) i -
              rowTermTrunc w cp (N k) m L (coinsOf γ ω) i|
            ≤ ∑ _i : Fin n, absWeightSum n w :=
              sum_le_sum fun i _ ↦ abs_rowTerm_sub_trunc_le (N k) m L _ i
          _ = B := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← sq_abs]
      nlinarith [abs_nonneg (Y k m ω - Yt k m L ω)]
    have hm : Measurable fun ω ↦ Y k m ω - Yt k m L ω :=
      (measurable_levelYN_coins hcp (N k) m γ).sub
        (isLocal_levelYNTrunc_coins (N k) m L γ).measurable
    have hi1 : Integrable (fun ω ↦ (Y k m ω - Yt k m L ω) ^ 2) (coinMeasure ι) := by
      refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
        (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd ω) 2
    have hi2 : Integrable (fun ω ↦ B * |Y k m ω - Yt k m L ω|) (coinMeasure ι) :=
      (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable (2 * B)
        (Eventually.of_forall fun ω ↦ by
          change ‖|Y k m ω - Yt k m L ω|‖ ≤ 2 * B
          rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul B
    refine (integral_mono hi1 hi2 hpt).trans ?_
    rw [integral_const_mul]
    have := integral_abs_levelYN_sub_trunc_le (w := w) hcp (N k) m L hγ
    calc B * ∫ ω, |Y k m ω - Yt k m L ω| ∂(coinMeasure ι) ≤ B * (B * (1 / 2) ^ L) :=
          mul_le_mul_of_nonneg_left this hB0
      _ = B ^ 2 * (1 / 2) ^ L := by ring

/-! ### Slutsky assembly -/

/-- **Slutsky assembly.** Let `E_k` be within `b_k` of a centred `M_k`, with
`b_k² / log₂ T_k → 0` and `Var E_k ≥ κ log₂ T_k` eventually. If `M_k` satisfies the CLT whenever
`Var M_k ≥ κ' (⌊log₂ T_k⌋ + 1)` eventually, then `E_k / √Var E_k ⇒ Z`. -/
theorem tendstoInDistribution_of_close_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {T : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    {b : ℕ → ℝ} (hb : Tendsto (fun k ↦ b k ^ 2 / Nat.log 2 (T k)) atTop (𝓝 0))
    (hE : ∀ k, MemLp (E k) 2 μ) (hM : ∀ k, MemLp (M k) 2 μ) (hM0 : ∀ k, μ[M k] = 0)
    (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop, κ * Nat.log 2 (T k) ≤ Var[E k; μ])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    (hclt : ∀ κ' : ℝ, 0 < κ' →
      (∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[M k; μ]) →
        TendstoInDistribution (fun k ω ↦ M k ω / √Var[M k; μ]) atTop Z (fun _ ↦ μ) P') :
    TendstoInDistribution (fun k ω ↦ E k ω / √Var[E k; μ]) atTop Z (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  have hlogT : Tendsto (fun k ↦ Nat.log 2 (T k)) atTop atTop :=
    (tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp hT
  have hlog1 : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (T k) := hlogT.eventually_ge_atTop 1
  have hbE : Tendsto (fun k ↦ b k ^ 2 / Var[E k; μ]) atTop (𝓝 0) := by
    have h := hb.div_const κ
    rw [zero_div] at h
    refine squeeze_zero' (Eventually.of_forall fun k ↦ by
      have := variance_nonneg (E k) μ
      have := hb0 k
      positivity) ?_ h
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (0 : ℝ) < Nat.log 2 (T k) := by exact_mod_cast hl
    rw [div_div, mul_comm (Nat.log 2 (T k) : ℝ) κ]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk
  have hpos : ∀ᶠ k in atTop, 0 < Var[E k; μ] := by
    filter_upwards [hvar, hlog1] with k hk hl
    have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
    nlinarith
  refine tendstoInDistribution_of_abs_sub_le hE hM hM0 hclose hbE hpos ?_
  refine hclt (κ / 8) (by positivity) ?_
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / Var[E k; μ] ≤ 1 / 4 :=
    hbE.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hvar, hlog1, hsmall, hpos] with k hk hl hs hp
  have hl' : (1 : ℝ) ≤ Nat.log 2 (T k) := by exact_mod_cast hl
  have hσ : |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  set sE := √Var[E k; μ] with hsE
  set sM := √Var[M k; μ] with hsM
  have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt hp.le
  have hbsE : b k ≤ sE / 2 := by
    rw [div_le_iff₀ hp, ← hsE2] at hs
    have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
    by_contra hc
    push Not at hc
    nlinarith [hb0 k]
  have hsMge : sE / 2 ≤ sM := by
    have := (abs_le.1 hσ).1
    linarith
  have hsE0 : 0 ≤ sE / 2 := by positivity
  have hVM : sE ^ 2 / 4 ≤ Var[M k; μ] := by
    have := pow_le_pow_left₀ hsE0 hsMge 2
    rw [hsM, Real.sq_sqrt (variance_nonneg _ _), div_pow] at this
    linarith
  have hK2 : ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ 2 * Nat.log 2 (T k) := by
    push_cast
    linarith
  calc κ / 8 * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ κ / 8 * (2 * Nat.log 2 (T k)) := by gcongr
    _ = κ * Nat.log 2 (T k) / 4 := by ring
    _ ≤ sE ^ 2 / 4 := by rw [hsE2]; linarith
    _ ≤ Var[M k; μ] := hVM

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Variance of level sums of fair coins (for post #3, n states)

The CLT of `CltNCoins` normalises by the standard deviation and needs `Var ≥ κ log T`. This
module gives the matching upper bound `Var = O(K)` for every coin layout, and a lower-bound
criterion for level sums along sparse ("pattern") indices, which is used for the non-vacuity
examples (`CltNExample`) under both randomisations.

Two level terms at levels `m < m'` are almost uncorrelated: the level-`m` term, truncated at
depth `m' − m`, depends only on coordinates of levels `[m, m')`, which are independent of the
level-`m'` term; the truncation costs `2^{-(m'-m)}` in `L¹`. No independence between cut points of
the same row is needed (they share coordinates for the digital shift and, along common binary
prefixes, for Owen's scramble).

## Main results

* `abs_covariance_le_of_bound`: `|cov[R, Y]| ≤ 2B E|R|` for `|Y| ≤ B`.
* `abs_covariance_le_of_local`: if `X` is `L¹`-close to a function of coordinates `S`, and `Y` is
  an `L¹`-limit of functions of coordinates disjoint from `S`, then `|cov[X, Y]| ≤ 2B E|X − X_S|`.
* `abs_covariance_levelYN_le`, `variance_levelSumN_le` (**upper bound**):
  `Var(levelSumN) ≤ 5 (nW)² K` for `K` levels, every coin layout.
* `variance_ge_of_int` (**integer variance bound**): an integer-valued `X` has
  `Var X ≥ φ(1 − φ)`, `φ` the fractional part of `E X`.
* `variance_rowTerm_ge_of_int`: a row term with integer weights at a level of a set bit has
  variance at least `φ(1−φ)` for `φ = {Σ_j w_j {2^m c_{ij}}}`, under ANY coin layout.
* `patternR r k = Σ_{a<k} 2^{ra}`, `testBit_patternR`.
* `covariance_rowTerm_eq_zero` (different rows, disjoint coordinates), `abs_covariance_rowTerm_le`.
* `variance_levelSumN_pattern_ge` (**lower-bound criterion**): at indices `patternR r k` in every
  row, rows on disjoint coordinates, and row-term variances `≥ a₀`:
  `Var ≥ n k (a₀ − 4 W² ρ/(1 − ρ))`, `ρ = 2^{-r}`.
* Mean-square tools: `natLog_add_one_sq_le`, `integral_sq_le_of_close`,
  `integral_sq_levelSumN_le`, `isBigO_meanSq_div_of_le`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Covariance tools -/

/-- **Covariance with a bounded variable**: `|cov[R, Y]| ≤ 2B E|R|` when `|Y| ≤ B`. -/
theorem abs_covariance_le_of_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {R Y : Ω → ℝ} (hR : MemLp R 2 μ) (hYm : Measurable Y) {B : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ B) : |cov[R, Y; μ]| ≤ 2 * B * ∫ ω, |R ω| ∂μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hYb (Classical.arbitrary Ω))
  have hI0 : 0 ≤ ∫ ω, |R ω| ∂μ := integral_nonneg fun ω ↦ abs_nonneg _
  rcases hB0.lt_or_eq with hB | hB
  · have e : Y = fun ω ↦ (2 * B) * (Y ω / (2 * B)) := funext fun ω ↦ by field_simp
    rw [e, covariance_const_mul_right, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * B)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine abs_covariance_le_integral_abs hR (hYm.div_const _) (a := -1 / 2) fun ω ↦ ?_
    have h := abs_le.1 (hYb ω)
    constructor
    · rw [le_div_iff₀ (by positivity)]
      linarith
    · rw [div_le_iff₀ (by positivity)]
      linarith
  · have e : Y = fun ω ↦ 0 * Y ω := funext fun ω ↦ by
      have := hYb ω
      rw [← hB] at this
      rw [zero_mul]
      exact abs_nonpos_iff.1 this
    rw [e, covariance_const_mul_right, zero_mul, abs_zero]
    positivity

variable {ι : Type*} {n : ℕ}

/-- **Covariance across disjoint coordinates.** On fair coins, let `|X|, |Y|, |X_S|, |Y_L| ≤ B`,
`X_S` depend only on the coordinates in `S`, each `Y_L` only on coordinates disjoint from `S`,
and `E|Y − Y_L| → 0`. Then `|cov[X, Y]| ≤ 2B E|X − X_S|`. -/
theorem abs_covariance_le_of_local {X Y Xt : (ι → Bool) → ℝ} {Yt : ℕ → (ι → Bool) → ℝ}
    {S : Finset ι} {S' : ℕ → Finset ι} {B : ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    (hXb : ∀ ω, |X ω| ≤ B) (hYb : ∀ ω, |Y ω| ≤ B) (hXtb : ∀ ω, |Xt ω| ≤ B)
    (hYtb : ∀ L ω, |Yt L ω| ≤ B) (hXt : IsLocal Xt S) (hYt : ∀ L, IsLocal (Yt L) (S' L))
    (hdisj : ∀ L, Disjoint S (S' L))
    (hYe : Tendsto (fun L ↦ ∫ ω, |Y ω - Yt L ω| ∂(coinMeasure ι)) atTop (𝓝 0)) :
    |cov[X, Y; coinMeasure ι]| ≤ 2 * B * ∫ ω, |X ω - Xt ω| ∂(coinMeasure ι) := by
  have hX2 : MemLp X 2 (coinMeasure ι) := MemLp.of_bound hXm.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hXb ω)
  have hY2 : MemLp Y 2 (coinMeasure ι) := MemLp.of_bound hYm.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYb ω)
  have hXt2 : MemLp Xt 2 (coinMeasure ι) := MemLp.of_bound hXt.measurable.aestronglyMeasurable B
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hXtb ω)
  have hYt2 : ∀ L, MemLp (Yt L) 2 (coinMeasure ι) := fun L ↦
    MemLp.of_bound (hYt L).measurable.aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYtb L ω)
  have hYvar : Tendsto (fun L ↦ Var[Y - Yt L; coinMeasure ι]) atTop (𝓝 0) := by
    have hlim := hYe.const_mul (2 * B)
    rw [mul_zero] at hlim
    refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_) hlim
    refine (variance_le_expectation_sq (hY2.sub (hYt2 L)).aestronglyMeasurable).trans ?_
    have hd : ∀ ω, |(Y - Yt L) ω| ≤ 2 * B := fun ω ↦ by
      have := abs_sub (Y ω) (Yt L ω)
      simp only [Pi.sub_apply]
      linarith [hYb ω, hYtb L ω]
    have hm : Measurable (Y - Yt L) := hYm.sub (hYt L).measurable
    have hi1 : Integrable ((Y - Yt L) ^ 2) (coinMeasure ι) :=
      (hY2.sub (hYt2 L)).integrable_sq
    have hi2 : Integrable (fun ω ↦ 2 * B * |Y ω - Yt L ω|) (coinMeasure ι) :=
      (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable (2 * B)
        (Eventually.of_forall fun ω ↦ by
          change ‖|(Y - Yt L) ω|‖ ≤ 2 * B
          rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul _
    refine (integral_mono hi1 hi2 fun ω ↦ ?_).trans (le_of_eq (integral_const_mul _ _))
    have h1 := hd ω
    simp only [Pi.pow_apply, Pi.sub_apply] at h1 ⊢
    rw [← sq_abs]
    nlinarith [abs_nonneg (Y ω - Yt L ω)]
  have h0 : cov[Xt, Y; coinMeasure ι] = 0 := by
    refine covariance_eq_zero_of_approx hXt2 hY2 (Xa := fun _ ↦ Xt) (fun _ ↦ hXt2) hYt2
      (fun L ↦ IsLocal.indepFun (fun _ ↦ fairCoin) hXt (hYt L) (hdisj L)) ?_ hYvar
    simp only [sub_self, variance_zero, tendsto_const_nhds]
  have e : cov[X, Y; coinMeasure ι] = cov[X - Xt, Y; coinMeasure ι] := by
    rw [covariance_sub_left hX2 hXt2 hY2, h0, sub_zero]
  rw [e]
  exact abs_covariance_le_of_bound (hX2.sub hXt2) hYm hYb

/-! ### The upper bound -/

variable {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ}

/-- Coordinates of disjoint level ranges are disjoint. -/
theorem disjoint_levelCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {m m' L L' : ℕ} (h : m + L ≤ m') :
    Disjoint (levelCoords n γ m L) (levelCoords n γ m' L') := by
  refine Finset.disjoint_left.2 fun q hq hq' ↦ ?_
  have h1 := lev_mem_of_mem_levelCoords hlev hq
  have h2 := lev_mem_of_mem_levelCoords hlev hq'
  omega

/-- **Level terms decorrelate geometrically**: for `m < m'`,
`|cov[Y_m, Y'_{m'}]| ≤ 2 (nW)² 2^{-(m'-m)}` (any index vectors `N`, `N'`). -/
theorem abs_covariance_levelYN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N N' : Fin n → ℕ)
    {m m' : ℕ} (hmm' : m < m') :
    |cov[fun ω ↦ levelYN w cp N m (coinsOf γ ω), fun ω ↦ levelYN w cp N' m' (coinsOf γ ω);
      coinMeasure ι]| ≤ 2 * (n * absWeightSum n w) ^ 2 * (1 / 2) ^ (m' - m) := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  have h := abs_covariance_le_of_local (B := B)
    (Xt := fun ω ↦ levelYNTrunc w cp N m (m' - m) (coinsOf γ ω))
    (Yt := fun L ω ↦ levelYNTrunc w cp N' m' L (coinsOf γ ω))
    (S := levelCoords n γ m (m' - m)) (S' := fun L ↦ levelCoords n γ m' L)
    (measurable_levelYN_coins hcp N m γ) (measurable_levelYN_coins hcp N' m' γ)
    (fun ω ↦ abs_levelYN_le hcp N m _) (fun ω ↦ abs_levelYN_le hcp N' m' _)
    (fun ω ↦ abs_levelYNTrunc_le hcp N m _ _) (fun L ω ↦ abs_levelYNTrunc_le hcp N' m' L _)
    (isLocal_levelYNTrunc_coins N m (m' - m) γ) (fun L ↦ isLocal_levelYNTrunc_coins N' m' L γ)
    (fun L ↦ disjoint_levelCoords hlev (by omega)) ?_
  · refine h.trans ?_
    have := integral_abs_levelYN_sub_trunc_le (w := w) hcp N m (m' - m) hγ
    calc 2 * B * ∫ ω, |levelYN w cp N m (coinsOf γ ω) - levelYNTrunc w cp N m (m' - m)
          (coinsOf γ ω)| ∂(coinMeasure ι) ≤ 2 * B * (B * (1 / 2) ^ (m' - m)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * B ^ 2 * (1 / 2) ^ (m' - m) := by ring
  · have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul B
    rw [mul_zero] at hlim
    exact squeeze_zero (fun L ↦ integral_nonneg fun ω ↦ abs_nonneg _)
      (fun L ↦ integral_abs_levelYN_sub_trunc_le (w := w) hcp N' m' L hγ) hlim

/-- **Variance upper bound**: `Var(levelSumN) ≤ 5 (nW)² K` for every coin layout. -/
theorem variance_levelSumN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ) :
    Var[fun ω ↦ levelSumN w cp N K (coinsOf γ ω); coinMeasure ι] ≤
      K * (5 * (n * absWeightSum n w) ^ 2) := by
  set B := n * absWeightSum n w with hB
  have hB0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg n) (absWeightSum_nonneg n w)
  set Z : ℕ → (ι → Bool) → ℝ := fun m ω ↦ levelYN w cp N m (coinsOf γ ω) with hZ
  have hZ2 : ∀ m ∈ range K, MemLp (Z m) 2 (coinMeasure ι) := fun m _ ↦
    MemLp.of_bound (measurable_levelYN_coins hcp N m γ).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_levelYN_le hcp N m _)
  have e : (fun ω ↦ levelSumN w cp N K (coinsOf γ ω)) = fun ω ↦ ∑ m ∈ range K, Z m ω := rfl
  rw [e]
  have h := variance_sum_le_of_cov (μ := coinMeasure ι) (range K) hZ2 (A := B ^ 2)
    (β := 4 * B ^ 2) (fun m _ ↦ ?_) (fun m _ ↦ ?_)
  · rw [card_range] at h
    refine h.trans (le_of_eq ?_)
    ring
  · refine (variance_le_sq_of_bounded (a := -B) (b := B) (Eventually.of_forall fun ω ↦
      abs_le.1 (abs_levelYN_le hcp N m _))
      (measurable_levelYN_coins hcp N m γ).aemeasurable).trans (le_of_eq ?_)
    ring
  · have hcov : ∀ m' ∈ (range K).erase m, |cov[Z m, Z m'; coinMeasure ι]| ≤
        2 * B ^ 2 * (1 / 2) ^ (m - m' + (m' - m)) := by
      intro m' hm'
      have hne := ne_of_mem_erase hm'
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := abs_covariance_levelYN_le lev hlev hcp (w := w) N N hlt
        rw [covariance_comm, show m - m' + (m' - m) = m - m' by omega]
        exact this
      · have := abs_covariance_levelYN_le lev hlev hcp (w := w) N N hlt
        rw [show m - m' + (m' - m) = m' - m by omega]
        exact this
    have hgeo := sum_erase_pow_dist_le (r := 1 / 2) (by norm_num) (by norm_num) m K
    calc ∑ m' ∈ (range K).erase m, |cov[Z m, Z m'; coinMeasure ι]|
        ≤ ∑ m' ∈ (range K).erase m, 2 * B ^ 2 * (1 / 2) ^ (m - m' + (m' - m)) :=
          sum_le_sum hcov
      _ = 2 * B ^ 2 * ∑ m' ∈ (range K).erase m, (1 / 2 : ℝ) ^ (m - m' + (m' - m)) := by
          rw [mul_sum]
      _ ≤ 2 * B ^ 2 * (2 * ((1 / 2) / (1 - 1 / 2))) :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = 4 * B ^ 2 := by norm_num; ring

/-! ### The integer variance bound -/

/-- **Integer-valued variables are spread out**: if `X` takes integer values, then
`Var X ≥ φ (1 − φ)` with `φ = {E X}` (the minimum is attained by the two-point law on
`⌊E X⌋, ⌈E X⌉`). -/
theorem variance_ge_of_int {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (hint : ∀ ω, ∃ z : ℤ, X ω = z) :
    Int.fract (μ[X]) * (1 - Int.fract (μ[X])) ≤ Var[X; μ] := by
  set a : ℝ := (⌊μ[X]⌋ : ℝ) with ha
  have hpt : ∀ ω, 0 ≤ (X ω - a) * (X ω - a - 1) := by
    intro ω
    obtain ⟨z, hz⟩ := hint ω
    rw [hz, ha]
    rcases le_or_gt z ⌊μ[X]⌋ with h | h
    · have h1 : (z : ℝ) - ⌊μ[X]⌋ ≤ 0 := by
        have : (z : ℝ) ≤ ⌊μ[X]⌋ := by exact_mod_cast h
        linarith
      nlinarith
    · have h1 : (⌊μ[X]⌋ : ℝ) + 1 ≤ z := by exact_mod_cast h
      nlinarith
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := hX.integrable_sq
  have hexp : ∫ ω, (X ω - a) * (X ω - a - 1) ∂μ =
      ∫ ω, X ω ^ 2 ∂μ - (2 * a + 1) * μ[X] + a * (a + 1) := by
    have e : (fun ω ↦ (X ω - a) * (X ω - a - 1)) =
        fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω + a * (a + 1) := funext fun ω ↦ by ring
    have h1 : Integrable (fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω) μ := hX2.sub (hXi.const_mul _)
    rw [e, integral_add (f := fun ω ↦ X ω ^ 2 - (2 * a + 1) * X ω) (g := fun _ ↦ a * (a + 1)) h1
      (integrable_const _), integral_sub (f := fun ω ↦ X ω ^ 2)
      (g := fun ω ↦ (2 * a + 1) * X ω) hX2 (hXi.const_mul _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have hnn : 0 ≤ ∫ ω, (X ω - a) * (X ω - a - 1) ∂μ := integral_nonneg hpt
  have hvar : Var[X; μ] = ∫ ω, X ω ^ 2 ∂μ - μ[X] ^ 2 := variance_eq_sub hX
  have hfr : Int.fract (μ[X]) = μ[X] - a := by rw [ha, Int.fract]
  rw [hvar, hfr]
  rw [hexp] at hnn
  nlinarith

/-- The fractional parts of `w_j {2^m c_{ij}}` summed over the cut points `c_{ij} < 1`. -/
noncomputable def rowFrac (w : ℕ → ℝ) (cp : Fin n → ℕ → ℝ) (m : ℕ) (i : Fin n) : ℝ :=
  ∑ j ∈ range (n - 1), w j * (if cp i j < 1 then fracPow (cp i j) m else 0)

/-- **Row terms with integer weights are spread out** (any coin layout): at a level `m` where
bit `m` of `N_i` is set, `Var(rowTerm) ≥ φ (1 − φ)` with `φ = {Σ_j w_j {2^m c_{ij}}}`. -/
theorem variance_rowTerm_ge_of_int {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j)) (hcp : ∀ i j, 0 ≤ cp i j)
    (hw : ∀ j ∈ range (n - 1), ∃ z : ℤ, w j = z) (N : Fin n → ℕ) (m : ℕ) (i : Fin n)
    (hbit : (N i).testBit m = true) :
    Int.fract (rowFrac w cp m i) * (1 - Int.fract (rowFrac w cp m i)) ≤
      Var[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i; coinMeasure ι] := by
  classical
  set I : (ι → Bool) → ℝ := fun ω ↦ ∑ j ∈ range (n - 1),
    w j * (if cp i j < 1 then levelVal (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) else 0)
    with hI
  have hrow : (fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) = fun ω ↦ I ω - rowFrac w cp m i := by
    funext ω
    rw [rowTerm, rowFrac, hI, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    unfold cutTerm coinTerm levelTerm
    by_cases hc : cp i j < 1
    · simp only [hc, hbit, ite_true, fracPow]
      ring
    · simp only [hc, ite_false]
      ring
  have hIm : Measurable I := Finset.measurable_fun_sum _ fun j _ ↦ by
    by_cases hc : cp i j < 1
    · simp only [hc, ite_true]
      exact (measurable_levelVal_coins (hcp i j) hc (N i) m (γ i j)).const_mul _
    · simp only [hc, ite_false]
      exact measurable_const
  have hIb : ∀ ω, |I ω| ≤ absWeightSum n w := fun ω ↦ by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs
    · rcases levelVal_mem (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) with h | h <;>
        rw [h] <;> simp
    · simp
  have hI2 : MemLp I 2 (coinMeasure ι) := MemLp.of_bound hIm.aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hIb ω)
  have hIint : ∀ ω, ∃ z : ℤ, I ω = z := by
    intro ω
    have : ∀ j ∈ range (n - 1), ∃ z : ℤ, w j * (if cp i j < 1 then
        levelVal (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) else 0) = z := by
      intro j hj
      obtain ⟨z, hz⟩ := hw j hj
      by_cases hc : cp i j < 1
      · simp only [hc, ite_true]
        rcases levelVal_mem (threshDigit (cp i j)) (N i) m (coinsOf γ ω i j) with h | h
        · exact ⟨0, by rw [h]; simp⟩
        · exact ⟨z, by rw [h, hz, mul_one]⟩
      · exact ⟨0, by simp [hc]⟩
    choose! zf hzf using this
    exact ⟨∑ j ∈ range (n - 1), zf j, by
      rw [hI]; push_cast; exact sum_congr rfl fun j hj ↦ hzf j hj⟩
  have hmean : (coinMeasure ι)[I] = rowFrac w cp m i := by
    have h0 := integral_rowTerm_coins (w := w) hcp N m hγ i
    rw [hrow, integral_sub (hI2.integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul] at h0
    linarith
  rw [hrow, variance_sub_const hIm.aestronglyMeasurable, ← hmean]
  exact variance_ge_of_int hI2 hIint

/-! ### Sparse indices and the lower-bound criterion -/

/-- The index `Σ_{a<k} 2^{ra}`: bits exactly at the levels `ra`, `a < k`. -/
def patternR (r k : ℕ) : ℕ := ∑ a ∈ range k, 2 ^ (r * a)

/-- `patternR r k < 2^{rk}` for `r ≥ 1`. -/
theorem patternR_lt {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : patternR r k < 2 ^ (r * k) := by
  induction k with
  | zero => simp [patternR]
  | succ k ih =>
      rw [patternR, sum_range_succ, ← patternR, show r * (k + 1) = r * k + r by ring, pow_add]
      have h2 : 2 ≤ 2 ^ r := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
      have : 0 < 2 ^ (r * k) := Nat.two_pow_pos _
      nlinarith

/-- **The bits of `patternR r k`** are exactly the levels `ra`, `a < k`. -/
theorem testBit_patternR {r : ℕ} (hr : 1 ≤ r) (k m : ℕ) :
    (patternR r k).testBit m = true ↔ m % r = 0 ∧ m / r < k := by
  induction k generalizing m with
  | zero => simp [patternR]
  | succ k ih =>
      have e : patternR r (k + 1) = 2 ^ (r * k) * 1 + patternR r k := by
        rw [patternR, sum_range_succ, ← patternR]
        ring
      rw [e, Nat.testBit_two_pow_mul_add _ (patternR_lt hr k)]
      by_cases hm : m < r * k
      · simp only [hm, ite_true]
        rw [ih]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [mul_comm]; exact hm)
      · simp only [hm, ite_false, Nat.testBit_one_eq_true_iff_self_eq_zero]
        have hdiv : m / r ≥ k := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
        constructor
        · intro h
          have hm' : m = r * k := by omega
          subst hm'
          rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega)]
          exact ⟨rfl, Nat.lt_succ_self k⟩
        · rintro ⟨h1, h2⟩
          have hmk : m / r = k := by omega
          have := Nat.div_add_mod m r
          rw [hmk, h1] at this
          omega

/-- The row coordinates of levels `[m, m + L)`. -/
def rowCoords [DecidableEq ι] (n : ℕ) (γ : Fin n → ℕ → ℕ → ι) (i : Fin n) (m L : ℕ) :
    Finset ι :=
  (range (n - 1)).biUnion fun j ↦ (Finset.Ico m (m + L)).image (γ i j)

/-- A coordinate of a row has a level in the range and comes from that row. -/
theorem mem_rowCoords [DecidableEq ι] {lev : ι → ℕ} {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) {i : Fin n} {m L : ℕ} {q : ι}
    (hq : q ∈ rowCoords n γ i m L) :
    (m ≤ lev q ∧ lev q < m + L) ∧ ∃ j d, q = γ i j d := by
  simp only [rowCoords, mem_biUnion, mem_image, Finset.mem_Ico] at hq
  obtain ⟨j, _, d, hd, rfl⟩ := hq
  rw [hlev]
  exact ⟨hd, j, d, rfl⟩

/-- The truncated row term is `L¹`-close: `E|row − row_L| → 0`, and its variance too. -/
theorem tendsto_variance_rowTerm_sub_trunc (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (m : ℕ)
    {γ : Fin n → ℕ → ℕ → ι} (hγ : ∀ i j, Function.Injective (γ i j)) (i : Fin n) :
    Tendsto (fun L ↦ Var[(fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i); coinMeasure ι]) atTop (𝓝 0) := by
  set W := absWeightSum n w with hW
  have hW0 : 0 ≤ W := absWeightSum_nonneg n w
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (W * W)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun L ↦ variance_nonneg _ _) (fun L ↦ ?_) hlim
  have hm : Measurable ((fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)) :=
    (measurable_rowTerm_coins hcp N m γ i).sub (measurable_rowTermTrunc_coins N m L γ i)
  refine (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_
  have hd : ∀ ω, |rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|
      ≤ W := fun ω ↦ abs_rowTerm_sub_trunc_le N m L _ i
  have hi1 : Integrable (((fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) -
      (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i)) ^ 2) (coinMeasure ι) := by
    refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (W ^ 2)
      (Eventually.of_forall fun ω ↦ ?_)
    simp only [Pi.pow_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd ω) 2
  have hi2 : Integrable (fun ω ↦ W * |rowTerm w cp N m (coinsOf γ ω) i -
      rowTermTrunc w cp N m L (coinsOf γ ω) i|) (coinMeasure ι) :=
    (Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable W
      (Eventually.of_forall fun ω ↦ by
        change ‖|rowTerm w cp N m (coinsOf γ ω) i - rowTermTrunc w cp N m L (coinsOf γ ω) i|‖ ≤ W
        rw [Real.norm_eq_abs, abs_abs]; exact hd ω)).const_mul W
  refine (integral_mono hi1 hi2 fun ω ↦ ?_).trans ?_
  · simp only [Pi.pow_apply, Pi.sub_apply]
    rw [← sq_abs]
    nlinarith [abs_nonneg (rowTerm w cp N m (coinsOf γ ω) i -
      rowTermTrunc w cp N m L (coinsOf γ ω) i), hd ω]
  · rw [integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_abs_rowTerm_sub_trunc_le hcp N m L hγ i) hW0

/-- **Different rows on disjoint coordinates are uncorrelated.** -/
theorem covariance_rowTerm_eq_zero {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j))
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hcp : ∀ i j, 0 ≤ cp i j)
    (N N' : Fin n → ℕ) (m m' : ℕ) {i i' : Fin n} (hii' : i ≠ i') :
    cov[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i, fun ω ↦ rowTerm w cp N' m' (coinsOf γ ω) i';
      coinMeasure ι] = 0 := by
  classical
  have hmem : ∀ N m i, MemLp (fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i) 2 (coinMeasure ι) :=
    fun N m i ↦ MemLp.of_bound (measurable_rowTerm_coins hcp N m γ i).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N m _ i)
  have hmemt : ∀ N m L i, MemLp (fun ω ↦ rowTermTrunc w cp N m L (coinsOf γ ω) i) 2
      (coinMeasure ι) := fun N m L i ↦
    MemLp.of_bound (measurable_rowTermTrunc_coins N m L γ i).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_rowTermTrunc_le hcp N m L _ i)
  refine covariance_eq_zero_of_approx (hmem N m i) (hmem N' m' i') (fun L ↦ hmemt N m L i)
    (fun L ↦ hmemt N' m' L i') (fun L ↦ ?_) (tendsto_variance_rowTerm_sub_trunc hcp N m hγ i)
    (tendsto_variance_rowTerm_sub_trunc hcp N' m' hγ i')
  refine IsLocal.indepFun (fun _ ↦ fairCoin) (isLocal_rowTermTrunc_coins N m L γ i)
    (isLocal_rowTermTrunc_coins N' m' L γ i') (Finset.disjoint_left.2 fun q hq hq' ↦ ?_)
  simp only [mem_biUnion, mem_image] at hq hq'
  obtain ⟨j, _, d, _, rfl⟩ := hq
  obtain ⟨j', _, d', _, h⟩ := hq'
  exact hrows i i' j j' d d' hii' h.symm

/-- **Same row: covariance decays geometrically**, `|cov| ≤ 2 W² 2^{-(m'-m)}` for `m < m'`. -/
theorem abs_covariance_rowTerm_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N N' : Fin n → ℕ)
    (i : Fin n) {m m' : ℕ} (hmm' : m < m') :
    |cov[fun ω ↦ rowTerm w cp N m (coinsOf γ ω) i, fun ω ↦ rowTerm w cp N' m' (coinsOf γ ω) i;
      coinMeasure ι]| ≤ 2 * absWeightSum n w ^ 2 * (1 / 2) ^ (m' - m) := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set W := absWeightSum n w with hW
  have hW0 : 0 ≤ W := absWeightSum_nonneg n w
  have h := abs_covariance_le_of_local (B := W)
    (Xt := fun ω ↦ rowTermTrunc w cp N m (m' - m) (coinsOf γ ω) i)
    (Yt := fun L ω ↦ rowTermTrunc w cp N' m' L (coinsOf γ ω) i)
    (S := rowCoords n γ i m (m' - m)) (S' := fun L ↦ rowCoords n γ i m' L)
    (measurable_rowTerm_coins hcp N m γ i) (measurable_rowTerm_coins hcp N' m' γ i)
    (fun ω ↦ abs_rowTerm_le hcp N m _ i) (fun ω ↦ abs_rowTerm_le hcp N' m' _ i)
    (fun ω ↦ abs_rowTermTrunc_le hcp N m _ _ i) (fun L ω ↦ abs_rowTermTrunc_le hcp N' m' L _ i)
    (isLocal_rowTermTrunc_coins N m (m' - m) γ i) (fun L ↦ isLocal_rowTermTrunc_coins N' m' L γ i)
    (fun L ↦ Finset.disjoint_left.2 fun q hq hq' ↦ by
      have h1 := (mem_rowCoords hlev hq).1
      have h2 := (mem_rowCoords hlev hq').1
      omega) ?_
  · refine h.trans ?_
    have := integral_abs_rowTerm_sub_trunc_le (w := w) hcp N m (m' - m) hγ i
    calc 2 * W * ∫ ω, |rowTerm w cp N m (coinsOf γ ω) i -
          rowTermTrunc w cp N m (m' - m) (coinsOf γ ω) i| ∂(coinMeasure ι)
        ≤ 2 * W * (W * (1 / 2) ^ (m' - m)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * W ^ 2 * (1 / 2) ^ (m' - m) := by ring
  · have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul W
    rw [mul_zero] at hlim
    exact squeeze_zero (fun L ↦ integral_nonneg fun ω ↦ abs_nonneg _)
      (fun L ↦ integral_abs_rowTerm_sub_trunc_le (w := w) hcp N' m' L hγ i) hlim

/-- At a level whose bit is not set the row term vanishes. -/
theorem rowTerm_eq_zero_of_testBit {N : Fin n → ℕ} {m : ℕ} {i : Fin n}
    (hbit : (N i).testBit m = false) (e : Fin n → ℕ → ℕ → Bool) : rowTerm w cp N m e i = 0 := by
  refine sum_eq_zero fun j _ ↦ ?_
  unfold cutTerm coinTerm
  simp [hbit]

/-- **Level sums along pattern indices** are sums of the row terms at the levels `ra`. -/
theorem levelSumN_pattern_eq {r k K : ℕ} (hr : 1 ≤ r) (hK : ∀ a < k, r * a < K) {N : Fin n → ℕ}
    (hN : ∀ i, N i = patternR r k) (e : Fin n → ℕ → ℕ → Bool) :
    levelSumN w cp N K e =
      ∑ p ∈ (univ : Finset (Fin n)) ×ˢ range k, rowTerm w cp N (r * p.2) e p.1 := by
  classical
  rw [levelSumN, sum_product, sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  have hsub : (range k).image (fun a ↦ r * a) ⊆ range K := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hm
    exact mem_range.2 (hK a (mem_range.1 ha))
  rw [← sum_subset hsub fun m _ hm ↦ ?_, sum_image fun a _ b _ h ↦ by
    simpa [Nat.mul_left_cancel_iff (show 0 < r by omega)] using h]
  refine rowTerm_eq_zero_of_testBit ?_ e
  rw [hN i]
  by_contra h
  have h' := (testBit_patternR hr k m).1 (by simpa using h)
  refine hm (mem_image.2 ⟨m / r, mem_range.2 h'.2, ?_⟩)
  have := Nat.div_add_mod m r
  rw [h'.1, add_zero] at this
  exact this

/-- **Lower-bound criterion.** Let every row have index `patternR r k`, the rows use disjoint
coordinates, and every row term at the levels `ra`, `a < k`, have variance `≥ a₀`. Then
`Var(levelSumN) ≥ n k (a₀ − 4 W² ρ/(1 − ρ))` with `ρ = 2^{-r}`. -/
theorem variance_levelSumN_pattern_ge (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d)
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hcp : ∀ i j, 0 ≤ cp i j)
    {r k K : ℕ} (hr : 1 ≤ r) (hK : ∀ a < k, r * a < K) {N : Fin n → ℕ}
    (hN : ∀ i, N i = patternR r k)
    {a₀ : ℝ} (hdiag : ∀ i, ∀ a < k,
      a₀ ≤ Var[fun ω ↦ rowTerm w cp N (r * a) (coinsOf γ ω) i; coinMeasure ι]) :
    n * k * (a₀ - 4 * absWeightSum n w ^ 2 * ((1 / 2) ^ r / (1 - (1 / 2) ^ r))) ≤
      Var[fun ω ↦ levelSumN w cp N K (coinsOf γ ω); coinMeasure ι] := by
  classical
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  set W := absWeightSum n w with hW
  set ρ : ℝ := (1 / 2) ^ r with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  set s := (univ : Finset (Fin n)) ×ˢ range k with hs
  set Z : Fin n × ℕ → (ι → Bool) → ℝ := fun p ω ↦ rowTerm w cp N (r * p.2) (coinsOf γ ω) p.1
    with hZ
  have e : (fun ω ↦ levelSumN w cp N K (coinsOf γ ω)) = fun ω ↦ ∑ p ∈ s, Z p ω :=
    funext fun ω ↦ levelSumN_pattern_eq hr hK hN _
  rw [e]
  have hZ2 : ∀ p ∈ s, MemLp (Z p) 2 (coinMeasure ι) := fun p _ ↦
    MemLp.of_bound (measurable_rowTerm_coins hcp N _ γ p.1).aestronglyMeasurable _
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_rowTerm_le hcp N _ _ _)
  have h := variance_sum_ge_of_cov s hZ2 (a := a₀)
    (β := 4 * W ^ 2 * (ρ / (1 - ρ))) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · rw [hs, card_product, card_univ, Fintype.card_fin, card_range] at h
    push_cast at h
    exact h
  · simp only [hs, mem_product, mem_univ, mem_range, true_and] at hp
    exact hdiag p.1 p.2 hp
  · -- the off-diagonal covariances
    obtain ⟨i, a⟩ := p
    have hcov : ∀ p' ∈ s.erase (i, a), |cov[Z (i, a), Z p'; coinMeasure ι]| ≤
        if p'.1 = i then 2 * W ^ 2 * ρ ^ (a - p'.2 + (p'.2 - a)) else 0 := by
      rintro ⟨i', b⟩ hp'
      have hne := ne_of_mem_erase hp'
      by_cases hii : i' = i
      · subst hii
        have hab : a ≠ b := fun h ↦ hne (by rw [h])
        simp only [ite_true]
        have hpow : ∀ d : ℕ, (1 / 2 : ℝ) ^ (r * d) = ρ ^ d := fun d ↦ by rw [hρ, pow_mul]
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · have hmm : r * a < r * b := Nat.mul_lt_mul_of_pos_left hlt (by omega)
          have := abs_covariance_rowTerm_le lev hlev hcp (w := w) N N i' hmm
          rw [show r * b - r * a = r * (b - a) by rw [Nat.mul_sub], hpow] at this
          rwa [show a - b + (b - a) = b - a by omega]
        · have hmm : r * b < r * a := Nat.mul_lt_mul_of_pos_left hlt (by omega)
          have := abs_covariance_rowTerm_le lev hlev hcp (w := w) N N i' hmm
          rw [show r * a - r * b = r * (a - b) by rw [Nat.mul_sub], hpow] at this
          rw [covariance_comm, show a - b + (b - a) = a - b by omega]
          exact this
      · simp only [hii, ite_false]
        rw [covariance_rowTerm_eq_zero hγ hrows hcp N N _ _ (Ne.symm hii), abs_zero]
    refine (sum_le_sum hcov).trans ?_
    rw [← sum_filter]
    have hfil : (s.erase (i, a)).filter (fun p' ↦ p'.1 = i) =
        ((range k).erase a).image (fun b ↦ (i, b)) := by
      ext ⟨i', b⟩
      simp only [hs, mem_filter, mem_erase, mem_product, mem_univ, mem_range, true_and,
        mem_image, ne_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hne, hb⟩, rfl⟩
        exact ⟨b, ⟨fun h ↦ hne ⟨rfl, h⟩, hb⟩, rfl, rfl⟩
      · rintro ⟨b', ⟨hb', hb⟩, rfl, rfl⟩
        exact ⟨⟨fun h ↦ hb' h.2, hb⟩, rfl⟩
    rw [hfil, sum_image fun b _ b' _ h ↦ by simpa using h]
    have hgeo := sum_erase_pow_dist_le hρ0 hρ1 a k
    calc ∑ b ∈ (range k).erase a, 2 * W ^ 2 * ρ ^ (a - b + (b - a))
        = 2 * W ^ 2 * ∑ b ∈ (range k).erase a, ρ ^ (a - b + (b - a)) := by rw [mul_sum]
      _ ≤ 2 * W ^ 2 * (2 * (ρ / (1 - ρ))) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = 4 * W ^ 2 * (ρ / (1 - ρ)) := by ring

/-! ### Mean-square tools -/

/-- `(⌊log₂ y⌋ + 1)² ≤ 4 y` for `y ≥ 1`. -/
theorem natLog_add_one_sq_le {y : ℕ} (hy : 1 ≤ y) : ((Nat.log 2 y : ℝ) + 1) ^ 2 ≤ 4 * y := by
  set ℓ := Nat.log 2 y with hℓ
  have hpow : 2 ^ ℓ ≤ y := Nat.pow_log_le_self 2 (by omega)
  have hnat : (ℓ + 1) ^ 2 ≤ 4 * 2 ^ ℓ := by
    clear hpow hℓ
    induction ℓ with
    | zero => norm_num
    | succ ℓ ih =>
        have h1 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
        have h2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
        rw [h2]
        nlinarith
  have h1 : ((ℓ + 1) ^ 2 : ℕ) ≤ 4 * y := hnat.trans (by omega)
  exact_mod_cast h1

/-- **Mean square of a perturbed centred term**: if `|E − M| ≤ b` and `E[M²] ≤ V`, then
`E[E²] ≤ 2V + 2b²`. -/
theorem integral_sq_le_of_close {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : Ω → ℝ} (hE : MemLp E 2 μ) (hM : MemLp M 2 μ) {b V : ℝ}
    (hclose : ∀ ω, |E ω - M ω| ≤ b) (hV : ∫ ω, M ω ^ 2 ∂μ ≤ V) :
    ∫ ω, E ω ^ 2 ∂μ ≤ 2 * V + 2 * b ^ 2 := by
  have hpt : ∀ ω, E ω ^ 2 ≤ 2 * M ω ^ 2 + 2 * b ^ 2 := by
    intro ω
    have h2 : (E ω - M ω) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hclose ω) 2
    nlinarith [sq_nonneg (E ω - 2 * M ω)]
  calc ∫ ω, E ω ^ 2 ∂μ ≤ ∫ ω, (2 * M ω ^ 2 + 2 * b ^ 2) ∂μ :=
        integral_mono hE.integrable_sq ((hM.integrable_sq.const_mul 2).add (integrable_const _))
          hpt
    _ = 2 * ∫ ω, M ω ^ 2 ∂μ + 2 * b ^ 2 := by
        rw [integral_add (hM.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 2 * V + 2 * b ^ 2 := by linarith

/-- **Mean square of a level sum**: `E[levelSumN²] = Var ≤ 5 (nW)² K`. -/
theorem integral_sq_levelSumN_le (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d) (hcp : ∀ i j, 0 ≤ cp i j) (N : Fin n → ℕ) (K : ℕ) :
    ∫ ω, levelSumN w cp N K (coinsOf γ ω) ^ 2 ∂(coinMeasure ι) ≤
      K * (5 * (n * absWeightSum n w) ^ 2) := by
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  have h0 := integral_levelSumN_coins (w := w) hcp N K hγ
  have hv := variance_levelSumN_le lev hlev hcp (w := w) N K
  rw [variance_of_integral_eq_zero
    (memLp_levelSumN_coins hcp N K γ).aestronglyMeasurable.aemeasurable h0] at hv
  exact hv

/-- **Rate of the mean square of the frequency**: if `E[E_T²] ≤ C (⌊log₂ T⌋ + 1)` for all `T`,
then `E[(E_T/T)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_div_of_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : ℕ → Ω → ℝ} {C : ℝ} (hC : ∀ T, ∫ ω, E T ω ^ 2 ∂μ ≤ C * ((Nat.log 2 T : ℝ) + 1)) :
    (fun T : ℕ ↦ ∫ ω, (E T ω / T) ^ 2 ∂μ) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by
  have hlog : ∀ᶠ T : ℕ in atTop, 1 ≤ Nat.log 2 T :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun t ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      tendsto_id).eventually_ge_atTop 1
  refine Asymptotics.IsBigO.of_bound (2 * |C|) ?_
  filter_upwards [hlog, eventually_ge_atTop 1] with T h2 h3
  have hT0 : (0 : ℝ) < T := by exact_mod_cast h3
  have hl : (1 : ℝ) ≤ Nat.log 2 T := by exact_mod_cast h2
  have e : ∫ ω, (E T ω / T) ^ 2 ∂μ = (∫ ω, E T ω ^ 2 ∂μ) / T ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
  have hnn : 0 ≤ ∫ ω, E T ω ^ 2 ∂μ := integral_nonneg fun ω ↦ sq_nonneg _
  have hq : (0 : ℝ) ≤ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_of_nonneg (div_nonneg hnn (by positivity)),
    abs_of_nonneg hq, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have h1 := hC T
  have h4 : C * ((Nat.log 2 T : ℝ) + 1) ≤ |C| * ((Nat.log 2 T : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  nlinarith [abs_nonneg C]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stacks CLT for n states: the random digital shift (post #3, code (ii))

Post #3, code (ii): one Sobol (base-2 van der Corput) sequence per state with a random digital
shift; "in the five-state chain normality cannot be rejected for the per-state Sobol sequences".

**Reading.** As for two states (`CltStacks`): for ANY number `n` of states, any stochastic `P`
with Poisson data for every target (`IsPoissonFamily`) and any target `s`, along times `T_k → ∞`
with `Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k`, the normalised occupation error is asymptotically
`N(0,1)`. The variance is always `O(log T)`, so the RMSE of the occupation frequency is
`O(√log T / T)`.

**Proof.** Under the digital shift the path coins of EVERY cut point of row `i` are the same
flips `ω (i, d)` (`pathCoin_shiftTable`): the main term is the level sum of the coin layout
`shiftLayout` on `Fin n × ℕ` with level `Prod.snd` (`mainTermN_shiftFlips_eq`). The CLT for level
sums (`CltNCoins`) and the deterministic Anscombe theorem (`CltNDecomp`, `O(log log T)`) with
Slutsky give the result. This proof uses no law of Owen's scramble (the laws differ for `n ≥ 3`,
`CltThreeState`); the Owen case is the separate `CltNOwen`.

**Hypotheses added.** `IsPoissonFamily P H π` (Poisson data for every target; satisfiable, e.g.
`CltNExample`); the variance hypothesis is stated along the given times (`∀ᶠ k`), as the CLT is
about such subsequences (along `T = 2^k` the variance stays bounded for non-dyadic chains,
`StackPowerOfTwo`). No positivity of `P` and no condition on the cut points is needed (cut points
equal to `1` contribute nothing).

## Main results

* `shiftLayout`, `pathCoins_shiftFlips_eq`, `mainTermN_shiftFlips_eq`, `shiftMainTerm`.
* `abs_occErrN_shift_sub_le`, `memLp_occErrN_shift`.
* `tendstoInDistribution_occErrN_shift` (**main theorem, code (ii)**).
* `integral_sq_occErrN_shift_le`, `variance_occErrN_shift_le`: `E[E_T²], Var(E_T) ≤ C (log₂ T + 1)`.
* `isBigO_meanSq_occFreqN_shift`: `E[(N_s(T)/T − π_s)²] = O(log T / T²)` (RMSE `O(√log T / T)`).
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The digital-shift coin layout: every cut point `j` of row `i` uses the flips `(i, d)`. -/
def shiftLayout (n : ℕ) : Fin n → ℕ → ℕ → Fin n × ℕ := fun i _ d ↦ (i, d)

/-- The level of the shift coordinate `(i, d)` is `d`. -/
theorem shiftLayout_lev (i : Fin n) (j d : ℕ) : (shiftLayout n i j d).2 = d := rfl

/-- Different rows use different shift flips. -/
theorem shiftLayout_rows (i i' : Fin n) (j j' d d' : ℕ) (hii' : i ≠ i') :
    shiftLayout n i j d ≠ shiftLayout n i' j' d' := fun h ↦ hii' (congrArg Prod.fst h)

/-- **Shift path coins.** Under the digital shift the path coins of every cut point of row `i`
are the flips `ω (i, ·)`. -/
theorem pathCoins_shiftFlips_eq (P : Fin n → Fin n → ℝ) (ω : Fin n × ℕ → Bool) :
    (fun i j ↦ pathCoin (shiftFlips ω i) (threshDigit (cutPoint P i j))) =
      coinsOf (shiftLayout n) ω := rfl

/-- The main term of the shifted chain as a level sum of the flips, with `⌊log₂ T⌋ + 1` levels. -/
noncomputable def shiftMainTerm (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) (ω : Fin n × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (H s)) (cutPoint P) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (shiftLayout n) ω)

/-- The main term of the shifted chain is the level sum of the flips. -/
theorem mainTermN_shiftFlips_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (s : Fin n) (T : ℕ)
    (ω : Fin n × ℕ → Bool) :
    mainTermN P (H s) pi (shiftFlips ω) T = shiftMainTerm P H pi s T ω :=
  mainTermN_eq_levelSumN hP (H s) pi (shiftFlips ω) T (chainIdxN_lt_two_pow hP hH T)

/-- The occupation error of the shifted chain is within `ansBoundN` of the level sum. -/
theorem abs_occErrN_shift_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) (ω : Fin n × ℕ → Bool) :
    |occErrN P pi x₀ (shiftFlips ω) s T - shiftMainTerm P H pi s T ω| ≤ ansBoundN H s T := by
  rw [← mainTermN_shiftFlips_eq hP hH s T ω]
  exact abs_occErrN_sub_mainTermN_le hP hH x₀ (shiftFlips ω) s T

/-- The occupation error is bounded: `|N_s(T) − T π_s| ≤ T + T |π_s|`. -/
theorem abs_occErrN_le (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (s : Fin n) (T : ℕ) :
    |occErrN P pi x₀ f s T| ≤ T + T * |pi s| := by
  rw [occErrN]
  refine (abs_sub _ _).trans ?_
  rw [Nat.abs_cast, abs_mul, Nat.abs_cast]
  have : (occCount (stackPath P x₀ (scrambledStack f)) s T : ℝ) ≤ T := by
    exact_mod_cast occCount_le _ s T
  linarith

/-- The occupation error of the shifted chain is in `L²`. -/
theorem memLp_occErrN_shift (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ s : Fin n) (T : ℕ) :
    MemLp (fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s T) 2 (shiftMeasure n) := by
  have hm : Measurable fun ω : Fin n × ℕ → Bool ↦ occErrN P pi x₀ (shiftFlips ω) s T :=
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
      (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ s T)).sub measurable_const
  exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact abs_occErrN_le P pi x₀ _ s T)

/-- `⌊log₂ T_k⌋ + 1 → ∞` along `T_k → ∞`. -/
theorem tendsto_natLog_add_one {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun k ↦ Nat.log 2 (T k) + 1) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ Nat.le_succ _)
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun _ ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      hT)

/-- **The stacks CLT for n states, random digital shift** (post #3, code (ii)). For a stochastic
`P` on `Fin n` with Poisson data `H`, `π` for every target, a target `s`, and `T_k → ∞` with
`Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` eventually,
`(N_s(T_k) − T_k π_s) / √Var(N_s(T_k) − T_k π_s) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_occErrN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k); shiftMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k) /
      √Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k); shiftMeasure n]) atTop Z
      (fun _ ↦ shiftMeasure n) P' := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hγ : ∀ i j, Function.Injective (shiftLayout n i j) := fun i j d d' h ↦
    congrArg Prod.snd h
  refine tendstoInDistribution_of_close_main (E := fun k ω ↦ occErrN P pi x₀ (shiftFlips ω) s (T k))
    (M := fun k ω ↦ shiftMainTerm P H pi s (T k) ω) hT (b := fun k ↦ ansBoundN H s (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ ansBoundN_nonneg H s (T k))
      (fun k ↦ ansBoundN_le_log H s (T k)))
    (fun k ↦ memLp_occErrN_shift P pi x₀ s (T k))
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ↦ integral_levelSumN_coins hcp _ _ hγ)
    (fun k ω ↦ abs_occErrN_shift_sub_le hP hH x₀ s (T k) ω) hκ hvar ?_
  intro κ' hκ' hv
  exact tendstoInDistribution_levelSumN Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv hZ

/-- The constant `10 (nW)² + 8 C²` of the mean-square bound. -/
noncomputable def varConstN (H : Fin n → Fin n → ℝ) (s : Fin n) : ℝ :=
  10 * (n * cutWeightSum (H s)) ^ 2 + 8 * ansConstN H s ^ 2

/-- `2 ansBoundN² ≤ 8 C² (⌊log₂ T⌋ + 1)`: the Anscombe error is `o(√log T)` in mean square. -/
theorem two_mul_ansBoundN_sq_le (H : Fin n → Fin n → ℝ) (s : Fin n) (T : ℕ) :
    2 * ansBoundN H s T ^ 2 ≤ 8 * ansConstN H s ^ 2 * ((Nat.log 2 T : ℝ) + 1) := by
  have h1 := ansBoundN_le_log H s T
  have h0 := ansBoundN_nonneg H s T
  have hy := natLog_add_one_sq_le (y := Nat.log 2 T + 1) (by omega)
  push_cast at hy
  have h2 : ansBoundN H s T ^ 2 ≤
      ansConstN H s ^ 2 * ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    rwa [mul_pow] at this
  nlinarith [sq_nonneg (ansConstN H s)]

/-- **Mean-square bound** (digital shift): `E[(N_s(T) − T π_s)²] ≤ C (⌊log₂ T⌋ + 1)`. -/
theorem integral_sq_occErrN_shift_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    ∫ ω, occErrN P pi x₀ (shiftFlips ω) s T ^ 2 ∂(shiftMeasure n) ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hV := integral_sq_levelSumN_le Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (w := cutWeight (H s)) (chainIdxN pi T) (Nat.log 2 T + 1)
  have h := integral_sq_le_of_close (memLp_occErrN_shift P pi x₀ s T)
    (memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (abs_occErrN_shift_sub_le hP hH x₀ s T) hV
  have hb := two_mul_ansBoundN_sq_le H s T
  refine h.trans ?_
  rw [varConstN]
  push_cast
  change 2 * (((Nat.log 2 T : ℝ) + 1) * (5 * (n * cutWeightSum (H s)) ^ 2)) +
    2 * ansBoundN H s T ^ 2 ≤ _
  nlinarith

/-- **Variance bound** (digital shift): `Var(N_s(T) − T π_s) ≤ C (⌊log₂ T⌋ + 1) = O(log T)`. -/
theorem variance_occErrN_shift_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    Var[fun ω ↦ occErrN P pi x₀ (shiftFlips ω) s T; shiftMeasure n] ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) :=
  (variance_le_expectation_sq (memLp_occErrN_shift P pi x₀ s T).aestronglyMeasurable).trans
    (integral_sq_occErrN_shift_le hP hH x₀ s T)

/-- **RMSE of the occupation frequency is `O(√log T / T)`** (digital shift, n states):
`E[(N_s(T)/T − π_s)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_occFreqN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n) :
    (fun T : ℕ ↦ ∫ ω, (occErrN P pi x₀ (shiftFlips ω) s T / T) ^ 2 ∂(shiftMeasure n)) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 :=
  isBigO_meanSq_div_of_le (E := fun T ω ↦ occErrN P pi x₀ (shiftFlips ω) s T)
    (integral_sq_occErrN_shift_le hP hH x₀ s)

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Owen's flips relabelled by the scrambled tree (post #3, code (iii), n states)

Under Owen's nested scramble the flip at depth `m` applied to the points of original `m`-digit
prefix `α` is `ω (i, m, α)`. The flips at depths `< m` induce a bijection `σ_m` of the depth-`m`
prefixes (original prefix ↦ scrambled prefix). The path coin of a cut point `c` at depth `m`
is the flip at the node `σ_m⁻¹(⌊2^m c⌋)` (`CltPathBits.pathPrefix`). We **relabel** the flips by
the nodes of the SCRAMBLED tree, `g ω (i, m, p) = ω (i, m, σ_m⁻¹ p)` (`owenRelabel`; the
coordinates with `p ≥ 2^m`, which Owen's scramble never uses, are left alone). Then:

* `pathCoin_owenTable_eq_relabel`: the path coin of `c ∈ [0,1)` at depth `m` is
  `g ω (i, m, ⌊2^m c⌋)` — two cut points share the relabelled coins of their common binary
  prefix, and use different ones from their first differing digit on;
* `measurePreserving_owenRelabel` (**the relabelling preserves Owen's measure**): `σ_m` depends
  only on the flips of depths `< m`, and a bijective relabelling of fresh fair coins is fair;
  proved through rectangle cylinders (`owenMeasure_relabel_rect`, by induction on the depth,
  conditioning on the finitely many flips above) and `eq_owenMeasure_of_box`.

This generalises `map_owenPathCoins` (one threshold per row) to all the nodes of the tree, which
is what the n-state CLT needs (`CltNOwen`). It is NOT a law transfer to the digital shift: under
the shift two cut points of a row share the same flip at every depth (`CltThreeState`).

## Main results

* `prefixDigits`, `owenNode`, `owenRelabel`, `owenRect`.
* `pathPrefix_congr_digits`, `pathPrefix_threshDigit_eq`, `pathCoin_owenTable_eq_relabel`.
* `owenNode_lt`, `owenNode_inj`, `owenNode_congr`, `owenRelabel_congr`, `measurable_owenRelabel`.
* `measure_eq_sum_restrict_preimage`, `coinMeasure_setOf_comp_eq` (cylinder tools).
* `owenMeasure_relabel_rect`, `eq_owenMeasure_of_box`, `measurePreserving_owenRelabel`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### The relabelling -/

/-- The `m` binary digits of `p` (most significant first): digit `j` is bit `m − 1 − j`. -/
def prefixDigits (m p : ℕ) : ℕ → Bool := fun j ↦ p.testBit (m - 1 - j)

/-- The original depth-`m` prefix (a node of Owen's tree) that the scramble of row `i` sends to
the scrambled prefix `p`. -/
def owenNode (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (m p : ℕ) : ℕ :=
  pathPrefix (owenTable ω i) (prefixDigits m p) m

/-- **Owen's flips relabelled by the scrambled tree**: the flip at depth `m` of the node whose
scrambled prefix is `p < 2^m` (other coordinates unchanged). -/
def owenRelabel (ω : Fin n × ℕ × ℕ → Bool) (q : Fin n × ℕ × ℕ) : Bool :=
  if q.2.2 < 2 ^ q.2.1 then ω (q.1, q.2.1, owenNode ω q.1 q.2.1 q.2.2) else ω q

/-- The rectangle of Owen coordinates of depth `< M` and prefix `< W`. -/
def owenRect (n M W : ℕ) : Finset (Fin n × ℕ × ℕ) := univ ×ˢ (range M ×ˢ range W)

/-- Membership in `owenRect`. -/
theorem mem_owenRect {M W : ℕ} {q : Fin n × ℕ × ℕ} :
    q ∈ owenRect n M W ↔ q.2.1 < M ∧ q.2.2 < W := by
  simp [owenRect]

/-- `owenBox n M = owenRect n M (2^M)`. -/
theorem owenBox_eq_owenRect (n M : ℕ) : owenBox n M = owenRect n M (2 ^ M) := rfl

/-- Path prefixes depend only on the first digits of the threshold. -/
theorem pathPrefix_congr_digits (f : ℕ → ℕ → Bool) {cb cb' : ℕ → Bool} {m : ℕ}
    (h : ∀ j < m, cb j = cb' j) : pathPrefix f cb m = pathPrefix f cb' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have ih' := ih fun j hj ↦ h j (by omega)
      change pathPrefix f cb m + 2 ^ m * (if xor (cb m) (f m (pathPrefix f cb m)) then 1 else 0) =
        pathPrefix f cb' m + 2 ^ m * (if xor (cb' m) (f m (pathPrefix f cb' m)) then 1 else 0)
      rw [ih', h m (by omega)]

/-- The digits of `c ∈ [0,1)` before depth `m` are those of `⌊2^m c⌋`. -/
theorem pathPrefix_threshDigit_eq (f : ℕ → ℕ → Bool) {c : ℝ} (hc1 : c < 1) (m : ℕ) :
    pathPrefix f (threshDigit c) m = pathPrefix f (prefixDigits m ⌊2 ^ m * c⌋₊) m := by
  refine pathPrefix_congr_digits f fun j hj ↦ ?_
  have h := (digitPrefix_eq_iff (threshDigit c) m ⌊2 ^ m * c⌋₊).1 (digitPrefix_threshDigit hc1 m)
  exact h.2 j hj

/-- `⌊2^m c⌋ < 2^m` for `c < 1`. -/
theorem floor_two_pow_mul_lt {c : ℝ} (hc1 : c < 1) (m : ℕ) : ⌊2 ^ m * c⌋₊ < 2 ^ m := by
  rw [← digitPrefix_threshDigit hc1 m]
  exact digitPrefix_lt _ m

/-- **Path coins are relabelled coins**: for `c ∈ [0,1)`, the path coin of `c` at depth `m` is the
relabelled flip at the scrambled node `⌊2^m c⌋`. -/
theorem pathCoin_owenTable_eq_relabel (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) {c : ℝ}
    (hc1 : c < 1) (m : ℕ) :
    pathCoin (owenTable ω i) (threshDigit c) m = owenRelabel ω (i, m, ⌊2 ^ m * c⌋₊) := by
  unfold pathCoin owenRelabel owenNode
  simp only [floor_two_pow_mul_lt hc1 m, ite_true]
  rw [pathPrefix_threshDigit_eq _ hc1 m]
  rfl

/-- `owenNode < 2^m`. -/
theorem owenNode_lt (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) (m p : ℕ) : owenNode ω i m p < 2 ^ m :=
  pathPrefix_lt _ _ m

/-- **The scrambled tree is a bijection**: distinct scrambled prefixes come from distinct
nodes. -/
theorem owenNode_inj (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n) {m p p' : ℕ} (hp : p < 2 ^ m)
    (hp' : p' < 2 ^ m) (h : owenNode ω i m p = owenNode ω i m p') : p = p' := by
  have key : ∀ q < 2 ^ m,
      digitPrefix (scrambledDigit (owenTable ω i) (owenNode ω i m q)) m = q := by
    intro q hq
    have hmod : owenNode ω i m q % 2 ^ m = pathPrefix (owenTable ω i) (prefixDigits m q) m :=
      Nat.mod_eq_of_lt (owenNode_lt ω i m q)
    have htie := (tie_iff_mod_eq_pathPrefix (owenTable ω i) (prefixDigits m q)
      (owenNode ω i m q) m).2 hmod
    exact (digitPrefix_eq_iff _ m q).2 ⟨hq, htie⟩
  rw [← key p hp, ← key p' hp', h]

/-- The scrambled tree of depth `m` depends only on the flips of `owenBox n m`. -/
theorem owenNode_congr {ω ω' : Fin n × ℕ × ℕ → Bool} {m : ℕ}
    (h : ∀ q ∈ owenBox n m, ω q = ω' q) (i : Fin n) (p : ℕ) :
    owenNode ω i m p = owenNode ω' i m p :=
  pathPrefix_owen_congr (prefixDigits m p) i h m le_rfl

/-- The relabelled flip at `q = (i, m, p)` depends only on the flips of
`owenRect n (m + 1) (max (p + 1) (2^m))`. -/
theorem owenRelabel_congr {ω ω' : Fin n × ℕ × ℕ → Bool} {q : Fin n × ℕ × ℕ}
    (h : ∀ q' ∈ owenRect n (q.2.1 + 1) (max (q.2.2 + 1) (2 ^ q.2.1)), ω q' = ω' q') :
    owenRelabel ω q = owenRelabel ω' q := by
  obtain ⟨i, m, p⟩ := q
  have hbox : ∀ q' ∈ owenBox n m, ω q' = ω' q' := fun q' hq' ↦ by
    refine h q' (mem_owenRect.2 ?_)
    have := mem_owenRect.1 ((owenBox_eq_owenRect n m) ▸ hq')
    exact ⟨by simp only at this ⊢; omega, by simp only at this ⊢; omega⟩
  unfold owenRelabel
  by_cases hp : p < 2 ^ m
  · simp only [hp, ite_true]
    rw [owenNode_congr hbox i p]
    refine h _ (mem_owenRect.2 ⟨by simp, ?_⟩)
    simp only
    exact lt_of_lt_of_le (owenNode_lt ω' i m p) (le_max_right _ _)
  · simp only [hp, ite_false]
    exact h _ (mem_owenRect.2 ⟨by simp, by simp⟩)

/-- The relabelling is measurable. -/
theorem measurable_owenRelabel : Measurable (owenRelabel (n := n)) := by
  classical
  refine measurable_pi_iff.2 fun q ↦ ?_
  have hloc : IsLocal (fun ω : Fin n × ℕ × ℕ → Bool ↦ owenRelabel ω q)
      (owenRect n (q.2.1 + 1) (max (q.2.2 + 1) (2 ^ q.2.1))) :=
    fun ω ω' h ↦ owenRelabel_congr h
  exact hloc.measurable

/-! ### Cylinder tools -/

/-- A measure on `ι → Bool` is the sum of its pieces on the cells of a finite restriction. -/
theorem measure_eq_sum_restrict_preimage {ι : Type*} [DecidableEq ι] (μ : Measure (ι → Bool))
    (S : Finset ι) (A : Set (ι → Bool)) :
    μ A = ∑ a : S → Bool, μ (A ∩ S.restrict ⁻¹' {a}) := by
  have h := sum_measure_preimage_singleton (μ := μ.restrict A) (univ : Finset (S → Bool))
    (f := S.restrict) fun y _ ↦ Finset.measurable_restrict S (measurableSet_singleton y)
  rw [coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  rw [← h]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Measure.restrict_apply (Finset.measurable_restrict S (measurableSet_singleton a)),
    Set.inter_comm]

/-- **Cylinders of fair coins**: prescribing the coins at `|A|` distinct coordinates has
probability `2^{-|A|}`. -/
theorem coinMeasure_setOf_comp_eq {ι κ : Type*} {c : κ → ι} (hc : Function.Injective c)
    (A : Finset κ) (v : κ → Bool) :
    coinMeasure ι {ω | ∀ t ∈ A, ω (c t) = v t} = 2⁻¹ ^ A.card := by
  classical
  set u : ι → Bool := Function.extend c v fun _ ↦ false with hu
  have e : {ω : ι → Bool | ∀ t ∈ A, ω (c t) = v t} =
      Set.pi ((A.image c : Finset ι) : Set ι) fun q ↦ ({u q} : Set Bool) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, coe_image, Set.mem_image, mem_coe,
      Set.mem_singleton_iff, forall_exists_index, and_imp]
    constructor
    · rintro h q t ht rfl
      rw [hu, hc.extend_apply]
      exact h t ht
    · intro h t ht
      have := h (c t) t ht rfl
      rwa [hu, hc.extend_apply] at this
  rw [e, Measure.infinitePi_pi _ fun q _ ↦ measurableSet_singleton _]
  simp only [fairCoin_singleton, prod_const, card_image_of_injective _ hc]

/-! ### The relabelling preserves Owen's measure -/

/-- **Rectangle cylinders of the relabelled flips**: for every depth `M`, width `W` and values
`b`, `P(g ω = b on owenRect n M W) = 2^{-nMW}`. By induction on `M`: conditionally on the flips
of the rows above (finitely many cells), the depth-`M` relabelled flips are a bijective relabelling
of fresh fair coins. -/
theorem owenMeasure_relabel_rect (W : ℕ) (b : Fin n × ℕ × ℕ → Bool) (M : ℕ) :
    owenMeasure n {ω | ∀ q ∈ owenRect n M W, owenRelabel ω q = b q} = 2⁻¹ ^ (n * M * W) := by
  classical
  induction M with
  | zero =>
      have : {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenRect n 0 W, owenRelabel ω q = b q} =
          Set.univ := by
        ext ω
        simp [owenRect]
      rw [this, measure_univ, mul_zero, zero_mul, pow_zero]
  | succ M ih =>
      set R := owenRect n M (max W (2 ^ M)) with hR
      set E := {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenRect n M W, owenRelabel ω q = b q}
        with hE
      set G := {ω : Fin n × ℕ × ℕ → Bool |
        ∀ i : Fin n, ∀ p < W, owenRelabel ω (i, M, p) = b (i, M, p)} with hG
      have hsplit : {ω : Fin n × ℕ × ℕ → Bool |
          ∀ q ∈ owenRect n (M + 1) W, owenRelabel ω q = b q} = E ∩ G := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE, hG]
        constructor
        · intro h
          refine ⟨fun q hq ↦ h q ?_, fun i p hp ↦ h (i, M, p) ?_⟩
          · have := mem_owenRect.1 hq
            exact mem_owenRect.2 ⟨by omega, this.2⟩
          · exact mem_owenRect.2 ⟨by simp, hp⟩
        · rintro ⟨h1, h2⟩ ⟨i, m, p⟩ hq
          have hq' := mem_owenRect.1 hq
          simp only at hq'
          rcases Nat.lt_succ_iff_lt_or_eq.1 hq'.1 with hm | rfl
          · exact h1 _ (mem_owenRect.2 ⟨hm, hq'.2⟩)
          · exact h2 i p hq'.2
      -- `E` and the depth-`M` tree only see the flips of `R`
      have hER : ∀ ω ω' : Fin n × ℕ × ℕ → Bool, (∀ q ∈ R, ω q = ω' q) →
          (ω ∈ E ↔ ω' ∈ E) := by
        intro ω ω' h
        have hq : ∀ q ∈ owenRect n M W, owenRelabel ω q = owenRelabel ω' q := by
          intro q hq
          refine owenRelabel_congr fun q' hq' ↦ h q' (mem_owenRect.2 ?_)
          have h1 := mem_owenRect.1 hq
          have h2 := mem_owenRect.1 hq'
          have h3 : 2 ^ q.2.1 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) h1.1.le
          refine ⟨by omega, lt_of_lt_of_le h2.2 ?_⟩
          exact max_le (le_trans (by omega) (le_max_left _ _)) (h3.trans (le_max_right _ _))
        simp only [hE, Set.mem_ofPred_eq]
        constructor
        · intro h' q hq'
          rw [← hq q hq']
          exact h' q hq'
        · intro h' q hq'
          rw [hq q hq']
          exact h' q hq'
      have hNR : ∀ ω ω' : Fin n × ℕ × ℕ → Bool, (∀ q ∈ R, ω q = ω' q) →
          ∀ i p, owenNode ω i M p = owenNode ω' i M p := by
        intro ω ω' h i p
        refine owenNode_congr (fun q hq ↦ h q (mem_owenRect.2 ?_)) i p
        have := mem_owenRect.1 ((owenBox_eq_owenRect n M) ▸ hq)
        exact ⟨this.1, lt_of_lt_of_le this.2 (le_max_right _ _)⟩
      -- the cells of the restriction to `R`
      set ωa : (R → Bool) → Fin n × ℕ × ℕ → Bool := fun a ↦ localExtend R (fun _ ↦ false) a
        with hωa
      have hcell : ∀ (a : R → Bool) (ω : Fin n × ℕ × ℕ → Bool), R.restrict ω = a →
          ∀ q ∈ R, ω q = ωa a q := by
        intro a ω hω q hq
        simp only [hωa, localExtend, hq, dite_true]
        rw [← hω]
        rfl
      set τ : (R → Bool) → Fin n → ℕ → ℕ := fun a i p ↦
        if p < 2 ^ M then owenNode (ωa a) i M p else p with hτ
      have hτinj : ∀ a i, Function.Injective (τ a i) := by
        intro a i p p' h
        simp only [hτ] at h
        by_cases hp : p < 2 ^ M <;> by_cases hp' : p' < 2 ^ M
        · simp only [hp, hp', ite_true] at h
          exact owenNode_inj _ i hp hp' h
        · simp only [hp, hp', ite_true, ite_false] at h
          have := owenNode_lt (ωa a) i M p
          omega
        · simp only [hp, hp', ite_true, ite_false] at h
          have := owenNode_lt (ωa a) i M p'
          omega
        · simp only [hp, hp', ite_false] at h
          exact h
      set c : (R → Bool) → Fin n × ℕ → Fin n × ℕ × ℕ := fun a t ↦ (t.1, M, τ a t.1 t.2) with hc
      have hcinj : ∀ a, Function.Injective (c a) := by
        rintro a ⟨t1, t2⟩ ⟨t1', t2'⟩ h
        simp only [hc, Prod.mk.injEq] at h
        obtain ⟨h1, -, h3⟩ := h
        subst h1
        rw [hτinj a _ h3]
      set Ga : (R → Bool) → Set (Fin n × ℕ × ℕ → Bool) := fun a ↦
        {ω | ∀ t ∈ (univ : Finset (Fin n)) ×ˢ range W, ω (c a t) = b (t.1, M, t.2)} with hGa
      have hGam : ∀ a, owenMeasure n (Ga a) = 2⁻¹ ^ (n * W) := by
        intro a
        have := coinMeasure_setOf_comp_eq (hcinj a) ((univ : Finset (Fin n)) ×ˢ range W)
          (fun t ↦ b (t.1, M, t.2))
        rw [card_product, card_univ, Fintype.card_fin, card_range] at this
        exact this
      have hpiece : ∀ a : R → Bool, (E ∩ G) ∩ R.restrict ⁻¹' ({a} : Set (R → Bool)) =
          if ωa a ∈ E then R.restrict ⁻¹' ({a} : Set (R → Bool)) ∩ Ga a else ∅ := by
        intro a
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hωE, hωG⟩, hωa'⟩
          have hagree := hcell a ω hωa'
          have hE' : ωa a ∈ E := (hER ω (ωa a) hagree).1 hωE
          simp only [hE', ite_true, Set.mem_inter_iff, Set.mem_preimage]
          refine ⟨hωa', fun t ht ↦ ?_⟩
          have ht' := mem_product.1 ht
          have := hωG t.1 t.2 (mem_range.1 ht'.2)
          unfold owenRelabel at this
          simp only [hc, hτ]
          by_cases hp : t.2 < 2 ^ M
          · simp only [hp, ite_true] at this ⊢
            rw [← hNR ω (ωa a) hagree t.1 t.2]
            exact this
          · simp only [hp, ite_false] at this ⊢
            exact this
        · intro h
          by_cases hE' : ωa a ∈ E
          · simp only [hE', ite_true, Set.mem_inter_iff, Set.mem_preimage] at h
            obtain ⟨hωa', hGa'⟩ := h
            have hagree := hcell a ω hωa'
            refine ⟨⟨(hER ω (ωa a) hagree).2 hE', fun i p hp ↦ ?_⟩, hωa'⟩
            have := hGa' (i, p) (mem_product.2 ⟨mem_univ _, mem_range.2 hp⟩)
            simp only [hc, hτ] at this
            unfold owenRelabel
            by_cases hp' : p < 2 ^ M
            · simp only [hp', ite_true] at this ⊢
              rw [hNR ω (ωa a) hagree i p]
              exact this
            · simp only [hp', ite_false] at this ⊢
              exact this
          · simp only [hE', ite_false, Set.mem_empty_iff_false] at h
      have hEpiece : ∀ a : R → Bool, E ∩ R.restrict ⁻¹' ({a} : Set (R → Bool)) =
          if ωa a ∈ E then R.restrict ⁻¹' ({a} : Set (R → Bool)) else ∅ := by
        intro a
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hωE, hωa'⟩
          have hE' : ωa a ∈ E := (hER ω (ωa a) (hcell a ω hωa')).1 hωE
          simp only [hE', ite_true, Set.mem_preimage]
          exact hωa'
        · intro h
          by_cases hE' : ωa a ∈ E
          · simp only [hE', ite_true, Set.mem_preimage] at h
            exact ⟨(hER ω (ωa a) (hcell a ω h)).2 hE', h⟩
          · simp only [hE', ite_false, Set.mem_empty_iff_false] at h
      have hind : ∀ a : R → Bool, owenMeasure n (R.restrict ⁻¹' ({a} : Set (R → Bool)) ∩ Ga a) =
          owenMeasure n (R.restrict ⁻¹' ({a} : Set (R → Bool))) * owenMeasure n (Ga a) := by
        intro a
        refine infinitePi_inter_of_local (fun _ : Fin n × ℕ × ℕ ↦ fairCoin)
          (S := R) (T := ((univ : Finset (Fin n)) ×ˢ range W).image (c a)) ?_ ?_ ?_
        · intro ω ω' h
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          have e : R.restrict ω = R.restrict ω' := funext fun q ↦ h q q.2
          rw [e]
        · intro ω ω' h
          simp only [hGa, Set.mem_ofPred_eq]
          constructor
          · intro h' t ht
            rw [← h _ (mem_image_of_mem _ ht)]
            exact h' t ht
          · intro h' t ht
            rw [h _ (mem_image_of_mem _ ht)]
            exact h' t ht
        · refine Finset.disjoint_left.2 fun q hq hqT ↦ ?_
          obtain ⟨t, -, rfl⟩ := mem_image.1 hqT
          have := (mem_owenRect.1 hq).1
          simp only [hc] at this
          exact lt_irrefl M this
      change owenMeasure n _ = _
      rw [hsplit, measure_eq_sum_restrict_preimage (owenMeasure n) R (E ∩ G)]
      have hsum : ∀ a : R → Bool, owenMeasure n ((E ∩ G) ∩ R.restrict ⁻¹' ({a} : Set (R → Bool))) =
          owenMeasure n (E ∩ R.restrict ⁻¹' ({a} : Set (R → Bool))) * 2⁻¹ ^ (n * W) := by
        intro a
        rw [hpiece a, hEpiece a]
        by_cases hE' : ωa a ∈ E
        · simp only [hE', ite_true]
          rw [hind a, hGam a]
        · simp only [hE', ite_false, measure_empty, zero_mul]
      rw [sum_congr rfl fun a _ ↦ hsum a, ← sum_mul,
        ← measure_eq_sum_restrict_preimage (owenMeasure n) R E]
      change owenMeasure n {ω : Fin n × ℕ × ℕ → Bool |
        ∀ q ∈ owenRect n M W, owenRelabel ω q = b q} * _ = _
      rw [ih, ← pow_add]
      congr 1
      ring

/-- A probability measure on Owen's flips whose box cylinders all have probability
`2^{-|box|}` is `owenMeasure n`. -/
theorem eq_owenMeasure_of_box {μ : Measure (Fin n × ℕ × ℕ → Bool)} [IsProbabilityMeasure μ]
    (h : ∀ (b : Fin n × ℕ × ℕ → Bool) (M : ℕ),
      μ {ω | ∀ q ∈ owenBox n M, ω q = b q} = 2⁻¹ ^ (owenBox n M).card) :
    μ = owenMeasure n := by
  classical
  have hmap : ∀ M, μ.map (Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M)) =
      (owenMeasure n).map
        (Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M)) := by
    intro M
    refine Measure.ext_of_singleton fun g ↦ ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton g)]
    set b : Fin n × ℕ × ℕ → Bool := fun q ↦
      if hq : q ∈ owenBox n M then g ⟨q, hq⟩ else false with hb
    have e : Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M) ⁻¹'
        ({g} : Set ((owenBox n M) → Bool)) =
        {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl q hq
        simp only [hb, hq, dite_true, Finset.restrict]
      · intro hω
        funext q
        have := hω q.1 q.2
        simp only [hb, q.2, dite_true] at this
        exact this
    have ho := coinMeasure_setOf_comp_eq (ι := Fin n × ℕ × ℕ) (c := id)
      Function.injective_id (owenBox n M) b
    rw [e, h b M]
    exact ho.symm
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  set M := s.sup (fun q ↦ q.2.1 + q.2.2) + 1 with hM
  have hsS : ∀ q ∈ s, q ∈ owenBox n M := fun q hq ↦ by
    have hle : q.2.1 + q.2.2 ≤ s.sup (fun q ↦ q.2.1 + q.2.2) :=
      Finset.le_sup (f := fun q : Fin n × ℕ × ℕ ↦ q.2.1 + q.2.2) hq
    rw [owenBox_eq_owenRect]
    refine mem_owenRect.2 ⟨by omega, lt_of_lt_of_le (Nat.lt_two_pow_self) ?_⟩
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set E : Set ((owenBox n M) → Bool) := {g | ∀ q (hq : q ∈ s), g ⟨q, hsS q hq⟩ ∈ t q} with hE
  have hpre : Finset.restrict (π := fun _ : Fin n × ℕ × ℕ ↦ Bool) (owenBox n M) ⁻¹' E =
      Set.pi (s : Set (Fin n × ℕ × ℕ)) t := by
    ext w
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, Set.mem_pi, mem_coe, Finset.restrict]
  have hEm : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← hpre, ← Measure.map_apply (Finset.measurable_restrict _) hEm, hmap M,
    Measure.map_apply (Finset.measurable_restrict _) hEm, hpre,
    Measure.infinitePi_pi _ fun q _ ↦ ht q]

/-- **The relabelling by the scrambled tree preserves Owen's measure**: the relabelled flips
`ω (i, m, σ_m⁻¹ p)` are again i.i.d. fair coins. -/
theorem measurePreserving_owenRelabel :
    MeasurePreserving (owenRelabel (n := n)) (owenMeasure n) (owenMeasure n) := by
  classical
  refine ⟨measurable_owenRelabel, ?_⟩
  refine eq_owenMeasure_of_box fun b M ↦ ?_
  have hm : MeasurableSet {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} := by
    have e : {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} =
        Set.pi ((owenBox n M : Finset (Fin n × ℕ × ℕ)) : Set (Fin n × ℕ × ℕ))
          fun q ↦ ({b q} : Set Bool) := by
      ext ω
      simp [Set.mem_pi]
    rw [e]
    exact MeasurableSet.pi (Set.to_countable _) fun _ _ ↦ measurableSet_singleton _
  rw [Measure.map_apply measurable_owenRelabel hm]
  have e : owenRelabel ⁻¹' {ω : Fin n × ℕ × ℕ → Bool | ∀ q ∈ owenBox n M, ω q = b q} =
      {ω | ∀ q ∈ owenRect n M (2 ^ M), owenRelabel ω q = b q} := by
    ext ω
    rfl
  rw [e, owenMeasure_relabel_rect, owenBox_eq_owenRect, owenRect, card_product, card_product,
    card_univ, Fintype.card_fin, card_range, card_range, mul_assoc]

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stacks CLT for n states: Owen's nested scramble (post #3, code (iii))

Post #3, code (iii): one Sobol (base-2 van der Corput) sequence per state with Owen's nested
scramble; "in the five-state chain normality cannot be rejected for the per-state Sobol
sequences ((ii) and (iii))".

**Reading.** As for the digital shift (`CltNShift`): for any number `n` of states, any
stochastic `P` with Poisson data for every target and any target `s`, along times `T_k → ∞`
with `Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` under Owen's measure, the normalised occupation
error is asymptotically `N(0,1)`; its variance is `O(log T)` and the RMSE of the occupation
frequency `O(√log T / T)`. The variance hypothesis is for Owen's own variance, which differs
from the shift's in general (`CltNExample` shows both satisfy it on the uniform chains; their
values are not claimed equal).

**Proof (separate from the shift).** By `CltThreeState` the path laws of (ii) and (iii) differ
for `n ≥ 3`, so nothing is transferred from the shift. Instead the flips are relabelled by the
scrambled tree (`CltNOwenTree`): the path coin of cut point `c_{ij}` at depth `d` is the
relabelled flip at `(i, d, ⌊2^d c_{ij}⌋)` (`pathCoins_owenTable_eq`), so the main term is the level
sum of the coin layout `owenLayout P` on `Fin n × ℕ × ℕ` with level `q ↦ q.2.1`
(`mainTermN_owenTable_eq`), evaluated at the relabelled flips. Two cut points of a row share
the coordinates of their common binary prefix (the level-sum CLT of `CltNCoins` allows this).
The relabelling preserves Owen's measure (`measurePreserving_owenRelabel`), so the CLT for level
sums transfers (`TendstoInDistribution.comp_measurePreserving`); the Anscombe theorem and
Slutsky finish as for the shift.

**Hypotheses added.** As in `CltNShift`: `IsPoissonFamily P H π`, and the variance hypothesis
along the given times.

## Main results

* `owenLayout`, `pathCoins_owenTable_eq`, `levelSumN_congr`, `mainTermN_owenTable_eq`,
  `owenMainTerm`, `abs_occErrN_owen_sub_le`, `memLp_occErrN_owen`.
* `tendstoInDistribution_occErrN_owen` (**main theorem, code (iii)**).
* `integral_sq_occErrN_owen_le`, `variance_occErrN_owen_le`, `isBigO_meanSq_occFreqN_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The Owen coin layout: cut point `j` of row `i` at depth `d` uses the relabelled flip at the
scrambled node `⌊2^d c_{ij}⌋`. -/
noncomputable def owenLayout (P : Fin n → Fin n → ℝ) : Fin n → ℕ → ℕ → Fin n × ℕ × ℕ :=
  fun i j d ↦ (i, d, ⌊2 ^ d * cutPoint P i j⌋₊)

/-- The level of the Owen coordinate `(i, d, p)` is the depth `d`. -/
theorem owenLayout_lev (P : Fin n → Fin n → ℝ) (i : Fin n) (j d : ℕ) :
    (owenLayout P i j d).2.1 = d := rfl

/-- Different rows use different Owen flips. -/
theorem owenLayout_rows (P : Fin n → Fin n → ℝ) (i i' : Fin n) (j j' d d' : ℕ) (hii' : i ≠ i') :
    owenLayout P i j d ≠ owenLayout P i' j' d' := fun h ↦ hii' (congrArg Prod.fst h)

/-- **Owen path coins are relabelled flips**: for a cut point `c_{ij} < 1`, its path coins are
the relabelled flips of the Owen layout. -/
theorem pathCoins_owenTable_eq (P : Fin n → Fin n → ℝ) (ω : Fin n × ℕ × ℕ → Bool) (i : Fin n)
    (j : ℕ) (hc : cutPoint P i j < 1) :
    pathCoin (owenTable ω i) (threshDigit (cutPoint P i j)) =
      coinsOf (owenLayout P) (owenRelabel ω) i j :=
  funext fun d ↦ pathCoin_owenTable_eq_relabel ω i hc d

/-- Level sums only see the coins of cut points `< 1`. -/
theorem levelSumN_congr {w : ℕ → ℝ} {cp : Fin n → ℕ → ℝ} (N : Fin n → ℕ) (K : ℕ)
    {e e' : Fin n → ℕ → ℕ → Bool} (h : ∀ i j, cp i j < 1 → e i j = e' i j) :
    levelSumN w cp N K e = levelSumN w cp N K e' := by
  refine sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  unfold cutTerm
  by_cases hc : cp i j < 1
  · simp only [hc, ite_true]
    rw [h i j hc]
  · simp only [hc, ite_false]

/-- The main term of the Owen-scrambled chain as a level sum of relabelled flips `ω'`, with
`⌊log₂ T⌋ + 1` levels. -/
noncomputable def owenMainTerm (P : Fin n → Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) (ω' : Fin n × ℕ × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (H s)) (cutPoint P) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (owenLayout P) ω')

/-- The main term of the Owen-scrambled chain is the level sum at the relabelled flips. -/
theorem mainTermN_owenTable_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (s : Fin n) (T : ℕ)
    (ω : Fin n × ℕ × ℕ → Bool) :
    mainTermN P (H s) pi (owenTable ω) T = owenMainTerm P H pi s T (owenRelabel ω) := by
  rw [mainTermN_eq_levelSumN hP (H s) pi (owenTable ω) T (chainIdxN_lt_two_pow hP hH T),
    owenMainTerm]
  exact levelSumN_congr _ _ fun i j hc ↦ pathCoins_owenTable_eq P ω i j hc

/-- The occupation error of the Owen-scrambled chain is within `ansBoundN` of the level sum. -/
theorem abs_occErrN_owen_sub_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) (ω : Fin n × ℕ × ℕ → Bool) :
    |occErrN P pi x₀ (owenTable ω) s T - owenMainTerm P H pi s T (owenRelabel ω)| ≤
      ansBoundN H s T := by
  rw [← mainTermN_owenTable_eq hP hH s T ω]
  exact abs_occErrN_sub_mainTermN_le hP hH x₀ (owenTable ω) s T

/-- The occupation error of the Owen-scrambled chain is in `L²`. -/
theorem memLp_occErrN_owen (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (x₀ s : Fin n) (T : ℕ) :
    MemLp (fun ω ↦ occErrN P pi x₀ (owenTable ω) s T) 2 (owenMeasure n) := by
  have hm : Measurable fun ω : Fin n × ℕ × ℕ → Bool ↦ occErrN P pi x₀ (owenTable ω) s T :=
    ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
      (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ s T)).sub measurable_const
  exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact abs_occErrN_le P pi x₀ _ s T)

/-- The relabelled main term has the moments of the level sum: it is centred. -/
theorem integral_owenMainTerm_relabel {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (H : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (s : Fin n) (T : ℕ) :
    ∫ ω, owenMainTerm P H pi s T (owenRelabel ω) ∂(owenMeasure n) = 0 := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hγ : ∀ i j, Function.Injective (owenLayout P i j) := fun i j d d' h ↦
    congrArg (fun q : Fin n × ℕ × ℕ ↦ q.2.1) h
  have hGm := measurable_levelSumN_coins (w := cutWeight (H s)) hcp (chainIdxN pi T)
    (Nat.log 2 T + 1) (owenLayout P)
  unfold owenMainTerm
  rw [← integral_map measurable_owenRelabel.aemeasurable hGm.aestronglyMeasurable,
    measurePreserving_owenRelabel.map_eq]
  exact integral_levelSumN_coins hcp _ _ hγ

/-- **The stacks CLT for n states, Owen's scramble** (post #3, code (iii)). For a stochastic `P`
on `Fin n` with Poisson data `H`, `π` for every target, a target `s`, and `T_k → ∞` with
`Var(N_s(T_k) − T_k π_s) ≥ κ log₂ T_k` eventually (Owen's variance),
`(N_s(T_k) − T_k π_s) / √Var(N_s(T_k) − T_k π_s) ⇒ N(0,1)`. -/
theorem tendstoInDistribution_occErrN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s (T k); owenMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ occErrN P pi x₀ (owenTable ω) s (T k) /
      √Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s (T k); owenMeasure n]) atTop Z
      (fun _ ↦ owenMeasure n) P' := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  set G : ℕ → (Fin n × ℕ × ℕ → Bool) → ℝ := fun k ω' ↦ owenMainTerm P H pi s (T k) ω' with hG
  have hGm : ∀ k, Measurable (G k) := fun k ↦
    measurable_levelSumN_coins (w := cutWeight (H s)) hcp _ _ (owenLayout P)
  have hvarG : ∀ k, Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n] =
      Var[G k; owenMeasure n] := fun k ↦ hMP.variance_fun_comp (hGm k).aemeasurable
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ occErrN P pi x₀ (owenTable ω) s (T k))
    (M := fun k ω ↦ G k (owenRelabel ω)) hT (b := fun k ↦ ansBoundN H s (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ ansBoundN_nonneg H s (T k))
      (fun k ↦ ansBoundN_le_log H s (T k)))
    (fun k ↦ memLp_occErrN_owen P pi x₀ s (T k))
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ (owenLayout P)).comp_measurePreserving hMP)
    (fun k ↦ integral_owenMainTerm_relabel hP H pi s (T k))
    (fun k ω ↦ abs_occErrN_owen_sub_le hP hH x₀ s (T k) ω) hκ hvar ?_
  intro κ' hκ' hv
  have hv' : ∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[G k; owenMeasure n] := by
    filter_upwards [hv] with k hk
    rwa [← hvarG k]
  have hclt := tendstoInDistribution_levelSumN (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
    (γ := owenLayout P) (fun i j d ↦ rfl) hcp (w := cutWeight (H s))
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv' hZ
  have htr := TendstoInDistribution.comp_measurePreserving hMP hclt
  have e : (fun k ω ↦ G k (owenRelabel ω) / √Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n]) =
      fun k ω ↦ G k (owenRelabel ω) / √Var[G k; owenMeasure n] := by
    funext k ω
    rw [hvarG k]
  rw [e]
  exact htr

/-- **Mean-square bound** (Owen): `E[(N_s(T) − T π_s)²] ≤ C (⌊log₂ T⌋ + 1)`. -/
theorem integral_sq_occErrN_owen_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    ∫ ω, occErrN P pi x₀ (owenTable ω) s T ^ 2 ∂(owenMeasure n) ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) := by
  have hcp : ∀ i j, 0 ≤ cutPoint P i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  have hGm := measurable_levelSumN_coins (w := cutWeight (H s)) hcp (chainIdxN pi T)
    (Nat.log 2 T + 1) (owenLayout P)
  have hV0 := integral_sq_levelSumN_le (fun q : Fin n × ℕ × ℕ ↦ q.2.1) (γ := owenLayout P)
    (fun i j d ↦ rfl) hcp (w := cutWeight (H s)) (chainIdxN pi T) (Nat.log 2 T + 1)
  have hV : ∫ ω, owenMainTerm P H pi s T (owenRelabel ω) ^ 2 ∂(owenMeasure n) ≤
      ((Nat.log 2 T + 1 : ℕ) : ℝ) * (5 * (n * absWeightSum n (cutWeight (H s))) ^ 2) := by
    rw [← integral_map (f := fun ω' ↦ owenMainTerm P H pi s T ω' ^ 2)
      measurable_owenRelabel.aemeasurable (hGm.pow_const 2).aestronglyMeasurable, hMP.map_eq]
    exact hV0
  have h := integral_sq_le_of_close (memLp_occErrN_owen P pi x₀ s T)
    ((memLp_levelSumN_coins hcp _ _ (owenLayout P)).comp_measurePreserving hMP)
    (abs_occErrN_owen_sub_le hP hH x₀ s T) hV
  have hb := two_mul_ansBoundN_sq_le H s T
  refine h.trans ?_
  rw [varConstN]
  push_cast
  change 2 * (((Nat.log 2 T : ℝ) + 1) * (5 * (n * cutWeightSum (H s)) ^ 2)) +
    2 * ansBoundN H s T ^ 2 ≤ _
  nlinarith

/-- **Variance bound** (Owen): `Var(N_s(T) − T π_s) ≤ C (⌊log₂ T⌋ + 1) = O(log T)`. -/
theorem variance_occErrN_owen_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n)
    (T : ℕ) :
    Var[fun ω ↦ occErrN P pi x₀ (owenTable ω) s T; owenMeasure n] ≤
      varConstN H s * ((Nat.log 2 T : ℝ) + 1) :=
  (variance_le_expectation_sq (memLp_occErrN_owen P pi x₀ s T).aestronglyMeasurable).trans
    (integral_sq_occErrN_owen_le hP hH x₀ s T)

/-- **RMSE of the occupation frequency is `O(√log T / T)`** (Owen, n states):
`E[(N_s(T)/T − π_s)²] = O(log T / T²)`. -/
theorem isBigO_meanSq_occFreqN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ s : Fin n) :
    (fun T : ℕ ↦ ∫ ω, (occErrN P pi x₀ (owenTable ω) s T / T) ^ 2 ∂(owenMeasure n)) =O[atTop]
      fun T : ℕ ↦ (Nat.log 2 T : ℝ) / (T : ℝ) ^ 2 :=
  isBigO_meanSq_div_of_le (E := fun T ω ↦ occErrN P pi x₀ (owenTable ω) s T)
    (integral_sq_occErrN_owen_le hP hH x₀ s)

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Non-vacuity of the n-state stacks CLT: uniform chains (post #3)

The CLTs `tendstoInDistribution_occErrN_shift` (code (ii)) and
`tendstoInDistribution_occErrN_owen` (code (iii)) assume `Var ≥ κ log T` along the given times.
This module proves that hypothesis, for BOTH randomisations, on the uniform chains
`P i j = 1/n` with `n` not a power of two (in particular `n = 3`, the REQUIRED example, and
`n = 5`, the number of states of post #3), and every target `s`. Every row has `n − 1` cut points
`j/n` in play, so Owen's tree of paths matters (two cut points share the flips of their common
binary prefix only).

* Poisson data: `H t = 1_{t} − 1/n`, `π = 1/n` (`isPoissonFamily_uniform`). The weights are
  `h_j − h_{j+1} = 1{j = s} − 1{j+1 = s} ∈ {−1, 0, 1}`, total `W ≤ 2`.
* Times `T_k = n Σ_{a<k} 2^{ra}` with spacing `r = 2n + 6` (`uniformTime`), so that
  `⌊T_k π_i⌋ = Σ_{a<k} 2^{ra}` in every row (`chainIdxN_uniformTime`).
* Per level, a row term is an integer minus `θ`, where `θ ≡ 2^m/n (mod 1)` (`rowFrac_uniform`),
  whose fractional part is `(2^m mod n)/n ∈ [1/n, 1 − 1/n]` as `n ∤ 2^m`; the integer variance
  bound gives `Var ≥ (n − 1)/n²` under ANY randomisation (`variance_rowTerm_uniform_ge`); for
  `n = 3` this is the value `2/9` of the brief.
* Rows are independent and levels at distance `d` have covariance `≤ 2W² 2^{-d}`; the spacing makes
  the diagonal dominate: `Var(main term) ≥ k/4` (`variance_levelSumN_uniform_ge`), and then
  `Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually
  (`eventually_variance_occErrN_uniform_shift_ge`, `_owen_ge`).

The values are consistent with simulation (`3·10³` replications, `400` for `k = 3`; spacing `8`
rather than the proof's `2n + 6`): for three states the
per-row variance at `k = 1, 2, 3` levels is `0.22, 0.42, 0.73` (shift) and `0.23, 0.66, 1.02`
(Owen), against the bound `(n − 1)/n² = 2/9` per level; for five states `0.16, 0.32, 0.50` (shift)
and `0.17, 0.66, 1.04` (Owen), against `4/25`. The two randomisations have different variances
(Owen's larger here); only the common lower bound is proved.

**Correction / scope.** For `n` a power of two the cut points are dyadic and there is no CLT at
all (`StackDyadic`); here `n ∤ 2^m` is assumed. Post #3's five-state Farmer–Toda probabilities are
not dyadic-checkable numbers, so the five-state instance is the uniform chain.

## Main results

* `uniformChain`, `uniformPoisson`, `uniformPi`, `uniformSpacing`, `uniformTime`;
  `isStochastic_uniformChain`, `isPoissonFamily_uniform`.
* `variance_levelSumN_uniform_ge` (any coin layout with independent rows).
* `eventually_variance_ge_of_close` (variance lower bounds pass to an `o(√k)` perturbation).
* `eventually_variance_occErrN_uniform_shift_ge`, `eventually_variance_occErrN_uniform_owen_ge`
  (**non-vacuity**), `occErrN_uniform_tendstoInDistribution_shift`, `_owen`.
* Three states, target `1` (REQUIRED): `eventually_variance_occErrN_example_shift_ge`,
  `eventually_variance_occErrN_example_owen_ge`, `occErrN_example_tendstoInDistribution_shift`,
  `occErrN_example_tendstoInDistribution_owen`.
* Five states, target `2`: `occErrN_five_tendstoInDistribution_shift`, `_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-! ### The uniform chain -/

/-- The uniform chain `P i j = 1/n`. -/
noncomputable def uniformChain (n : ℕ) : Fin n → Fin n → ℝ := fun _ _ ↦ 1 / n

/-- Its Poisson functions `H t = 1_{t} − 1/n`. -/
noncomputable def uniformPoisson (n : ℕ) : Fin n → Fin n → ℝ :=
  fun t i ↦ (if i = t then 1 else 0) - 1 / n

/-- Its stationary distribution `π = 1/n`. -/
noncomputable def uniformPi (n : ℕ) : Fin n → ℝ := fun _ ↦ 1 / n

/-- The spacing `r = 2n + 6` of the levels. -/
def uniformSpacing (n : ℕ) : ℕ := 2 * n + 6

/-- The times `T_k = n Σ_{a<k} 2^{ra}`. -/
def uniformTime (n k : ℕ) : ℕ := n * patternR (uniformSpacing n) k

/-- The uniform chain is stochastic. -/
theorem isStochastic_uniformChain (hn : 1 ≤ n) : IsStochastic (uniformChain n) where
  nonneg _ _ := by unfold uniformChain; positivity
  sum_eq_one _ := by
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [uniformChain, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

open Matrix in
/-- `P H_t = 0` for the uniform chain. -/
theorem mulVec_uniformPoisson (hn : 1 ≤ n) (t i : Fin n) :
    (uniformChain n *ᵥ uniformPoisson n t) i = 0 := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  change ∑ k, uniformChain n i k * uniformPoisson n t k = 0
  simp only [uniformChain, uniformPoisson, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Poisson data of the uniform chain** for every target. -/
theorem isPoissonFamily_uniform (hn : 1 ≤ n) :
    IsPoissonFamily (uniformChain n) (uniformPoisson n) (uniformPi n) := fun t i ↦ by
  rw [mulVec_uniformPoisson hn, sub_zero]
  rfl

/-- `n_i(T_k) = Σ_{a<k} 2^{ra}` in every row. -/
theorem chainIdxN_uniformTime (hn : 1 ≤ n) (k : ℕ) :
    chainIdxN (uniformPi n) (uniformTime n k) = fun _ ↦ patternR (uniformSpacing n) k := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  funext i
  unfold chainIdxN uniformTime uniformPi
  push_cast
  rw [show (n : ℝ) * (patternR (uniformSpacing n) k : ℝ) * (1 / n) =
    (patternR (uniformSpacing n) k : ℝ) by field_simp]
  exact Nat.floor_natCast _

/-- The weights of the uniform chain: `h_j − h_{j+1} = 1{j = s} − 1{j + 1 = s}`. -/
theorem cutWeight_uniform (s : Fin n) {j : ℕ} (hj : j + 1 < n) :
    cutWeight (uniformPoisson n s) j =
      (if j = s.val then 1 else 0) - (if j + 1 = s.val then 1 else 0) := by
  have hj' : j < n := by omega
  unfold cutWeight extendNat
  simp only [hj', hj, dite_true, uniformPoisson, Fin.ext_iff]
  ring

/-- The weights are integers. -/
theorem cutWeight_uniform_int (s : Fin n) :
    ∀ j ∈ range (n - 1), ∃ z : ℤ, cutWeight (uniformPoisson n s) j = z := by
  intro j hj
  have hj' : j + 1 < n := by have := mem_range.1 hj; omega
  refine ⟨(if j = s.val then 1 else 0) - (if j + 1 = s.val then 1 else 0), ?_⟩
  rw [cutWeight_uniform s hj']
  push_cast
  rfl

/-- The total weight is at most `2`. -/
theorem absWeightSum_uniform_le (s : Fin n) :
    absWeightSum n (cutWeight (uniformPoisson n s)) ≤ 2 := by
  unfold absWeightSum
  calc ∑ j ∈ range (n - 1), |cutWeight (uniformPoisson n s) j|
      ≤ ∑ j ∈ range (n - 1), ((if j = s.val then (1 : ℝ) else 0) +
          (if j = s.val - 1 then (1 : ℝ) else 0)) := by
        refine sum_le_sum fun j hj ↦ ?_
        have hj' : j + 1 < n := by have := mem_range.1 hj; omega
        rw [cutWeight_uniform s hj']
        split_ifs <;> first | (norm_num; done) | omega
    _ = (∑ j ∈ range (n - 1), if j = s.val then (1 : ℝ) else 0) +
          ∑ j ∈ range (n - 1), if j = s.val - 1 then (1 : ℝ) else 0 := sum_add_distrib
    _ ≤ 1 + 1 := by
        rw [sum_ite_eq', sum_ite_eq']
        gcongr <;> split_ifs <;> norm_num
    _ = 2 := by norm_num

/-- `{2^m · 1} = 0`. -/
theorem fracPow_one (m : ℕ) : fracPow 1 m = 0 := by
  rw [fracPow, mul_one, show (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_natCast, sub_self]

/-- For `c ≤ 1`, the cut-point fractional part vanishes at `c = 1`. -/
theorem ite_fracPow_eq {c : ℝ} (hc : c ≤ 1) (m : ℕ) :
    (if c < 1 then fracPow c m else 0) = fracPow c m := by
  by_cases h : c < 1
  · simp [h]
  · have : c = 1 := le_antisymm hc (not_lt.1 h)
    subst this
    simp [fracPow_one]

/-- **The weighted cut points are `1/n` modulo integers** (from Abel summation at `u = 0`). -/
theorem sum_cutWeight_mul_cutPoint_uniform (hn : 1 ≤ n) (s i : Fin n) :
    ∃ z : ℤ, ∑ j ∈ range (n - 1),
      cutWeight (uniformPoisson n s) j * cutPoint (uniformChain n) i j = z + 1 / n := by
  have hP := isStochastic_uniformChain hn
  have h := step_sub_mulVec_eq_sum_cut hP (uniformPoisson n s) i (u := 0) (by norm_num)
  rw [mulVec_uniformPoisson hn, sub_zero] at h
  have h' : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
      ((if (0 : ℝ) ≤ cutPoint (uniformChain n) i j then 1 else 0) -
        cutPoint (uniformChain n) i j) =
      ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j -
        ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
          cutPoint (uniformChain n) i j := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [(cutPoint_mem_Icc hP i j).1, ite_true]
    ring
  rw [h'] at h
  choose! zw hzw using cutWeight_uniform_int (n := n) s
  have hsum : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j =
      ((∑ j ∈ range (n - 1), zw j : ℤ) : ℝ) := by
    push_cast
    exact sum_congr rfl fun j hj ↦ hzw j hj
  refine ⟨(∑ j ∈ range (n - 1), zw j) - (if step (uniformChain n) i 0 = s then 1 else 0), ?_⟩
  rw [hsum] at h
  simp only [uniformPoisson] at h
  push_cast at h ⊢
  split_ifs at h ⊢ <;> linarith

/-- **The row fraction of the uniform chain is `2^m/n` modulo integers.** -/
theorem rowFrac_uniform (hn : 1 ≤ n) (s i : Fin n) (m : ℕ) :
    ∃ z : ℤ, rowFrac (cutWeight (uniformPoisson n s)) (cutPoint (uniformChain n)) m i =
      2 ^ m / n + z := by
  have hP := isStochastic_uniformChain hn
  obtain ⟨z, hz⟩ := sum_cutWeight_mul_cutPoint_uniform hn s i
  choose! zw hzw using cutWeight_uniform_int (n := n) s
  refine ⟨2 ^ m * z - ∑ j ∈ range (n - 1), zw j * ⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊, ?_⟩
  have e : rowFrac (cutWeight (uniformPoisson n s)) (cutPoint (uniformChain n)) m i =
      2 ^ m * ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
        cutPoint (uniformChain n) i j -
      ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
        (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) := by
    rw [rowFrac, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [ite_fracPow_eq (cutPoint_mem_Icc hP i j).2, fracPow]
    ring
  rw [e, hz]
  push_cast
  have e2 : ∑ j ∈ range (n - 1), cutWeight (uniformPoisson n s) j *
      (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) =
      ∑ j ∈ range (n - 1), (zw j : ℝ) * (⌊2 ^ m * cutPoint (uniformChain n) i j⌋₊ : ℝ) :=
    sum_congr rfl fun j hj ↦ by rw [hzw j hj]
  rw [e2]
  ring

/-- `{2^m / n} = (2^m mod n)/n`, which lies in `[1/n, 1 − 1/n]` when `n ∤ 2^m`. -/
theorem fract_mul_one_sub_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m) (m : ℕ) :
    ((n : ℝ) - 1) / n ^ 2 ≤
      Int.fract ((2 : ℝ) ^ m / n) * (1 - Int.fract ((2 : ℝ) ^ m / n)) := by
  have hfr : Int.fract ((2 : ℝ) ^ m / n) = ((2 ^ m % n : ℕ) : ℝ) / n := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 2 ^ m) (n := n)
    push_cast at this
    exact this
  set r' := 2 ^ m % n with hr'
  have hr1 : 1 ≤ r' := Nat.pos_of_ne_zero fun h ↦ hnd m (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r' < n := Nat.mod_lt _ (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr1' : (1 : ℝ) ≤ r' := by exact_mod_cast hr1
  have hr2' : (r' : ℝ) + 1 ≤ n := by exact_mod_cast hr2
  rw [hfr, div_le_iff₀ (by positivity)]
  have e : (r' : ℝ) / n * (1 - r' / n) * n ^ 2 = r' * (n - r') := by
    field_simp
  rw [e]
  nlinarith

/-- **Per-level variance** of a row term of the uniform chain (any coin layout): at a set bit,
`Var ≥ (n − 1)/n²` (`2/9` for `n = 3`). -/
theorem variance_rowTerm_uniform_ge {ι : Type*} {γ : Fin n → ℕ → ℕ → ι}
    (hγ : ∀ i j, Function.Injective (γ i j)) (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (s : Fin n) (N : Fin n → ℕ) (m : ℕ) (i : Fin n) (hbit : (N i).testBit m = true) :
    ((n : ℝ) - 1) / n ^ 2 ≤ Var[fun ω ↦ rowTerm (cutWeight (uniformPoisson n s))
      (cutPoint (uniformChain n)) N m (coinsOf γ ω) i; coinMeasure ι] := by
  have hP := isStochastic_uniformChain (n := n) (by omega)
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  refine le_trans ?_ (variance_rowTerm_ge_of_int hγ hcp (cutWeight_uniform_int s) N m i hbit)
  obtain ⟨z, hz⟩ := rowFrac_uniform (by omega) s i m
  rw [hz, Int.fract_add_intCast]
  exact fract_mul_one_sub_ge hn2 hnd m

/-- `ρ = 2^{-(2n+6)}` is small: `4 W² ρ/(1 − ρ) ≤ (n − 1)/(2n²)` for `W ≤ 2`. -/
theorem uniformSpacing_bound (hn2 : 2 ≤ n) {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 2) :
    4 * W ^ 2 * ((1 / 2) ^ uniformSpacing n / (1 - (1 / 2) ^ uniformSpacing n)) ≤
      ((n : ℝ) - 1) / n ^ 2 / 2 := by
  set ρ : ℝ := (1 / 2) ^ uniformSpacing n with hρ
  have hρ0 : 0 < ρ := by positivity
  have hq : ((1 : ℝ) / 2) ^ n * n < 1 := by
    have h1 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    exact h1
  have hρe : ρ = (1 / 64) * ((1 / 2) ^ n) ^ 2 := by
    rw [hρ, uniformSpacing, ← pow_mul, show 2 * n + 6 = n * 2 + 6 by ring, pow_add]
    norm_num
    ring
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρ]
    calc ((1 : ℝ) / 2) ^ uniformSpacing n ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold uniformSpacing; omega)
      _ = 1 / 2 := by norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have h64 : 64 * (n : ℝ) ^ 2 * ρ ≤ 1 := by
    rw [hρe]
    have hq0 : 0 ≤ ((1 : ℝ) / 2) ^ n * n := by positivity
    nlinarith
  have hfrac : ρ / (1 - ρ) ≤ 2 * ρ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hW2 : W ^ 2 ≤ 4 := by nlinarith
  calc 4 * W ^ 2 * (ρ / (1 - ρ)) ≤ 4 * 4 * (2 * ρ) := by
        gcongr
        · exact div_nonneg hρ0.le (by linarith)
    _ = 32 * ρ := by ring
    _ ≤ ((n : ℝ) - 1) / n ^ 2 / 2 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        nlinarith

/-- **Variance of the main term of the uniform chain** (any coin layout with independent rows):
along `n_i = Σ_{a<k} 2^{ra}`, `Var(levelSumN) ≥ k/4`. -/
theorem variance_levelSumN_uniform_ge {ι : Type*} (lev : ι → ℕ) {γ : Fin n → ℕ → ℕ → ι}
    (hlev : ∀ i j d, lev (γ i j d) = d)
    (hrows : ∀ i i' j j' d d', i ≠ i' → γ i j d ≠ γ i' j' d') (hn2 : 2 ≤ n)
    (hnd : ∀ m, ¬ n ∣ 2 ^ m) (s : Fin n) {k K : ℕ}
    (hK : ∀ a < k, uniformSpacing n * a < K) :
    (k : ℝ) / 4 ≤ Var[fun ω ↦ levelSumN (cutWeight (uniformPoisson n s))
      (cutPoint (uniformChain n)) (fun _ ↦ patternR (uniformSpacing n) k) K (coinsOf γ ω);
      coinMeasure ι] := by
  have hγ : ∀ i j, Function.Injective (γ i j) := fun i j d d' h ↦ by
    have := congrArg lev h
    rwa [hlev, hlev] at this
  have hP := isStochastic_uniformChain (n := n) (by omega)
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hr : 1 ≤ uniformSpacing n := by unfold uniformSpacing; omega
  have h := variance_levelSumN_pattern_ge lev hlev hrows hcp hr hK
    (N := fun _ ↦ patternR (uniformSpacing n) k) (fun _ ↦ rfl) (a₀ := ((n : ℝ) - 1) / n ^ 2)
    (w := cutWeight (uniformPoisson n s)) fun i a ha ↦
      variance_rowTerm_uniform_ge hγ hn2 hnd s _ _ i
        ((testBit_patternR hr k _).2 ⟨Nat.mul_mod_right _ _, by
          rw [Nat.mul_div_cancel_left _ (by omega)]; exact ha⟩)
  refine le_trans ?_ h
  have hb := uniformSpacing_bound hn2 (absWeightSum_nonneg n (cutWeight (uniformPoisson n s)))
    (absWeightSum_uniform_le s)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkey : (k : ℝ) / 4 ≤ n * k * (((n : ℝ) - 1) / n ^ 2 / 2) := by
    have e : (n : ℝ) * k * (((n : ℝ) - 1) / n ^ 2 / 2) = k * ((n - 1) / (2 * n)) := by
      field_simp
    rw [e]
    have : (1 : ℝ) / 4 ≤ (n - 1) / (2 * n) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    nlinarith
  refine hkey.trans ?_
  gcongr
  linarith

/-! ### From the main term to the occupation error -/

/-- **Variance lower bounds survive an `o(√k)` perturbation**: if `|E_k − M_k| ≤ b_k`,
`Var M_k ≥ c k` eventually and `b_k² / k → 0`, then `Var E_k ≥ c k / 4` eventually. -/
theorem eventually_variance_ge_of_close {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E M : ℕ → Ω → ℝ} {b : ℕ → ℝ} (hE : ∀ k, MemLp (E k) 2 μ)
    (hM : ∀ k, MemLp (M k) 2 μ) (hclose : ∀ k ω, |E k ω - M k ω| ≤ b k) {c : ℝ} (hc : 0 < c)
    (hVM : ∀ᶠ k in atTop, c * k ≤ Var[M k; μ])
    (hb : Tendsto (fun k ↦ b k ^ 2 / k) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, c / 4 * k ≤ Var[E k; μ] := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ (abs_nonneg _).trans (hclose k (Classical.arbitrary Ω))
  have hsmall : ∀ᶠ k in atTop, b k ^ 2 / k ≤ c / 4 :=
    hb.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hVM, hsmall, eventually_ge_atTop 1] with k hk hs hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ : |√Var[M k; μ] - √Var[E k; μ]| ≤ b k := by
    refine (abs_sqrt_variance_sub_le (hE k) (hM k)).trans ?_
    refine (Real.sqrt_le_sqrt (variance_le_sq_of_bounded (a := -b k) (b := b k)
      (Eventually.of_forall fun ω ↦ abs_le.1 (hclose k ω))
      ((hE k).sub (hM k)).aestronglyMeasurable.aemeasurable)).trans (le_of_eq ?_)
    rw [show (b k - -b k) / 2 = b k by ring, Real.sqrt_sq (hb0 k)]
  set sM := √Var[M k; μ] with hsM
  set sE := √Var[E k; μ] with hsE
  have hsM2 : sM ^ 2 = Var[M k; μ] := Real.sq_sqrt (variance_nonneg _ _)
  have hsE2 : sE ^ 2 = Var[E k; μ] := Real.sq_sqrt (variance_nonneg _ _)
  have hsM0 : 0 ≤ sM := Real.sqrt_nonneg _
  have hb2 : b k ^ 2 ≤ c * k / 4 := by
    rw [div_le_iff₀ hk0] at hs
    linarith
  have hbM : b k ≤ sM / 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith [hb0 k]
  have hsE : sM / 2 ≤ sE := by
    have := (abs_le.1 hσ).2
    linarith
  have h4 : sM ^ 2 / 4 ≤ sE ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hsE 2
    rw [div_pow] at this
    linarith
  rw [← hsE2]
  nlinarith

/-- `2^{ra} ≤ T_k` for `a < k`, so the levels `ra` are below `⌊log₂ T_k⌋ + 1`. -/
theorem uniformSpacing_mul_lt (hn : 1 ≤ n) {k a : ℕ} (ha : a < k) :
    uniformSpacing n * a < Nat.log 2 (uniformTime n k) + 1 := by
  have h1 : 2 ^ (uniformSpacing n * a) ≤ patternR (uniformSpacing n) k :=
    single_le_sum (f := fun a ↦ 2 ^ (uniformSpacing n * a)) (fun _ _ ↦ Nat.zero_le _)
      (mem_range.2 ha)
  have h2 : patternR (uniformSpacing n) k ≤ uniformTime n k := by
    unfold uniformTime
    exact Nat.le_mul_of_pos_left _ (by omega)
  have := Nat.le_log_of_pow_le one_lt_two (h1.trans h2)
  omega

/-- `⌊log₂ T_k⌋ ≤ (n + r) k` for `k ≥ 1`. -/
theorem natLog_uniformTime_le {k : ℕ} (hk : 1 ≤ k) :
    Nat.log 2 (uniformTime n k) ≤ (n + uniformSpacing n) * k := by
  have hr : 1 ≤ uniformSpacing n := by unfold uniformSpacing; omega
  have hlt : uniformTime n k < 2 ^ (n + uniformSpacing n * k) := by
    unfold uniformTime
    rw [pow_add]
    exact Nat.mul_lt_mul'' Nat.lt_two_pow_self (patternR_lt hr k)
  by_cases h0 : uniformTime n k = 0
  · rw [h0, Nat.log_zero_right]
    exact Nat.zero_le _
  have := Nat.log_lt_of_lt_pow h0 hlt
  nlinarith

/-- `T_k → ∞`. -/
theorem tendsto_uniformTime (hn : 1 ≤ n) : Tendsto (uniformTime n) atTop atTop := by
  refine tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
  have h : k ≤ patternR (uniformSpacing n) k := by
    rw [patternR]
    calc k = ∑ _a ∈ range k, 1 := by simp
      _ ≤ ∑ a ∈ range k, 2 ^ (uniformSpacing n * a) :=
          sum_le_sum fun a _ ↦ Nat.one_le_two_pow
  exact h.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- The Anscombe error along the uniform times is `o(√k)`. -/
theorem tendsto_ansBoundN_uniform (hn : 1 ≤ n) (s : Fin n) :
    Tendsto (fun k ↦ ansBoundN (uniformPoisson n) s (uniformTime n k) ^ 2 / k) atTop (𝓝 0) := by
  have h := tendsto_sq_div_natLog_of_le (tendsto_uniformTime hn)
    (fun k ↦ ansBoundN_nonneg (uniformPoisson n) s (uniformTime n k))
    (fun k ↦ ansBoundN_le_log (uniformPoisson n) s (uniformTime n k))
  have hlim := h.const_mul ((n : ℝ) + uniformSpacing n)
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hlim
  have hlog : ∀ᶠ k in atTop, 1 ≤ Nat.log 2 (uniformTime n k) :=
    ((tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun _ ht ↦ Nat.le_log_of_pow_le one_lt_two ht⟩).comp
      (tendsto_uniformTime hn)).eventually_ge_atTop 1
  filter_upwards [hlog, eventually_ge_atTop 1] with k hl hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < Nat.log 2 (uniformTime n k) := by exact_mod_cast hl
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk
  have hb := sq_nonneg (ansBoundN (uniformPoisson n) s (uniformTime n k))
  rw [mul_div_assoc', div_le_div_iff₀ hk0 hl0]
  nlinarith

/-- **Non-vacuity, digital shift** (uniform chain, `n` not a power of two, any target):
`Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually. -/
theorem eventually_variance_occErrN_uniform_shift_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) :
    ∀ᶠ k in atTop, 1 / (16 * ((n : ℝ) + uniformSpacing n)) * Nat.log 2 (uniformTime n k) ≤
      Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k);
        shiftMeasure n] := by
  have hn : 1 ≤ n := by omega
  have hP := isStochastic_uniformChain hn
  have hH := isPoissonFamily_uniform hn
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hVM : ∀ᶠ k in atTop, (1 / 4 : ℝ) * k ≤ Var[fun ω ↦ shiftMainTerm (uniformChain n)
      (uniformPoisson n) (uniformPi n) s (uniformTime n k) ω; shiftMeasure n] := by
    refine Eventually.of_forall fun k ↦ ?_
    have h := variance_levelSumN_uniform_ge (fun q : Fin n × ℕ ↦ q.2) (γ := shiftLayout n)
      (fun i j d ↦ rfl) shiftLayout_rows hn2 hnd s (k := k)
      (K := Nat.log 2 (uniformTime n k) + 1) fun a ha ↦ uniformSpacing_mul_lt hn ha
    unfold shiftMainTerm
    rw [chainIdxN_uniformTime hn k]
    linarith
  have hev := eventually_variance_ge_of_close
    (E := fun k ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k))
    (M := fun k ω ↦ shiftMainTerm (uniformChain n) (uniformPoisson n) (uniformPi n) s
      (uniformTime n k) ω)
    (fun k ↦ memLp_occErrN_shift _ _ x₀ s _)
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ω ↦ abs_occErrN_shift_sub_le hP hH x₀ s _ ω) (by norm_num : (0 : ℝ) < 1 / 4) hVM
    (tendsto_ansBoundN_uniform hn s)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk1
  have hpos : (0 : ℝ) < (n : ℝ) + uniformSpacing n := by positivity
  refine le_trans ?_ hk
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Non-vacuity, Owen's scramble** (uniform chain, `n` not a power of two, any target):
`Var(N_s(T_k) − T_k/n) ≥ log₂ T_k / (16 (n + r))` eventually (Owen's own variance). -/
theorem eventually_variance_occErrN_uniform_owen_ge (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) :
    ∀ᶠ k in atTop, 1 / (16 * ((n : ℝ) + uniformSpacing n)) * Nat.log 2 (uniformTime n k) ≤
      Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k);
        owenMeasure n] := by
  have hn : 1 ≤ n := by omega
  have hP := isStochastic_uniformChain hn
  have hH := isPoissonFamily_uniform hn
  have hcp : ∀ i j, 0 ≤ cutPoint (uniformChain n) i j := fun i j ↦ (cutPoint_mem_Icc hP i j).1
  have hMP := measurePreserving_owenRelabel (n := n)
  have hVM : ∀ᶠ k in atTop, (1 / 4 : ℝ) * k ≤ Var[fun ω ↦ owenMainTerm (uniformChain n)
      (uniformPoisson n) (uniformPi n) s (uniformTime n k) (owenRelabel ω); owenMeasure n] := by
    refine Eventually.of_forall fun k ↦ ?_
    have h := variance_levelSumN_uniform_ge (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
      (γ := owenLayout (uniformChain n)) (fun i j d ↦ rfl) (owenLayout_rows _) hn2 hnd s
      (k := k) (K := Nat.log 2 (uniformTime n k) + 1) fun a ha ↦ uniformSpacing_mul_lt hn ha
    unfold owenMainTerm
    rw [hMP.variance_fun_comp (measurable_levelSumN_coins hcp _ _ _).aemeasurable,
      chainIdxN_uniformTime hn k]
    linarith
  have hev := eventually_variance_ge_of_close
    (E := fun k ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k))
    (M := fun k ω ↦ owenMainTerm (uniformChain n) (uniformPoisson n) (uniformPi n) s
      (uniformTime n k) (owenRelabel ω))
    (fun k ↦ memLp_occErrN_owen _ _ x₀ s _)
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ (owenLayout _)).comp_measurePreserving hMP)
    (fun k ω ↦ abs_occErrN_owen_sub_le hP hH x₀ s _ ω) (by norm_num : (0 : ℝ) < 1 / 4) hVM
    (tendsto_ansBoundN_uniform hn s)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hle : (Nat.log 2 (uniformTime n k) : ℝ) ≤ ((n : ℝ) + uniformSpacing n) * k := by
    exact_mod_cast natLog_uniformTime_le hk1
  have hpos : (0 : ℝ) < (n : ℝ) + uniformSpacing n := by positivity
  refine le_trans ?_ hk
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The CLT holds on the uniform chain, digital shift** (`n` not a power of two, any start,
any target), along `T_k = n Σ_{a<k} 2^{ra}`. -/
theorem occErrN_uniform_tendstoInDistribution_shift (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s (uniformTime n k) /
      √Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (shiftFlips ω) s
        (uniformTime n k); shiftMeasure n]) atTop Z (fun _ ↦ shiftMeasure n) P' :=
  tendstoInDistribution_occErrN_shift (isStochastic_uniformChain (by omega))
    (isPoissonFamily_uniform (by omega)) x₀ s (tendsto_uniformTime (by omega))
    (by positivity) (eventually_variance_occErrN_uniform_shift_ge hn2 hnd x₀ s) hZ

/-- **The CLT holds on the uniform chain, Owen's scramble** (`n` not a power of two, any start,
any target), along `T_k = n Σ_{a<k} 2^{ra}`. -/
theorem occErrN_uniform_tendstoInDistribution_owen (hn2 : 2 ≤ n) (hnd : ∀ m, ¬ n ∣ 2 ^ m)
    (x₀ s : Fin n) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s (uniformTime n k) /
      √Var[fun ω ↦ occErrN (uniformChain n) (uniformPi n) x₀ (owenTable ω) s
        (uniformTime n k); owenMeasure n]) atTop Z (fun _ ↦ owenMeasure n) P' :=
  tendstoInDistribution_occErrN_owen (isStochastic_uniformChain (by omega))
    (isPoissonFamily_uniform (by omega)) x₀ s (tendsto_uniformTime (by omega))
    (by positivity) (eventually_variance_occErrN_uniform_owen_ge hn2 hnd x₀ s) hZ

/-! ### Three states (required) and five states -/

/-- `5 ∤ 2^m`. -/
theorem not_five_dvd_two_pow (m : ℕ) : ¬ 5 ∣ 2 ^ m := fun h ↦ by
  have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
  omega

/-- **Non-vacuity on the three-state uniform chain, target `1`, digital shift**:
`Var(N_1(T_k) − T_k/3) ≥ log₂ T_k / 240` eventually, `T_k = 3 Σ_{a<k} 2^{12a}`. -/
theorem eventually_variance_occErrN_example_shift_ge (x₀ : Fin 3) :
    ∀ᶠ k in atTop, 1 / 240 * Nat.log 2 (uniformTime 3 k) ≤
      Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1 (uniformTime 3 k);
        shiftMeasure 3] := by
  have h := eventually_variance_occErrN_uniform_shift_ge (n := 3) (by norm_num)
    not_three_dvd_two_pow x₀ 1
  norm_num [uniformSpacing] at h ⊢
  exact h

/-- **Non-vacuity on the three-state uniform chain, target `1`, Owen's scramble**:
`Var(N_1(T_k) − T_k/3) ≥ log₂ T_k / 240` eventually, `T_k = 3 Σ_{a<k} 2^{12a}`. -/
theorem eventually_variance_occErrN_example_owen_ge (x₀ : Fin 3) :
    ∀ᶠ k in atTop, 1 / 240 * Nat.log 2 (uniformTime 3 k) ≤
      Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1 (uniformTime 3 k);
        owenMeasure 3] := by
  have h := eventually_variance_occErrN_uniform_owen_ge (n := 3) (by norm_num)
    not_three_dvd_two_pow x₀ 1
  norm_num [uniformSpacing] at h ⊢
  exact h

/-- **The CLT on the three-state uniform chain, target `1`, digital shift** (post #3, code (ii)). -/
theorem occErrN_example_tendstoInDistribution_shift (x₀ : Fin 3) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1 (uniformTime 3 k) /
      √Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (shiftFlips ω) 1
        (uniformTime 3 k); shiftMeasure 3]) atTop Z (fun _ ↦ shiftMeasure 3) P' :=
  occErrN_uniform_tendstoInDistribution_shift (by norm_num) not_three_dvd_two_pow x₀ 1 hZ

/-- **The CLT on the three-state uniform chain, target `1`, Owen's scramble** (post #3,
code (iii)). -/
theorem occErrN_example_tendstoInDistribution_owen (x₀ : Fin 3) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1 (uniformTime 3 k) /
      √Var[fun ω ↦ occErrN (uniformChain 3) (uniformPi 3) x₀ (owenTable ω) 1
        (uniformTime 3 k); owenMeasure 3]) atTop Z (fun _ ↦ owenMeasure 3) P' :=
  occErrN_uniform_tendstoInDistribution_owen (by norm_num) not_three_dvd_two_pow x₀ 1 hZ

/-- **The CLT on the five-state uniform chain, target `2`, digital shift** (post #3's number of
states, code (ii)). -/
theorem occErrN_five_tendstoInDistribution_shift (x₀ : Fin 5) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 5) (uniformPi 5) x₀ (shiftFlips ω) 2 (uniformTime 5 k) /
      √Var[fun ω ↦ occErrN (uniformChain 5) (uniformPi 5) x₀ (shiftFlips ω) 2
        (uniformTime 5 k); shiftMeasure 5]) atTop Z (fun _ ↦ shiftMeasure 5) P' :=
  occErrN_uniform_tendstoInDistribution_shift (by norm_num) not_five_dvd_two_pow x₀ 2 hZ

/-- **The CLT on the five-state uniform chain, target `2`, Owen's scramble** (post #3's number
of states, code (iii)). -/
theorem occErrN_five_tendstoInDistribution_owen (x₀ : Fin 5) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦
      occErrN (uniformChain 5) (uniformPi 5) x₀ (owenTable ω) 2 (uniformTime 5 k) /
      √Var[fun ω ↦ occErrN (uniformChain 5) (uniformPi 5) x₀ (owenTable ω) 2
        (uniformTime 5 k); owenMeasure 5]) atTop Z (fun _ ↦ owenMeasure 5) P' :=
  occErrN_uniform_tendstoInDistribution_owen (by norm_num) not_five_dvd_two_pow x₀ 2 hZ

end RQMCMarkov.ScrambledStacks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stacks CLT for transition counts, n states (post #3, codes (ii) and (iii))

Post #3 reports "the error in the number of each transition" of the per-state Sobol stacks.
The transition-count error `N_ij(T) − p_ij N_i(T)` is EXACTLY the departure discrepancy of row
`i` for the indicator `1_{j}` (`transCount_sub_eq_departureDiscrepancy`); by Abel summation it is
`segErr(v_i, c_{i,j+1}, 0, N_i(T)) − segErr(v_i, c_{i,j}, 0, N_i(T))`: integer weights `±1` at the
cut points `c_{i,j}`, `c_{i,j+1}` (`transErrN_eq`).

**Reading.** As for the occupation error: along times `T_k → ∞` with
`Var(N_ij(T_k) − p_ij N_i(T_k)) ≥ κ log₂ T_k`, the normalised transition-count error is
asymptotically `N(0,1)`, for the digital shift (`tendstoInDistribution_transErrN_shift`) and,
by a separate proof, for Owen's scramble (`tendstoInDistribution_transErrN_owen`).

**Proof.** Only row `i` is in play: we give the other rows the inert cut point `1` (`rowCut`),
whose level terms vanish, so the main term `Σ_{j'} w_{j'} segErr(v_i, c_{ij'}, 0, ⌊T π_i⌋)` is a
level sum (`transMainN_eq_levelSumN`); the Anscombe step uses only `|N_i(T) − T π_i| = O(log T)`
(`abs_transErrN_sub_transMainN_le`, `O(log log T)`). Then `CltNCoins` (shift layout) or the Owen
relabelling of `CltNOwenTree` (Owen layout of the row cut points), and Slutsky.

**Hypotheses added.** `IsPoissonFamily P H π` (for `|N_i(T) − T π_i| = O(log T)`); the variance
hypothesis along the given times. Non-vacuity is not proved here (the uniform chains of
`CltNExample` treat the occupation error).

## Main results

* `transErrN`, `indicatorFn`, `transErrN_eq`, `transMainN`, `abs_transErrN_sub_transMainN_le`,
  `transBound`, `transBound_le_log`.
* `rowCut`, `transMainN_eq_levelSumN`, `owenLayoutOf`.
* `tendstoInDistribution_transErrN_shift`, `tendstoInDistribution_transErrN_owen`.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {n : ℕ}

/-- The transition-count error `N_ij(T) − p_ij N_i(T)` of the chain driven by the stacks of
`f`. -/
noncomputable def transErrN (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : ℝ :=
  (transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) -
    P i j * occCount (stackPath P x₀ (scrambledStack f)) i T

/-- The indicator `1_{j}` of a state. -/
noncomputable def indicatorFn (j : Fin n) : Fin n → ℝ := fun k ↦ if k = j then 1 else 0

/-- **The transition-count error is a weighted sum of local discrepancies of row `i`.** -/
theorem transErrN_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    transErrN P x₀ f i j T = ∑ j' ∈ range (n - 1), cutWeight (indicatorFn j) j' *
      segErr (scrambledVdc (f i)) (cutPoint P i j') 0
        (occCount (stackPath P x₀ (scrambledStack f)) i T) := by
  rw [transErrN, transCount_sub_eq_departureDiscrepancy P _ i j T]
  refine (departureDiscrepancy_stackDrive P (indicatorFn j) (step P) x₀ (scrambledStack f) i
    T).trans ?_
  exact sum_step_sub_eq_sum_segErr hP (indicatorFn j) i (fun k ↦ (scrambledVdc_mem_Icc (f i) k).2) _

/-- The main term of the transition-count error at the deterministic index `⌊T π_i⌋`. -/
noncomputable def transMainN (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : ℝ :=
  ∑ j' ∈ range (n - 1), cutWeight (indicatorFn j) j' *
    segErr (scrambledVdc (f i)) (cutPoint P i j') 0 (chainIdxN pi T i)

/-- The Anscombe bound `W (2⌊log₂ (A (⌊log₂ T⌋ + 1))⌋ + 3)` for transitions. -/
noncomputable def transBound (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) : ℝ :=
  cutWeightSum (indicatorFn j) * (2 * (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) + 3)

/-- **Deterministic Anscombe theorem for transition counts** (every flip table). -/
theorem abs_transErrN_sub_transMainN_le {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ : Fin n)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) :
    |transErrN P x₀ f i j T - transMainN P pi f i j T| ≤ transBound H j T := by
  rw [transErrN_eq hP x₀ f i j T, transMainN, ← sum_sub_distrib, transBound, cutWeightSum,
    sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j' _ ↦ ?_)
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hc := cutPoint_mem_Icc hP i j'
  refine (abs_segErr_sub_segErr_le (f i) hc.1 hc.2 _ _).trans ?_
  have hpi := hH.mem_Icc hP i
  have hfl : |T * pi i - (chainIdxN pi T i : ℝ)| < 1 := by
    have hy : 0 ≤ (T : ℝ) * pi i := mul_nonneg (Nat.cast_nonneg T) hpi.1
    rw [chainIdxN, abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy))]
    linarith [Nat.lt_floor_add_one ((T : ℝ) * pi i)]
  have hd := natLog_dist_le (abs_occCount_sub_pi_le hP hH x₀ f i T) hfl
  have hd' : (Nat.log 2 (occCount (stackPath P x₀ (scrambledStack f)) i T - chainIdxN pi T i +
      (chainIdxN pi T i - occCount (stackPath P x₀ (scrambledStack f)) i T)) : ℝ) ≤
      Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) := by exact_mod_cast hd
  linarith

/-- `0 ≤ transBound`. -/
theorem transBound_nonneg (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) : 0 ≤ transBound H j T := by
  have := cutWeightSum_nonneg (indicatorFn j)
  rw [transBound]
  positivity

/-- **The transition Anscombe bound is `O(log log T)`.** -/
theorem transBound_le_log (H : Fin n → Fin n → ℝ) (j : Fin n) (T : ℕ) :
    transBound H j T ≤ cutWeightSum (indicatorFn j) * (2 * Nat.log 2 (anscConstN H) + 5) *
      ((Nat.log 2 (Nat.log 2 T + 1) : ℝ) + 1) := by
  have hmul : (Nat.log 2 (anscConstN H * (Nat.log 2 T + 1)) : ℝ) ≤
      Nat.log 2 (anscConstN H) + Nat.log 2 (Nat.log 2 T + 1) + 1 := by
    exact_mod_cast natLog_mul_le _ _
  have hW := cutWeightSum_nonneg (indicatorFn j)
  have h0 := (Nat.log 2 (anscConstN H)).cast_nonneg (α := ℝ)
  have h1 := (Nat.log 2 (Nat.log 2 T + 1)).cast_nonneg (α := ℝ)
  rw [transBound, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hW
  nlinarith

/-- Row-restricted cut points: those of row `i`, and the inert cut point `1` in other rows. -/
noncomputable def rowCut (P : Fin n → Fin n → ℝ) (i : Fin n) : Fin n → ℕ → ℝ :=
  fun i' j' ↦ if i' = i then cutPoint P i' j' else 1

/-- Row-restricted cut points are nonnegative. -/
theorem rowCut_nonneg {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (i i' : Fin n) (j' : ℕ) :
    0 ≤ rowCut P i i' j' := by
  unfold rowCut
  split_ifs
  · exact (cutPoint_mem_Icc hP i' j').1
  · norm_num

/-- **Level decomposition of the transition main term** (every flip table). -/
theorem transMainN_eq_levelSumN {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (pi : Fin n → ℝ)
    (f : Fin n → ℕ → ℕ → Bool) (i j : Fin n) (T : ℕ) {K : ℕ}
    (hK : ∀ i', chainIdxN pi T i' < 2 ^ K) :
    transMainN P pi f i j T = levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) K
      (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) := by
  have hrow : ∀ m, ∑ i', rowTerm (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) m
      (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) i' =
      rowTerm (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) m
        (fun i' j' ↦ pathCoin (f i') (threshDigit (rowCut P i i' j'))) i := by
    intro m
    refine sum_eq_single i (fun i' _ hne ↦ sum_eq_zero fun j' _ ↦ ?_)
      (fun h ↦ absurd (mem_univ i) h)
    simp only [cutTerm, rowCut, hne, ite_false, lt_irrefl, mul_zero]
  rw [levelSumN, sum_congr rfl fun m _ ↦ hrow m, transMainN]
  simp only [rowTerm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j' _ ↦ ?_
  have hc := cutPoint_mem_Icc hP i j'
  rw [segErr_scrambledVdc_eq_sum_cutTerm (f i) hc.1 hc.2 (hK i), mul_sum]
  simp only [rowCut, ite_true]

/-- The transition main term under the digital shift. -/
noncomputable def shiftTransMain (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (i j : Fin n) (T : ℕ)
    (ω : Fin n × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (shiftLayout n) ω)

/-- The transition-count error is bounded: `|N_ij − p_ij N_i| ≤ T + |p_ij| T`. -/
theorem abs_transErrN_le (P : Fin n → Fin n → ℝ) (x₀ : Fin n) (f : Fin n → ℕ → ℕ → Bool)
    (i j : Fin n) (T : ℕ) : |transErrN P x₀ f i j T| ≤ T + |P i j| * T := by
  rw [transErrN]
  refine (abs_sub _ _).trans ?_
  rw [Nat.abs_cast, abs_mul, Nat.abs_cast]
  have h1 : (transCount (stackPath P x₀ (scrambledStack f)) i j T : ℝ) ≤ T := by
    exact_mod_cast (transCount_le_occCount _ i j T).trans (occCount_le _ i T)
  have h2 : (occCount (stackPath P x₀ (scrambledStack f)) i T : ℝ) ≤ T := by
    exact_mod_cast occCount_le _ i T
  nlinarith [abs_nonneg (P i j)]

/-- **The transition-count CLT, digital shift** (post #3, code (ii), n states): along `T_k → ∞`
with `Var(N_ij(T_k) − p_ij N_i(T_k)) ≥ κ log₂ T_k`, the normalised error is asymptotically
`N(0,1)`. -/
theorem tendstoInDistribution_transErrN_shift {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ i j : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k); shiftMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k) /
      √Var[fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k); shiftMeasure n]) atTop Z
      (fun _ ↦ shiftMeasure n) P' := by
  have hcp := rowCut_nonneg hP i
  have hγ : ∀ i j, Function.Injective (shiftLayout n i j) := fun i j d d' h ↦
    congrArg Prod.snd h
  have hE : ∀ k, MemLp (fun ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k)) 2 (shiftMeasure n) := by
    intro k
    have hm : Measurable fun ω : Fin n × ℕ → Bool ↦ transErrN P x₀ (shiftFlips ω) i j (T k) :=
      ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_transCount_of
        (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ i j (T k))).sub
        (((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
        (fun i k ↦ measurable_scrambledStack_shift i k) P x₀ i (T k))).const_mul _)
    exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_transErrN_le P x₀ _ i j (T k))
  have hclose : ∀ k ω, |transErrN P x₀ (shiftFlips ω) i j (T k) -
      shiftTransMain P pi i j (T k) ω| ≤ transBound H j (T k) := by
    intro k ω
    have e : shiftTransMain P pi i j (T k) ω = transMainN P pi (shiftFlips ω) i j (T k) :=
      (transMainN_eq_levelSumN hP pi (shiftFlips ω) i j (T k)
        (chainIdxN_lt_two_pow hP hH (T k))).symm
    rw [e]
    exact abs_transErrN_sub_transMainN_le hP hH x₀ (shiftFlips ω) i j (T k)
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ transErrN P x₀ (shiftFlips ω) i j (T k))
    (M := fun k ω ↦ shiftTransMain P pi i j (T k) ω) hT (b := fun k ↦ transBound H j (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ transBound_nonneg H j (T k))
      (fun k ↦ transBound_le_log H j (T k))) hE
    (fun k ↦ memLp_levelSumN_coins hcp _ _ (shiftLayout n))
    (fun k ↦ integral_levelSumN_coins hcp _ _ hγ) hclose hκ hvar ?_
  intro κ' hκ' hv
  exact tendstoInDistribution_levelSumN Prod.snd (γ := shiftLayout n) (fun i j d ↦ rfl) hcp
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv hZ

/-- The Owen coin layout of arbitrary cut points `cp`. -/
noncomputable def owenLayoutOf (cp : Fin n → ℕ → ℝ) : Fin n → ℕ → ℕ → Fin n × ℕ × ℕ :=
  fun i j d ↦ (i, d, ⌊2 ^ d * cp i j⌋₊)

/-- The transition main term under Owen's scramble, at relabelled flips `ω'`. -/
noncomputable def owenTransMain (P : Fin n → Fin n → ℝ) (pi : Fin n → ℝ) (i j : Fin n) (T : ℕ)
    (ω' : Fin n × ℕ × ℕ → Bool) : ℝ :=
  levelSumN (cutWeight (indicatorFn j)) (rowCut P i) (chainIdxN pi T) (Nat.log 2 T + 1)
    (coinsOf (owenLayoutOf (rowCut P i)) ω')

/-- **The transition-count CLT, Owen's scramble** (post #3, code (iii), n states), a separate
proof through the relabelling by the scrambled tree. -/
theorem tendstoInDistribution_transErrN_owen {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {H : Fin n → Fin n → ℝ} {pi : Fin n → ℝ} (hH : IsPoissonFamily P H pi) (x₀ i j : Fin n)
    {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hvar : ∀ᶠ k in atTop,
      κ * Nat.log 2 (T k) ≤ Var[fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k); owenMeasure n])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ transErrN P x₀ (owenTable ω) i j (T k) /
      √Var[fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k); owenMeasure n]) atTop Z
      (fun _ ↦ owenMeasure n) P' := by
  have hcp := rowCut_nonneg hP i
  have hγ : ∀ i' j', Function.Injective (owenLayoutOf (rowCut P i) i' j') := fun i' j' d d' h ↦
    congrArg (fun q : Fin n × ℕ × ℕ ↦ q.2.1) h
  have hMP := measurePreserving_owenRelabel (n := n)
  set G : ℕ → (Fin n × ℕ × ℕ → Bool) → ℝ := fun k ω' ↦ owenTransMain P pi i j (T k) ω' with hG
  have hGm : ∀ k, Measurable (G k) := fun k ↦
    measurable_levelSumN_coins (w := cutWeight (indicatorFn j)) hcp _ _ _
  have hvarG : ∀ k, Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n] =
      Var[G k; owenMeasure n] := fun k ↦ hMP.variance_fun_comp (hGm k).aemeasurable
  have hE : ∀ k, MemLp (fun ω ↦ transErrN P x₀ (owenTable ω) i j (T k)) 2 (owenMeasure n) := by
    intro k
    have hm : Measurable fun ω : Fin n × ℕ × ℕ → Bool ↦ transErrN P x₀ (owenTable ω) i j (T k) :=
      ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_transCount_of
        (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ i j (T k))).sub
        (((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_occCount_of
        (fun i k ↦ measurable_scrambledStack_owen i k) P x₀ i (T k))).const_mul _)
    exact MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact abs_transErrN_le P x₀ _ i j (T k))
  have hclose : ∀ k ω, |transErrN P x₀ (owenTable ω) i j (T k) - G k (owenRelabel ω)| ≤
      transBound H j (T k) := by
    intro k ω
    have e : G k (owenRelabel ω) = transMainN P pi (owenTable ω) i j (T k) := by
      rw [transMainN_eq_levelSumN hP pi (owenTable ω) i j (T k)
        (chainIdxN_lt_two_pow hP hH (T k))]
      refine levelSumN_congr _ _ fun i' j' hc ↦ ?_
      exact (funext fun d ↦ pathCoin_owenTable_eq_relabel ω i' hc d).symm
    rw [e]
    exact abs_transErrN_sub_transMainN_le hP hH x₀ (owenTable ω) i j (T k)
  have hM0 : ∀ k, ∫ ω, G k (owenRelabel ω) ∂(owenMeasure n) = 0 := by
    intro k
    rw [← integral_map measurable_owenRelabel.aemeasurable (hGm k).aestronglyMeasurable,
      hMP.map_eq]
    exact integral_levelSumN_coins hcp _ _ hγ
  refine tendstoInDistribution_of_close_main
    (E := fun k ω ↦ transErrN P x₀ (owenTable ω) i j (T k))
    (M := fun k ω ↦ G k (owenRelabel ω)) hT (b := fun k ↦ transBound H j (T k))
    (tendsto_sq_div_natLog_of_le hT (fun k ↦ transBound_nonneg H j (T k))
      (fun k ↦ transBound_le_log H j (T k))) hE
    (fun k ↦ (memLp_levelSumN_coins hcp _ _ _).comp_measurePreserving hMP) hM0 hclose hκ hvar ?_
  intro κ' hκ' hv
  have hv' : ∀ᶠ k in atTop, κ' * ((Nat.log 2 (T k) + 1 : ℕ) : ℝ) ≤ Var[G k; owenMeasure n] := by
    filter_upwards [hv] with k hk
    rwa [← hvarG k]
  have hclt := tendstoInDistribution_levelSumN (fun q : Fin n × ℕ × ℕ ↦ q.2.1)
    (γ := owenLayoutOf (rowCut P i)) (fun i j d ↦ rfl) hcp (w := cutWeight (indicatorFn j))
    (N := fun k ↦ chainIdxN pi (T k)) (K := fun k ↦ Nat.log 2 (T k) + 1)
    (tendsto_natLog_add_one hT) hκ' hv' hZ
  have htr := TendstoInDistribution.comp_measurePreserving hMP hclt
  have e : (fun k ω ↦ G k (owenRelabel ω) / √Var[fun ω ↦ G k (owenRelabel ω); owenMeasure n]) =
      fun k ω ↦ G k (owenRelabel ω) / √Var[G k; owenMeasure n] := by
    funext k ω
    rw [hvarG k]
  rw [e]
  exact htr

end RQMCMarkov.ScrambledStacks

set_option linter.style.longLine false
#print axioms RQMCMarkov.ScrambledStacks.uniformIco
#print axioms RQMCMarkov.ScrambledStacks.isProbabilityMeasure_uniformIco
#print axioms RQMCMarkov.ScrambledStacks.uniformCube
#print axioms RQMCMarkov.ScrambledStacks.isProbabilityMeasure_uniformCube
#print axioms RQMCMarkov.ScrambledStacks.sampleMean
#print axioms RQMCMarkov.ScrambledStacks.map_le_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.integrable_map_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.memLp_map_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.variance_sampleMean_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.variance_sampleMean_le_of_sum_map_eq
#print axioms RQMCMarkov.ScrambledStacks.sum_map_eq_of_hasLaw
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_iid
#print axioms RQMCMarkov.ScrambledStacks.variance_sampleMean_iid
#print axioms RQMCMarkov.ScrambledStacks.rmse_sampleMean_iid
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_sampleMean_iid
#print axioms RQMCMarkov.ScrambledStacks.measure_all_draws_lt_tenth
#print axioms RQMCMarkov.ScrambledStacks.measure_all_draws_lt_tenth_pos
#print axioms RQMCMarkov.ScrambledStacks.measure_sampleMean_far_pos
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_of_hasLaw_uniformCube
#print axioms RQMCMarkov.ScrambledStacks.uniformIco_eq_restrict_Ioc
#print axioms RQMCMarkov.ScrambledStacks.map_fract_restrict_Ioc
#print axioms RQMCMarkov.ScrambledStacks.measurePreserving_fract_add
#print axioms RQMCMarkov.ScrambledStacks.shiftMod1
#print axioms RQMCMarkov.ScrambledStacks.shiftMod1_mem_cube
#print axioms RQMCMarkov.ScrambledStacks.measurePreserving_shiftMod1
#print axioms RQMCMarkov.ScrambledStacks.hasLaw_shiftMod1
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_shiftMod1
#print axioms RQMCMarkov.ScrambledStacks.stratum
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_stratum
#print axioms RQMCMarkov.ScrambledStacks.stratumMap
#print axioms RQMCMarkov.ScrambledStacks.measurable_stratumMap
#print axioms RQMCMarkov.ScrambledStacks.stratumMap_preimage_stratum
#print axioms RQMCMarkov.ScrambledStacks.map_stratumMap_uniformIco
#print axioms RQMCMarkov.ScrambledStacks.iUnion_stratum
#print axioms RQMCMarkov.ScrambledStacks.pairwise_disjoint_stratum
#print axioms RQMCMarkov.ScrambledStacks.sum_map_stratumMap
#print axioms RQMCMarkov.ScrambledStacks.sum_map_stratified
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_stratified
#print axioms RQMCMarkov.ScrambledStacks.not_hasLaw_stratumMap
#print axioms RQMCMarkov.ScrambledStacks.sum_map_eq_of_integral_sampleMean_indicator
#print axioms RQMCMarkov.ScrambledStacks.sampleMean_const_points
#print axioms RQMCMarkov.ScrambledStacks.integral_sampleMean_of_hasLaw_const
#print axioms RQMCMarkov.ScrambledStacks.variance_sampleMean_const
#print axioms RQMCMarkov.ScrambledStacks.IsStochastic
#print axioms RQMCMarkov.ScrambledStacks.IsStochastic.mk
#print axioms RQMCMarkov.ScrambledStacks.IsStochastic.nonneg
#print axioms RQMCMarkov.ScrambledStacks.IsStochastic.sum_eq_one
#print axioms RQMCMarkov.ScrambledStacks.cumProb
#print axioms RQMCMarkov.ScrambledStacks.lastState
#print axioms RQMCMarkov.ScrambledStacks.step
#print axioms RQMCMarkov.ScrambledStacks.cumProb_zero
#print axioms RQMCMarkov.ScrambledStacks.cumProb_succ
#print axioms RQMCMarkov.ScrambledStacks.cumProb_of_le
#print axioms RQMCMarkov.ScrambledStacks.cumProb_mono
#print axioms RQMCMarkov.ScrambledStacks.cumProb_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.step_eq_iff
#print axioms RQMCMarkov.ScrambledStacks.step_mono
#print axioms RQMCMarkov.ScrambledStacks.step_zero
#print axioms RQMCMarkov.ScrambledStacks.measurable_step
#print axioms RQMCMarkov.ScrambledStacks.step_preimage_inter_Ioc
#print axioms RQMCMarkov.ScrambledStacks.uniformIco_step_eq
#print axioms RQMCMarkov.ScrambledStacks.volume_step_eq
#print axioms RQMCMarkov.ScrambledStacks.step_post3_example
#print axioms RQMCMarkov.ScrambledStacks.drive
#print axioms RQMCMarkov.ScrambledStacks.drivenPath
#print axioms RQMCMarkov.ScrambledStacks.drive_zero
#print axioms RQMCMarkov.ScrambledStacks.drive_succ
#print axioms RQMCMarkov.ScrambledStacks.drive_eq_iff
#print axioms RQMCMarkov.ScrambledStacks.occCount
#print axioms RQMCMarkov.ScrambledStacks.transCount
#print axioms RQMCMarkov.ScrambledStacks.occCount_zero
#print axioms RQMCMarkov.ScrambledStacks.transCount_zero
#print axioms RQMCMarkov.ScrambledStacks.occCount_succ
#print axioms RQMCMarkov.ScrambledStacks.transCount_succ
#print axioms RQMCMarkov.ScrambledStacks.occCount_le
#print axioms RQMCMarkov.ScrambledStacks.occCount_mono
#print axioms RQMCMarkov.ScrambledStacks.transCount_le_occCount
#print axioms RQMCMarkov.ScrambledStacks.occCount_congr
#print axioms RQMCMarkov.ScrambledStacks.transCount_congr
#print axioms RQMCMarkov.ScrambledStacks.occCount_add
#print axioms RQMCMarkov.ScrambledStacks.transCount_add
#print axioms RQMCMarkov.ScrambledStacks.departureIndex
#print axioms RQMCMarkov.ScrambledStacks.departureIndex_congr
#print axioms RQMCMarkov.ScrambledStacks.departureIndex_lt
#print axioms RQMCMarkov.ScrambledStacks.departureIndex_injective
#print axioms RQMCMarkov.ScrambledStacks.stackState
#print axioms RQMCMarkov.ScrambledStacks.stackDrive
#print axioms RQMCMarkov.ScrambledStacks.stackPath
#print axioms RQMCMarkov.ScrambledStacks.stackState_snd
#print axioms RQMCMarkov.ScrambledStacks.stackDrive_zero
#print axioms RQMCMarkov.ScrambledStacks.stackDrive_succ
#print axioms RQMCMarkov.ScrambledStacks.stackDrive_eq_iff
#print axioms RQMCMarkov.ScrambledStacks.IsSpellStart
#print axioms RQMCMarkov.ScrambledStacks.runLength
#print axioms RQMCMarkov.ScrambledStacks.spellCount
#print axioms RQMCMarkov.ScrambledStacks.runLength_eq_of_exit
#print axioms RQMCMarkov.ScrambledStacks.runLength_eq_iff
#print axioms RQMCMarkov.ScrambledStacks.spellCount_succ
#print axioms RQMCMarkov.ScrambledStacks.sum_occCount
#print axioms RQMCMarkov.ScrambledStacks.sum_transCount_right
#print axioms RQMCMarkov.ScrambledStacks.sum_transCount_left
#print axioms RQMCMarkov.ScrambledStacks.flowBalance
#print axioms RQMCMarkov.ScrambledStacks.abs_flowBalance_le
#print axioms RQMCMarkov.ScrambledStacks.sum_sum_transCount
#print axioms RQMCMarkov.ScrambledStacks.spellCount_succ_eq
#print axioms RQMCMarkov.ScrambledStacks.departureDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.sum_sub_eq_boundary_add
#print axioms RQMCMarkov.ScrambledStacks.sum_indicator_eq_occCount
#print axioms RQMCMarkov.ScrambledStacks.occCount_sub_eq_boundary_add
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_sub_le
#print axioms RQMCMarkov.ScrambledStacks.mulVec_indicator
#print axioms RQMCMarkov.ScrambledStacks.transCount_sub_eq_departureDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_sub_le
#print axioms RQMCMarkov.ScrambledStacks.sum_filter_occCount_eq
#print axioms RQMCMarkov.ScrambledStacks.stackDrive_succ_of_eq
#print axioms RQMCMarkov.ScrambledStacks.departureDiscrepancy_stackDrive
#print axioms RQMCMarkov.ScrambledStacks.transCount_stackDrive
#print axioms RQMCMarkov.ScrambledStacks.InUnitIco
#print axioms RQMCMarkov.ScrambledStacks.countBelow
#print axioms RQMCMarkov.ScrambledStacks.countAtMost
#print axioms RQMCMarkov.ScrambledStacks.localDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.qmcEstimate
#print axioms RQMCMarkov.ScrambledStacks.midpointRule
#print axioms RQMCMarkov.ScrambledStacks.countBelow_le
#print axioms RQMCMarkov.ScrambledStacks.countBelow_mono
#print axioms RQMCMarkov.ScrambledStacks.countBelow_div_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.localDiscrepancy_le_one
#print axioms RQMCMarkov.ScrambledStacks.localDiscrepancy_eq_abs_div
#print axioms RQMCMarkov.ScrambledStacks.bddAbove_localDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.localDiscrepancy_le_starDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_le_of_forall
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_nonneg
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_le_one
#print axioms RQMCMarkov.ScrambledStacks.countAtMost_div_sub_le_starDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.inv_two_mul_le_starDiscrepancy
#print axioms RQMCMarkov.ScrambledStacks.midpointRule_mem
#print axioms RQMCMarkov.ScrambledStacks.midpointRule_lt_iff
#print axioms RQMCMarkov.ScrambledStacks.countBelow_midpointRule_le
#print axioms RQMCMarkov.ScrambledStacks.le_countBelow_midpointRule
#print axioms RQMCMarkov.ScrambledStacks.abs_countBelow_midpointRule_sub_le
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_midpointRule
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_midpointRule_le
#print axioms RQMCMarkov.ScrambledStacks.midpointRule_three
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_midpointRule_three
#print axioms RQMCMarkov.ScrambledStacks.totalVariation
#print axioms RQMCMarkov.ScrambledStacks.countBelow_eq_sum_indicator
#print axioms RQMCMarkov.ScrambledStacks.countAtMost_eq_sum_indicator
#print axioms RQMCMarkov.ScrambledStacks.countAtMost_le
#print axioms RQMCMarkov.ScrambledStacks.countAtMost_div_sub_le_starDiscrepancy_of_mem
#print axioms RQMCMarkov.ScrambledStacks.indicator_one_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_indicator_upperSet_sub_le
#print axioms RQMCMarkov.ScrambledStacks.antitone_indicator_Iic
#print axioms RQMCMarkov.ScrambledStacks.integral_indicator_Iic_one
#print axioms RQMCMarkov.ScrambledStacks.sum_div_eq_integral_indicator
#print axioms RQMCMarkov.ScrambledStacks.integral_sub_eq_integral_measureReal
#print axioms RQMCMarkov.ScrambledStacks.koksma_monotone
#print axioms RQMCMarkov.ScrambledStacks.monotone_comp_projIcc
#print axioms RQMCMarkov.ScrambledStacks.comp_projIcc_eq
#print axioms RQMCMarkov.ScrambledStacks.qmcError_congr
#print axioms RQMCMarkov.ScrambledStacks.koksma_monotoneOn
#print axioms RQMCMarkov.ScrambledStacks.koksma_sub_monotoneOn
#print axioms RQMCMarkov.ScrambledStacks.koksma_boundedVariationOn
#print axioms RQMCMarkov.ScrambledStacks.koksma_hasDerivAt
#print axioms RQMCMarkov.ScrambledStacks.eVariationOn_le_integral_abs_deriv
#print axioms RQMCMarkov.ScrambledStacks.boundedVariationOn_of_hasDerivAt
#print axioms RQMCMarkov.ScrambledStacks.totalVariation_le_integral_abs_deriv
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput_eq
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput_two_mul_add
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput_one_two_three
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput_mem_Ico
#print axioms RQMCMarkov.ScrambledStacks.vanDerCorput_inUnitIco
#print axioms RQMCMarkov.ScrambledStacks.floor_two_pow_mul_vanDerCorput_lt
#print axioms RQMCMarkov.ScrambledStacks.floor_two_pow_succ_mul_vanDerCorput
#print axioms RQMCMarkov.ScrambledStacks.mod_eq_of_floor_vanDerCorput_eq
#print axioms RQMCMarkov.ScrambledStacks.floor_vanDerCorput_injOn
#print axioms RQMCMarkov.ScrambledStacks.mem_dyadic_iff_floor
#print axioms RQMCMarkov.ScrambledStacks.card_vanDerCorput_mem_dyadic
#print axioms RQMCMarkov.ScrambledStacks.card_vanDerCorput_mem_dyadic_aligned
#print axioms RQMCMarkov.ScrambledStacks.abs_card_block_vanDerCorput_sub_le
#print axioms RQMCMarkov.ScrambledStacks.countBelow_add
#print axioms RQMCMarkov.ScrambledStacks.abs_countBelow_vanDerCorput_sub_le
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_vanDerCorput_le
#print axioms RQMCMarkov.ScrambledStacks.natLog_two_add_one_le
#print axioms RQMCMarkov.ScrambledStacks.starDiscrepancy_vanDerCorput_le_log
#print axioms RQMCMarkov.ScrambledStacks.abs_qmcError_vanDerCorput_le
#print axioms RQMCMarkov.ScrambledStacks.tendsto_log_add_one_div_sqrt
#print axioms RQMCMarkov.ScrambledStacks.tendsto_sqrt_mul_vanDerCorput_bound
#print axioms RQMCMarkov.ScrambledStacks.tendsto_sqrt_mul_qmcError_vanDerCorput
#print axioms RQMCMarkov.ScrambledStacks.step_lt_iff
#print axioms RQMCMarkov.ScrambledStacks.departuresBelow
#print axioms RQMCMarkov.ScrambledStacks.departuresBelow_eq_countAtMost
#print axioms RQMCMarkov.ScrambledStacks.abs_departuresBelow_sub_le
#print axioms RQMCMarkov.ScrambledStacks.card_step_eq_eq_sub
#print axioms RQMCMarkov.ScrambledStacks.abs_card_step_eq_sub_le
#print axioms RQMCMarkov.ScrambledStacks.extendNat
#print axioms RQMCMarkov.ScrambledStacks.stateVariation
#print axioms RQMCMarkov.ScrambledStacks.stateVariation_nonneg
#print axioms RQMCMarkov.ScrambledStacks.stateVariation_le
#print axioms RQMCMarkov.ScrambledStacks.sum_mul_sub_eq_abel
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_step_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_stackPath_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_departureDiscrepancy_stackPath_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_stackPath_sub_le
#print axioms RQMCMarkov.ScrambledStacks.mul_starDiscrepancy_vdc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_vdc_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_vdc_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occFreq_vdc_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_empiricalTrans_vdc_sub_le
#print axioms RQMCMarkov.ScrambledStacks.one_le_log_of_three_le
#print axioms RQMCMarkov.ScrambledStacks.isBigO_log_div_of_le
#print axioms RQMCMarkov.ScrambledStacks.occFreq_vdc_isBigO
#print axioms RQMCMarkov.ScrambledStacks.empiricalTrans_vdc_isBigO
#print axioms RQMCMarkov.ScrambledStacks.binaryVal
#print axioms RQMCMarkov.ScrambledStacks.digitTerm_le
#print axioms RQMCMarkov.ScrambledStacks.digitTerm_nonneg
#print axioms RQMCMarkov.ScrambledStacks.summable_digitTerm
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_nonneg
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_one
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_pos
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_lt_one
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_lt
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_congr
#print axioms RQMCMarkov.ScrambledStacks.eq_of_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_eq_iff
#print axioms RQMCMarkov.ScrambledStacks.sum_digitTerm_eq_digitPrefix
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_eq_digitPrefix_add
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_div_le_binaryVal
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_digitPrefix_add_one_div
#print axioms RQMCMarkov.ScrambledStacks.NotEventuallyConst
#print axioms RQMCMarkov.ScrambledStacks.NotEventuallyConst.shift
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_div_lt_binaryVal
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_lt_digitPrefix_add_one_div
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_ne_dyadic
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_eq_tsum
#print axioms RQMCMarkov.ScrambledStacks.shiftTable
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit_shiftTable
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.scrambledStack
#print axioms RQMCMarkov.ScrambledStacks.scrambledStack_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.IsGoodTable
#print axioms RQMCMarkov.ScrambledStacks.scrambledStack_ne_dyadic
#print axioms RQMCMarkov.ScrambledStacks.scrambledStack_mem_Ioo
#print axioms RQMCMarkov.ScrambledStacks.fairCoin
#print axioms RQMCMarkov.ScrambledStacks.fairCoin_singleton
#print axioms RQMCMarkov.ScrambledStacks.owenMeasure
#print axioms RQMCMarkov.ScrambledStacks.owenTable
#print axioms RQMCMarkov.ScrambledStacks.shiftMeasure
#print axioms RQMCMarkov.ScrambledStacks.shiftFlips
#print axioms RQMCMarkov.ScrambledStacks.isProbabilityMeasure_owenMeasure
#print axioms RQMCMarkov.ScrambledStacks.isProbabilityMeasure_shiftMeasure
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit_owenTable
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit_shiftFlips
#print axioms RQMCMarkov.ScrambledStacks.infinitePi_setOf_forall_mem'
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_xor_cylinder
#print axioms RQMCMarkov.ScrambledStacks.infinitePi_xor_cylinder
#print axioms RQMCMarkov.ScrambledStacks.setOf_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.measure_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.measure_digitPrefix_lt
#print axioms RQMCMarkov.ScrambledStacks.measurable_digitPrefix
#print axioms RQMCMarkov.ScrambledStacks.measurable_binaryVal
#print axioms RQMCMarkov.ScrambledStacks.measurable_xor_digits
#print axioms RQMCMarkov.ScrambledStacks.map_binaryVal_xor_eq_uniformIco
#print axioms RQMCMarkov.ScrambledStacks.owen_coord_injective
#print axioms RQMCMarkov.ScrambledStacks.shift_coord_injective
#print axioms RQMCMarkov.ScrambledStacks.map_scrambledStack_owen
#print axioms RQMCMarkov.ScrambledStacks.map_scrambledStack_shift
#print axioms RQMCMarkov.ScrambledStacks.owen_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.shift_digitPrefix_eq
#print axioms RQMCMarkov.ScrambledStacks.measurable_scrambledStack_owen
#print axioms RQMCMarkov.ScrambledStacks.measurable_scrambledStack_shift
#print axioms RQMCMarkov.ScrambledStacks.ae_notEventuallyConst_xor
#print axioms RQMCMarkov.ScrambledStacks.ae_isGoodTable_owen
#print axioms RQMCMarkov.ScrambledStacks.ae_isGoodTable_shift
#print axioms RQMCMarkov.ScrambledStacks.measurable_stackPath_restrict_of
#print axioms RQMCMarkov.ScrambledStacks.measurable_comp_stackPath_of
#print axioms RQMCMarkov.ScrambledStacks.measurable_stackPath_of
#print axioms RQMCMarkov.ScrambledStacks.measurable_occCount_of
#print axioms RQMCMarkov.ScrambledStacks.measurable_transCount_of
#print axioms RQMCMarkov.ScrambledStacks.segErr
#print axioms RQMCMarkov.ScrambledStacks.segErr_zero
#print axioms RQMCMarkov.ScrambledStacks.segErr_add
#print axioms RQMCMarkov.ScrambledStacks.segErr_eq_card
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_prefix_le
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_le_of_block
#print axioms RQMCMarkov.ScrambledStacks.mod_two_pow_eq_of_testBit_eq
#print axioms RQMCMarkov.ScrambledStacks.testBit_eq_of_scrambledDigit_eq
#print axioms RQMCMarkov.ScrambledStacks.mod_eq_of_digitPrefix_scrambledDigit_eq
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_scrambledDigit_mod
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_scrambledDigit_block
#print axioms RQMCMarkov.ScrambledStacks.injOn_digitPrefix_scrambledDigit
#print axioms RQMCMarkov.ScrambledStacks.image_digitPrefix_scrambledDigit_block
#print axioms RQMCMarkov.ScrambledStacks.card_filter_digitPrefix_block
#print axioms RQMCMarkov.ScrambledStacks.card_filter_lt_range
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_scrambledVdc_block_le
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_scrambledVdc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_scrambledVdc_log_le
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_scrambledVdc_zero_le
#print axioms RQMCMarkov.ScrambledStacks.card_filter_step_eq_eq_sub
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_step_sub_le_of_count
#print axioms RQMCMarkov.ScrambledStacks.card_filter_segment_sub_eq_segErr
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_step_scrambledVdc_segment_le
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_step_scrambledVdc_segment_log_le
#print axioms RQMCMarkov.ScrambledStacks.abs_sum_step_scrambledVdc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_departuresBelow_scrambledVdc_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_scrambled_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_departureDiscrepancy_scrambled_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_scrambled_sub_le
#print axioms RQMCMarkov.ScrambledStacks.occFreq_scrambled_isBigO
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_owen_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_shift_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_owen_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_shift_sub_le
#print axioms RQMCMarkov.ScrambledStacks.step_two_eq_zero_iff
#print axioms RQMCMarkov.ScrambledStacks.segErr_zero_eq_card
#print axioms RQMCMarkov.ScrambledStacks.abs_two_state_identity
#print axioms RQMCMarkov.ScrambledStacks.piZero
#print axioms RQMCMarkov.ScrambledStacks.piOne
#print axioms RQMCMarkov.ScrambledStacks.occErr
#print axioms RQMCMarkov.ScrambledStacks.mainTerm
#print axioms RQMCMarkov.ScrambledStacks.anscConst
#print axioms RQMCMarkov.ScrambledStacks.anscBound
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_sub_segErr_le
#print axioms RQMCMarkov.ScrambledStacks.piZero_add_piOne
#print axioms RQMCMarkov.ScrambledStacks.abs_occErr_le
#print axioms RQMCMarkov.ScrambledStacks.natLog_dist_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occErr_sub_mainTerm_le
#print axioms RQMCMarkov.ScrambledStacks.AlignedBlockBound
#print axioms RQMCMarkov.ScrambledStacks.AlignedBlockBound.nonneg
#print axioms RQMCMarkov.ScrambledStacks.abs_sub_alignedPrefix_le
#print axioms RQMCMarkov.ScrambledStacks.abs_sub_le_of_le_add_pow
#print axioms RQMCMarkov.ScrambledStacks.abs_sub_le_log
#print axioms RQMCMarkov.ScrambledStacks.abs_sub_le_log_dist
#print axioms RQMCMarkov.ScrambledStacks.abs_sub_zero_le_log
#print axioms RQMCMarkov.ScrambledStacks.card_le_add_frac_eq
#print axioms RQMCMarkov.ScrambledStacks.alignedBlockBound_of_cells
#print axioms RQMCMarkov.ScrambledStacks.norm_prod_sub_prod_le
#print axioms RQMCMarkov.ScrambledStacks.norm_cexp_mul_I_sub_le
#print axioms RQMCMarkov.ScrambledStacks.norm_charFun_sub_le_of_abs_le
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_sum_of_bounded
#print axioms RQMCMarkov.ScrambledStacks.IsLocal
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.mono
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.comp
#print axioms RQMCMarkov.ScrambledStacks.isLocal_const
#print axioms RQMCMarkov.ScrambledStacks.isLocal_sum
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.add
#print axioms RQMCMarkov.ScrambledStacks.localExtend
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.eq_restrict
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.measurable
#print axioms RQMCMarkov.ScrambledStacks.IsLocal.indepFun
#print axioms RQMCMarkov.ScrambledStacks.charFun_map_sum_range_eq_prod
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_sum_range_of_bounded
#print axioms RQMCMarkov.ScrambledStacks.tendstoInMeasure_of_integral_sq
#print axioms RQMCMarkov.ScrambledStacks.sq_covariance_le
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_le_sqrt
#print axioms RQMCMarkov.ScrambledStacks.sqrt_variance_add_le
#print axioms RQMCMarkov.ScrambledStacks.abs_sqrt_variance_sub_le
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_of_blocks
#print axioms RQMCMarkov.ScrambledStacks.tendsto_natLog_atTop
#print axioms RQMCMarkov.ScrambledStacks.tendsto_natLog_pow_six_div
#print axioms RQMCMarkov.ScrambledStacks.sqrt_variance_sum_le
#print axioms RQMCMarkov.ScrambledStacks.disjoint_of_lev
#print axioms RQMCMarkov.ScrambledStacks.div_mul_le_and_lt
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_of_truncations
#print axioms RQMCMarkov.ScrambledStacks.threshDigit
#print axioms RQMCMarkov.ScrambledStacks.digitPrefix_threshDigit
#print axioms RQMCMarkov.ScrambledStacks.floor_two_pow_succ_mul
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_threshDigit
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_iff_of_firstDiff
#print axioms RQMCMarkov.ScrambledStacks.LexLeFrom
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_iff_lexLeFrom
#print axioms RQMCMarkov.ScrambledStacks.lexLeFrom_congr
#print axioms RQMCMarkov.ScrambledStacks.mod_two_pow_succ_eq
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix
#print axioms RQMCMarkov.ScrambledStacks.pathCoin
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix_lt
#print axioms RQMCMarkov.ScrambledStacks.tie_iff_mod_eq_pathPrefix
#print axioms RQMCMarkov.ScrambledStacks.tie_of_mod
#print axioms RQMCMarkov.ScrambledStacks.two_pow_mul_add_mod
#print axioms RQMCMarkov.ScrambledStacks.card_block_le_eq
#print axioms RQMCMarkov.ScrambledStacks.levelBase
#print axioms RQMCMarkov.ScrambledStacks.levelDigits
#print axioms RQMCMarkov.ScrambledStacks.LevelInd
#print axioms RQMCMarkov.ScrambledStacks.levelVal
#print axioms RQMCMarkov.ScrambledStacks.levelTerm
#print axioms RQMCMarkov.ScrambledStacks.testBit_levelBase_add
#print axioms RQMCMarkov.ScrambledStacks.levelBase_add_mod
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_levelPoint_le_iff
#print axioms RQMCMarkov.ScrambledStacks.levelBase_two_pow_add
#print axioms RQMCMarkov.ScrambledStacks.levelBase_eq_zero
#print axioms RQMCMarkov.ScrambledStacks.segErr_eq_sum_levelPoint
#print axioms RQMCMarkov.ScrambledStacks.segErr_scrambledVdc_eq_sum_level
#print axioms RQMCMarkov.ScrambledStacks.LexLeFromTrunc
#print axioms RQMCMarkov.ScrambledStacks.lexLeFrom_iff_of_firstBreak
#print axioms RQMCMarkov.ScrambledStacks.lexLeFromTrunc_iff_of_firstBreak
#print axioms RQMCMarkov.ScrambledStacks.exists_firstBreak
#print axioms RQMCMarkov.ScrambledStacks.lexLeFrom_iff_trunc
#print axioms RQMCMarkov.ScrambledStacks.LevelIndTrunc
#print axioms RQMCMarkov.ScrambledStacks.levelValTrunc
#print axioms RQMCMarkov.ScrambledStacks.LevelTie
#print axioms RQMCMarkov.ScrambledStacks.levelVal_eq_trunc_of_not_tie
#print axioms RQMCMarkov.ScrambledStacks.levelValTrunc_congr
#print axioms RQMCMarkov.ScrambledStacks.levelInd_iff_binaryVal_le
#print axioms RQMCMarkov.ScrambledStacks.coinPrefix
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix_eq_coinPrefix
#print axioms RQMCMarkov.ScrambledStacks.coinPrefix_congr
#print axioms RQMCMarkov.ScrambledStacks.pathCoin_shiftTable
#print axioms RQMCMarkov.ScrambledStacks.owenPathCoins
#print axioms RQMCMarkov.ScrambledStacks.owenBox
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix_owen_congr
#print axioms RQMCMarkov.ScrambledStacks.owenPathCoins_congr
#print axioms RQMCMarkov.ScrambledStacks.measurable_owenPathCoins
#print axioms RQMCMarkov.ScrambledStacks.infinitePi_inter_of_local
#print axioms RQMCMarkov.ScrambledStacks.owenMeasure_pathCoins_cylinder
#print axioms RQMCMarkov.ScrambledStacks.cylinder_eq_pi
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_cylinder
#print axioms RQMCMarkov.ScrambledStacks.shiftMeasure_cylinder
#print axioms RQMCMarkov.ScrambledStacks.eq_shiftMeasure_of_cylinder
#print axioms RQMCMarkov.ScrambledStacks.map_owenPathCoins
#print axioms RQMCMarkov.ScrambledStacks.covariance_eq_zero_of_approx
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_le_integral_abs
#print axioms RQMCMarkov.ScrambledStacks.variance_sum_ge_of_cov
#print axioms RQMCMarkov.ScrambledStacks.variance_sum_le_of_cov
#print axioms RQMCMarkov.ScrambledStacks.stateCoins
#print axioms RQMCMarkov.ScrambledStacks.fracPow
#print axioms RQMCMarkov.ScrambledStacks.coinTerm
#print axioms RQMCMarkov.ScrambledStacks.coinTermTrunc
#print axioms RQMCMarkov.ScrambledStacks.coinSum
#print axioms RQMCMarkov.ScrambledStacks.fracPow_mem_Ico
#print axioms RQMCMarkov.ScrambledStacks.levelVal_mem
#print axioms RQMCMarkov.ScrambledStacks.levelValTrunc_mem
#print axioms RQMCMarkov.ScrambledStacks.coinTerm_mem
#print axioms RQMCMarkov.ScrambledStacks.abs_coinTerm_le
#print axioms RQMCMarkov.ScrambledStacks.abs_coinTermTrunc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_coinTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.isLocal_coinTermTrunc
#print axioms RQMCMarkov.ScrambledStacks.levelInd_stateCoins_iff
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_levelInd
#print axioms RQMCMarkov.ScrambledStacks.measurable_coinTerm
#print axioms RQMCMarkov.ScrambledStacks.measureReal_levelInd
#print axioms RQMCMarkov.ScrambledStacks.integral_levelVal
#print axioms RQMCMarkov.ScrambledStacks.setOf_levelTie_eq
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_levelTie
#print axioms RQMCMarkov.ScrambledStacks.measureReal_levelTie
#print axioms RQMCMarkov.ScrambledStacks.memLp_coinTerm
#print axioms RQMCMarkov.ScrambledStacks.memLp_coinTermTrunc
#print axioms RQMCMarkov.ScrambledStacks.integral_sq_coinTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.tendsto_variance_coinTerm_sub_trunc
#print axioms RQMCMarkov.ScrambledStacks.variance_coinTerm
#print axioms RQMCMarkov.ScrambledStacks.covariance_coinTerm_eq_zero
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_coinTerm_le
#print axioms RQMCMarkov.ScrambledStacks.sum_erase_pow_dist_le
#print axioms RQMCMarkov.ScrambledStacks.coinZ
#print axioms RQMCMarkov.ScrambledStacks.coinSum_eq_sum_coinZ
#print axioms RQMCMarkov.ScrambledStacks.covBound
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_coinZ_le
#print axioms RQMCMarkov.ScrambledStacks.sum_erase_covBound_le
#print axioms RQMCMarkov.ScrambledStacks.memLp_coinZ
#print axioms RQMCMarkov.ScrambledStacks.memLp_coinSum
#print axioms RQMCMarkov.ScrambledStacks.variance_coinSum_le
#print axioms RQMCMarkov.ScrambledStacks.patternN
#print axioms RQMCMarkov.ScrambledStacks.patternN_lt
#print axioms RQMCMarkov.ScrambledStacks.testBit_patternN
#print axioms RQMCMarkov.ScrambledStacks.frac_div_three_mem
#print axioms RQMCMarkov.ScrambledStacks.not_three_dvd_two_pow
#print axioms RQMCMarkov.ScrambledStacks.fracPow_two_thirds_mem
#print axioms RQMCMarkov.ScrambledStacks.fracPow_one_third_mem
#print axioms RQMCMarkov.ScrambledStacks.coinSum_patternN
#print axioms RQMCMarkov.ScrambledStacks.variance_coinSum_pattern_ge
#print axioms RQMCMarkov.ScrambledStacks.integral_coinTerm
#print axioms RQMCMarkov.ScrambledStacks.integral_coinSum
#print axioms RQMCMarkov.ScrambledStacks.chainThresh
#print axioms RQMCMarkov.ScrambledStacks.chainIdx
#print axioms RQMCMarkov.ScrambledStacks.chainDigits
#print axioms RQMCMarkov.ScrambledStacks.sum_segErr_eq_coinSum
#print axioms RQMCMarkov.ScrambledStacks.chainIdx_le
#print axioms RQMCMarkov.ScrambledStacks.chainThresh_mem
#print axioms RQMCMarkov.ScrambledStacks.mul_mainTerm_eq_coinSum
#print axioms RQMCMarkov.ScrambledStacks.owenPathCoins_chainDigits
#print axioms RQMCMarkov.ScrambledStacks.shiftPathCoins_eq
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.mk
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.measurePreserving
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.pathCoin_eq
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.measurable_stack
#print axioms RQMCMarkov.ScrambledStacks.isPathCoinModel_owen
#print axioms RQMCMarkov.ScrambledStacks.isPathCoinModel_shift
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.mainTerm_eq
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.variance_mainTerm
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.integral_mainTerm
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.memLp_mainTerm
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.memLp_occErr
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.abs_sqrt_variance_occErr_sub_le
#print axioms RQMCMarkov.ScrambledStacks.exampleChain
#print axioms RQMCMarkov.ScrambledStacks.isStochastic_exampleChain
#print axioms RQMCMarkov.ScrambledStacks.exampleChain_01
#print axioms RQMCMarkov.ScrambledStacks.exampleChain_10
#print axioms RQMCMarkov.ScrambledStacks.exampleChain_11
#print axioms RQMCMarkov.ScrambledStacks.exampleChain_00
#print axioms RQMCMarkov.ScrambledStacks.exampleTime
#print axioms RQMCMarkov.ScrambledStacks.chainIdx_exampleTime
#print axioms RQMCMarkov.ScrambledStacks.fracPow_exampleChain_mem
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.variance_mainTerm_example_ge
#print axioms RQMCMarkov.ScrambledStacks.anscBound_exampleTime_le
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.eventually_variance_occErr_example_ge
#print axioms RQMCMarkov.ScrambledStacks.TendstoInDistribution.comp_measurePreserving
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_coinSum
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_of_abs_sub_le
#print axioms RQMCMarkov.ScrambledStacks.anscBound_le_log
#print axioms RQMCMarkov.ScrambledStacks.tendsto_anscBound_sq_div
#print axioms RQMCMarkov.ScrambledStacks.chainIdx_lt_two_pow
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.tendstoInDistribution_occErr
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_occErr_owen
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_occErr_shift
#print axioms RQMCMarkov.ScrambledStacks.tendsto_exampleTime
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.eventually_variance_example
#print axioms RQMCMarkov.ScrambledStacks.occErr_example_tendstoInDistribution
#print axioms RQMCMarkov.ScrambledStacks.occErr_example_tendstoInDistribution_owen
#print axioms RQMCMarkov.ScrambledStacks.occErr_example_tendstoInDistribution_shift
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.integral_sq_occErr_le
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.isBigO_meanSq_occFreq
#print axioms RQMCMarkov.ScrambledStacks.chainSumErr
#print axioms RQMCMarkov.ScrambledStacks.chainSumErr_eq
#print axioms RQMCMarkov.ScrambledStacks.TendstoInDistribution.of_map_eq
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.tendstoInDistribution_chainSumErr
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_le_iff_lexLeFrom_pathCoin
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_le_iff_shiftTable
#print axioms RQMCMarkov.ScrambledStacks.scrambledVdc_le_congr_pathCoin
#print axioms RQMCMarkov.ScrambledStacks.step_congr_of_le_iff
#print axioms RQMCMarkov.ScrambledStacks.stackDrive_congr_of_forall
#print axioms RQMCMarkov.ScrambledStacks.cumProb_one_eq_two_state
#print axioms RQMCMarkov.ScrambledStacks.cumProb_two_eq_two_state
#print axioms RQMCMarkov.ScrambledStacks.pathShift
#print axioms RQMCMarkov.ScrambledStacks.stackPath_eq_pathShift
#print axioms RQMCMarkov.ScrambledStacks.coinPath
#print axioms RQMCMarkov.ScrambledStacks.measurable_coinPath
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.pathShift_eq
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.stackPath_eq_coinPath
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.measurable_stackPath
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.map_stackPath
#print axioms RQMCMarkov.ScrambledStacks.IsPathCoinModel.identDistrib_stackPath
#print axioms RQMCMarkov.ScrambledStacks.stackPath_owen_eq_coinPath
#print axioms RQMCMarkov.ScrambledStacks.stackPath_shift_eq_coinPath
#print axioms RQMCMarkov.ScrambledStacks.map_stackPath_owen_eq_shift
#print axioms RQMCMarkov.ScrambledStacks.identDistrib_stackPath_owen_shift
#print axioms RQMCMarkov.ScrambledStacks.owenMeasure_stackPath_cylinder
#print axioms RQMCMarkov.ScrambledStacks.identDistrib_comp_stackPath_owen_shift
#print axioms RQMCMarkov.ScrambledStacks.measurable_occCount_path
#print axioms RQMCMarkov.ScrambledStacks.measurable_transCount_path
#print axioms RQMCMarkov.ScrambledStacks.identDistrib_occCount_owen_shift
#print axioms RQMCMarkov.ScrambledStacks.identDistrib_transCount_owen_shift
#print axioms RQMCMarkov.ScrambledStacks.identDistrib_occErr_owen_shift
#print axioms RQMCMarkov.ScrambledStacks.variance_occErr_owen_eq_shift
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_congr_identDistrib
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_occErr_owen_iff_shift
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_normalised_occErr_owen_iff_shift
#print axioms RQMCMarkov.ScrambledStacks.threeChain
#print axioms RQMCMarkov.ScrambledStacks.isStochastic_threeChain
#print axioms RQMCMarkov.ScrambledStacks.threeChain_step_eq_zero_iff
#print axioms RQMCMarkov.ScrambledStacks.threeChain_step_eq_one_iff
#print axioms RQMCMarkov.ScrambledStacks.StayThenMove
#print axioms RQMCMarkov.ScrambledStacks.stayThenMove_iff
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_quarter_iff
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_mem_middle_iff
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit_one
#print axioms RQMCMarkov.ScrambledStacks.scrambledDigit_zero
#print axioms RQMCMarkov.ScrambledStacks.stayThenMove_iff_digits
#print axioms RQMCMarkov.ScrambledStacks.owenMeasure_stayThenMove
#print axioms RQMCMarkov.ScrambledStacks.shiftMeasure_stayThenMove
#print axioms RQMCMarkov.ScrambledStacks.owen_ne_shift_stayThenMove
#print axioms RQMCMarkov.ScrambledStacks.continuous_cdf_of_noAtoms
#print axioms RQMCMarkov.ScrambledStacks.exists_cdf_eq
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_of_card_le
#print axioms RQMCMarkov.ScrambledStacks.exists_eq_ceil_add_of_abs_le
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_of_abs_sub_le
#print axioms RQMCMarkov.ScrambledStacks.segErr_scrambledVdc_block_dyadic
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_scrambledVdc_dyadic_le
#print axioms RQMCMarkov.ScrambledStacks.DyadicCumProb
#print axioms RQMCMarkov.ScrambledStacks.dyadicCumProb_of_entries
#print axioms RQMCMarkov.ScrambledStacks.abs_departuresBelow_dyadic_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_transCount_dyadic_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_departureDiscrepancy_dyadic_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_dyadic_sub_le
#print axioms RQMCMarkov.ScrambledStacks.ae_abs_occCount_dyadic_owen_le
#print axioms RQMCMarkov.ScrambledStacks.ae_abs_occCount_dyadic_shift_le
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_occCount_owen
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_occCount_shift
#print axioms RQMCMarkov.ScrambledStacks.map_id_gaussianReal_singleton
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_occCount_owen_gaussian
#print axioms RQMCMarkov.ScrambledStacks.stackChain78
#print axioms RQMCMarkov.ScrambledStacks.isStochastic_stackChain78
#print axioms RQMCMarkov.ScrambledStacks.dyadicCumProb_stackChain78
#print axioms RQMCMarkov.ScrambledStacks.poisson78
#print axioms RQMCMarkov.ScrambledStacks.poisson78_spec
#print axioms RQMCMarkov.ScrambledStacks.abs_poisson78_le
#print axioms RQMCMarkov.ScrambledStacks.stateVariation_poisson78
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_stackChain78_le
#print axioms RQMCMarkov.ScrambledStacks.occCount_stackChain78_mem
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_stackChain78_owen
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_stackChain78_shift
#print axioms RQMCMarkov.ScrambledStacks.exists_le_of_mul_le_log
#print axioms RQMCMarkov.ScrambledStacks.symChain
#print axioms RQMCMarkov.ScrambledStacks.isStochastic_symChain
#print axioms RQMCMarkov.ScrambledStacks.cumProb_one_fin_two
#print axioms RQMCMarkov.ScrambledStacks.card_filter_le_eq_add_segErr
#print axioms RQMCMarkov.ScrambledStacks.transCount_zero_one_eq
#print axioms RQMCMarkov.ScrambledStacks.transCount_one_zero_eq
#print axioms RQMCMarkov.ScrambledStacks.abs_segErr_zero_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_symChain_pow_two_le
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_comp_pow_two
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_symChain
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_symChain_owen
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_symChain_shift
#print axioms RQMCMarkov.ScrambledStacks.not_tendstoInDistribution_symChain_twoThirds_owen
#print axioms RQMCMarkov.ScrambledStacks.binaryVal_le_div_iff
#print axioms RQMCMarkov.ScrambledStacks.leaveTarget78
#print axioms RQMCMarkov.ScrambledStacks.cumProb_stackChain78_one
#print axioms RQMCMarkov.ScrambledStacks.stay78_zero_iff
#print axioms RQMCMarkov.ScrambledStacks.stay78_one_iff
#print axioms RQMCMarkov.ScrambledStacks.stay78_iff
#print axioms RQMCMarkov.ScrambledStacks.exists_leaveResidue78
#print axioms RQMCMarkov.ScrambledStacks.occCount_add_of_forall_eq
#print axioms RQMCMarkov.ScrambledStacks.stackPath_stay_iff
#print axioms RQMCMarkov.ScrambledStacks.stackPath_exit_eq
#print axioms RQMCMarkov.ScrambledStacks.exists_lt_occCount_eq
#print axioms RQMCMarkov.ScrambledStacks.not_stay_prev_of_spellStart
#print axioms RQMCMarkov.ScrambledStacks.spells_stackChain78
#print axioms RQMCMarkov.ScrambledStacks.firstSpell78_iff
#print axioms RQMCMarkov.ScrambledStacks.two_inv_pow_three
#print axioms RQMCMarkov.ScrambledStacks.owen_firstSpell78
#print axioms RQMCMarkov.ScrambledStacks.shift_firstSpell78
#print axioms RQMCMarkov.ScrambledStacks.runLength_zero_stackPath_iff
#print axioms RQMCMarkov.ScrambledStacks.owen_runLength_first78
#print axioms RQMCMarkov.ScrambledStacks.shift_runLength_first78
#print axioms RQMCMarkov.ScrambledStacks.cutWeight
#print axioms RQMCMarkov.ScrambledStacks.cutPoint
#print axioms RQMCMarkov.ScrambledStacks.cutPoint_mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.extendNat_fin
#print axioms RQMCMarkov.ScrambledStacks.sum_extendNat_mul_sub_eq
#print axioms RQMCMarkov.ScrambledStacks.step_sub_mulVec_eq_sum_cut
#print axioms RQMCMarkov.ScrambledStacks.sum_step_sub_eq_sum_segErr
#print axioms RQMCMarkov.ScrambledStacks.occCount_sub_eq_boundary_add_cuts
#print axioms RQMCMarkov.ScrambledStacks.IsPoissonFamily
#print axioms RQMCMarkov.ScrambledStacks.mulVec_le_of_le
#print axioms RQMCMarkov.ScrambledStacks.le_mulVec_of_le
#print axioms RQMCMarkov.ScrambledStacks.IsPoissonFamily.mem_Icc
#print axioms RQMCMarkov.ScrambledStacks.poissonSup
#print axioms RQMCMarkov.ScrambledStacks.abs_le_poissonSup
#print axioms RQMCMarkov.ScrambledStacks.poissonSup_nonneg
#print axioms RQMCMarkov.ScrambledStacks.anscConstN
#print axioms RQMCMarkov.ScrambledStacks.abs_occCount_sub_pi_le
#print axioms RQMCMarkov.ScrambledStacks.occErrN
#print axioms RQMCMarkov.ScrambledStacks.chainIdxN
#print axioms RQMCMarkov.ScrambledStacks.mainTermN
#print axioms RQMCMarkov.ScrambledStacks.cutWeightSum
#print axioms RQMCMarkov.ScrambledStacks.cutWeightSum_nonneg
#print axioms RQMCMarkov.ScrambledStacks.ansBoundN
#print axioms RQMCMarkov.ScrambledStacks.chainIdxN_le
#print axioms RQMCMarkov.ScrambledStacks.chainIdxN_lt_two_pow
#print axioms RQMCMarkov.ScrambledStacks.abs_occErrN_sub_mainTermN_le
#print axioms RQMCMarkov.ScrambledStacks.natLog_mul_le
#print axioms RQMCMarkov.ScrambledStacks.ansConstN
#print axioms RQMCMarkov.ScrambledStacks.ansBoundN_nonneg
#print axioms RQMCMarkov.ScrambledStacks.ansConstN_nonneg
#print axioms RQMCMarkov.ScrambledStacks.ansBoundN_le_log
#print axioms RQMCMarkov.ScrambledStacks.tendsto_sq_div_natLog_of_le
#print axioms RQMCMarkov.ScrambledStacks.cutTerm
#print axioms RQMCMarkov.ScrambledStacks.cutTermTrunc
#print axioms RQMCMarkov.ScrambledStacks.segErr_scrambledVdc_one
#print axioms RQMCMarkov.ScrambledStacks.segErr_scrambledVdc_eq_sum_cutTerm
#print axioms RQMCMarkov.ScrambledStacks.rowTerm
#print axioms RQMCMarkov.ScrambledStacks.rowTermTrunc
#print axioms RQMCMarkov.ScrambledStacks.levelSumN
#print axioms RQMCMarkov.ScrambledStacks.mainTermN_eq_levelSumN
#print axioms RQMCMarkov.ScrambledStacks.coinMeasure
#print axioms RQMCMarkov.ScrambledStacks.coinsOf
#print axioms RQMCMarkov.ScrambledStacks.absWeightSum
#print axioms RQMCMarkov.ScrambledStacks.absWeightSum_nonneg
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_levelInd_coins
#print axioms RQMCMarkov.ScrambledStacks.measureReal_levelInd_coins
#print axioms RQMCMarkov.ScrambledStacks.measurable_levelVal_coins
#print axioms RQMCMarkov.ScrambledStacks.integral_levelVal_coins
#print axioms RQMCMarkov.ScrambledStacks.measurable_cutTerm_coins
#print axioms RQMCMarkov.ScrambledStacks.abs_cutTerm_le
#print axioms RQMCMarkov.ScrambledStacks.abs_cutTermTrunc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_cutTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.setOf_levelTie_coins_eq
#print axioms RQMCMarkov.ScrambledStacks.measurableSet_levelTie_coins
#print axioms RQMCMarkov.ScrambledStacks.measureReal_levelTie_coins
#print axioms RQMCMarkov.ScrambledStacks.isLocal_cutTermTrunc_coins
#print axioms RQMCMarkov.ScrambledStacks.measurable_cutTermTrunc_coins
#print axioms RQMCMarkov.ScrambledStacks.integral_abs_cutTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.integral_cutTerm_coins
#print axioms RQMCMarkov.ScrambledStacks.abs_rowTerm_le
#print axioms RQMCMarkov.ScrambledStacks.abs_rowTermTrunc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_rowTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.measurable_rowTerm_coins
#print axioms RQMCMarkov.ScrambledStacks.isLocal_rowTermTrunc_coins
#print axioms RQMCMarkov.ScrambledStacks.measurable_rowTermTrunc_coins
#print axioms RQMCMarkov.ScrambledStacks.integral_abs_rowTerm_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.integral_rowTerm_coins
#print axioms RQMCMarkov.ScrambledStacks.levelYN
#print axioms RQMCMarkov.ScrambledStacks.levelYNTrunc
#print axioms RQMCMarkov.ScrambledStacks.levelSumN_eq_sum_levelYN
#print axioms RQMCMarkov.ScrambledStacks.abs_levelYN_le
#print axioms RQMCMarkov.ScrambledStacks.abs_levelYNTrunc_le
#print axioms RQMCMarkov.ScrambledStacks.abs_levelYN_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.measurable_levelYN_coins
#print axioms RQMCMarkov.ScrambledStacks.levelCoords
#print axioms RQMCMarkov.ScrambledStacks.lev_mem_of_mem_levelCoords
#print axioms RQMCMarkov.ScrambledStacks.isLocal_levelYNTrunc_coins
#print axioms RQMCMarkov.ScrambledStacks.integral_abs_levelYN_sub_trunc_le
#print axioms RQMCMarkov.ScrambledStacks.integral_levelSumN_coins
#print axioms RQMCMarkov.ScrambledStacks.measurable_levelSumN_coins
#print axioms RQMCMarkov.ScrambledStacks.abs_levelSumN_le
#print axioms RQMCMarkov.ScrambledStacks.memLp_levelSumN_coins
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_levelSumN
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_of_close_main
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_le_of_bound
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_le_of_local
#print axioms RQMCMarkov.ScrambledStacks.disjoint_levelCoords
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_levelYN_le
#print axioms RQMCMarkov.ScrambledStacks.variance_levelSumN_le
#print axioms RQMCMarkov.ScrambledStacks.variance_ge_of_int
#print axioms RQMCMarkov.ScrambledStacks.rowFrac
#print axioms RQMCMarkov.ScrambledStacks.variance_rowTerm_ge_of_int
#print axioms RQMCMarkov.ScrambledStacks.patternR
#print axioms RQMCMarkov.ScrambledStacks.patternR_lt
#print axioms RQMCMarkov.ScrambledStacks.testBit_patternR
#print axioms RQMCMarkov.ScrambledStacks.rowCoords
#print axioms RQMCMarkov.ScrambledStacks.mem_rowCoords
#print axioms RQMCMarkov.ScrambledStacks.tendsto_variance_rowTerm_sub_trunc
#print axioms RQMCMarkov.ScrambledStacks.covariance_rowTerm_eq_zero
#print axioms RQMCMarkov.ScrambledStacks.abs_covariance_rowTerm_le
#print axioms RQMCMarkov.ScrambledStacks.rowTerm_eq_zero_of_testBit
#print axioms RQMCMarkov.ScrambledStacks.levelSumN_pattern_eq
#print axioms RQMCMarkov.ScrambledStacks.variance_levelSumN_pattern_ge
#print axioms RQMCMarkov.ScrambledStacks.natLog_add_one_sq_le
#print axioms RQMCMarkov.ScrambledStacks.integral_sq_le_of_close
#print axioms RQMCMarkov.ScrambledStacks.integral_sq_levelSumN_le
#print axioms RQMCMarkov.ScrambledStacks.isBigO_meanSq_div_of_le
#print axioms RQMCMarkov.ScrambledStacks.shiftLayout
#print axioms RQMCMarkov.ScrambledStacks.shiftLayout_lev
#print axioms RQMCMarkov.ScrambledStacks.shiftLayout_rows
#print axioms RQMCMarkov.ScrambledStacks.pathCoins_shiftFlips_eq
#print axioms RQMCMarkov.ScrambledStacks.shiftMainTerm
#print axioms RQMCMarkov.ScrambledStacks.mainTermN_shiftFlips_eq
#print axioms RQMCMarkov.ScrambledStacks.abs_occErrN_shift_sub_le
#print axioms RQMCMarkov.ScrambledStacks.abs_occErrN_le
#print axioms RQMCMarkov.ScrambledStacks.memLp_occErrN_shift
#print axioms RQMCMarkov.ScrambledStacks.tendsto_natLog_add_one
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_occErrN_shift
#print axioms RQMCMarkov.ScrambledStacks.varConstN
#print axioms RQMCMarkov.ScrambledStacks.two_mul_ansBoundN_sq_le
#print axioms RQMCMarkov.ScrambledStacks.integral_sq_occErrN_shift_le
#print axioms RQMCMarkov.ScrambledStacks.variance_occErrN_shift_le
#print axioms RQMCMarkov.ScrambledStacks.isBigO_meanSq_occFreqN_shift
#print axioms RQMCMarkov.ScrambledStacks.prefixDigits
#print axioms RQMCMarkov.ScrambledStacks.owenNode
#print axioms RQMCMarkov.ScrambledStacks.owenRelabel
#print axioms RQMCMarkov.ScrambledStacks.owenRect
#print axioms RQMCMarkov.ScrambledStacks.mem_owenRect
#print axioms RQMCMarkov.ScrambledStacks.owenBox_eq_owenRect
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix_congr_digits
#print axioms RQMCMarkov.ScrambledStacks.pathPrefix_threshDigit_eq
#print axioms RQMCMarkov.ScrambledStacks.floor_two_pow_mul_lt
#print axioms RQMCMarkov.ScrambledStacks.pathCoin_owenTable_eq_relabel
#print axioms RQMCMarkov.ScrambledStacks.owenNode_lt
#print axioms RQMCMarkov.ScrambledStacks.owenNode_inj
#print axioms RQMCMarkov.ScrambledStacks.owenNode_congr
#print axioms RQMCMarkov.ScrambledStacks.owenRelabel_congr
#print axioms RQMCMarkov.ScrambledStacks.measurable_owenRelabel
#print axioms RQMCMarkov.ScrambledStacks.measure_eq_sum_restrict_preimage
#print axioms RQMCMarkov.ScrambledStacks.coinMeasure_setOf_comp_eq
#print axioms RQMCMarkov.ScrambledStacks.owenMeasure_relabel_rect
#print axioms RQMCMarkov.ScrambledStacks.eq_owenMeasure_of_box
#print axioms RQMCMarkov.ScrambledStacks.measurePreserving_owenRelabel
#print axioms RQMCMarkov.ScrambledStacks.owenLayout
#print axioms RQMCMarkov.ScrambledStacks.owenLayout_lev
#print axioms RQMCMarkov.ScrambledStacks.owenLayout_rows
#print axioms RQMCMarkov.ScrambledStacks.pathCoins_owenTable_eq
#print axioms RQMCMarkov.ScrambledStacks.levelSumN_congr
#print axioms RQMCMarkov.ScrambledStacks.owenMainTerm
#print axioms RQMCMarkov.ScrambledStacks.mainTermN_owenTable_eq
#print axioms RQMCMarkov.ScrambledStacks.abs_occErrN_owen_sub_le
#print axioms RQMCMarkov.ScrambledStacks.memLp_occErrN_owen
#print axioms RQMCMarkov.ScrambledStacks.integral_owenMainTerm_relabel
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_occErrN_owen
#print axioms RQMCMarkov.ScrambledStacks.integral_sq_occErrN_owen_le
#print axioms RQMCMarkov.ScrambledStacks.variance_occErrN_owen_le
#print axioms RQMCMarkov.ScrambledStacks.isBigO_meanSq_occFreqN_owen
#print axioms RQMCMarkov.ScrambledStacks.uniformChain
#print axioms RQMCMarkov.ScrambledStacks.uniformPoisson
#print axioms RQMCMarkov.ScrambledStacks.uniformPi
#print axioms RQMCMarkov.ScrambledStacks.uniformSpacing
#print axioms RQMCMarkov.ScrambledStacks.uniformTime
#print axioms RQMCMarkov.ScrambledStacks.isStochastic_uniformChain
#print axioms RQMCMarkov.ScrambledStacks.mulVec_uniformPoisson
#print axioms RQMCMarkov.ScrambledStacks.isPoissonFamily_uniform
#print axioms RQMCMarkov.ScrambledStacks.chainIdxN_uniformTime
#print axioms RQMCMarkov.ScrambledStacks.cutWeight_uniform
#print axioms RQMCMarkov.ScrambledStacks.cutWeight_uniform_int
#print axioms RQMCMarkov.ScrambledStacks.absWeightSum_uniform_le
#print axioms RQMCMarkov.ScrambledStacks.fracPow_one
#print axioms RQMCMarkov.ScrambledStacks.ite_fracPow_eq
#print axioms RQMCMarkov.ScrambledStacks.sum_cutWeight_mul_cutPoint_uniform
#print axioms RQMCMarkov.ScrambledStacks.rowFrac_uniform
#print axioms RQMCMarkov.ScrambledStacks.fract_mul_one_sub_ge
#print axioms RQMCMarkov.ScrambledStacks.variance_rowTerm_uniform_ge
#print axioms RQMCMarkov.ScrambledStacks.uniformSpacing_bound
#print axioms RQMCMarkov.ScrambledStacks.variance_levelSumN_uniform_ge
#print axioms RQMCMarkov.ScrambledStacks.eventually_variance_ge_of_close
#print axioms RQMCMarkov.ScrambledStacks.uniformSpacing_mul_lt
#print axioms RQMCMarkov.ScrambledStacks.natLog_uniformTime_le
#print axioms RQMCMarkov.ScrambledStacks.tendsto_uniformTime
#print axioms RQMCMarkov.ScrambledStacks.tendsto_ansBoundN_uniform
#print axioms RQMCMarkov.ScrambledStacks.eventually_variance_occErrN_uniform_shift_ge
#print axioms RQMCMarkov.ScrambledStacks.eventually_variance_occErrN_uniform_owen_ge
#print axioms RQMCMarkov.ScrambledStacks.occErrN_uniform_tendstoInDistribution_shift
#print axioms RQMCMarkov.ScrambledStacks.occErrN_uniform_tendstoInDistribution_owen
#print axioms RQMCMarkov.ScrambledStacks.not_five_dvd_two_pow
#print axioms RQMCMarkov.ScrambledStacks.eventually_variance_occErrN_example_shift_ge
#print axioms RQMCMarkov.ScrambledStacks.eventually_variance_occErrN_example_owen_ge
#print axioms RQMCMarkov.ScrambledStacks.occErrN_example_tendstoInDistribution_shift
#print axioms RQMCMarkov.ScrambledStacks.occErrN_example_tendstoInDistribution_owen
#print axioms RQMCMarkov.ScrambledStacks.occErrN_five_tendstoInDistribution_shift
#print axioms RQMCMarkov.ScrambledStacks.occErrN_five_tendstoInDistribution_owen
#print axioms RQMCMarkov.ScrambledStacks.transErrN
#print axioms RQMCMarkov.ScrambledStacks.indicatorFn
#print axioms RQMCMarkov.ScrambledStacks.transErrN_eq
#print axioms RQMCMarkov.ScrambledStacks.transMainN
#print axioms RQMCMarkov.ScrambledStacks.transBound
#print axioms RQMCMarkov.ScrambledStacks.abs_transErrN_sub_transMainN_le
#print axioms RQMCMarkov.ScrambledStacks.transBound_nonneg
#print axioms RQMCMarkov.ScrambledStacks.transBound_le_log
#print axioms RQMCMarkov.ScrambledStacks.rowCut
#print axioms RQMCMarkov.ScrambledStacks.rowCut_nonneg
#print axioms RQMCMarkov.ScrambledStacks.transMainN_eq_levelSumN
#print axioms RQMCMarkov.ScrambledStacks.shiftTransMain
#print axioms RQMCMarkov.ScrambledStacks.abs_transErrN_le
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_transErrN_shift
#print axioms RQMCMarkov.ScrambledStacks.owenLayoutOf
#print axioms RQMCMarkov.ScrambledStacks.owenTransMain
#print axioms RQMCMarkov.ScrambledStacks.tendstoInDistribution_transErrN_owen
