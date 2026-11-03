/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.CentralLimitTheorem

/-!
# Monte Carlo: unbiasedness, variance `σ²/n`, RMSE `n^{-1/2}`, CLT (post #1)

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

namespace RQMCMarkov.PointSets

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

end RQMCMarkov.PointSets
