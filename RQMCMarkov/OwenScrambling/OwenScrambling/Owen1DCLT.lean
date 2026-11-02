/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Owen1DScramble
import OwenScrambling.Owen1DLindeberg
import OwenScrambling.Owen1DVariance

/-!
# The CLT for the Owen-scrambled net in one dimension (post #2, Loh 2003)

Post #2: "If we use an RQMC estimator with a digital net and nested uniform scrambling (Owen
scrambling) then a standard CLT applies and the asymptotic distribution is normally distributed"
(Loh 2003). Reading, in dimension `d = 1`, base `b ≥ 2`: the Owen-scrambled `(0,m,1)`-net
estimator `μ̂ₙ = (1/n) Σₖ f(owenNet T R k)`, `n = bᵐ`, normalised by its own standard deviation
`σₙ = √Var(μ̂ₙ)`, converges in distribution to `N(0,1)` as `m → ∞`.

## Main results

* `tendstoInDistribution_stratified`: for measurable `f`, `C¹` on `[0,1]` and not constant there,
  independent stratified sampling with `N k → ∞` cells satisfies
  `(μ̂ − μ)/σ ⇒ N(0,1)` (any number of cells, not only `bᵐ`; any probability spaces).
* `tendstoInDistribution_stratified_all_n`: the same along all `n`.
* Tools: `cellTerm` (the centred normalised cell terms, `sum_cellTerm`), `integrable_cell`,
  `inv_mul_sum_integral_cell`, `iIndepFun_coords`, `abs_cellTerm_le`, `exists_lipschitz_of_C1`,
  `memLp_uniformIco_of_continuousOn`, `sampleMean_owenNet_eq_stratPoints`.
* `tendstoInDistribution_owenNet` (**post #2's claim in `d = 1`**): the Owen-scrambled net,
  `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)` as `n = bᵐ → ∞`.
* `variance_owenNet_eq_stratVar`, `tendsto_cube_mul_variance_owenNet`: `σₙ² = stratVar n f` and
  `n³ σₙ² → (1/12) ∫₀¹ f'²`, so the RMSE is of order `n^{-3/2}`.
* `owenNet_exact_of_const`, `not_tendstoInDistribution_owenNet_const`: the correction below.
* `owenNet_normal_and_shift_not_normal` (the contrast of post #2): for the same `f`, Owen
  scrambling gives a normal limit while the randomly shifted lattice (`ShiftLimit`) has the uniform
  limit `n (μ̂ₙ − μ) ⇒ (f(1) − f(0))(U − 1/2)` and no normal limit.

**Correction.** "A standard CLT applies" needs a non-degenerate integrand: for constant `f`
(`stratVar_const`, `owenNet_exact_of_const`) the scrambled-net estimator is exact, `σₙ = 0`, and the
normalised error is identically `0`, which converges to the point mass at `0`, not to `N(0,1)`
(`not_tendstoInDistribution_owenNet_const`). The corrected statement assumes `f` non-constant on
`[0,1]`, which for `C¹` `f` gives `σₙ > 0` eventually (`eventually_stratVar_pos`). Smoothness is
also needed: for the discontinuous `f = 1_{[0,1/3)}` (base 2) `σₙ > 0` but the normalised error is
bounded and has no normal limit (`not_tendstoInDistribution_owenNet_indicator` in
`Owen1DCounterexample`). The theorem also
does not need the tree to be uniform: any random permutation of the cells independent of the
remainders gives the same law of the estimator (uniformity is what makes each point `U[0,1)`).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The centred, normalised contribution of cell `i` to the stratified estimator:
`(f((i + u)/n) − E f((i + U)/n)) / (n σₙ)`, with `σₙ = √(stratVar n f)`. -/
noncomputable def cellTerm (n : ℕ) (f : ℝ → ℝ) (i : Fin n) (u : ℝ) : ℝ :=
  (f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco) /
    (n * Real.sqrt (stratVar n f))

/-- A stratified point of `[0,1]` stays in `[0,1]`. -/
theorem stratumMap_mem_Icc {n : ℕ} (i : Fin n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    stratumMap n i u ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  simp only [stratumMap, mem_Icc]
  refine ⟨div_nonneg (by linarith [hu.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) hn.le, ?_⟩
  rw [div_le_one hn]
  linarith [hu.2]

/-- For `f` continuous on `[0,1]`, the cell function `u ↦ f((i + u)/n)` is integrable on
`U[0,1)`. -/
theorem integrable_cell {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {n : ℕ} (i : Fin n) :
    Integrable (fun u ↦ f (stratumMap n i u)) uniformIco := by
  have hg : ContinuousOn (fun u ↦ f (stratumMap n i u)) (Icc 0 1) :=
    hc.comp (continuous_stratumMap n i).continuousOn (fun u hu ↦ stratumMap_mem_Icc i hu)
  exact (hg.integrableOn_Icc).mono_set Ico_subset_Icc_self

/-- **The cell means average to the integral**: `(1/n) Σᵢ E f((i + U)/n) = ∫₀¹ f`. -/
theorem inv_mul_sum_integral_cell {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {n : ℕ}
    (hn : n ≠ 0) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ x, f (stratumMap n i x) ∂uniformIco = ∫ x, f x ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  have hfi : Integrable f uniformIco :=
    (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Ico_subset_Icc_self
  have h := integral_sampleMean_stratified hn (P := uniformCube n)
    (V := fun i v ↦ v i) hasLaw_eval_uniformCube hfi
  rw [← h]
  unfold sampleMean
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    have := (hasLaw_eval_uniformCube (n := n) i).integral_comp
      (integrable_cell hc i).aestronglyMeasurable
    exact this.symm
  · intro i _
    exact (hasLaw_eval_uniformCube (n := n) i).integrable_comp (integrable_cell hc i)

/-- **The normalised error is the sum of the cell terms**: for every `v`,
`(μ̂(v) − ∫₀¹ f)/σₙ = Σᵢ cellTerm n f i (vᵢ)`. -/
theorem sum_cellTerm {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) (n : ℕ) (v : Fin n → ℝ) :
    ∑ i, cellTerm n f i (v i) =
      (sampleMean n f (stratPoints n v) - ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar n f) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hs : stratVar 0 f = 0 := by
      unfold stratVar
      rw [Nat.cast_zero, inv_zero, zero_pow two_ne_zero, zero_mul]
    rw [hs, Real.sqrt_zero, div_zero]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hmean := inv_mul_sum_integral_cell hc hpos.ne'
  unfold cellTerm
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← div_div, ← hmean]
  congr 1
  unfold sampleMean stratPoints
  field_simp

/-- The coordinates of a `U[0,1)ⁿ` vector are independent. -/
theorem iIndepFun_coords {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {V : Ω → Fin n → ℝ} (hV : HasLaw V (uniformCube n) P) :
    iIndepFun (fun i ω ↦ V ω i) P := by
  have := isProbabilityMeasure_uniformIco
  have hc : ∀ i : Fin n, HasLaw (fun ω ↦ V ω i) uniformIco P := fun i ↦
    (hasLaw_eval_uniformCube i).comp hV
  exact (iIndepFun_iff_hasLaw_pi_pi hc).2 hV

/-- A cell term is bounded: if `|f x − f y| ≤ K |x − y|` on `[0,1]` then
`|cellTerm n f i u| ≤ (K/n)/(n σₙ)` for `u ∈ [0,1)`. -/
theorem abs_cellTerm_le {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) {K : ℝ}
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ K * |x - y|) {n : ℕ}
    (i : Fin n) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    |cellTerm n f i u| ≤ (K / n) / (n * Real.sqrt (stratVar n f)) := by
  have := isProbabilityMeasure_uniformIco
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (Fin.pos i).ne')
  have hK0 : 0 ≤ K := by
    have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hpt : ∀ x ∈ Ico (0 : ℝ) 1, |f (stratumMap n i u) - f (stratumMap n i x)| ≤ K / n := by
    intro x hx
    refine (hK _ (stratumMap_mem_Icc i (Ico_subset_Icc_self hu)) _
      (stratumMap_mem_Icc i (Ico_subset_Icc_self hx))).trans ?_
    have heq : stratumMap n i u - stratumMap n i x = (u - x) / n := by
      simp only [stratumMap]
      ring
    rw [heq, abs_div, abs_of_pos hn]
    have hux : |u - x| ≤ 1 := abs_le.2 ⟨by linarith [hu.1, hx.2], by linarith [hu.2, hx.1]⟩
    calc K * (|u - x| / n) ≤ K * (1 / n) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hux hn.le) hK0
      _ = K / n := by ring
  have hdiff : |f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco| ≤ K / n := by
    have heq : f (stratumMap n i u) - ∫ x, f (stratumMap n i x) ∂uniformIco =
        ∫ x, (f (stratumMap n i u) - f (stratumMap n i x)) ∂uniformIco := by
      rw [integral_sub (integrable_const _) (integrable_cell hc i), integral_const,
        probReal_univ, one_smul]
    rw [heq]
    have h := norm_integral_le_of_norm_le_const (μ := uniformIco)
      (f := fun x ↦ f (stratumMap n i u) - f (stratumMap n i x)) (C := K / n)
      (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ by
        rw [Real.norm_eq_abs]
        exact hpt x hx)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  unfold cellTerm
  rw [abs_div, abs_of_nonneg (mul_nonneg hn.le (Real.sqrt_nonneg _))]
  exact div_le_div_of_nonneg_right hdiff (mul_nonneg hn.le (Real.sqrt_nonneg _))

/-- A `C¹` function on `[0,1]` is Lipschitz there with constant `sup |f'|`. -/
theorem exists_lipschitz_of_C1 {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) :
    ∃ K : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x - f y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  refine ⟨K, fun x hx y hy ↦ ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hK (convex_Icc 0 1) hy hx
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **CLT for independent stratified sampling** (any number of cells): let `f` be measurable,
`C¹` on `[0,1]` and not constant there. For probability spaces `(Ωₖ, Pₖ)` carrying
`Vₖ ~ U[0,1)^(Nₖ)` with `Nₖ → ∞`, the stratified estimator
`μ̂ₖ = (1/Nₖ) Σᵢ f((i + Vₖ i)/Nₖ)` satisfies `(μ̂ₖ − ∫₀¹ f)/σ_{Nₖ} ⇒ N(0,1)`, with
`σₙ² = stratVar n f` its variance. -/
theorem tendstoInDistribution_stratified {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
    {P : (k : ℕ) → Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {V : (k : ℕ) → Ω k → Fin (N k) → ℝ} (hV : ∀ k, HasLaw (V k) (uniformCube (N k)) (P k))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω ↦ (sampleMean (N k) f (stratPoints (N k) (V k ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (N k) f)) atTop Z P P' := by
  have := isProbabilityMeasure_uniformIco
  have hc : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  obtain ⟨K, hK⟩ := exists_lipschitz_of_C1 hf hf'
  have hcoord : ∀ k (i : Fin (N k)), HasLaw (fun ω ↦ V k ω i) uniformIco (P k) := fun k i ↦
    (hasLaw_eval_uniformCube i).comp (hV k)
  have hcm : ∀ n (i : Fin n), Measurable (cellTerm n f i) := fun n i ↦
    ((hfm.comp (measurable_stratumMap n i)).sub_const _).div_const _
  have hfun : (fun k ω ↦ (sampleMean (N k) f (stratPoints (N k) (V k ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (N k) f)) =
      fun k ω ↦ ∑ i, cellTerm (N k) f i (V k ω i) := by
    funext k ω
    rw [sum_cellTerm hc]
  rw [hfun]
  -- the asymptotics of the variance
  set c : ℝ := (∫ x in (0 : ℝ)..1, f' x ^ 2) / 12 with hcdef
  have hcpos : 0 < c := div_pos (integral_sq_deriv_pos hf hf' hnc) (by norm_num)
  have hlim : Tendsto (fun k ↦ (N k : ℝ) ^ 3 * stratVar (N k) f) atTop (𝓝 c) :=
    (tendsto_cube_mul_stratVar hf hf').comp hN
  have hspos : ∀ᶠ k in atTop, 0 < stratVar (N k) f :=
    hN.eventually (eventually_stratVar_pos hf hf' hnc)
  have hNpos : ∀ᶠ k in atTop, 0 < N k := hN.eventually (eventually_gt_atTop 0)
  set δ : ℕ → ℝ := fun k ↦ (K / N k) / (N k * Real.sqrt (stratVar (N k) f)) with hδdef
  have hδ0 : ∀ k, 0 ≤ δ k := by
    intro k
    rcases le_or_gt 0 K with hK0 | hK0
    · exact div_nonneg (div_nonneg hK0 (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    · rcases Nat.eq_zero_or_pos (N k) with h0 | hp
      · simp only [hδdef, h0, Nat.cast_zero, div_zero, zero_div, le_refl]
      · have h := hK 1 (right_mem_Icc.2 zero_le_one) 0 (left_mem_Icc.2 zero_le_one)
        rw [sub_zero, abs_one, mul_one] at h
        linarith [abs_nonneg (f 1 - f 0)]
  have hδsq : ∀ᶠ k in atTop, δ k ^ 2 = K ^ 2 / N k * ((N k : ℝ) ^ 3 * stratVar (N k) f)⁻¹ := by
    filter_upwards [hspos, hNpos] with k hs hNk
    have hNr : (0 : ℝ) < N k := Nat.cast_pos.2 hNk
    have hsq : Real.sqrt (stratVar (N k) f) ^ 2 = stratVar (N k) f := Real.sq_sqrt hs.le
    simp only [hδdef]
    rw [div_pow, div_pow, mul_pow, hsq]
    field_simp
  have hδ2lim : Tendsto (fun k ↦ δ k ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k ↦ K ^ 2 / (N k : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (K ^ 2)).comp hN
    have h2 := h1.mul (hlim.inv₀ hcpos.ne')
    rw [zero_mul] at h2
    exact h2.congr' (hδsq.mono fun k hk ↦ hk.symm)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδ2lim
    rw [Real.sqrt_zero] at h
    refine h.congr (fun k ↦ ?_)
    change Real.sqrt (δ k ^ 2) = δ k
    exact Real.sqrt_sq (hδ0 k)
  refine tendstoInDistribution_sum_of_bounded (L := N)
    (X := fun k i ω ↦ cellTerm (N k) f i (V k ω i))
    (fun k i ↦ (hcm _ i).comp_aemeasurable (hcoord k i).aemeasurable)
    (fun k ↦ (iIndepFun_coords (hV k)).comp _ (fun i ↦ hcm _ i))
    (fun k i ↦ ?_) hδlim (fun k i ↦ ?_) (v := 1) ?_ (by rw [Real.toNNReal_one]; exact hZ)
  · -- centred
    change ∫ ω, (cellTerm (N k) f i ∘ fun ω ↦ V k ω i) ω ∂(P k) = 0
    rw [(hcoord k i).integral_comp (hcm _ i).aestronglyMeasurable]
    unfold cellTerm
    rw [integral_div, integral_sub (integrable_cell hc i) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self, zero_div]
  · -- bounded
    filter_upwards [ae_mem_Ico_of_hasLaw (hcoord k i)] with ω hω
    exact abs_cellTerm_le hc hK i hω
  · -- the variances sum to one, eventually
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hspos] with k hs
    have hNk : N k ≠ 0 := by
      rintro h0
      have : stratVar (N k) f = 0 := by
        unfold stratVar
        rw [h0, Nat.cast_zero, inv_zero, zero_pow two_ne_zero, zero_mul]
      rw [this] at hs
      exact lt_irrefl 0 hs
    have hNr : (N k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hNk
    have hsq : Real.sqrt (stratVar (N k) f) ^ 2 = stratVar (N k) f := Real.sq_sqrt hs.le
    have hterm : ∀ i : Fin (N k), ∫ ω, cellTerm (N k) f i (V k ω i) ^ 2 ∂(P k) =
        Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] /
          ((N k : ℝ) ^ 2 * stratVar (N k) f) := by
      intro i
      change ∫ ω, ((fun u ↦ cellTerm (N k) f i u ^ 2) ∘ fun ω ↦ V k ω i) ω ∂(P k) = _
      rw [(hcoord k i).integral_comp ((hcm _ i).pow_const 2).aestronglyMeasurable,
        variance_eq_integral (X := fun u ↦ f (stratumMap (N k) i u))
          (hfm.comp (measurable_stratumMap _ i)).aemeasurable]
      unfold cellTerm
      rw [← integral_div]
      congr 1
      funext u
      rw [div_pow, mul_pow, hsq]
    rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← Finset.sum_div]
    have hS : (N k : ℝ) ^ 2 * stratVar (N k) f =
        ∑ i : Fin (N k), Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] := by
      unfold stratVar
      field_simp
    have hS0 : ∑ i : Fin (N k), Var[fun u ↦ f (stratumMap (N k) i u); uniformIco] ≠ 0 := by
      rw [← hS]
      exact (mul_pos (by positivity) hs).ne'
    rw [hS, div_self hS0]

/-- **CLT for independent stratification with `n` cells, along all `n`** (target 3): for each `n`
let `Vₙ ~ U[0,1)ⁿ` on `(Ωₙ, Pₙ)`; then `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)` for every measurable `f`
that is `C¹` and non-constant on `[0,1]`. -/
theorem tendstoInDistribution_stratified_all_n {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {V : (n : ℕ) → Ω n → Fin n → ℝ}
    (hV : ∀ n, HasLaw (V n) (uniformCube n) (P n))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ (sampleMean n f (stratPoints n (V n ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar n f)) atTop Z P P' :=
  tendstoInDistribution_stratified hfm hf hf' hnc (N := id) tendsto_id hV hZ

/-- The scrambled-net estimator is the stratified estimator of the relabelled remainders. -/
theorem sampleMean_owenNet_eq_stratPoints {b m : ℕ} (T : OwenTree b m) (r : Fin (b ^ m) → ℝ)
    (f : ℝ → ℝ) :
    sampleMean (b ^ m) f (owenNet T r) =
      sampleMean (b ^ m) f (stratPoints (b ^ m) (owenRemainder T r)) := by
  rw [sampleMean_owenNet, owenNetSorted_eq_stratPoints]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {b : ℕ}
  {mT : ∀ m, MeasurableSpace (OwenTree b m)} [∀ m, DiscreteMeasurableSpace (OwenTree b m)]

/-- **Post #2's CLT for Owen scrambling, one dimension** (Loh 2003 in `d = 1`): let `b ≥ 2`, and
for each `m` let the scrambling tree `T m` be independent of the remainders `R m ~ U[0,1)^(bᵐ)`.
For measurable `f`, `C¹` and non-constant on `[0,1]`, the Owen-scrambled net estimator
`μ̂ₙ = (1/n) Σₖ f(owenNet (T m) (R m) k)`, `n = bᵐ`, satisfies `(μ̂ₙ − ∫₀¹ f)/σₙ ⇒ N(0,1)`, where
`σₙ² = stratVar n f = Var(μ̂ₙ)` (`variance_owenNet_eq_stratVar`). -/
theorem tendstoInDistribution_owenNet (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) =
      fun m ω ↦ (sampleMean (b ^ m) f (stratPoints (b ^ m) (owenRemainder (T m ω) (R m ω))) -
        ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f) := by
    funext m ω
    rw [sampleMean_owenNet_eq_stratPoints]
  rw [hfun]
  exact tendstoInDistribution_stratified hfm hf hf' hnc (N := fun m ↦ b ^ m)
    (tendsto_pow_atTop_atTop_of_one_lt hb) (Ω := fun _ ↦ Ω) (P := fun _ ↦ P)
    (V := fun m ω ↦ owenRemainder (T m ω) (R m ω))
    (fun m ↦ hasLaw_owenRemainder (hT m) (hR m) (hRlaw m) (hind m)) hZ

/-- A function continuous on `[0,1]` is in `L^p(U[0,1))` when measurable. -/
theorem memLp_uniformIco_of_continuousOn {f : ℝ → ℝ} (hfm : Measurable f)
    (hc : ContinuousOn f (Icc 0 1)) (p : ℝ≥0∞) : MemLp f p uniformIco := by
  have := isProbabilityMeasure_uniformIco
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact MemLp.of_bound hfm.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ico fun x hx ↦ hC x (Ico_subset_Icc_self hx))

/-- **The variance of the scrambled net is `stratVar`**: `Var(μ̂ₙ) = σₙ² = stratVar (bᵐ) f`. -/
theorem variance_owenNet_eq_stratVar (hb : b ≠ 0) {m : ℕ} {f : ℝ → ℝ} (hfm : Measurable f)
    (hc : ContinuousOn f (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Ω → OwenTree b m} {R : Ω → Fin (b ^ m) → ℝ} (hT : Measurable T) (hR : Measurable R)
    (hRlaw : HasLaw R (uniformCube (b ^ m)) P) (hind : IndepFun T R P) :
    Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T ω) (R ω)); P] = stratVar (b ^ m) f :=
  variance_sampleMean_owenNet hb hT hR hRlaw hind hfm (memLp_uniformIco_of_continuousOn hfm hc 2)

/-- **The rate of the scrambled net**: `n³ Var(μ̂ₙ) → (1/12) ∫₀¹ f'²` as `n = bᵐ → ∞`, so the
RMSE is `n^{-3/2} (∫₀¹ f'²/12)^{1/2} (1 + o(1))`. -/
theorem tendsto_cube_mul_variance_owenNet (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P]
    {T : (m : ℕ) → Ω → OwenTree b m} {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ}
    (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P) :
    Tendsto (fun m ↦ ((b ^ m : ℕ) : ℝ) ^ 3 *
        Var[fun ω ↦ sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)); P]) atTop
      (𝓝 ((∫ x in (0 : ℝ)..1, f' x ^ 2) / 12)) := by
  have hc : ContinuousOn f (Icc 0 1) := fun x hx ↦ (hf x hx).continuousWithinAt
  have h := (tendsto_cube_mul_stratVar hf hf').comp (tendsto_pow_atTop_atTop_of_one_lt hb)
  refine h.congr (fun m ↦ ?_)
  change ((b ^ m : ℕ) : ℝ) ^ 3 * stratVar (b ^ m) f = _
  rw [variance_owenNet_eq_stratVar (by omega) hfm hc (hT m) (hR m) (hRlaw m) (hind m)]

/-- **Post #2's contrast, as a theorem pair** (one dimension, the same `C¹` non-constant `f`):
(1) the Owen-scrambled net is asymptotically normal, `(μ̂ₙ − μ)/σₙ ⇒ N(0,1)`; (2) the randomly
shifted lattice `(1/n) Σᵢ f((i + U)/n)` has the uniform limit
`n (μ̂ₙ − μ) ⇒ (f(1) − f(0))(U − 1/2)` and (3) does not converge to any normal `N(m₀, v)`, `v ≠ 0`
(`ShiftLimit`). -/
theorem owenNet_normal_and_shift_not_normal (hb : 1 < b) {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) (hnc : ∃ x ∈ Icc (0 : ℝ) 1, f x ≠ f 0)
    {P : Measure Ω} [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ} (hT : ∀ m, Measurable (T m)) (hR : ∀ m, Measurable (R m))
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (b ^ m)) P) (hind : ∀ m, IndepFun (T m) (R m) P)
    {U : Ω → ℝ} (hU : HasLaw U uniformIco P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) f (owenNet (T m ω) (R m ω)) -
      ∫ x, f x ∂uniformIco) / Real.sqrt (stratVar (b ^ m) f)) atTop Z (fun _ ↦ P) P' ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P ∧
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ stratumMap n i (U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' :=
  ⟨tendstoInDistribution_owenNet hb hfm hf hf' hnc hT hR hRlaw hind hZ,
    tendstoInDistribution_scaled_error hfm hf hf' hU,
    not_tendstoInDistribution_scaled_error_gaussian hfm hf hf' hU m₀ hv hY⟩

/-- **Correction: constant integrands are integrated exactly** by the scrambled net: for
`f ≡ c`, `μ̂ₙ = c = ∫₀¹ f` for every realisation, so `σₙ = 0` (`stratVar_const`). -/
theorem owenNet_exact_of_const (hb : b ≠ 0) {m : ℕ} (c : ℝ) (T : OwenTree b m)
    (r : Fin (b ^ m) → ℝ) :
    sampleMean (b ^ m) (fun _ ↦ c) (owenNet T r) = ∫ _x, c ∂uniformIco := by
  have := isProbabilityMeasure_uniformIco
  rw [integral_const, probReal_univ, one_smul]
  exact sampleMean_const_points (pow_ne_zero m hb) (fun _ ↦ c) 0

/-- **Correction: no CLT for constant `f`.** For `f ≡ c` the normalised error
`(μ̂ₙ − μ)/σₙ` of the scrambled net is identically `0`, so it does not converge in distribution to
any normal law `N(m₀, v)` with `v ≠ 0` (in particular not to `N(0,1)`). -/
theorem not_tendstoInDistribution_owenNet_const (hb : b ≠ 0) (c : ℝ) {P : Measure Ω}
    [IsProbabilityMeasure P] {T : (m : ℕ) → Ω → OwenTree b m}
    {R : (m : ℕ) → Ω → Fin (b ^ m) → ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m ω ↦ (sampleMean (b ^ m) (fun _ ↦ c) (owenNet (T m ω) (R m ω)) -
      ∫ _x, c ∂uniformIco) / Real.sqrt (stratVar (b ^ m) (fun _ ↦ c))) atTop Y (fun _ ↦ P) P' := by
  have hfun : (fun m ω ↦ (sampleMean (b ^ m) (fun _ ↦ c) (owenNet (T m ω) (R m ω)) -
      ∫ _x, c ∂uniformIco) / Real.sqrt (stratVar (b ^ m) (fun _ ↦ c))) =
      fun (_ : ℕ) (_ : Ω) ↦ (0 : ℝ) := by
    funext m ω
    rw [owenNet_exact_of_const hb c, sub_self, zero_div]
  rw [hfun]
  intro h
  have h0 : TendstoInDistribution (fun (_ : ℕ) (_ : Ω) ↦ (0 : ℝ)) atTop (fun _ ↦ (0 : ℝ))
      (fun _ ↦ P) P :=
    tendstoInDistribution_of_ae_tendsto (fun _ ↦ aemeasurable_const) aemeasurable_const
      (Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  have heq := tendstoInDistribution_unique _ h0 h
  rw [hY.map_eq] at heq
  refine ne_gaussianReal_of_measure_Ioi_eq_zero (M := 0) ?_ m₀ hv heq
  rw [Measure.map_apply measurable_const measurableSet_Ioi,
    preimage_const_of_notMem (s := Ioi (0 : ℝ)) (fun h ↦ lt_irrefl (0 : ℝ) h), measure_empty]

end RQMCMarkov.OwenScrambling
