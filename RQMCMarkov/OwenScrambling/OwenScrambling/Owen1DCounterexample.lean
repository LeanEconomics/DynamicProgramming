/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.Owen1DCLT
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# No CLT for the Owen-scrambled net with a discontinuous integrand (post #2, correction)

Post #2 says that with Owen scrambling "a standard CLT applies". In one dimension we proved it for
`C¹` non-constant integrands (`tendstoInDistribution_owenNet`). Here we show that smoothness cannot
be dropped, even when the variance is non-degenerate: for the indicator `f = 1_{[0,1/3)}` and the
base-2 scrambled net, `σₙ > 0` for every `n = 2ᵐ`, but the normalised error `(μ̂ₙ − μ)/σₙ` is
bounded by `3` almost surely for every `m`, so it cannot converge to any normal law. (Only the one
cell containing the jump at `1/3` is random; the estimator takes two values.) Loh's (2003) CLT
assumes a smooth integrand, so this is a correction of the post's unqualified claim, not of Loh.

## Main results

* `not_tendstoInDistribution_gaussian_of_abs_le`: a.s. uniformly bounded random variables do not
  converge in distribution to a normal law `N(m₀, v)`, `v ≠ 0` (portmanteau).
* `abs_sum_indicator_sub_le`: for points `xᵢ` in the cells `[i/n, (i+1)/n)` and `c ∈ [0,1]`,
  `|Σᵢ 1{xᵢ < c} − n c| ≤ 1`.
* `variance_indicator_uniformIco`: `Var_{U[0,1)} 1{u < p} = p (1 − p)` for `p ∈ [0,1]`.
* `two_pow_mod_three`, `stratVar_indicator_third_ge`: for `n = 2ᵐ`,
  `σₙ² ≥ (2/9)/n² > 0` for `f = 1_{[0,1/3)}`.
* `abs_normalised_error_indicator_le`: `|(μ̂ₙ − μ)/σₙ| ≤ 3` for every realisation of the
  scrambled base-2 net with remainders in `[0,1)`.
* `not_tendstoInDistribution_owenNet_indicator` (**counterexample**): for `f = 1_{[0,1/3)}`,
  `(μ̂ₙ − μ)/σₙ` does not converge in distribution to any `N(m₀, v)`, `v ≠ 0`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- **Bounded variables have no normal limit**: if `|X k| ≤ M` a.s. for every `k`, then `X k` does
not converge in distribution to `Y ~ N(m₀, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_gaussian_of_abs_le {Ω : ℕ → Type*}
    {mΩ : ∀ k, MeasurableSpace (Ω k)} {P : (k : ℕ) → Measure (Ω k)}
    [∀ k, IsProbabilityMeasure (P k)] {X : (k : ℕ) → Ω k → ℝ} {M : ℝ}
    (hM : ∀ k, ∀ᵐ ω ∂(P k), |X k ω| ≤ M) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution X atTop Y P P' := by
  intro h
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_Ioi (a := M))
  have hzero : ∀ k, ((P k).map (X k)) (Ioi M) = 0 := by
    intro k
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable k) measurableSet_Ioi,
      measure_eq_zero_iff_ae_notMem]
    filter_upwards [hM k] with ω hω
    intro hmem
    rw [mem_preimage, mem_Ioi] at hmem
    exact absurd (hω.trans' (le_abs_self _)) (not_le.2 hmem)
  change (P'.map Y) (Ioi M) ≤ atTop.liminf fun k ↦ ((P k).map (X k)) (Ioi M) at hle
  rw [funext hzero, liminf_const, nonpos_iff_eq_zero] at hle
  exact ne_gaussianReal_of_measure_Ioi_eq_zero hle m₀ hv hY.map_eq

/-- `Σ_{j<n} 1{j < k} = min n k`. -/
theorem sum_range_ite_lt (n k : ℕ) :
    ∑ j ∈ Finset.range n, (if j < k then (1 : ℕ) else 0) = min n k := by
  induction n with
  | zero => rw [Finset.sum_range_zero, Nat.zero_min]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : n < k
      · simp only [h, ↓reduceIte]
        omega
      · simp only [h, ↓reduceIte]
        omega

/-- `Σ_{i : Fin n} 1{i < k} = min n k`, in `ℝ`. -/
theorem sum_fin_ite_lt (n k : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) < k then (1 : ℝ) else 0) = (min n k : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if j < k then (1 : ℝ) else 0) n, ← sum_range_ite_lt,
    Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  by_cases h : j < k
  · simp only [h, ↓reduceIte, Nat.cast_one]
  · simp only [h, ↓reduceIte, Nat.cast_zero]

/-- **One boundary cell**: for points `xᵢ ∈ [i/n, (i+1)/n)` and `c ∈ [0,1]`,
`|Σᵢ 1{xᵢ < c} − n c| ≤ 1`. -/
theorem abs_sum_indicator_sub_le {n : ℕ} (hn : n ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {x : Fin n → ℝ} (hx : ∀ i : Fin n, x i ∈ stratum n i) :
    |∑ i, (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) - n * c| ≤ 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set k : ℕ := ⌊(n : ℝ) * c⌋₊ with hk
  have hnc0 : 0 ≤ (n : ℝ) * c := mul_nonneg hn'.le hc0
  have hk1 : (k : ℝ) ≤ n * c := Nat.floor_le hnc0
  have hk2 : (n : ℝ) * c < k + 1 := Nat.lt_floor_add_one _
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := hk1.trans (by nlinarith)
    exact_mod_cast this
  have hlo : ∀ i : Fin n, (if (i : ℕ) < k then (1 : ℝ) else 0) ≤
      (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) := by
    intro i
    by_cases h : (i : ℕ) < k
    · simp only [h, ↓reduceIte]
      rw [indicator_of_mem]
      have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
      have hx2 := (hx i).2
      rw [mem_Iio]
      calc x i < ((i : ℝ) + 1) / n := hx2
        _ ≤ k / n := div_le_div_of_nonneg_right hi hn'.le
        _ ≤ c := by rw [div_le_iff₀ hn']; linarith
    · simp only [h, ↓reduceIte]
      exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hhi : ∀ i : Fin n, (Iio c).indicator (fun _ ↦ (1 : ℝ)) (x i) ≤
      (if (i : ℕ) < k + 1 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : (i : ℕ) < k + 1
    · simp only [h, ↓reduceIte]
      exact indicator_le_self' (fun _ _ ↦ zero_le_one) _
    · simp only [h, ↓reduceIte]
      rw [indicator_of_notMem]
      have hi : (k : ℝ) + 1 ≤ i := by
        have : k + 1 ≤ (i : ℕ) := by omega
        exact_mod_cast this
      have hx1 := (hx i).1
      rw [mem_Iio, not_lt]
      calc c ≤ ((k : ℝ) + 1) / n := by rw [le_div_iff₀ hn']; linarith
        _ ≤ i / n := div_le_div_of_nonneg_right hi hn'.le
        _ ≤ x i := hx1
  have hS1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hlo i
  have hS2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hhi i
  rw [sum_fin_ite_lt, Nat.min_eq_right hkn] at hS1
  rw [sum_fin_ite_lt] at hS2
  have hmin : ((min n (k + 1) : ℕ) : ℝ) ≤ k + 1 := by
    have : min n (k + 1) ≤ k + 1 := Nat.min_le_right _ _
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- **The variance of an indicator**: `Var_{u ~ U[0,1)} 1{u < p} = p (1 − p)` for `p ∈ [0,1]`. -/
theorem variance_indicator_uniformIco {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Var[(Iio p).indicator (fun _ ↦ (1 : ℝ)); uniformIco] = p * (1 - p) := by
  have := isProbabilityMeasure_uniformIco
  set g : ℝ → ℝ := (Iio p).indicator (fun _ ↦ (1 : ℝ)) with hg
  have hgm : Measurable g := measurable_const.indicator measurableSet_Iio
  have hgL : MemLp g 2 uniformIco := MemLp.of_bound hgm.aestronglyMeasurable 1
    (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, hg]
      by_cases h : x ∈ Iio p
      · rw [indicator_of_mem h, abs_one]
      · rw [indicator_of_notMem h, abs_zero]
        exact zero_le_one)
  have hsq : g ^ 2 = g := by
    funext x
    rw [Pi.pow_apply, hg]
    by_cases h : x ∈ Iio p
    · rw [indicator_of_mem h, one_pow]
    · rw [indicator_of_notMem h, zero_pow two_ne_zero]
  have hint : ∫ x, g x ∂uniformIco = p := by
    have h1 : g = (Iio p).indicator 1 := rfl
    rw [h1, integral_indicator_one measurableSet_Iio]
    change (volume.restrict (Ico (0 : ℝ) 1)).real (Iio p) = p
    rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
    have hset : Iio p ∩ Ico (0 : ℝ) 1 = Ico 0 p := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, lt_of_lt_of_le h2 hp1⟩
    rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal hp0]
  rw [variance_eq_sub hgL, hsq]
  change ∫ x, g x ∂uniformIco - (∫ x, g x ∂uniformIco) ^ 2 = _
  rw [hint]
  ring

/-- `2ᵐ mod 3 ∈ {1, 2}`. -/
theorem two_pow_mod_three (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide

/-- The integrand of the counterexample, `f = 1_{[0,1/3)}` (on `[0,1)`). -/
noncomputable def indicatorThird : ℝ → ℝ := (Iio (1 / 3 : ℝ)).indicator fun _ ↦ 1

/-- `∫₀¹ 1_{[0,1/3)} = 1/3`. -/
theorem integral_indicatorThird : ∫ x, indicatorThird x ∂uniformIco = 1 / 3 := by
  have := isProbabilityMeasure_uniformIco
  have h1 : indicatorThird = (Iio (1 / 3 : ℝ)).indicator 1 := rfl
  rw [h1, integral_indicator_one measurableSet_Iio]
  change (volume.restrict (Ico (0 : ℝ) 1)).real (Iio (1 / 3)) = 1 / 3
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
  have hset : Iio (1 / 3 : ℝ) ∩ Ico (0 : ℝ) 1 = Ico 0 (1 / 3) := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by norm_num)]

/-- **The variance is non-degenerate**: for `n = 2ᵐ`, `σₙ² ≥ (2/9)/n²` for `f = 1_{[0,1/3)}`
(the cell containing `1/3` contributes `p(1 − p) = 2/9`, `p = frac(n/3) ∈ {1/3, 2/3}`). -/
theorem stratVar_indicator_third_ge (m : ℕ) :
    2 / 9 / ((2 ^ m : ℕ) : ℝ) ^ 2 ≤ stratVar (2 ^ m) indicatorThird := by
  have := isProbabilityMeasure_uniformIco
  set n : ℕ := 2 ^ m with hn
  have hn0 : n ≠ 0 := pow_ne_zero m two_ne_zero
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set k : ℕ := n / 3 with hk
  set r : ℕ := n % 3 with hr
  have hdiv : 3 * k + r = n := Nat.div_add_mod n 3
  have hr12 : r = 1 ∨ r = 2 := two_pow_mod_three m
  have hkn : k < n := by omega
  set p : ℝ := (r : ℝ) / 3 with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by norm_num : (0 : ℝ) < 3)]
    have : r ≤ 3 := by omega
    exact_mod_cast this
  have hpp : p * (1 - p) = 2 / 9 := by
    rcases hr12 with h | h <;> rw [hp, h] <;> norm_num
  -- the cell `k` function equals `1{u < p}` on `[0,1)`
  have hcell : (fun u ↦ indicatorThird (stratumMap n k u)) =ᵐ[uniformIco]
      (Iio p).indicator (fun _ ↦ (1 : ℝ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ico (fun u _ ↦ ?_)
    have hiff : stratumMap n k u < 1 / 3 ↔ u < p := by
      have hnr : (n : ℝ) = 3 * k + r := by exact_mod_cast hdiv.symm
      simp only [stratumMap, hp]
      rw [div_lt_iff₀ hn', hnr]
      constructor <;> intro h <;> linarith
    change (Iio (1 / 3 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (stratumMap n k u) =
      (Iio p).indicator (fun _ ↦ (1 : ℝ)) u
    by_cases h : u < p
    · rw [indicator_of_mem (mem_Iio.2 (hiff.2 h)), indicator_of_mem (mem_Iio.2 h)]
    · rw [indicator_of_notMem (fun h' ↦ h (hiff.1 (mem_Iio.1 h'))),
        indicator_of_notMem (fun h' ↦ h (mem_Iio.1 h'))]
  have hVk : Var[fun u ↦ indicatorThird (stratumMap n (⟨k, hkn⟩ : Fin n) u); uniformIco] =
      2 / 9 := by
    rw [variance_congr hcell, variance_indicator_uniformIco hp0 hp1, hpp]
  unfold stratVar
  have hle : Var[fun u ↦ indicatorThird (stratumMap n (⟨k, hkn⟩ : Fin n) u); uniformIco] ≤
      ∑ i : Fin n, Var[fun u ↦ indicatorThird (stratumMap n i u); uniformIco] :=
    Finset.single_le_sum (f := fun i : Fin n ↦
      Var[fun u ↦ indicatorThird (stratumMap n i u); uniformIco])
      (fun i _ ↦ variance_nonneg _ _) (Finset.mem_univ _)
  rw [hVk] at hle
  rw [inv_pow, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right hle (sq_nonneg _)

/-- **The normalised error is bounded by `3`**: for every tree and every remainders `r` in
`[0,1)`, the base-2 scrambled net with `f = 1_{[0,1/3)}` has `|(μ̂ₙ − μ)/σₙ| ≤ 3`, `n = 2ᵐ`. -/
theorem abs_normalised_error_indicator_le {m : ℕ} (T : OwenTree 2 m) {r : Fin (2 ^ m) → ℝ}
    (hr : ∀ k, r k ∈ Ico (0 : ℝ) 1) :
    |(sampleMean (2 ^ m) indicatorThird (owenNet T r) - ∫ x, indicatorThird x ∂uniformIco) /
      Real.sqrt (stratVar (2 ^ m) indicatorThird)| ≤ 3 := by
  have hn0 : 2 ^ m ≠ 0 := pow_ne_zero m two_ne_zero
  have hn' : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set x : Fin (2 ^ m) → ℝ := stratPoints (2 ^ m) (owenRemainder T r) with hx
  have hxmem : ∀ i : Fin (2 ^ m), x i ∈ stratum (2 ^ m) i := by
    intro i
    have h := stratumMap_preimage_stratum hn0 i
    have hmem : owenRemainder T r i ∈ stratumMap (2 ^ m) i ⁻¹' stratum (2 ^ m) i := by
      rw [h]
      exact hr _
    exact hmem
  have hsum := abs_sum_indicator_sub_le hn0 (c := 1 / 3) (by norm_num) (by norm_num) hxmem
  have herr : |sampleMean (2 ^ m) indicatorThird x - 1 / 3| ≤ 1 / ((2 ^ m : ℕ) : ℝ) := by
    have heq : sampleMean (2 ^ m) indicatorThird x - 1 / 3 =
        (∑ i, (Iio (1 / 3 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (x i) -
          ((2 ^ m : ℕ) : ℝ) * (1 / 3)) / ((2 ^ m : ℕ) : ℝ) := by
      unfold sampleMean
      rw [indicatorThird]
      field_simp
    rw [heq, abs_div, abs_of_pos hn']
    exact div_le_div_of_nonneg_right hsum hn'.le
  have hs := stratVar_indicator_third_ge m
  have hsq : 1 / (3 * ((2 ^ m : ℕ) : ℝ)) ≤ Real.sqrt (stratVar (2 ^ m) indicatorThird) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hs
    rw [div_pow, mul_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((2 ^ m : ℕ) : ℝ)]
  have hspos : 0 < Real.sqrt (stratVar (2 ^ m) indicatorThird) := lt_of_lt_of_le (by positivity) hsq
  rw [sampleMean_owenNet_eq_stratPoints, integral_indicatorThird, abs_div, abs_of_pos hspos,
    div_le_iff₀ hspos]
  calc |sampleMean (2 ^ m) indicatorThird x - 1 / 3| ≤ 1 / ((2 ^ m : ℕ) : ℝ) := herr
    _ = 3 * (1 / (3 * ((2 ^ m : ℕ) : ℝ))) := by field_simp
    _ ≤ 3 * Real.sqrt (stratVar (2 ^ m) indicatorThird) := by linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {mT : ∀ m, MeasurableSpace (OwenTree 2 m)} [∀ m, DiscreteMeasurableSpace (OwenTree 2 m)]

/-- **Counterexample to "a standard CLT applies" without smoothness** (post #2): for the
indicator `f = 1_{[0,1/3)}` and the base-2 Owen-scrambled net (any trees, remainders
`R m ~ U[0,1)^(2ᵐ)`), the variance is non-degenerate (`stratVar_indicator_third_ge`) but the
normalised error `(μ̂ₙ − μ)/σₙ` does not converge in distribution to any `N(m₀, v)`, `v ≠ 0`. -/
theorem not_tendstoInDistribution_owenNet_indicator {P : Measure Ω} [IsProbabilityMeasure P]
    {T : (m : ℕ) → Ω → OwenTree 2 m} {R : (m : ℕ) → Ω → Fin (2 ^ m) → ℝ}
    (hRlaw : ∀ m, HasLaw (R m) (uniformCube (2 ^ m)) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (m₀ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal m₀ v) P') :
    ¬ TendstoInDistribution (fun m ω ↦
      (sampleMean (2 ^ m) indicatorThird (owenNet (T m ω) (R m ω)) -
        ∫ x, indicatorThird x ∂uniformIco) / Real.sqrt (stratVar (2 ^ m) indicatorThird))
      atTop Y (fun _ ↦ P) P' := by
  refine not_tendstoInDistribution_gaussian_of_abs_le (M := 3) (fun m ↦ ?_) m₀ hv hY
  have hall : ∀ k : Fin (2 ^ m), ∀ᵐ ω ∂P, R m ω k ∈ Ico (0 : ℝ) 1 := fun k ↦
    ae_mem_Ico_of_hasLaw ((hasLaw_eval_uniformCube k).comp (hRlaw m))
  filter_upwards [ae_all_iff.2 hall] with ω hω
  exact abs_normalised_error_indicator_le (T m ω) hω

end RQMCMarkov.OwenScrambling
