/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.Unbiased
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ConditionalProbability

/-!
# Stratified sampling: variance at most MC, `O(n^{-3})` and `O(n^{-2})` rates (post #2)

Post #2: "RQMC using stratification would … use the same three sections and draw a random number
from each interval", and its codes do "stratification + random shift (it applies the same random
shift to all, rather than doing a different shift for each, both are valid)". Reading, in one
dimension with strata `[i/n, (i+1)/n)`, `i < n`, and `stratumMap n i u = (i + u)/n`:

* (a) independent stratification: points `(i + Vᵢ)/n` with `V₀, …, V_{n-1}` i.i.d. `U[0,1)`;
* (b) common shift: points `(i + U)/n` with one `U ~ U[0,1)`.

Both are unbiased (`integral_sampleMean_stratified` in `Unbiased`, and
`integral_sampleMean_commonShift` here); "valid" is read as unbiased.

## Main results

* `stratumMap_eq_midpoint_add`, `midpoint_shift_mem`: the stratified point `(i + u)/n` is the
  midpoint `(2i + 1)/(2n)` plus a shift in `[−1/(2n), 1/(2n))` (post #2's `U(−1/6, 1/6)`, `n = 3`).
* `variance_stratified_eq`: for (a), `Var = n⁻² Σᵢ Var(f | stratum i)`, with
  `Var(f | stratum i) = Var[u ↦ f((i + u)/n); U[0,1)]`, for every `f ∈ L²`.
* `variance_stratified_le_mc`: for (a), `Var ≤ σ²/n`, the MC variance (proportional allocation
  never loses), for every `f ∈ L²`.
* `integral_sq_sub_half_uniformIco`: `∫₀¹ (u − 1/2)² du = 1/12`; `variance_le_of_lipschitz_half`.
* `variance_stratified_le_lipschitz`: for (a) and `K`-Lipschitz `f`, `Var ≤ K²/(12 n³)`, the
  "faster than MC" rate `O(n^{-3})` (RMSE `O(n^{-3/2})`).
* `variance_commonShift_le_lipschitz`: for (b) and `K`-Lipschitz `f`, `Var ≤ K²/(12 n²)`
  (RMSE `O(n^{-1})`).
* `variance_uniformIco_id`, `variance_stratified_id`, `variance_commonShift_id`,
  `variance_stratified_id_lt_commonShift_id`: for `f(x) = x`, (a) has variance `1/(12 n³)` and
  (b) has `1/(12 n²)`, so for `n ≥ 2` the common shift is strictly worse, by the factor `n`.
* `sum_cond_eq_of_partition`, `variance_sampleMean_partition_le`: the general statement — for any
  probability space `(E, μ)`, a finite measurable partition into `n` cells of measure `1/n`, and
  independent points `Xᵢ ~ μ[|Aᵢ]` (`μ` conditioned on cell `i`), `Var ≤ Var_μ(f)/n`.

**Precision.** Post #2 calls both randomizations "valid": both are unbiased, but they are not
equally good. Independent shifts give `O(n^{-3})` variance for Lipschitz `f`, while one common
shift gives only `O(n^{-2})`, and `f(x) = x` shows the `n^{-2}` rate is attained
(`variance_commonShift_id`). The common shift is the randomly shifted lattice rule with generator
`1` (see `ShiftLimit`).
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `stratumMap n i` is continuous. -/
theorem continuous_stratumMap (n i : ℕ) : Continuous (stratumMap n i) :=
  (continuous_const.add continuous_id).div_const _

/-- **A stratified point is the QMC midpoint plus a shift** (post #2):
`(i + u)/n = (2i + 1)/(2n) + (u − 1/2)/n`. -/
theorem stratumMap_eq_midpoint_add {n : ℕ} (hn : n ≠ 0) (i : ℕ) (u : ℝ) :
    stratumMap n i u = (2 * i + 1) / (2 * n) + (u - 1 / 2) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [stratumMap]
  field_simp
  ring

/-- The shift `(u − 1/2)/n`, `u ∈ [0,1)`, lies in `[−1/(2n), 1/(2n))`; for `n = 3` this is post
#2's `U(−1/6, 1/6)`. -/
theorem midpoint_shift_mem {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (u - 1 / 2) / n ∈ Ico (-(1 / (2 * n : ℝ))) (1 / (2 * n)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have heq : (u - 1 / 2) / n = (2 * u - 1) / (2 * n) := by
    field_simp
  rw [heq, mem_Ico, ← neg_div, div_le_div_iff_of_pos_right h2n, div_lt_div_iff_of_pos_right h2n]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- `∫₀¹ (u − 1/2)² du = 1/12`. -/
theorem integral_sq_sub_half_uniformIco : ∫ u, (u - 1 / 2) ^ 2 ∂uniformIco = 1 / 12 := by
  rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2), integral_pow]
  norm_num

/-- `∫₀¹ u du = 1/2`. -/
theorem integral_id_uniformIco : ∫ u, u ∂uniformIco = 1 / 2 := by
  rw [uniformIco_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

/-- A continuous function is integrable for `U[0,1)`. -/
theorem integrable_uniformIco_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g uniformIco :=
  (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set Ico_subset_Icc_self

/-- **Variance bound from a Lipschitz-type bound at the midpoint.** If
`|g(u) − g(1/2)| ≤ C |u − 1/2|` on `[0,1)`, then `Var_{U[0,1)}(g) ≤ C²/12`. -/
theorem variance_le_of_lipschitz_half {g : ℝ → ℝ} (hg : AEStronglyMeasurable g uniformIco)
    {C : ℝ} (hC : ∀ u ∈ Ico (0 : ℝ) 1, |g u - g (1 / 2)| ≤ C * |u - 1 / 2|) :
    Var[g; uniformIco] ≤ C ^ 2 / 12 := by
  have := isProbabilityMeasure_uniformIco
  rw [← variance_sub_const hg (g (1 / 2))]
  refine (variance_le_expectation_sq (hg.sub aestronglyMeasurable_const)).trans ?_
  have hint : Integrable (fun u : ℝ ↦ C ^ 2 * (u - 1 / 2) ^ 2) uniformIco :=
    integrable_uniformIco_of_continuous (by fun_prop)
  calc ∫ u, ((fun u ↦ g u - g (1 / 2)) ^ 2) u ∂uniformIco
      ≤ ∫ u, C ^ 2 * (u - 1 / 2) ^ 2 ∂uniformIco := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u ↦ sq_nonneg _) hint ?_
        refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu ↦ ?_)
        change (g u - g (1 / 2)) ^ 2 ≤ C ^ 2 * (u - 1 / 2) ^ 2
        have h0 : 0 ≤ |g u - g (1 / 2)| := abs_nonneg _
        calc (g u - g (1 / 2)) ^ 2 = |g u - g (1 / 2)| ^ 2 := (sq_abs _).symm
          _ ≤ (C * |u - 1 / 2|) ^ 2 := pow_le_pow_left₀ h0 (hC u hu) 2
          _ = C ^ 2 * (u - 1 / 2) ^ 2 := by rw [mul_pow, sq_abs]
    _ = C ^ 2 / 12 := by
        rw [integral_const_mul, integral_sq_sub_half_uniformIco]
        ring

/-- A Lipschitz function is in `L²(U[0,1))`. -/
theorem memLp_uniformIco_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (p : ℝ≥0∞) : MemLp f p uniformIco := by
  have := isProbabilityMeasure_uniformIco
  refine MemLp.of_bound hf.continuous.aestronglyMeasurable (|f 0| + K) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ ?_)
  have h1 : |f x - f 0| ≤ K * |x - 0| := by
    have := hf.dist_le_mul x 0
    rwa [Real.dist_eq, Real.dist_eq] at this
  have h2 : |x - 0| ≤ 1 := by
    rw [sub_zero, abs_of_nonneg hx.1]
    exact hx.2.le
  rw [Real.norm_eq_abs]
  calc |f x| = |f 0 + (f x - f 0)| := by ring_nf
    _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
    _ ≤ |f 0| + K * 1 := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)
    _ = |f 0| + K := by rw [mul_one]

/-- The stratum-`i` component of a `K`-Lipschitz `f` satisfies the midpoint bound with
constant `K/n`. -/
theorem abs_sub_stratumMap_half_le {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {n : ℕ}
    (hn : n ≠ 0) (i : ℕ) (u : ℝ) :
    |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| ≤ (K / n) * |u - 1 / 2| := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have := hf.dist_le_mul (stratumMap n i u) (stratumMap n i (1 / 2))
  rw [Real.dist_eq, Real.dist_eq] at this
  have heq : stratumMap n i u - stratumMap n i (1 / 2) = (u - 1 / 2) / n := by
    simp only [stratumMap]
    ring
  rw [heq, abs_div, abs_of_pos hn'] at this
  calc |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| ≤ K * (|u - 1 / 2| / n) := this
    _ = (K / n) * |u - 1 / 2| := by ring

/-- **Independent stratification, exact variance** (post #2): for `Vᵢ` i.i.d. `U[0,1)` and
`f ∈ L²`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) = n⁻² Σᵢ Var(f | stratum i)`. -/
theorem variance_stratified_eq {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P) {f : ℝ → ℝ}
    (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco] := by
  have hX : ∀ i : Fin n, AEMeasurable (fun ω ↦ stratumMap n i (V i ω)) P := fun i ↦
    (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable
  have hind' : iIndepFun (fun (i : Fin n) ω ↦ stratumMap n i (V i ω)) P :=
    hind.comp (fun i ↦ stratumMap n i) (fun i ↦ measurable_stratumMap n i)
  have hμ := sum_map_stratified hn hV
  rw [variance_sampleMean_of_sum_map_eq hX hind' hμ hf]
  congr 1
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  have hL := memLp_map_of_sum_map_eq hμ hf i
  have hmap : P.map (fun ω ↦ stratumMap n i (V i ω)) = uniformIco.map (stratumMap n i) := by
    rw [← (hV i).map_eq, AEMeasurable.map_map_of_aemeasurable
      (measurable_stratumMap n i).aemeasurable (hV i).aemeasurable]
    rfl
  rw [hmap] at hL ⊢
  rw [variance_map hL.aestronglyMeasurable.aemeasurable (measurable_stratumMap n i).aemeasurable]
  rfl

/-- **Independent stratification never does worse than MC** (post #2, proportional allocation):
for `Vᵢ` i.i.d. `U[0,1)` and every `f ∈ L²`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) ≤ σ²/n`, where
`σ² = Var_{U[0,1)}(f)` and `σ²/n` is the MC variance (`variance_sampleMean_iid`). -/
theorem variance_stratified_le_mc {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} (hf : MemLp f 2 uniformIco) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] ≤ Var[f; uniformIco] / n :=
  variance_sampleMean_le_of_sum_map_eq hn
    (fun i ↦ (measurable_stratumMap n i).comp_aemeasurable (hV i).aemeasurable)
    (hind.comp (fun i ↦ stratumMap n i) (fun i ↦ measurable_stratumMap n i))
    (sum_map_stratified hn hV) hf

/-- **Independent stratification, Lipschitz rate `O(n^{-3})`** (post #2): for `Vᵢ` i.i.d.
`U[0,1)` and `K`-Lipschitz `f`, `Var((1/n) Σᵢ f((i + Vᵢ)/n)) ≤ K²/(12 n³)`. -/
theorem variance_stratified_le_lipschitz {n : ℕ} (hn : n ≠ 0) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (V i ω)); P] ≤
      (K : ℝ) ^ 2 / (12 * n ^ 3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [variance_stratified_eq hn hV hind (memLp_uniformIco_of_lipschitz hf 2)]
  have hle : ∀ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco] ≤ (K / n) ^ 2 / 12 :=
    fun i ↦ variance_le_of_lipschitz_half
      (hf.continuous.comp (continuous_stratumMap n i)).aestronglyMeasurable
      (fun u _ ↦ abs_sub_stratumMap_half_le hf hn i u)
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, Var[fun u ↦ f (stratumMap n i u); uniformIco]
      ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, ((K : ℝ) / n) ^ 2 / 12 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hle i) (sq_nonneg _)
    _ = (K : ℝ) ^ 2 / (12 * n ^ 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **The common shift is unbiased** (post #2): with one `U ~ U[0,1)`,
`E[(1/n) Σᵢ f((i + U)/n)] = ∫₀¹ f`. -/
theorem integral_sampleMean_commonShift {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {f : ℝ → ℝ} (hf : Integrable f uniformIco) :
    ∫ ω, sampleMean n f (fun i ↦ stratumMap n i (U ω)) ∂P = ∫ x, f x ∂uniformIco :=
  integral_sampleMean_stratified hn (V := fun _ ↦ U) (fun _ ↦ hU) hf

/-- **The common shift, Lipschitz rate `O(n^{-2})`** (post #2): with one `U ~ U[0,1)` and
`K`-Lipschitz `f`, `Var((1/n) Σᵢ f((i + U)/n)) ≤ K²/(12 n²)`. -/
theorem variance_commonShift_le_lipschitz {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Var[fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (U ω)); P] ≤ (K : ℝ) ^ 2 / (12 * n ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set G : ℝ → ℝ := fun u ↦ sampleMean n f (fun i ↦ stratumMap n i u) with hG
  have hGc : Continuous G := by
    simp only [hG, sampleMean]
    exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦
      hf.continuous.comp (continuous_stratumMap n i)))
  have hfun : (fun ω ↦ sampleMean n f (fun i ↦ stratumMap n i (U ω))) = G ∘ U := rfl
  rw [hfun, ← variance_map (hU.map_eq ▸ hGc.aemeasurable) hU.aemeasurable, hU.map_eq]
  have hbound : ∀ u ∈ Ico (0 : ℝ) 1, |G u - G (1 / 2)| ≤ (K / n) * |u - 1 / 2| := by
    intro u _
    simp only [hG, sampleMean]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_inv, abs_of_pos hn']
    calc (n : ℝ)⁻¹ * |∑ i : Fin n, (f (stratumMap n i u) - f (stratumMap n i (1 / 2)))|
        ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |f (stratumMap n i u) - f (stratumMap n i (1 / 2))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hn'.le)
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (K / n) * |u - 1 / 2| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦
            abs_sub_stratumMap_half_le hf hn i u) (inv_nonneg.2 hn'.le)
      _ = (K / n) * |u - 1 / 2| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hn'.ne', one_mul]
  calc Var[G; uniformIco] ≤ ((K : ℝ) / n) ^ 2 / 12 :=
        variance_le_of_lipschitz_half hGc.aestronglyMeasurable hbound
    _ = (K : ℝ) ^ 2 / (12 * n ^ 2) := by
        field_simp

/-- `Var_{U[0,1)}(u) = 1/12`. -/
theorem variance_uniformIco_id : Var[fun u : ℝ ↦ u; uniformIco] = 1 / 12 := by
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_uniformIco,
    integral_sq_sub_half_uniformIco]

/-- `Var_{U[0,1)}(c + d u) = d²/12`. -/
theorem variance_uniformIco_affine (c d : ℝ) :
    Var[fun u : ℝ ↦ c + d * u; uniformIco] = d ^ 2 / 12 := by
  have := isProbabilityMeasure_uniformIco
  rw [variance_const_add (measurable_id'.const_mul d).aestronglyMeasurable c, variance_const_mul,
    variance_uniformIco_id]
  ring

/-- **Independent stratification for `f(x) = x`**: `Var = 1/(12 n³)`. -/
theorem variance_stratified_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {V : Fin n → Ω → ℝ}
    (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (V i ω)); P] = 1 / (12 * n ^ 3) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [variance_stratified_eq hn hV hind (memLp_uniformIco_of_lipschitz LipschitzWith.id 2)]
  have hi : ∀ i : Fin n, Var[fun u ↦ id (stratumMap n i u); uniformIco] = ((n : ℝ)⁻¹) ^ 2 / 12 := by
    intro i
    have hfun : (fun u ↦ id (stratumMap n i u)) = fun u : ℝ ↦ (i : ℝ) / n + (n : ℝ)⁻¹ * u := by
      funext u
      simp only [id, stratumMap]
      ring
    rw [hfun, variance_uniformIco_affine]
  rw [Finset.sum_congr rfl (fun i _ ↦ hi i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- **The common shift for `f(x) = x`**: `Var = 1/(12 n²)`, so the `n^{-2}` rate of
`variance_commonShift_le_lipschitz` is attained. -/
theorem variance_commonShift_id {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω)); P] = 1 / (12 * n ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set c : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, (i : ℝ) / n with hc
  have hG : (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) =
      fun u : ℝ ↦ c + (n : ℝ)⁻¹ * u := by
    funext u
    simp only [hc, sampleMean, id, stratumMap]
    rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ add_div (i : ℝ) u n), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hfun : (fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω))) =
      (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) ∘ U := rfl
  have hGm : Measurable (fun u ↦ sampleMean n id (fun i ↦ stratumMap n i u)) := by
    rw [hG]
    fun_prop
  rw [hfun, ← variance_map (hU.map_eq ▸ hGm.aemeasurable) hU.aemeasurable, hU.map_eq, hG,
    variance_uniformIco_affine]
  field_simp

/-- **The common shift is strictly worse for `f(x) = x`** once `n ≥ 2`:
`Var(independent) = 1/(12 n³) < 1/(12 n²) = Var(common shift)`. -/
theorem variance_stratified_id_lt_commonShift_id {n : ℕ} (hn : 2 ≤ n) {P : Measure Ω}
    {V : Fin n → Ω → ℝ} (hV : ∀ i, HasLaw (V i) uniformIco P) (hind : iIndepFun V P)
    {U : Ω → ℝ} (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (V i ω)); P] <
      Var[fun ω ↦ sampleMean n id (fun i ↦ stratumMap n i (U ω)); P] := by
  have hn0 : n ≠ 0 := by omega
  rw [variance_stratified_id hn0 hV hind, variance_commonShift_id hn0 hU]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 12 * n ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_left one_pos (by positivity) hpos]
  nlinarith

/-- **Cells of a partition with `μ`-measure `1/n`**: the conditional laws `μ[|Aᵢ]` sum to
`n • μ`. -/
theorem sum_cond_eq_of_partition {E : Type*} {mE : MeasurableSpace E} {μ : Measure E} {n : ℕ}
    {A : Fin n → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ)
    (hμA : ∀ i, μ (A i) = (n : ℝ≥0∞)⁻¹) :
    ∑ i, μ[|A i] = (n : ℝ≥0∞) • μ := by
  have hc : ∀ i, μ[|A i] = (n : ℝ≥0∞) • μ.restrict (A i) := fun i ↦ by
    rw [ProbabilityTheory.cond, hμA i, inv_inv]
  rw [Finset.sum_congr rfl (fun i _ ↦ hc i), ← Finset.smul_sum, ← Measure.sum_fintype,
    ← Measure.restrict_iUnion hdisj hA, hcover, Measure.restrict_univ]

/-- **Stratified sampling with proportional allocation never loses to MC**, in any dimension:
for a measurable partition `A₀, …, A_{n-1}` of `E` into cells of `μ`-measure `1/n` and independent
points `Xᵢ ~ μ[|Aᵢ]` (one uniform point in each cell when `μ` is uniform),
`Var((1/n) Σᵢ f(Xᵢ)) ≤ Var_μ(f)/n` for every `f ∈ L²(μ)`; the estimator is unbiased. -/
theorem variance_sampleMean_partition_le {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    {n : ℕ} (hn : n ≠ 0) {A : Fin n → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ)
    (hμA : ∀ i, μ (A i) = (n : ℝ≥0∞)⁻¹) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} (hX : ∀ i, HasLaw (X i) μ[|A i] P) (hind : iIndepFun X P)
    {f : E → ℝ} (hf : MemLp f 2 μ) :
    ∫ ω, sampleMean n f (fun i ↦ X i ω) ∂P = ∫ x, f x ∂μ ∧
      Var[fun ω ↦ sampleMean n f (fun i ↦ X i ω); P] ≤ Var[f; μ] / n := by
  have hsum : ∑ i, P.map (X i) = (n : ℝ≥0∞) • μ := by
    rw [Finset.sum_congr rfl (fun i _ ↦ (hX i).map_eq)]
    exact sum_cond_eq_of_partition hA hdisj hcover hμA
  have hμ : IsFiniteMeasure μ := by
    have h1 : μ univ = ∑ i, μ (A i) := by
      rw [← hcover, measure_iUnion hdisj hA, tsum_fintype]
    refine ⟨?_⟩
    rw [h1, Finset.sum_congr rfl (fun i _ ↦ hμA i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn)
        (ENNReal.natCast_ne_top n)]
    exact ENNReal.one_lt_top
  exact ⟨integral_sampleMean_of_sum_map_eq hn (fun i ↦ (hX i).aemeasurable) hsum
      (hf.integrable one_le_two),
    variance_sampleMean_le_of_sum_map_eq hn (fun i ↦ (hX i).aemeasurable) hind hsum hf⟩

end RQMCMarkov.PointSets
