/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.MonteCarlo
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.CompletePartialOrder

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
