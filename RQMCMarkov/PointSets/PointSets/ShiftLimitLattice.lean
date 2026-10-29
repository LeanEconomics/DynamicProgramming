/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PointSets.ShiftLimit
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# The randomly shifted lattice `{fract (i/n + U)}` and the common-shift rule (post #2)

The rank-1 lattice rule with generator `1` in one dimension is `{i/n : i < n}`; its random shift
modulo 1 is `{fract (i/n + U)}`, `U ~ U[0,1)`, whose points are each marginally `U[0,1)`
(requirement (i), `measurePreserving_fract_add`). This module identifies it with the
common-shift stratified rule `(i + V)/n` of `Stratified` and `ShiftLimit`, with `V = fract (n U)`,
and transfers the limit theorems.

## Main results

* `sampleMean_fract_lattice`: for every `u`,
  `(1/n) Σᵢ f(fract (i/n + u)) = (1/n) Σᵢ f((i + fract (n u))/n)` (the two point sets coincide).
* `measurePreserving_fract_natCast_mul`, `hasLaw_fract_natCast_mul`: `u ↦ fract (n u)` preserves
  `U[0,1)` (via Haar measure on the circle `ℝ/ℤ`, `measurePreserving_zsmul`).
* `hasLaw_scaled_error_id_lattice`: for `f(x) = x`, the scaled lattice error
  `n (μ̂ₙ − 1/2) = fract (n U) − 1/2` is `U[−1/2, 1/2)` for every `n ≥ 1`.
* `tendstoInDistribution_scaled_error_lattice`: for measurable `f`, `C¹` on `[0,1]`, the scaled
  lattice error converges in distribution to `(f(1) − f(0)) (U − 1/2)`;
  `not_tendstoInDistribution_scaled_error_lattice_gaussian`: and not to any non-degenerate normal.
* `fract_natCast_mul_stratumMap`, `variance_commonShift_sawtooth`,
  `mc_variance_lt_commonShift_sawtooth`: for the sawtooth `f(x) = fract (n x)` the shifted lattice
  (common shift) has variance `1/12`, `n` times the MC variance `1/(12 n)`.

**Correction.** Posts #1–#2 say RQMC gives a "low-variance estimator" and that "RQMC is much
lower variance than the MC". For independent stratification this holds for every `f ∈ L²`
(`variance_stratified_le_mc`), but not for the randomly shifted lattice: for each `n ≥ 2` the
sawtooth `f(x) = fract (n x)` makes its variance `n` times the MC variance
(`mc_variance_lt_commonShift_sawtooth`). The gain of a shifted lattice depends on the smoothness
of `f` (`variance_commonShift_le_lipschitz`: `O(n^{-2})` for Lipschitz `f`, uniformly in `n` only
through the Lipschitz constant, which is `n` for the sawtooth).

**Remark (not formalised).** For the lattice labelling the convergence is only in distribution:
`n (μ̂ₙ − 1/2) = fract (n U) − 1/2` does not converge almost surely, since `fract (n U)` is
equidistributed for irrational `U` (Weyl). The labelling `(i + U)/n` of `ShiftLimit` gives the
same law for every `n` and converges almost surely.
-/

namespace RQMCMarkov.PointSets

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The randomly shifted lattice is the common-shift rule**: for every `u`,
`(1/n) Σᵢ f(fract (i/n + u)) = (1/n) Σᵢ f((i + fract (n u))/n)`. -/
theorem sampleMean_fract_lattice {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (u : ℝ) :
    sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + u)) =
      sampleMean n f (fun i ↦ stratumMap n i (Int.fract ((n : ℝ) * u))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set m : ℤ := ⌊(n : ℝ) * u⌋ with hm
  set v : ℝ := Int.fract ((n : ℝ) * u) with hvdef
  have hv : (n : ℝ) * u = m + v := (Int.floor_add_fract _).symm
  have hv0 : 0 ≤ v := Int.fract_nonneg _
  have hv1 : v < 1 := Int.fract_lt_one _
  set r : Fin n → ℤ := fun i ↦ ((i : ℤ) + m) % (n : ℤ) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ Int.emod_nonneg _ hnZ.ne'
  have hrn : ∀ i, r i < n := fun i ↦ Int.emod_lt_of_pos _ hnZ
  set σ : Fin n → Fin n := fun i ↦ ⟨(r i).toNat, by have := hr0 i; have := hrn i; omega⟩ with hσ
  have hσval : ∀ i, ((σ i : ℕ) : ℝ) = (r i : ℝ) := by
    intro i
    have h1 : (((r i).toNat : ℕ) : ℤ) = r i := Int.toNat_of_nonneg (hr0 i)
    have h2 : (((r i).toNat : ℕ) : ℝ) = ((((r i).toNat : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
    change (((r i).toNat : ℕ) : ℝ) = _
    rw [h2, h1]
  have hfract : ∀ i : Fin n, Int.fract ((i : ℝ) / n + u) = stratumMap n (σ i) v := by
    intro i
    have hdec : (r i : ℝ) + n * (((i : ℤ) + m) / n : ℤ) = (i : ℝ) + m := by
      have := Int.emod_add_mul_ediv ((i : ℤ) + m) n
      have h' : ((((i : ℤ) + m) % n + n * (((i : ℤ) + m) / n) : ℤ) : ℝ) = (((i : ℤ) + m : ℤ) : ℝ) :=
        by rw [this]
      push_cast at h'
      rw [hr]
      exact h'
    have hri0 : (0 : ℝ) ≤ r i := by exact_mod_cast hr0 i
    have hrin : (r i : ℝ) + 1 ≤ n := by
      have : r i + 1 ≤ n := hrn i
      exact_mod_cast this
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, ((i : ℤ) + m) / n, ?_⟩
    · simp only [stratumMap]
      rw [hσval]
      positivity
    · simp only [stratumMap]
      rw [hσval, div_lt_one hn']
      linarith
    · simp only [stratumMap]
      rw [hσval]
      field_simp
      linarith
  have hinj : Function.Injective σ := by
    intro i j hij
    have h1 : (r i).toNat = (r j).toNat := congrArg Fin.val hij
    have h2 : r i = r j := by
      rw [← Int.toNat_of_nonneg (hr0 i), ← Int.toNat_of_nonneg (hr0 j), h1]
    have h3 : ((i : ℤ) + m) ≡ ((j : ℤ) + m) [ZMOD n] := h2
    have h4 : (i : ℤ) ≡ (j : ℤ) [ZMOD n] := Int.ModEq.add_right_cancel' m h3
    have hi : ((i : ℕ) : ℤ) % n = (i : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast i.isLt)
    have hj : ((j : ℕ) : ℤ) % n = (j : ℤ) :=
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast j.isLt)
    have h5 : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
      have : ((i : ℕ) : ℤ) % n = ((j : ℕ) : ℤ) % n := h4
      rw [hi, hj] at this
      exact this
    exact Fin.ext (by exact_mod_cast h5)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  unfold sampleMean
  congr 1
  rw [Finset.sum_congr rfl (fun i _ ↦ congrArg f (hfract i))]
  exact hbij.sum_comp (fun j : Fin n ↦ f (stratumMap n j v))

/-- **`u ↦ fract (n u)` preserves the uniform law** on `[0,1)`, for every `n ≥ 1`. -/
theorem measurePreserving_fract_natCast_mul {n : ℕ} (hn : n ≠ 0) :
    MeasurePreserving (fun u ↦ Int.fract ((n : ℝ) * u)) uniformIco uniformIco := by
  have hm : Measurable fun u : ℝ ↦ Int.fract ((n : ℝ) * u) :=
    measurable_fract.comp (measurable_const_mul _)
  refine ⟨hm, ?_⟩
  set h : UnitAddCircle → ℝ := fun x ↦ ((AddCircle.equivIco (1 : ℝ) 0 x : Ico (0 : ℝ) (0 + 1)) : ℝ)
    with hh
  have hhm : Measurable h :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hfr : (Int.fract : ℝ → ℝ) = h ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext x
    simp only [hh, Function.comp_apply]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  have hz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hcomp : (fun u : ℝ ↦ Int.fract ((n : ℝ) * u)) =
      h ∘ (fun x : UnitAddCircle ↦ (n : ℤ) • x) ∘ ((↑) : ℝ → UnitAddCircle) := by
    funext u
    rw [hfr]
    simp only [Function.comp_apply]
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast]
  have hid : uniformIco.map Int.fract = uniformIco := by
    have hae : Int.fract =ᵐ[uniformIco] id :=
      ae_restrict_of_forall_mem measurableSet_Ico (fun x hx ↦ Int.fract_eq_self.2 hx)
    rw [Measure.map_congr hae, Measure.map_id]
  have hcirc : (volume.restrict (Ioc (0 : ℝ) 1)).map ((↑) : ℝ → UnitAddCircle) = volume := by
    have := (UnitAddCircle.measurePreserving_mk 0).map_eq
    rwa [zero_add] at this
  have hzm := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hz).measurable
  rw [hcomp, ← Measure.map_map hhm (hzm.comp AddCircle.measurable_mk'),
    ← Measure.map_map hzm AddCircle.measurable_mk',
    uniformIco_eq_restrict_Ioc, hcirc,
    (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hz).map_eq, ← hcirc,
    Measure.map_map hhm AddCircle.measurable_mk', ← hfr, ← uniformIco_eq_restrict_Ioc,
    hid]

/-- If `U ~ U[0,1)` then `fract (n U) ~ U[0,1)`. -/
theorem hasLaw_fract_natCast_mul {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) : HasLaw (fun ω ↦ Int.fract ((n : ℝ) * U ω)) uniformIco P :=
  (measurePreserving_fract_natCast_mul hn).fun_comp_hasLaw hU

/-- **The scaled lattice error for `f(x) = x` is `U[−1/2, 1/2)` for every `n ≥ 1`**: with
`U ~ U[0,1)`, `n ((1/n) Σᵢ fract (i/n + U) − 1/2) = fract (n U) − 1/2`. -/
theorem hasLaw_scaled_error_id_lattice {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    HasLaw (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - 1 / 2))
      (volume.restrict (Ico (-(1 / 2) : ℝ) (1 / 2))) P := by
  have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
      1 / 2)) = fun ω ↦ (n : ℝ) * (sampleMean n id (fun i ↦ stratumMap n i
        (Int.fract ((n : ℝ) * U ω))) - 1 / 2) := by
    funext ω
    rw [sampleMean_fract_lattice hn]
  rw [hfun]
  exact hasLaw_scaled_error_id hn (hasLaw_fract_natCast_mul hn hU)

/-- **Convergence in distribution of the scaled lattice error**: for measurable `f`, `C¹` on
`[0,1]`, and `U ~ U[0,1)`, `n ((1/n) Σᵢ f(fract (i/n + U)) − ∫₀¹ f) ⇒ (f(1) − f(0)) (U − 1/2)`. -/
theorem tendstoInDistribution_scaled_error_lattice {f f' : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop (fun ω ↦ (f 1 - f 0) * (U ω - 1 / 2)) (fun _ ↦ P) P := by
  have hS := tendstoInDistribution_scaled_error hfm hf hf' hU
  set G : ℕ → ℝ → ℝ := fun n u ↦ (n : ℝ) *
    (sampleMean n f (fun i ↦ stratumMap n i u) - ∫ x in (0 : ℝ)..1, f x) with hG
  have hGm : ∀ n, Measurable (G n) := fun n ↦
    ((measurable_sampleMean_stratumMap hfm n).sub_const _).const_mul _
  have hlaw : ∀ n : ℕ, n ≠ 0 →
      P.map (fun ω ↦ (n : ℝ) * (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
        ∫ x in (0 : ℝ)..1, f x)) = P.map (fun ω ↦ G n (U ω)) := by
    intro n hn
    have hfun : (fun ω ↦ (n : ℝ) * (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) -
        ∫ x in (0 : ℝ)..1, f x)) = G n ∘ (fun ω ↦ Int.fract ((n : ℝ) * U ω)) := by
      funext ω
      simp only [hG, Function.comp_apply]
      rw [sampleMean_fract_lattice hn]
    have hV := hasLaw_fract_natCast_mul hn hU
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable (hGm n).aemeasurable hV.aemeasurable,
      hV.map_eq, ← hU.map_eq, AEMeasurable.map_map_of_aemeasurable (hGm n).aemeasurable
        hU.aemeasurable]
    rfl
  have hmeasL : ∀ n : ℕ, AEMeasurable (fun ω ↦ (n : ℝ) *
      (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x)) P := by
    intro n
    have hm : Measurable fun u : ℝ ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + u)) - ∫ x in (0 : ℝ)..1, f x) := by
      change Measurable fun u : ℝ ↦ (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        f (Int.fract ((i : ℝ) / n + u)) - ∫ x in (0 : ℝ)..1, f x)
      refine Measurable.const_mul (Measurable.sub_const (Measurable.const_mul ?_ _) _) _
      exact Finset.measurable_fun_sum _ (fun i _ ↦
        (hfm.comp (measurable_fract.comp (measurable_const_add _)) :))
    exact hm.comp_aemeasurable hU.aemeasurable
  refine ⟨hmeasL, hS.aemeasurable_limit, ?_⟩
  refine (hS.tendsto).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact Subtype.ext (hlaw n hn).symm

/-- **The randomly shifted lattice is not asymptotically normal**: the scaled lattice error
does not converge in distribution to any `N(m, v)` with `v ≠ 0`. -/
theorem not_tendstoInDistribution_scaled_error_lattice_gaussian {f f' : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ContinuousOn f' (Icc 0 1)) {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal m v) P') :
    ¬ TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        (sampleMean n f (fun i ↦ Int.fract ((i : ℝ) / n + U ω)) - ∫ x in (0 : ℝ)..1, f x))
      atTop Y (fun _ ↦ P) P' := by
  intro h
  have heq := tendstoInDistribution_unique _
    (tendstoInDistribution_scaled_error_lattice hfm hf hf' hU) h
  rw [hY.map_eq] at heq
  exact limit_law_ne_gaussianReal _ hU m hv heq

/-- The sawtooth `x ↦ fract (n x)` evaluated at the common-shift points `(i + u)/n`, `u ∈ [0,1)`,
is `u` at every point. -/
theorem fract_natCast_mul_stratumMap {n : ℕ} (hn : n ≠ 0) (i : ℕ) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) : Int.fract ((n : ℝ) * stratumMap n i u) = u := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : (n : ℝ) * stratumMap n i u = (i : ℝ) + u := by
    simp only [stratumMap]
    field_simp
  rw [h1, Int.fract_natCast_add, Int.fract_eq_self.2 hu]

/-- **Correction: a randomly shifted lattice can be worse than MC.** For every `n ≥ 1` and the
sawtooth `f(x) = fract (n x)` (period `1/n`), the common-shift estimate `(1/n) Σᵢ f((i + U)/n)`
equals `U` almost surely, so its variance is `1/12 = Var_{U[0,1)}(f)`: `n` times the MC variance
`Var_{U[0,1)}(f)/n` (`variance_sampleMean_iid`). -/
theorem variance_commonShift_sawtooth {n : ℕ} (hn : n ≠ 0) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω)); P] = 1 / 12 ∧
      Var[fun x ↦ Int.fract ((n : ℝ) * x); uniformIco] = 1 / 12 := by
  constructor
  · have hae : (fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω))) =ᵐ[P] U := by
      filter_upwards [ae_mem_Ico_of_hasLaw hU] with ω hω
      change (n : ℝ)⁻¹ * ∑ i : Fin n, Int.fract ((n : ℝ) * stratumMap n i (U ω)) = U ω
      rw [Finset.sum_congr rfl (fun (i : Fin n) _ ↦ fract_natCast_mul_stratumMap hn i hω),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_mul]
    rw [variance_congr hae, ← variance_id_map hU.aemeasurable, hU.map_eq]
    exact variance_uniformIco_id
  · rw [(measurePreserving_fract_natCast_mul hn).variance_fun_comp
      (f := fun u : ℝ ↦ u) measurable_id'.aemeasurable]
    exact variance_uniformIco_id

/-- **The randomly shifted lattice loses to MC on the sawtooth**: for `n ≥ 2` and
`f(x) = fract (n x)`, the MC variance `Var(f)/n = 1/(12 n)` is strictly smaller than the
common-shift variance `1/12`. (Independent stratification never loses:
`variance_stratified_le_mc`.) -/
theorem mc_variance_lt_commonShift_sawtooth {n : ℕ} (hn : 2 ≤ n) {P : Measure Ω} {U : Ω → ℝ}
    (hU : HasLaw U uniformIco P) :
    Var[fun x ↦ Int.fract ((n : ℝ) * x); uniformIco] / n <
      Var[fun ω ↦ sampleMean n (fun x ↦ Int.fract ((n : ℝ) * x))
        (fun i ↦ stratumMap n i (U ω)); P] := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := variance_commonShift_sawtooth hn0 hU
  rw [h1, h2]
  have h2' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by linarith)]
  linarith

end RQMCMarkov.PointSets
