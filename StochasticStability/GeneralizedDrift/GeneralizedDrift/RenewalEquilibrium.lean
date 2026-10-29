/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.RenewalKey

/-!
# Proposition 14.5.4 and the equilibrium renewal measure (MT §14.5)

Copied for Chapter 19 from the Chapter 14 project
(`FErgodicity/RenewalEquilibrium.lean`), with the
namespace changed to `MeynTweedie.GeneralizedDrift` and the imports to `GeneralizedDrift.*`.

Meyn and Tweedie, Proposition 14.5.4 and p. 357: the stationary delay `Γₑ = β⁻¹ Γ(y, ∞) dy`
(`fwdSkelInv Γ` normalised) has `Γₑ ∗ U = β⁻¹ μ_Leb` on `(0, ∞)`.

* **Proposition 14.5.4** (`proposition_14_5_4_renewal`, p. 357), (14.45): for a spread-out `Γ`
  with finite mean, first-epoch laws `Γ₁, Γ₂` on `(0, ∞)` with finite means and a bounded
  measurable `f` vanishing on `(−∞, 0)` with `f(t) → 0`, `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) −
  Γ₂ ∗ U ∗ g(t)| → 0` (from Proposition 14.5.3 and `proposition_14_5_4`).
* `renMeas_stationary`: `Γₑ ∗ U` is invariant under translation on `(0, ∞)`, since `Γₑ` is invariant
  for every skeleton (10.36) and (14.43) holds.
* `eq_mul_of_add_monotone`: an additive monotone function on `[0, ∞)` is linear.
* `renMeas_eqLaw_eq_smul`: `Γₑ ∗ U = c μ_Leb|_{(0, ∞)}` with `c = Γₑ ∗ U(0, 1]`.
* `secondLaw`, `renMeas_eq_add` (the renewal equation): `μ ∗ U = μ + (μ ∗ Γ) ∗ U`.
* `renMeas_eqLaw` (p. 357): `Γₑ ∗ U = β⁻¹ μ_Leb|_{(0, ∞)}`, with `β = ∫ y Γ(dy)` (`renMean`) and
  `Γₑ = β⁻¹ Γ[y, ∞) dy` (`eqLaw`). The constant comes from the renewal equation on `(0, t]`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- **Proposition 14.5.4** (MT p. 357), (14.45), for renewal measures: for a spread-out `Γ` on
`[0, ∞)` with finite mean, first-epoch laws `Γ₁, Γ₂` on `(0, ∞)` with finite means, and a bounded
measurable `f` vanishing on `(−∞, 0)` with `f(t) → 0` ((14.37), (14.39)),
`sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0`. -/
theorem proposition_14_5_4_renewal (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hs : IsSpreadOut Γ) (hm : ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞) (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (h₁ : μ₁ (Iic 0) = 0)
    (h₂ : μ₂ (Iic 0) = 0) (hm₁ : ∫⁻ x, ENNReal.ofReal x ∂μ₁ ≠ ∞)
    (hm₂ : ∫⁻ x, ENNReal.ofReal x ∂μ₂ ≠ ∞) {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ s < 0, f s = 0) {d : ℝ} (hfd : ∀ s, f s ≤ d) (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (convSupDiff f (renMeas Γ μ₁) (renMeas Γ μ₂)) atTop (𝓝 0) := by
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, heq⟩ := proposition_14_5_3 Γ hΓ0 hΓpos hs hm μ₁ μ₂ h₁ h₂ hm₁ hm₂
  have hloc : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Iic 0) = 0 → ∀ t,
      ∫⁻ u, ENNReal.ofReal (f (t - u)) ∂renMeas Γ μ ≠ ∞ := fun μ _ hμ t => by
    have hle : ∀ u, ENNReal.ofReal (f (t - u)) ≤ (Iic t).indicator (fun _ => ENNReal.ofReal d) u :=
      fun u => by
        by_cases hu : u ∈ Iic t
        · rw [indicator_of_mem hu]; exact ENNReal.ofReal_le_ofReal (hfd _)
        · rw [indicator_of_notMem hu, hf0 _ (by simp only [mem_Iic, not_le] at hu; linarith),
            ENNReal.ofReal_zero]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_indicator_const measurableSet_Iic]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0
        hΓpos)).ne')) (renMeas_Iic_le Γ μ hμ t))
  exact proposition_14_5_4 heq hf hfd hlim fun t => ⟨hloc μ₁ h₁ t, hloc μ₂ h₂ t⟩

/-! ### The stationary delay -/

/-- The mean `m = ∫ y Γ(dy)` of the increments. -/
noncomputable abbrev renMean : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal y ∂Γ

/-- The stationary delay `Γₑ = m⁻¹ Γ[y, ∞) dy` on `(0, ∞)` (MT (10.36)). -/
noncomputable abbrev eqLaw : Measure ℝ := (renMean Γ)⁻¹ • fwdSkelInv Γ

omit [IsProbabilityMeasure Γ] in
/-- `Γₑ` does not charge `(−∞, 0]`. -/
theorem eqLaw_Iic_zero : eqLaw Γ (Iic 0) = 0 := by
  rw [eqLaw, Measure.smul_apply, fwdSkelInv_Iic_zero Γ, smul_zero]

/-- **Stationarity of the equilibrium renewal process**: for `s ≥ 0` and `A ⊆ (s, ∞)`,
`Γₑ ∗ U(A) = Γₑ ∗ U(A − s)`. -/
theorem renMeas_stationary (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hm : renMean Γ ≠ ∞) {s : ℝ} (hs : 0 ≤ s) {A : Set ℝ} (hA : MeasurableSet A)
    (hAs : A ⊆ Ioi s) :
    renMeas Γ (eqLaw Γ) A = renMeas Γ (eqLaw Γ) ((fun u => u + s) ⁻¹' A) := by
  obtain ⟨hp, hinv⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have := isMarkovKernel_fwdSkelKernel Γ s
  have h := renMeas_eq_lintegral_skeleton Γ hΓ0 hΓpos (eqLaw Γ) (eqLaw_Iic_zero Γ) hs 1 hA
    (by rwa [Nat.cast_one, one_mul])
  rw [pow_one, hinv s hs] at h
  rw [h, renMeas_eq_lintegral Γ _ (A := (fun u => u + s) ⁻¹' A)
    ((measurable_id.add measurable_const) hA)]
  simp only [Nat.cast_one, one_mul]

/-- **Cauchy's equation**: an additive monotone function on `[0, ∞)` is linear. -/
theorem eq_mul_of_add_monotone {g : ℝ → ℝ} (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → g (s + t) = g s + g t)
    (hmono : MonotoneOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) : g t = t * g 1 := by
  have h0 : g 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at this
    linarith
  have hnat : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → g (n * s) = n * g s := fun n s hs => by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, h0]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ (by positivity) hs, ih, add_mul, one_mul]
  have hg1 : 0 ≤ g 1 := by
    rw [← h0]; exact hmono (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_le_one
  -- rational values
  have hrat : ∀ (p k : ℕ), 0 < k → g (p / k) = p / k * g 1 := fun p k hk => by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 := hnat k (p / k) (by positivity)
    rw [mul_div_cancel₀ _ hk'.ne'] at h1
    have h2 := hnat p 1 zero_le_one
    rw [mul_one] at h2
    rw [h2] at h1
    field_simp
    linarith
  -- squeeze between rationals with denominator `N`
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · obtain ⟨N, hN⟩ := exists_nat_gt ((g 1 + 1) / ε)
    have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    set p := ⌊t * N⌋₊
    have hp1 : t * N < p + 1 := Nat.lt_floor_add_one _
    have hle : g t ≤ g ((p + 1 : ℕ) / N) := hmono (mem_Ici.2 ht) (mem_Ici.2 (by positivity))
      (by rw [le_div_iff₀ hN0]; push_cast; linarith)
    rw [hrat _ _ (by exact_mod_cast hN0)] at hle
    have : ((p + 1 : ℕ) : ℝ) / N * g 1 ≤ t * g 1 + ε := by
      have h1 : ((p + 1 : ℕ) : ℝ) / N ≤ t + 1 / N := by
        rw [div_le_iff₀ hN0, add_mul, one_div, inv_mul_cancel₀ hN0.ne']; push_cast
        linarith [Nat.floor_le (show 0 ≤ t * N by positivity)]
      have h2 : g 1 / N ≤ ε := by
        rw [div_le_iff₀ hN0]
        have := (div_lt_iff₀ hε).1 hN
        nlinarith
      calc ((p + 1 : ℕ) : ℝ) / N * g 1 ≤ (t + 1 / N) * g 1 := mul_le_mul_of_nonneg_right h1 hg1
        _ = t * g 1 + g 1 / N := by ring
        _ ≤ t * g 1 + ε := by linarith
    linarith
  · obtain ⟨N, hN⟩ := exists_nat_gt ((g 1 + 1) / ε)
    have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    set p := ⌊t * N⌋₊
    have hp0 : (p : ℝ) ≤ t * N := Nat.floor_le (by positivity)
    have hp1 : t * N < p + 1 := Nat.lt_floor_add_one _
    have hle : g (p / N) ≤ g t := hmono (mem_Ici.2 (by positivity)) (mem_Ici.2 ht)
      (by rw [div_le_iff₀ hN0]; linarith)
    rw [hrat _ _ (by exact_mod_cast hN0)] at hle
    have h1 : t ≤ (p : ℝ) / N + 1 / N := by
      rw [← add_div, le_div_iff₀ hN0]; linarith
    have h2 : g 1 / N ≤ ε := by
      rw [div_le_iff₀ hN0]
      have := (div_lt_iff₀ hε).1 hN
      nlinarith
    calc t * g 1 ≤ ((p : ℝ) / N + 1 / N) * g 1 := mul_le_mul_of_nonneg_right h1 hg1
      _ = (p : ℝ) / N * g 1 + g 1 / N := by ring
      _ ≤ g t + ε := by linarith

/-- **The equilibrium renewal measure is a multiple of Lebesgue measure on `(0, ∞)`**:
`Γₑ ∗ U = c μ_Leb|_{(0, ∞)}` with `c = Γₑ ∗ U(0, 1]`. -/
theorem renMeas_eqLaw_eq_smul (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hm : renMean Γ ≠ ∞) :
    renMeas Γ (eqLaw Γ) = renMeas Γ (eqLaw Γ) (Ioc 0 1) • volume.restrict (Ioi 0) := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  set ρ := renMeas Γ (eqLaw Γ) with hρ
  have hfinIic : ∀ t, ρ (Iic t) ≠ ∞ := fun t => ne_top_of_le_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0
      hΓpos)).ne')) (renMeas_Iic_le Γ (eqLaw Γ) (eqLaw_Iic_zero Γ) t)
  have hfin : ∀ a b, ρ (Ioc a b) ≠ ∞ := fun a b =>
    ne_top_of_le_ne_top (hfinIic b) (measure_mono Ioc_subset_Iic_self)
  -- translation invariance on `(0, ∞)`
  have hshift : ∀ a b : ℝ, 0 ≤ a → ρ (Ioc a b) = ρ (Ioc 0 (b - a)) := fun a b ha => by
    rw [hρ, renMeas_stationary Γ hΓ0 hΓpos hm ha measurableSet_Ioc (fun x hx => hx.1)]
    congr 1
    ext u
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  set G : ℝ → ℝ := fun t => (ρ (Ioc 0 t)).toReal with hG
  have hadd : ∀ s t, 0 ≤ s → 0 ≤ t → G (s + t) = G s + G t := fun s t hs ht => by
    simp only [hG]
    rw [← Ioc_union_Ioc_eq_Ioc hs (le_add_of_nonneg_right ht),
      measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      hshift s (s + t) hs, add_sub_cancel_left, ENNReal.toReal_add (hfin _ _) (hfin _ _)]
  have hmono : MonotoneOn G (Ici 0) := fun s _ t _ hst =>
    ENNReal.toReal_mono (hfin _ _) (measure_mono (Ioc_subset_Ioc_right hst))
  have hlin : ∀ t, 0 ≤ t → ρ (Ioc 0 t) = ENNReal.ofReal t * ρ (Ioc 0 1) := fun t ht => by
    have h := eq_mul_of_add_monotone hadd hmono ht
    simp only [hG] at h
    rw [← ENNReal.ofReal_toReal (hfin 0 t), h, ENNReal.ofReal_mul ht,
      ENNReal.ofReal_toReal (hfin 0 1)]
  have hz : ρ (Iic 0) = 0 := renMeas_Iic_zero Γ hΓ0 hΓpos (eqLaw Γ) (eqLaw_Iic_zero Γ)
  have hnull : ∀ A, MeasurableSet A → ρ A = ρ (A ∩ Ioi 0) := fun A hA => by
    have e := measure_inter_add_sdiff A (measurableSet_Ioi (a := (0 : ℝ))) (μ := ρ)
    have h0 : ρ (A \ Ioi 0) = 0 :=
      measure_mono_null (fun x hx => (not_lt.1 (show ¬ (0 : ℝ) < x from hx.2) : x ≤ 0)) hz
    rw [h0, add_zero] at e
    exact e.symm
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => hfin a b) fun a b hab => ?_
  have hset : Ioc a b ∩ Ioi 0 = Ioc (max a 0) (max b 0) := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff, le_max_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, Or.inl h2⟩
    · rintro ⟨⟨h1, h3⟩, h2 | h2⟩
      · exact ⟨⟨h1, h2⟩, h3⟩
      · linarith
  rw [hnull _ measurableSet_Ioc, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    hset, smul_eq_mul, hshift _ _ (le_max_right a 0), Real.volume_Ioc,
    hlin _ (sub_nonneg.2 (max_le_max hab.le le_rfl)), mul_comm]


/-! ### The renewal equation and the constant `β⁻¹` -/

/-- The law of the second epoch `x + Y₀`: `μ ∗ Γ`. -/
noncomputable abbrev secondLaw (μ : Measure ℝ) : Measure ℝ := (μ.prod Γ).map fun q => q.1 + q.2

/-- The second epoch and the later increments are independent:
`(x + Y₀, (Y₁, Y₂, …))` has law `(μ ∗ Γ) ⊗ Γ^{⊗ℕ}`. -/
theorem prod_map_second_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ.prod (incr Γ)).map (fun p => (p.1 + p.2 0, tailSeq 1 p.2)) =
      (secondLaw Γ μ).prod (incr Γ) := by
  set ν := incr Γ
  have hHT : Measurable fun w : ℕ → ℝ => (w 0, tailSeq 1 w) :=
    (measurable_pi_apply 0).prodMk (measurable_tailSeq 1)
  have h1 : (μ.prod ν).map (Prod.map id fun w : ℕ → ℝ => (w 0, tailSeq 1 w)) =
      μ.prod (Γ.prod ν) := by
    rw [← Measure.map_prod_map _ _ measurable_id hHT, Measure.map_id, infinitePi_map_head_tail]
  have hmp := (measurePreserving_prodAssoc μ Γ ν).symm
  have hadd : Measurable fun q : ℝ × ℝ => q.1 + q.2 := measurable_fst.add measurable_snd
  have h2 : (fun p : ℝ × (ℕ → ℝ) => (p.1 + p.2 0, tailSeq 1 p.2)) =
      (Prod.map (fun q : ℝ × ℝ => q.1 + q.2) id) ∘
        ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℕ → ℝ)).symm ∘
          (Prod.map id fun w : ℕ → ℝ => (w 0, tailSeq 1 w))) := by
    funext p
    rfl
  rw [h2, ← Measure.map_map (hadd.prodMap measurable_id)
    (hmp.measurable.comp (measurable_id.prodMap hHT)),
    ← Measure.map_map hmp.measurable (measurable_id.prodMap hHT), h1, hmp.map_eq,
    ← Measure.map_prod_map _ _ hadd measurable_id, Measure.map_id]

/-- **The renewal equation**: `μ ∗ U = μ + (μ ∗ Γ) ∗ U`. -/
theorem renMeas_eq_add (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    renMeas Γ μ = μ + renMeas Γ (secondLaw Γ μ) := by
  have := (inferInstance : IsProbabilityMeasure (incr Γ))
  ext A hA
  rw [Measure.add_apply, renMeas_apply Γ μ hA, renMeas_apply Γ _ hA,
    tsum_eq_zero_add' ENNReal.summable]
  have hmeas : Measurable fun p : ℝ × (ℕ → ℝ) => (p.1 + p.2 0, tailSeq 1 p.2) :=
    (measurable_fst.add ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_tailSeq 1).comp measurable_snd)
  congr 1
  · -- the first epoch
    have e : {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (0 + 1) ∈ A} = A ×ˢ univ := by
      ext p
      simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true, zero_add, resEpoch_succ_eq,
        Finset.range_zero, Finset.sum_empty, add_zero]
    rw [e, Measure.prod_prod, measure_univ, mul_one]
  · -- the later epochs are those of the process started at the second epoch
    refine tsum_congr fun m => ?_
    have e : {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (m + 1 + 1) ∈ A} =
        (fun p : ℝ × (ℕ → ℝ) => (p.1 + p.2 0, tailSeq 1 p.2)) ⁻¹'
          {q | resEpoch q.1 q.2 (m + 1) ∈ A} := by
      ext p
      simp only [mem_ofPred_eq, mem_preimage, resEpoch_succ_eq, tailSeq]
      rw [Finset.sum_range_succ', add_comm (∑ i ∈ Finset.range m, p.2 (i + 1)) (p.2 0),
        ← add_assoc]
      simp only [add_comm 1]
    rw [e, ← Measure.map_apply hmeas (s := {q : ℝ × (ℕ → ℝ) | resEpoch q.1 q.2 (m + 1) ∈ A})
      ((measurable_resEpoch (m + 1)) hA), prod_map_second_tail]

/-- **`Γₑ ∗ U = β⁻¹ μ_Leb`** (MT p. 357): the equilibrium renewal measure is `m⁻¹` times Lebesgue
measure on `(0, ∞)`, where `m = ∫ y Γ(dy)`. The constant is identified from the renewal equation
`Γₑ ∗ U = Γₑ + (Γₑ ∗ Γ) ∗ U` on `(0, t]`. -/
theorem renMeas_eqLaw (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hm : renMean Γ ≠ ∞) :
    renMeas Γ (eqLaw Γ) = (renMean Γ)⁻¹ • volume.restrict (Ioi 0) := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have hρ := renMeas_eqLaw_eq_smul Γ hΓ0 hΓpos hm
  set c := renMeas Γ (eqLaw Γ) (Ioc 0 1) with hc
  suffices hcm : c = (renMean Γ)⁻¹ by rw [hρ, hcm]
  have hct : c ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne'))
    ((measure_mono Ioc_subset_Iic_self).trans (renMeas_Iic_le Γ (eqLaw Γ) (eqLaw_Iic_zero Γ) 1))
  -- a level `t > 0` with `Γ[t, ∞) > 0`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 0 < Γ (Ici ((j : ℝ) + 1)⁻¹) := by
    refine exists_measure_pos_of_iUnion (hΓpos.trans_le (measure_mono fun y hy => ?_))
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.1 hy)
    exact mem_iUnion.2 ⟨j, mem_Ici.2 (by rw [← one_div]; exact hj.le)⟩
  set t : ℝ := ((j : ℝ) + 1)⁻¹ with ht
  have ht0 : 0 < t := by positivity
  have hvol : volume (Ioc 0 t) = ENNReal.ofReal t := by rw [Real.volume_Ioc, sub_zero]
  -- the three terms of the renewal equation on `(0, t]`
  have hL : renMeas Γ (eqLaw Γ) (Ioc 0 t) = c * ENNReal.ofReal t := by
    rw [hρ, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.2 Ioc_subset_Ioi_self, hvol, smul_eq_mul]
  set K := ∫⁻ s in Ioc 0 t, Γ (Ici s) with hK
  set J := ∫⁻ s in Ioc 0 t, Γ (Iio s) with hJ
  have hIio : Measurable fun s : ℝ => Γ (Iio s) :=
    Monotone.measurable fun _ _ hab => measure_mono (Iio_subset_Iio hab)
  have hπ : eqLaw Γ (Ioc 0 t) = (renMean Γ)⁻¹ * K := by
    rw [eqLaw, Measure.smul_apply, fwdSkelInv, withDensity_apply _ measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self,
      smul_eq_mul]
  have hR : renMeas Γ (secondLaw Γ (eqLaw Γ)) (Ioc 0 t) = c * J := by
    have hsum : Measurable fun q : ℝ × ℝ => q.1 + q.2 := measurable_fst.add measurable_snd
    have hF := (measurable_renMeas_dirac Γ (A := Ioc 0 t) measurableSet_Ioc).comp hsum
    rw [renMeas_eq_lintegral Γ _ measurableSet_Ioc, secondLaw,
      lintegral_map (measurable_renMeas_dirac Γ measurableSet_Ioc) hsum,
      lintegral_prod (f := fun q : ℝ × ℝ => renMeas Γ (Measure.dirac (q.1 + q.2)) (Ioc 0 t))
        hF.aemeasurable,
      lintegral_lintegral_swap (f := fun x y => renMeas Γ (Measure.dirac (x + y)) (Ioc 0 t))
        hF.aemeasurable]
    -- the inner integral is `Γₑ ∗ U` of a shifted interval
    have hin : ∀ y, 0 ≤ y → ∫⁻ x, renMeas Γ (Measure.dirac (x + y)) (Ioc 0 t) ∂eqLaw Γ =
        c * ENNReal.ofReal (t - y) := fun y hy => by
      simp_rw [renMeas_dirac_add Γ _ y measurableSet_Ioc]
      have hpre : MeasurableSet ((fun u => u + y) ⁻¹' Ioc 0 t) :=
        (measurable_id.add measurable_const) measurableSet_Ioc
      rw [← renMeas_eq_lintegral Γ _ hpre, hρ, Measure.smul_apply, Measure.restrict_apply hpre,
        smul_eq_mul]
      have hset : (fun u => u + y) ⁻¹' Ioc 0 t ∩ Ioi 0 = Ioc 0 (t - y) := by
        ext u
        simp only [mem_inter_iff, mem_preimage, mem_Ioc, mem_Ioi]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, by linarith⟩, h1⟩
      rw [hset, Real.volume_Ioc, sub_zero]
    calc ∫⁻ y, ∫⁻ x, renMeas Γ (Measure.dirac (x + y)) (Ioc 0 t) ∂eqLaw Γ ∂Γ
        = ∫⁻ y, c * ENNReal.ofReal (t - y) ∂Γ := by
          refine lintegral_congr_ae ((ae_iff.2 ?_).mono fun y hy => hin y hy)
          refine measure_mono_null (fun y hy => ?_) hΓ0
          exact not_le.1 hy
      _ = c * J := by
          rw [lintegral_const_mul (f := fun y => ENNReal.ofReal (t - y)) _
            (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id))]
          congr 1
          -- `(t − y)⁺ = μ_Leb{s ∈ (0, t] : y < s}` for `y ≥ 0`, and Fubini
          have hcalc : ∀ y, 0 ≤ y → ENNReal.ofReal (t - y) =
              ∫⁻ s in Ioc 0 t, (Ioi y).indicator 1 s := fun y hy => by
            rw [lintegral_indicator_one measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi]
            have : Ioi y ∩ Ioc 0 t = Ioc y t := by
              ext s
              simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
              constructor
              · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
              · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
            rw [this, Real.volume_Ioc]
          have hmeas2 : Measurable (Function.uncurry fun (y s : ℝ) => (Ioi y).indicator
              (1 : ℝ → ℝ≥0∞) s) := by
            have : (Function.uncurry fun (y s : ℝ) => (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s) =
                {q : ℝ × ℝ | q.1 < q.2}.indicator 1 := by
              funext q
              simp only [Function.uncurry, indicator, mem_Ioi, mem_ofPred_eq, Pi.one_apply]
            rw [this]
            exact measurable_one.indicator (measurableSet_lt measurable_fst measurable_snd)
          have hnn : ∀ᵐ y ∂Γ, 0 ≤ y := ae_iff.2 (measure_mono_null
            (fun y hy => (not_le.1 (show ¬ (0 : ℝ) ≤ y from hy) : y < 0)) hΓ0)
          have step1 : ∫⁻ y, ENNReal.ofReal (t - y) ∂Γ =
              ∫⁻ y, (∫⁻ s in Ioc 0 t, (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s) ∂Γ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hnn] with y hy
            exact hcalc y hy
          have step2 : ∫⁻ y, (∫⁻ s in Ioc 0 t, (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s) ∂Γ =
              ∫⁻ s in Ioc 0 t, (∫⁻ y, (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s ∂Γ) :=
            lintegral_lintegral_swap (μ := Γ) (ν := volume.restrict (Ioc 0 t))
              (f := fun y s => (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s) hmeas2.aemeasurable
          have step3 : ∫⁻ s in Ioc 0 t, (∫⁻ y, (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s ∂Γ) = J := by
            refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
            have e : (fun y => (Ioi y).indicator (1 : ℝ → ℝ≥0∞) s) = (Iio s).indicator 1 := by
              funext y
              simp only [indicator, mem_Ioi, mem_Iio, Pi.one_apply]
            rw [e, lintegral_indicator_one measurableSet_Iio]
          rw [step1, step2, step3]
  -- `t = J + K`
  have hsplit : ENNReal.ofReal t = J + K := by
    rw [← hvol, ← setLIntegral_one, hJ, hK, ← lintegral_add_left hIio]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    rw [← compl_Iio, measure_add_measure_compl measurableSet_Iio, measure_univ]
  have hrenew := renMeas_eq_add Γ (eqLaw Γ)
  have h1 := congrArg (fun ρ : Measure ℝ => ρ (Ioc 0 t)) hrenew
  simp only [Measure.add_apply] at h1
  rw [hL, hπ, hR, hsplit, mul_add] at h1
  have hJt : J ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_self_add)
  have hKt : K ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsplit ▸ le_add_self)
  have hK0 : K ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (setLIntegral_mono (measurable_tail_Ici Γ) fun s hs =>
      measure_mono (Ici_subset_Ici.2 hs.2))).ne'
    rw [setLIntegral_const, hvol]
    exact ENNReal.mul_pos hj.ne' (ENNReal.ofReal_pos.2 ht0).ne'
  have h2 : c * K = (renMean Γ)⁻¹ * K := by
    have h3 : c * K + c * J = (renMean Γ)⁻¹ * K + c * J := by
      rw [add_comm (c * K)]; exact h1
    exact (ENNReal.add_left_inj (ENNReal.mul_ne_top hct hJt)).1 h3
  exact (ENNReal.mul_left_inj hK0 hKt).1 h2

end MeynTweedie.GeneralizedDrift
