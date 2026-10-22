/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.BlackwellHarmonic

/-!
# Blackwell's renewal theorem (MT Theorem 14.5.1)

Meyn and Tweedie, Theorem 14.5.1 (p. 354). The book quotes this result from Feller and does not
prove it. We prove it in full here, for every non-lattice `Γ` on `[0, ∞)` with finite mean.

Write `U₁ = δ₁ ∗ U` for the renewal measure with first epoch `1`, and `β = ∫ y Γ(dy)`.

* `epochLaw Γ j = δ₁ ∗ Γ^{j∗}`, the law of the epoch `1 + Y₀ + ⋯ + Y_{j−1}`. Its basic facts are
  `isProbabilityMeasure_epochLaw` and `epochLaw_Iic_zero`. `epochLaw_Icc_ge` gives
  `epochLaw Γ j [1 + j y ± j ρ] ≥ Γ[y ± ρ]^j`, and `epochLaw_charges` gives the uniform lower bound
  that the maximum principle needs at a support point `y`.
* `exists_window_bound`: `sup_t U₁[t, t + l] < ∞`, via `Γₑ ∗ U = β⁻¹ μ_Leb` and the fact that
  `Γₑ` charges a small interval `(0, a]`.
* `convAt_renMeas_eq_integral`: `μ ∗ U ∗ g(t) = ∫ U₁ ∗ g(t − x + 1) μ(dx)`.
* `convAt_eq_iterate`, the iterated renewal equation:
  `U₁ ∗ g = (δ₁ ∗ Γ^{j∗}) ∗ U ∗ g + Σ_{i<j} δ₁ ∗ Γ^{i∗} ∗ g`.
* `tendsto_convAt_of_lipschitz` (the key renewal theorem for Lipschitz `g` with compact support
  in `[0, ℓ]`): `U₁ ∗ g(t) → β⁻¹ ∫ g`. The function `Z = U₁ ∗ g` is bounded and uniformly
  continuous. By the maximum principle (`tendsto_sub_of_harmonic`), `Z(t) − Z(t − y) → 0` at
  every support point `y`, and then at every `a`, since `Γ` is non-lattice
  (`tendsto_sub_of_isNonLattice`). Averaging against the stationary delay `Γₑ` identifies the limit
  as `β⁻¹ ∫ g`.
* `trap ℓ ε`, the trapezoid functions, which sandwich `1_{[0, ℓ]}`.
* `blackwell_dirac`: `U₁[a + t, b + t] → β⁻¹ (b − a)`.
* **Theorem 14.5.1** (`theorem_14_5_1`, p. 354), (14.35): for a non-lattice `Γ` on `[0, ∞)` with
  finite mean `β`, any first-epoch law `Γ₀` on `ℝ` and `a ≤ b`,
  `Γ₀ ∗ U[a + t, b + t] → β⁻¹ (b − a)`.

**Added hypotheses.** As in the rest of §14.5, `Γ(−∞, 0) = 0 < Γ(0, ∞)`; for a law on `[0, ∞)`,
the second condition just says `Γ ≠ δ₀`. The non-lattice condition is `IsNonLattice`: `Γ` is not
concentrated on `hℤ` for any `h > 0`. For a law on `[0, ∞)`, that is the same as the book's
`hℤ₊`.

**Proof.** The book gives none. Ours follows Feller's analytic route, with two changes. A
compactness-free maximum principle replaces the Choquet–Deny lemma for vague limits, and the
exact identity `Γₑ ∗ U = β⁻¹ μ_Leb` replaces the identification of the limit through the renewal
equation.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-! ### The epoch laws `δ₁ ∗ Γ^{j∗}` -/

/-- The law `δ₁ ∗ Γ^{j∗}` of the epoch `1 + Y₀ + ⋯ + Y_{j−1}`. -/
noncomputable def epochLaw (j : ℕ) : Measure ℝ := (secondLaw Γ)^[j] (Measure.dirac 1)

omit [IsProbabilityMeasure Γ] in
/-- `δ₁ ∗ Γ^{0∗} = δ₁`. -/
theorem epochLaw_zero : epochLaw Γ 0 = Measure.dirac 1 := rfl

omit [IsProbabilityMeasure Γ] in
/-- `δ₁ ∗ Γ^{(j+1)∗} = (δ₁ ∗ Γ^{j∗}) ∗ Γ`. -/
theorem epochLaw_succ (j : ℕ) : epochLaw Γ (j + 1) = secondLaw Γ (epochLaw Γ j) := by
  rw [epochLaw, epochLaw, Function.iterate_succ_apply']

/-- The epoch laws are probability measures. -/
theorem isProbabilityMeasure_epochLaw (j : ℕ) : IsProbabilityMeasure (epochLaw Γ j) := by
  induction j with
  | zero =>
    rw [epochLaw_zero]
    infer_instance
  | succ j ih =>
    rw [epochLaw_succ]
    infer_instance

/-- `μ ∗ Γ` does not charge `(−∞, 0]` when `μ` does not. -/
theorem secondLaw_Iic_zero (hΓ0 : Γ (Iio 0) = 0) (μ : Measure ℝ) [SFinite μ]
    (hμ : μ (Iic 0) = 0) : secondLaw Γ μ (Iic 0) = 0 := by
  rw [secondLaw, Measure.map_apply (f := fun q : ℝ × ℝ => q.1 + q.2)
    (measurable_fst.add measurable_snd) measurableSet_Iic]
  refine measure_mono_null (t := (Iic 0 ×ˢ univ) ∪ (univ ×ˢ Iio 0)) (fun p hp => ?_)
    (measure_union_null ?_ ?_)
  · have hp' : p.1 + p.2 ≤ 0 := hp
    by_cases h1 : p.1 ≤ 0
    · exact Or.inl ⟨h1, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, show p.2 < 0 by linarith [not_le.1 h1]⟩
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hΓ0, mul_zero]

/-- The epoch laws do not charge `(−∞, 0]`. -/
theorem epochLaw_Iic_zero (hΓ0 : Γ (Iio 0) = 0) (j : ℕ) : epochLaw Γ j (Iic 0) = 0 := by
  induction j with
  | zero =>
    rw [epochLaw_zero, Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
        simp only [mem_Iic, not_le]; exact one_pos)]
  | succ j ih =>
    have := isProbabilityMeasure_epochLaw Γ j
    rw [epochLaw_succ]
    exact secondLaw_Iic_zero Γ hΓ0 _ ih

/-- `(ν ∗ Γ)[a + b ± (ρ + ρ')] ≥ ν[a ± ρ] Γ[b ± ρ']`. -/
theorem secondLaw_Icc_ge (ν : Measure ℝ) [SFinite ν] (a b ρ ρ' : ℝ) :
    ν (Icc (a - ρ) (a + ρ)) * Γ (Icc (b - ρ') (b + ρ')) ≤
      secondLaw Γ ν (Icc (a + b - ρ - ρ') (a + b + ρ + ρ')) := by
  rw [secondLaw, Measure.map_apply (f := fun q : ℝ × ℝ => q.1 + q.2)
    (measurable_fst.add measurable_snd) measurableSet_Icc, ← Measure.prod_prod]
  exact measure_mono fun p hp => ⟨by linarith [hp.1.1, hp.2.1], by linarith [hp.1.2, hp.2.2]⟩

/-- `δ₁ ∗ Γ^{j∗}[1 + j y ± j ρ] ≥ Γ[y ± ρ]^j`. -/
theorem epochLaw_Icc_ge (y ρ : ℝ) (j : ℕ) :
    Γ (Icc (y - ρ) (y + ρ)) ^ j ≤ epochLaw Γ j (Icc (1 + j * y - j * ρ) (1 + j * y + j * ρ)) := by
  induction j with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, sub_zero]
    rw [epochLaw_zero, Measure.dirac_apply_of_mem (show (1 : ℝ) ∈ Icc 1 1 from ⟨le_rfl, le_rfl⟩)]
  | succ j ih =>
    have := isProbabilityMeasure_epochLaw Γ j
    have e1 : 1 + j * y + y - j * ρ - ρ = 1 + ((j : ℝ) + 1) * y - ((j : ℝ) + 1) * ρ := by ring
    have e2 : 1 + j * y + y + j * ρ + ρ = 1 + ((j : ℝ) + 1) * y + ((j : ℝ) + 1) * ρ := by ring
    calc Γ (Icc (y - ρ) (y + ρ)) ^ (j + 1)
          = Γ (Icc (y - ρ) (y + ρ)) ^ j * Γ (Icc (y - ρ) (y + ρ)) := pow_succ _ _
      _ ≤ epochLaw Γ j (Icc (1 + j * y - j * ρ) (1 + j * y + j * ρ)) * Γ (Icc (y - ρ) (y + ρ)) :=
          mul_le_mul' ih le_rfl
      _ ≤ secondLaw Γ (epochLaw Γ j)
          (Icc (1 + j * y + y - j * ρ - ρ) (1 + j * y + y + j * ρ + ρ)) :=
          secondLaw_Icc_ge Γ _ _ _ _ _
      _ = epochLaw Γ (j + 1)
          (Icc (1 + ((j + 1 : ℕ) : ℝ) * y - ((j + 1 : ℕ) : ℝ) * ρ)
            (1 + ((j + 1 : ℕ) : ℝ) * y + ((j + 1 : ℕ) : ℝ) * ρ)) := by
          rw [epochLaw_succ, Nat.cast_succ, e1, e2]

/-- At a support point `y`, the epoch laws charge the intervals `[1 + j y ± r]` uniformly in
`j < k`: the hypothesis of the maximum principle. -/
theorem epochLaw_charges {y : ℝ} (hy : IsSupportPoint Γ y) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    ∃ q : ℝ, 0 < q ∧ ∀ j < k, q ≤ (epochLaw Γ j).real (Icc (1 + j * y - r) (1 + j * y + r)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact ⟨1, one_pos, fun j hj => absurd hj (by omega)⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set ρ : ℝ := r / k with hρ
  have hρpos : 0 < ρ := div_pos hr hkpos
  set p := Γ (Icc (y - ρ) (y + ρ)) with hp
  have hp0 : 0 < p := hy ρ hρpos
  have hpr0 : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' (measure_ne_top _ _)
  have hpr1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  refine ⟨p.toReal ^ k, pow_pos hpr0 k, fun j hj => ?_⟩
  have := isProbabilityMeasure_epochLaw Γ j
  have hjr : (j : ℝ) * ρ ≤ r := by
    rw [hρ, mul_div_assoc', div_le_iff₀ hkpos, mul_comm r]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj.le) hr.le
  have hj0 : (0 : ℝ) ≤ j * ρ := by positivity
  calc p.toReal ^ k ≤ p.toReal ^ j := pow_le_pow_of_le_one hpr0.le hpr1 hj.le
    _ = (p ^ j).toReal := (ENNReal.toReal_pow p j).symm
    _ ≤ (epochLaw Γ j).real (Icc (1 + j * y - j * ρ) (1 + j * y + j * ρ)) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (epochLaw_Icc_ge Γ y ρ j)
    _ ≤ (epochLaw Γ j).real (Icc (1 + j * y - r) (1 + j * y + r)) :=
        measureReal_mono (Icc_subset_Icc (by linarith) (by linarith))

/-! ### Uniform local finiteness of `U₁` -/

/-- **`sup_t U₁[t, t + l] < ∞`** for `Γ` on `[0, ∞)` with finite mean. If `Γₑ(0, a] > 0`, then
`U₁[t, t + l] Γₑ(0, a] ≤ ∫_{(0, a]} δ_x ∗ U[t − 1, t + l + a − 1] Γₑ(dx)`, and this is at most
`Γₑ ∗ U[t − 1, t + l + a − 1] = β⁻¹ (l + a)`. -/
theorem exists_window_bound (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hm : renMean Γ ≠ ∞)
    (l : ℝ) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t, renMeas Γ (Measure.dirac 1) (Icc t (t + l)) ≤ K := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have hm0 : renMean Γ ≠ 0 := by
    refine (?_ : 0 < renMean Γ).ne'
    rw [renMean, lintegral_pos_iff_support ENNReal.measurable_ofReal]
    refine lt_of_lt_of_le hΓpos (measure_mono fun y hy => ?_)
    rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hy
  obtain ⟨a, ha, hpos⟩ := exists_eqLaw_Ioc_pos Γ hΓpos hm
  refine ⟨(renMean Γ)⁻¹ * ENNReal.ofReal (l + a) / eqLaw Γ (Ioc 0 a), ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) ENNReal.ofReal_ne_top) hpos.ne', fun t => ?_⟩
  have hA : MeasurableSet (Icc (t - 1) (t + l + a - 1)) := measurableSet_Icc
  have hmain : renMeas Γ (Measure.dirac 1) (Icc t (t + l)) * eqLaw Γ (Ioc 0 a) ≤
      (renMean Γ)⁻¹ * ENNReal.ofReal (l + a) := by
    calc renMeas Γ (Measure.dirac 1) (Icc t (t + l)) * eqLaw Γ (Ioc 0 a)
        = ∫⁻ _ in Ioc 0 a, renMeas Γ (Measure.dirac 1) (Icc t (t + l)) ∂eqLaw Γ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Ioc 0 a, renMeas Γ (Measure.dirac x) (Icc (t - 1) (t + l + a - 1)) ∂eqLaw Γ :=
          setLIntegral_mono (measurable_renMeas_dirac Γ hA) fun x hx => by
            rw [renMeas_dirac_eq_map Γ x, Measure.map_apply (f := fun u => u + (x - 1))
              (measurable_id.add measurable_const) hA]
            exact measure_mono fun u hu =>
              ⟨by linarith [hu.1, hx.1], by linarith [hu.2, hx.2]⟩
      _ ≤ ∫⁻ x, renMeas Γ (Measure.dirac x) (Icc (t - 1) (t + l + a - 1)) ∂eqLaw Γ :=
          setLIntegral_le_lintegral _ _
      _ = renMeas Γ (eqLaw Γ) (Icc (t - 1) (t + l + a - 1)) :=
          (renMeas_eq_lintegral Γ _ hA).symm
      _ = (renMean Γ)⁻¹ * volume (Icc (t - 1) (t + l + a - 1) ∩ Ioi 0) := by
          rw [renMeas_eqLaw Γ hΓ0 hΓpos hm, Measure.smul_apply, Measure.restrict_apply hA,
            smul_eq_mul]
      _ ≤ (renMean Γ)⁻¹ * ENNReal.ofReal (l + a) := by
          refine mul_le_mul' le_rfl ((measure_mono inter_subset_left).trans (le_of_eq ?_))
          rw [Real.volume_Icc]
          congr 1
          ring
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl (measure_ne_top _ _))]
  exact hmain

/-! ### Convolution identities -/

/-- `g(t − ·)` is integrable for `μ ∗ U` when `|g| ≤ d` and `g` vanishes on `(−∞, 0)`. -/
theorem integrable_comp_sub_renMeas (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iic 0) = 0) {g : ℝ → ℝ} (hg : Measurable g)
    {d : ℝ} (hgd : ∀ s, |g s| ≤ d) (hg0 : ∀ s < 0, g s = 0) (t : ℝ) :
    Integrable (fun u => g (t - u)) (renMeas Γ ν) := by
  have hfin : renMeas Γ ν (Iic t) ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0
      hΓpos)).ne')) (renMeas_Iic_le Γ ν hν t)
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_Iic).2
    (integrableOn_const hfin (C := d)))
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs]
  by_cases hu : u ∈ Iic t
  · rw [indicator_of_mem hu]
    exact hgd _
  · have htu : t < u := not_le.1 hu
    rw [indicator_of_notMem hu, hg0 _ (by linarith), abs_zero]

omit [IsProbabilityMeasure Γ] in
/-- `g(t − ·)` is integrable for a probability measure when `|g| ≤ d`. -/
theorem integrable_comp_sub_prob (ν : Measure ℝ) [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hg : Measurable g) {d : ℝ} (hgd : ∀ s, |g s| ≤ d) (t : ℝ) :
    Integrable (fun u => g (t - u)) ν :=
  Integrable.mono' (integrable_const d)
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hgd _)

/-- **Mixing over the first epoch**: `μ ∗ U ∗ g(t) = ∫ U₁ ∗ g(t − x + 1) μ(dx)` for a first-epoch
law `μ` on `(0, ∞)` and a bounded measurable `g` vanishing on `(−∞, 0)`. -/
theorem convAt_renMeas_eq_integral (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) {g : ℝ → ℝ} (hg : Measurable g)
    {d : ℝ} (hgd : ∀ s, |g s| ≤ d) (hg0 : ∀ s < 0, g s = 0) (t : ℝ) :
    convAt (renMeas Γ μ) g t = ∫ x, convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1) ∂μ := by
  have := sFinite_renMeas Γ (Measure.dirac (1 : ℝ))
  have hmeas : Measurable fun p : ℝ × ℝ => p.2 + (p.1 - 1) :=
    measurable_snd.add (measurable_fst.sub measurable_const)
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
      simp only [mem_Iic, not_le]; exact one_pos)]
  set E : Set (ℝ × ℝ) := (univ ×ˢ Iic (t + 1)) ∪ (Iic 0 ×ˢ univ) with hE
  have hEm : MeasurableSet E :=
    (MeasurableSet.univ.prod measurableSet_Iic).union (measurableSet_Iic.prod MeasurableSet.univ)
  have hEfin : (μ.prod (renMeas Γ (Measure.dirac 1))) E ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    rw [Measure.prod_prod, Measure.prod_prod, hμ, zero_mul, add_zero, measure_univ, one_mul]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2
      (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne'))
      (renMeas_Iic_le Γ (Measure.dirac 1) hd1 (t + 1))
  have hInt : Integrable (fun z : ℝ × ℝ => g (t - (z.2 + (z.1 - 1))))
      (μ.prod (renMeas Γ (Measure.dirac 1))) := by
    refine Integrable.mono' ((integrable_indicator_iff hEm).2 (integrableOn_const hEfin
      (C := d))) (hg.comp (measurable_const.sub hmeas)).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz]
      exact hgd _
    · rw [indicator_of_notMem hz]
      have h2 : t + 1 < z.2 := by
        by_contra h
        exact hz (Or.inl ⟨mem_univ _, not_lt.1 h⟩)
      have h1 : 0 < z.1 := by
        by_contra h
        exact hz (Or.inr ⟨not_lt.1 h, mem_univ _⟩)
      rw [hg0 _ (by linarith), abs_zero]
  rw [convAt, renMeas_eq_map_prod Γ μ, integral_map (f := fun u => g (t - u)) hmeas.aemeasurable
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, integral_prod _ hInt]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change ∫ u, g (t - (u + (x - 1))) ∂renMeas Γ (Measure.dirac 1) =
    ∫ u, g (t - x + 1 - u) ∂renMeas Γ (Measure.dirac 1)
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  change g (t - (u + (x - 1))) = g (t - x + 1 - u)
  congr 1
  ring

/-- **The iterated renewal equation**:
`U₁ ∗ g(t) = (δ₁ ∗ Γ^{j∗}) ∗ U ∗ g(t) + Σ_{i<j} δ₁ ∗ Γ^{i∗} ∗ g(t)`. -/
theorem convAt_eq_iterate (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {g : ℝ → ℝ}
    (hg : Measurable g) {d : ℝ} (hgd : ∀ s, |g s| ≤ d) (hg0 : ∀ s < 0, g s = 0) (t : ℝ)
    (j : ℕ) :
    convAt (renMeas Γ (Measure.dirac 1)) g t =
      convAt (renMeas Γ (epochLaw Γ j)) g t + ∑ i ∈ Finset.range j, convAt (epochLaw Γ i) g t := by
  induction j with
  | zero => rw [Finset.sum_range_zero, add_zero, epochLaw_zero]
  | succ j ih =>
    have := isProbabilityMeasure_epochLaw Γ j
    have hstep : convAt (renMeas Γ (epochLaw Γ j)) g t =
        convAt (epochLaw Γ j) g t + convAt (renMeas Γ (epochLaw Γ (j + 1))) g t := by
      unfold convAt
      rw [renMeas_eq_add Γ (epochLaw Γ j), integral_add_measure
        (integrable_comp_sub_prob (epochLaw Γ j) hg hgd t)
        (integrable_comp_sub_renMeas Γ hΓ0 hΓpos _
          (secondLaw_Iic_zero Γ hΓ0 _ (epochLaw_Iic_zero Γ hΓ0 j)) hg hgd hg0 t),
        epochLaw_succ]
    rw [ih, hstep, Finset.sum_range_succ]
    ring

/-! ### The key renewal theorem for Lipschitz test functions -/

/-- **The key renewal theorem for Lipschitz `g`**: for a non-lattice `Γ` on `[0, ∞)` with finite
mean `β` and a Lipschitz `g` with `|g| ≤ d` and support in `[0, ℓ]`, `U₁ ∗ g(t) → β⁻¹ ∫ g`. -/
theorem tendsto_convAt_of_lipschitz (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hnl : IsNonLattice Γ) (hm : renMean Γ ≠ ∞) {g : ℝ → ℝ} {L d ℓ : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ a b, |g a - g b| ≤ L * |a - b|) (hgd : ∀ s, |g s| ≤ d) (hg0 : ∀ s < 0, g s = 0)
    (hgℓ : ∀ s, ℓ < s → g s = 0) :
    Tendsto (convAt (renMeas Γ (Measure.dirac 1)) g) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * ∫ s, g s)) := by
  have := sFinite_renMeas Γ (Measure.dirac (1 : ℝ))
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hgd 0)
  have hgc : Continuous g := continuous_of_unifCont fun η hη => ⟨η / (L + 1), by positivity,
    fun a b hab => (hLip a b).trans (by
      calc L * |a - b| ≤ L * (η / (L + 1)) := mul_le_mul_of_nonneg_left hab hL
        _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith)⟩
  have hgm : Measurable g := hgc.measurable
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
      simp only [mem_Iic, not_le]; exact one_pos)]
  obtain ⟨K, hK, hKb⟩ := exists_window_bound Γ hΓ0 hΓpos hm (ℓ + 2)
  have hgi : ∀ s, Integrable (fun u => g (s - u)) (renMeas Γ (Measure.dirac 1)) := fun s =>
    integrable_comp_sub_renMeas Γ hΓ0 hΓpos _ hd1 hgm hgd hg0 s
  have hκ0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  -- `Z = U₁ ∗ g` is bounded
  have hZB : ∀ t, |convAt (renMeas Γ (Measure.dirac 1)) g t| ≤ d * K.toReal := fun t => by
    have hsub : renMeas Γ (Measure.dirac 1) (Icc (t - ℓ) t) ≤ K :=
      (measure_mono (Icc_subset_Icc le_rfl (by linarith))).trans (hKb (t - ℓ))
    have hfin : renMeas Γ (Measure.dirac 1) (Icc (t - ℓ) t) ≠ ∞ := ne_top_of_le_ne_top hK hsub
    rw [convAt, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const hfin (C := d))) (ae_of_all _ fun u => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      by_cases hu : u ∈ Icc (t - ℓ) t
      · rw [indicator_of_mem hu]
        exact hgd _
      · rw [indicator_of_notMem hu]
        have hu' : ¬ (t - ℓ ≤ u ∧ u ≤ t) := hu
        rcases not_and_or.1 hu' with h | h
        · rw [hgℓ _ (by linarith [not_le.1 h]), abs_zero]
        · rw [hg0 _ (by linarith [not_le.1 h]), abs_zero]
    · rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hK hsub) hd0
  -- `Z` is uniformly continuous
  have hZuc : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ a b, |a - b| ≤ r →
      |convAt (renMeas Γ (Measure.dirac 1)) g a - convAt (renMeas Γ (Measure.dirac 1)) g b| ≤
        η := by
    intro η hη
    refine ⟨min 1 (η / (L * K.toReal + 1)), lt_min one_pos (by positivity), fun a b hab => ?_⟩
    have hab1 : |a - b| ≤ 1 := hab.trans (min_le_left _ _)
    have hab2 : |a - b| ≤ η / (L * K.toReal + 1) := hab.trans (min_le_right _ _)
    have hab1' := abs_le.1 hab1
    have hsub : renMeas Γ (Measure.dirac 1) (Icc (a - ℓ - 1) (a + 1)) ≤ K :=
      (measure_mono (Icc_subset_Icc le_rfl (by linarith))).trans (hKb (a - ℓ - 1))
    have hfin : renMeas Γ (Measure.dirac 1) (Icc (a - ℓ - 1) (a + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top hK hsub
    rw [convAt, convAt, ← integral_sub (hgi a) (hgi b), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const hfin (C := L * |a - b|))) (ae_of_all _ fun u => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      by_cases hu : u ∈ Icc (a - ℓ - 1) (a + 1)
      · rw [indicator_of_mem hu]
        have h := hLip (a - u) (b - u)
        rwa [show a - u - (b - u) = a - b by ring] at h
      · rw [indicator_of_notMem hu]
        have hu' : ¬ (a - ℓ - 1 ≤ u ∧ u ≤ a + 1) := hu
        rcases not_and_or.1 hu' with h | h
        · rw [hgℓ _ (by linarith [not_le.1 h]), hgℓ _ (by linarith [not_le.1 h]), sub_self,
            abs_zero]
        · rw [hg0 _ (by linarith [not_le.1 h]), hg0 _ (by linarith [not_le.1 h]), sub_self,
            abs_zero]
    · rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
      calc (renMeas Γ (Measure.dirac 1)).real (Icc (a - ℓ - 1) (a + 1)) * (L * |a - b|)
          ≤ K.toReal * (L * (η / (L * K.toReal + 1))) :=
            mul_le_mul (ENNReal.toReal_mono hK hsub) (mul_le_mul_of_nonneg_left hab2 hL)
              (by positivity) hκ0
        _ ≤ η := by
            rw [← mul_assoc, mul_comm K.toReal L, mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith [mul_nonneg hL hκ0]
  have hZc : Continuous (convAt (renMeas Γ (Measure.dirac 1)) g) := continuous_of_unifCont hZuc
  -- the iterated renewal equation and its remainder
  have hZeq : ∀ (j : ℕ) (t : ℝ), convAt (renMeas Γ (Measure.dirac 1)) g t =
      ∫ x, convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1) ∂epochLaw Γ j +
        ∑ i ∈ Finset.range j, convAt (epochLaw Γ i) g t := fun j t => by
    have := isProbabilityMeasure_epochLaw Γ j
    rw [← convAt_renMeas_eq_integral Γ hΓ0 hΓpos (epochLaw Γ j) (epochLaw_Iic_zero Γ hΓ0 j) hgm
      hgd hg0 t]
    exact convAt_eq_iterate Γ hΓ0 hΓpos hgm hgd hg0 t j
  have hR : ∀ j : ℕ, Tendsto (fun t => ∑ i ∈ Finset.range j, convAt (epochLaw Γ i) g t) atTop
      (𝓝 0) := fun j => by
    have h : ∀ i ∈ Finset.range j, Tendsto (fun t => convAt (epochLaw Γ i) g t) atTop (𝓝 0) :=
      fun i _ => by
        have := isProbabilityMeasure_epochLaw Γ i
        have h := tendsto_integral_filter_of_dominated_convergence (μ := epochLaw Γ i)
          (l := atTop) (F := fun t u => g (t - u)) (f := fun _ => 0) (fun _ => d)
          (Eventually.of_forall fun t =>
            (hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
          (Eventually.of_forall fun t => ae_of_all _ fun u => by
            rw [Real.norm_eq_abs]
            exact hgd _)
          (integrable_const d)
          (ae_of_all _ fun u => tendsto_const_nhds.congr' (eventually_atTop.2
            ⟨u + ℓ + 1, fun t ht => (hgℓ _ (by linarith)).symm⟩))
        rw [integral_zero] at h
        exact h
    have h' := tendsto_finsetSum (Finset.range j) h
    rw [Finset.sum_const_zero] at h'
    exact h'
  -- asymptotic translation invariance
  have hinv : ∀ a : ℝ, Tendsto (fun t => convAt (renMeas Γ (Measure.dirac 1)) g t -
      convAt (renMeas Γ (Measure.dirac 1)) g (t - a)) atTop (𝓝 0) :=
    tendsto_sub_of_isNonLattice hΓpos hnl hZuc fun y hy =>
      tendsto_sub_of_harmonic hZB hZuc (epochLaw Γ) (hP := isProbabilityMeasure_epochLaw Γ)
        (fun j t => ∑ i ∈ Finset.range j, convAt (epochLaw Γ i) g t) hZeq hR
        (epochLaw_charges Γ hy)
  -- identification of the limit through `Γₑ ∗ U = β⁻¹ μ_Leb`
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  have hZint : ∀ t, Integrable (fun x => convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1))
      (eqLaw Γ) := fun t =>
    Integrable.mono' (integrable_const (d * K.toReal))
      (hZc.comp ((continuous_const.sub continuous_id).add continuous_const)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hZB _)
  have heq : ∀ t, ℓ < t → ∫ x, convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1) ∂eqLaw Γ =
      ((renMean Γ).toReal)⁻¹ * ∫ s, g s := fun t ht => by
    rw [← convAt_renMeas_eq_integral Γ hΓ0 hΓpos (eqLaw Γ) (eqLaw_Iic_zero Γ) hgm hgd hg0 t,
      convAt_eqLaw Γ hΓ0 hΓpos hm g t, ENNReal.toReal_inv,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs =>
        hgℓ s (by have : t ≤ s := not_lt.1 hs; linarith)]
  have hdiff : Tendsto (fun t => ∫ x, (convAt (renMeas Γ (Measure.dirac 1)) g t -
      convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1)) ∂eqLaw Γ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := eqLaw Γ) (l := atTop)
      (F := fun t x => convAt (renMeas Γ (Measure.dirac 1)) g t -
        convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1)) (f := fun _ => 0)
      (fun _ => 2 * (d * K.toReal))
      (Eventually.of_forall fun t => (continuous_const.sub (hZc.comp
        ((continuous_const.sub continuous_id).add continuous_const))).aestronglyMeasurable)
      (Eventually.of_forall fun t => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hZB t, hZB (t - x + 1)]))
      (integrable_const _)
      (ae_of_all _ fun x => (hinv (x - 1)).congr fun t => by
        rw [show t - (x - 1) = t - x + 1 by ring])
    rw [integral_zero] at h
    exact h
  have hev : (fun t => ∫ x, (convAt (renMeas Γ (Measure.dirac 1)) g t -
      convAt (renMeas Γ (Measure.dirac 1)) g (t - x + 1)) ∂eqLaw Γ) =ᶠ[atTop]
      fun t => convAt (renMeas Γ (Measure.dirac 1)) g t - ((renMean Γ).toReal)⁻¹ * ∫ s, g s := by
    filter_upwards [eventually_gt_atTop ℓ] with t ht
    rw [integral_sub (integrable_const _) (hZint t), integral_const, probReal_univ, one_smul,
      heq t ht]
  exact tendsto_sub_nhds_zero_iff.1 (hdiff.congr' hev)

/-! ### Trapezoids -/

/-- The trapezoid `trap ℓ ε s = max 0 (min 1 (min (s / ε) ((ℓ − s) / ε)))`. It vanishes off
`[0, ℓ]`, equals `1` on `[ε, ℓ − ε]`, and is linear in between. -/
noncomputable def trap (ℓ ε s : ℝ) : ℝ := max 0 (min 1 (min (s / ε) ((ℓ - s) / ε)))

/-- `trap ≥ 0`. -/
theorem trap_nonneg (ℓ ε s : ℝ) : 0 ≤ trap ℓ ε s := le_max_left _ _

/-- `trap ≤ 1`. -/
theorem trap_le_one (ℓ ε s : ℝ) : trap ℓ ε s ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- `|trap| ≤ 1`. -/
theorem abs_trap_le (ℓ ε s : ℝ) : |trap ℓ ε s| ≤ 1 := by
  rw [abs_of_nonneg (trap_nonneg ℓ ε s)]
  exact trap_le_one ℓ ε s

/-- `trap` vanishes on `(−∞, 0)`. -/
theorem trap_of_neg (ℓ : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s < 0) : trap ℓ ε s = 0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (div_neg_of_neg_of_pos hs hε).le))

/-- `trap` vanishes on `(ℓ, ∞)`. -/
theorem trap_of_gt {ℓ ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : ℓ < s) : trap ℓ ε s = 0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans
    (div_neg_of_neg_of_pos (by linarith) hε).le))

/-- `trap = 1` on `[ε, ℓ − ε]`. -/
theorem trap_eq_one {ℓ ε : ℝ} (hε : 0 < ε) {s : ℝ} (h1 : ε ≤ s) (h2 : s ≤ ℓ - ε) :
    trap ℓ ε s = 1 := by
  unfold trap
  have a1 : 1 ≤ s / ε := (one_le_div hε).2 h1
  have a2 : 1 ≤ (ℓ - s) / ε := (one_le_div hε).2 (by linarith)
  rw [min_eq_left (le_min a1 a2), max_eq_right zero_le_one]

/-- `trap` is `ε⁻¹`-Lipschitz. -/
theorem abs_trap_sub_le (ℓ : ℝ) {ε : ℝ} (hε : 0 < ε) (s s' : ℝ) :
    |trap ℓ ε s - trap ℓ ε s'| ≤ ε⁻¹ * |s - s'| := by
  unfold trap
  have h1 : |s / ε - s' / ε| = ε⁻¹ * |s - s'| := by
    rw [← sub_div, abs_div, abs_of_pos hε, div_eq_inv_mul]
  have h2 : |(ℓ - s) / ε - (ℓ - s') / ε| = ε⁻¹ * |s - s'| := by
    rw [← sub_div, show ℓ - s - (ℓ - s') = s' - s by ring, abs_div, abs_of_pos hε, abs_sub_comm,
      div_eq_inv_mul]
  calc |max 0 (min 1 (min (s / ε) ((ℓ - s) / ε))) - max 0 (min 1 (min (s' / ε) ((ℓ - s') / ε)))|
      ≤ |min 1 (min (s / ε) ((ℓ - s) / ε)) - min 1 (min (s' / ε) ((ℓ - s') / ε))| := by
        rw [max_comm 0, max_comm 0]
        exact abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |min (s / ε) ((ℓ - s) / ε) - min (s' / ε) ((ℓ - s') / ε)| :=
        abs_min_sub_min_le_max _ _ _ _
    _ ≤ ε⁻¹ * |s - s'| := by
        rw [sub_self, abs_zero]
        refine max_le (by positivity) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
        rw [h1, h2, max_self]

/-- `trap` is continuous. -/
theorem continuous_trap (ℓ ε : ℝ) : Continuous (trap ℓ ε) :=
  continuous_const.max (continuous_const.min ((continuous_id.div_const ε).min
    ((continuous_const.sub continuous_id).div_const ε)))

/-- `trap` is integrable. -/
theorem integrable_trap (ℓ : ℝ) {ε : ℝ} (hε : 0 < ε) : Integrable (trap ℓ ε) := by
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (C := (1 : ℝ)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) :
      IntegrableOn (fun _ => (1 : ℝ)) (Icc 0 ℓ))) (continuous_trap ℓ ε).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs]
  by_cases hs : s ∈ Icc 0 ℓ
  · rw [indicator_of_mem hs]
    exact abs_trap_le ℓ ε s
  · rw [indicator_of_notMem hs]
    have hs' : ¬ (0 ≤ s ∧ s ≤ ℓ) := hs
    rcases not_and_or.1 hs' with h | h
    · rw [trap_of_neg ℓ hε (not_le.1 h), abs_zero]
    · rw [trap_of_gt hε (not_le.1 h), abs_zero]

/-- `∫ trap ℓ ε ≥ ℓ − 2ε`. -/
theorem integral_trap_ge (ℓ : ℝ) {ε : ℝ} (hε : 0 < ε) : ℓ - 2 * ε ≤ ∫ s, trap ℓ ε s := by
  have h1 : ∫ s, (Icc ε (ℓ - ε)).indicator (fun _ => (1 : ℝ)) s ≤ ∫ s, trap ℓ ε s :=
    integral_mono ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
      (integrable_trap ℓ hε) fun s => by
        by_cases hs : s ∈ Icc ε (ℓ - ε)
        · rw [indicator_of_mem hs, trap_eq_one hε hs.1 hs.2]
        · rw [indicator_of_notMem hs]
          exact trap_nonneg ℓ ε s
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc] at h1
  exact le_trans (by linarith [le_max_left (ℓ - ε - ε) 0]) h1

/-- `∫ trap ℓ ε ≤ ℓ` for `ℓ ≥ 0`. -/
theorem integral_trap_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {ε : ℝ} (hε : 0 < ε) : ∫ s, trap ℓ ε s ≤ ℓ := by
  have h1 : ∫ s, trap ℓ ε s ≤ ∫ s, (Icc 0 ℓ).indicator (fun _ => (1 : ℝ)) s :=
    integral_mono (integrable_trap ℓ hε) ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))) fun s => by
        by_cases hs : s ∈ Icc 0 ℓ
        · rw [indicator_of_mem hs]
          exact trap_le_one ℓ ε s
        · rw [indicator_of_notMem hs]
          have hs' : ¬ (0 ≤ s ∧ s ≤ ℓ) := hs
          rcases not_and_or.1 hs' with h | h
          · rw [trap_of_neg ℓ hε (not_le.1 h)]
          · rw [trap_of_gt hε (not_le.1 h)]
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc, sub_zero, max_eq_left hℓ] at h1
  exact h1

/-! ### Blackwell's renewal theorem -/

/-- **Blackwell's theorem for the first epoch `1`**: `U₁[a + t, b + t] → β⁻¹ (b − a)`, by
sandwiching `1_{[a + t, b + t]}` between trapezoids. -/
theorem blackwell_dirac (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hnl : IsNonLattice Γ)
    (hm : renMean Γ ≠ ∞) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun t => (renMeas Γ (Measure.dirac 1)).real (Icc (a + t) (b + t))) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * (b - a))) := by
  have hm0 : renMean Γ ≠ 0 := by
    refine (?_ : 0 < renMean Γ).ne'
    rw [renMean, lintegral_pos_iff_support ENNReal.measurable_ofReal]
    refine lt_of_lt_of_le hΓpos (measure_mono fun y hy => ?_)
    rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hy
  have hβ : 0 < ((renMean Γ).toReal)⁻¹ := inv_pos.2 (ENNReal.toReal_pos hm0 hm)
  have hd1 : (Measure.dirac (1 : ℝ)) (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic, indicator_of_notMem (show (1 : ℝ) ∉ Iic 0 by
      simp only [mem_Iic, not_le]; exact one_pos)]
  have hℓ : 0 ≤ b - a := sub_nonneg.2 hab
  obtain ⟨K, hK, hKb⟩ := exists_window_bound Γ hΓ0 hΓpos hm (b - a)
  have hfinI : ∀ t, renMeas Γ (Measure.dirac 1) (Icc (a + t) (b + t)) ≠ ∞ := fun t =>
    ne_top_of_le_ne_top hK (by rw [show b + t = a + t + (b - a) by ring]; exact hKb (a + t))
  have hlow : ∀ ε : ℝ, 0 < ε → Tendsto (fun t =>
      convAt (renMeas Γ (Measure.dirac 1)) (trap (b - a) ε) (b + t)) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * ∫ s, trap (b - a) ε s)) := fun ε hε =>
    (tendsto_convAt_of_lipschitz Γ hΓ0 hΓpos hnl hm (inv_nonneg.2 hε.le)
      (abs_trap_sub_le (b - a) hε) (abs_trap_le (b - a) ε) (fun s hs => trap_of_neg _ hε hs)
      (fun s hs => trap_of_gt hε hs)).comp (tendsto_atTop_add_const_left atTop b tendsto_id)
  have hup : ∀ ε : ℝ, 0 < ε → Tendsto (fun t =>
      convAt (renMeas Γ (Measure.dirac 1)) (trap (b - a + 2 * ε) ε) (b + t + ε)) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * ∫ s, trap (b - a + 2 * ε) ε s)) := fun ε hε =>
    (tendsto_convAt_of_lipschitz Γ hΓ0 hΓpos hnl hm (inv_nonneg.2 hε.le)
      (abs_trap_sub_le (b - a + 2 * ε) hε) (abs_trap_le (b - a + 2 * ε) ε)
      (fun s hs => trap_of_neg _ hε hs) (fun s hs => trap_of_gt hε hs)).comp
      (tendsto_atTop_add_const_right atTop ε (tendsto_atTop_add_const_left atTop b tendsto_id))
  have hle1 : ∀ ε : ℝ, 0 < ε → ∀ t, convAt (renMeas Γ (Measure.dirac 1)) (trap (b - a) ε) (b + t)
      ≤ (renMeas Γ (Measure.dirac 1)).real (Icc (a + t) (b + t)) := fun ε hε t => by
    rw [convAt, ← integral_indicator_one measurableSet_Icc]
    refine integral_mono (integrable_comp_sub_renMeas Γ hΓ0 hΓpos _ hd1
      (continuous_trap _ ε).measurable (abs_trap_le (b - a) ε)
      (fun s hs => trap_of_neg _ hε hs) _)
      ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (hfinI t)))
      fun u => ?_
    by_cases hu : u ∈ Icc (a + t) (b + t)
    · rw [indicator_of_mem hu, Pi.one_apply]
      exact trap_le_one _ _ _
    · rw [indicator_of_notMem hu]
      have hu' : ¬ (a + t ≤ u ∧ u ≤ b + t) := hu
      rcases not_and_or.1 hu' with h | h
      · exact le_of_eq (trap_of_gt hε (by linarith [not_le.1 h]))
      · exact le_of_eq (trap_of_neg _ hε (by linarith [not_le.1 h]))
  have hle2 : ∀ ε : ℝ, 0 < ε → ∀ t, (renMeas Γ (Measure.dirac 1)).real (Icc (a + t) (b + t)) ≤
      convAt (renMeas Γ (Measure.dirac 1)) (trap (b - a + 2 * ε) ε) (b + t + ε) :=
    fun ε hε t => by
      rw [convAt, ← integral_indicator_one measurableSet_Icc]
      refine integral_mono ((integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (hfinI t)))
        (integrable_comp_sub_renMeas Γ hΓ0 hΓpos _ hd1 (continuous_trap _ ε).measurable
          (abs_trap_le (b - a + 2 * ε) ε) (fun s hs => trap_of_neg _ hε hs) _) fun u => ?_
      by_cases hu : u ∈ Icc (a + t) (b + t)
      · rw [indicator_of_mem hu, Pi.one_apply, trap_eq_one hε (by linarith [hu.2])
          (by linarith [hu.1])]
      · rw [indicator_of_notMem hu]
        exact trap_nonneg _ _ _
  have hkey : ∀ β' D : ℝ, 0 < β' → β' * (2 * (D / (4 * β'))) = D / 2 := fun β' D hβ' => by
    have hne : β' ≠ 0 := hβ'.ne'
    field_simp
    ring
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
        ε = (((renMean Γ).toReal)⁻¹ * (b - a) - c) / (4 * ((renMean Γ).toReal)⁻¹) := ⟨_, rfl⟩
    have hε : 0 < ε := by
      rw [hεdef]
      exact div_pos (by linarith) (by linarith)
    have h2 : ((renMean Γ).toReal)⁻¹ * (2 * ε) = (((renMean Γ).toReal)⁻¹ * (b - a) - c) / 2 := by
      rw [hεdef]
      exact hkey _ _ hβ
    have hlim : c < ((renMean Γ).toReal)⁻¹ * ∫ s, trap (b - a) ε s := by
      have h1 := mul_le_mul_of_nonneg_left (integral_trap_ge (b - a) hε) hβ.le
      rw [mul_sub] at h1
      linarith
    filter_upwards [(tendsto_order.1 (hlow ε hε)).1 c hlim] with t ht
    exact lt_of_lt_of_le ht (hle1 ε hε t)
  · obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
        ε = (c - ((renMean Γ).toReal)⁻¹ * (b - a)) / (4 * ((renMean Γ).toReal)⁻¹) := ⟨_, rfl⟩
    have hε : 0 < ε := by
      rw [hεdef]
      exact div_pos (by linarith) (by linarith)
    have h2 : ((renMean Γ).toReal)⁻¹ * (2 * ε) = (c - ((renMean Γ).toReal)⁻¹ * (b - a)) / 2 := by
      rw [hεdef]
      exact hkey _ _ hβ
    have hlim : ((renMean Γ).toReal)⁻¹ * ∫ s, trap (b - a + 2 * ε) ε s < c := by
      have h1 := mul_le_mul_of_nonneg_left
        (integral_trap_le (ℓ := b - a + 2 * ε) (by linarith) hε) hβ.le
      rw [mul_add] at h1
      linarith
    filter_upwards [(tendsto_order.1 (hup ε hε)).2 c hlim] with t ht
    exact lt_of_le_of_lt (hle2 ε hε t) ht

/-- **Theorem 14.5.1** (Blackwell's renewal theorem; MT p. 354), (14.35): for a non-lattice `Γ`
on `[0, ∞)` with finite mean `β`, every first-epoch law `Γ₀` on `ℝ` and `a ≤ b`,
`Γ₀ ∗ U[a + t, b + t] → β⁻¹ (b − a)`. -/
theorem theorem_14_5_1 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hnl : IsNonLattice Γ)
    (hm : renMean Γ ≠ ∞) (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun t => (renMeas Γ μ).real (Icc (a + t) (b + t))) atTop
      (𝓝 (((renMean Γ).toReal)⁻¹ * (b - a))) := by
  obtain ⟨K, hK, hKb⟩ := exists_window_bound Γ hΓ0 hΓpos hm (b - a)
  have hδ := blackwell_dirac Γ hΓ0 hΓpos hnl hm hab
  have hc0 : 0 ≤ ((renMean Γ).toReal)⁻¹ * (b - a) :=
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (sub_nonneg.2 hab)
  have hshift : ∀ x t, renMeas Γ (Measure.dirac x) (Icc (a + t) (b + t)) =
      renMeas Γ (Measure.dirac 1) (Icc (a + (t - x + 1)) (b + (t - x + 1))) := fun x t => by
    rw [renMeas_dirac_eq_map Γ x, Measure.map_apply (f := fun u => u + (x - 1))
      (measurable_id.add measurable_const) measurableSet_Icc]
    congr 1
    ext u
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hbd : ∀ s, renMeas Γ (Measure.dirac 1) (Icc (a + s) (b + s)) ≤ K := fun s => by
    rw [show b + s = a + s + (b - a) by ring]
    exact hKb (a + s)
  have hlim : ∀ x, Tendsto (fun t => renMeas Γ (Measure.dirac x) (Icc (a + t) (b + t))) atTop
      (𝓝 (ENNReal.ofReal (((renMean Γ).toReal)⁻¹ * (b - a)))) := fun x => by
    have hsh : Tendsto (fun t : ℝ => t - x + 1) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 - x) tendsto_id).congr fun t => by
        change t + (1 - x) = t - x + 1
        ring
    refine (ENNReal.tendsto_ofReal (hδ.comp hsh)).congr fun t => ?_
    rw [hshift x t]
    exact ofReal_measureReal (ne_top_of_le_ne_top hK (hbd _))
  have hint := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun t x => renMeas Γ (Measure.dirac x) (Icc (a + t) (b + t)))
    (f := fun _ => ENNReal.ofReal (((renMean Γ).toReal)⁻¹ * (b - a))) (fun _ => K)
    (Eventually.of_forall fun t => measurable_renMeas_dirac Γ measurableSet_Icc)
    (Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [hshift x t]
      exact hbd _)
    (by rw [lintegral_const, measure_univ, mul_one]; exact hK)
    (ae_of_all _ hlim)
  rw [lintegral_const, measure_univ, mul_one] at hint
  have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hint
  rw [ENNReal.toReal_ofReal hc0] at h2
  refine h2.congr fun t => ?_
  change (∫⁻ x, renMeas Γ (Measure.dirac x) (Icc (a + t) (b + t)) ∂μ).toReal =
    (renMeas Γ μ (Icc (a + t) (b + t))).toReal
  rw [← renMeas_eq_lintegral Γ μ measurableSet_Icc]

end MeynTweedie.FErgodicity
