/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.RenewalSkeletons

/-!
# The renewal measure of a delayed renewal process on `ℝ₊` (MT §14.5)

Meyn and Tweedie, §14.5, pp. 354–356. The delayed renewal process has epochs
`Z₁ = x, Z_{m+1} = x + Y₀ + ⋯ + Y_{m−1}` (`resEpoch x Y`), with first epoch `x ~ μ` and i.i.d.
increments `Yᵢ ~ Γ` (law `incr Γ = Γ^{⊗ℕ}`). Its renewal measure is
`μ ∗ U = Σ_{m ≥ 0} μ ∗ Γ^{m∗}`, the expected number of epochs in a set (`renMeas Γ μ`); in the
book's notation it is `Γ₀ ∗ U` with `Γ₀ = μ`.

* `renMeas_apply`, `renMeas_dirac_apply`, `renMeas_eq_lintegral`: `μ ∗ U(A) = ∫ μ(dx) δ_x ∗ U(A)`;
  `incr_map_partialSum`: `Y₀ + ⋯ + Y_{m−1}` has law `Γ^{m∗}`.
* `lintegral_exp_neg_partialSum`: `E e^{−(Y₀ + ⋯ + Y_{m−1})} = φᵐ` with `φ = ∫ e^{−y} Γ(dy)`;
  `exp_moment_lt_one`: `φ < 1` when `Γ` is not concentrated at `0`.
* **The renewal measure is locally finite** (`renMeas_dirac_Iic_le`): `δ_x ∗ U(−∞, t] ≤
  e^{t−x}/(1 − φ)` (a Chernoff bound for each `Γ^{m∗}` and a geometric series), so
  `U[0, t] < ∞` for every `t`; `renMeas_Iic_le`: `μ ∗ U(−∞, t] ≤ eᵗ/(1 − φ)` for every probability
  `μ` on `(0, ∞)`.
* `renMeas_Iic_zero`: for `μ` on `(0, ∞)`, `μ ∗ U` does not charge `(−∞, 0]`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The law `Γ^{⊗ℕ}` of the i.i.d. increments. -/
noncomputable abbrev incr (Γ : Measure ℝ) : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => Γ

/-- The renewal measure `μ ∗ U` (MT p. 354): the expected number of epochs
`Z_{m+1} = x + Y₀ + ⋯ + Y_{m−1}`, `m ≥ 0`, in a set, for first epoch `x ~ μ` and increments
`Γ^{⊗ℕ}`. -/
noncomputable def renMeas (Γ μ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun m : ℕ => (μ.prod (incr Γ)).map fun p => resEpoch p.1 p.2 (m + 1)

/-- `μ ∗ U(A) = Σₘ P(Z_{m+1} ∈ A)`. -/
theorem renMeas_apply (Γ μ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    renMeas Γ μ A = ∑' m : ℕ, (μ.prod (incr Γ)) {p | resEpoch p.1 p.2 (m + 1) ∈ A} := by
  rw [renMeas, Measure.sum_apply _ hA]
  exact tsum_congr fun m => Measure.map_apply (measurable_resEpoch (m + 1)) hA

/-- `δ_x ∗ U(A) = Σₘ P(x + Y₀ + ⋯ + Y_{m−1} ∈ A)`. -/
theorem renMeas_dirac_apply (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (x : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    renMeas Γ (Measure.dirac x) A = ∑' m : ℕ, incr Γ {w | resEpoch x w (m + 1) ∈ A} := by
  rw [renMeas_apply Γ _ hA]
  refine tsum_congr fun m => ?_
  rw [Measure.dirac_prod, Measure.map_apply (f := Prod.mk x) measurable_prodMk_left
    (s := {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (m + 1) ∈ A}) ((measurable_resEpoch (m + 1)) hA)]
  rfl

/-- `x ↦ δ_x ∗ U(A)` is measurable. -/
theorem measurable_renMeas_dirac (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {A : Set ℝ}
    (hA : MeasurableSet A) : Measurable fun x => renMeas Γ (Measure.dirac x) A := by
  simp_rw [renMeas_dirac_apply Γ _ hA]
  exact Measurable.tsum fun m : ℕ =>
    measurable_measure_prodMk_left (ν := incr Γ) ((measurable_resEpoch (m + 1)) hA)

/-- **The renewal measure is a mixture**: `μ ∗ U(A) = ∫ μ(dx) δ_x ∗ U(A)`. -/
theorem renMeas_eq_lintegral (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (μ : Measure ℝ)
    [SFinite μ] {A : Set ℝ} (hA : MeasurableSet A) :
    renMeas Γ μ A = ∫⁻ x, renMeas Γ (Measure.dirac x) A ∂μ := by
  simp_rw [renMeas_dirac_apply Γ _ hA]
  rw [renMeas_apply Γ μ hA]
  have hm : ∀ m : ℕ, Measurable fun x => incr Γ {w | resEpoch x w (m + 1) ∈ A} := fun m =>
    measurable_measure_prodMk_left ((measurable_resEpoch (m + 1)) hA)
  calc ∑' m : ℕ, (μ.prod (incr Γ)) {p | resEpoch p.1 p.2 (m + 1) ∈ A}
      = ∑' m : ℕ, ∫⁻ x, incr Γ {w | resEpoch x w (m + 1) ∈ A} ∂μ := tsum_congr fun m => by
        rw [Measure.prod_apply (s := {p : ℝ × (ℕ → ℝ) | resEpoch p.1 p.2 (m + 1) ∈ A})
          ((measurable_resEpoch (m + 1)) hA)]
        rfl
    _ = ∫⁻ x, ∑' m : ℕ, incr Γ {w | resEpoch x w (m + 1) ∈ A} ∂μ :=
        (lintegral_tsum fun m => (hm m).aemeasurable).symm

/-- The partial sum `Y₀ + ⋯ + Y_{m−1}` has law `Γ^{m∗}`. -/
theorem incr_map_partialSum (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (m : ℕ) :
    (incr Γ).map (fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i) = convPow Γ m := by
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range m, w i, w m) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply m)
  have h := congrArg (fun ρ : Measure (ℝ × ℝ) => ρ.map Prod.fst)
    (infinitePi_map_partialSum_next Γ m)
  rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
    one_smul] at h
  exact h

/-! ### Exponential moments and local finiteness -/

/-- `E e^{−(Y₀ + ⋯ + Y_{m−1})} = φᵐ`, `φ = ∫ e^{−y} Γ(dy)`. -/
theorem lintegral_exp_neg_partialSum (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (m : ℕ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range m, w i)) ∂incr Γ =
      (∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ) ^ m := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one, pow_zero]
  | succ m ih =>
    have hg : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-q.1)) *
        ENNReal.ofReal (Real.exp (-q.2)) :=
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        measurable_fst.neg)).mul (ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.measurable.comp measurable_snd.neg))
    have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range m, w i, w m) :=
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply m)
    have hmarg : (incr Γ).map (fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i) = convPow Γ m := by
      have h := congrArg (fun ρ : Measure (ℝ × ℝ) => ρ.map Prod.fst)
        (infinitePi_map_partialSum_next Γ m)
      rw [Measure.map_map measurable_fst hpair, Measure.map_fst_prod, measure_univ,
        one_smul] at h
      exact h
    have hsm : Measurable fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hexp : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-s)) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp measurable_neg)
    calc ∫⁻ w, ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range (m + 1), w i)) ∂incr Γ
        = ∫⁻ w, (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-q.1)) *
            ENNReal.ofReal (Real.exp (-q.2))) (∑ i ∈ Finset.range m, w i, w m) ∂incr Γ := by
          refine lintegral_congr fun w => ?_
          simp only [Finset.sum_range_succ, neg_add, Real.exp_add]
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ∫⁻ q, ENNReal.ofReal (Real.exp (-q.1)) * ENNReal.ofReal (Real.exp (-q.2))
            ∂((convPow Γ m).prod Γ) := by
          rw [← infinitePi_map_partialSum_next Γ m, lintegral_map hg hpair]
      _ = (∫⁻ s, ENNReal.ofReal (Real.exp (-s)) ∂convPow Γ m) *
            ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ :=
          lintegral_prod_mul hexp.aemeasurable hexp.aemeasurable
      _ = (∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ) ^ (m + 1) := by
          rw [← hmarg, lintegral_map hexp hsm, ih, pow_succ]

/-- `φ = ∫ e^{−y} Γ(dy) < 1` when `Γ` lives on `[0, ∞)` and is not concentrated at `0`. -/
theorem exp_moment_lt_one (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) : ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ < 1 := by
  have hexp : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-s)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp measurable_neg)
  have hg : Measurable fun s : ℝ => ENNReal.ofReal (1 - Real.exp (-s)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub
      (Real.continuous_exp.measurable.comp measurable_neg))
  -- `e^{−y} + (1 − e^{−y}) = 1` for `y ≥ 0`
  have hsplit : ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ +
      ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-y)) ∂Γ = 1 := by
    rw [← lintegral_add_left hexp]
    have hae : ∀ᵐ y ∂Γ, ENNReal.ofReal (Real.exp (-y)) + ENNReal.ofReal (1 - Real.exp (-y))
        = 1 := by
      rw [ae_iff]
      refine measure_mono_null (fun y hy => ?_) hΓ0
      by_contra hc
      have hy0 : 0 ≤ y := not_lt.1 hc
      have h1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      apply hy
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by linarith), add_sub_cancel,
        ENNReal.ofReal_one]
    rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]
  have hpos : 0 < ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-y)) ∂Γ := by
    rw [lintegral_pos_iff_support hg]
    refine lt_of_lt_of_le hΓpos (measure_mono fun y hy => ?_)
    rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
    have h1 : Real.exp (-y) < Real.exp 0 := Real.exp_lt_exp.2 (neg_lt_zero.2 hy)
    rwa [Real.exp_zero] at h1
  have hfin : ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsplit ▸ le_self_add)
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ
      < ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ +
          ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-y)) ∂Γ := ENNReal.lt_add_right hfin hpos.ne'
    _ = 1 := hsplit

/-- **Local finiteness of the renewal measure**: `δ_x ∗ U(−∞, t] ≤ e^{t−x} (1 − φ)⁻¹`, where
`φ = ∫ e^{−y} Γ(dy) < 1`. -/
theorem renMeas_dirac_Iic_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (x t : ℝ) :
    renMeas Γ (Measure.dirac x) (Iic t) ≤ ENNReal.ofReal (Real.exp (t - x)) *
      (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ := by
  set φ := ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ
  rw [renMeas_dirac_apply Γ x measurableSet_Iic, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  have hsm : Measurable fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hF : Measurable fun w : ℕ → ℝ =>
      ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range m, w i)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hsm.neg)
  -- Markov's inequality for `e^{−S_m}`
  have hmk := mul_meas_ge_le_lintegral hF (ENNReal.ofReal (Real.exp (x - t))) (μ := incr Γ)
  rw [lintegral_exp_neg_partialSum Γ m] at hmk
  have hsub : {w : ℕ → ℝ | resEpoch x w (m + 1) ∈ Iic t} ⊆
      {w | ENNReal.ofReal (Real.exp (x - t)) ≤
        ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range m, w i))} := fun w hw => by
    simp only [mem_ofPred_eq, mem_Iic, resEpoch_succ_eq] at hw ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  have hpos : ENNReal.ofReal (Real.exp (x - t)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hne : ENNReal.ofReal (Real.exp (x - t)) ≠ ∞ := ENNReal.ofReal_ne_top
  calc incr Γ {w | resEpoch x w (m + 1) ∈ Iic t}
      ≤ incr Γ {w | ENNReal.ofReal (Real.exp (x - t)) ≤
          ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range m, w i))} := measure_mono hsub
    _ ≤ φ ^ m / ENNReal.ofReal (Real.exp (x - t)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hne), mul_comm]
        exact hmk
    _ = (ENNReal.ofReal (Real.exp (x - t)))⁻¹ * φ ^ m := by
        rw [div_eq_mul_inv, mul_comm]
    _ = ENNReal.ofReal (Real.exp (t - x)) * φ ^ m := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_sub]

/-- For a probability `μ` on `(0, ∞)`, `μ ∗ U(−∞, t] ≤ eᵗ (1 − φ)⁻¹`. -/
theorem renMeas_Iic_le (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) (t : ℝ) :
    renMeas Γ μ (Iic t) ≤ ENNReal.ofReal (Real.exp t) *
      (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ := by
  rw [renMeas_eq_lintegral Γ μ measurableSet_Iic]
  calc ∫⁻ x, renMeas Γ (Measure.dirac x) (Iic t) ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp t) * (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ ∂μ := by
        refine lintegral_mono_ae ((show ∀ᵐ x ∂μ, 0 < x from ae_iff.2 (measure_mono_null
          (fun x hx => (not_lt.1 hx : x ≤ 0)) hμ)).mono fun x hx0 => ?_)
        refine (renMeas_dirac_Iic_le Γ x t).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by linarith))) le_rfl)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- For `μ` on `(0, ∞)` and `Γ` on `[0, ∞)`, the epochs are positive: `μ ∗ U(−∞, 0] = 0`. -/
theorem renMeas_Iic_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [SFinite μ] (hμ : μ (Iic 0) = 0) :
    renMeas Γ μ (Iic 0) = 0 := by
  have hnn : ∀ᵐ w ∂incr Γ, ∀ i, 0 ≤ w i :=
    (tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos).mono fun w hw => hw.2
  rw [renMeas_eq_lintegral Γ μ measurableSet_Iic]
  refine le_antisymm ?_ zero_le
  calc ∫⁻ x, renMeas Γ (Measure.dirac x) (Iic 0) ∂μ ≤ ∫⁻ _, 0 ∂μ := by
        refine lintegral_mono_ae ((show ∀ᵐ x ∂μ, 0 < x from ae_iff.2 (measure_mono_null
          (fun x hx => (not_lt.1 hx : x ≤ 0)) hμ)).mono fun x hx0 => ?_)
        rw [renMeas_dirac_apply Γ x measurableSet_Iic]
        refine le_of_eq (ENNReal.tsum_eq_zero.2 fun m => ?_)
        refine measure_mono_null (t := {a : ℕ → ℝ | ¬ ∀ i, 0 ≤ a i})
          (fun w hw hall => ?_) (ae_iff.1 hnn)
        simp only [mem_ofPred_eq, mem_Iic, resEpoch_succ_eq] at hw
        have : 0 ≤ ∑ i ∈ Finset.range m, w i := Finset.sum_nonneg fun i _ => hall i
        linarith
    _ = 0 := lintegral_zero

end MeynTweedie.VUniformErgodicity
