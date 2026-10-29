/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalChain
import FErgodicity.FNormMeasurable
import FErgodicity.ContinuousRenewal

/-!
# The uniform key renewal theorem: Proposition 14.5.3 (MT §14.5)

Meyn and Tweedie, Proposition 14.5.3, p. 356: for a spread-out `Γ` with finite mean and two
first-epoch laws `Γ₁, Γ₂` with finite mean, `Γ₁ ∗ U − Γ₂ ∗ U` has finite total variation (14.42).

* `renMeas_add`, `renMeas_dirac_add`, `renMeas_map_add_apply`: the renewal measure is additive in
  the first-epoch law and shifts with it.
* `exists_jordan`: a Jordan decomposition `l₁ + β = l₂ + α` with `α ≤ l₁`, `β ≤ l₂` and
  `α(X) + β(X) ≤ ‖l₁ − l₂‖` (from the Hahn decomposition).
* `renMeas_restrict_slab`: on the slab `(nδ, (n + 1)δ]`, `μ ∗ U = (μ(P^δ)ⁿ shifted by nδ) ∗ U`, the
  regeneration identity (14.43).
* **Proposition 14.5.3** (`proposition_14_5_3`, p. 356), (14.42): finite measures `σ₁, σ₂` with
  `Γ₁ ∗ U + σ₂ = Γ₂ ∗ U + σ₁`; this is (14.44): on each slab the difference is carried by the
  Jordan parts of `Γ₁P^{nδ} − Γ₂P^{nδ}`, of total mass at most `U[0, δ] ‖Γ₁P^{nδ} − Γ₂P^{nδ}‖`,
  and these are summable by (14.41).

**Hypotheses.** The first-epoch laws live on `(0, ∞)` (the forward recurrence time chain starts
from its first epoch), and `Γ` lives on `[0, ∞)` and is not concentrated at `0`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-! ### Algebra of renewal measures -/

/-- `(μ + ν) ∗ U = μ ∗ U + ν ∗ U`. -/
theorem renMeas_add (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    renMeas Γ (μ + ν) = renMeas Γ μ + renMeas Γ ν := by
  ext A hA
  rw [Measure.add_apply, renMeas_eq_lintegral Γ _ hA, renMeas_eq_lintegral Γ _ hA,
    renMeas_eq_lintegral Γ _ hA, lintegral_add_measure]

/-- `δ_{v+s} ∗ U(A) = δ_v ∗ U(A − s)`. -/
theorem renMeas_dirac_add (v s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    renMeas Γ (Measure.dirac (v + s)) A = renMeas Γ (Measure.dirac v) ((fun u => u + s) ⁻¹' A) := by
  rw [renMeas_dirac_apply Γ _ hA, renMeas_dirac_apply Γ v (A := (fun u => u + s) ⁻¹' A)
    ((measurable_id.add measurable_const) hA)]
  refine tsum_congr fun m => ?_
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_preimage, resEpoch_succ_eq]
  rw [add_right_comm]

/-- The renewal measure of a shifted first-epoch law:
`(λ shifted by s) ∗ U(A) = ∫ λ(dv) δ_v ∗ U(A − s)`. -/
theorem renMeas_map_add_apply (l' : Measure ℝ) [SFinite l'] (s : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    renMeas Γ (l'.map fun u => u + s) A =
      ∫⁻ v, renMeas Γ (Measure.dirac v) ((fun u => u + s) ⁻¹' A) ∂l' := by
  have hs : Measurable fun u : ℝ => u + s := measurable_id.add measurable_const
  rw [renMeas_eq_lintegral Γ _ hA, lintegral_map (measurable_renMeas_dirac Γ hA) hs]
  exact lintegral_congr fun v => renMeas_dirac_add Γ v s hA

/-! ### A Jordan decomposition -/

omit [IsProbabilityMeasure Γ] in
/-- **Jordan decomposition**: for finite `l₁, l₂` there are `α ≤ l₁`, `β ≤ l₂` with
`l₁ + β = l₂ + α` and `α(X) + β(X) ≤ ‖l₁ − l₂‖_1`. -/
theorem exists_jordan (l₁ l₂ : Measure ℝ) [IsFiniteMeasure l₁] [IsFiniteMeasure l₂] :
    ∃ α β : Measure ℝ, α ≤ l₁ ∧ β ≤ l₂ ∧ l₁ + β = l₂ + α ∧
      α univ + β univ ≤ fNorm 1 l₁ l₂ := by
  obtain ⟨S, hS, h1, h2⟩ := hahn_decomposition l₁ l₂
  have hle1 : l₂.restrict S ≤ l₁.restrict S := Measure.le_intro fun t ht _ => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h1 _ (ht.inter hS) inter_subset_right
  have hle2 : l₁.restrict Sᶜ ≤ l₂.restrict Sᶜ := Measure.le_intro fun t ht _ => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h2 _ (ht.inter hS.compl) inter_subset_right
  set α := l₁.restrict S - l₂.restrict S with hα
  set β := l₂.restrict Sᶜ - l₁.restrict Sᶜ with hβ
  have hαc : α + l₂.restrict S = l₁.restrict S := Measure.sub_add_cancel_of_le hle1
  have hβc : β + l₁.restrict Sᶜ = l₂.restrict Sᶜ := Measure.sub_add_cancel_of_le hle2
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · calc α ≤ α + l₂.restrict S := Measure.le_add_right le_rfl
      _ = l₁.restrict S := hαc
      _ ≤ l₁ := Measure.restrict_le_self
  · calc β ≤ β + l₁.restrict Sᶜ := Measure.le_add_right le_rfl
      _ = l₂.restrict Sᶜ := hβc
      _ ≤ l₂ := Measure.restrict_le_self
  · conv_lhs => rw [← Measure.restrict_add_restrict_compl hS (μ := l₁)]
    conv_rhs => rw [← Measure.restrict_add_restrict_compl hS (μ := l₂)]
    have e1 : l₁.restrict S + l₁.restrict Sᶜ + β = l₁.restrict S + (β + l₁.restrict Sᶜ) := by
      abel
    have e2 : l₂.restrict S + l₂.restrict Sᶜ + α = (α + l₂.restrict S) + l₂.restrict Sᶜ := by
      abel
    rw [e1, e2, hβc, hαc]
  · -- the masses of the Jordan parts
    have hαu : α univ = l₁ S - l₂ S := by
      rw [hα, Measure.sub_apply MeasurableSet.univ hle1, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
    have hβu : β univ = l₂ Sᶜ - l₁ Sᶜ := by
      rw [hβ, Measure.sub_apply MeasurableSet.univ hle2, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
    have h1S := h1 S hS subset_rfl
    have h2S := h2 Sᶜ hS.compl subset_rfl
    have hfs := ofReal_abs_fSigned_le_fNorm (f := 1) measurable_one (fun _ => ENNReal.one_ne_top)
      (by simp) (by simp) hS (μ := l₁) (ν := l₂)
    refine le_trans (le_of_eq ?_) ((ENNReal.ofReal_le_ofReal (le_abs_self _)).trans hfs)
    have e1 : ∀ ρ : Measure ℝ, (∫⁻ x in S, (1 : ℝ → ℝ≥0∞) x ∂ρ) = ρ S := fun ρ => by
      simp only [Pi.one_apply, setLIntegral_one]
    have e2 : ∀ ρ : Measure ℝ, (∫⁻ x, (1 : ℝ → ℝ≥0∞) x ∂ρ) = ρ univ := fun ρ => by
      simp only [Pi.one_apply, lintegral_one]
    rw [fSigned, e1, e1, e2, e2, hαu, hβu]
    have hS1 : l₁ univ = l₁ S + l₁ Sᶜ := (measure_add_measure_compl hS).symm
    have hS2 : l₂ univ = l₂ S + l₂ Sᶜ := (measure_add_measure_compl hS).symm
    rw [hS1, hS2, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨ENNReal.sub_ne_top (measure_ne_top _ _),
        ENNReal.sub_ne_top (measure_ne_top _ _)⟩), ENNReal.toReal_add
        (ENNReal.sub_ne_top (measure_ne_top _ _)) (ENNReal.sub_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_sub_of_le h1S (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le h2S (measure_ne_top _ _)]
    congr 1
    ring

/-! ### Slabs -/

/-- The slab `(nδ, (n + 1)δ]`. -/
def slab (δ : ℝ) (n : ℕ) : Set ℝ := Ioc ((n : ℝ) * δ) ((n + 1 : ℕ) * δ)

omit [IsProbabilityMeasure Γ] in
/-- The slabs are disjoint and cover `(0, ∞)`. -/
theorem iUnion_slab {δ : ℝ} (hδ : 0 < δ) : ⋃ n, slab δ n = Ioi 0 := by
  ext x
  simp only [mem_iUnion, slab, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩
    exact lt_of_le_of_lt (by positivity) h1
  · intro hx
    refine ⟨⌈x / δ⌉₊ - 1, ?_, ?_⟩
    · have hc : 1 ≤ ⌈x / δ⌉₊ := Nat.one_le_iff_ne_zero.2 (by
        rw [ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos hx hδ)
      have h := Nat.ceil_lt_add_one (div_pos hx hδ).le
      have : ((⌈x / δ⌉₊ - 1 : ℕ) : ℝ) = (⌈x / δ⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hc, Nat.cast_one]
      rw [this]
      have h2 : (⌈x / δ⌉₊ : ℝ) - 1 < x / δ := by linarith
      calc ((⌈x / δ⌉₊ : ℝ) - 1) * δ < x / δ * δ := mul_lt_mul_of_pos_right h2 hδ
        _ = x := div_mul_cancel₀ x hδ.ne'
    · have hc : 1 ≤ ⌈x / δ⌉₊ := Nat.one_le_iff_ne_zero.2 (by
        rw [ne_eq, Nat.ceil_eq_zero, not_le]; exact div_pos hx hδ)
      rw [show ⌈x / δ⌉₊ - 1 + 1 = ⌈x / δ⌉₊ by omega]
      calc x = x / δ * δ := (div_mul_cancel₀ x hδ.ne').symm
        _ ≤ (⌈x / δ⌉₊ : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le

omit [IsProbabilityMeasure Γ] in
/-- The slabs are pairwise disjoint. -/
theorem pairwise_disjoint_slab {δ : ℝ} (hδ : 0 < δ) :
    Pairwise fun m n => Disjoint (slab δ m) (slab δ n) := by
  intro m n hmn
  refine Set.disjoint_left.2 fun x hm hn => ?_
  simp only [slab, mem_Ioc] at hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [hm.2, hn.1]
  · have : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
    nlinarith [hm.1, hn.2]

/-- `δ_v ∗ U` gives each slab mass at most `U(δ) = e^δ (1 − φ)⁻¹` once shifted, for `v > 0`. -/
theorem renMeas_dirac_preimage_slab_le {δ : ℝ} (n : ℕ) {v : ℝ} (hv : 0 < v) :
    renMeas Γ (Measure.dirac v) ((fun u => u + n * δ) ⁻¹' slab δ n) ≤
      ENNReal.ofReal (Real.exp δ) * (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ := by
  refine (measure_mono fun u hu => ?_).trans ((renMeas_dirac_Iic_le Γ v δ).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))) le_rfl))
  simp only [mem_preimage, slab, mem_Ioc] at hu
  simp only [mem_Iic]
  push_cast at hu
  linarith [hu.2]

/-- **The renewal measure on a slab** ((14.43)): for a first-epoch law `μ` on `(0, ∞)`,
`(μ ∗ U)|_{(nδ, (n+1)δ]} = (μ(P^δ)ⁿ shifted by nδ) ∗ U|_{(nδ, (n+1)δ]}`. -/
theorem renMeas_restrict_slab (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : μ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    haveI := isMarkovKernel_fwdSkelKernel Γ δ
    (renMeas Γ μ).restrict (slab δ n) =
      (renMeas Γ (((fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ).map fun u => u + n * δ)).restrict
        (slab δ n) := by
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have := isMarkovKernel_pow (fwdSkelKernel Γ δ) n
  have hsl : MeasurableSet (slab δ n) := measurableSet_Ioc
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
    renMeas_eq_lintegral_skeleton Γ hΓ0 hΓpos μ hμ hδ n (hA.inter hsl)
      (fun x hx => hx.2.1), renMeas_map_add_apply Γ _ _ (hA.inter hsl)]

/-! ### Proposition 14.5.3 -/

/-- The skeleton keeps first-epoch laws on `(0, ∞)`. -/
theorem comp_pow_Iic_zero (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} (n : ℕ)
    (μ : Measure ℝ) (hμ : μ (Iic 0) = 0) :
    ((fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ) (Iic 0) = 0 := by
  rw [measure_kernel_apply _ _ measurableSet_Iic]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hxs => ?_) hμ
  by_contra hx0
  have hx : x ∈ Ioi (0 : ℝ) := not_le.1 (show ¬ x ≤ 0 from hx0)
  apply hxs
  have h := pow_compl_eq_zero_of_absorbing _ measurableSet_Ioi
    (fwdSkelKernel_compl_Ioi Γ hΓ0 hΓpos δ) n x hx
  rw [compl_Ioi] at h
  exact h

/-- **Proposition 14.5.3** (MT p. 356), (14.42): for a spread-out `Γ` on `[0, ∞)` with finite mean
and first-epoch laws `Γ₁, Γ₂` on `(0, ∞)` with finite means, `Γ₁ ∗ U − Γ₂ ∗ U` has finite total
variation: `Γ₁ ∗ U + σ₂ = Γ₂ ∗ U + σ₁` with `σ₁, σ₂` finite. -/
theorem proposition_14_5_3 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞) (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : μ₁ (Iic 0) = 0) (h₂ : μ₂ (Iic 0) = 0)
    (hm₁ : ∫⁻ x, ENNReal.ofReal x ∂μ₁ ≠ ∞) (hm₂ : ∫⁻ x, ENNReal.ofReal x ∂μ₂ ≠ ∞) :
    ∃ σ₁ σ₂ : Measure ℝ, IsFiniteMeasure σ₁ ∧ IsFiniteMeasure σ₂ ∧
      renMeas Γ μ₁ + σ₂ = renMeas Γ μ₂ + σ₁ := by
  obtain ⟨δ, hδ, hall⟩ := tsum_tvNorm_fwdSkel_ne_top Γ hΓ0 hΓpos hs hm
  have hT := hall δ hδ le_rfl μ₁ μ₂ h₁ h₂ hm₁ hm₂
  have := isMarkovKernel_fwdSkelKernel Γ δ
  set L : ℕ → ℕ → Measure ℝ := fun i n =>
    (fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ (if i = 1 then μ₁ else μ₂) with hL
  have hLp : ∀ i n, IsProbabilityMeasure (L i n) := fun i n => by
    have := isMarkovKernel_pow (fwdSkelKernel Γ δ) n
    by_cases hi : i = 1
    · simp only [hL, hi, ↓reduceIte]; infer_instance
    · simp only [hL, hi, ↓reduceIte]; infer_instance
  -- Jordan parts of `Γ₁P^{nδ} − Γ₂P^{nδ}`
  have hJ := fun n => exists_jordan (L 1 n) (L 2 n)
  choose α β hαle hβle heq hmass using hJ
  have hshm : ∀ n : ℕ, Measurable fun u : ℝ => u + n * δ := fun n =>
    measurable_id.add measurable_const
  set A : ℕ → Measure ℝ := fun n =>
    (renMeas Γ ((α n).map fun u => u + n * δ)).restrict (slab δ n) with hA
  set B : ℕ → Measure ℝ := fun n =>
    (renMeas Γ ((β n).map fun u => u + n * δ)).restrict (slab δ n) with hB
  have hαf : ∀ n, IsFiniteMeasure (α n) := fun n => by
    have := hLp 1 n
    exact ⟨lt_of_le_of_lt ((hαle n) univ) (measure_lt_top _ _)⟩
  have hβf : ∀ n, IsFiniteMeasure (β n) := fun n => by
    have := hLp 2 n
    exact ⟨lt_of_le_of_lt ((hβle n) univ) (measure_lt_top _ _)⟩
  set U := ENNReal.ofReal (Real.exp δ) * (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹
    with hUdef
  have hU : U ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne')
  -- the slab masses of a Jordan part
  have hslab : ∀ (n : ℕ) (ρ : Measure ℝ) [IsFiniteMeasure ρ], ρ (Iic 0) = 0 →
      renMeas Γ (ρ.map fun u => u + n * δ) (slab δ n) ≤ U * ρ univ := fun n ρ _ hρ => by
    rw [renMeas_map_add_apply Γ ρ _ (show MeasurableSet (slab δ n) from measurableSet_Ioc)]
    calc ∫⁻ v, renMeas Γ (Measure.dirac v) ((fun u => u + n * δ) ⁻¹' slab δ n) ∂ρ
        ≤ ∫⁻ _, U ∂ρ := by
          refine lintegral_mono_ae ((show ∀ᵐ v ∂ρ, 0 < v from ae_iff.2 (measure_mono_null
            (fun v hv => (not_lt.1 hv : v ≤ 0)) hρ)).mono fun v hv => ?_)
          exact renMeas_dirac_preimage_slab_le Γ n hv
      _ = U * ρ univ := lintegral_const U
  have hLi : ∀ i n, L i n (Iic 0) = 0 := fun i n => by
    by_cases hi : i = 1
    · simp only [hL, hi, ↓reduceIte]; exact comp_pow_Iic_zero Γ hΓ0 hΓpos n μ₁ h₁
    · simp only [hL, hi, ↓reduceIte]; exact comp_pow_Iic_zero Γ hΓ0 hΓpos n μ₂ h₂
  have hfinA : ∀ n, A n univ ≤ U * fNorm 1 (L 1 n) (L 2 n) := fun n => by
    rw [hA, Measure.restrict_apply_univ]
    refine (hslab n (α n) (measure_mono_null (fun x hx => hx) ?_)).trans
      (mul_le_mul' le_rfl (le_self_add.trans (hmass n)))
    exact measure_mono_null (fun x hx => hx) (le_antisymm ((hαle n) _ |>.trans (le_of_eq
      (hLi 1 n))) zero_le)
  have hfinB : ∀ n, B n univ ≤ U * fNorm 1 (L 1 n) (L 2 n) := fun n => by
    rw [hB, Measure.restrict_apply_univ]
    refine (hslab n (β n) ?_).trans (mul_le_mul' le_rfl (le_add_self.trans (hmass n)))
    exact le_antisymm ((hβle n) _ |>.trans (le_of_eq (hLi 2 n))) zero_le
  have hsumT : ∑' n, fNorm 1 (L 1 n) (L 2 n) ≠ ∞ := by
    refine ne_top_of_le_ne_top hT (le_of_eq (tsum_congr fun n => ?_))
    have := hLp 1 n
    have := hLp 2 n
    rw [fNorm_one]
    simp only [hL, ↓reduceIte, show (2 : ℕ) ≠ 1 by norm_num]
  refine ⟨Measure.sum A, Measure.sum B, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · rw [Measure.sum_apply _ MeasurableSet.univ]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hfinA) ?_
    rw [ENNReal.tsum_mul_left]
    exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hU hsumT)
  · rw [Measure.sum_apply _ MeasurableSet.univ]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hfinB) ?_
    rw [ENNReal.tsum_mul_left]
    exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hU hsumT)
  · -- slab by slab
    have hsplit : ∀ (ρ : Measure ℝ), ρ (Iic 0) = 0 →
        ρ = Measure.sum fun n => ρ.restrict (slab δ n) := fun ρ hρ => by
      rw [← Measure.restrict_iUnion (pairwise_disjoint_slab hδ) (fun n => measurableSet_Ioc),
        iUnion_slab hδ]
      refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hρ
      exact not_lt.1 (show ¬ 0 < x from hx)
    have hR1 := renMeas_Iic_zero Γ hΓ0 hΓpos μ₁ h₁
    have hR2 := renMeas_Iic_zero Γ hΓ0 hΓpos μ₂ h₂
    rw [hsplit _ hR1, hsplit _ hR2, Measure.sum_add_sum, Measure.sum_add_sum]
    congr 1
    funext n
    have := isMarkovKernel_pow (fwdSkelKernel Γ δ) n
    have e1 := renMeas_restrict_slab Γ hΓ0 hΓpos μ₁ h₁ hδ.le n
    have e2 := renMeas_restrict_slab Γ hΓ0 hΓpos μ₂ h₂ hδ.le n
    rw [e1, e2, hA, hB]
    simp only
    rw [← Measure.restrict_add, ← Measure.restrict_add, ← renMeas_add, ← renMeas_add,
      ← Measure.map_add _ _ (hshm n), ← Measure.map_add _ _ (hshm n)]
    have h1 : (fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ₁ = L 1 n := by simp only [hL, ↓reduceIte]
    have h2 : (fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ₂ = L 2 n := by
      simp only [hL, show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
    rw [h1, h2, heq n]

end MeynTweedie.FErgodicity
