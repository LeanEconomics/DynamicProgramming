/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.RenewalSkeletons
import Ergodicity.Invariance
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The invariant measure of the forward recurrence time `δ`-skeleton (MT §10.5.2)

Meyn and Tweedie, §10.5.2, pp. 248–249. `fwdSkelKernel Γ δ` is the kernel of the forward
recurrence time `δ`-skeleton `V⁺_δ` of a renewal process with increment law `Γ`
(`RenewalSkeletons`), where `Γ` lives on `[0, ∞)` and is not concentrated at `0`, and `δ ≥ 0`.
Write `F[y, ∞) = Γ[y, ∞)`.

* `tsum_straddle`: for `s > 0` exactly one renewal interval `[Sⱼ, Sⱼ₊₁)` straddles `s`:
  `Σⱼ 1{Sⱼ < s ≤ Sⱼ + wⱼ} = 1`; `tsum_prod_straddle`: hence
  `Σⱼ (Γ^{j∗} ⊗ Γ){t < s ≤ t + v} = 1`.
* `fwdSkelKernel_apply_eq_tsum`: for `x ≤ δ` and `A ⊆ (0, ∞)`,
  `P^δ(x, A) = Σⱼ (Γ^{j∗} ⊗ Γ){x + t ≤ δ, x + t + v − δ ∈ A}`.
* `fwdSkelKernel_Iic_zero`: `V⁺_δ` lives on `(0, ∞)`.
* `fwdSkelInv Γ`: the measure `F[y, ∞) dy` on `(0, ∞)`; `isInvariant_fwdSkelInv` (10.36): it is
  invariant for `V⁺_δ`, for every `δ ≥ 0` ("by direct integration", p. 249);
  `fwdSkelInv_univ`: its total mass is the mean `m = ∫ t F(dt)`, so `m⁻¹ F[y, ∞) dy` is an
  invariant probability when `m < ∞` (`isProbabilityMeasure_fwdSkelInv_normalised`).

**Not formalised.** The sandwich `F[y, ∞) dy ≤ U_{[0, δ]}(x, dy) ≤ F[y − δ, ∞) dy` and the
argument through `δ/2ⁿ`, which the book uses to guess (10.36) before verifying it directly.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### The renewal interval straddling a time -/

/-- Pathwise: for `s > 0`, exactly one renewal interval `[Sⱼ, Sⱼ + wⱼ)` contains `s` (with `Sⱼ`
strictly before `s`). -/
theorem tsum_straddle {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) {s : ℝ} (hs : 0 < s) :
    ∑' j, {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
      (∑ i ∈ Finset.range j, w i, w j) = 1 := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, w i with hS
  have hex : ∃ m, s ≤ S (m + 1) := by
    obtain ⟨m, hm⟩ := (hdiv.eventually_ge_atTop s).exists
    exact ⟨m, le_trans hm (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by omega)) fun i _ _ => hw i)⟩
  set τ := sInf {m | s ≤ S (m + 1)} with hτdef
  have hτ : s ≤ S (τ + 1) := Nat.sInf_mem hex
  have hmin : ∀ m < τ, S (m + 1) < s := fun m hm => not_le.1 (Nat.notMem_of_lt_sInf hm)
  have hmono : ∀ a b, a ≤ b → S a ≤ S b := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab) fun i _ _ => hw i
  have hSτ : S τ < s := by
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · rw [h0]; simpa [hS] using hs
    · have := hmin (τ - 1) (by omega)
      rwa [show τ - 1 + 1 = τ by omega] at this
  have hsucc : ∀ j, S j + w j = S (j + 1) := fun j => (Finset.sum_range_succ w j).symm
  rw [tsum_eq_single τ]
  · rw [indicator_of_mem (show (S τ, w τ) ∈ {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2} from
      ⟨hSτ, by simp only; rw [hsucc]; exact hτ⟩)]
    rfl
  · intro j hj
    refine indicator_of_notMem ?_ _
    rintro ⟨h1, h2⟩
    change S j < s at h1
    change s ≤ S j + w j at h2
    rw [hsucc] at h2
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact absurd h2 (not_le.2 (hmin j hlt))
    · exact absurd h1 (not_lt.2 (hτ.trans (hmono _ _ (by omega))))

/-- `w ↦ (Sⱼ, wⱼ)` is measurable. -/
theorem measurable_partialSum_pair (j : ℕ) :
    Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) :=
  (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)

/-- `(Γ^{j∗} ⊗ Γ)(E) = Γ^{⊗ℕ}{(Sⱼ, wⱼ) ∈ E}`. -/
theorem convPow_prod_apply (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (j : ℕ)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    ((convPow Γ j).prod Γ) E = ∫⁻ w, E.indicator 1 (∑ i ∈ Finset.range j, w i, w j)
      ∂(Measure.infinitePi fun _ : ℕ => Γ) := by
  rw [← infinitePi_map_partialSum_next, ← lintegral_indicator_one hE,
    lintegral_map (measurable_one.indicator hE) (measurable_partialSum_pair j)]

/-- For `s > 0`: `Σⱼ (Γ^{j∗} ⊗ Γ){t < s ≤ t + v} = 1`. -/
theorem tsum_prod_straddle (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    ∑' j, ((convPow Γ j).prod Γ) {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2} = 1 := by
  have hE : MeasurableSet {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2} :=
    (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_le measurable_const (measurable_fst.add measurable_snd))
  simp_rw [convPow_prod_apply Γ _ hE]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) (Measure.infinitePi fun _ : ℕ => Γ) := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (measurable_partialSum_pair j)).aemeasurable
  rw [← lintegral_tsum hmj]
  rw [lintegral_congr_ae ((tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos).mono fun w hw =>
    tsum_straddle hw.2 hw.1 hs), lintegral_one, measure_univ]

/-! ### The kernel of the skeleton -/

/-- For `x ≤ δ` and `A ⊆ (0, ∞)`: `P^δ(x, A) = Σⱼ (Γ^{j∗} ⊗ Γ){x + t ≤ δ, x + t + v − δ ∈ A}`. -/
theorem fwdSkelKernel_apply_eq_tsum (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ x : ℝ} (hxδ : x ≤ δ) {A : Set ℝ}
    (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0) :
    fwdSkelKernel Γ δ x A =
      ∑' j, ((convPow Γ j).prod Γ) {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  have hE : MeasurableSet {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A} :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hA)
  rw [fwdSkelKernel, recursionKernel_apply' ν (measurable_fwdSkelStep δ) x hA,
    ← lintegral_indicator_one (s := {w | fwdSkelStep δ (x, w) ∈ A})
      (((measurable_fwdSkelStep δ).comp measurable_prodMk_left) hA)]
  have hae : ∀ᵐ w ∂ν, {w | fwdSkelStep δ (x, w) ∈ A}.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) w =
      ∑' j, {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j) := by
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
    rw [← indicator_fwdTimeCts_eq_tsum hxδ hw hdiv hA0]
    by_cases h : fwdSkelStep δ (x, w) ∈ A
    · rw [indicator_of_mem (show w ∈ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_mem (show fwdTimeCts (resEpoch x w) δ ∈ A from h)]
      rfl
    · rw [indicator_of_notMem (show w ∉ {w | fwdSkelStep δ (x, w) ∈ A} from h),
        indicator_of_notMem (show fwdTimeCts (resEpoch x w) δ ∉ A from h)]
  have hmj : ∀ j, AEMeasurable (fun w : ℕ → ℝ =>
      {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ A}.indicator (1 : ℝ × ℝ → ℝ≥0∞)
        (∑ i ∈ Finset.range j, w i, w j)) ν := fun j =>
    (Measurable.indicator measurable_one hE |>.comp (measurable_partialSum_pair j)).aemeasurable
  rw [lintegral_congr_ae hae, lintegral_tsum hmj]
  exact tsum_congr fun j => (convPow_prod_apply Γ j hE).symm

/-- `V⁺_δ` lives on `(0, ∞)`: `P^δ(x, (−∞, 0]) = 0`. -/
theorem fwdSkelKernel_Iic_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) (δ x : ℝ) : fwdSkelKernel Γ δ x (Iic 0) = 0 := by
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  rw [fwdSkelKernel, recursionKernel_apply' ν (measurable_fwdSkelStep δ) x measurableSet_Iic]
  refine measure_mono_null (fun w hw => ?_) (ae_iff.1
    (tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos))
  simp only [mem_ofPred_eq, mem_Iic] at hw ⊢
  intro ⟨hdiv, hwpos⟩
  have hex := exists_resEpoch_gt (x := x) hdiv δ
  have hτ : δ < resEpoch x w (sInf {m | δ < resEpoch x w (m + 1)} + 1) := Nat.sInf_mem hex
  have := fwdTimeCts_eq_resEpoch (x := x) (t := δ) hwpos hdiv
  change fwdTimeCts (resEpoch x w) δ ≤ 0 at hw
  rw [this] at hw
  linarith

/-! ### Direct integration -/

/-- `if c then a else b = a` when `c` holds. -/
theorem ite_of_cond {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- `if c then a else b = b` when `c` fails. -/
theorem ite_of_not_cond {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- `y ↦ F[y, ∞) = Γ[y, ∞)` is measurable. -/
theorem measurable_tail_Ici (Γ : Measure ℝ) : Measurable fun y : ℝ => Γ (Ici y) :=
  Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab)

/-- `u ↦ Γ{v : u + v ∈ B}` is measurable. -/
theorem measurable_shift_measure (Γ : Measure ℝ) [SFinite Γ] {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun u : ℝ => Γ {v | u + v ∈ B} :=
  measurable_measure_prodMk_left (s := {p : ℝ × ℝ | p.1 + p.2 ∈ B}) (measurable_add hB)

/-- The section of `{x + t ≤ δ, x + t + v − δ ∈ B}` at `t`. -/
theorem prod_apply_window (Γ μ : Measure ℝ) [SFinite Γ] [SFinite μ] {δ x : ℝ} {B : Set ℝ}
    (hB : MeasurableSet B) :
    (μ.prod Γ) {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ B} =
      ∫⁻ t, (if x + t ≤ δ then Γ {v | (x + t - δ) + v ∈ B} else 0) ∂μ := by
  have hE : MeasurableSet {q : ℝ × ℝ | x + q.1 ≤ δ ∧ x + q.1 + q.2 - δ ∈ B} :=
    (measurableSet_le (measurable_const.add measurable_fst) measurable_const).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hB)
  rw [Measure.prod_apply hE]
  refine lintegral_congr fun t => ?_
  by_cases h : x + t ≤ δ
  · simp only [h, ite_true]
    congr 1
    ext v
    simp only [mem_preimage, mem_ofPred_eq, h, true_and]
    ring_nf
  · simp only [h, ite_false]
    convert measure_empty (μ := Γ)
    ext v
    simp [h]

/-- The section of `{t < s ≤ t + v}` at `t` is `[s − t, ∞)`. -/
theorem prod_apply_straddle (Γ μ : Measure ℝ) [SFinite Γ] [SFinite μ] (s : ℝ) :
    (μ.prod Γ) {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2} =
      ∫⁻ t, (if t < s then Γ (Ici (s - t)) else 0) ∂μ := by
  have hE : MeasurableSet {q : ℝ × ℝ | q.1 < s ∧ s ≤ q.1 + q.2} :=
    (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_le measurable_const (measurable_fst.add measurable_snd))
  rw [Measure.prod_apply hE]
  refine lintegral_congr fun t => ?_
  by_cases h : t < s
  · simp only [h, ite_true]
    congr 1
    ext v
    simp only [mem_preimage, mem_ofPred_eq, h, true_and, mem_Ici]
    constructor <;> intro hv <;> linarith
  · simp only [h, ite_false]
    convert measure_empty (μ := Γ)
    ext v
    simp [h]

/-- The core computation of §10.5.2: for `δ ≥ 0` and `B ⊆ (0, ∞)`,
`∫_{(0, δ]} F[x, ∞) P^δ(x, B) dx = ∫_{[0, δ)} Γ(B + r) dr`. -/
theorem fwdSkel_core (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} {B : Set ℝ} (hB : MeasurableSet B) (hB0 : B ⊆ Ioi 0) :
    ∫⁻ x, (if 0 < x ∧ x ≤ δ then Γ (Ici x) * fwdSkelKernel Γ δ x B else 0) =
      ∫⁻ r, (if 0 ≤ r ∧ r < δ then Γ {w | -r + w ∈ B} else 0) := by
  set h : ℝ → ℝ≥0∞ := fun u => Γ {v | u + v ∈ B} with hh
  have hhm : Measurable h := measurable_shift_measure Γ hB
  have hFm := measurable_tail_Ici Γ
  -- the integrand as a sum of integrals over the renewal times
  set G : ℝ → ℝ → ℝ≥0∞ := fun x t =>
    if (0 < x ∧ x ≤ δ) ∧ x + t ≤ δ then Γ (Ici x) * h (x + t - δ) else 0 with hG
  have hGm : Measurable (Function.uncurry G) := by
    refine Measurable.ite ?_ ((hFm.comp measurable_fst).mul
      (hhm.comp ((measurable_fst.add measurable_snd).sub measurable_const))) measurable_const
    exact ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)).inter
        (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
  have h1 : ∀ x, (if 0 < x ∧ x ≤ δ then Γ (Ici x) * fwdSkelKernel Γ δ x B else 0) =
      ∑' j, ∫⁻ t, G x t ∂convPow Γ j := by
    intro x
    by_cases hx : 0 < x ∧ x ≤ δ
    · simp only [hx]
      rw [fwdSkelKernel_apply_eq_tsum Γ hΓ0 hΓpos hx.2 hB hB0, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun j => ?_
      have := isProbabilityMeasure_convPow_real Γ j
      rw [prod_apply_window Γ _ hB, ← lintegral_const_mul' _ _ (measure_ne_top Γ _)]
      refine lintegral_congr fun t => ?_
      by_cases ht : x + t ≤ δ <;> simp [hG, hh, hx, ht]
    · simp only [hx, ite_false]
      symm
      refine ENNReal.tsum_eq_zero.2 fun j => ?_
      simp [hG, hx]
  simp_rw [h1]
  have hGj : ∀ j, AEMeasurable (fun x => ∫⁻ t, G x t ∂convPow Γ j) volume := fun j => by
    have := isProbabilityMeasure_convPow_real Γ j
    exact (hGm.lintegral_prod_right').aemeasurable
  rw [lintegral_tsum hGj]
  -- swap `x` and `t`, and substitute `x = δ − t − r`
  set K : ℝ → ℝ → ℝ≥0∞ := fun t r =>
    if 0 ≤ r ∧ t + r < δ ∧ -t ≤ r then Γ (Ici (δ - r - t)) * h (-r) else 0 with hK
  have hKm : Measurable (Function.uncurry K) := by
    refine Measurable.ite ?_ ((hFm.comp ((measurable_const.sub measurable_snd).sub
      measurable_fst)).mul (hhm.comp measurable_snd.neg)) measurable_const
    exact (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_lt (measurable_fst.add measurable_snd) measurable_const).inter
        (measurableSet_le measurable_fst.neg measurable_snd))
  have h2 : ∀ j, ∫⁻ x, ∫⁻ t, G x t ∂convPow Γ j = ∫⁻ r, ∫⁻ t, K t r ∂convPow Γ j := by
    intro j
    have := isProbabilityMeasure_convPow_real Γ j
    rw [lintegral_lintegral_swap hGm.aemeasurable,
      lintegral_lintegral_swap (f := fun r t => K t r) (hKm.comp measurable_swap).aemeasurable]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_sub_left_eq_self (fun x => G x t) (δ - t)]
    refine lintegral_congr fun r => ?_
    simp only [hG, hK]
    have hc : ((0 < δ - t - r ∧ δ - t - r ≤ δ) ∧ δ - t - r + t ≤ δ) ↔
        (0 ≤ r ∧ t + r < δ ∧ -t ≤ r) := by
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    by_cases hcond : 0 ≤ r ∧ t + r < δ ∧ -t ≤ r
    · rw [ite_of_cond ((hc.2 hcond)), ite_of_cond (hcond),
        show δ - t - r = δ - r - t by ring, show δ - r - t + t - δ = -r by ring]
    · rw [ite_of_not_cond ((fun h' => hcond (hc.1 h'))),
        ite_of_not_cond (hcond)]
  simp_rw [h2]
  have hKj : ∀ j, AEMeasurable (fun r => ∫⁻ t, K t r ∂convPow Γ j) volume := fun j => by
    have := isProbabilityMeasure_convPow_real Γ j
    exact (hKm.comp measurable_swap).lintegral_prod_right'.aemeasurable
  rw [← lintegral_tsum hKj]
  refine lintegral_congr fun r => ?_
  by_cases hr : 0 ≤ r
  · have hK' : ∀ j, ∫⁻ t, K t r ∂convPow Γ j = h (-r) *
        ((convPow Γ j).prod Γ) {q : ℝ × ℝ | q.1 < δ - r ∧ δ - r ≤ q.1 + q.2} := by
      intro j
      have := isProbabilityMeasure_convPow_real Γ j
      rw [prod_apply_straddle, ← lintegral_const_mul' _ _ (measure_ne_top Γ _)]
      refine lintegral_congr_ae ?_
      have hpos : ∀ᵐ t ∂convPow Γ j, 0 ≤ t := by
        rw [ae_iff]
        have hset : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext a; simp
        rw [hset]
        exact convPow_Iio_zero Γ hΓ0 j
      filter_upwards [hpos] with t ht
      simp only [hK]
      by_cases htr : t < δ - r
      · have hc : 0 ≤ r ∧ t + r < δ ∧ -t ≤ r := ⟨hr, by linarith, by linarith⟩
        rw [ite_of_cond (hc), ite_of_cond (htr)]
        rw [mul_comm]
      · have hc : ¬ (0 ≤ r ∧ t + r < δ ∧ -t ≤ r) := fun h' => htr (by linarith [h'.2.1])
        rw [ite_of_not_cond (hc), ite_of_not_cond (htr), mul_zero]
    simp_rw [hK']
    rw [ENNReal.tsum_mul_left]
    by_cases hrδ : r < δ
    · rw [tsum_prod_straddle Γ hΓ0 hΓpos (by linarith), mul_one,
        ite_of_cond (⟨hr, hrδ⟩)]
    · rw [ite_of_not_cond ((fun h' => hrδ h'.2))]
      refine mul_eq_zero.2 (Or.inr (ENNReal.tsum_eq_zero.2 fun j => ?_))
      have := isProbabilityMeasure_convPow_real Γ j
      refine measure_mono_null (t := Iio 0 ×ˢ univ) (fun q hq => ?_) ?_
      · simp only [mem_ofPred_eq] at hq
        exact ⟨by simp only [mem_Iio]; linarith [hq.1], mem_univ _⟩
      · rw [Measure.prod_prod, convPow_Iio_zero Γ hΓ0 j, zero_mul]
  · rw [ite_of_not_cond ((fun h' => hr h'.1))]
    refine ENNReal.tsum_eq_zero.2 fun j => ?_
    refine lintegral_eq_zero_iff (hKm.comp (measurable_id.prodMk measurable_const)) |>.2 ?_
    exact Eventually.of_forall fun t => by simp [hK, hr]

/-- `∫_{[0, δ)} Γ(B + r) dr = ∫_B Γ[y, y + δ) dy`. -/
theorem lintegral_shift_window (Γ : Measure ℝ) [SFinite Γ] (δ : ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ∫⁻ r, (if 0 ≤ r ∧ r < δ then Γ {w | -r + w ∈ B} else 0) =
      ∫⁻ y, B.indicator (fun y => Γ {w | y ≤ w ∧ w < y + δ}) y := by
  set φ : ℝ → ℝ → ℝ≥0∞ := fun r w =>
    if 0 ≤ r ∧ r < δ then B.indicator 1 (-r + w) else 0 with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    refine Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const))
      ((measurable_one.indicator hB).comp (measurable_fst.neg.add measurable_snd))
      measurable_const
  have e1 : ∀ r, (if 0 ≤ r ∧ r < δ then Γ {w | -r + w ∈ B} else 0) = ∫⁻ w, φ r w ∂Γ := by
    intro r
    by_cases hr : 0 ≤ r ∧ r < δ
    · rw [ite_of_cond hr, ← lintegral_indicator_one (s := {w | -r + w ∈ B})
        (measurable_const_add (-r) hB)]
      refine lintegral_congr fun w => ?_
      simp only [hφ, ite_of_cond hr]
      by_cases hw : -r + w ∈ B
      · rw [indicator_of_mem (show w ∈ {w | -r + w ∈ B} from hw), indicator_of_mem hw]
        rfl
      · rw [indicator_of_notMem (show w ∉ {w | -r + w ∈ B} from hw), indicator_of_notMem hw]
    · rw [ite_of_not_cond hr]
      symm
      simp [hφ, hr]
  simp_rw [e1]
  rw [lintegral_lintegral_swap hφm.aemeasurable]
  have e2 : ∀ w, ∫⁻ r, φ r w = ∫⁻ y, (if 0 ≤ w - y ∧ w - y < δ then B.indicator 1 y else 0) := by
    intro w
    rw [← lintegral_sub_left_eq_self (fun r => φ r w) w]
    refine lintegral_congr fun y => ?_
    simp only [hφ, show -(w - y) + w = y by ring]
  simp_rw [e2]
  have hψm : Measurable (Function.uncurry fun (w y : ℝ) =>
      (if 0 ≤ w - y ∧ w - y < δ then B.indicator (1 : ℝ → ℝ≥0∞) y else 0)) := by
    refine Measurable.ite ((measurableSet_le measurable_const
      (measurable_fst.sub measurable_snd)).inter
      (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))
      ((measurable_one.indicator hB).comp measurable_snd) measurable_const
  rw [lintegral_lintegral_swap hψm.aemeasurable]
  refine lintegral_congr fun y => ?_
  have hset : MeasurableSet {w : ℝ | y ≤ w ∧ w < y + δ} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy (f := fun y => Γ {w | y ≤ w ∧ w < y + δ}),
      ← lintegral_indicator_one hset]
    refine lintegral_congr fun w => ?_
    by_cases hw : y ≤ w ∧ w < y + δ
    · rw [ite_of_cond (show 0 ≤ w - y ∧ w - y < δ from ⟨by linarith, by linarith⟩),
        indicator_of_mem hy, indicator_of_mem (s := {w : ℝ | y ≤ w ∧ w < y + δ}) hw]
      rfl
    · rw [ite_of_not_cond (show ¬ (0 ≤ w - y ∧ w - y < δ) from fun h =>
        hw ⟨by linarith, by linarith⟩), indicator_of_notMem (s := {w : ℝ | y ≤ w ∧ w < y + δ}) hw]
  · rw [indicator_of_notMem hy (f := fun y => Γ {w | y ≤ w ∧ w < y + δ})]
    simp [indicator_of_notMem hy]

/-- The measure `F[y, ∞) dy` on `(0, ∞)` (10.36), unnormalised. -/
noncomputable def fwdSkelInv (Γ : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun y => Γ (Ici y)

/-- **(10.36)** (MT p. 248): `F[y, ∞) dy` on `(0, ∞)` is invariant for the forward recurrence time
`δ`-skeleton `V⁺_δ`, for every `δ ≥ 0`. -/
theorem isInvariant_fwdSkelInv (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0)
    (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsInvariant (fwdSkelKernel Γ δ) (fwdSkelInv Γ) := by
  have hFm := measurable_tail_Ici Γ
  ext A hA
  set B := A ∩ Ioi 0 with hBdef
  have hB : MeasurableSet B := hA.inter measurableSet_Ioi
  have hB0 : B ⊆ Ioi 0 := inter_subset_right
  have hAB : ∀ x, fwdSkelKernel Γ δ x A = fwdSkelKernel Γ δ x B := fun x => by
    have h1 := measure_inter_add_sdiff (μ := fwdSkelKernel Γ δ x) A
      (measurableSet_Ioi (a := (0 : ℝ)))
    have : fwdSkelKernel Γ δ x (A \ Ioi 0) = 0 :=
      measure_mono_null (fun y hy => by simpa using hy.2) (fwdSkelKernel_Iic_zero Γ hΓ0 hΓpos δ x)
    rw [this, add_zero] at h1
    exact h1.symm
  rw [measure_kernel_apply _ _ hA, fwdSkelInv, lintegral_withDensity_eq_lintegral_mul _ hFm
    (Kernel.measurable_coe _ hA), withDensity_apply _ hA, Measure.restrict_restrict hA,
    ← hBdef]
  simp_rw [Pi.mul_apply, hAB]
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator hB]
  set f : ℝ → ℝ≥0∞ := fun x => Γ (Ici x) * fwdSkelKernel Γ δ x B with hf
  have hfm : Measurable f := hFm.mul (Kernel.measurable_coe _ hB)
  have hsplit : ∀ x, (Ioi 0).indicator f x =
      (if 0 < x ∧ x ≤ δ then f x else 0) + (if δ < x then f x else 0) := by
    intro x
    by_cases h1 : 0 < x ∧ x ≤ δ
    · rw [indicator_of_mem (show x ∈ Ioi 0 from h1.1), ite_of_cond h1,
        ite_of_not_cond (show ¬ δ < x by linarith [h1.2]), add_zero]
    · rw [ite_of_not_cond h1, zero_add]
      by_cases h2 : δ < x
      · rw [indicator_of_mem (show x ∈ Ioi 0 by simp only [mem_Ioi]; linarith), ite_of_cond h2]
      · rw [ite_of_not_cond h2]
        refine indicator_of_notMem (fun hx => h1 ⟨hx, by linarith⟩) _
  simp_rw [hsplit]
  have hm1 : Measurable fun x : ℝ => if 0 < x ∧ x ≤ δ then f x else 0 :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) hfm measurable_const
  rw [lintegral_add_left hm1,
    fwdSkel_core Γ hΓ0 hΓpos hB hB0, lintegral_shift_window Γ δ hB]
  -- the jump part `x > δ`
  have e3 : ∫⁻ x, (if δ < x then f x else 0) = ∫⁻ y, B.indicator (fun y => Γ (Ici (y + δ))) y := by
    rw [← lintegral_add_right_eq_self (fun x => if δ < x then f x else 0) δ]
    refine lintegral_congr fun y => ?_
    by_cases hy : 0 < y
    · rw [ite_of_cond (show δ < y + δ by linarith), hf]
      simp only
      rw [fwdSkelKernel_of_lt Γ hΓ0 hΓpos hδ (by linarith), Measure.dirac_apply' _ hB,
        show y + δ - δ = y by ring]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB, indicator_of_mem hyB, Pi.one_apply, mul_one]
      · rw [indicator_of_notMem hyB, indicator_of_notMem hyB, mul_zero]
    · rw [ite_of_not_cond (show ¬ δ < y + δ by linarith),
        indicator_of_notMem (fun h => hy (hB0 h))]
  have hm2 : Measurable fun y => B.indicator (fun y => Γ {w | y ≤ w ∧ w < y + δ}) y :=
    (Measurable.indicator (measurable_measure_prodMk_left
      (s := {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 < p.1 + δ})
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_fst.add measurable_const))))) hB
  rw [e3, ← lintegral_add_left hm2]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy,
      ← measure_union (Set.disjoint_left.2 fun w (hw : w ∈ {w : ℝ | y ≤ w ∧ w < y + δ})
        (hw' : w ∈ Ici (y + δ)) => by
          simp only [mem_Ici] at hw'; linarith [hw.2]) measurableSet_Ici]
    congr 1
    ext w
    simp only [mem_union, mem_ofPred_eq, mem_Ici]
    constructor
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · linarith
    · intro hw
      by_cases hw' : w < y + δ
      · exact Or.inl ⟨hw, hw'⟩
      · exact Or.inr (by linarith)
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy, add_zero]

/-- (10.36): the total mass of `F[y, ∞) dy` is the mean `m = ∫ t F(dt)`. -/
theorem fwdSkelInv_univ (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hΓ0 : Γ (Iio 0) = 0) :
    fwdSkelInv Γ univ = ∫⁻ w, ENNReal.ofReal w ∂Γ := by
  have hnn : 0 ≤ᵐ[Γ] fun w : ℝ => w := by
    rw [Filter.EventuallyLE, ae_iff]
    have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Iio 0 := by ext a; simp
    rw [this]; exact hΓ0
  rw [fwdSkelInv, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_eq_lintegral_meas_le Γ hnn aemeasurable_id]
  rfl

/-- (10.36): when the mean `m` is finite, `m⁻¹ F[y, ∞) dy` is an invariant probability for every
`V⁺_δ`, `δ ≥ 0`. -/
theorem isProbabilityMeasure_fwdSkelInv_normalised (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hm : ∫⁻ w, ENNReal.ofReal w ∂Γ ≠ ∞) :
    IsProbabilityMeasure ((∫⁻ w, ENNReal.ofReal w ∂Γ)⁻¹ • fwdSkelInv Γ) ∧
      ∀ δ, 0 ≤ δ →
        IsInvariant (fwdSkelKernel Γ δ) ((∫⁻ w, ENNReal.ofReal w ∂Γ)⁻¹ • fwdSkelInv Γ) := by
  have hm0 : ∫⁻ w, ENNReal.ofReal w ∂Γ ≠ 0 := by
    refine (lt_of_lt_of_le (?_ : (0 : ℝ≥0∞) < ∫⁻ w in Ioi 0, ENNReal.ofReal w ∂Γ)
      (setLIntegral_le_lintegral _ _)).ne'
    rw [setLIntegral_pos_iff (f := fun w : ℝ => ENNReal.ofReal w) ENNReal.measurable_ofReal]
    have : Function.support (fun w : ℝ => ENNReal.ofReal w) ∩ Ioi 0 = Ioi 0 := by
      ext w; simp [Function.mem_support]
    rw [this]; exact hΓpos
  refine ⟨⟨?_⟩, fun δ hδ => (isInvariant_fwdSkelInv Γ hΓ0 hΓpos hδ).smul _⟩
  rw [Measure.smul_apply, smul_eq_mul, fwdSkelInv_univ Γ hΓ0, ENNReal.inv_mul_cancel hm0 hm]

end MeynTweedie.Ergodicity
