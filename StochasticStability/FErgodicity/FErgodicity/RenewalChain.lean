/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalRegeneration
import FErgodicity.RenewalInvariant
import FErgodicity.FNormErgodicTheorem

/-!
# The forward recurrence time `δ`-skeleton is positive and aperiodic (MT §14.5)

Meyn and Tweedie, p. 356: for a spread-out increment law `Γ` with finite mean and `δ` small, the
forward recurrence time `δ`-skeleton `V⁺_δ` (kernel `P = fwdSkelKernel Γ δ`) is aperiodic
(Propositions 5.3.3, 5.4.7), satisfies (V2) with `V(x) = x`, and initial laws with finite mean
are regular (Theorem 11.3.12); Theorem 13.4.4 then gives (14.41). The book leaves the
`ψ`-irreducibility implicit.

`V⁺_δ` lives on `(0, ∞)`. To work with a chain that is irreducible on all of `ℝ`, `fwdChain Γ δ`
moves by `P` on `(0, ∞)` and restarts uniformly on `(0, δ)` (`unifδ δ`) from `(−∞, 0]`; it agrees
with `P` from every positive state (`fwdChain_pow_of_pos`).

* `exists_pow_Ioo_pos`: from every `x > 0`, `V⁺_δ` enters `(0, δ)` (an epoch of
  `x + Y₀ + ⋯ + Y_{N−1}` falls in a window `(Mδ, (M + 1)δ)`, by the spread-out minorant of
  `Γ^{N∗}`).
* `isPhiIrreducible_fwdChain`: the chain is irreducible for Lebesgue measure on `(0, δ)`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The uniform law on `(0, δ)`. -/
noncomputable def unifδ (δ : ℝ) : Measure ℝ := (ENNReal.ofReal δ)⁻¹ • volume.restrict (Ioo 0 δ)

/-- `unifδ δ` is a probability measure for `δ > 0`. -/
theorem isProbabilityMeasure_unifδ {δ : ℝ} (hδ : 0 < δ) : IsProbabilityMeasure (unifδ δ) := by
  refine ⟨?_⟩
  rw [unifδ, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    smul_eq_mul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top]

/-- The chain that moves by the forward `δ`-skeleton kernel on `(0, ∞)` and restarts uniformly on
`(0, δ)` from `(−∞, 0]`. -/
noncomputable def fwdChain (Γ : Measure ℝ) (δ : ℝ) : Kernel ℝ ℝ :=
  absorbKernel (fwdSkelKernel Γ δ) (measurableSet_Ioi (a := (0 : ℝ))) (unifδ δ)

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- The restarted chain is a transition kernel. -/
theorem isMarkovKernel_fwdChain {δ : ℝ} (hδ : 0 < δ) : IsMarkovKernel (fwdChain Γ δ) :=
  haveI := isProbabilityMeasure_unifδ hδ
  haveI := isMarkovKernel_fwdSkelKernel Γ δ
  isMarkovKernel_absorbKernel _ _ _

/-- `V⁺_δ` stays in `(0, ∞)`. -/
theorem fwdSkelKernel_compl_Ioi (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (δ : ℝ) :
    ∀ x ∈ Ioi (0 : ℝ), fwdSkelKernel Γ δ x (Ioi 0)ᶜ = 0 := fun x _ => by
  rw [compl_Ioi]
  exact fwdSkelKernel_Iic_zero Γ hΓ0 hΓpos δ x

/-- From a positive state the restarted chain is `V⁺_δ`. -/
theorem fwdChain_pow_of_pos (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (δ : ℝ) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (fwdChain Γ δ ^ n : Kernel ℝ ℝ) x = (fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) x :=
  absorbKernel_pow_of_mem _ (fwdSkelKernel_compl_Ioi Γ hΓ0 hΓpos δ) n x hx

/-- **Entering `(0, δ)`**: if `Γ^{N∗} ≥ β μ_Leb` on `[a, b]` with `0 ≤ a`, `β > 0` and
`2δ ≤ b − a`, then from every `x > 0` the skeleton charges `(0, δ)` at some time. -/
theorem exists_pow_Ioo_pos (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {N : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) {β : ℝ≥0∞} (hβ : 0 < β)
    (hmin : ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B) {δ : ℝ}
    (hδ : 0 < δ) (hδab : 2 * δ ≤ b - a) {x : ℝ} (hx : 0 < x) :
    ∃ M : ℕ, 0 < (fwdSkelKernel Γ δ ^ M : Kernel ℝ ℝ) x (Ioo 0 δ) := by
  set M := ⌈(x + a) / δ⌉₊ with hMdef
  have hxa : 0 ≤ (x + a) / δ := div_nonneg (by linarith) hδ.le
  have hM1 : x + a ≤ M * δ := (div_le_iff₀ hδ).1 (Nat.le_ceil _)
  have hM2 : (M : ℝ) * δ < x + a + δ := by
    have h := Nat.ceil_lt_add_one hxa
    have h2 := (mul_lt_mul_of_pos_right h hδ)
    rw [add_mul, one_mul, div_mul_cancel₀ _ hδ.ne'] at h2
    exact h2
  refine ⟨M, ?_⟩
  rw [fwdSkelKernel_pow_apply Γ hΓ0 hΓpos hδ.le hx M measurableSet_Ioo]
  set ν := incr Γ with hν
  have hsm : Measurable fun w : ℕ → ℝ => ∑ i ∈ Finset.range N, w i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  set I := Ioo ((M : ℝ) * δ - x) ((M : ℝ) * δ - x + δ) with hI
  -- the epoch `x + Y₀ + ⋯ + Y_{N−1}` falls in `(Mδ, (M + 1)δ)` with positive probability
  have hE : 0 < ν {w | (∑ i ∈ Finset.range N, w i) ∈ I} := by
    have h1 : ν {w | (∑ i ∈ Finset.range N, w i) ∈ I} = convPow Γ N I := by
      rw [← incr_map_partialSum Γ N, Measure.map_apply hsm measurableSet_Ioo]
      rfl
    rw [h1]
    refine lt_of_lt_of_le ?_ (hmin I measurableSet_Ioo)
    have hsub : I ⊆ Icc a b := fun s hs => ⟨by rw [hI] at hs; linarith [hs.1],
      by rw [hI] at hs; linarith [hs.2]⟩
    rw [inter_eq_left.2 hsub, hI, Real.volume_Ioo]
    exact ENNReal.mul_pos hβ.ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
  refine lt_of_lt_of_le hE (measure_mono_ae ?_)
  filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩ hwE
  change fwdTimeCts (resEpoch x w) (M * δ) ∈ Ioo 0 δ
  rw [fwdTimeCts_eq_resEpoch hw hdiv]
  set t := (M : ℝ) * δ
  have hex : t < resEpoch x w (N + 1) := by
    rw [resEpoch_succ_eq]; linarith [hwE.1]
  have hτ : t < resEpoch x w (sInf {m | t < resEpoch x w (m + 1)} + 1) :=
    Nat.sInf_mem (s := {m | t < resEpoch x w (m + 1)}) ⟨N, hex⟩
  have hτN : sInf {m | t < resEpoch x w (m + 1)} ≤ N := Nat.sInf_le hex
  have hmono := resEpoch_mono (x := x) hw (show 1 ≤ sInf {m | t < resEpoch x w (m + 1)} + 1 by
    omega) (Nat.succ_le_succ hτN)
  have hN : resEpoch x w (N + 1) < t + δ := by
    rw [resEpoch_succ_eq]; linarith [hwE.2]
  exact ⟨by linarith, by linarith⟩

/-- `(Pᵐ⁺ⁿ)(x, A) = ∫ Pⁿ(x, dy) Pᵐ(y, A)`. -/
theorem pow_add_apply_eq_lintegral {X : Type*} [MeasurableSpace X] (K : Kernel X X) (m n : ℕ)
    (x : X) {A : Set X} (hA : MeasurableSet A) :
    (K ^ (m + n) : Kernel X X) x A = ∫⁻ y, (K ^ m : Kernel X X) y A ∂(K ^ n : Kernel X X) x := by
  rw [pow_add]
  exact Kernel.comp_apply' _ _ _ hA

/-- **`ψ`-irreducibility** of the restarted chain: with a spread-out minorant as in
`exists_pow_Ioo_pos` and a small set `(0, δ)` with Lebesgue minorization, the chain is
irreducible for Lebesgue measure on `(0, δ)`. -/
theorem isPhiIrreducible_fwdChain (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {N : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) {β : ℝ≥0∞} (hβ : 0 < β)
    (hmin : ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B) {δ : ℝ}
    (hδ : 0 < δ) (hδab : 2 * δ ≤ b - a) {M' : ℕ} {c : ℝ≥0∞} (hc : 0 < c)
    (hsmall : IsSmallSet (fwdSkelKernel Γ δ) M' (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ)) :
    haveI := isMarkovKernel_fwdChain Γ hδ
    IsPhiIrreducible (fwdChain Γ δ) (volume.restrict (Ioo 0 δ)) := by
  have := isMarkovKernel_fwdChain Γ hδ
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have := isProbabilityMeasure_unifδ hδ
  intro A hA hφA x
  rw [Measure.restrict_apply hA] at hφA
  set q := c * volume (A ∩ Ioo 0 δ) with hq
  have hq0 : 0 < q := ENNReal.mul_pos hc.ne' hφA.ne'
  have hM'1 : 1 ≤ M' := hsmall.2.1
  have hmeas : Measurable fun y => (fwdChain Γ δ ^ M' : Kernel ℝ ℝ) y A :=
    Kernel.measurable_coe _ hA
  -- the minorization on `(0, δ)`
  have hlow : ∀ y ∈ Ioo (0 : ℝ) δ, q ≤ (fwdChain Γ δ ^ M' : Kernel ℝ ℝ) y A := fun y hy => by
    rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M' hy.1]
    have h := hsmall.le_apply hy A
    rwa [Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul] at h
  have hint : ∀ ρ : Measure ℝ, q * ρ (Ioo 0 δ) ≤
      ∫⁻ y, (fwdChain Γ δ ^ M' : Kernel ℝ ℝ) y A ∂ρ := fun ρ => by
    rw [← setLIntegral_const]
    exact (setLIntegral_mono hmeas fun y hy => hlow y hy).trans (setLIntegral_le_lintegral _ _)
  by_cases hx : 0 < x
  · obtain ⟨M, hM⟩ := exists_pow_Ioo_pos Γ hΓ0 hΓpos ha hβ hmin hδ hδab hx
    have h1 : 0 < (fwdChain Γ δ ^ (M' + M) : Kernel ℝ ℝ) x A := by
      rw [pow_add_apply_eq_lintegral _ M' M x hA]
      refine lt_of_lt_of_le ?_ (hint _)
      rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M hx]
      exact ENNReal.mul_pos hq0.ne' hM.ne'
    have h2 := pow_le_hitProb (fwdChain Γ δ) hA (M' + M - 1) x
    rw [show M' + M - 1 + 1 = M' + M by omega] at h2
    exact lt_of_lt_of_le h1 h2
  · have h1 : 0 < (fwdChain Γ δ ^ (M' + 1) : Kernel ℝ ℝ) x A := by
      rw [pow_add_apply_eq_lintegral _ M' 1 x hA, pow_one, fwdChain,
        absorbKernel_of_notMem _ _ _ (show x ∉ Ioi (0 : ℝ) from hx)]
      refine lt_of_lt_of_le ?_ (hint _)
      rw [unifδ, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo, inter_self,
        Real.volume_Ioo, sub_zero, smul_eq_mul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hδ).ne'
        ENNReal.ofReal_ne_top, mul_one]
      exact hq0
    have h2 := pow_le_hitProb (fwdChain Γ δ) hA M' x
    exact lt_of_lt_of_le h1 h2

/-! ### The mean of `V⁺(δ)` -/

/-- **The overshoot is at most one increment**: if `0 < x ≤ δ`, the increments are nonnegative and
their partial sums diverge, then `V⁺(δ) ≤ Σⱼ Yⱼ 1{Z_{j+1} ≤ δ}`. -/
theorem ofReal_fwdTimeCts_le {x δ : ℝ} (hxδ : x ≤ δ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    ENNReal.ofReal (fwdTimeCts (resEpoch x w) δ) ≤
      ∑' j : ℕ, ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) := by
  rw [fwdTimeCts_eq_resEpoch hw hdiv]
  set τ := sInf {m | δ < resEpoch x w (m + 1)} with hτdef
  have hex := exists_resEpoch_gt (x := x) hdiv δ
  have hτ : δ < resEpoch x w (τ + 1) := Nat.sInf_mem (s := {m | δ < resEpoch x w (m + 1)}) hex
  have hτ1 : 1 ≤ τ := by
    by_contra h
    have h0 : τ = 0 := by omega
    rw [h0, zero_add, resEpoch_succ_eq, Finset.range_zero, Finset.sum_empty, add_zero] at hτ
    linarith
  obtain ⟨j, hj⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
  have hjle : resEpoch x w (j + 1) ≤ δ :=
    not_lt.1 (Nat.notMem_of_lt_sInf (s := {m | δ < resEpoch x w (m + 1)}) (by omega))
  have hstep : resEpoch x w (τ + 1) - δ ≤ w j := by
    rw [hj, resEpoch_succ_eq, Finset.sum_range_succ] at hτ ⊢
    rw [resEpoch_succ_eq] at hjle
    linarith
  calc ENNReal.ofReal (resEpoch x w (τ + 1) - δ) ≤ ENNReal.ofReal (w j) * 1 := by
        rw [mul_one]; exact ENNReal.ofReal_le_ofReal hstep
    _ = ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) := by
        rw [indicator_of_mem (show resEpoch x w (j + 1) ∈ Iic δ from hjle), Pi.one_apply]
    _ ≤ _ := ENNReal.le_tsum (f := fun j : ℕ =>
        ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1))) j

/-- **The mean forward recurrence time**: for `0 < x ≤ δ`,
`E_x[V⁺(δ)] ≤ m δ_x ∗ U(−∞, δ]`, where `m = ∫ y Γ(dy)` (each increment following an epoch in
`(0, δ]` is independent of that epoch). -/
theorem lintegral_fwdSkelKernel_le (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {x δ : ℝ}
    (hxδ : x ≤ δ) :
    ∫⁻ y, ENNReal.ofReal y ∂fwdSkelKernel Γ δ x ≤
      (∫⁻ y, ENNReal.ofReal y ∂Γ) * renMeas Γ (Measure.dirac x) (Iic δ) := by
  set ν := incr Γ with hν
  rw [fwdSkelKernel, recursionKernel_apply _ (measurable_fwdSkelStep δ) x,
    lintegral_map (f := fun y => ENNReal.ofReal y) (g := fun w => fwdSkelStep δ (x, w))
      ENNReal.measurable_ofReal ((measurable_fwdSkelStep δ).comp measurable_prodMk_left)]
  have hpair : ∀ j : ℕ, Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range j, w i, w j) := fun j =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hF : ∀ j : ℕ, Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal q.2 * (Iic δ).indicator 1 (x + q.1) := fun j =>
    (ENNReal.measurable_ofReal.comp measurable_snd).mul
      ((measurable_one.indicator measurableSet_Iic).comp (measurable_const.add measurable_fst))
  calc ∫⁻ w, ENNReal.ofReal (fwdSkelStep δ (x, w)) ∂ν
      ≤ ∫⁻ w, ∑' j : ℕ, ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨hdiv, hw⟩
        exact ofReal_fwdTimeCts_le hxδ hw hdiv
    _ = ∑' j : ℕ, ∫⁻ w, ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν :=
        lintegral_tsum fun j => ((hF j).comp (hpair j)).aemeasurable
    _ = ∑' j : ℕ, (∫⁻ y, ENNReal.ofReal y ∂Γ) * ν {w | resEpoch x w (j + 1) ∈ Iic δ} := by
        refine tsum_congr fun j => ?_
        have e : ∫⁻ w, ENNReal.ofReal (w j) * (Iic δ).indicator 1 (resEpoch x w (j + 1)) ∂ν =
            ∫⁻ q, ENNReal.ofReal q.2 * (Iic δ).indicator 1 (x + q.1) ∂((convPow Γ j).prod Γ) := by
          rw [← infinitePi_map_partialSum_next Γ j, lintegral_map (hF j) (hpair j)]
          rfl
        have hsm : Measurable fun w : ℕ → ℝ => ∑ i ∈ Finset.range j, w i :=
          Finset.measurable_sum _ fun i _ => measurable_pi_apply i
        have hind : Measurable fun s : ℝ => (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s) :=
          (measurable_one.indicator measurableSet_Iic).comp (measurable_const.add measurable_id)
        have e2 : ∫⁻ q, ENNReal.ofReal q.2 * (Iic δ).indicator 1 (x + q.1)
            ∂((convPow Γ j).prod Γ) = (∫⁻ s, (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s)
              ∂convPow Γ j) * ∫⁻ y, ENNReal.ofReal y ∂Γ := by
          rw [← lintegral_prod_mul hind.aemeasurable ENNReal.measurable_ofReal.aemeasurable]
          exact lintegral_congr fun q => mul_comm _ _
        have e3 : ∫⁻ s, (Iic δ).indicator (1 : ℝ → ℝ≥0∞) (x + s) ∂convPow Γ j =
            ν {w | resEpoch x w (j + 1) ∈ Iic δ} := by
          rw [← incr_map_partialSum Γ j, lintegral_map hind hsm]
          exact (lintegral_indicator_const_comp (measurable_const.add hsm) measurableSet_Iic
            1).trans (one_mul _)
        rw [e, e2, e3, mul_comm]
    _ = (∫⁻ y, ENNReal.ofReal y ∂Γ) * renMeas Γ (Measure.dirac x) (Iic δ) := by
        rw [ENNReal.tsum_mul_left, renMeas_dirac_apply Γ x measurableSet_Iic]

/-! ### The drift (V2) with `V(x) = x/δ + 1` -/

/-- The test function `V(x) = x/δ + 1` on `(0, ∞)`, `V = 3` on `(−∞, 0]`. -/
noncomputable def fwdV (δ : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioi 0).piecewise (fun x => ENNReal.ofReal (x / δ) + 1) fun _ => 3

/-- `fwdV δ` is measurable. -/
theorem measurable_fwdV (δ : ℝ) : Measurable (fwdV δ) := by
  classical
  exact Measurable.piecewise measurableSet_Ioi
    ((ENNReal.measurable_ofReal.comp (measurable_id.div_const δ)).add measurable_const)
    measurable_const

/-- `fwdV δ ≤ x/δ + 3`. -/
theorem fwdV_le (δ x : ℝ) : fwdV δ x ≤ ENNReal.ofReal (x / δ) + 3 := by
  classical
  unfold fwdV
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    exact add_le_add le_rfl (by norm_num)
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
    exact le_add_self

/-- **(V2) for the restarted chain** (MT p. 356, `V(x) = x`): off `C = (0, δ]`,
`∫ V dK(x, ·) + 1 ≤ V(x)`, and on `C` the drift is bounded by `b = δ⁻¹ m U(δ) + 4`, where
`m = ∫ y Γ(dy)` and `U(δ) = e^δ (1 − φ)⁻¹` bounds `δ_x ∗ U(−∞, δ]`. -/
theorem driftV2_fwdChain (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) :
    DriftV2 (fwdChain Γ δ) (fwdV δ)
      ((ENNReal.ofReal δ)⁻¹ * ((∫⁻ y, ENNReal.ofReal y ∂Γ) * (ENNReal.ofReal (Real.exp δ) *
        (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹)) + 4) (Ioc 0 δ) := by
  classical
  have := isProbabilityMeasure_unifδ hδ
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have hδe : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have hdivR : ∀ y : ℝ, ENNReal.ofReal (y / δ) = (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal y :=
    fun y => by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.2 hδ.le), ENNReal.ofReal_inv_of_pos hδ,
        mul_comm]
  intro x
  by_cases hx0 : 0 < x
  · rw [fwdChain, absorbKernel_of_mem _ _ _ (show x ∈ Ioi (0 : ℝ) from hx0)]
    by_cases hxδ : x ≤ δ
    · -- inside `C`
      rw [indicator_of_mem (show x ∈ Ioc 0 δ from ⟨hx0, hxδ⟩)]
      have h1 : ∫⁻ y, fwdV δ y ∂fwdSkelKernel Γ δ x ≤
          (ENNReal.ofReal δ)⁻¹ * ∫⁻ y, ENNReal.ofReal y ∂fwdSkelKernel Γ δ x + 3 := by
        calc ∫⁻ y, fwdV δ y ∂fwdSkelKernel Γ δ x
            ≤ ∫⁻ y, ((ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal y + 3) ∂fwdSkelKernel Γ δ x := by
              refine lintegral_mono fun y => ?_
              rw [← hdivR]
              exact fwdV_le δ y
          _ = _ := by
              rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
                ENNReal.measurable_ofReal, lintegral_const, measure_univ, mul_one]
      have h2 := lintegral_fwdSkelKernel_le Γ hΓ0 hΓpos hxδ
      have h3 := renMeas_dirac_Iic_le Γ x δ
      have h4 : ENNReal.ofReal (Real.exp (δ - x)) ≤ ENNReal.ofReal (Real.exp δ) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
      calc ∫⁻ y, fwdV δ y ∂fwdSkelKernel Γ δ x + 1
          ≤ (ENNReal.ofReal δ)⁻¹ * ((∫⁻ y, ENNReal.ofReal y ∂Γ) *
              (ENNReal.ofReal (Real.exp δ) * (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹))
              + 3 + 1 := by
            refine add_le_add (h1.trans (add_le_add (mul_le_mul' le_rfl (h2.trans
              (mul_le_mul' le_rfl (h3.trans (mul_le_mul' h4 le_rfl))))) le_rfl)) le_rfl
        _ ≤ fwdV δ x + ((ENNReal.ofReal δ)⁻¹ * ((∫⁻ y, ENNReal.ofReal y ∂Γ) *
              (ENNReal.ofReal (Real.exp δ) * (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹))
              + 4) := by
            rw [add_assoc, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
            exact le_add_self
    · -- beyond `δ` the skeleton moves down by `δ`
      push Not at hxδ
      rw [indicator_of_notMem (show x ∉ Ioc 0 δ from fun h => absurd h.2 (not_le.2 hxδ)),
        add_zero, fwdSkelKernel_of_lt Γ hΓ0 hΓpos hδ.le hxδ, lintegral_dirac' _ (measurable_fwdV δ)]
      unfold fwdV
      rw [Set.piecewise_eq_of_mem _ _ _ (show x - δ ∈ Ioi (0 : ℝ) from sub_pos.2 hxδ),
        Set.piecewise_eq_of_mem _ _ _ (show x ∈ Ioi (0 : ℝ) from hx0)]
      have h1 : (x - δ) / δ = x / δ - 1 := by field_simp
      have h2 : 1 ≤ x / δ := (le_div_iff₀ hδ).2 (by linarith)
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (x / δ) := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h2
      rw [h1, add_assoc, ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one, ← add_assoc,
        tsub_add_cancel_of_le h3]
  · -- from `(−∞, 0]` the chain restarts uniformly on `(0, δ)`
    rw [fwdChain, absorbKernel_of_notMem _ _ _ (show x ∉ Ioi (0 : ℝ) from hx0),
      indicator_of_notMem (show x ∉ Ioc 0 δ from fun h => hx0 h.1), add_zero]
    unfold fwdV
    rw [Set.piecewise_eq_of_notMem _ _ _ (show x ∉ Ioi (0 : ℝ) from hx0)]
    have hle : ∀ᵐ y ∂unifδ δ, (Ioi 0).piecewise (fun x => ENNReal.ofReal (x / δ) + 1)
        (fun _ => (3 : ℝ≥0∞)) y ≤ 2 := by
      have hmem : ∀ᵐ y ∂unifδ δ, y ∈ Ioo 0 δ := by
        rw [unifδ]
        exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _
      filter_upwards [hmem] with y hy
      rw [Set.piecewise_eq_of_mem _ _ _ (show y ∈ Ioi (0 : ℝ) from hy.1)]
      have : ENNReal.ofReal (y / δ) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((div_le_one hδ).2 hy.2.le)
      calc ENNReal.ofReal (y / δ) + 1 ≤ 1 + 1 := add_le_add this le_rfl
        _ = 2 := by norm_num
    calc ∫⁻ y, (Ioi 0).piecewise (fun x => ENNReal.ofReal (x / δ) + 1) (fun _ => (3 : ℝ≥0∞)) y
          ∂unifδ δ + 1 ≤ ∫⁻ _, (2 : ℝ≥0∞) ∂unifδ δ + 1 := add_le_add (lintegral_mono_ae hle) le_rfl
      _ = 3 := by rw [lintegral_const, measure_univ, mul_one]; norm_num

/-! ### Positivity, aperiodicity and regularity -/

omit [IsProbabilityMeasure Γ] in
/-- `fwdSkelInv Γ` does not charge `(−∞, 0]`. -/
theorem fwdSkelInv_Iic_zero : fwdSkelInv Γ (Iic 0) = 0 := by
  rw [fwdSkelInv, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2; linarith
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

/-- **The forward recurrence time `δ`-skeleton is positive, aperiodic and has regular initial
laws** (MT p. 356): for a spread-out `Γ` on `[0, ∞)` with finite mean and every small enough
`δ > 0`, the restarted chain has a maximal irreducibility measure `ψ` for which it is positive and
aperiodic, and every probability on `(0, ∞)` with finite mean is regular. -/
theorem fwdChain_structure (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (hs : IsSpreadOut Γ)
    (hm : ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ (hδ : 0 < δ), δ ≤ δ₀ →
      haveI := isMarkovKernel_fwdChain Γ hδ
      ∃ ψ : Measure ℝ, IsPositive (fwdChain Γ δ) ψ ∧ IsAperiodic (fwdChain Γ δ) ψ ∧
        ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Iic 0) = 0 →
          ∫⁻ x, ENNReal.ofReal x ∂μ ≠ ∞ → IsRegularMeasure (fwdChain Γ δ) ψ μ := by
  obtain ⟨N, a, b, ha, hab, β, hβ, hmin⟩ := exists_convPow_minorant Γ hΓ0 hs
  obtain ⟨δ₁, hδ₁, hsmallAll⟩ := proposition_5_3_3 Γ hΓ0 hΓpos hs
  obtain ⟨δ₂, hδ₂, haperAll⟩ := proposition_5_4_7 Γ hΓ0 hΓpos hs
  refine ⟨min (min δ₁ δ₂) ((b - a) / 2), lt_min (lt_min hδ₁ hδ₂) (by linarith),
    fun δ hδ hδle => ?_⟩
  have hδ₁le : δ ≤ δ₁ := hδle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₂le : δ ≤ δ₂ := hδle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδab : 2 * δ ≤ b - a := by
    have := hδle.trans (min_le_right _ _); linarith
  have := isMarkovKernel_fwdChain Γ hδ
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have := isProbabilityMeasure_unifδ hδ
  set K := fwdChain Γ δ with hK
  obtain ⟨M', c, hc, hsm, -⟩ := hsmallAll δ hδ hδ₁le
  have hφ := isPhiIrreducible_fwdChain Γ hΓ0 hΓpos ha hβ hmin hδ hδab hc hsm
  have hvolC : volume (Ioo (0 : ℝ) δ) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]; exact (ENNReal.ofReal_pos.2 hδ).ne'
  have hφ0 : volume.restrict (Ioo (0 : ℝ) δ) ≠ 0 := fun h0 => by
    have := congrArg (fun ρ : Measure ℝ => ρ (Ioo 0 δ)) h0
    simp only [Measure.restrict_apply measurableSet_Ioo, inter_self, Measure.coe_zero,
      Pi.zero_apply] at this
    exact hvolC this
  obtain ⟨φ₀, -, -, -, hmax⟩ := proposition_4_2_2_maximal K hφ hφ0
  set ψ := maxIrrMeasure K φ₀ with hψ
  have hψC : 0 < ψ (Ioo 0 δ) := by
    have hac := (hmax.isPhiIrreducible_iff _).1 hφ
    refine pos_iff_ne_zero.2 fun h0 => hvolC ?_
    have := hac h0
    rwa [Measure.restrict_apply measurableSet_Ioo, inter_self] at this
  -- aperiodicity
  obtain ⟨M, ν, hsmP, hνC, hgcd, -⟩ := haperAll δ hδ hδ₂le
  have hsmK : IsSmallSet K M ν (Ioo 0 δ) := ⟨hsmP.1, hsmP.2.1, hsmP.2.2.1, fun x hx => by
    rw [hK, fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M hx.1]; exact hsmP.2.2.2 x hx⟩
  have htimes : smallTimes K (Ioo 0 δ) ν = smallTimes (fwdSkelKernel Γ δ) (Ioo 0 δ) ν := by
    ext n
    refine and_congr_right fun _ => exists_congr fun δ' => and_congr_right fun _ =>
      forall₂_congr fun x hx => ?_
    rw [hK, fwdChain_pow_of_pos Γ hΓ0 hΓpos δ n hx.1]
  have hap : IsAperiodic K ψ := by
    have h := isPeriod_gcd K hmax hsmK hψC hνC
    rwa [htimes, hgcd] at h
  -- positivity
  obtain ⟨hπp, hπinv⟩ := isProbabilityMeasure_fwdSkelInv_normalised Γ hΓ0 hΓpos hm
  set πe := (∫⁻ w, ENNReal.ofReal w ∂Γ)⁻¹ • fwdSkelInv Γ with hπe
  have hπc : πe (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi, hπe, Measure.smul_apply, fwdSkelInv_Iic_zero Γ, smul_zero]
  have hπK : IsInvariant K πe := by
    unfold IsInvariant
    rw [hK, fwdChain, comp_congr_of_compl_eq_zero hπc fun y hy => absorbKernel_of_mem _ _ _ hy]
    exact hπinv δ hδ.le
  have hpos : IsPositive K ψ := ⟨hmax, πe, hπp, hπK⟩
  refine ⟨ψ, hpos, hap, fun μ _ hμ0 hμm => ?_⟩
  -- the petite set `(0, δ]`
  have hpet1 : IsPetite K (Ioo 0 δ) := ⟨_, _, proposition_5_5_3 (⟨hsm.1, hsm.2.1, hsm.2.2.1,
    fun x hx => by rw [hK, fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M' hx.1]; exact hsm.2.2.2 x hx⟩ :
      IsSmallSet K M' (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ))⟩
  obtain ⟨M₀, hM₀⟩ := exists_pow_Ioo_pos Γ hΓ0 hΓpos ha hβ hmin hδ hδab hδ
  set p := (fwdSkelKernel Γ δ ^ M₀ : Kernel ℝ ℝ) δ (Ioo 0 δ) with hp
  have hpet2 : IsPetite K {δ} := by
    have hsm2 : IsSmallSet K (M' + M₀) (p • c • volume.restrict (Ioo 0 δ)) {δ} := by
      refine ⟨measurableSet_singleton δ, by have := hsm.2.1; omega,
        smul_measure_ne_zero (smul_measure_ne_zero hφ0 hc.ne') hM₀.ne',
        fun x hx => Measure.le_intro fun B hB _ => ?_⟩
      rw [mem_singleton_iff.1 hx, pow_add_apply_eq_lintegral _ M' M₀ δ hB,
        hK, fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M₀ hδ, Measure.smul_apply, Measure.smul_apply,
        smul_eq_mul, smul_eq_mul]
      have hmeas : Measurable fun y => (fwdChain Γ δ ^ M' : Kernel ℝ ℝ) y B :=
        Kernel.measurable_coe _ hB
      calc p * (c * volume.restrict (Ioo 0 δ) B)
          = ∫⁻ _ in Ioo 0 δ, c * volume.restrict (Ioo 0 δ) B
              ∂(fwdSkelKernel Γ δ ^ M₀ : Kernel ℝ ℝ) δ := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in Ioo 0 δ, (fwdChain Γ δ ^ M' : Kernel ℝ ℝ) y B
              ∂(fwdSkelKernel Γ δ ^ M₀ : Kernel ℝ ℝ) δ := by
            refine setLIntegral_mono hmeas fun y hy => ?_
            rw [fwdChain_pow_of_pos Γ hΓ0 hΓpos δ M' hy.1]
            have h := hsm.le_apply hy B
            rwa [Measure.smul_apply, smul_eq_mul] at h
        _ ≤ _ := setLIntegral_le_lintegral _ _
    exact ⟨_, _, proposition_5_5_3 hsm2⟩
  have hpet : IsPetite K (Ioc 0 δ) := by
    have h := proposition_5_5_5_ii K hmax hpet1 hpet2
    rwa [Ioo_union_right hδ] at h
  -- regularity from (V2)
  have hU : (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (tsub_pos_of_lt (exp_moment_lt_one Γ hΓ0 hΓpos)).ne'
  have hb : (ENNReal.ofReal δ)⁻¹ * ((∫⁻ y, ENNReal.ofReal y ∂Γ) * (ENNReal.ofReal (Real.exp δ) *
      (1 - ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂Γ)⁻¹)) + 4 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hδ).ne')
      (ENNReal.mul_ne_top hm (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU)), by norm_num⟩
  refine theorem_11_3_12_i hmax (measurable_fwdV δ) hb hpet (driftV2_fwdChain Γ hΓ0 hΓpos hδ) ?_
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => fwdV_le δ x)
  have hdivR : ∀ y : ℝ, ENNReal.ofReal (y / δ) = (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal y :=
    fun y => by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.2 hδ.le), ENNReal.ofReal_inv_of_pos hδ,
        mul_comm]
  simp_rw [hdivR]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ ENNReal.measurable_ofReal,
    lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hδ).ne') hμm, by norm_num⟩

/-- **(14.41)** (MT p. 356, from Theorem 13.4.4): for a spread-out `Γ` on `[0, ∞)` with finite mean
and every small enough `δ > 0`, any two first-epoch laws `μ₁, μ₂` on `(0, ∞)` with finite means
have `Σₙ ‖μ₁(P^δ)ⁿ − μ₂(P^δ)ⁿ‖ < ∞`. -/
theorem tsum_tvNorm_fwdSkel_ne_top (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0))
    (hs : IsSpreadOut Γ) (hm : ∫⁻ y, ENNReal.ofReal y ∂Γ ≠ ∞) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∀ (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂],
        μ₁ (Iic 0) = 0 → μ₂ (Iic 0) = 0 → ∫⁻ x, ENNReal.ofReal x ∂μ₁ ≠ ∞ →
          ∫⁻ x, ENNReal.ofReal x ∂μ₂ ≠ ∞ →
          ∑' n, ENNReal.ofReal (tvNorm ((fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ₁)
            ((fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ₂)) ≠ ∞ := by
  obtain ⟨δ₀, hδ₀, hall⟩ := fwdChain_structure Γ hΓ0 hΓpos hs hm
  refine ⟨δ₀, hδ₀, fun δ hδ hδle μ₁ μ₂ _ _ h₁ h₂ hm₁ hm₂ => ?_⟩
  have := isMarkovKernel_fwdChain Γ hδ
  have := isMarkovKernel_fwdSkelKernel Γ δ
  obtain ⟨ψ, hpos, hap, hreg⟩ := hall δ hδ hδle
  have hsum := theorem_13_4_4 hpos hap μ₁ μ₂ (hreg μ₁ inferInstance h₁ hm₁)
    (hreg μ₂ inferInstance h₂ hm₂)
  have hc₁ : μ₁ (Ioi 0)ᶜ = 0 := by rw [compl_Ioi]; exact h₁
  have hc₂ : μ₂ (Ioi 0)ᶜ = 0 := by rw [compl_Ioi]; exact h₂
  have hcomp : ∀ n (μ : Measure ℝ), μ (Ioi 0)ᶜ = 0 →
      (fwdChain Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ = (fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ :=
    fun n μ hμ => comp_absorbKernel_pow _ (fwdSkelKernel_compl_Ioi Γ hΓ0 hΓpos δ) n hμ
  -- each term by convexity
  have hterm : ∀ n, ENNReal.ofReal (tvNorm ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) ∘ₘ μ₁)
      ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) ∘ₘ μ₂)) ≤
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (tvNorm ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) x)
        ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) y)) ∂μ₂ ∂μ₁ := fun n => by
    have := isMarkovKernel_pow (fwdChain Γ δ) (n + 1)
    rw [← fNorm_one]
    refine (fNorm_comp_le_lintegral _ 1 μ₁ μ₂).trans (le_of_eq ?_)
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    rw [fNorm_one]
  have hshift : ∑' n, ENNReal.ofReal (tvNorm ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) ∘ₘ μ₁)
      ((fwdChain Γ δ ^ (n + 1) : Kernel ℝ ℝ) ∘ₘ μ₂)) ≠ ∞ := by
    refine ne_top_of_le_ne_top hsum ((ENNReal.tsum_le_tsum hterm).trans ?_)
    refine (tsum_lintegral_le_lintegral_tsum μ₁ _).trans (lintegral_mono fun x => ?_)
    exact tsum_lintegral_le_lintegral_tsum μ₂ _
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ?_⟩
  refine ne_top_of_le_ne_top hshift (le_of_eq (tsum_congr fun n => ?_))
  rw [hcomp (n + 1) μ₁ hc₁, hcomp (n + 1) μ₂ hc₂]

end MeynTweedie.FErgodicity
