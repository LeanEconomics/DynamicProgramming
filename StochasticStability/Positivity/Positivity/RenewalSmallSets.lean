/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.RenewalSkeletons
import Positivity.SpreadOut
import Positivity.Cycles

/-!
# Small sets and aperiodicity of the forward recurrence time `δ`-skeleton (MT §§5.3.4, 5.4.4)

Meyn and Tweedie, Proposition 5.3.3 (p. 109) and Proposition 5.4.7 (p. 115), for the forward
recurrence time `δ`-skeleton `V⁺_δ` with kernel `fwdSkelKernel Γ δ` (copied from the
`TransitionProbabilities` project, `RenewalSkeletons`). The increment law `Γ` lives on `[0, ∞)`
and is not concentrated at `0`, so that `V⁺_δ` is a Markov chain (`fwdSkeleton_isMarkovChain`).

* `fwdSkelKernel_pow_apply`: `Pᴹ(x, B) = Γ^{⊗ℕ}{V⁺(Mδ) ∈ B}` for the renewal process with
  first epoch `x > 0`.
* `fwdTimeCts_eq_of_window`: if the epoch `Z_{n+1} = x + S_n + y` lies in `(t, t + δ)` and
  `y ≥ δ`, then `V⁺(t) = Z_{n+1} − t` (the argument of (5.33)).
* `exists_convPow_minorant`: a spread-out `Γ` has `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}` with `0 ≤ a < b`
  (from Proposition 5.3.1, as in (5.28)).
* `fwdSkel_pow_ge`: the bound (5.35), `Pᴹ(x, B) ≥ β γ μ_Leb(B)` for `x, B ⊆ (0, δ)` and
  `M ∈ {k + m + 2, k + m + 3}`.
* **Proposition 5.3.3** (`proposition_5_3_3`, p. 109): if `Γ` is spread out, then for every small
  enough `δ > 0` the set `(0, δ)` is small for `V⁺_δ`, with a multiple of Lebesgue measure on
  `(0, δ)` as minorizing measure, at the two consecutive times `M` and `M + 1`.
* **Proposition 5.4.7** (`proposition_5_4_7`, p. 115): for such `δ`, `g.c.d. E_C = 1` for
  `C = (0, δ)`, so `V⁺_δ` is aperiodic for every maximal irreducibility measure `ψ` with
  `ψ(C) > 0`.

**Corrections and hypotheses.** The book uses the set `[0, δ)`. In this construction
`V⁺(t) > 0` always (the first epoch strictly after `t`), so the small set is `(0, δ)`. The book
leaves the irreducibility of `V⁺_δ` implicit in "aperiodic". Here the conclusion is the g.c.d.
statement (5.40), which is how the book proves it, and aperiodicity for every maximal
irreducibility measure that charges `(0, δ)`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable (Γ : Measure ℝ) [IsProbabilityMeasure Γ]

/-- The forward skeleton kernel is a transition kernel. -/
theorem isMarkovKernel_fwdSkelKernel (δ : ℝ) : IsMarkovKernel (fwdSkelKernel Γ δ) :=
  isMarkovKernel_recursionKernel _ (measurable_fwdSkelStep δ)

/-- `Pᴹ(x, B) = Γ^{⊗ℕ}{w : V⁺(Mδ) ∈ B}` for the renewal process with first epoch `x > 0` and
increments `w`. -/
theorem fwdSkelKernel_pow_apply (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {δ : ℝ}
    (hδ : 0 ≤ δ) {x : ℝ} (hx : 0 < x) (M : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    (fwdSkelKernel Γ δ ^ M) x B =
      (Measure.infinitePi fun _ : ℕ => Γ) {w | fwdTimeCts (resEpoch x w) (M * δ) ∈ B} := by
  have := isMarkovKernel_fwdSkelKernel Γ δ
  have h := fwdSkeleton_isMarkovChain_delayed Γ hΓ0 hΓpos (Measure.dirac x)
    (by simp [hx.not_ge]) hδ
  have hmap := congrArg (fun μ : Measure ℝ => μ B) (h.map_eq M)
  rw [Measure.map_apply (measurable_fwdSkel δ M) hB, Measure.dirac_bind (Kernel.measurable _),
    Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
      ((measurable_fwdSkel δ M) hB)] at hmap
  rw [← hmap]
  rfl

/-- **The window argument of (5.33).** With nonnegative increments, if `y = wₙ ≥ δ` and the epoch
`Z_{n+2} = x + w₀ + ⋯ + wₙ` lies in `(t, t + δ)`, then `V⁺(t) = Z_{n+2} − t`. -/
theorem fwdTimeCts_eq_of_window {x t δ : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (n : ℕ)
    (hy : δ ≤ w n) (h1 : t < resEpoch x w (n + 2)) (h2 : resEpoch x w (n + 2) < t + δ) :
    fwdTimeCts (resEpoch x w) t = resEpoch x w (n + 2) - t := by
  have hprev : resEpoch x w (n + 1) ≤ t := by
    have : resEpoch x w (n + 2) = resEpoch x w (n + 1) + w n := by
      simp only [resEpoch_succ_eq, Finset.sum_range_succ]
      ring
    linarith
  refine IsLeast.csInf_eq ⟨⟨n + 2, by omega, h1, rfl⟩, ?_⟩
  rintro d ⟨j, hj, htj, rfl⟩
  have hj2 : n + 2 ≤ j := by
    by_contra hlt
    have := resEpoch_mono (x := x) hw hj (show j ≤ n + 1 by omega)
    linarith
  have := resEpoch_mono (x := x) hw (show 1 ≤ n + 2 by omega) hj2
  linarith

/-- A spread-out increment law on `[0, ∞)` has `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}` for some `N`,
`0 ≤ a < b` and `β > 0` (from Proposition 5.3.1, as in (5.28)). -/
theorem exists_convPow_minorant (hΓ0 : Γ (Iio 0) = 0) (h : IsSpreadOut Γ) :
    ∃ N : ℕ, ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ ∃ β : ℝ≥0∞, 0 < β ∧
      ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B := by
  obtain ⟨n, -, r, hr, s, t, hst, ε, hε, hsmall⟩ := proposition_5_3_1 Γ h
  have hle : ∀ B, MeasurableSet B → ε * volume (B ∩ Icc s t) ≤ convPow Γ (2 * n) B :=
    fun B hB => by
      have := hsmall.le_apply (x := 0) ⟨by linarith, by linarith⟩ B
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
        randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add 0) hB] at this
      have hpre : (fun w : ℝ => 0 + w) ⁻¹' B = B := by ext w; simp
      rwa [hpre] at this
  have ht : 0 < t := by
    by_contra hneg
    push Not at hneg
    have h1 := hle (Iio 0) measurableSet_Iio
    rw [convPow_Iio_zero Γ hΓ0] at h1
    have h2 : volume (Ico s t) ≤ volume (Iio (0 : ℝ) ∩ Icc s t) :=
      measure_mono fun u hu => ⟨lt_of_lt_of_le hu.2 hneg, hu.1, hu.2.le⟩
    rw [Real.volume_Ico] at h2
    have h3 : 0 < ENNReal.ofReal (t - s) := ENNReal.ofReal_pos.2 (by linarith)
    exact absurd (nonpos_iff_eq_zero.1 h1) (mul_ne_zero hε.ne' (h3.trans_le h2).ne')
  refine ⟨2 * n, max s 0, t, le_max_right _ _, max_lt hst ht, ε, hε, fun B hB => ?_⟩
  refine le_trans ?_ (hle B hB)
  gcongr
  exact le_max_left s 0

/-- **The bound (5.35)** (MT p. 109). Suppose `Γ^{N∗} ≥ β μ_Leb|_{[a, b]}`,
`[kδ, (k + 4)δ] ⊆ [a, b]`, `m ≥ 1` and `k + m + 2 ≤ M ≤ k + m + 3`. Then
`Pᴹ(x, B) ≥ β Γ[mδ, (m + 1)δ) μ_Leb(B)` for `x ∈ (0, δ)` and `B ⊆ (0, δ)`. -/
theorem fwdSkel_pow_ge (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) {N : ℕ} {a b : ℝ}
    {β : ℝ≥0∞} (hmin : ∀ B, MeasurableSet B → β * volume (B ∩ Icc a b) ≤ convPow Γ N B)
    {δ : ℝ} (hδ : 0 < δ) {k m : ℕ} (hm : 1 ≤ m) (hka : a ≤ k * δ) (hkb : (k + 4) * δ ≤ b)
    {M : ℕ} (hM1 : k + m + 2 ≤ M) (hM2 : M ≤ k + m + 3) {x : ℝ} (hx : x ∈ Ioo 0 δ)
    {B : Set ℝ} (hB : MeasurableSet B) (hBδ : B ⊆ Ioo 0 δ) :
    β * Γ (Ico (m * δ) ((m + 1) * δ)) * volume B ≤ (fwdSkelKernel Γ δ ^ M) x B := by
  rw [fwdSkelKernel_pow_apply Γ hΓ0 hΓpos hδ.le hx.1 M hB]
  have : IsFiniteMeasure (convPow Γ N) := by unfold convPow; infer_instance
  set ν := Measure.infinitePi fun _ : ℕ => Γ
  set R : Set (ℝ × ℝ) := {q | δ ≤ q.2 ∧ x + q.1 + q.2 - M * δ ∈ B} with hRdef
  have hRm : MeasurableSet R :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((((measurable_const.add measurable_fst).add measurable_snd).sub measurable_const) hB)
  have hpair : Measurable fun w : ℕ → ℝ => (∑ i ∈ Finset.range N, w i, w N) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).prodMk (measurable_pi_apply N)
  have hMr1 : ((k : ℝ) + m + 2) ≤ M := by exact_mod_cast hM1
  have hMr2 : (M : ℝ) ≤ (k : ℝ) + m + 3 := by exact_mod_cast hM2
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- (5.33): the event `{(S_N, w_N) ∈ R}` forces `V⁺(Mδ) ∈ B`
  have hsub : ν ((fun w : ℕ → ℝ => (∑ i ∈ Finset.range N, w i, w N)) ⁻¹' R) ≤
      ν {w | fwdTimeCts (resEpoch x w) (M * δ) ∈ B} := by
    refine measure_mono_ae ?_
    filter_upwards [tendsto_partialSum_atTop_ae Γ hΓ0 hΓpos] with w ⟨_, hw⟩ hwR
    obtain ⟨hy, hb⟩ := hwR
    have hZ : resEpoch x w (N + 2) = x + ∑ i ∈ Finset.range N, w i + w N := by
      rw [resEpoch_succ_eq, Finset.sum_range_succ, add_assoc]
    have hb' := hBδ hb
    have h1 : (M : ℝ) * δ < resEpoch x w (N + 2) := by rw [hZ]; linarith [hb'.1]
    have h2 : resEpoch x w (N + 2) < M * δ + δ := by rw [hZ]; linarith [hb'.2]
    change fwdTimeCts (resEpoch x w) (M * δ) ∈ B
    rw [fwdTimeCts_eq_of_window hw N hy h1 h2, hZ]
    exact hb
  refine le_trans ?_ hsub
  rw [← Measure.map_apply hpair hRm, infinitePi_map_partialSum_next Γ N,
    Measure.prod_apply_symm hRm]
  calc β * Γ (Ico (m * δ) ((m + 1) * δ)) * volume B
      = ∫⁻ _ in Ico (m * δ) ((m + 1) * δ), β * volume B ∂Γ := by
        rw [setLIntegral_const]; ring
    _ ≤ ∫⁻ y in Ico (m * δ) ((m + 1) * δ), convPow Γ N ((fun s => (s, y)) ⁻¹' R) ∂Γ := by
        refine setLIntegral_mono' measurableSet_Ico fun y hy => ?_
        have hsec : (fun s => (s, y)) ⁻¹' R = (· + (x + y - M * δ)) ⁻¹' B := by
          ext s
          simp only [hRdef, mem_preimage, mem_ofPred_eq]
          constructor
          · rintro ⟨-, h⟩; convert h using 1; ring
          · intro h
            refine ⟨?_, by convert h using 1; ring⟩
            nlinarith [hy.1]
        have hwin : (· + (x + y - M * δ)) ⁻¹' B ⊆ Icc a b := fun s hs => by
          have := hBδ hs
          simp only [mem_Ioo] at this
          constructor
          · nlinarith [hx.2, hy.2]
          · nlinarith [hx.1, hy.1]
        have hpre : MeasurableSet ((· + (x + y - M * δ)) ⁻¹' B) :=
          (measurable_add_const _) hB
        rw [hsec]
        calc β * volume B = β * volume ((· + (x + y - M * δ)) ⁻¹' B ∩ Icc a b) := by
              rw [inter_eq_left.2 hwin, measure_preimage_add_right]
          _ ≤ _ := hmin _ hpre
    _ ≤ ∫⁻ y, convPow Γ N ((fun s => (s, y)) ⁻¹' R) ∂Γ := setLIntegral_le_lintegral _ _

/-- **Proposition 5.3.3** (MT p. 109). If `Γ` is spread out, then for every small enough
`δ > 0` the set `C = (0, δ)` is small for the forward recurrence time `δ`-skeleton, with
minorizing measure `c μ_Leb|_C`, at two consecutive times `M` and `M + 1`. -/
theorem proposition_5_3_3 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (h : IsSpreadOut Γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ M : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧
      IsSmallSet (fwdSkelKernel Γ δ) M (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) ∧
      IsSmallSet (fwdSkelKernel Γ δ) (M + 1) (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) := by
  obtain ⟨N, a, b, ha0, hab, β, hβ, hmin⟩ := exists_convPow_minorant Γ hΓ0 h
  -- a level `δ₁ > 0` with `Γ[δ₁, ∞) > 0`
  obtain ⟨j₁, hj₁⟩ : ∃ j : ℕ, 0 < Γ (Ici ((j : ℝ) + 1)⁻¹) := by
    refine exists_measure_pos_of_iUnion (hΓpos.trans_le (measure_mono fun y hy => ?_))
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (mem_Ioi.1 hy)
    exact mem_iUnion.2 ⟨j, mem_Ici.2 (by rw [← one_div]; exact hj.le)⟩
  set δ₁ : ℝ := ((j₁ : ℝ) + 1)⁻¹
  have hδ₁ : 0 < δ₁ := by positivity
  refine ⟨min ((b - a) / 5) δ₁, lt_min (by linarith) hδ₁, fun δ hδ hδ₀ => ?_⟩
  have hδa : δ ≤ (b - a) / 5 := hδ₀.trans (min_le_left _ _)
  have hδb : δ ≤ δ₁ := hδ₀.trans (min_le_right _ _)
  -- the window `[kδ, (k + 4)δ] ⊆ [a, b]`
  set k := ⌈a / δ⌉₊
  have hka : a ≤ k * δ := (div_le_iff₀ hδ).1 (Nat.le_ceil _)
  have hkb : (k + 4) * δ ≤ b := by
    have := Nat.ceil_lt_add_one (div_nonneg ha0 hδ.le)
    have h2 : (k : ℝ) * δ < a + δ := by
      have := (lt_div_iff₀ hδ).1 (show (k : ℝ) - 1 < a / δ by linarith)
      linarith
    linarith
  -- a cell `[mδ, (m + 1)δ)`, `m ≥ 1`, charged by `Γ`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 0 < Γ (Ico (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ)) := by
    refine exists_measure_pos_of_iUnion (hj₁.trans_le (measure_mono fun y hy => ?_))
    have hy' : δ ≤ y := hδb.trans (mem_Ici.1 hy)
    set f := ⌊y / δ⌋₊
    have hf1 : 1 ≤ f := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ]; linarith)
    have hf2 : (f : ℝ) * δ ≤ y :=
      (le_div_iff₀ hδ).1 (Nat.floor_le (div_nonneg (hδ.le.trans hy') hδ.le))
    have hf3 : y < ((f : ℝ) + 1) * δ := (div_lt_iff₀ hδ).1 (Nat.lt_floor_add_one _)
    refine mem_iUnion.2 ⟨f - 1, ?_, ?_⟩
    · rw [Nat.cast_sub hf1, Nat.cast_one]; linarith
    · rw [Nat.cast_sub hf1, Nat.cast_one]; linarith
  set m := j + 1
  have hm : 1 ≤ m := by omega
  have hγ : Γ (Ico (m * δ) ((m + 1) * δ)) = Γ (Ico (((j : ℝ) + 1) * δ) (((j : ℝ) + 2) * δ)) := by
    congr 2 <;> push_cast [m] <;> ring
  have hc : 0 < β * Γ (Ico (m * δ) ((m + 1) * δ)) :=
    ENNReal.mul_pos hβ.ne' (by rw [hγ]; exact hj.ne')
  have hsmall : ∀ M, k + m + 2 ≤ M → M ≤ k + m + 3 →
      IsSmallSet (fwdSkelKernel Γ δ) M
        ((β * Γ (Ico (m * δ) ((m + 1) * δ))) • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) :=
    fun M hM1 hM2 => by
      refine ⟨measurableSet_Ioo, by omega, smul_measure_ne_zero ?_ hc.ne', fun x hx => ?_⟩
      · rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
        linarith
      refine Measure.le_intro fun B hB _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
      exact (fwdSkel_pow_ge Γ hΓ0 hΓpos hmin hδ hm hka hkb hM1 hM2 hx
        (hB.inter measurableSet_Ioo) inter_subset_right).trans (measure_mono inter_subset_left)
  exact ⟨k + m + 2, _, hc, hsmall _ le_rfl (by omega), hsmall _ (by omega) le_rfl⟩

/-- **Proposition 5.4.7** (MT p. 115). If `Γ` is spread out, then for every small enough `δ > 0`
the forward recurrence time `δ`-skeleton has a small set `C = (0, δ)` with `ν(C) > 0` and
`g.c.d. E_C = 1`. Hence it is aperiodic for every maximal irreducibility measure `ψ` with
`ψ(C) > 0`. -/
theorem proposition_5_4_7 (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (h : IsSpreadOut Γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → ∃ M : ℕ, ∃ ν : Measure ℝ,
      IsSmallSet (fwdSkelKernel Γ δ) M ν (Ioo 0 δ) ∧ 0 < ν (Ioo 0 δ) ∧
      setGcd (smallTimes (fwdSkelKernel Γ δ) (Ioo 0 δ) ν) = 1 ∧
      ∀ ψ : Measure ℝ, (haveI := isMarkovKernel_fwdSkelKernel Γ δ
        IsMaximalIrreducibility (fwdSkelKernel Γ δ) ψ) → 0 < ψ (Ioo 0 δ) →
        IsAperiodic (fwdSkelKernel Γ δ) ψ := by
  obtain ⟨δ₀, hδ₀, hall⟩ := proposition_5_3_3 Γ hΓ0 hΓpos h
  refine ⟨δ₀, hδ₀, fun δ hδ hle => ?_⟩
  have := isMarkovKernel_fwdSkelKernel Γ δ
  obtain ⟨M, c, hc, h1, h2⟩ := hall δ hδ hle
  have hνC : 0 < (c • volume.restrict (Ioo 0 δ)) (Ioo 0 δ) := by
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioo, inter_self,
      Real.volume_Ioo, smul_eq_mul]
    exact ENNReal.mul_pos hc.ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hS := smallTimes_isAddClosed (fwdSkelKernel Γ δ) hνC
  have hM := mem_smallTimes_of_isSmallSet h1
  have hM1 := mem_smallTimes_of_isSmallSet h2
  have hg : setGcd (smallTimes (fwdSkelKernel Γ δ) (Ioo 0 δ) (c • volume.restrict (Ioo 0 δ))) =
      1 := Nat.dvd_one.1 ((Nat.dvd_add_right (setGcd_dvd hS hM h1.2.1 hM)).1
        (setGcd_dvd hS hM h1.2.1 hM1))
  refine ⟨M, _, h1, hνC, hg, fun ψ hψ hψC => ?_⟩
  have := isPeriod_gcd (fwdSkelKernel Γ δ) hψ h1 hψC hνC
  rwa [hg] at this

end MeynTweedie.Positivity
