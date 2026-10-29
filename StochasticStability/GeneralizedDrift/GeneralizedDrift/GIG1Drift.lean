/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.LadderDrift
import GeneralizedDrift.RenewalEquilibrium

/-!
# Stability of the GI/G/1 queue through the average drift (MT §19.3.3)

Meyn and Tweedie, §19.3.3, pp. 506–508: Theorem 19.3.5 for the GI/G/1 ladder chain
`gig1Ladder H G` ((3.40), (3.42)–(3.43), `LadderChains`), with service law `H` (mean `µ`) and
interarrival law `G` (mean `λ`); `Λ = gig1Lambda H G`, `β = ladderBeta Λ` (19.67).

**Pathwise renewal facts.** `resEpoch_mono'`; `tsum_mul_straddle`: the index `N(t)` of the
renewal interval straddling `t` equals the number of epochs `≤ t`; `tsum_straddle_mem`: the
straddle decomposition of `{V⁺(t) ∈ B}`; `tsum_mul_prod_apply` (Tonelli for the weighted sums).

**The proof of p. 507.**
* `ladderBeta_gig1`: `β(x) = ∫ G(dt) E[N(t) | R₀ = x]` with `E[N(t) | R₀ = x] = δₓ ∗ U(−∞, t]`
  (`renMeas`), for `x ≥ 0`.
* `isInvariant_eqLaw_gig1`: `Σₙ Λₙ(x, ·) = ∫ G(dt) Pᵗ(x, ·)` and the stationary forward
  recurrence law `ν = µ⁻¹ H[y, ∞) dy` (`eqLaw H`, (10.36)) is invariant for every `Pᵗ`, hence for
  `Λ`.
* `lintegral_ladderBeta_gig1` (the stationary renewal identity `∫ ν(dx) E[N(t) | R₀ = x] = t/µ`,
  from `Γₑ ∗ U = µ⁻¹ μ_Leb` (`renMeas_eqLaw`), and Fubini, (19.83)): `∫ ν β = λ/µ`.
* **Theorem 19.3.5**, first part (`theorem_19_3_5`, p. 506): `ν` is an invariant probability of
  `Φ_Λ`, `∫ ν β = λ/µ`, and (19.68) holds iff `λ > µ`.

**Hypotheses.** Service times are nonnegative and not a.s. zero with finite mean
(`H(−∞, 0) = 0 < H(0, ∞)`, `µ < ∞`), interarrival times are nonnegative; `λ = ∞` is allowed.

**Elsewhere.** The second part of Theorem 19.3.5 (the invariant measure (10.52) when `λ > µ`),
with a corrected proof and a counterexample to (19.84), is in `GIG1Stability`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The epochs `0, x, x + u₀, …` are nondecreasing for `x ≥ 0` and `u ≥ 0`. -/
theorem resEpoch_mono' {x : ℝ} (hx : 0 ≤ x) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) {a b : ℕ}
    (hab : a ≤ b) : resEpoch x u a ≤ resEpoch x u b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; exact le_rfl
    · calc resEpoch x u 0 = 0 := rfl
        _ ≤ x := hx
        _ = resEpoch x u 1 := by simp [resEpoch]
        _ ≤ resEpoch x u b := resEpoch_mono hu le_rfl hb
  · exact resEpoch_mono hu ha hab

/-- **The straddle count** (pathwise): for `x, t ≥ 0`, nonnegative increments with divergent
sums, the index `N(t)` of the renewal interval `[Zₙ, Zₙ₊₁)` containing `t` is the number of
epochs `Z_{m+1} ≤ t`: `Σₙ n 1{Zₙ ≤ t < Zₙ₊₁} = Σₘ 1{Zₘ₊₁ ≤ t}`. -/
theorem tsum_mul_straddle {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop) :
    ∑' n : ℕ, (n : ℝ≥0∞) * {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 n ≤ p.1 ∧
      p.1 < resEpoch x p.2 (n + 1)}.indicator 1 (t, u) =
      ∑' m, (Iic t).indicator (1 : ℝ → ℝ≥0∞) (resEpoch x u (m + 1)) := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x u (m + 1)} with hτdef
  have hτ : t < resEpoch x u (τ + 1) := Nat.sInf_mem hex
  have hle : ∀ m < τ, resEpoch x u (m + 1) ≤ t := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hZτ : resEpoch x u τ ≤ t := by
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · rw [h0]; exact ht
    · have := hle (τ - 1) (by omega)
      rwa [show τ - 1 + 1 = τ by omega] at this
  have hL : ∑' n : ℕ, (n : ℝ≥0∞) * {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 n ≤ p.1 ∧
      p.1 < resEpoch x p.2 (n + 1)}.indicator 1 (t, u) = τ := by
    rw [tsum_eq_single τ fun n hn => ?_]
    · rw [indicator_of_mem (show (t, u) ∈ {p : ℝ × (ℕ → ℝ) | resEpoch x p.2 τ ≤ p.1 ∧
        p.1 < resEpoch x p.2 (τ + 1)} from ⟨hZτ, hτ⟩), Pi.one_apply, mul_one]
    · rw [indicator_of_notMem, mul_zero]
      rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne hn with h | h
      · exact absurd (hle n h) (not_le.2 h2)
      · have := resEpoch_mono' hx hu (show τ + 1 ≤ n by omega)
        linarith
  have hR : ∑' m, (Iic t).indicator (1 : ℝ → ℝ≥0∞) (resEpoch x u (m + 1)) = τ := by
    rw [tsum_eq_sum (s := Finset.range τ) fun m hm => ?_]
    · rw [Finset.sum_congr rfl fun m hm => indicator_of_mem (mem_Iic.2
        (hle m (Finset.mem_range.1 hm))) _]
      simp
    · rw [indicator_of_notMem]
      have := resEpoch_mono' hx hu (show τ + 1 ≤ m + 1 by
        have := Finset.mem_range.not.1 hm; omega)
      simp only [mem_Iic, not_le]
      linarith
  rw [hL, hR]

/-- **The forward recurrence time as a straddle sum** (pathwise): for `x, t ≥ 0`,
`Σₙ 1{Zₙ ≤ t < Zₙ₊₁, Zₙ₊₁ − t ∈ B} = 1{V⁺(t) ∈ B}`. -/
theorem tsum_straddle_mem {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop atTop) (B : Set ℝ) :
    ∑' n, (gig1Set n B).indicator (1 : ℝ × (ℝ × (ℕ → ℝ)) → ℝ≥0∞) (x, (t, u)) =
      B.indicator 1 (fwdTimeCts (resEpoch x u) t) := by
  have hex := exists_resEpoch_gt (x := x) hdiv t
  set τ := sInf {m | t < resEpoch x u (m + 1)} with hτdef
  have hτ : t < resEpoch x u (τ + 1) := Nat.sInf_mem hex
  have hle : ∀ m < τ, resEpoch x u (m + 1) ≤ t := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hZτ : resEpoch x u τ ≤ t := by
    rcases Nat.eq_zero_or_pos τ with h0 | hpos
    · rw [h0]; exact ht
    · have := hle (τ - 1) (by omega)
      rwa [show τ - 1 + 1 = τ by omega] at this
  rw [fwdTimeCts_eq_resEpoch hu hdiv, ← hτdef, tsum_eq_single τ fun n hn => ?_]
  · by_cases hB : resEpoch x u (τ + 1) - t ∈ B
    · rw [indicator_of_mem (show (x, (t, u)) ∈ gig1Set τ B from ⟨hZτ, hτ, hB⟩),
        indicator_of_mem hB]
      rfl
    · rw [indicator_of_notMem (fun h => hB h.2.2), indicator_of_notMem hB]
  · rw [indicator_of_notMem]
    rintro ⟨h1, h2, -⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact absurd (hle n h) (not_le.2 h2)
    · have := resEpoch_mono' hx hu (show τ + 1 ≤ n by omega)
      simp only at h1
      linarith

/-- `Σₙ cₙ (G ⊗ I)(Sₙ) = ∫ G(dt) ∫ I(du) Σₙ cₙ 1_{Sₙ}(t, u)`. -/
theorem tsum_mul_prod_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (c : ℕ → ℝ≥0∞)
    {S : ℕ → Set (α × β)} (hS : ∀ n, MeasurableSet (S n)) :
    ∑' n, c n * (μ.prod ν) (S n) =
      ∫⁻ a, ∫⁻ b, ∑' n, c n * (S n).indicator 1 (a, b) ∂ν ∂μ := by
  have hm : ∀ n, Measurable fun p : α × β => c n * (S n).indicator 1 p := fun n =>
    (measurable_one.indicator (hS n)).const_mul _
  rw [← lintegral_prod _ (Measurable.tsum hm).aemeasurable,
    lintegral_tsum fun n => (hm n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (hS n)), lintegral_indicator_one (hS n)]

/-- `G`-almost every interarrival time is nonnegative. -/
theorem ae_nonneg_of_Iio {G : Measure ℝ} (hG0 : G (Iio 0) = 0) : ∀ᵐ t ∂G, 0 ≤ t := by
  rw [ae_iff]
  convert hG0 using 2
  ext t
  simp

/-- The mean of a law on `[0, ∞)` charging `(0, ∞)` is positive. -/
theorem renMean_ne_zero {H : Measure ℝ} (hHpos : 0 < H (Ioi 0)) : renMean H ≠ 0 := by
  intro h
  rw [renMean, lintegral_eq_zero_iff ENNReal.measurable_ofReal] at h
  have h' : H {w | ¬ ENNReal.ofReal w = 0} = 0 := ae_iff.1 h
  refine hHpos.ne' (measure_mono_null (fun w hw => ?_) h')
  simp only [mem_ofPred_eq, ENNReal.ofReal_eq_zero, not_le]
  exact hw

/-- **(3.42) summed with weights `n`** (MT p. 507): for `x ≥ 0`, the expected ladder height is the
expected number of service completions in an interarrival time,
`β(x) = ∫ G(dt) E[N(t) | R₀ = x]`, with `E[N(t) | R₀ = x] = δₓ ∗ U(−∞, t]` the renewal measure of
the service process started with residual service `x`. -/
theorem ladderBeta_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) {x : ℝ} (hx : 0 ≤ x) :
    ladderBeta (gig1Lambda H G) x = ∫⁻ t, renMeas H (Measure.dirac x) (Iic t) ∂G := by
  set I := Measure.infinitePi fun _ : ℕ => H
  set S : ℕ → Set (ℝ × (ℕ → ℝ)) :=
    fun n => {p | resEpoch x p.2 n ≤ p.1 ∧ p.1 < resEpoch x p.2 (n + 1)} with hSdef
  have hZ : ∀ k, Measurable fun p : ℝ × (ℕ → ℝ) => resEpoch x p.2 k := fun k =>
    (measurable_resEpoch k).comp (measurable_const.prodMk measurable_snd)
  have hS : ∀ n, MeasurableSet (S n) := fun n =>
    (measurableSet_le (hZ n) measurable_fst).inter (measurableSet_lt measurable_fst (hZ (n + 1)))
  have hΛ : ∀ n, gig1Lambda H G n x univ = (G.prod I) (S n) := fun n => by
    change gig1LambdaMeasure H G n x univ = _
    rw [gig1LambdaMeasure_apply H G n x MeasurableSet.univ]
    congr 1
    ext p
    simp [gig1Set, hSdef]
  unfold ladderBeta
  simp_rw [hΛ]
  rw [tsum_mul_prod_apply G I _ hS]
  refine lintegral_congr_ae ((ae_nonneg_of_Iio hG0).mono fun t ht => ?_)
  beta_reduce
  rw [renMeas_dirac_apply H x measurableSet_Iic,
    lintegral_congr_ae ((tendsto_partialSum_atTop_ae H hH0 hHpos).mono fun u hu =>
      tsum_mul_straddle hx ht hu.2 hu.1)]
  have hm : ∀ m : ℕ, Measurable fun u : ℕ → ℝ => resEpoch x u (m + 1) := fun m =>
    (measurable_resEpoch (m + 1)).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_tsum (f := fun m u => (Iic t).indicator (1 : ℝ → ℝ≥0∞) (resEpoch x u (m + 1)))
    fun m => ((measurable_one.indicator measurableSet_Iic).comp (hm m)).aemeasurable]
  refine tsum_congr fun m => ?_
  refine (lintegral_congr fun u => ?_).trans (lintegral_indicator_one (hm m measurableSet_Iic))
  by_cases h : resEpoch x u (m + 1) ≤ t
  · rw [indicator_of_mem (mem_Iic.2 h), indicator_of_mem (show u ∈ {w | resEpoch x w
      (m + 1) ∈ Iic t} from mem_Iic.2 h)]
    rfl
  · rw [indicator_of_notMem (fun h' => h (mem_Iic.1 h')), indicator_of_notMem (show
      u ∉ {w | resEpoch x w (m + 1) ∈ Iic t} from fun h' => h (mem_Iic.1 h'))]

/-- **The stationary renewal identity and (19.83)** (MT p. 507): with the stationary
forward recurrence law `ν = µ⁻¹ H[y, ∞) dy` (`eqLaw H`), `∫ ν(dx) E[N(t) | R₀ = x] = t/µ`, so
`∫ ν(dx) β(x) = λ/µ`, where `µ`, `λ` are the mean service and interarrival times. -/
theorem lintegral_ladderBeta_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0)
    (hHm : renMean H ≠ ∞) :
    ∫⁻ x, ladderBeta (gig1Lambda H G) x ∂eqLaw H = (renMean H)⁻¹ * renMean G := by
  obtain ⟨hp, -⟩ := isProbabilityMeasure_fwdSkelInv_normalised H hH0 hHpos hHm
  have hνpos : ∀ᵐ x ∂eqLaw H, 0 ≤ x := ae_iff.2 (measure_mono_null (fun x hx => by
    simp only [mem_ofPred_eq, not_le] at hx; exact mem_Iic.2 hx.le) (eqLaw_Iic_zero H))
  set f : ℝ → ℝ → ℝ≥0∞ := fun x t => renMeas H (Measure.dirac x) (Iic t) with hfdef
  have hf : Measurable (Function.uncurry f) := by
    have e : Function.uncurry f = fun q : ℝ × ℝ =>
        ∑' m : ℕ, incr H {w | resEpoch q.1 w (m + 1) ∈ Iic q.2} :=
      funext fun q => renMeas_dirac_apply H q.1 measurableSet_Iic
    rw [e]
    refine Measurable.tsum fun m => ?_
    have hs : MeasurableSet {p : (ℝ × ℝ) × (ℕ → ℝ) | resEpoch p.1.1 p.2 (m + 1) ∈ Iic p.1.2} :=
      measurableSet_le ((measurable_resEpoch (m + 1)).comp
        (measurable_fst.fst.prodMk measurable_snd)) measurable_fst.snd
    exact measurable_measure_prodMk_left hs
  calc ∫⁻ x, ladderBeta (gig1Lambda H G) x ∂eqLaw H
      = ∫⁻ x, ∫⁻ t, f x t ∂G ∂eqLaw H :=
        lintegral_congr_ae (hνpos.mono fun x hx => ladderBeta_gig1 H G hH0 hHpos hG0 hx)
    _ = ∫⁻ t, ∫⁻ x, f x t ∂eqLaw H ∂G := lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ t, renMeas H (eqLaw H) (Iic t) ∂G :=
        lintegral_congr fun t => (renMeas_eq_lintegral H (eqLaw H) measurableSet_Iic).symm
    _ = ∫⁻ t, (renMean H)⁻¹ * ENNReal.ofReal t ∂G := lintegral_congr fun t => by
        rw [renMeas_eqLaw H hH0 hHpos hHm, Measure.smul_apply,
          Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi, Real.volume_Ioc, sub_zero,
          smul_eq_mul]
    _ = (renMean H)⁻¹ * renMean G := lintegral_const_mul _ ENNReal.measurable_ofReal

/-- **The stationary forward recurrence law is invariant for `Λ`** (MT p. 507):
`Σₙ Λₙ(x, ·) = ∫ G(dt) Pᵗ(x, ·)` for `x ≥ 0`, and `ν` is invariant for every `Pᵗ` (10.36). -/
theorem isInvariant_eqLaw_gig1 (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0)
    (hHm : renMean H ≠ ∞) : IsInvariant (ladderMarg (gig1Lambda H G)) (eqLaw H) := by
  obtain ⟨hp, hinv⟩ := isProbabilityMeasure_fwdSkelInv_normalised H hH0 hHpos hHm
  have hνpos : ∀ᵐ x ∂eqLaw H, 0 ≤ x := ae_iff.2 (measure_mono_null (fun x hx => by
    simp only [mem_ofPred_eq, not_le] at hx; exact mem_Iic.2 hx.le) (eqLaw_Iic_zero H))
  rw [isInvariant_iff]
  intro B hB
  set I := Measure.infinitePi fun _ : ℕ => H
  set g : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ∫⁻ u, ∑' n, (gig1Set n B).indicator (1 : ℝ × (ℝ × (ℕ → ℝ)) → ℝ≥0∞) (q.1, (q.2, u)) ∂I
    with hgdef
  have hgm : Measurable g :=
    Measurable.lintegral_prod_right' (f := fun p : (ℝ × ℝ) × (ℕ → ℝ) =>
      ∑' n, (gig1Set n B).indicator (1 : ℝ × (ℝ × (ℕ → ℝ)) → ℝ≥0∞) (p.1.1, (p.1.2, p.2)))
      (Measurable.tsum fun n => (measurable_one.indicator (measurableSet_gig1Set n hB)).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hmarg : ∀ x, ladderMarg (gig1Lambda H G) x B = ∫⁻ t, g (x, t) ∂G := by
    intro x
    rw [ladderMarg, Kernel.sum_apply' _ _ hB]
    have hΛ : ∀ n, gig1Lambda H G n x B = 1 * (G.prod I) (Prod.mk x ⁻¹' gig1Set n B) :=
      fun n => by rw [one_mul]; exact gig1LambdaMeasure_apply H G n x hB
    simp_rw [hΛ]
    rw [tsum_mul_prod_apply G I _ fun n => measurable_prodMk_left (measurableSet_gig1Set n hB)]
    simp only [one_mul, hgdef]
    rfl
  have hkern : ∀ x, 0 ≤ x → ∀ t, 0 ≤ t → g (x, t) = fwdSkelKernel H t x B := by
    intro x hx t ht
    rw [hgdef]
    simp only
    rw [lintegral_congr_ae ((tendsto_partialSum_atTop_ae H hH0 hHpos).mono fun u hu =>
      tsum_straddle_mem hx ht hu.2 hu.1 B), fwdSkelKernel,
      recursionKernel_apply' _ (measurable_fwdSkelStep t) x hB]
    have hm : Measurable fun u : ℕ → ℝ => fwdSkelStep t (x, u) :=
      (measurable_fwdSkelStep t).comp measurable_prodMk_left
    refine (lintegral_congr fun u => ?_).trans (lintegral_indicator_one (hm hB))
    by_cases h : fwdSkelStep t (x, u) ∈ B
    · rw [indicator_of_mem (show fwdTimeCts (resEpoch x u) t ∈ B from h),
        indicator_of_mem (show u ∈ {w | fwdSkelStep t (x, w) ∈ B} from h)]
      rfl
    · rw [indicator_of_notMem (show fwdTimeCts (resEpoch x u) t ∉ B from h),
        indicator_of_notMem (show u ∉ {w | fwdSkelStep t (x, w) ∈ B} from h)]
  calc ∫⁻ x, ladderMarg (gig1Lambda H G) x B ∂eqLaw H
      = ∫⁻ x, ∫⁻ t, g (x, t) ∂G ∂eqLaw H := lintegral_congr fun x => hmarg x
    _ = ∫⁻ t, ∫⁻ x, g (x, t) ∂eqLaw H ∂G := lintegral_lintegral_swap hgm.aemeasurable
    _ = ∫⁻ t, ∫⁻ x, fwdSkelKernel H t x B ∂eqLaw H ∂G :=
        lintegral_congr_ae ((ae_nonneg_of_Iio hG0).mono fun t ht =>
          lintegral_congr_ae (hνpos.mono fun x hx => hkern x hx t ht))
    _ = ∫⁻ _t, eqLaw H B ∂G :=
        lintegral_congr_ae ((ae_nonneg_of_Iio hG0).mono fun t ht =>
          (isInvariant_iff _ _).1 (hinv t ht) B hB)
    _ = eqLaw H B := by rw [lintegral_const, measure_univ, mul_one]

/-- **Theorem 19.3.5** (MT p. 506), first part: for the GI/G/1 queue with service law `H` (mean
`µ < ∞`) and interarrival law `G` (mean `λ`), the stationary forward recurrence law `ν` is an
invariant probability of the marginal chain `Φ_Λ`, `∫ ν(dx) β(x) = λ/µ` (19.83), and so the
average drift condition (19.68) holds if and only if `λ > µ`. -/
theorem theorem_19_3_5 (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    (hH0 : H (Iio 0) = 0) (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (hHm : renMean H ≠ ∞) :
    IsProbabilityMeasure (eqLaw H) ∧ IsInvariant (ladderMarg (gig1Lambda H G)) (eqLaw H) ∧
      ∫⁻ x, ladderBeta (gig1Lambda H G) x ∂eqLaw H = renMean G / renMean H ∧
      (1 < ∫⁻ x, ladderBeta (gig1Lambda H G) x ∂eqLaw H ↔ renMean H < renMean G) := by
  have h83 : ∫⁻ x, ladderBeta (gig1Lambda H G) x ∂eqLaw H = renMean G / renMean H := by
    rw [lintegral_ladderBeta_gig1 H G hH0 hHpos hG0 hHm, div_eq_mul_inv, mul_comm]
  refine ⟨(isProbabilityMeasure_fwdSkelInv_normalised H hH0 hHpos hHm).1,
    isInvariant_eqLaw_gig1 H G hH0 hHpos hG0 hHm, h83, ?_⟩
  rw [h83, ENNReal.lt_div_iff_mul_lt (Or.inl (renMean_ne_zero hHpos)) (Or.inl hHm), one_mul]

end MeynTweedie.GeneralizedDrift
