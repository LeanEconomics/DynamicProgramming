/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.ModelQueues
import FErgodicity.SpecificMatrices
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Poisson counts of exponential services (MT (3.14)–(3.19))

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/PoissonCounts.lean`), with the namespace changed to
`MeynTweedie.FErgodicity` and the imports to `InvariantMeasures.*`.

Meyn and Tweedie, §3.3.3, pp. 56–58, cite Çinlar for the fact that the number of exponential
services completed in a time `t` is Poisson with parameter `μt`. This module proves it, and the
mixed Poisson laws of the embedded GI/M/1 and M/G/1 chains that follow.

* `countEvent j t`: exactly `j` of the services `S₁, S₂, …` are completed by `t`.
* `eq_3_18`: **(3.18)**, `P(S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}) = e^{−μt}(μt)ʲ/j!`, by induction
  on `j`, conditioning on the first service (`pi_finSucc_eq_lintegral`, `cons_mem_countEvent`)
  and integrating against the exponential density (`lintegral_poissonCount`). No Erlang law is
  needed.
* `eq_3_14`: **(3.14)/(3.17)**, `p₀ = P(S > T) = ∫ e^{−μt} G(dt)`.
* `eq_3_15`: **(3.15)**, `pⱼ = P(exactly j services in T) = ∫ e^{−μt}(μt)ʲ/j! G(dt)`.
* `eq_3_19`: **(3.19)**, the M/G/1 arrival counts `qⱼ = ∫ e^{−rt}(rt)ʲ/j! H(dt)`.
* The memoryless property (3.17) is `expMeasure_memoryless` in `ModelQueues`.

**Correction.** (3.18) as printed, `P(S₀ + ⋯ + S_{j+1} > t > S₀ + ⋯ + Sⱼ) = e^{−μt}(μt)ʲ/j!`,
counts `j + 1` completed services `S₀, …, Sⱼ`, so the index is off by one: the probability of
exactly one completion by `t` is `μt e^{−μt}`, not `e^{−μt}` (`eq_3_18_counterexample`). The
correct form is `eq_3_18`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

/-- The event that exactly `j` of the i.i.d. service times `S₁, …, S_{j+1}` are completed by
time `t`: `S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}` (coordinates `u₀, …, uⱼ`). -/
def countEvent (j : ℕ) (t : ℝ) : Set (Fin (j + 1) → ℝ) :=
  {u | ∑ i : Fin j, u (Fin.castSucc i) ≤ t ∧ t < ∑ i, u i}

/-- The count event is measurable. -/
theorem measurableSet_countEvent (j : ℕ) (t : ℝ) : MeasurableSet (countEvent j t) := by
  have h1 : Measurable fun u : Fin (j + 1) → ℝ => ∑ i : Fin j, u (Fin.castSucc i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  have h2 : Measurable fun u : Fin (j + 1) → ℝ => ∑ i, u i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_lt measurable_const h2)

/-- Conditioning on the first service time `s`: exactly `j + 1` completions by `t` means
exactly `j` completions of the remaining services by `t − s`. -/
theorem cons_mem_countEvent (j : ℕ) (t s : ℝ) (v : Fin (j + 1) → ℝ) :
    (Fin.cons s v : Fin (j + 2) → ℝ) ∈ countEvent (j + 1) t ↔ v ∈ countEvent j (t - s) := by
  simp only [countEvent, mem_ofPred_eq]
  rw [Fin.sum_univ_succ, Fin.sum_cons]
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Splitting off the first coordinate of `ν^{⊗(j+1)}`:
`ν^{⊗(j+1)}(E) = ∫ ν^{⊗j}{v : (s, v) ∈ E} ν(ds)`. -/
theorem pi_finSucc_eq_lintegral (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : ℕ)
    {E : Set (Fin (j + 1) → ℝ)} (hE : MeasurableSet E) :
    (Measure.pi fun _ : Fin (j + 1) => ν) E =
      ∫⁻ s, (Measure.pi fun _ : Fin j => ν) {v | (Fin.cons s v : Fin (j + 1) → ℝ) ∈ E} ∂ν := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => ν) 0
  rw [← hmp.symm.measure_preimage_equiv, Measure.prod_apply
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => ℝ) 0).symm.measurable hE)]
  refine lintegral_congr fun s => ?_
  congr 1
  ext v
  simp only [mem_preimage, mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero']

/-- The Poisson probability `e^{−μt}(μt)ʲ/j!` for `t ≥ 0`, and `0` for `t < 0`. -/
noncomputable def poissonCount (μ : ℝ) (j : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ici (0 : ℝ)).indicator
    (fun t => exp (-(μ * t)) * (μ * t) ^ j / j.factorial) t)

/-- `t ↦ e^{−μt}(μt)ʲ/j!` (cut off at `0`) is measurable. -/
theorem measurable_poissonCount (μ : ℝ) (j : ℕ) : Measurable (poissonCount μ j) :=
  ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ =>
    exp (-(μ * t)) * (μ * t) ^ j / j.factorial).indicator measurableSet_Ici)

/-- For `t ≥ 0` the cut-off Poisson weight is `e^{−μt}(μt)ʲ/j!`. -/
theorem poissonCount_of_nonneg (μ : ℝ) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    poissonCount μ j t = ENNReal.ofReal (exp (-(μ * t)) * (μ * t) ^ j / j.factorial) := by
  rw [poissonCount, indicator_of_mem (mem_Ici.2 ht)]

/-- For `t < 0` the cut-off Poisson weight is `0`. -/
theorem poissonCount_of_neg (μ : ℝ) (j : ℕ) {t : ℝ} (ht : t < 0) : poissonCount μ j t = 0 := by
  rw [poissonCount, indicator_of_notMem (by simpa using ht), ENNReal.ofReal_zero]

/-- The convolution step behind (3.18): integrating the `j`-count probability at `t − s`
against an exponential first service time gives the `(j + 1)`-count probability,
`∫ e^{−μ(t−s)}(μ(t−s))ʲ/j! μe^{−μs} ds = e^{−μt}(μt)^{j+1}/(j+1)!` over `0 ≤ s ≤ t`. -/
theorem lintegral_poissonCount {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (t : ℝ) :
    ∫⁻ s, poissonCount μ j (t - s) ∂expMeasure μ = poissonCount μ (j + 1) t := by
  have hexp : expMeasure μ = volume.withDensity (exponentialPDF μ) := rfl
  have hpdf : Measurable (exponentialPDF μ) := (measurable_exponentialPDFReal μ).ennreal_ofReal
  rw [hexp, lintegral_withDensity_eq_lintegral_mul _ hpdf
    (g := fun s => poissonCount μ j (t - s))
    ((measurable_poissonCount μ j).comp (measurable_const.sub measurable_id))]
  rcases lt_or_ge t 0 with ht | ht
  · rw [poissonCount_of_neg μ _ ht]
    refine (lintegral_congr fun s => ?_).trans lintegral_zero
    simp only [Pi.mul_apply]
    rcases lt_or_ge s 0 with hs | hs
    · rw [exponentialPDF_of_neg hs, zero_mul]
    · rw [poissonCount_of_neg μ j (by linarith), mul_zero]
  · set F : ℝ → ℝ := fun s => μ ^ (j + 1) * exp (-(μ * t)) * (t - s) ^ j / j.factorial
      with hF
    have hpt : ∀ s, (exponentialPDF μ * fun s => poissonCount μ j (t - s)) s =
        (Icc 0 t).indicator (fun s => ENNReal.ofReal (F s)) s := by
      intro s
      simp only [Pi.mul_apply]
      rcases lt_or_ge s 0 with hs | hs
      · rw [exponentialPDF_of_neg hs, zero_mul, indicator_of_notMem (by simp [hs])]
      · rcases le_or_gt s t with hst | hst
        · rw [exponentialPDF_of_nonneg hs, poissonCount_of_nonneg μ j (by linarith),
            indicator_of_mem (mem_Icc.2 ⟨hs, hst⟩),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have he : exp (-(μ * s)) * exp (-(μ * (t - s))) = exp (-(μ * t)) := by
            rw [← exp_add]
            ring_nf
          rw [hF]
          simp only
          rw [mul_pow, ← he]
          ring
        · rw [poissonCount_of_neg μ j (by linarith), mul_zero,
            indicator_of_notMem (by simp only [mem_Icc, not_and, not_le]; intro; exact hst)]
    have hcont : Continuous F := by
      rw [hF]
      fun_prop
    have hint : IntegrableOn F (Icc 0 t) := hcont.integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 t)] F := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
      have : 0 ≤ t - s := by linarith [hs.2]
      simp only [Pi.zero_apply, hF]
      positivity
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht, poissonCount_of_nonneg μ _ ht]
    congr 1
    have hI : ∫ s in (0 : ℝ)..t, F s =
        μ ^ (j + 1) * exp (-(μ * t)) / j.factorial * ∫ s in (0 : ℝ)..t, (t - s) ^ j := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext s
      rw [hF]
      ring
    rw [hI, intervalIntegral.integral_comp_sub_left (fun x => x ^ j) t, sub_self, sub_zero,
      integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **(3.18)**, MT p. 57 (Çinlar's elementary property of exponential sums). For i.i.d.
exponential services of rate `μ > 0`, the number completed in `[0, t]` is Poisson with parameter
`μt`: `P(S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}) = e^{−μt}(μt)ʲ/j!` (and `0` for `t < 0`). -/
theorem eq_3_18 {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin (j + 1) => expMeasure μ) (countEvent j t) = poissonCount μ j t := by
  have := isProbabilityMeasure_expMeasure hμ
  induction j generalizing t with
  | zero =>
    have hms : MeasurableSet {s : ℝ | 0 ≤ t ∧ t < s} :=
      (MeasurableSet.const (0 ≤ t)).inter (measurableSet_lt measurable_const measurable_id)
    rw [pi_finSucc_eq_lintegral _ 0 (measurableSet_countEvent _ _)]
    have h1 : ∀ s, (Measure.pi fun _ : Fin 0 => expMeasure μ)
        {v | (Fin.cons s v : Fin 1 → ℝ) ∈ countEvent 0 t} =
          {s : ℝ | 0 ≤ t ∧ t < s}.indicator 1 s := by
      intro s
      have hv : ∀ v : Fin 0 → ℝ, (Fin.cons s v : Fin 1 → ℝ) ∈ countEvent 0 t ↔ 0 ≤ t ∧ t < s := by
        intro v
        simp [countEvent]
      by_cases h : 0 ≤ t ∧ t < s
      · rw [indicator_of_mem (show s ∈ {s : ℝ | 0 ≤ t ∧ t < s} from h)]
        convert measure_univ (μ := Measure.pi fun _ : Fin 0 => expMeasure μ)
        ext v
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (hv v).2 h
      · rw [indicator_of_notMem (show s ∉ {s : ℝ | 0 ≤ t ∧ t < s} from h)]
        convert measure_empty (μ := Measure.pi fun _ : Fin 0 => expMeasure μ)
        ext v
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hc => h ((hv v).1 hc)
    simp_rw [h1]
    rw [lintegral_indicator_one hms]
    rcases lt_or_ge t 0 with ht | ht
    · rw [poissonCount_of_neg μ 0 ht]
      convert measure_empty (μ := expMeasure μ)
      ext s
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    · rw [poissonCount_of_nonneg μ 0 ht]
      have : {s : ℝ | 0 ≤ t ∧ t < s} = Ioi t := by
        ext s
        simp [ht]
      rw [this, expMeasure_Ioi hμ ht]
      simp
  | succ j ih =>
    rw [pi_finSucc_eq_lintegral _ (j + 1) (measurableSet_countEvent _ _),
      ← lintegral_poissonCount hμ]
    refine lintegral_congr fun s => ?_
    rw [← ih]
    congr 1
    ext v
    exact cons_mem_countEvent j t s v

/-- **(3.15)**, MT p. 56. With interarrival time `T ∼ G` independent of the exponential
services, the probability that exactly `j` services are completed during `T` is
`pⱼ = ∫ e^{−μt}(μt)ʲ/j! G(dt)` (`poissonWeight`). -/
theorem eq_3_15 (G : Measure ℝ≥0) [SFinite G] {μ : ℝ≥0} (hμ : 0 < μ) (j : ℕ) :
    (G.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure μ))
        {p | p.2 ∈ countEvent j p.1} = poissonWeight G μ j := by
  have hm : MeasurableSet {p : ℝ≥0 × (Fin (j + 1) → ℝ) | p.2 ∈ countEvent j p.1} := by
    have h1 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) =>
        ∑ i : Fin j, p.2 (Fin.castSucc i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).comp measurable_snd
    have h2 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) => ∑ i, p.2 i :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).comp measurable_snd
    have h3 : Measurable fun p : ℝ≥0 × (Fin (j + 1) → ℝ) => ((p.1 : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_fst
    exact (measurableSet_le h1 h3).inter (measurableSet_lt h3 h2)
  have := isProbabilityMeasure_expMeasure (by exact_mod_cast hμ : (0 : ℝ) < μ)
  rw [Measure.prod_apply hm, poissonWeight_eq]
  refine lintegral_congr fun t => ?_
  have : Prod.mk t ⁻¹' {p : ℝ≥0 × (Fin (j + 1) → ℝ) | p.2 ∈ countEvent j p.1} =
      countEvent j t := rfl
  rw [this, eq_3_18 (by exact_mod_cast hμ), poissonCount_of_nonneg _ _ t.coe_nonneg, NNReal.coe_mul]

/-- **Correction to (3.18)** (MT p. 57). As printed, the event has `j + 1` completed services
`S₀, …, Sⱼ` but the Poisson weight of `j`. With `j = 0`, `μ = 1`, `t = 2`: the probability that
exactly one service is completed by `t` is `2e^{−2}`, not `e^{−2}`. The correct statement is
`eq_3_18` (sums `S₁ + ⋯ + Sⱼ ≤ t < S₁ + ⋯ + S_{j+1}`). -/
theorem eq_3_18_counterexample :
    (Measure.pi fun _ : Fin 2 => expMeasure 1) (countEvent 1 2) ≠
      ENNReal.ofReal (exp (-(1 * 2)) * (1 * 2) ^ 0 / (Nat.factorial 0)) := by
  rw [eq_3_18 one_pos, poissonCount_of_nonneg _ _ (by norm_num)]
  have hpos : 0 < exp (-(1 * 2 : ℝ)) := exp_pos _
  rw [Ne, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  norm_num

/-- **(3.14)** and **(3.17)**, MT pp. 56–57: the probability that the exponential service in
progress outlasts an independent interarrival time `T ∼ G` is
`p₀ = P(S > T) = ∫ e^{−μt} G(dt)`. -/
theorem eq_3_14 (G : Measure ℝ≥0) [SFinite G] {μ : ℝ≥0} (hμ : 0 < μ) :
    (G.prod (expMeasure μ)) {p | (p.1 : ℝ) < p.2} = poissonWeight G μ 0 := by
  have := isProbabilityMeasure_expMeasure (by exact_mod_cast hμ : (0 : ℝ) < μ)
  have hm : MeasurableSet {p : ℝ≥0 × ℝ | (p.1 : ℝ) < p.2} :=
    measurableSet_lt (measurable_coe_nnreal_real.comp measurable_fst) measurable_snd
  rw [Measure.prod_apply hm, poissonWeight_eq]
  refine lintegral_congr fun t => ?_
  have : Prod.mk t ⁻¹' {p : ℝ≥0 × ℝ | (p.1 : ℝ) < p.2} = Ioi (t : ℝ) := rfl
  rw [this, expMeasure_Ioi (by exact_mod_cast hμ) t.coe_nonneg, NNReal.coe_mul]
  simp

/-- **(3.19)**, MT p. 58: in the M/G/1 queue the number of Poisson(`r`) arrivals during a
service time `T ∼ H` is `j` with probability `qⱼ = ∫ e^{−rt}(rt)ʲ/j! H(dt)`. -/
theorem eq_3_19 (H : Measure ℝ≥0) [SFinite H] {r : ℝ≥0} (hr : 0 < r) (j : ℕ) :
    (H.prod (Measure.pi fun _ : Fin (j + 1) => expMeasure r))
        {p | p.2 ∈ countEvent j p.1} = poissonWeight H r j :=
  eq_3_15 H hr j

end MeynTweedie.FErgodicity
