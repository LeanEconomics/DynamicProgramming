/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Option exercise: the waiting time until investment

Miao, §8.1, p. 233. The payoffs `z₀, z₁, …` are i.i.d. with distribution `F`, i.e. the path
`ω = (z_t)` has law `Measure.infinitePi (fun _ => F)`, and the decision maker invests the first
time the payoff exceeds the threshold `z*`. With `λ = F(z*) = F((−∞, z*])` (the probability of
not investing in a period), the event `{N = j}` that the project is invested at date `j` is
`{z₀ ≤ z*, …, z_{j−1} ≤ z*, z_j > z*}` (`od_waitEvent`).

* `od_wait_prob`: `Pr(N = j) = (1 − λ)λʲ`; `od_wait_total`: if `λ < 1` these sum to `1`.
* `od_wait_mean`: the mean of `N` is `∑ j Pr(N = j) = λ/(1 − λ)`; `od_wait_mean_dates`: counting
  the first draw as period `1` (`N + 1`), the mean is `1/(1 − λ)`.
* `od_wait_mean_mono`: the mean waiting time increases with the threshold `z*`.

**Correction.** The book's `Pr(N = j) = (1 − λ)λʲ` (`j = 0, 1, …`) and `E[N] = 1/(1 − λ)` are
inconsistent: with that distribution `E[N] = λ/(1 − λ)` (`od_wait_mean_misprint`); the mean
`1/(1 − λ)` is that of `N + 1`, the number of draws until the investment, with
`Pr(N + 1 = j) = (1 − λ)λ^{j−1}`, `j ≥ 1`.
-/

namespace Miao.Applications

open MeasureTheory

/-- The event `{N = j}`: the first `j` payoffs are at most `z*` and the `j`-th exceeds it. -/
def od_waitEvent (zs : ℝ) (j : ℕ) : Set (ℕ → ℝ) :=
  {ω | (∀ i < j, ω i ≤ zs) ∧ zs < ω j}

/-- The probability `λ = F(z*)` that the project is not invested in a given period. -/
noncomputable def od_waitLam (F : Measure ℝ) (zs : ℝ) : ℝ := (F (Set.Iic zs)).toReal

variable {F : Measure ℝ} [IsProbabilityMeasure F]

theorem od_waitLam_mem (zs : ℝ) : 0 ≤ od_waitLam F zs ∧ od_waitLam F zs ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold od_waitLam
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩

theorem od_waitEvent_eq (zs : ℝ) (j : ℕ) :
    od_waitEvent zs j = Set.pi (↑(Finset.range (j + 1)))
      (fun i => if i < j then Set.Iic zs else Set.Ioi zs) := by
  ext ω
  simp only [od_waitEvent, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    split_ifs with h
    · exact h1 i h
    · have : i = j := by omega
      subst this; exact h2
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i (by omega)
      simp only [hi, ↓reduceIte, Set.mem_Iic] at this
      exact this
    · have := h j (by omega)
      simp only [lt_irrefl, ↓reduceIte, Set.mem_Ioi] at this
      exact this

/-- Miao, p. 233: `Pr(N = j) = (1 − λ)λʲ` for i.i.d. payoffs and `λ = F(z*)`. -/
theorem od_wait_prob (zs : ℝ) (j : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => F) (od_waitEvent zs j)).toReal =
      (1 - od_waitLam F zs) * od_waitLam F zs ^ j := by
  rw [od_waitEvent_eq, Measure.infinitePi_pi]
  swap
  · intro i _
    split_ifs
    · exact measurableSet_Iic
    · exact measurableSet_Ioi
  rw [Finset.prod_range_succ, ENNReal.toReal_mul, ENNReal.toReal_prod]
  simp only [lt_irrefl, ↓reduceIte]
  have hprod : ∏ i ∈ Finset.range j, (F (if i < j then Set.Iic zs else Set.Ioi zs)).toReal =
      od_waitLam F zs ^ j := by
    rw [show od_waitLam F zs ^ j = ∏ _i ∈ Finset.range j, od_waitLam F zs by simp]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_range.1 hi, ↓reduceIte, od_waitLam]
  have hc : (F (Set.Ioi zs)).toReal = 1 - od_waitLam F zs := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, od_waitLam,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [hprod, hc, mul_comm]

/-- Miao, p. 233: if `λ < 1`, the probabilities `Pr(N = j)` sum to one (the project is invested
eventually, almost surely). -/
theorem od_wait_total {zs : ℝ} (hlam : od_waitLam F zs < 1) :
    HasSum (fun j => (Measure.infinitePi (fun _ : ℕ => F) (od_waitEvent zs j)).toReal) 1 := by
  simp only [od_wait_prob]
  have h := (hasSum_geometric_of_lt_one (od_waitLam_mem zs).1 hlam).mul_left (1 - od_waitLam F zs)
  rwa [mul_inv_cancel₀ (by linarith)] at h

/-- Miao, p. 233 (corrected): the mean waiting time is `E[N] = ∑ j Pr(N = j) = λ/(1 − λ)`. -/
theorem od_wait_mean {zs : ℝ} (hlam : od_waitLam F zs < 1) :
    HasSum (fun j : ℕ => j * (Measure.infinitePi (fun _ : ℕ => F) (od_waitEvent zs j)).toReal)
      (od_waitLam F zs / (1 - od_waitLam F zs)) := by
  simp only [od_wait_prob]
  have hn : ‖od_waitLam F zs‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (od_waitLam_mem zs).1]; exact hlam
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 - od_waitLam F zs)
  have hne : 1 - od_waitLam F zs ≠ 0 := by linarith
  convert h using 1
  · funext j; ring
  · field_simp

/-- Miao, p. 233: counting the first draw as period `1`, the mean number of periods until the
investment is `E[N + 1] = 1/(1 − λ)`, the book's formula. -/
theorem od_wait_mean_dates {zs : ℝ} (hlam : od_waitLam F zs < 1) :
    HasSum (fun j : ℕ =>
      (j + 1) * (Measure.infinitePi (fun _ : ℕ => F) (od_waitEvent zs j)).toReal)
      (1 / (1 - od_waitLam F zs)) := by
  have h := (od_wait_mean hlam).add (od_wait_total hlam)
  have hne : 1 - od_waitLam F zs ≠ 0 := by linarith
  convert h using 1
  · funext j; ring
  · field_simp; ring

omit [IsProbabilityMeasure F] in
/-- Miao, p. 233, the misprint: with `Pr(N = j) = (1 − λ)λʲ`, the mean `λ/(1 − λ)` is never the
printed `1/(1 − λ)`. -/
theorem od_wait_mean_misprint {zs : ℝ} (hlam : od_waitLam F zs < 1) :
    od_waitLam F zs / (1 - od_waitLam F zs) ≠ 1 / (1 - od_waitLam F zs) := by
  have hpos : 0 < 1 - od_waitLam F zs := by linarith
  intro h
  rw [div_left_inj' hpos.ne'] at h
  linarith

/-- Miao, p. 233 ("the mean waiting time increases with the threshold `z*`"). -/
theorem od_wait_mean_mono {zs₁ zs₂ : ℝ} (h12 : zs₁ ≤ zs₂) (hlam : od_waitLam F zs₂ < 1) :
    od_waitLam F zs₁ ≤ od_waitLam F zs₂ ∧
      od_waitLam F zs₁ / (1 - od_waitLam F zs₁) ≤ od_waitLam F zs₂ / (1 - od_waitLam F zs₂) ∧
      1 / (1 - od_waitLam F zs₁) ≤ 1 / (1 - od_waitLam F zs₂) := by
  have hle : od_waitLam F zs₁ ≤ od_waitLam F zs₂ :=
    ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Iic_subset_Iic.2 h12))
  have h0 := (od_waitLam_mem (F := F) zs₁).1
  have hp1 : 0 < 1 - od_waitLam F zs₁ := by linarith
  have hp2 : 0 < 1 - od_waitLam F zs₂ := by linarith
  refine ⟨hle, ?_, ?_⟩
  · rw [div_le_div_iff₀ hp1 hp2]; nlinarith
  · exact one_div_le_one_div_of_le hp2 (by linarith)

end Miao.Applications
