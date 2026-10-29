/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.MartingaleFCLT
import Mathlib.Probability.CondVar

/-!
# Tools for the martingale FCLT under (D.8) and (D.9) (MT Theorem D.6.4)

The general form of Theorem D.6.4 (MT p. 563) is proved in `MartingaleFCLTGeneral` by truncating
the increments at `√(εn)`, recentring them, and stopping them when the conditional-variance clock
leaves a band around the time. This module collects the tools.

* Martingale-difference arrays: `array_weighted_clt_rows`, `array_fidi_clt_rows`,
  `array_fidiLin_polygonal_rows` (fidis of the polygonal processes of an array, along rows, under
  almost sure hypotheses) and `array_fidiLin_polygonal_of_tendstoInMeasure` (under convergence in
  probability, by the subsequence principle).
* Localisation: `locWeight` (the predictable weight `1{Σ_{j≤k} E[Wⱼ | 𝓕ⱼ] ≤ c}`),
  `sum_integral_locWeight_mul_le`, and **Lenglart's inequality**
  `measureReal_sum_ge_le_lenglart`: `P(Σ Xₖ ≥ a) ≤ c/a + P(Σ E[Xₖ | 𝓕ₖ] > c)`.
* `eventually_abs_sum_sub_le`: if `(1/n) Σ_{k<n} uₖ → 1` with `uₖ ≥ 0`, then
  `max_{j≤n} |Σ_{k<j} uₖ − j| = o(n)` (Pólya's uniformity for monotone limits).
* `tendsto_measureReal_exists_big`: under (D.9), `P(∃ k < n, Dₖ² ≥ εn) → 0` (Lenglart).
* `integral_pow_four_sum_le_clock`: `E[(Σ_{i<m} dᵢ)⁴] ≤ 8c² + 3b²c` for martingale differences
  with `|dᵢ| ≤ b` and conditional-variance clock `Σ E[dᵢ² | 𝓖ᵢ] ≤ c`.
* The construction: `bigSq` (`D² 1{D² ≥ a}`), `truncSq` (`D 1{D² < a}`), `ctrunc` (recentred),
  `cvar` (its conditional variance), `ctClock`, `activeW` (stopping when the clock leaves the
  band `|clock(j) − j| ≤ τ`), `locInc`; `truncSq_pointwise`, `abs_sub_truncSq_le`,
  `truncSq_props`, `ctrunc_props`.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Martingale-difference arrays -/

/-- **A CLT for weighted martingale-difference arrays**: for rows `i` of martingale differences
`Y i k` with `Σ_{k<rᵢ} E[(Y i k)²] ≤ C rᵢ`, `max_{k≤rᵢ} (Y i k)²/rᵢ → 0` a.s., and deterministic
weights `|w i k| ≤ W` with `(1/rᵢ) Σ_{k<rᵢ} w i k² (Y i k)² → τ²` a.s.,
`rᵢ^{−1/2} Σ_{k<rᵢ} w i k Y i k ⇒ N(0, τ²)`. -/
theorem array_weighted_clt_rows {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (Y i k)) (hL2 : ∀ i k, MemLp (Y i k) 2 Q)
    (h0 : ∀ i k, Q[Y i k | ℱ k] =ᵐ[Q] 0) {r : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ i, ∑ k ∈ Finset.range (r i), ∫ ω, Y i k ω ^ 2 ∂Q ≤ C * r i)
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, Y i k ω ^ 2 ≤ ε * r i)
    {w : ℕ → ℕ → ℝ} {W : ℝ} (hW : ∀ i k, |w i k| ≤ W) {τ2 : ℝ} (hτ : 0 ≤ τ2)
    (hwvar : ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range (r i), w i k ^ 2 * Y i k ω ^ 2) / r i) atTop (𝓝 τ2))
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 τ2.toNNReal) Q') :
    TendstoInDistribution (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (r i), w i k * Y i k ω) atTop Z (fun _ => Q) Q' := by
  set X : ℕ → ℕ → Ω → ℝ := fun i k ω => (√(r i : ℝ))⁻¹ * (w i k * Y i k ω) with hXdef
  have hXsq : ∀ i k ω, X i k ω ^ 2 = w i k ^ 2 * Y i k ω ^ 2 / r i := fun i k ω => by
    simp only [hXdef]
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, inv_mul_eq_div]
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0 0)
  have hX : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (X i k) := fun i k =>
    ((hY i k).const_mul (w i k)).const_mul _
  have hXL2 : ∀ i k, MemLp (X i k) 2 Q := fun i k => ((hL2 i k).const_mul _).const_mul _
  have hX0 : ∀ i k, Q[X i k | ℱ k] =ᵐ[Q] 0 := fun i k => by
    have := condExp_smul (μ := Q) ((√(r i : ℝ))⁻¹ * w i k) (Y i k) (ℱ k)
    have e : X i k = ((√(r i : ℝ))⁻¹ * w i k) • Y i k := by
      ext ω; simp only [hXdef, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    refine this.trans ((h0 i k).mono fun ω h => ?_)
    simp [h]
  have hsum : ∀ i ω, ∑ k ∈ Finset.range (r i), X i k ω ^ 2 =
      (∑ k ∈ Finset.range (r i), w i k ^ 2 * Y i k ω ^ 2) / r i := fun i ω => by
    simp only [hXsq, Finset.sum_div]
  have hfun : (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ * ∑ k ∈ Finset.range (r i), w i k * Y i k ω) =
      fun (i : ℕ) ω => ∑ k ∈ Finset.range (r i), X i k ω := by
    funext i ω; simp only [hXdef, Finset.mul_sum]
  rw [hfun]
  refine martingale_array_clt (L := r) hX hXL2 hX0 hτ ?_ ?_ (C := W ^ 2 * C) ?_ hZ
  · filter_upwards [hwvar] with ω hω
    exact hω.congr fun i => (hsum i ω).symm
  · filter_upwards [hmax] with ω hω ε hε
    have hε' : 0 < ε ^ 2 / (W ^ 2 + 1) := by positivity
    filter_upwards [hω _ hε'] with i hi k hk
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast (show 0 < r i by omega)
    have hsq : X i k ω ^ 2 ≤ ε ^ 2 := by
      rw [hXsq, div_le_iff₀ hn0]
      have h1 : w i k ^ 2 ≤ W ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hW i k) 2
      have h2 := hi k hk.le
      calc w i k ^ 2 * Y i k ω ^ 2 ≤ W ^ 2 * (ε ^ 2 / (W ^ 2 + 1) * r i) :=
            mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
        _ ≤ ε ^ 2 * r i := by
            rw [← mul_assoc, ← mul_div_assoc, mul_comm (W ^ 2) (ε ^ 2), mul_div_assoc]
            gcongr
            · exact mul_le_of_le_one_right (sq_nonneg _)
                ((div_le_one (by positivity)).2 (by linarith))
    rw [← sq_abs (X i k ω)] at hsq
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le two_ne_zero).1 hsq
  · intro i
    rcases Nat.eq_zero_or_pos (r i) with h | hn
    · rw [h]
      simp only [Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg (sq_nonneg W) hC
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast hn
    simp_rw [hXsq]
    have e : ∀ k, ∫ ω, w i k ^ 2 * Y i k ω ^ 2 / r i ∂Q =
        w i k ^ 2 * (∫ ω, Y i k ω ^ 2 ∂Q) / r i :=
      fun k => by rw [integral_div, integral_const_mul]
    simp_rw [e]
    rw [← Finset.sum_div, div_le_iff₀ hn0]
    calc ∑ k ∈ Finset.range (r i), w i k ^ 2 * ∫ ω, Y i k ω ^ 2 ∂Q
        ≤ ∑ k ∈ Finset.range (r i), W ^ 2 * ∫ ω, Y i k ω ^ 2 ∂Q := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_
            (integral_nonneg fun ω => sq_nonneg _)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hW i k) 2
      _ = W ^ 2 * ∑ k ∈ Finset.range (r i), ∫ ω, Y i k ω ^ 2 ∂Q := by rw [Finset.mul_sum]
      _ ≤ W ^ 2 * (C * r i) := mul_le_mul_of_nonneg_left (hbdd i) (sq_nonneg W)
      _ = W ^ 2 * C * r i := by ring

/-- **The finite-dimensional CLT for martingale-difference arrays** `Y i k`: for times `tⱼ ≤ 1`,
row lengths `rᵢ` with `(1/rᵢ) Σ_{k<⌊rᵢ tⱼ⌋} Dₖ² → tⱼ σ²` and
`max_{k≤rᵢ} Dₖ²/rᵢ → 0` a.s., and `Σ_{k<n} E[Dₖ²] ≤ C n`,
`rᵢ^{−1/2} Σⱼ cⱼ S_{⌊rᵢ tⱼ⌋} ⇒ N(0, σ² Σⱼₗ cⱼ cₗ min(tⱼ, tₗ))`. -/
theorem array_fidi_clt_rows {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (Y i k)) (hL2 : ∀ i k, MemLp (Y i k) 2 Q)
    (h0 : ∀ i k, Q[Y i k | ℱ k] =ᵐ[Q] 0) {r : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ i, ∑ k ∈ Finset.range (r i), ∫ ω, Y i k ω ^ 2 ∂Q ≤ C * r i)
    {K : ℕ} (t : Fin K → ℝ) (ht1 : ∀ i, t i ≤ 1) (c : Fin K → ℝ)
    {σ2 : ℝ}
    (hvt : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * t j⌋₊, Y i k ω ^ 2) / r i) atTop (𝓝 (t j * σ2)))
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, Y i k ω ^ 2 ≤ ε * r i)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0
      (σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j)).toNNReal) Q') :
    TendstoInDistribution (fun (i : ℕ) ω => (√(r i : ℝ))⁻¹ *
      ∑ j, c j * ∑ k ∈ Finset.range ⌊(r i : ℝ) * t j⌋₊, Y i k ω) atTop Z (fun _ => Q) Q' := by
  set w : ℕ → ℕ → ℝ := fun n k => ∑ i, c i * (if k < ⌊(r n : ℝ) * t i⌋₊ then 1 else 0) with hw
  have hfl : ∀ (n : ℕ) i, ⌊(r n : ℝ) * t i⌋₊ ≤ r n := fun n i => by
    refine Nat.floor_le_of_le ?_
    calc (r n : ℝ) * t i ≤ r n * 1 := mul_le_mul_of_nonneg_left (ht1 i) (Nat.cast_nonneg _)
      _ = r n := mul_one _
  have hrep : ∀ (n : ℕ) ω, ∑ i, c i * ∑ k ∈ Finset.range ⌊(r n : ℝ) * t i⌋₊, Y n k ω =
      ∑ k ∈ Finset.range (r n), w n k * Y n k ω := by
    intro n ω
    simp only [hw, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_range_ite_lt (fun k => Y n k ω) (hfl n i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hW : ∀ n k, |w n k| ≤ ∑ i, |c i| := fun n k => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    split_ifs <;> simp
  have hmin : ∀ (n k : ℕ) i j, (if k < ⌊(r n : ℝ) * t i⌋₊ then (1 : ℝ) else 0) *
      (if k < ⌊(r n : ℝ) * t j⌋₊ then 1 else 0) =
        if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then 1 else 0 := by
    intro n k i j
    have e : ⌊(r n : ℝ) * min (t i) (t j)⌋₊ = min ⌊(r n : ℝ) * t i⌋₊ ⌊(r n : ℝ) * t j⌋₊ := by
      rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg _)]
      exact Monotone.map_min Nat.floor_mono
    rw [e]
    by_cases h1 : k < ⌊(r n : ℝ) * t i⌋₊ <;> by_cases h2 : k < ⌊(r n : ℝ) * t j⌋₊ <;>
      simp [h1, h2, lt_min_iff]
  have hwvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range (r n), w n k ^ 2 * Y n k ω ^ 2) / r n)
      atTop (𝓝 (σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j))) := by
    filter_upwards [ae_all_iff.2 hvt] with ω hω
    have hij : ∀ i j, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (r n),
        (if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * Y n k ω ^ 2) / r n) atTop
        (𝓝 (min (t i) (t j) * σ2)) := by
      intro i j
      have hm : ∃ l, min (t i) (t j) = t l := by
        rcases le_total (t i) (t j) with h | h
        · exact ⟨i, min_eq_left h⟩
        · exact ⟨j, min_eq_right h⟩
      obtain ⟨l, hl⟩ := hm
      rw [hl]
      refine (hω l).congr fun n => ?_
      congr 1
      rw [← sum_range_ite_lt (fun k => Y n k ω ^ 2) (hfl n l)]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    have hall := tendsto_finsetSum (Finset.univ : Finset (Fin K)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin K)) fun j _ => (hij i j).const_mul (c i * c j)
    have hlim : ∑ i, ∑ j, c i * c j * (min (t i) (t j) * σ2) =
        σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hlim] at hall
    refine hall.congr fun n => ?_
    have e : ∀ k, w n k ^ 2 * Y n k ω ^ 2 = ∑ i, ∑ j, c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * Y n k ω ^ 2) := by
      intro k
      simp only [hw]
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hmin n k i j]
      ring
    simp_rw [e]
    have e2 : ∑ k ∈ Finset.range (r n), ∑ i, ∑ j, c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * Y n k ω ^ 2) =
        ∑ i, ∑ j, ∑ k ∈ Finset.range (r n), c i * c j *
        ((if k < ⌊(r n : ℝ) * min (t i) (t j)⌋₊ then (1 : ℝ) else 0) * Y n k ω ^ 2) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [e2]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  have hτ0 : 0 ≤ σ2 * ∑ i, ∑ j, c i * c j * min (t i) (t j) := by
    obtain ⟨ω, hω⟩ := hwvar.exists
    exact ge_of_tendsto' hω fun n => div_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hfun : (fun (n : ℕ) ω => (√(r n : ℝ))⁻¹ *
      ∑ i, c i * ∑ k ∈ Finset.range ⌊(r n : ℝ) * t i⌋₊, Y n k ω) =
      fun (n : ℕ) ω => (√(r n : ℝ))⁻¹ * ∑ k ∈ Finset.range (r n), w n k * Y n k ω := by
    funext n ω; rw [hrep]
  rw [hfun]
  exact array_weighted_clt_rows hY hL2 h0 hC hbdd hmax hW hτ0 hwvar hZ

/-- The linear fidis of the normalised polygonal partial sums of a martingale-difference array
along rows `rᵢ → ∞`: if `(1/rᵢ) Σ_{k<⌊rᵢ tⱼ⌋} (Y i k)² → tⱼ` and `max_{k≤rᵢ} (Y i k)²/rᵢ → 0`
a.s. and `Σ_{k<rᵢ} E[(Y i k)²] ≤ C rᵢ`, then `fidiLin t c (polygonal rᵢ (rᵢ^{−1/2} Σ_{l<·} Y i l))`
converges in distribution to `fidiLin t c` under Wiener measure. -/
theorem array_fidiLin_polygonal_rows [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : ∀ i k, StronglyMeasurable[ℱ (k + 1)] (Y i k)) (hL2 : ∀ i k, MemLp (Y i k) 2 Q)
    (h0 : ∀ i k, Q[Y i k | ℱ k] =ᵐ[Q] 0) {r : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ i, ∑ k ∈ Finset.range (r i), ∫ ω, Y i k ω ^ 2 ∂Q ≤ C * r i)
    {K : ℕ} (t : Fin K → unitInterval) (c : Fin K → ℝ) (hr : Tendsto r atTop atTop)
    (hvt : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, Y i k ω ^ 2) / r i) atTop
      (𝓝 ((t j : ℝ) * 1)))
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, Y i k ω ^ 2 ≤ ε * r i) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (i : ℕ) ω => fidiLin t c
      (polygonal (r i) fun k => (√(r i : ℝ))⁻¹ * ∑ l ∈ Finset.range k, Y i l ω)) atTop
      (fidiLin t c) (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hYm : ∀ i k, Measurable (Y i k) := fun i k =>
    (hY i k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hZ : HasLaw (fidiLin t c) (gaussianReal 0
      (1 * ∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)).toNNReal) wienerMeasure := by
    rw [one_mul]
    exact ⟨(measurable_fidiLin t c).aemeasurable, wienerMeasure_fidiLin t c⟩
  have hX := array_fidi_clt_rows hY hL2 h0 hC hbdd (fun i => (t i : ℝ))
    (fun i => (t i).2.2) c hvt hmax hZ
  set s : ℕ → Ω → ℕ → ℝ := fun i ω k => (√(r i : ℝ))⁻¹ * ∑ l ∈ Finset.range k, Y i l ω
    with hs
  have hPm : ∀ i : ℕ, Measurable fun ω => fidiLin t c (polygonal (r i) (s i ω)) := fun i =>
    (measurable_fidiLin t c).comp (measurable_polygonal_comp (fun k =>
      measurable_const.mul (Finset.measurable_sum _ fun l _ => hYm i l)) (r i))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_ fun i => (hPm i).aemeasurable
  have hXm : ∀ i : ℕ, Measurable fun ω => (√(r i : ℝ))⁻¹ *
      ∑ j, c j * ∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, Y i k ω := fun i =>
    measurable_const.mul (Finset.measurable_sum _ fun j _ => measurable_const.mul
      (Finset.measurable_sum _ fun k _ => hYm i k))
  refine tendstoInMeasure_of_tendsto_ae (fun i =>
    ((hPm i).sub (hXm i)).aestronglyMeasurable) ?_
  filter_upwards [hmax] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  set W := ∑ i, |c i| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hε' : 0 < (ε / (2 * (W + 1))) ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hω _ hε').and (hr.eventually_ge_atTop 1))
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨hn1, hn2⟩ := hN i hi
  have hn0 : (0 : ℝ) < r i := by exact_mod_cast hn2
  have hsq : 0 < √(r i : ℝ) := Real.sqrt_pos.2 hn0
  rw [Real.dist_eq, Pi.zero_apply, sub_zero, Pi.sub_apply, Pi.sub_apply]
  have hb := abs_fidiLin_polygonal_sub_le t c (r i) (s i ω)
  have hrw : ∑ j, c j * s i ω ⌊(r i : ℝ) * (t j : ℝ)⌋₊ = (√(r i : ℝ))⁻¹ *
      ∑ j, c j * ∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, Y i k ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [hs]; ring
  rw [hrw] at hb
  have hinc : ∀ j, |s i ω (⌊(r i : ℝ) * (t j : ℝ)⌋₊ + 1) - s i ω ⌊(r i : ℝ) * (t j : ℝ)⌋₊| ≤
      ε / (2 * (W + 1)) := by
    intro j
    set m := ⌊(r i : ℝ) * (t j : ℝ)⌋₊
    have hm : m ≤ r i := floor_natCast_mul_le (r i) (t j)
    have e : s i ω (m + 1) - s i ω m = (√(r i : ℝ))⁻¹ * Y i m ω := by
      simp only [hs]; rw [Finset.sum_range_succ]; ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hsq), inv_mul_le_iff₀ hsq]
    have h1 := hn1 m hm
    have h2 : Y i m ω ^ 2 ≤ (ε / (2 * (W + 1)) * √(r i : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]; exact h1
    have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
    rw [abs_le]
    constructor <;> nlinarith [h3.1, h3.2]
  calc |fidiLin t c (polygonal (r i) (s i ω)) - (√(r i : ℝ))⁻¹ *
        ∑ j, c j * ∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, Y i k ω|
      ≤ ∑ j, |c j| * |s i ω (⌊(r i : ℝ) * (t j : ℝ)⌋₊ + 1) - s i ω ⌊(r i : ℝ) * (t j : ℝ)⌋₊| :=
        hb
    _ ≤ ∑ j, |c j| * (ε / (2 * (W + 1))) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hinc j) (abs_nonneg _)
    _ = W * (ε / (2 * (W + 1))) := by rw [← Finset.sum_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- The linear fidis of the normalised polygonal partial sums of a martingale-difference array
`Y n k` (row `n`), under convergence in probability: if `(1/n) Σ_{k<⌊n tⱼ⌋} (Y n k)² → tⱼ` and
`max_{k≤n} (Y n k)²/n → 0` in probability and `Σ_{k<n} E[(Y n k)²] ≤ C n`, then
`fidiLin t c (polygonal n (n^{−1/2} Σ_{l<·} Y n l)) ⇒ fidiLin t c` under Wiener measure. -/
theorem array_fidiLin_polygonal_of_tendstoInMeasure [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : ∀ n k, StronglyMeasurable[ℱ (k + 1)] (Y n k)) (hL2 : ∀ n k, MemLp (Y n k) 2 Q)
    (h0 : ∀ n k, Q[Y n k | ℱ k] =ᵐ[Q] 0) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, Y n k ω ^ 2 ∂Q ≤ C * n)
    {K : ℕ} (t : Fin K → unitInterval) (c : Fin K → ℝ)
    (hvt : ∀ j, TendstoInMeasure Q (fun (n : ℕ) ω =>
      (∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, Y n k ω ^ 2) / n - (t j : ℝ)) atTop 0)
    (hmax : TendstoInMeasure Q (fun (n : ℕ) ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => Y n k ω ^ 2) / n) atTop 0) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω => fidiLin t c
      (polygonal n fun k => (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range k, Y n l ω)) atTop
      (fidiLin t c) (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hYm : ∀ n k, Measurable (Y n k) := fun n k =>
    (hY n k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hPm : ∀ n : ℕ, Measurable fun ω => fidiLin t c
      (polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range k, Y n l ω)) := fun n =>
    (measurable_fidiLin t c).comp (measurable_polygonal_comp (fun k =>
      measurable_const.mul (Finset.measurable_sum _ fun l _ => hYm n l)) n)
  refine ⟨fun n => (hPm n).aemeasurable, (measurable_fidiLin t c).aemeasurable, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  set F : Option (Fin K) → ℕ → Ω → ℝ := fun o => Option.elim o
    (fun n ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => Y n k ω ^ 2) / n)
    (fun j n ω => (∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊, Y n k ω ^ 2) / n - (t j : ℝ))
    with hF
  have hFm : ∀ o, TendstoInMeasure Q (F o) atTop 0 := by
    intro o
    cases o with
    | none => exact hmax
    | some j => exact hvt j
  have hFns : ∀ o, TendstoInMeasure Q (fun i => F o (ns i)) atTop 0 := fun o ε hε =>
    ((hFm o) ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_zero hFns
  set r : ℕ → ℕ := fun i => ns (ms i) with hr
  have hrt : Tendsto r atTop atTop := hns.comp hms.tendsto_atTop
  have hvt' : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, Y (r i) k ω ^ 2) / r i) atTop
      (𝓝 ((t j : ℝ) * 1)) := by
    intro j
    filter_upwards [hae] with ω hω
    have h1 := (hω (some j)).add_const (t j : ℝ)
    rw [zero_add, ← mul_one (t j : ℝ)] at h1
    refine h1.congr fun i => ?_
    simp only [hF, Option.elim]
    ring
  have hmax' : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, Y (r i) k ω ^ 2 ≤ ε * r i := by
    filter_upwards [hae] with ω hω ε hε
    have h1 := (hω none).eventually (gt_mem_nhds hε)
    filter_upwards [h1, hrt.eventually_ge_atTop 1] with i hi hi1 k hk
    simp only [hF, Option.elim] at hi
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast hi1
    rw [div_lt_iff₀ hn0] at hi
    exact (Finset.le_sup' (fun k => Y (r i) k ω ^ 2)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))).trans hi.le
  exact ⟨ms, (array_fidiLin_polygonal_rows (Y := fun i => Y (r i)) (fun i => hY (r i))
    (fun i => hL2 (r i)) (fun i => h0 (r i)) hC (fun i => hbdd (r i)) t c hrt hvt'
    hmax').tendsto⟩

/-! ### Localisation by a predictable clock; Lenglart's inequality -/

/-- `E[F W] = E[F E[W | 𝓜]]` for `𝓜`-measurable `F`. -/
theorem integral_mul_eq_integral_mul_condExp {Q : Measure Ω} [IsFiniteMeasure Q]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {F W : Ω → ℝ} (hF : StronglyMeasurable[m] F)
    (hFW : Integrable (fun ω => F ω * W ω) Q) (hW : Integrable W Q) :
    ∫ ω, F ω * W ω ∂Q = ∫ ω, F ω * Q[W | m] ω ∂Q := by
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  exact condExp_mul_of_stronglyMeasurable_left hF hFW hW

/-- The predictable localisation weight `1{Σ_{j≤k} E[Wⱼ | 𝓕ⱼ] ≤ c}`. -/
noncomputable def locWeight (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (c : ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  if ∑ j ∈ Finset.range (k + 1), Q[W j | ℱ j] ω ≤ c then 1 else 0

/-- The localisation weight is `𝓕ₖ`-measurable. -/
theorem stronglyMeasurable_locWeight (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ)
    (c : ℝ) (k : ℕ) : StronglyMeasurable[ℱ k] (locWeight Q ℱ W c k) := by
  have h : Measurable[ℱ k] fun ω => ∑ j ∈ Finset.range (k + 1), Q[W j | ℱ j] ω :=
    Finset.measurable_sum _ fun j hj => (stronglyMeasurable_condExp.measurable).mono
      (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) le_rfl
  exact (Measurable.ite (measurableSet_le h measurable_const) measurable_const
    measurable_const).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- The pathwise arithmetic of the localisation: if `qⱼ ≥ 0` and `aₖ = 1{Σ_{j≤k} qⱼ ≤ c}`, then
`Σ_{k<n} aₖ qₖ ≤ c`, and all `aₖ = 1` (`k < n`) when `Σ_{j<n} qⱼ ≤ c`. -/
theorem sum_ite_mul_le {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, (if ∑ j ∈ Finset.range (k + 1), q j ≤ c then (1 : ℝ) else 0) * q k
      ≤ c := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases h : ∑ j ∈ Finset.range (n + 1), q j ≤ c
    · have hall : ∀ k ∈ Finset.range (n + 1),
          (if ∑ j ∈ Finset.range (k + 1), q j ≤ c then (1 : ℝ) else 0) = 1 := by
        intro k hk
        have : ∑ j ∈ Finset.range (k + 1), q j ≤ c :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
            (Nat.succ_le_of_lt (Finset.mem_range.1 hk))) fun j _ _ => hq j).trans h
        simp [this]
      rw [← Finset.sum_range_succ (fun k => (if ∑ j ∈ Finset.range (k + 1), q j ≤ c then
        (1 : ℝ) else 0) * q k) n, Finset.sum_congr rfl fun k hk => by rw [hall k hk, one_mul]]
      exact h
    · simp only [h, ite_false, zero_mul, add_zero]
      exact ih

omit [MeasurableSpace Ω] in
/-- If `Σ_{j<n} qⱼ ≤ c` with `qⱼ ≥ 0`, all weights `1{Σ_{j≤k} qⱼ ≤ c}`, `k < n`, are `1`. -/
theorem ite_sum_le_eq_one {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) {c : ℝ} {n : ℕ}
    (h : ∑ j ∈ Finset.range n, q j ≤ c) {k : ℕ} (hk : k < n) :
    (if ∑ j ∈ Finset.range (k + 1), q j ≤ c then (1 : ℝ) else 0) = 1 := by
  have : ∑ j ∈ Finset.range (k + 1), q j ≤ c :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
      fun j _ _ => hq j).trans h
  simp [this]

/-- **The localised first moment**: for nonnegative integrable `Wₖ` (`𝓕ₖ₊₁`-measurable),
`Σ_{k<n} E[aₖ Wₖ] ≤ c` for the localisation weights `aₖ = 1{Σ_{j≤k} E[Wⱼ | 𝓕ⱼ] ≤ c}`. -/
theorem sum_integral_locWeight_mul_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {W : ℕ → Ω → ℝ} (hWi : ∀ k, Integrable (W k) Q)
    (hW0 : ∀ k, ∀ᵐ ω ∂Q, 0 ≤ W k ω) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫ ω, locWeight Q ℱ W c k ω * W k ω ∂Q ≤ c := by
  have hab : ∀ k ω, |locWeight Q ℱ W c k ω| ≤ 1 := fun k ω => by
    unfold locWeight; split_ifs <;> simp
  have hint : ∀ k, Integrable (fun ω => locWeight Q ℱ W c k ω * W k ω) Q := fun k =>
    (hWi k).bdd_mul ((stronglyMeasurable_locWeight Q ℱ W c k).mono (ℱ.le k)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hab k ω)
  have e : ∀ k, ∫ ω, locWeight Q ℱ W c k ω * W k ω ∂Q =
      ∫ ω, locWeight Q ℱ W c k ω * Q[W k | ℱ k] ω ∂Q := fun k =>
    integral_mul_eq_integral_mul_condExp (ℱ.le k) (stronglyMeasurable_locWeight Q ℱ W c k)
      (hint k) (hWi k)
  simp_rw [e]
  have hint' : ∀ k, Integrable (fun ω => locWeight Q ℱ W c k ω * Q[W k | ℱ k] ω) Q := fun k =>
    integrable_condExp.bdd_mul
      ((stronglyMeasurable_locWeight Q ℱ W c k).mono (ℱ.le k)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hab k ω)
  rw [← integral_finsetSum _ fun k _ => hint' k]
  have hpos : ∀ᵐ ω ∂Q, ∀ j, 0 ≤ Q[W j | ℱ j] ω :=
    ae_all_iff.2 fun j => (condExp_nonneg (hW0 j)).mono fun ω h => by simpa using h
  calc ∫ ω, ∑ k ∈ Finset.range n, locWeight Q ℱ W c k ω * Q[W k | ℱ k] ω ∂Q ≤ ∫ _, c ∂Q :=
        integral_mono_ae (integrable_finsetSum _ fun k _ => hint' k) (integrable_const c)
          (hpos.mono fun ω hω => sum_ite_mul_le hω hc n)
    _ = c := by simp

/-- **Lenglart's inequality** (the form used here): for nonnegative integrable `Xₖ`
(`𝓕ₖ₊₁`-measurable), `a > 0` and `c ≥ 0`,
`P(Σ_{k<n} Xₖ ≥ a) ≤ c/a + P(Σ_{k<n} E[Xₖ | 𝓕ₖ] > c)`. -/
theorem measureReal_sum_ge_le_lenglart {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} (hX : ∀ k, StronglyMeasurable[ℱ (k + 1)] (X k))
    (hXi : ∀ k, Integrable (X k) Q) (hX0 : ∀ k ω, 0 ≤ X k ω) (n : ℕ) {a c : ℝ} (ha : 0 < a)
    (hc : 0 ≤ c) :
    Q.real {ω | a ≤ ∑ k ∈ Finset.range n, X k ω} ≤
      c / a + Q.real {ω | c < ∑ k ∈ Finset.range n, Q[X k | ℱ k] ω} := by
  set w := locWeight Q ℱ X c with hw
  have hXm : ∀ k, Measurable (X k) := fun k => (hX k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (stronglyMeasurable_locWeight Q ℱ X c k).measurable.mono (ℱ.le k) le_rfl
  have hw01 : ∀ k ω, 0 ≤ w k ω ∧ w k ω ≤ 1 := fun k ω => by
    simp only [hw, locWeight]; split_ifs <;> norm_num
  have hY0 : ∀ ω, 0 ≤ ∑ k ∈ Finset.range n, w k ω * X k ω := fun ω =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hw01 k ω).1 (hX0 k ω)
  have hYi : Integrable (fun ω => ∑ k ∈ Finset.range n, w k ω * X k ω) Q :=
    integrable_finsetSum _ fun k _ => (hXi k).bdd_mul (hwm k).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw01 k ω).1]; exact (hw01 k ω).2)
  have hE : ∫ ω, ∑ k ∈ Finset.range n, w k ω * X k ω ∂Q ≤ c := by
    rw [integral_finsetSum _ fun k _ => (hXi k).bdd_mul (hwm k).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw01 k ω).1]; exact (hw01 k ω).2)]
    exact sum_integral_locWeight_mul_le hXi (fun k => Eventually.of_forall (hX0 k)) hc n
  have hmarkov : a * Q.real {ω | a ≤ ∑ k ∈ Finset.range n, w k ω * X k ω} ≤ c :=
    (mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hY0) hYi a).trans hE
  have hpos : ∀ᵐ ω ∂Q, ∀ j, 0 ≤ Q[X j | ℱ j] ω :=
    ae_all_iff.2 fun j => (condExp_nonneg (Eventually.of_forall (hX0 j))).mono fun ω h => by
      simpa using h
  have hsub : {ω | a ≤ ∑ k ∈ Finset.range n, X k ω} ≤ᵐ[Q]
      ({ω | a ≤ ∑ k ∈ Finset.range n, w k ω * X k ω} ∪
        {ω | c < ∑ k ∈ Finset.range n, Q[X k | ℱ k] ω} : Set Ω) := by
    filter_upwards [hpos] with ω hω h
    by_cases hc' : c < ∑ k ∈ Finset.range n, Q[X k | ℱ k] ω
    · exact Or.inr hc'
    · left
      push Not at hc'
      simp only [mem_ofPred_eq]
      rw [Finset.sum_congr rfl fun k hk => by
        simp only [hw, locWeight]
        rw [ite_sum_le_eq_one hω hc' (Finset.mem_range.1 hk), one_mul]]
      exact h
  have h1 : Q.real {ω | a ≤ ∑ k ∈ Finset.range n, X k ω} ≤
      Q.real ({ω | a ≤ ∑ k ∈ Finset.range n, w k ω * X k ω} ∪
        {ω | c < ∑ k ∈ Finset.range n, Q[X k | ℱ k] ω}) :=
    ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono_ae hsub)
  have h2 := measureReal_union_le (μ := Q) {ω | a ≤ ∑ k ∈ Finset.range n, w k ω * X k ω}
    {ω | c < ∑ k ∈ Finset.range n, Q[X k | ℱ k] ω}
  have h3 : Q.real {ω | a ≤ ∑ k ∈ Finset.range n, w k ω * X k ω} ≤ c / a := by
    rw [le_div_iff₀ ha, mul_comm]; exact hmarkov
  linarith

/-! ### A uniform law for the conditional-variance clock -/

/-- **Uniformity of the clock** (Pólya): if `uₖ ≥ 0` and `(1/n) Σ_{k<n} uₖ → 1`, then for every
`θ > 0` eventually `|Σ_{k<j} uₖ − j| ≤ θ n` for all `j ≤ n`. -/
theorem eventually_abs_sum_sub_le {u : ℕ → ℝ} (hu0 : ∀ k, 0 ≤ u k)
    (hu : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u k) / n) atTop (𝓝 1)) {θ : ℝ}
    (hθ : 0 < θ) : ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, |∑ k ∈ Finset.range j, u k - j| ≤ θ * n := by
  set f : ℕ → ℝ := fun j => ∑ k ∈ Finset.range j, u k with hf
  have hfmono : Monotone f := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab) fun k _ _ => hu0 k
  obtain ⟨M, hM⟩ := exists_nat_gt (3 / θ)
  have hM0 : (0 : ℝ) < M := (by positivity : (0 : ℝ) < 3 / θ).trans hM
  have hMθ : 1 / (M : ℝ) < θ / 3 := by
    rw [div_lt_iff₀ hM0]; rw [div_lt_iff₀ hθ] at hM; linarith
  have hgrid : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range (M + 1),
      |f ⌊(n : ℝ) * ((i : ℝ) / M)⌋₊ / n - (i : ℝ) / M| < θ / 3 := by
    rw [Finset.eventually_all]
    intro i _
    have h := tendsto_sum_floor_div hu (show (0 : ℝ) ≤ (i : ℝ) / M by positivity)
    rw [mul_one] at h
    filter_upwards [h.eventually (Metric.ball_mem_nhds _ (show 0 < θ / 3 by positivity))]
      with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (3 / θ)
  filter_upwards [hgrid, eventually_ge_atTop (N₀ + 1)] with n hn hnN j hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnθ : 1 / (n : ℝ) < θ / 3 := by
    have : (N₀ : ℝ) + 1 ≤ n := by exact_mod_cast hnN
    rw [div_lt_iff₀ hn0]; rw [div_lt_iff₀ hθ] at hN₀; nlinarith
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  set i := ⌊(j : ℝ) * M / n⌋₊ with hi
  have hiM : i ≤ M := Nat.floor_le_of_le (by
    rw [div_le_iff₀ hn0]; nlinarith)
  have hil : (i : ℝ) ≤ (j : ℝ) * M / n := Nat.floor_le (by positivity)
  have hiu : (j : ℝ) * M / n < i + 1 := Nat.lt_floor_add_one _
  -- the lower grid point
  set a := ⌊(n : ℝ) * ((i : ℝ) / M)⌋₊ with ha
  have haj : a ≤ j := Nat.floor_le_of_le (by
    rw [mul_div_assoc', div_le_iff₀ hM0]; rw [le_div_iff₀ hn0] at hil; linarith)
  have hal : (n : ℝ) * ((i : ℝ) / M) - 1 < a := by
    have := Nat.lt_floor_add_one ((n : ℝ) * ((i : ℝ) / M)); linarith
  -- the upper grid point
  set i' := min (i + 1) M with hi'
  set b := ⌊(n : ℝ) * ((i' : ℝ) / M)⌋₊ with hb
  have hjb : j ≤ b := by
    refine Nat.le_floor ?_
    rcases le_or_gt (i + 1) M with h | h
    · have : i' = i + 1 := min_eq_left h
      rw [this]; push_cast
      rw [mul_div_assoc', le_div_iff₀ hM0]
      rw [div_lt_iff₀ hn0] at hiu; linarith
    · have : i' = M := min_eq_right h.le
      rw [this, div_self hM0.ne', mul_one]; exact hjn
  have hbu : (b : ℝ) ≤ (n : ℝ) * ((i + 1 : ℝ) / M) := by
    refine (Nat.floor_le (by positivity)).trans ?_
    gcongr
    exact_mod_cast min_le_left _ _
  have hga := hn i (Finset.mem_range.2 (Nat.lt_succ_of_le hiM))
  have hgb := hn i' (Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _)))
  have hfa := hfmono haj
  have hfb := hfmono hjb
  have hi'le : (i' : ℝ) ≤ i + 1 := by exact_mod_cast min_le_left _ _
  have e1 : (f a / n - (i : ℝ) / M) * n = f a - n * ((i : ℝ) / M) := by field_simp
  have e2 : (f b / n - (i' : ℝ) / M) * n = f b - n * ((i' : ℝ) / M) := by field_simp
  have ga1 : -(θ / 3) * n < f a - n * ((i : ℝ) / M) := by
    have := mul_lt_mul_of_pos_right (abs_lt.1 hga).1 hn0; rw [e1] at this; linarith
  have gb2 : f b - n * ((i' : ℝ) / M) < θ / 3 * n := by
    have := mul_lt_mul_of_pos_right (abs_lt.1 hgb).2 hn0; rw [e2] at this; linarith
  have h4 : (n : ℝ) * (1 / M) ≤ n * (θ / 3) := mul_le_mul_of_nonneg_left hMθ.le hn0.le
  have hθn : 0 ≤ θ * n := by positivity
  rw [show ∑ k ∈ Finset.range j, u k = f j from rfl, abs_le]
  constructor
  · have h2 : (j : ℝ) ≤ n * ((i + 1 : ℝ) / M) := (by exact_mod_cast hjb : (j : ℝ) ≤ b).trans hbu
    have h3 : (n : ℝ) * ((i + 1 : ℝ) / M) = n * ((i : ℝ) / M) + n * (1 / M) := by ring
    have : f a ≤ f j := hfa
    linarith
  · have h3 : (n : ℝ) * ((i' : ℝ) / M) ≤ n * ((i : ℝ) / M) + n * (1 / M) := by
      rw [← mul_add]; gcongr; rw [← add_div]; gcongr
    have h5 : (1 : ℝ) ≤ n * (θ / 3) := by
      rw [div_lt_iff₀ hn0] at hnθ; linarith
    have h6 : (n : ℝ) * ((i : ℝ) / M) - 1 < j := hal.trans_le (by exact_mod_cast haj)
    have : f j ≤ f b := hfb
    linarith

/-! ### Convergence in probability -/

/-- Convergence in probability to `0`, in terms of real measures. -/
theorem tendsto_measureReal_of_tendstoInMeasure {Q : Measure Ω} [IsFiniteMeasure Q]
    {f : ℕ → Ω → ℝ} (h : TendstoInMeasure Q f atTop 0) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n => Q.real {ω | κ ≤ |f n ω|}) atTop (𝓝 0) := by
  have h1 := (tendstoInMeasure_iff_norm.1 h) κ hκ
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [ENNReal.toReal_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
  rfl

/-- Almost sure convergence to `0` gives `P(|fₙ| ≥ κ) → 0`. -/
theorem tendsto_measureReal_of_ae_tendsto {Q : Measure Ω} [IsFiniteMeasure Q]
    {f : ℕ → Ω → ℝ} (hfm : ∀ n, Measurable (f n))
    (h : ∀ᵐ ω ∂Q, Tendsto (fun n => f n ω) atTop (𝓝 0)) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n => Q.real {ω | κ ≤ |f n ω|}) atTop (𝓝 0) :=
  tendsto_measureReal_of_tendstoInMeasure
    (tendstoInMeasure_of_tendsto_ae (fun n => (hfm n).aestronglyMeasurable) h) hκ

/-! ### Large increments under the conditional Lindeberg condition -/

/-- The large part `Dₖ² 1{Dₖ² ≥ a}` of `Dₖ²`. -/
noncomputable def bigSq (D : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  {ω | a ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω

omit [MeasurableSpace Ω] in
/-- `0 ≤ Dₖ² 1{Dₖ² ≥ a} ≤ Dₖ²`. -/
theorem bigSq_nonneg_le (D : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ bigSq D a k ω ∧ bigSq D a k ω ≤ D k ω ^ 2 :=
  ⟨Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω,
    Set.indicator_le_self' (fun _ _ => sq_nonneg _) ω⟩

/-- `bigSq` is `𝓕ₖ₊₁`-measurable and integrable. -/
theorem bigSq_props {Q : Measure Ω} {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) (hL2 : ∀ k, MemLp (D k) 2 Q) (a : ℝ)
    (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] (bigSq D a k) ∧ Integrable (bigSq D a k) Q := by
  have hDk : Measurable[ℱ (k + 1)] (D k) := (hD k).measurable
  refine ⟨((hDk.pow_const 2).indicator (measurableSet_le measurable_const
    (hDk.pow_const 2))).stronglyMeasurable, ?_⟩
  exact (hL2 k).integrable_sq.indicator (measurableSet_le measurable_const
    (((hD k).measurable.mono (ℱ.le (k + 1)) le_rfl).pow_const 2))

/-- **No large increments** (from (D.9) by Lenglart's inequality):
`P(∃ k < n, Dₖ² ≥ εn) → 0`. -/
theorem tendsto_measureReal_exists_big {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) {ε : ℝ} (hε : 0 < ε)
    (hlin : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Q.real {ω | ∃ k < n, ε * n ≤ D k ω ^ 2}) atTop (𝓝 0) := by
  have hLm : ∀ n : ℕ, Measurable fun ω =>
      (∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω) / n := fun n =>
    (Finset.measurable_sum _ fun k _ => (stronglyMeasurable_condExp.measurable).mono
      (ℱ.le k) le_rfl).div_const _
  rw [Metric.tendsto_atTop]
  intro κ hκ
  have hκ' : 0 < κ / 3 := by positivity
  have hlim := tendsto_measureReal_of_ae_tendsto hLm hlin (show 0 < κ / 3 * ε by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (κ / 3) hκ'
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNn := hN n (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hNn ⊢
  have hsub : {ω | ∃ k < n, ε * n ≤ D k ω ^ 2} ⊆
      {ω | ε * n ≤ ∑ k ∈ Finset.range n, bigSq D (ε * n) k ω} := by
    rintro ω ⟨k, hk, hbig⟩
    simp only [mem_ofPred_eq]
    have h1 : bigSq D (ε * n) k ω = D k ω ^ 2 := by
      simp only [bigSq]; rw [Set.indicator_of_mem (show ω ∈ {ω | ε * n ≤ D k ω ^ 2} from hbig)]
    calc ε * n ≤ bigSq D (ε * n) k ω := h1 ▸ hbig
      _ ≤ _ := Finset.single_le_sum (f := fun k => bigSq D (ε * n) k ω)
          (fun j _ => (bigSq_nonneg_le D _ j ω).1) (Finset.mem_range.2 hk)
  have hL := measureReal_sum_ge_le_lenglart (Q := Q) (ℱ := ℱ) (X := fun k => bigSq D (ε * n) k)
    (fun k => (bigSq_props hD hL2 _ k).1) (fun k => (bigSq_props hD hL2 _ k).2)
    (fun k ω => (bigSq_nonneg_le D _ k ω).1) n (show 0 < ε * n by positivity)
    (show 0 ≤ κ / 3 * ε * n by positivity)
  have hset : {ω | κ / 3 * ε * n < ∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω} ⊆
      {ω | κ / 3 * ε ≤ |(∑ k ∈ Finset.range n, Q[bigSq D (ε * n) k | ℱ k] ω) / n|} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    refine le_trans ?_ (le_abs_self _)
    rw [le_div_iff₀ hn0]; exact hω.le
  have h2 : κ / 3 * ε * n / (ε * n) = κ / 3 := by field_simp
  rw [h2] at hL
  calc Q.real {ω | ∃ k < n, ε * n ≤ D k ω ^ 2}
      ≤ Q.real {ω | ε * n ≤ ∑ k ∈ Finset.range n, bigSq D (ε * n) k ω} := measureReal_mono hsub
    _ ≤ κ / 3 + κ / 3 := hL.trans (add_le_add le_rfl ((measureReal_mono hset).trans hNn.le))
    _ < κ := by linarith

/-! ### A fourth-moment bound through the conditional-variance clock -/

/-- **The fourth moment of a bounded martingale with a bounded clock**: for martingale differences
`|dᵢ| ≤ b` with `Σ_{i<m} E[dᵢ² | 𝓖ᵢ] ≤ c` a.s., `E[(Σ_{i<m} dᵢ)⁴] ≤ 8c² + 3b²c`. -/
theorem integral_pow_four_sum_le_clock {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝒢 : Filtration ℕ mΩ} {d : ℕ → Ω → ℝ} (hd : ∀ i, StronglyMeasurable[𝒢 (i + 1)] (d i))
    (h0 : ∀ i, Q[d i | 𝒢 i] =ᵐ[Q] 0) {b : ℝ} (hb : ∀ i, ∀ᵐ ω ∂Q, |d i ω| ≤ b) (m : ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (hclock : ∀ᵐ ω ∂Q, ∑ i ∈ Finset.range m, Q[fun ω => d i ω ^ 2 | 𝒢 i] ω ≤ c) :
    ∫ ω, (∑ i ∈ Finset.range m, d i ω) ^ 4 ∂Q ≤ 8 * c ^ 2 + 3 * b ^ 2 * c := by
  have hdm : ∀ i, Measurable (d i) := fun i => (hd i).measurable.mono (𝒢.le (i + 1)) le_rfl
  have hall : ∀ᵐ ω ∂Q, ∀ i, |d i ω| ≤ b := ae_all_iff.2 hb
  have hb0 : 0 ≤ b := by obtain ⟨ω, hω⟩ := (hb 0).exists; exact (abs_nonneg _).trans hω
  -- notation
  set S : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range j, d i ω with hS
  set v : ℕ → Ω → ℝ := fun i => Q[fun ω => d i ω ^ 2 | 𝒢 i] with hv
  set A : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range j, v i ω with hA
  have hint : ∀ f : Ω → ℝ, AEStronglyMeasurable f Q → ∀ C : ℝ, (∀ᵐ ω ∂Q, |f ω| ≤ C) →
      Integrable f Q := fun f hf C hC =>
    Integrable.of_bound hf C (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hSF : ∀ j, StronglyMeasurable[𝒢 j] (S j) := fun j => by
    refine (Finset.measurable_sum _ fun i hi => ?_).stronglyMeasurable
    exact (hd i).measurable.mono (𝒢.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) le_rfl
  have hSm : ∀ j, Measurable (S j) := fun j => (hSF j).measurable.mono (𝒢.le j) le_rfl
  have hSb : ∀ j, ∀ᵐ ω ∂Q, |S j ω| ≤ j * b := fun j => by
    filter_upwards [hall] with ω hω
    calc |S j ω| ≤ ∑ i ∈ Finset.range j, |d i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, b := Finset.sum_le_sum fun i _ => hω i
      _ = j * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hd2i : ∀ i, Integrable (fun ω => d i ω ^ 2) Q := fun i =>
    hint _ ((hdm i).pow_const 2).aestronglyMeasurable (b ^ 2) ((hb i).mono fun ω h => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  have hvF : ∀ i, StronglyMeasurable[𝒢 i] (v i) := fun i => stronglyMeasurable_condExp
  have hvm : ∀ i, Measurable (v i) := fun i => (hvF i).measurable.mono (𝒢.le i) le_rfl
  have hv0 : ∀ i, ∀ᵐ ω ∂Q, 0 ≤ v i ω := fun i =>
    (condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (d i ω))).mono fun ω h => by
      simpa using h
  have hvb : ∀ i, ∀ᵐ ω ∂Q, |v i ω| ≤ b ^ 2 := fun i =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := 𝒢 i) (R := b ^ 2)
      ((hb i).mono fun ω h => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  have hvi : ∀ i, Integrable (v i) Q := fun i => integrable_condExp
  have hAF : ∀ j, StronglyMeasurable[𝒢 j] (A (j + 1)) := fun j => by
    refine (Finset.measurable_sum _ fun i hi => ?_).stronglyMeasurable
    exact (hvF i).measurable.mono (𝒢.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) le_rfl
  have hAm : ∀ j, Measurable (A j) := fun j => Finset.measurable_sum _ fun i _ => hvm i
  have hAb : ∀ j, ∀ᵐ ω ∂Q, |A j ω| ≤ j * b ^ 2 := fun j => by
    filter_upwards [ae_all_iff.2 hvb] with ω hω
    calc |A j ω| ≤ ∑ i ∈ Finset.range j, |v i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, b ^ 2 := Finset.sum_le_sum fun i _ => hω i
      _ = j * b ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hA0 : ∀ j, ∀ᵐ ω ∂Q, 0 ≤ A j ω := fun j => by
    filter_upwards [ae_all_iff.2 hv0] with ω hω
    exact Finset.sum_nonneg fun i _ => hω i
  have hAi : ∀ j, Integrable (A j) Q := fun j => integrable_finsetSum _ fun i _ => hvi i
  -- second moments
  have hdL2 : ∀ i, MemLp (d i) 2 Q := fun i =>
    MemLp.of_bound (hdm i).aestronglyMeasurable b ((hb i).mono fun ω h => by
      rwa [Real.norm_eq_abs])
  have hEv : ∀ i, ∫ ω, d i ω ^ 2 ∂Q = ∫ ω, v i ω ∂Q := fun i =>
    (integral_condExp (𝒢.le i)).symm
  have hS2 : ∫ ω, S m ω ^ 2 ∂Q = ∫ ω, A m ω ∂Q := by
    rw [hS, integral_sq_sum_of_martingale hd hdL2 h0 m, hA,
      integral_finsetSum _ fun i _ => hvi i]
    exact Finset.sum_congr rfl fun i _ => hEv i
  have hAmc : ∫ ω, A m ω ∂Q ≤ c := by
    calc ∫ ω, A m ω ∂Q ≤ ∫ _, c ∂Q := integral_mono_ae (hAi m) (integrable_const c) hclock
      _ = c := by simp
  -- integrability of the products
  have iS4 : ∀ j, Integrable (fun ω => S j ω ^ 4) Q := fun j =>
    hint _ ((hSm j).pow_const 4).aestronglyMeasurable ((j * b) ^ 4) ((hSb j).mono fun ω h => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
  have iS3d : ∀ j, Integrable (fun ω => S j ω ^ 3 * d j ω) Q := fun j =>
    hint _ (((hSm j).pow_const 3).mul (hdm j)).aestronglyMeasurable ((j * b) ^ 3 * b)
      (by filter_upwards [hSb j, hb j] with ω h1 h2
          rw [abs_mul, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 3) h2 (abs_nonneg _)
            (by positivity))
  have iS2d2 : ∀ j, Integrable (fun ω => S j ω ^ 2 * d j ω ^ 2) Q := fun j =>
    hint _ (((hSm j).pow_const 2).mul ((hdm j).pow_const 2)).aestronglyMeasurable
      ((j * b) ^ 2 * b ^ 2)
      (by filter_upwards [hSb j, hb j] with ω h1 h2
          rw [abs_mul, abs_pow, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2)
            (pow_le_pow_left₀ (abs_nonneg _) h2 2) (by positivity) (by positivity))
  have iS2v : ∀ j, Integrable (fun ω => S j ω ^ 2 * v j ω) Q := fun j =>
    hint _ (((hSm j).pow_const 2).mul (hvm j)).aestronglyMeasurable ((j * b) ^ 2 * b ^ 2)
      (by filter_upwards [hSb j, hvb j] with ω h1 h2
          rw [abs_mul, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) h2 (abs_nonneg _)
            (by positivity))
  have id4 : ∀ j, Integrable (fun ω => d j ω ^ 4) Q := fun j =>
    hint _ ((hdm j).pow_const 4).aestronglyMeasurable (b ^ 4) ((hb j).mono fun ω h => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 4)
  -- the recursion
  have hstep : ∀ j, ∫ ω, S (j + 1) ω ^ 4 ∂Q ≤ ∫ ω, S j ω ^ 4 ∂Q +
      8 * ∫ ω, S j ω ^ 2 * v j ω ∂Q + 3 * b ^ 2 * ∫ ω, v j ω ∂Q := by
    intro j
    have hcross : ∫ ω, S j ω ^ 3 * d j ω ∂Q = 0 :=
      integral_mul_eq_zero_of_condExp (𝒢.le j) ((hSF j).pow 3) (iS3d j)
        ((hdL2 j).integrable one_le_two) (h0 j)
    have hpull : ∫ ω, S j ω ^ 2 * d j ω ^ 2 ∂Q = ∫ ω, S j ω ^ 2 * v j ω ∂Q :=
      integral_mul_eq_integral_mul_condExp (𝒢.le j) ((hSF j).pow 2) (iS2d2 j) (hd2i j)
    have h4 : ∫ ω, d j ω ^ 4 ∂Q ≤ b ^ 2 * ∫ ω, v j ω ∂Q := by
      rw [← hEv j, ← integral_const_mul]
      refine integral_mono_ae (id4 j) ((hd2i j).const_mul _) ?_
      filter_upwards [hb j] with ω hω
      have : d j ω ^ 2 ≤ b ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      have e : d j ω ^ 4 = d j ω ^ 2 * d j ω ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hpt : ∀ ω, S (j + 1) ω ^ 4 ≤ S j ω ^ 4 + 4 * (S j ω ^ 3 * d j ω) +
        (8 * (S j ω ^ 2 * d j ω ^ 2) + 3 * d j ω ^ 4) := by
      intro ω
      have hS1 : S (j + 1) ω = S j ω + d j ω := by simp only [hS]; rw [Finset.sum_range_succ]
      rw [hS1]
      nlinarith [sq_nonneg (S j ω * d j ω - d j ω ^ 2)]
    have iR : Integrable (fun ω => 8 * (S j ω ^ 2 * d j ω ^ 2) + 3 * d j ω ^ 4) Q :=
      ((iS2d2 j).const_mul _).add ((id4 j).const_mul _)
    calc ∫ ω, S (j + 1) ω ^ 4 ∂Q
        ≤ ∫ ω, (S j ω ^ 4 + 4 * (S j ω ^ 3 * d j ω) +
          (8 * (S j ω ^ 2 * d j ω ^ 2) + 3 * d j ω ^ 4)) ∂Q :=
          integral_mono (iS4 (j + 1)) (((iS4 j).add ((iS3d j).const_mul 4)).add iR) hpt
      _ = ∫ ω, S j ω ^ 4 ∂Q + 4 * ∫ ω, S j ω ^ 3 * d j ω ∂Q +
          (8 * ∫ ω, S j ω ^ 2 * d j ω ^ 2 ∂Q + 3 * ∫ ω, d j ω ^ 4 ∂Q) := by
          rw [integral_add (f := fun ω => S j ω ^ 4 + 4 * (S j ω ^ 3 * d j ω))
            (g := fun ω => 8 * (S j ω ^ 2 * d j ω ^ 2) + 3 * d j ω ^ 4)
            ((iS4 j).add ((iS3d j).const_mul 4)) iR,
            integral_add (f := fun ω => S j ω ^ 4) (g := fun ω => 4 * (S j ω ^ 3 * d j ω))
              (iS4 j) ((iS3d j).const_mul 4), integral_const_mul,
            integral_add (f := fun ω => 8 * (S j ω ^ 2 * d j ω ^ 2))
              (g := fun ω => 3 * d j ω ^ 4) ((iS2d2 j).const_mul _) ((id4 j).const_mul _),
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by rw [hcross, hpull]; nlinarith [h4]
  have hsum4 : ∀ m' : ℕ, ∫ ω, S m' ω ^ 4 ∂Q ≤
      8 * ∑ j ∈ Finset.range m', ∫ ω, S j ω ^ 2 * v j ω ∂Q +
      3 * b ^ 2 * ∑ j ∈ Finset.range m', ∫ ω, v j ω ∂Q := by
    intro m'
    induction m' with
    | zero => simp [hS]
    | succ m' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := hstep m'
      linarith
  -- summation by parts: `Σ E[Sⱼ² vⱼ] ≤ E[Sₘ² Aₘ]`
  have hparts : ∀ (m' : ℕ) ω, ∑ j ∈ Finset.range m', S j ω ^ 2 * v j ω = S m' ω ^ 2 * A m' ω -
      ∑ j ∈ Finset.range m', A (j + 1) ω * (S (j + 1) ω ^ 2 - S j ω ^ 2) := by
    intro m' ω
    induction m' with
    | zero => simp [hS, hA]
    | succ m' ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have e1 : A (m' + 1) ω = A m' ω + v m' ω := by
        simp only [hA]; rw [Finset.sum_range_succ]
      rw [e1]
      ring
  have iAS : ∀ j, Integrable (fun ω => A (j + 1) ω * (S (j + 1) ω ^ 2 - S j ω ^ 2)) Q := fun j =>
    hint _ ((hAm (j + 1)).mul (((hSm (j + 1)).pow_const 2).sub
      ((hSm j).pow_const 2))).aestronglyMeasurable
      (((j + 1 : ℕ) * b ^ 2) * (((j + 1 : ℕ) * b) ^ 2 + (j * b) ^ 2))
      (by filter_upwards [hAb (j + 1), hSb (j + 1), hSb j] with ω h1 h2 h3
          rw [abs_mul]
          refine mul_le_mul h1 ((abs_sub _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
            (by positivity)
          · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
          · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2)
  have hnonneg : ∀ j, 0 ≤ ∫ ω, A (j + 1) ω * (S (j + 1) ω ^ 2 - S j ω ^ 2) ∂Q := by
    intro j
    have iASd : Integrable (fun ω => A (j + 1) ω * S j ω * d j ω) Q :=
      hint _ (((hAm (j + 1)).mul (hSm j)).mul (hdm j)).aestronglyMeasurable
        (((j + 1 : ℕ) * b ^ 2) * (j * b) * b)
        (by filter_upwards [hAb (j + 1), hSb j, hb j] with ω h1 h2 h3
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3
              (abs_nonneg _) (by positivity))
    have iAd2 : Integrable (fun ω => A (j + 1) ω * d j ω ^ 2) Q :=
      hint _ ((hAm (j + 1)).mul ((hdm j).pow_const 2)).aestronglyMeasurable
        (((j + 1 : ℕ) * b ^ 2) * b ^ 2)
        (by filter_upwards [hAb (j + 1), hb j] with ω h1 h2
            rw [abs_mul, abs_pow]
            exact mul_le_mul h1 (pow_le_pow_left₀ (abs_nonneg _) h2 2) (by positivity)
              (by positivity))
    have hz : ∫ ω, A (j + 1) ω * S j ω * d j ω ∂Q = 0 :=
      integral_mul_eq_zero_of_condExp (𝒢.le j) ((hAF j).mul (hSF j)) iASd
        ((hdL2 j).integrable one_le_two) (h0 j)
    have he : (fun ω => A (j + 1) ω * (S (j + 1) ω ^ 2 - S j ω ^ 2)) =
        fun ω => 2 * (A (j + 1) ω * S j ω * d j ω) + A (j + 1) ω * d j ω ^ 2 := by
      ext ω
      have hS1 : S (j + 1) ω = S j ω + d j ω := by simp only [hS]; rw [Finset.sum_range_succ]
      rw [hS1]; ring
    rw [he, integral_add (iASd.const_mul 2) iAd2, integral_const_mul, hz, mul_zero, zero_add]
    exact integral_nonneg_of_ae ((hA0 (j + 1)).mono fun ω h => mul_nonneg h (sq_nonneg _))
  have iSA : Integrable (fun ω => S m ω ^ 2 * A m ω) Q :=
    hint _ (((hSm m).pow_const 2).mul (hAm m)).aestronglyMeasurable ((m * b) ^ 2 * (m * b ^ 2))
      (by filter_upwards [hSb m, hAb m] with ω h1 h2
          rw [abs_mul, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) h2 (abs_nonneg _)
            (by positivity))
  have hSv : ∑ j ∈ Finset.range m, ∫ ω, S j ω ^ 2 * v j ω ∂Q ≤ c ^ 2 := by
    rw [← integral_finsetSum _ fun j _ => iS2v j]
    simp_rw [hparts m]
    rw [integral_sub iSA (integrable_finsetSum _ fun j _ => iAS j),
      integral_finsetSum _ fun j _ => iAS j]
    have h1 : 0 ≤ ∑ j ∈ Finset.range m,
        ∫ ω, A (j + 1) ω * (S (j + 1) ω ^ 2 - S j ω ^ 2) ∂Q :=
      Finset.sum_nonneg fun j _ => hnonneg j
    have h2 : ∫ ω, S m ω ^ 2 * A m ω ∂Q ≤ c * ∫ ω, S m ω ^ 2 ∂Q := by
      rw [← integral_const_mul]
      refine integral_mono_ae iSA ((hdL2 0 |> fun _ =>
        (memLp_finsetSum _ fun i _ => hdL2 i).integrable_sq).const_mul c) ?_
      filter_upwards [hclock] with ω hω
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left hω (sq_nonneg _)
    have h3 : c * ∫ ω, S m ω ^ 2 ∂Q ≤ c * c := by
      rw [hS2]; exact mul_le_mul_of_nonneg_left hAmc hc
    nlinarith
  have hvs : ∑ j ∈ Finset.range m, ∫ ω, v j ω ∂Q ≤ c := by
    rw [← integral_finsetSum _ fun j _ => hvi j]; exact hAmc
  calc ∫ ω, (∑ i ∈ Finset.range m, d i ω) ^ 4 ∂Q = ∫ ω, S m ω ^ 4 ∂Q := rfl
    _ ≤ 8 * c ^ 2 + 3 * b ^ 2 * c := by nlinarith [sq_nonneg b, hsum4 m]

/-! ### Truncation, recentring and stopping at the clock -/

/-- The truncation `Dₖ 1{Dₖ² < a}`. -/
noncomputable def truncSq (D : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if D k ω ^ 2 < a then D k ω else 0

/-- The recentred truncation `Dₖ 1{Dₖ² < a} − E[Dₖ 1{Dₖ² < a} | 𝓕ₖ]`. -/
noncomputable def ctrunc (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a : ℝ)
    (k : ℕ) : Ω → ℝ :=
  truncSq D a k - Q[truncSq D a k | ℱ k]

/-- Its conditional variance `E[ctrunc² | 𝓕ₖ]`. -/
noncomputable def cvar (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a : ℝ)
    (k : ℕ) : Ω → ℝ :=
  Q[ctrunc Q ℱ D a k ^ 2 | ℱ k]

/-- The clock `Σ_{i<j} E[ctruncᵢ² | 𝓕ᵢ]`. -/
noncomputable def ctClock (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a : ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, cvar Q ℱ D a i ω

/-- The stopping weight: `1` while the clock stays within `τ` of the time,
`|ctClock (j+1) − (j+1)| ≤ τ` for all `j ≤ k`. -/
noncomputable def activeW (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a τ : ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  {ω | ∀ j ∈ Finset.range (k + 1), |ctClock Q ℱ D a (j + 1) ω - (j + 1)| ≤ τ}.indicator
    (fun _ => 1) ω

/-- The localised increments `activeW · ctrunc`. -/
noncomputable def locInc (Q : Measure Ω) (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (a τ : ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  activeW Q ℱ D a τ k ω * ctrunc Q ℱ D a k ω

omit [MeasurableSpace Ω] in
/-- Pathwise facts on the truncation: `|D 1{D² < a}| ≤ √a` and
`(D 1{D² < a})² + D² 1{D² ≥ a} = D²`. -/
theorem truncSq_pointwise (D : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) :
    |truncSq D a k ω| ≤ √a ∧ truncSq D a k ω ^ 2 + bigSq D a k ω = D k ω ^ 2 := by
  unfold truncSq bigSq
  by_cases h : D k ω ^ 2 < a
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | a ≤ D k ω ^ 2} by
      simp only [mem_ofPred_eq, not_le]; exact h)]
    simp only [h, ↓reduceIte]
    refine ⟨?_, by ring⟩
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h.le
  · push Not at h
    rw [Set.indicator_of_mem (show ω ∈ {ω | a ≤ D k ω ^ 2} from h)]
    simp only [not_lt.2 h, ↓reduceIte]
    exact ⟨by simp [Real.sqrt_nonneg], by ring⟩

omit [MeasurableSpace Ω] in
/-- On the large values, `|D 1{D² ≥ a}| ≤ D² 1{D² ≥ a} / √a`. -/
theorem abs_sub_truncSq_le (D : ℕ → Ω → ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ) (ω : Ω) :
    |D k ω - truncSq D a k ω| ≤ bigSq D a k ω / √a := by
  unfold truncSq bigSq
  by_cases h : D k ω ^ 2 < a
  · simp only [h, ↓reduceIte, sub_self, abs_zero]
    exact div_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω) (Real.sqrt_nonneg _)
  · push Not at h
    simp only [not_lt.2 h, ↓reduceIte, sub_zero]
    rw [Set.indicator_of_mem (show ω ∈ {ω | a ≤ D k ω ^ 2} from h),
      le_div_iff₀ (Real.sqrt_pos.2 ha)]
    have h1 : √a ≤ |D k ω| := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h
    calc |D k ω| * √a ≤ |D k ω| * |D k ω| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = D k ω ^ 2 := by rw [← sq, sq_abs]

/-- Measurability and integrability of the truncation. -/
theorem truncSq_props {Q : Measure Ω} [IsFiniteMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k)) (a : ℝ)
    (k : ℕ) : StronglyMeasurable[ℱ (k + 1)] (truncSq D a k) ∧ MemLp (truncSq D a k) 2 Q ∧
      MemLp (truncSq D a k) ⊤ Q := by
  have hDk : Measurable[ℱ (k + 1)] (D k) := (hD k).measurable
  have hm : StronglyMeasurable[ℱ (k + 1)] (truncSq D a k) :=
    (Measurable.ite (measurableSet_lt (hDk.pow_const 2) measurable_const) hDk
      measurable_const).stronglyMeasurable
  have hm0 : AEStronglyMeasurable (truncSq D a k) Q :=
    (hm.measurable.mono (ℱ.le (k + 1)) le_rfl).aestronglyMeasurable
  refine ⟨hm, MemLp.of_bound hm0 (√a) (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (truncSq_pointwise D a k ω).1), memLp_top_of_bound hm0 (√a)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (truncSq_pointwise D a k ω).1)⟩

/-- **The recentred truncation**: `𝓕ₖ₊₁`-measurable, `|ctrunc| ≤ 2√a`, `E[ctrunc | 𝓕ₖ] = 0`,
`|E[D 1{D² < a} | 𝓕ₖ]| ≤ E[D² 1{D² ≥ a} | 𝓕ₖ]/√a` and
`|E[ctrunc² | 𝓕ₖ] − E[D² | 𝓕ₖ]| ≤ E[D² 1{D² ≥ a} | 𝓕ₖ] + E[D 1{D² < a} | 𝓕ₖ]²`. -/
theorem ctrunc_props {Q : Measure Ω} [IsProbabilityMeasure Q] {ℱ : Filtration ℕ mΩ}
    {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0) {a : ℝ} (ha : 0 < a)
    (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (ctrunc Q ℱ D a k) ∧
      (∀ᵐ ω ∂Q, |ctrunc Q ℱ D a k ω| ≤ 2 * √a) ∧ Q[ctrunc Q ℱ D a k | ℱ k] =ᵐ[Q] 0 ∧
      (∀ᵐ ω ∂Q, |Q[truncSq D a k | ℱ k] ω| ≤ Q[bigSq D a k | ℱ k] ω / √a) ∧
      (∀ᵐ ω ∂Q, |cvar Q ℱ D a k ω - Q[fun ω => D k ω ^ 2 | ℱ k] ω| ≤
        Q[bigSq D a k | ℱ k] ω + Q[truncSq D a k | ℱ k] ω ^ 2) ∧
      (∀ᵐ ω ∂Q, 0 ≤ cvar Q ℱ D a k ω) := by
  obtain ⟨hYF, hY2, hYt⟩ := truncSq_props (Q := Q) hD a k
  have hYi : Integrable (truncSq D a k) Q := hY2.integrable one_le_two
  have hDi : Integrable (D k) Q := (hL2 k).integrable one_le_two
  obtain ⟨hBF, hBi⟩ := bigSq_props hD hL2 a k
  have hce : StronglyMeasurable[ℱ k] (Q[truncSq D a k | ℱ k]) := stronglyMeasurable_condExp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hYF.measurable.sub (hce.measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl))
      |>.stronglyMeasurable
  · have hb := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := Q) (m := ℱ k) (R := √a)
      (f := truncSq D a k) (Eventually.of_forall fun ω => (truncSq_pointwise D a k ω).1)
    filter_upwards [hb] with ω hω
    simp only [ctrunc, Pi.sub_apply]
    calc |truncSq D a k ω - Q[truncSq D a k | ℱ k] ω|
        ≤ |truncSq D a k ω| + |Q[truncSq D a k | ℱ k] ω| := abs_sub _ _
      _ ≤ √a + √a := add_le_add (truncSq_pointwise D a k ω).1 hω
      _ = 2 * √a := by ring
  · have h1 : Q[ctrunc Q ℱ D a k | ℱ k] =ᵐ[Q]
        Q[truncSq D a k | ℱ k] - Q[Q[truncSq D a k | ℱ k] | ℱ k] :=
      condExp_sub hYi integrable_condExp _
    have h2 : Q[Q[truncSq D a k | ℱ k] | ℱ k] = Q[truncSq D a k | ℱ k] :=
      condExp_of_stronglyMeasurable (ℱ.le k) hce integrable_condExp
    filter_upwards [h1] with ω e1
    rw [e1, h2, Pi.sub_apply, sub_self, Pi.zero_apply]
  · -- `E[Y | 𝓕] = −E[D − Y | 𝓕]`
    set R : Ω → ℝ := fun ω => D k ω - truncSq D a k ω with hR
    have hRi : Integrable R Q := hDi.sub hYi
    have hY : truncSq D a k = fun ω => D k ω - R ω := by ext ω; simp only [hR]; ring
    have h1 : Q[truncSq D a k | ℱ k] =ᵐ[Q] Q[D k | ℱ k] - Q[R | ℱ k] := by
      rw [hY]; exact condExp_sub hDi hRi _
    have h2 := norm_condExp_le (μ := Q) (m := ℱ k) R
    have h3 : Q[fun ω => ‖R ω‖ | ℱ k] ≤ᵐ[Q] Q[fun ω => bigSq D a k ω / √a | ℱ k] :=
      condExp_mono hRi.norm (hBi.div_const _) (Eventually.of_forall fun ω => by
        change ‖R ω‖ ≤ bigSq D a k ω / √a
        rw [Real.norm_eq_abs]; exact abs_sub_truncSq_le D ha k ω)
    have h4 : Q[fun ω => bigSq D a k ω / √a | ℱ k] =ᵐ[Q]
        fun ω => Q[bigSq D a k | ℱ k] ω / √a := by
      have e : (fun ω => bigSq D a k ω / √a) = (√a)⁻¹ • bigSq D a k := by
        ext ω; simp [div_eq_inv_mul]
      rw [e]
      refine (condExp_smul (μ := Q) (m := ℱ k) (√a)⁻¹ (bigSq D a k)).trans
        (Eventually.of_forall fun ω => ?_)
      simp [div_eq_inv_mul]
    filter_upwards [h1, h0 k, h2, h3, h4] with ω e1 e2 e3 e4 e5
    rw [e1, Pi.sub_apply, e2, Pi.zero_apply, zero_sub, abs_neg, ← Real.norm_eq_abs, ← e5]
    exact e3.trans e4
  · -- the conditional variance
    have hcv := condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le k) hY2 (μ := Q)
    have hsq : truncSq D a k ^ 2 = fun ω => D k ω ^ 2 - bigSq D a k ω := by
      ext ω; simp only [Pi.pow_apply]; linarith [(truncSq_pointwise D a k ω).2]
    have h1 : Q[truncSq D a k ^ 2 | ℱ k] =ᵐ[Q] Q[fun ω => D k ω ^ 2 | ℱ k] - Q[bigSq D a k | ℱ k] :=
      by rw [hsq]; exact condExp_sub (hL2 k).integrable_sq hBi _
    have h2 := condExp_nonneg (μ := Q) (m := ℱ k)
      (Eventually.of_forall fun ω => (bigSq_nonneg_le D a k ω).1 : 0 ≤ᵐ[Q] bigSq D a k)
    filter_upwards [hcv, h1, h2] with ω e1 e2 e3
    have e1' : cvar Q ℱ D a k ω = Q[truncSq D a k ^ 2 | ℱ k] ω - Q[truncSq D a k | ℱ k] ω ^ 2 :=
      e1
    rw [e1', e2, Pi.sub_apply]
    simp only [Pi.zero_apply] at e3
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Q[truncSq D a k | ℱ k] ω)]
  · have := condExp_nonneg (μ := Q) (m := ℱ k) (f := ctrunc Q ℱ D a k ^ 2)
      (Eventually.of_forall fun ω => by simp only [Pi.pow_apply, Pi.zero_apply]; positivity)
    filter_upwards [this] with ω h
    exact h

end MeynTweedie.LimitTheorems
