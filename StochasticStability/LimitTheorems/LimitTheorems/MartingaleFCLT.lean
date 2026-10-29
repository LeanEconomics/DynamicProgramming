/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.MartingaleArrayCLT
import LimitTheorems.MartingaleUI
import LimitTheorems.BrownianMotion
import LimitTheorems.WeakConvergenceC01

/-!
# The functional CLT for martingales with uniformly integrable squares (MT Theorem D.6.4)

Meyn and Tweedie, §D.6.2, pp. 562–563. For a martingale `Mₙ = Σ_{k<n} Dₖ` the interpolated
process (D.7) is `mₙ(t) = M_{⌊nt⌋} + (nt − ⌊nt⌋)(M_{⌊nt⌋+1} − M_{⌊nt⌋})`, here
`polygonal n M` (`PathSpaceC01`); `wienerMeasure` (`BrownianMotion`) is the law of standard
Brownian motion on `C([0,1], ℝ)`.

Theorem D.6.4 under the book's own hypotheses, (D.8) and the conditional Lindeberg condition
(D.9), is `theorem_D_6_4` in `MartingaleFCLTGeneral`. This module proves the versions in which
(D.9) is replaced by the **uniform integrability of the squares** `Dₖ²` (`IsUnifSqIntegrable`:
`sup_k E[Dₖ² 1{Dₖ² ≥ K}] → 0` as `K → ∞`), which hold for identically distributed or bounded
increments and have a shorter proof (the block bound of `MartingaleUI` needs no stopping).

**Results.**
* `martingale_fidiLin_polygonal_rows`, `martingale_fidiLin_polygonal`: the linear
  finite-dimensional distributions of `n^{−1/2} mₙ` converge to those of Brownian motion (along
  rows `rᵢ → ∞`, or along all `n`), from the martingale-array CLT `martingale_fidi_clt_rows` and
  `abs_fidiLin_polygonal_sub_le` (the interpolation error is at most `max_{k≤n} |Dₖ|/√n → 0`).
* `martingale_block_condition`, `isTightMeasureSet_martingale_polygonal`: Billingsley's block
  condition and tightness, from `exists_block_max_le` (`MartingaleUI`).
* `theorem_D_6_4_of_unifSqIntegrable`: `(γ² n)^{−1/2} mₙ ⇒ B` under (D.8),
  `(1/n) Σ_{k<n} E[Dₖ² | 𝓕ₖ] → γ²` a.s., and uniform integrability of the squares;
  `martingale_fclt_condVar_one` is the case `γ² = 1`, `theorem_D_6_4_identDistrib` the case of
  identically distributed increments (as under `P_π` for the Markov chain martingale `Mₙ(g)` of
  (17.43)); `FunctionalCLT` uses the book's version `theorem_D_6_4`
  (`MartingaleFCLTGeneral`). `martingale_fclt` (with `martingale_fclt_one`) is the variant
  with the squares themselves, `(1/n) Σ_{k<n} Dₖ² → γ²` a.s., as in the McLeish CLT
  `martingale_clt`.
* Tools for (D.8): `tendstoInMeasure_sum_floor_sq_sub_condExp` (the squares and their
  conditional expectations have the same averages, in probability), `tendstoInMeasure_max_sq_div`
  (`max_{k≤n} Dₖ²/n → 0` in probability) and `exists_subseq_ae_tendsto_zero` (a common almost
  surely convergent subsequence); the fidis then converge along a further subsequence of every
  subsequence.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The finite-dimensional distributions of the normalised polygonal martingale along rows
`rᵢ → ∞`: if `(1/rᵢ) Σ_{k<⌊rᵢ tⱼ⌋} Dₖ² → tⱼ` and `max_{k≤rᵢ} Dₖ²/rᵢ → 0` a.s., then
`fidiLin t c (rᵢ^{−1/2} m_{rᵢ})` converges in distribution to `fidiLin t c` under Wiener
measure. -/
theorem martingale_fidiLin_polygonal_rows [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {K : ℕ} (t : Fin K → unitInterval) (c : Fin K → ℝ) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop)
    (hvt : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, D k ω ^ 2) / r i) atTop
      (𝓝 ((t j : ℝ) * 1)))
    (hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, D k ω ^ 2 ≤ ε * r i) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (i : ℕ) ω => fidiLin t c
      (polygonal (r i) fun k => (√(r i : ℝ))⁻¹ * ∑ l ∈ Finset.range k, D l ω)) atTop
      (fidiLin t c) (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  have hZ : HasLaw (fidiLin t c) (gaussianReal 0
      (1 * ∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)).toNNReal) wienerMeasure := by
    rw [one_mul]
    exact ⟨(measurable_fidiLin t c).aemeasurable, wienerMeasure_fidiLin t c⟩
  have hX := martingale_fidi_clt_rows hD hL2 h0 hbdd (fun i => (t i : ℝ))
    (fun i => (t i).2.2) c hvt hmax hZ
  set s : ℕ → Ω → ℕ → ℝ := fun n ω k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D i ω with hs
  have hYm : ∀ n : ℕ, Measurable fun ω => fidiLin t c (polygonal n (s n ω)) := fun n =>
    (measurable_fidiLin t c).comp (measurable_polygonal_comp (fun k =>
      measurable_const.mul (Finset.measurable_sum _ fun i _ => hDm i)) n)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX ?_ fun i =>
    (hYm (r i)).aemeasurable
  -- the difference tends to zero almost surely
  have hXm : ∀ n : ℕ, Measurable fun ω => (√(n : ℝ))⁻¹ *
      ∑ i, c i * ∑ k ∈ Finset.range ⌊(n : ℝ) * (t i : ℝ)⌋₊, D k ω := fun n =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Finset.measurable_sum _ fun k _ => hDm k))
  refine tendstoInMeasure_of_tendsto_ae (fun i =>
    ((hYm (r i)).sub (hXm (r i))).aestronglyMeasurable) ?_
  filter_upwards [hmax] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  set W := ∑ i, |c i| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hε' : 0 < (ε / (2 * (W + 1))) ^ 2 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hω _ hε').and (hr.eventually_ge_atTop 1))
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨hn1, hn2⟩ := hN i hi
  set n := r i with hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn2
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [Real.dist_eq, Pi.zero_apply, sub_zero, Pi.sub_apply, Pi.sub_apply]
  have hb := abs_fidiLin_polygonal_sub_le t c n (s n ω)
  have hrw : ∑ i, c i * s n ω ⌊(n : ℝ) * (t i : ℝ)⌋₊ = (√(n : ℝ))⁻¹ *
      ∑ i, c i * ∑ k ∈ Finset.range ⌊(n : ℝ) * (t i : ℝ)⌋₊, D k ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hs]; ring
  rw [hrw] at hb
  -- each increment is at most `ε / (2 (W + 1))`
  have hinc : ∀ i, |s n ω (⌊(n : ℝ) * (t i : ℝ)⌋₊ + 1) - s n ω ⌊(n : ℝ) * (t i : ℝ)⌋₊| ≤
      ε / (2 * (W + 1)) := by
    intro i
    set j := ⌊(n : ℝ) * (t i : ℝ)⌋₊
    have hj : j ≤ n := floor_natCast_mul_le n (t i)
    have e : s n ω (j + 1) - s n ω j = (√(n : ℝ))⁻¹ * D j ω := by
      simp only [hs]; rw [Finset.sum_range_succ]; ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hsq), inv_mul_le_iff₀ hsq]
    have h1 := hn1 j hj
    have h2 : D j ω ^ 2 ≤ (ε / (2 * (W + 1)) * √(n : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]; exact h1
    have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
    rw [abs_le]
    constructor <;> nlinarith [h3.1, h3.2]
  calc |fidiLin t c (polygonal n (s n ω)) - (√(n : ℝ))⁻¹ *
        ∑ i, c i * ∑ k ∈ Finset.range ⌊(n : ℝ) * (t i : ℝ)⌋₊, D k ω|
      ≤ ∑ i, |c i| * |s n ω (⌊(n : ℝ) * (t i : ℝ)⌋₊ + 1) - s n ω ⌊(n : ℝ) * (t i : ℝ)⌋₊| := hb
    _ ≤ ∑ i, |c i| * (ε / (2 * (W + 1))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinc i) (abs_nonneg _)
    _ = W * (ε / (2 * (W + 1))) := by rw [← Finset.sum_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- The finite-dimensional distributions of the normalised polygonal martingale: under the
hypotheses of `martingale_clt` with `σ² = 1`, `fidiLin t c (n^{−1/2} mₙ)` converges in
distribution to `fidiLin t c` under Wiener measure. -/
theorem martingale_fidiLin_polygonal [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 1))
    {C : ℝ} (hbdd : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂Q ≤ C * n)
    {K : ℕ} (t : Fin K → unitInterval) (c : Fin K → ℝ) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω => fidiLin t c
      (polygonal n fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop
      (fidiLin t c) (fun _ => Q) wienerMeasure :=
  martingale_fidiLin_polygonal_rows (r := fun n => n) hD hL2 h0 hbdd t c tendsto_id
    (fun j => hvar.mono fun _ hω => tendsto_sum_floor_div hω (t j).2.1)
    (ae_eventually_sq_le_of_tendsto hvar)

/-- Billingsley's block condition (the hypothesis of `isTightMeasureSet_polygonal_of_blocks`) for
the partial sums of square-integrable martingale differences with uniformly integrable
squares. -/
theorem martingale_block_condition {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ m : ℕ, 0 < m ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ j : ℕ,
      (m : ℝ≥0∞) * Q {ω | ∃ i ≤ n / m + 1, ε * √(n : ℝ) ≤
        |∑ k ∈ Finset.range (j + i), D k ω - ∑ k ∈ Finset.range j, D k ω|} ≤ η := by
  intro ε hε η hη
  by_cases hηt : η = ⊤
  · exact ⟨1, one_pos, 0, fun n _ j => by rw [hηt]; exact le_top⟩
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηt
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_block_max_le hD hL2 h0 hUI hε (half_pos hηr)
  set m := ⌈1 / δ⌉₊ with hm
  have hm1 : 1 / δ ≤ m := Nat.le_ceil _
  have hm0 : 0 < m := Nat.cast_pos.1 ((by positivity : (0 : ℝ) < 1 / δ).trans_le hm1)
  have hm2 : (m : ℝ) ≤ 2 / δ := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / δ by positivity)
    have h2 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    rw [← hm] at this
    calc (m : ℝ) ≤ 1 / δ + 1 := this.le
      _ ≤ 2 / δ := by rw [show (2 : ℝ) / δ = 1 / δ + 1 / δ by ring]; linarith
  refine ⟨m, hm0, m, fun n hn j => ?_⟩
  have hn1 : 1 ≤ n := le_trans hm0 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  -- the block length
  have hL : ((n / m + 1 : ℕ) : ℝ) ≤ 2 * δ * n := by
    have h1 : ((n / m : ℕ) : ℝ) ≤ n / m := Nat.cast_div_le
    have h2 : (n : ℝ) / m ≤ δ * n := by
      rw [div_le_iff₀ hm0']
      have : 1 ≤ δ * m := by rw [div_le_iff₀ hδ0] at hm1; linarith
      nlinarith
    have h3 : (1 : ℝ) ≤ δ * n := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hδ0] at hm1
      nlinarith
    push_cast
    linarith
  have hsub : {ω | ∃ i ≤ n / m + 1, ε * √(n : ℝ) ≤
      |∑ k ∈ Finset.range (j + i), D k ω - ∑ k ∈ Finset.range j, D k ω|} ⊆
      {ω | ε * √(n : ℝ) ≤ (Finset.range (n / m + 1 + 1)).sup' Finset.nonempty_range_add_one
        fun i => |∑ k ∈ Finset.range i, D (j + k) ω|} := by
    intro ω hω
    obtain ⟨i, hi, hle⟩ := hω
    simp only [mem_ofPred_eq]
    rw [Finset.sum_range_add, add_sub_cancel_left] at hle
    exact hle.trans (Finset.le_sup' (fun i => |∑ k ∈ Finset.range i, D (j + k) ω|)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hb := hδ n hn1 j (n / m + 1) hL
  calc (m : ℝ≥0∞) * Q _ ≤ (m : ℝ≥0∞) * Q {ω | ε * √(n : ℝ) ≤
        (Finset.range (n / m + 1 + 1)).sup' Finset.nonempty_range_add_one
          fun i => |∑ k ∈ Finset.range i, D (j + k) ω|} := by gcongr
    _ = ENNReal.ofReal (m * Q.real {ω | ε * √(n : ℝ) ≤
        (Finset.range (n / m + 1 + 1)).sup' Finset.nonempty_range_add_one
          fun i => |∑ k ∈ Finset.range i, D (j + k) ω|}) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast, ofReal_measureReal]
    _ ≤ ENNReal.ofReal η.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (m : ℝ) * Q.real _ ≤ (2 / δ) * (η.toReal / 2 * δ) :=
              mul_le_mul hm2 hb measureReal_nonneg (by positivity)
          _ = η.toReal := by field_simp
    _ = η := ENNReal.ofReal_toReal hηt

/-- **Tightness** of the normalised polygonal martingales `n^{−1/2} mₙ` (D.7) for
square-integrable martingale differences with uniformly integrable squares. -/
theorem isTightMeasureSet_martingale_polygonal [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D) :
    IsTightMeasureSet (Set.range fun n : ℕ =>
      Q.map fun ω => polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) :=
  isTightMeasureSet_polygonal_of_blocks Q (S := fun k ω => ∑ i ∈ Finset.range k, D i ω)
    (fun _k => Finset.measurable_sum _ fun i _ =>
      (hD i).measurable.mono (ℱ.le (i + 1)) le_rfl)
    (fun _ω => Finset.sum_range_zero _) (martingale_block_condition hD hL2 h0 hUI)

/-! ### The martingale FCLT -/

/-- The martingale FCLT with unit variance: for square-integrable martingale differences with
uniformly integrable squares and `(1/n) Σ_{k<n} Dₖ² → 1` a.s., `n^{−1/2} mₙ ⇒ W` (Wiener
measure). -/
theorem martingale_fclt_one [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D)
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 1)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  obtain ⟨C, hbdd⟩ := hUI.exists_sum_le (fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl)
    hL2
  exact tendstoInDistribution_polygonal_of_blocks (S := fun k ω => ∑ i ∈ Finset.range k, D i ω)
    (fun _k => Finset.measurable_sum _ fun i _ => (hD i).measurable.mono (ℱ.le (i + 1)) le_rfl)
    (fun _ω => Finset.sum_range_zero _) (martingale_block_condition hD hL2 h0 hUI) wienerMeasure
    fun _k t c => martingale_fidiLin_polygonal hD hL2 h0 hvar hbdd t c

/-- **The martingale FCLT with squared increments** (the variant of Theorem D.6.4 with the
squares in (D.8)): let `Mₙ = Σ_{k<n} Dₖ` with `Dₖ` `𝓕ₖ₊₁`-measurable, square integrable,
`E[Dₖ | 𝓕ₖ] = 0`, with uniformly integrable squares, and `(1/n) Σ_{k<n} Dₖ² → γ² > 0` almost
surely. Then `(γ² n)^{−1/2} mₙ ⇒ B`, a standard Brownian motion (`wienerMeasure`). -/
theorem martingale_fclt [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D) {γ2 : ℝ} (hγ : 0 < γ2)
    (hvar : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D k ω ^ 2) / n) atTop
      (𝓝 γ2)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(γ2 * n))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  set a := (√γ2)⁻¹ with ha
  have hsq : 0 < √γ2 := Real.sqrt_pos.2 hγ
  have ha2 : a ^ 2 = γ2⁻¹ := by rw [ha, inv_pow, Real.sq_sqrt hγ.le]
  set D' : ℕ → Ω → ℝ := fun k ω => a * D k ω with hD'
  have hD'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D' k) := fun k => (hD k).const_mul a
  have hL2' : ∀ k, MemLp (D' k) 2 Q := fun k => (hL2 k).const_mul a
  have h0' : ∀ k, Q[D' k | ℱ k] =ᵐ[Q] 0 := fun k => by
    have := condExp_smul (μ := Q) a (D k) (ℱ k)
    refine this.trans ((h0 k).mono fun ω h => ?_)
    simp [h]
  have hUI' : IsUnifSqIntegrable Q D' := hUI.const_mul a
  have hvar' : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, D' k ω ^ 2) / n) atTop
      (𝓝 1) := by
    filter_upwards [hvar] with ω hω
    have h := hω.const_mul (a ^ 2)
    rw [ha2, inv_mul_cancel₀ hγ.ne'] at h
    refine h.congr fun n => ?_
    simp only [hD', mul_pow]
    rw [← Finset.mul_sum, mul_div_assoc, ha2]
  have hfun : (fun (n : ℕ) ω => polygonal n (fun k => (√(γ2 * n))⁻¹ *
      ∑ i ∈ Finset.range k, D i ω)) =
      fun (n : ℕ) ω => polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D' i ω) := by
    funext n ω
    congr 1
    funext k
    simp only [hD', ← Finset.mul_sum, ha]
    rw [Real.sqrt_mul hγ.le, mul_inv]
    ring
  rw [hfun]
  exact martingale_fclt_one hD'm hL2' h0' hUI' hvar'

/-! ### Theorem D.6.4 with conditional variances -/

/-- A finite family of sequences tending to `0` in probability has a common subsequence along
which all of them tend to `0` almost surely. -/
theorem exists_subseq_ae_tendsto_zero {Q : Measure Ω} [IsFiniteMeasure Q] {ι : Type*}
    [Finite ι] {f : ι → ℕ → Ω → ℝ} (h : ∀ j, TendstoInMeasure Q (f j) atTop 0) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂Q, ∀ j, Tendsto (fun i => f j (ms i) ω) atTop (𝓝 0) := by
  have : Fintype ι := Fintype.ofFinite ι
  set g : ℕ → Ω → ℝ := fun n ω => ∑ j, |f j n ω| with hg
  have hgm : TendstoInMeasure Q g atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    set c := (Fintype.card ι : ℝ) + 1 with hc
    have hc0 : 0 < c := by positivity
    have hsub : ∀ n, {ω | ε ≤ ‖g n ω - (0 : Ω → ℝ) ω‖} ⊆
        ⋃ j, {ω | ε / c ≤ ‖f j n ω - (0 : Ω → ℝ) ω‖} := by
      intro n ω hω
      simp only [mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, mem_iUnion] at hω ⊢
      by_contra hne
      push Not at hne
      have h1 : g n ω < ε := by
        calc g n ω = ∑ j, |f j n ω| := rfl
          _ ≤ ∑ _j : ι, ε / c := Finset.sum_le_sum fun j _ => (hne j).le
          _ = Fintype.card ι * (ε / c) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ < ε := by
              rw [mul_div_assoc', div_lt_iff₀ hc0, hc]; nlinarith
      rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at hω
      exact absurd hω (not_le.2 h1)
    have hlim : Tendsto (fun n => ∑ j, Q {ω | ε / c ≤ ‖f j n ω - (0 : Ω → ℝ) ω‖}) atTop
        (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ =>
        (tendstoInMeasure_iff_norm.1 (h j)) (ε / c) (by positivity)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      fun n => (measure_mono (hsub n)).trans (measure_iUnion_fintype_le _ _)
  obtain ⟨ms, hms, hae⟩ := hgm.exists_seq_tendsto_ae
  refine ⟨ms, hms, hae.mono fun ω hω j => ?_⟩
  refine squeeze_zero_norm (fun i => ?_) hω
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |f j (ms i) ω|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ j)

/-- For square-integrable `Dₖ` with uniformly integrable squares, `max_{k≤n} Dₖ²/n → 0` in
probability. -/
theorem tendstoInMeasure_max_sq_div {Q : Measure Ω} [IsProbabilityMeasure Q] {D : ℕ → Ω → ℝ}
    (hDm : ∀ k, Measurable (D k)) (hL2 : ∀ k, MemLp (D k) 2 Q) (hUI : IsUnifSqIntegrable Q D) :
    TendstoInMeasure Q (fun (n : ℕ) ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => D k ω ^ 2) / n) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro θ hθ
  by_cases hθt : θ = ⊤
  · exact ⟨0, fun n _ => hθt ▸ le_top⟩
  have hθr : 0 < θ.toReal := ENNReal.toReal_pos hθ.ne' hθt
  obtain ⟨K, -, hK⟩ := hUI.exists_forall_ge hDm hL2 (show 0 < ε * θ.toReal / 2 by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hKn : K ≤ ε * n := by
    have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  have hsub : {ω | ε ≤ ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => D k ω ^ 2) / n - (0 : Ω → ℝ) ω‖} ⊆
      ⋃ k ∈ Finset.range (n + 1), {ω | ε * n ≤ D k ω ^ 2} := by
    intro ω hω
    simp only [mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun k => D k ω ^ 2)
    rw [hkeq, abs_of_nonneg (by positivity), le_div_iff₀ hn0] at hω
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨k, hk, hω⟩
  have hk : ∀ k, Q {ω | ε * n ≤ D k ω ^ 2} ≤ ENNReal.ofReal (θ.toReal / (2 * n)) := by
    intro k
    have hsetm : MeasurableSet {ω | ε * n ≤ D k ω ^ 2} :=
      measurableSet_le measurable_const ((hDm k).pow_const 2)
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := Q)
      (f := {ω | ε * n ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2))
      (Eventually.of_forall fun ω => Set.indicator_nonneg (fun ω _ => sq_nonneg _) ω)
      ((hL2 k).integrable_sq.indicator hsetm) (ε * n)
    have hset : {ω | ε * n ≤ {ω | ε * n ≤ D k ω ^ 2}.indicator (fun ω => D k ω ^ 2) ω} =
        {ω | ε * n ≤ D k ω ^ 2} := by
      ext ω
      simp only [mem_ofPred_eq, Set.indicator_apply]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => h⟩
      · exact ⟨fun h' => absurd h' (not_le.2 (by positivity)), fun h' => absurd h' h⟩
    rw [hset] at h1
    have h2 : (ε * n) * Q.real {ω | ε * n ≤ D k ω ^ 2} ≤ ε * θ.toReal / 2 :=
      h1.trans (hK _ hKn k)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc Q _ ≤ Q (⋃ k ∈ Finset.range (n + 1), {ω | ε * n ≤ D k ω ^ 2}) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (n + 1), Q {ω | ε * n ≤ D k ω ^ 2} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n + 1), ENNReal.ofReal (θ.toReal / (2 * n)) :=
        Finset.sum_le_sum fun k _ => hk k
    _ = ENNReal.ofReal ((n + 1) * (θ.toReal / (2 * n))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        norm_cast
    _ ≤ ENNReal.ofReal θ.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : ((n : ℝ) + 1) ≤ 2 * n := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          linarith
        calc ((n : ℝ) + 1) * (θ.toReal / (2 * n)) ≤ 2 * n * (θ.toReal / (2 * n)) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = θ.toReal := by field_simp
    _ = θ := ENNReal.ofReal_toReal hθt

/-- For square-integrable `Dₖ` (`𝓕ₖ₊₁`-measurable) with uniformly integrable squares and
`0 ≤ t ≤ 1`,
`(1/n) Σ_{k<⌊nt⌋} (Dₖ² − E[Dₖ² | 𝓕ₖ]) → 0` in probability. -/
theorem tendstoInMeasure_sum_floor_sq_sub_condExp {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (hUI : IsUnifSqIntegrable Q D) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoInMeasure Q (fun (n : ℕ) ω => (∑ k ∈ Finset.range ⌊(n : ℝ) * t⌋₊,
      (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n) atTop 0 := by
  set m : ℕ → ℕ := fun n => ⌊(n : ℝ) * t⌋₊ with hm
  set A : ℕ → Ω → ℝ := fun j ω => ∑ k ∈ Finset.range j,
    (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω) with hA
  have hAi : ∀ j, Integrable (A j) Q := fun j =>
    integrable_finsetSum _ fun k _ => (hL2 k).integrable_sq.sub integrable_condExp
  have hmn : ∀ n : ℕ, m n ≤ n := fun n => Nat.floor_le_of_le
    (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  refine tendstoInMeasure_zero_of_integral_abs (fun n => (hAi (m n)).div_const _) ?_
  have hL1 := tendsto_integral_abs_avg_sq_sub_condExp hD hL2 hUI
  have hcomp : Tendsto (fun n : ℕ => ∫ ω, |A (m n) ω / m n| ∂Q) atTop (𝓝 0) := by
    rcases ht0.eq_or_lt with rfl | htpos
    · refine tendsto_const_nhds.congr fun n => ?_
      simp [hm, hA]
    · have hmt : Tendsto m atTop atTop := by
        refine (tendsto_nat_floor_mul_atTop t htpos).congr fun n => ?_
        simp only [hm, mul_comm]
      exact hL1.comp hmt
  refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_) hcomp
  refine integral_mono ((hAi (m n)).div_const _).abs ((hAi (m n)).div_const _).abs fun ω => ?_
  simp only
  rcases Nat.eq_zero_or_pos (m n) with h0 | hpos
  · have h0' : ⌊(n : ℝ) * t⌋₊ = 0 := h0
    simp [hA, hm, h0']
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos.trans_le (hmn n)
    have hm0 : (0 : ℝ) < m n := by exact_mod_cast hpos
    rw [abs_div, abs_div, abs_of_pos hn0, abs_of_pos hm0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm0 (by exact_mod_cast hmn n)

/-- **Theorem D.6.4 with conditional variances, unit variance**: square-integrable martingale
differences with uniformly integrable squares and `(1/n) Σ_{k<n} E[Dₖ² | 𝓕ₖ] → 1` a.s. (D.8)
satisfy `n^{−1/2} mₙ ⇒ W`. -/
theorem martingale_fclt_condVar_one [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  have hDm : ∀ k, Measurable (D k) := fun k => (hD k).measurable.mono (ℱ.le (k + 1)) le_rfl
  obtain ⟨C, hbdd⟩ := hUI.exists_sum_le hDm hL2
  refine tendstoInDistribution_polygonal_of_blocks (S := fun k ω => ∑ i ∈ Finset.range k, D i ω)
    (fun _k => Finset.measurable_sum _ fun i _ => hDm i)
    (fun _ω => Finset.sum_range_zero _) (martingale_block_condition hD hL2 h0 hUI) wienerMeasure
    fun K t c => ?_
  have hYm : ∀ n : ℕ, Measurable fun ω => fidiLin t c
      (polygonal n (fun j => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range j, D i ω)) := fun n =>
    (measurable_fidiLin t c).comp (measurable_polygonal_comp (fun k =>
      measurable_const.mul (Finset.measurable_sum _ fun i _ => hDm i)) n)
  refine ⟨fun n => (hYm n).aemeasurable, (measurable_fidiLin t c).aemeasurable, ?_⟩
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  -- the in-probability limits along `ns`
  set F : Option (Fin K) → ℕ → Ω → ℝ := fun o => Option.elim o
    (fun n ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => D k ω ^ 2) / n)
    (fun j n ω => (∑ k ∈ Finset.range ⌊(n : ℝ) * (t j : ℝ)⌋₊,
      (D k ω ^ 2 - Q[fun ω => D k ω ^ 2 | ℱ k] ω)) / n) with hF
  have hFm : ∀ o, TendstoInMeasure Q (F o) atTop 0 := by
    intro o
    cases o with
    | none => exact tendstoInMeasure_max_sq_div hDm hL2 hUI
    | some j => exact tendstoInMeasure_sum_floor_sq_sub_condExp hD hL2 hUI (t j).2.1 (t j).2.2
  have hFns : ∀ o, TendstoInMeasure Q (fun i => F o (ns i)) atTop 0 := fun o ε hε =>
    ((hFm o) ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_zero hFns
  set r : ℕ → ℕ := fun i => ns (ms i) with hr
  have hrt : Tendsto r atTop atTop := hns.comp hms.tendsto_atTop
  have hvt : ∀ j, ∀ᵐ ω ∂Q, Tendsto (fun i : ℕ =>
      (∑ k ∈ Finset.range ⌊(r i : ℝ) * (t j : ℝ)⌋₊, D k ω ^ 2) / r i) atTop
      (𝓝 ((t j : ℝ) * 1)) := by
    intro j
    filter_upwards [hae, hcv] with ω hω hcω
    have h1 := hω (some j)
    have h2 := (tendsto_sum_floor_div hcω (t j).2.1).comp hrt
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun i => ?_
    simp only [hF, Option.elim, Function.comp_apply]
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmax : ∀ᵐ ω ∂Q, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k ≤ r i, D k ω ^ 2 ≤ ε * r i := by
    filter_upwards [hae] with ω hω ε hε
    have h1 := (hω none).eventually (gt_mem_nhds hε)
    filter_upwards [h1, hrt.eventually_ge_atTop 1] with i hi hi1 k hk
    simp only [hF, Option.elim] at hi
    have hn0 : (0 : ℝ) < r i := by exact_mod_cast hi1
    rw [div_lt_iff₀ hn0] at hi
    exact (Finset.le_sup' (fun k => D k ω ^ 2) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))).trans
      hi.le
  exact ⟨ms, (martingale_fidiLin_polygonal_rows hD hL2 h0 hbdd t c hrt hvt hmax).tendsto⟩

/-- **Theorem D.6.4 with uniformly integrable squares** (MT p. 563; the book's version with the
Lindeberg condition (D.9) is `theorem_D_6_4` in `MartingaleFCLTGeneral`): let `Mₙ = Σ_{k<n} Dₖ`
with `Dₖ` `𝓕ₖ₊₁`-measurable, square integrable, `E[Dₖ | 𝓕ₖ] = 0`, with uniformly integrable
squares, and let (D.8) hold:
`(1/n) Σ_{k<n} E[Dₖ² | 𝓕ₖ] → γ² > 0` almost surely. Then the interpolated process `mₙ` of
(D.7) satisfies `(γ² n)^{−1/2} mₙ ⇒ B`, a standard Brownian motion (`wienerMeasure`). -/
theorem theorem_D_6_4_of_unifSqIntegrable [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hUI : IsUnifSqIntegrable Q D) {γ2 : ℝ} (hγ : 0 < γ2)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 γ2)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(γ2 * n))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure := by
  have := isProbabilityMeasure_wienerMeasure
  set a := (√γ2)⁻¹ with ha
  have hsq : 0 < √γ2 := Real.sqrt_pos.2 hγ
  have ha2 : a ^ 2 = γ2⁻¹ := by rw [ha, inv_pow, Real.sq_sqrt hγ.le]
  set D' : ℕ → Ω → ℝ := fun k ω => a * D k ω with hD'
  have hD'm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D' k) := fun k => (hD k).const_mul a
  have hL2' : ∀ k, MemLp (D' k) 2 Q := fun k => (hL2 k).const_mul a
  have h0' : ∀ k, Q[D' k | ℱ k] =ᵐ[Q] 0 := fun k => by
    have := condExp_smul (μ := Q) a (D k) (ℱ k)
    refine this.trans ((h0 k).mono fun ω h => ?_)
    simp [h]
  have hUI' : IsUnifSqIntegrable Q D' := hUI.const_mul a
  have hce : ∀ k, Q[fun ω => D' k ω ^ 2 | ℱ k] =ᵐ[Q]
      fun ω => a ^ 2 * Q[fun ω => D k ω ^ 2 | ℱ k] ω := fun k => by
    have e : (fun ω => D' k ω ^ 2) = (a ^ 2) • fun ω => D k ω ^ 2 := by
      ext ω; simp only [hD', Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact condExp_smul (μ := Q) (a ^ 2) (fun ω => D k ω ^ 2) (ℱ k)
  have hcv' : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D' k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 1) := by
    filter_upwards [hcv, ae_all_iff.2 hce] with ω hω hceω
    have h := hω.const_mul (a ^ 2)
    rw [ha2, inv_mul_cancel₀ hγ.ne'] at h
    refine h.congr fun n => ?_
    rw [Finset.sum_congr rfl fun k _ => hceω k, ← Finset.mul_sum, mul_div_assoc, ha2]
  have hfun : (fun (n : ℕ) ω => polygonal n (fun k => (√(γ2 * n))⁻¹ *
      ∑ i ∈ Finset.range k, D i ω)) =
      fun (n : ℕ) ω => polygonal n (fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range k, D' i ω) := by
    funext n ω
    congr 1
    funext k
    simp only [hD', ← Finset.mul_sum, ha]
    rw [Real.sqrt_mul hγ.le, mul_inv]
    ring
  rw [hfun]
  exact martingale_fclt_condVar_one hD'm hL2' h0' hUI' hcv'

/-- **Theorem D.6.4 for identically distributed increments** (the case used in Theorem 17.4.4):
square-integrable martingale differences `Dₖ` with the law of `D₀` and (D.8) satisfy
`(γ² n)^{−1/2} mₙ ⇒ B`. -/
theorem theorem_D_6_4_identDistrib [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ} (hD : ∀ k, StronglyMeasurable[ℱ (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 Q) (h0 : ∀ k, Q[D k | ℱ k] =ᵐ[Q] 0)
    (hid : ∀ k, IdentDistrib (D k) (D 0) Q Q) {γ2 : ℝ} (hγ : 0 < γ2)
    (hcv : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range n, Q[fun ω => D k ω ^ 2 | ℱ k] ω) / n) atTop (𝓝 γ2)) :
    haveI := isProbabilityMeasure_wienerMeasure
    TendstoInDistribution (fun (n : ℕ) ω =>
      polygonal n (fun k => (√(γ2 * n))⁻¹ * ∑ i ∈ Finset.range k, D i ω)) atTop id
      (fun _ => Q) wienerMeasure :=
  theorem_D_6_4_of_unifSqIntegrable hD hL2 h0 (isUnifSqIntegrable_of_identDistrib
    ((hD 0).measurable.mono (ℱ.le 1) le_rfl) (hL2 0) hid) hγ hcv

end MeynTweedie.LimitTheorems
