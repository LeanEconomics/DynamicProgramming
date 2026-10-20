/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.ModesOfConvergence

/-!
# Laws of large numbers for uncorrelated random variables

SLP §14.1, pp. 421–423.

* **Chebyshev's inequality** (`chebyshev`, (3) on p. 421).
* Uncorrelated sequences (`Uncorrelated`, p. 421), and (4): the centred variables are orthogonal
  (`integral_centered_mul`). Hence the variance of a sum is the sum of the variances
  (`integral_sq_sum`, (6)).
* **Theorem 14.4** (`theorem_14_4`, the weak law): the average of `fₖ − E fₖ` tends to `0` in
  probability.
* **Theorem 14.5** (`theorem_14_5`, the strong law): it tends to `0` almost everywhere.

**Book pp. 422–423 are missing from the scan used** (the end of the proof of Theorem 14.4, the
statement and proof of Theorem 14.5, and display (6)). Theorem 14.5 is formalised in the form in
which the book later uses it, under the hypotheses of Theorem 14.4. Its proof here is the
"method of subsequences" that the book's index names, along the squares `m²`:
* Chebyshev and Borel–Cantelli give `S_{m²}/m² → 0`;
* the gaps are controlled by `Q_m = Σ_{m² ≤ n < (m+1)²} (S_n − S_{m²})²`, whose mean is at most
  `6m²M`, so that `Q_m/m⁴ → 0`.

Sums run over `k = 0, …, n − 1` (the book's `k = 1, …, n`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Chebyshev's inequality** ((3), p. 421): `μ(|h| ≥ ε) ≤ E(h²)/ε²`. -/
theorem chebyshev [IsFiniteMeasure μ] {h : Ω → ℝ} (hh : MemLp h 2 μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |h ω|} ≤ (∫ ω, h ω ^ 2 ∂μ) / ε ^ 2 := by
  have h2 : Integrable (fun ω => h ω ^ 2) μ := hh.integrable_sq
  have := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg (h ω)) h2
    (ε ^ 2)
  have hset : {ω | ε ^ 2 ≤ h ω ^ 2} = {ω | ε ≤ |h ω|} := by
    ext ω
    simp only [mem_ofPred_eq, sq_le_sq, abs_of_pos hε]
  rw [hset] at this
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- A sequence is **uncorrelated** (p. 421): square integrable, with `E(fⱼfₖ) = E(fⱼ)E(fₖ)` for
`j ≠ k`. -/
def Uncorrelated (μ : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ k, MemLp (f k) 2 μ) ∧
    ∀ j k, j ≠ k → ∫ ω, f j ω * f k ω ∂μ = (∫ ω, f j ω ∂μ) * ∫ ω, f k ω ∂μ

/-- The centred variables `fₖ − E fₖ`. -/
noncomputable def centered (μ : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  f k ω - ∫ ω', f k ω' ∂μ

theorem memLp_centered [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    MemLp (centered μ f k) 2 μ :=
  (hf k).sub (memLp_const _)

theorem integral_centered [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (k : ℕ) : ∫ ω, centered μ f k ω ∂μ = 0 := by
  simp only [centered]
  rw [integral_sub ((hf k).integrable one_le_two) (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self]

/-- (4), p. 421: the centred variables are orthogonal. -/
theorem integral_centered_mul [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {j k : ℕ} (hjk : j ≠ k) : ∫ ω, centered μ f j ω * centered μ f k ω ∂μ = 0 := by
  set a := ∫ ω, f j ω ∂μ
  set b := ∫ ω, f k ω ∂μ
  have hj := (hf.1 j).integrable one_le_two
  have hk := (hf.1 k).integrable one_le_two
  have hjk' : Integrable (fun ω => f j ω * f k ω) μ := (hf.1 j).integrable_mul (hf.1 k)
  have hexp : (fun ω => centered μ f j ω * centered μ f k ω) =
      fun ω => f j ω * f k ω - b * f j ω - a * f k ω + a * b := by
    funext ω; simp only [centered, a, b]; ring
  have h1 : Integrable (fun ω => f j ω * f k ω - b * f j ω) μ := hjk'.sub (hj.const_mul b)
  have h2 : Integrable (fun ω => f j ω * f k ω - b * f j ω - a * f k ω) μ :=
    h1.sub (hk.const_mul a)
  rw [hexp, integral_add h2 (integrable_const _), integral_sub h1 (hk.const_mul a),
    integral_sub hjk' (hj.const_mul b), integral_const_mul, integral_const_mul, integral_const,
    probReal_univ, one_smul, hf.2 j k hjk]
  ring

/-- (6): for orthogonal square-integrable variables, the second moment of a sum is the sum of the
second moments. -/
theorem integral_sq_sum {g : ℕ → Ω → ℝ} (hg : ∀ k, MemLp (g k) 2 μ)
    (horth : ∀ j k, j ≠ k → ∫ ω, g j ω * g k ω ∂μ = 0) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, g k ω) ^ 2 ∂μ = ∑ k ∈ s, ∫ ω, g k ω ^ 2 ∂μ := by
  have hexp : ∀ ω, (∑ k ∈ s, g k ω) ^ 2 = ∑ j ∈ s, ∑ k ∈ s, g j ω * g k ω := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (hg j).integrable_mul (hg k)
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => hint j k,
    Finset.sum_eq_single j (fun k _ hkj => horth j k (Ne.symm hkj)) (fun h => absurd hj h)]
  simp only [sq]

/-- The variance bound used for Theorems 14.4–14.5: `E[(Σ_{k∈s} (fₖ − E fₖ))²] ≤ |s| M`. -/
theorem integral_sq_sum_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, centered μ f k ω) ^ 2 ∂μ ≤ s.card * M := by
  rw [integral_sq_sum (memLp_centered hf.1) (fun j k hjk => integral_centered_mul hf hjk)]
  calc ∑ k ∈ s, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ ∑ _k ∈ s, M := Finset.sum_le_sum fun k _ => hM k
    _ = s.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

theorem memLp_sum_centered [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (s : Finset ℕ) : MemLp (fun ω => ∑ k ∈ s, centered μ f k ω) 2 μ := by
  have := memLp_finsetSum' s fun k _ => memLp_centered (μ := μ) hf k
  convert this using 1
  funext ω; simp

/-- The averages `(1/n) Σ_{k<n} (fₖ − E fₖ)`. -/
noncomputable def avgDev (μ : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, centered μ f k ω

/-- **Theorem 14.4** (the weak law). For an uncorrelated sequence with bounded variances,
`(1/n) Σ_{k<n} (fₖ − E fₖ) → 0` in probability. -/
theorem theorem_14_4 [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvInProb μ (avgDev μ f) fun _ => 0 := by
  intro ε hε
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  have hbound : ∀ n : ℕ, 1 ≤ n →
      μ {ω | ε < |avgDev μ f n ω - 0|} ≤ ENNReal.ofReal (M / ε ^ 2 * (1 / n)) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hmem : MemLp (avgDev μ f n) 2 μ := (memLp_sum_centered hf.1 _).const_mul _
    have hsq : ∫ ω, avgDev μ f n ω ^ 2 ∂μ ≤ M / n := by
      simp only [avgDev, mul_pow]
      rw [integral_const_mul]
      have := integral_sq_sum_le hf hM (Finset.range n)
      rw [Finset.card_range] at this
      calc ((n : ℝ)⁻¹) ^ 2 * ∫ ω, (∑ k ∈ Finset.range n, centered μ f k ω) ^ 2 ∂μ ≤
            ((n : ℝ)⁻¹) ^ 2 * (n * M) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = M / n := by field_simp
    have hc := chebyshev hmem hε
    rw [← ofReal_measureReal (μ := μ)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc μ.real {ω | ε < |avgDev μ f n ω - 0|} ≤ μ.real {ω | ε ≤ |avgDev μ f n ω|} :=
          measureReal_mono fun ω (hω : ε < |avgDev μ f n ω - 0|) => by
            simp only [sub_zero] at hω; exact hω.le
      _ ≤ (∫ ω, avgDev μ f n ω ^ 2 ∂μ) / ε ^ 2 := hc
      _ ≤ M / n / ε ^ 2 := by gcongr
      _ = M / ε ^ 2 * (1 / n) := by ring
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (M / ε ^ 2 * (1 / n))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, ← mul_zero (M / ε ^ 2)]
    exact ENNReal.tendsto_ofReal (tendsto_one_div_atTop_nhds_zero_nat.const_mul _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) (eventually_atTop.2 ⟨1, hbound⟩)

/-! ### Theorem 14.5 -/

/-- The partial sums `S_n = Σ_{k<n} (fₖ − E fₖ)`. -/
noncomputable def partialDev (μ : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, centered μ f k ω

theorem partialDev_sub {f : ℕ → Ω → ℝ} {a n : ℕ} (h : a ≤ n) (ω : Ω) :
    partialDev μ f n ω - partialDev μ f a ω = ∑ k ∈ Finset.Ico a n, centered μ f k ω :=
  (Finset.sum_Ico_eq_sub _ h).symm

theorem memLp_partialDev_sub [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    {a n : ℕ} (h : a ≤ n) :
    MemLp (fun ω => partialDev μ f n ω - partialDev μ f a ω) 2 μ := by
  simp_rw [partialDev_sub h]
  exact memLp_sum_centered hf _

theorem integral_sq_partialDev_sub_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ}
    (hf : Uncorrelated μ f) {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) {a n : ℕ}
    (h : a ≤ n) :
    ∫ ω, (partialDev μ f n ω - partialDev μ f a ω) ^ 2 ∂μ ≤ ((n : ℝ) - a) * M := by
  simp_rw [partialDev_sub h]
  have := integral_sq_sum_le hf hM (Finset.Ico a n)
  rwa [Nat.card_Ico, Nat.cast_sub h] at this

theorem tsum_ofReal_div_sq_ne_top (c : ℝ) (hc : 0 ≤ c) :
    ∑' m : ℕ, ENNReal.ofReal (c * (1 / (m : ℝ) ^ 2)) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
    ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left c)]
  exact ENNReal.ofReal_ne_top

/-- Step 1: `S_{m²}/m² → 0` a.e. -/
theorem squares_convAE [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun m ω => partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2) fun _ => 0 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  refine lemma_14_3 μ fun ε hε => ne_top_of_le_ne_top
    (tsum_ofReal_div_sq_ne_top (M / ε ^ 2) (by positivity)) (ENNReal.tsum_le_tsum fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : {ω | ε < |partialDev μ f (0 ^ 2) ω / ((0 : ℕ) : ℝ) ^ 2 - 0|} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero,
        abs_zero, mem_empty_iff_false, iff_false, not_lt]; exact hε.le
    rw [this, measure_empty]; exact zero_le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmem : MemLp (partialDev μ f (m ^ 2)) 2 μ := memLp_sum_centered hf.1 _
  have hc := chebyshev hmem (show 0 < ε * (m : ℝ) ^ 2 by positivity)
  have hsq : ∫ ω, partialDev μ f (m ^ 2) ω ^ 2 ∂μ ≤ (m : ℝ) ^ 2 * M := by
    have := integral_sq_sum_le hf hM (Finset.range (m ^ 2))
    rw [Finset.card_range] at this
    push_cast at this
    exact this
  rw [← ofReal_measureReal (μ := μ)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc μ.real {ω | ε < |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2 - 0|} ≤
        μ.real {ω | ε * (m : ℝ) ^ 2 ≤ |partialDev μ f (m ^ 2) ω|} :=
        measureReal_mono fun ω (hω : ε < |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2 - 0|) => by
          rw [sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 2),
            lt_div_iff₀ (by positivity)] at hω
          exact hω.le
    _ ≤ (∫ ω, partialDev μ f (m ^ 2) ω ^ 2 ∂μ) / (ε * (m : ℝ) ^ 2) ^ 2 := hc
    _ ≤ (m : ℝ) ^ 2 * M / (ε * (m : ℝ) ^ 2) ^ 2 := by gcongr
    _ = M / ε ^ 2 * (1 / (m : ℝ) ^ 2) := by field_simp

/-- The gap statistic `Q_m = Σ_{m² ≤ n < (m+1)²} (S_n − S_{m²})²`. -/
noncomputable def gapSq (μ : Measure Ω) (f : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2

theorem gapSq_nonneg {f : ℕ → Ω → ℝ} (m : ℕ) (ω : Ω) : 0 ≤ gapSq μ f m ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integrable_gapSq [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ)
    (m : ℕ) : Integrable (gapSq μ f m) μ := by
  unfold gapSq
  refine integrable_finsetSum _ fun n hn => ?_
  exact (memLp_partialDev_sub hf (Finset.mem_Ico.1 hn).1).integrable_sq

theorem integral_gapSq_le [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f)
    {M : ℝ} (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) (m : ℕ) :
    ∫ ω, gapSq μ f m ω ∂μ ≤ 6 * M * (m : ℝ) ^ 2 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  unfold gapSq
  rw [integral_finsetSum _ fun n hn =>
    (memLp_partialDev_sub hf.1 (Finset.mem_Ico.1 hn).1).integrable_sq]
  calc ∑ n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2),
        ∫ ω, (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2 ∂μ ≤
        ∑ _n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), 2 * (m : ℝ) * M := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
        refine (integral_sq_partialDev_sub_le hf hM h1).trans ?_
        have : (n : ℝ) - (m ^ 2 : ℕ) ≤ 2 * m := by
          have : n ≤ m ^ 2 + 2 * m := by nlinarith
          have : (n : ℝ) ≤ (m ^ 2 + 2 * m : ℕ) := by exact_mod_cast this
          push_cast at this ⊢; linarith
        exact mul_le_mul_of_nonneg_right this hM0
    _ = (2 * (m : ℝ) + 1) * (2 * m * M) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        congr 1
        rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.le_succ m) 2)]
        push_cast; ring
    _ ≤ 6 * M * (m : ℝ) ^ 2 := by
        have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp
          · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith
        nlinarith

/-- Step 2: `Q_m/m⁴ → 0` a.e. -/
theorem gaps_convAE [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun m ω => gapSq μ f m ω / (m : ℝ) ^ 4) fun _ => 0 := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hM 0)
  refine lemma_14_3 μ fun ε hε => ne_top_of_le_ne_top
    (tsum_ofReal_div_sq_ne_top (6 * M / ε) (by positivity)) (ENNReal.tsum_le_tsum fun m => ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : {ω | ε < |gapSq μ f 0 ω / ((0 : ℕ) : ℝ) ^ 4 - 0|} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, Nat.cast_zero, zero_pow (by norm_num : 4 ≠ 0), div_zero,
        sub_zero, abs_zero, mem_empty_iff_false, iff_false, not_lt]; exact hε.le
    rw [this, measure_empty]; exact zero_le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (gapSq_nonneg (μ := μ)
    (f := f) m)) (integrable_gapSq hf.1 m) (ε * (m : ℝ) ^ 4)
  have hint := integral_gapSq_le hf hM m
  rw [← ofReal_measureReal (μ := μ)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < ε * (m : ℝ) ^ 4 := by positivity
  calc μ.real {ω | ε < |gapSq μ f m ω / (m : ℝ) ^ 4 - 0|} ≤
        μ.real {ω | ε * (m : ℝ) ^ 4 ≤ gapSq μ f m ω} :=
        measureReal_mono fun ω (hω : ε < |gapSq μ f m ω / (m : ℝ) ^ 4 - 0|) => by
          rw [sub_zero, abs_of_nonneg (div_nonneg (gapSq_nonneg m ω) (by positivity)),
            lt_div_iff₀ (by positivity)] at hω
          exact hω.le
    _ ≤ (∫ ω, gapSq μ f m ω ∂μ) / (ε * (m : ℝ) ^ 4) := by
        rw [le_div_iff₀ hpos]; linarith
    _ ≤ 6 * M * (m : ℝ) ^ 2 / (ε * (m : ℝ) ^ 4) := by gcongr
    _ = 6 * M / ε * (1 / (m : ℝ) ^ 2) := by field_simp

theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.2 hn⟩

/-- **Theorem 14.5** (the strong law, reconstructed; see the module docstring). For an uncorrelated
sequence with bounded variances, `(1/n) Σ_{k<n} (fₖ − E fₖ) → 0` almost everywhere. -/
theorem theorem_14_5 [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} (hf : Uncorrelated μ f) {M : ℝ}
    (hM : ∀ k, ∫ ω, centered μ f k ω ^ 2 ∂μ ≤ M) : ConvAE μ (avgDev μ f) fun _ => 0 := by
  filter_upwards [squares_convAE hf hM, gaps_convAE hf hM] with ω hA hB
  set c : ℕ → ℝ := fun m => |partialDev μ f (m ^ 2) ω / (m : ℝ) ^ 2| +
    Real.sqrt (gapSq μ f m ω / (m : ℝ) ^ 4)
  have hc : Tendsto c atTop (𝓝 0) := by
    have h1 := hA.abs
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hB
    simp only [abs_zero, Real.sqrt_zero, Function.comp_def] at h1 h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  refine squeeze_zero_norm' ?_ (hc.comp tendsto_sqrt_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  set m := Nat.sqrt n
  have hm1 : 1 ≤ m := Nat.le_sqrt.2 (by simpa using hn)
  have hmn : m ^ 2 ≤ n := Nat.sqrt_le' n
  have hnm : n < (m + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn' : ((m : ℝ)) ^ 2 ≤ n := by exact_mod_cast hmn
  -- `|S_n − S_{m²}| ≤ √Q_m`
  have hgap : |partialDev μ f n ω - partialDev μ f (m ^ 2) ω| ≤ Real.sqrt (gapSq μ f m ω) :=
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun n =>
      (partialDev μ f n ω - partialDev μ f (m ^ 2) ω) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_Ico.2 ⟨hmn, hnm⟩))
  have hsqrt : Real.sqrt (gapSq μ f m ω / (m : ℝ) ^ 4) =
      Real.sqrt (gapSq μ f m ω) / (m : ℝ) ^ 2 := by
    rw [Real.sqrt_div' _ (by positivity), show (m : ℝ) ^ 4 = ((m : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [Function.comp_apply, Real.norm_eq_abs, avgDev, abs_mul, abs_inv, Nat.abs_cast]
  change (n : ℝ)⁻¹ * |partialDev μ f n ω| ≤ c m
  simp only [c, hsqrt, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)]
  have htri : |partialDev μ f n ω| ≤ |partialDev μ f (m ^ 2) ω| + Real.sqrt (gapSq μ f m ω) := by
    have := abs_sub_abs_le_abs_sub (partialDev μ f n ω) (partialDev μ f (m ^ 2) ω)
    linarith
  calc (n : ℝ)⁻¹ * |partialDev μ f n ω| ≤ ((m : ℝ) ^ 2)⁻¹ * |partialDev μ f n ω| :=
        mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) hn') (abs_nonneg _)
    _ ≤ ((m : ℝ) ^ 2)⁻¹ * (|partialDev μ f (m ^ 2) ω| + Real.sqrt (gapSq μ f m ω)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = _ := by field_simp

end StokeyLucasPrescott.LawsOfLargeNumbers
