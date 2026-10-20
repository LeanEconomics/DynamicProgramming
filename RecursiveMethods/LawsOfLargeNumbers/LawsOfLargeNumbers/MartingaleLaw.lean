/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LawsOfLargeNumbers.Uncorrelated

/-!
# A strong law for martingale differences: Theorem 14.6

SLP §14.1, p. 424. Let `𝒜₀ ⊆ 𝒜₁ ⊆ ⋯ ⊆ 𝓕` be σ-algebras with `fₖ` `𝒜ₖ`-measurable, and
`φₖ = E(fₖ | 𝒜ₖ₋₁)`. If `E[(fₖ − φₖ)²] ≤ M` for `k ≥ 1`, then `(1/n) Σ_{k=1}^n (fₖ − φₖ) → 0` a.e.

The proof is the book's. The differences `gₖ = fₖ − φₖ` have conditional mean zero,
`E(gₖ | 𝒜ₖ₋₁) = 0` (`condExp_diff_ae_eq_zero`). For `j < k` the factor `gⱼ` is
`𝒜ₖ₋₁`-measurable, so it can be taken out of `E(gⱼ gₖ | 𝒜ₖ₋₁)`. Hence `E(gⱼ gₖ) = 0` and the
`gₖ` are uncorrelated (`uncorrelated_diff`). Theorem 14.5 then applies.

**Correction.** `E(fₖ | 𝒜ₖ₋₁)` needs `fₖ` integrable, which the book does not assume. Also
`E[(fₖ − φₖ)²] < M` must be read with `fₖ − φₖ ∈ L²`; for a Bochner integral, the bound would
otherwise hold vacuously for a non-integrable square. We assume `fₖ ∈ L²` (then
`φₖ ∈ L²`). Condition (c) involves `𝒜ₖ₋₁`, so it is required for `k ≥ 1` only.

Indices are shifted to avoid `k − 1`: the `k`-th difference is
`f (k + 1) − E(f (k + 1) | 𝒜 k)`, `k = 0, …, n − 1`.
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The martingale differences `gₖ = f_{k+1} − E(f_{k+1} | 𝒜ₖ)`. -/
noncomputable def mgDiff (μ : Measure Ω) (𝒜 : ℕ → MeasurableSpace Ω) (f : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → ℝ :=
  f (k + 1) - μ[f (k + 1) | 𝒜 k]

theorem memLp_mgDiff [IsFiniteMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) : MemLp (mgDiff μ 𝒜 f k) 2 μ :=
  (hf (k + 1)).sub ((hf (k + 1)).condExp one_le_two)

/-- `E(gₖ | 𝒜ₖ) = 0` a.e. -/
theorem condExp_diff_ae_eq_zero [IsFiniteMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    μ[mgDiff μ 𝒜 f k | 𝒜 k] =ᵐ[μ] 0 := by
  have hi : Integrable (f (k + 1)) μ := (hf (k + 1)).integrable one_le_two
  filter_upwards [condExp_sub hi integrable_condExp (𝒜 k)] with ω hω
  rw [mgDiff, hω, Pi.sub_apply,
    condExp_of_stronglyMeasurable (h𝒜le k) stronglyMeasurable_condExp integrable_condExp]
  simp

/-- `gⱼ` is `𝒜ₖ`-measurable for `j < k`. -/
theorem stronglyMeasurable_mgDiff {𝒜 : ℕ → MeasurableSpace Ω} (h𝒜 : Monotone 𝒜)
    {f : ℕ → Ω → ℝ} (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) {j k : ℕ} (hjk : j < k) :
    StronglyMeasurable[𝒜 k] (mgDiff μ 𝒜 f j) :=
  ((hfm (j + 1)).mono (h𝒜 hjk)).sub (stronglyMeasurable_condExp.mono (h𝒜 hjk.le))

/-- `E(gⱼ gₖ) = 0` for `j < k`. -/
theorem integral_mgDiff_mul [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜 : Monotone 𝒜) (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ}
    (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) (hf : ∀ k, MemLp (f k) 2 μ) {j k : ℕ}
    (hjk : j < k) : ∫ ω, mgDiff μ 𝒜 f j ω * mgDiff μ 𝒜 f k ω ∂μ = 0 := by
  have hprod : Integrable (mgDiff μ 𝒜 f j * mgDiff μ 𝒜 f k) μ :=
    (memLp_mgDiff hf j).integrable_mul (memLp_mgDiff hf k)
  have hk : Integrable (mgDiff μ 𝒜 f k) μ := (memLp_mgDiff hf k).integrable one_le_two
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝒜 k)
    (stronglyMeasurable_mgDiff h𝒜 hfm hjk) hprod hk
  have h0 := condExp_diff_ae_eq_zero h𝒜le hf k
  have : ∫ ω, (μ[mgDiff μ 𝒜 f j * mgDiff μ 𝒜 f k | 𝒜 k]) ω ∂μ = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hpull, h0] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]
  rw [integral_condExp (h𝒜le k)] at this
  exact this

/-- `E(gₖ) = 0`. -/
theorem integral_mgDiff [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (k : ℕ) :
    ∫ ω, mgDiff μ 𝒜 f k ω ∂μ = 0 := by
  rw [← integral_condExp (h𝒜le k), integral_eq_zero_of_ae (condExp_diff_ae_eq_zero h𝒜le hf k)]

/-- The martingale differences are uncorrelated. -/
theorem uncorrelated_diff [IsProbabilityMeasure μ] {𝒜 : ℕ → MeasurableSpace Ω}
    (h𝒜 : Monotone 𝒜) (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ}
    (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k)) (hf : ∀ k, MemLp (f k) 2 μ) :
    Uncorrelated μ (mgDiff μ 𝒜 f) := by
  refine ⟨memLp_mgDiff hf, fun j k hjk => ?_⟩
  rw [integral_mgDiff h𝒜le hf j, zero_mul]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact integral_mgDiff_mul h𝒜 h𝒜le hfm hf h
  · simp_rw [mul_comm (mgDiff μ 𝒜 f j _)]
    exact integral_mgDiff_mul h𝒜 h𝒜le hfm hf h

/-- **Theorem 14.6.** Let `𝒜ₖ` be increasing sub-σ-algebras, `fₖ` `𝒜ₖ`-measurable and in `L²`,
and `E[(f_{k+1} − E(f_{k+1} | 𝒜ₖ))²] ≤ M` for all `k`. Then
`(1/n) Σ_{k=0}^{n−1} [f_{k+1} − E(f_{k+1} | 𝒜ₖ)] → 0` a.e. (the book's `Σ_{k=1}^n`). -/
theorem theorem_14_6 [IsProbabilityMeasure μ] (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : Monotone 𝒜)
    (h𝒜le : ∀ k, 𝒜 k ≤ mΩ) {f : ℕ → Ω → ℝ} (hfm : ∀ k, StronglyMeasurable[𝒜 k] (f k))
    (hf : ∀ k, MemLp (f k) 2 μ) {M : ℝ}
    (hM : ∀ k, ∫ ω, (f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω) ^ 2 ∂μ ≤ M) :
    ConvAE μ (fun n ω => (n : ℝ)⁻¹ *
      ∑ k ∈ Finset.range n, (f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω)) fun _ => 0 := by
  have hc : ∀ k ω, centered μ (mgDiff μ 𝒜 f) k ω = f (k + 1) ω - μ[f (k + 1) | 𝒜 k] ω :=
    fun k ω => by rw [centered, integral_mgDiff h𝒜le hf k, sub_zero]; rfl
  have := theorem_14_5 (uncorrelated_diff h𝒜 h𝒜le hfm hf) (M := M) fun k => by
    simp_rw [hc]; exact hM k
  filter_upwards [this] with ω h
  simpa only [avgDev, hc] using h

end StokeyLucasPrescott.LawsOfLargeNumbers
