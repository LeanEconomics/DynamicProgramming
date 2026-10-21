/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PseudoAtoms.SmallSets

/-!
# Sampled chains (MT §5.5.1)

Meyn and Tweedie, §5.5.1, pp. 115–117. A sampling distribution is a probability `a` on `ℤ₊`,
and `K_a = Σₙ a(n) Pⁿ` (5.43) is `sampledKernel P a` (Chapter 3).

* `IsSamplingDist a`: `Σₙ a(n) = 1`; `diracDist m` (`K_{δ_m} = Pᵐ`, `sampledKernel_diracDist`),
  `geomDist ε` (`K_{a_ε}` is the resolvent, `sampledKernel_geomDist`), `uniformDist N`
  (`a(i) = 1/N` for `1 ≤ i ≤ N`) and `mixDist` (`½(a₁ + a₂)`), all sampling distributions.
* `sampleConv a b = a ∗ b`, the convolution of sampling distributions, and
  `isSamplingDist_sampleConv`; `tsum_sum_antidiagonal`: `Σₙ Σ_{i+j=n} f(i, j) = Σᵢ Σⱼ f(i, j)`.
* **Lemma 5.5.2 (i)** (`lemma_5_5_2_i`, (5.46), p. 116): `K_{a∗b}(x, A) = ∫ K_a(x, dy) K_b(y, A)`,
  that is `K_{a∗b} = K_b ∘ₖ K_a`.
* `SampledAccessible P a A B`, `A ⇝ᵃ B` (5.44), p. 116: `inf_{x ∈ A} K_a(x, B) ≥ δ > 0`.
* **Lemma 5.5.1** (p. 116): `lemma_5_5_1_counterexample` shows that it fails as stated, and
  (5.45) with it, when `a(0) > 0`; `lemma_5_5_1` is the corrected statement for `a(0) = 0`, and
  `lemma_5_5_1_firstHit` the statement for the hitting time `σ_B` (time `0` included) for every
  `a`.
* **Lemma 5.5.2 (ii)** (`lemma_5_5_2_ii`): `A ⇝ᵃ B` and `B ⇝ᵇ C` give `A ⇝^{a∗b} C`.
* **Lemma 5.5.2 (iii)** (`lemma_5_5_2_iii`, (5.47)): `U(x, A) ≥ ∫ U(x, dy) K_a(y, A)`.

**Corrections.** Lemma 5.5.1 and (5.45) are false when `a(0) > 0` (the book's proof identifies
`L(x, B) = Pₓ(τ_B < ∞)` with the probability of ever being in `B`, time `0` included):
`lemma_5_5_1_counterexample`. They hold for `a(0) = 0`, and with `σ_B` in place of `τ_B` for every
`a`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Sampling distributions -/

/-- `a` is a **sampling distribution** (MT p. 115): a probability on `ℤ₊`. -/
def IsSamplingDist (a : ℕ → ℝ≥0∞) : Prop := ∑' n, a n = 1

/-- The point mass `δ_m` at time `m`. -/
noncomputable def diracDist (m : ℕ) (n : ℕ) : ℝ≥0∞ := if n = m then 1 else 0

/-- `δ_m` is a sampling distribution. -/
theorem isSamplingDist_diracDist (m : ℕ) : IsSamplingDist (diracDist m) := by
  unfold IsSamplingDist diracDist
  rw [tsum_ite_eq]

/-- `K_{δ_m} = Pᵐ`: the `δ_m`-sampled chain is the `m`-skeleton (MT p. 116). -/
theorem sampledKernel_diracDist (P : Kernel X X) (m : ℕ) :
    sampledKernel P (diracDist m) = P ^ m := by
  ext x A hA
  rw [sampledKernel_apply P _ x hA]
  unfold diracDist
  simp only [ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq]

/-- The geometric distribution `a_ε(n) = (1 − ε) εⁿ`. -/
noncomputable def geomDist (ε : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := (1 - ε) * ε ^ n

/-- `a_ε` is a sampling distribution for `ε < 1`. -/
theorem isSamplingDist_geomDist {ε : ℝ≥0∞} (hε : ε < 1) : IsSamplingDist (geomDist ε) :=
  tsum_geometric_weights hε

/-- `K_{a_ε}` is the resolvent (MT p. 116). -/
theorem sampledKernel_geomDist (P : Kernel X X) (ε : ℝ≥0∞) :
    sampledKernel P (geomDist ε) = resolvent P ε := rfl

/-- The uniform distribution `a(i) = 1/N` for `1 ≤ i ≤ N` (MT p. 120). -/
noncomputable def uniformDist (N : ℕ) (n : ℕ) : ℝ≥0∞ := if 1 ≤ n ∧ n ≤ N then (N : ℝ≥0∞)⁻¹ else 0

/-- The uniform distribution vanishes off `{1, …, N}`. -/
theorem uniformDist_eq_indicator (N : ℕ) :
    uniformDist N = (Finset.Icc 1 N : Set ℕ).indicator fun _ => (N : ℝ≥0∞)⁻¹ := by
  ext n
  simp [uniformDist, indicator]

/-- `Σ_{n ∈ {1, …, N}} f(n) ≥ ...`: the uniform kernel is the average of `P, …, Pᴺ`. -/
theorem sampledKernel_uniformDist_apply (P : Kernel X X) (N : ℕ) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    sampledKernel P (uniformDist N) x A = (N : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.Icc 1 N, (P ^ n) x A := by
  rw [sampledKernel_apply P _ x hA, Finset.mul_sum, tsum_eq_sum (s := Finset.Icc 1 N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp [uniformDist, hn.1, hn.2]
  · intro n hn
    rw [Finset.mem_Icc] at hn
    simp [uniformDist, hn]

/-- The uniform distribution on `{1, …, N}` is a sampling distribution for `N ≥ 1`. -/
theorem isSamplingDist_uniformDist {N : ℕ} (hN : 1 ≤ N) : IsSamplingDist (uniformDist N) := by
  unfold IsSamplingDist
  rw [uniformDist_eq_indicator, ← sum_eq_tsum_indicator, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, Nat.add_sub_cancel]
  exact ENNReal.mul_inv_cancel (by simp; omega) (by simp)

/-- The uniform distribution has finite mean `Σ i a(i) = (N + 1)/2` (MT p. 120). -/
theorem tsum_mul_uniformDist_ne_top (N : ℕ) :
    ∑' n : ℕ, (n : ℝ≥0∞) * uniformDist N n ≠ ∞ := by
  have : (fun n : ℕ => (n : ℝ≥0∞) * uniformDist N n) =
      (Finset.Icc 1 N : Set ℕ).indicator fun n : ℕ => (n : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ := by
    ext n
    simp [uniformDist, indicator]
  rw [this, ← sum_eq_tsum_indicator]
  refine ENNReal.sum_ne_top.2 fun n hn => ENNReal.mul_ne_top (by simp) ?_
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h] at hn
  · simp; omega

/-- The mixture `½(a₁ + a₂)` of two sampling distributions (MT p. 119). -/
noncomputable def mixDist (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := 2⁻¹ * a n + 2⁻¹ * b n

/-- The mixture is a sampling distribution. -/
theorem isSamplingDist_mixDist {a b : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (hb : IsSamplingDist b) : IsSamplingDist (mixDist a b) := by
  unfold IsSamplingDist mixDist at *
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ha, hb, mul_one,
    ENNReal.inv_two_add_inv_two]

/-- `K_{½(a + b)} = ½ K_a + ½ K_b`. -/
theorem sampledKernel_mixDist_apply (P : Kernel X X) (a b : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) : sampledKernel P (mixDist a b) x A =
      2⁻¹ * sampledKernel P a x A + 2⁻¹ * sampledKernel P b x A := by
  simp only [sampledKernel_apply P _ x hA, mixDist, add_mul, ENNReal.tsum_add, mul_assoc,
    ENNReal.tsum_mul_left]

/-! ### Convolution -/

/-- The convolution `a ∗ b (n) = Σ_{i+j=n} a(i) b(j)` (MT p. 116). -/
noncomputable def sampleConv (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Summation over antidiagonals: `Σₙ Σ_{i+j=n} f(i, j) = Σᵢ Σⱼ f(i, j)`. -/
theorem tsum_sum_antidiagonal (f : ℕ × ℕ → ℝ≥0∞) :
    ∑' n, ∑ p ∈ Finset.antidiagonal n, f p = ∑' i, ∑' j, f (i, j) := by
  rw [← ENNReal.tsum_prod', ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype]
  rfl

/-- The convolution of sampling distributions is a sampling distribution. -/
theorem isSamplingDist_sampleConv {a b : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (hb : IsSamplingDist b) : IsSamplingDist (sampleConv a b) := by
  unfold IsSamplingDist sampleConv at *
  rw [tsum_sum_antidiagonal (fun p => a p.1 * b p.2)]
  simp_rw [ENNReal.tsum_mul_left, hb, mul_one, ha]

/-- **Lemma 5.5.2 (i)**, the generalized Chapman–Kolmogorov equations (5.46), MT p. 116:
`K_{a∗b}(x, A) = ∫ K_a(x, dy) K_b(y, A)`. -/
theorem lemma_5_5_2_i (P : Kernel X X) (a b : ℕ → ℝ≥0∞) (x : X) {A : Set X}
    (hA : MeasurableSet A) :
    sampledKernel P (sampleConv a b) x A = ∫⁻ y, sampledKernel P b y A ∂sampledKernel P a x := by
  rw [sampledKernel_apply P _ x hA]
  simp_rw [sampleConv, Finset.sum_mul]
  have h1 : ∀ n, ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 * (P ^ n) x A =
      ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 * (P ^ (p.1 + p.2)) x A := fun n =>
    Finset.sum_congr rfl fun p hp => by rw [Finset.mem_antidiagonal.1 hp]
  simp_rw [h1]
  rw [tsum_sum_antidiagonal (fun p => a p.1 * b p.2 * (P ^ (p.1 + p.2)) x A)]
  change _ = ∫⁻ y, sampledKernel P b y A ∂(Measure.sum fun n => a n • (P ^ n) x)
  rw [lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure]
  simp_rw [sampledKernel_apply P _ _ hA]
  rw [lintegral_tsum fun j => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable,
    smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA),
    ← Kernel.pow_add_apply_eq_lintegral P i j x hA]
  ring

/-- Lemma 5.5.2 (i) as an identity of kernels: `K_{a∗b} = K_b ∘ₖ K_a`. -/
theorem sampledKernel_sampleConv (P : Kernel X X) (a b : ℕ → ℝ≥0∞) :
    sampledKernel P (sampleConv a b) = sampledKernel P b ∘ₖ sampledKernel P a := by
  ext x A hA
  rw [lemma_5_5_2_i P a b x hA, Kernel.comp_apply' _ _ _ hA]

/-! ### Uniform accessibility using a sampling distribution -/

/-- `A ⇝ᵃ B` (5.44), MT p. 116: `K_a(x, B) ≥ δ` for all `x ∈ A`, for some `δ > 0`. -/
def SampledAccessible (P : Kernel X X) (a : ℕ → ℝ≥0∞) (A B : Set X) : Prop :=
  ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ A, δ ≤ sampledKernel P a x B

/-- (5.45), corrected: if `a(0) = 0`, then `K_a(x, B) ≤ L(x, B)`. -/
theorem sampledKernel_le_hitProb (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) (ha0 : a 0 = 0) {B : Set X} (hB : MeasurableSet B) (x : X) :
    sampledKernel P a x B ≤ hitProb P B x := by
  rw [sampledKernel_apply P a x hB]
  calc ∑' n, a n * (P ^ n) x B ≤ ∑' n, a n * hitProb P B x := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases n with _ | n
        · rw [ha0, zero_mul, zero_mul]
        · gcongr
          exact pow_le_hitProb P hB n x
    _ = hitProb P B x := by rw [ENNReal.tsum_mul_right, ha, one_mul]

/-- **Lemma 5.5.1**, corrected (MT p. 116): if `a(0) = 0` and `A ⇝ᵃ B`, then `A ⇝ B`. -/
theorem lemma_5_5_1 (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a)
    (ha0 : a 0 = 0) {A B : Set X} (hB : MeasurableSet B) (h : SampledAccessible P a A B) :
    UnifAccessible P A B := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun x hx => (h x hx).trans (sampledKernel_le_hitProb P ha ha0 hB x)⟩

/-- **Lemma 5.5.1** for the hitting time `σ_B` (time `0` included), for every sampling
distribution: `K_a(x, B) ≤ Pₓ(Φₙ ∈ B for some n ≥ 0)`, so `A ⇝ᵃ B` gives a uniform lower bound on
the probability of ever being in `B`. -/
theorem lemma_5_5_1_firstHit (P : Kernel X X) [IsMarkovKernel P] {a : ℕ → ℝ≥0∞}
    (ha : IsSamplingDist a) {B : Set X} (hB : MeasurableSet B) (x : X) :
    sampledKernel P a x B ≤ pathKernel P x {ω | ∃ n, ω n ∈ B} := by
  rw [sampledKernel_apply P a x hB]
  calc ∑' n, a n * (P ^ n) x B ≤ ∑' n, a n * pathKernel P x {ω | ∃ n, ω n ∈ B} := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        gcongr
        rw [← pathKernel_coord_mem P x n hB]
        exact measure_mono fun ω hω => ⟨n, hω⟩
    _ = pathKernel P x {ω | ∃ n, ω n ∈ B} := by rw [ENNReal.tsum_mul_right, ha, one_mul]

/-- The chain on `Bool` that jumps to `true` from every state. -/
noncomputable def toTrueKernel : Kernel Bool Bool := Kernel.const Bool (Measure.dirac true)

/-- `toTrueKernel` is a transition kernel. -/
theorem isMarkovKernel_toTrueKernel : IsMarkovKernel toTrueKernel := by
  unfold toTrueKernel; infer_instance

/-- **Correction to Lemma 5.5.1 and (5.45)** (MT p. 116): with `a = δ₀` (so `a(0) > 0`), the
chain that jumps to `true` from every state has `{false} ⇝ᵃ {false}`, since `K_{δ₀}(x, ·) = δₓ`,
but `L(false, {false}) = 0`: the chain never returns to `false`. -/
theorem lemma_5_5_1_counterexample :
    haveI := isMarkovKernel_toTrueKernel
    SampledAccessible toTrueKernel (diracDist 0) {false} {false} ∧
      ¬ UnifAccessible toTrueKernel {false} {false} := by
  have := isMarkovKernel_toTrueKernel
  refine ⟨⟨1, one_pos, fun x hx => ?_⟩, ?_⟩
  · rw [mem_singleton_iff.1 hx, sampledKernel_diracDist, pow_zero_apply]
    simp
  · rintro ⟨δ, hδ, h⟩
    have h0 : hitProb toTrueKernel {false} false = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := (hitProb_pos_iff toTrueKernel (measurableSet_singleton false) false).1
        (pos_iff_ne_zero.2 hne)
      rw [pow_succ_apply' _ n false (measurableSet_singleton false)] at hn
      simp [toTrueKernel] at hn
    exact hδ.ne' (le_antisymm ((h false rfl).trans h0.le) zero_le)

/-- **Lemma 5.5.2 (ii)** (MT p. 116): if `A ⇝ᵃ B` and `B ⇝ᵇ C` then `A ⇝^{a∗b} C`. -/
theorem lemma_5_5_2_ii (P : Kernel X X) {a b : ℕ → ℝ≥0∞} {A B C : Set X}
    (hC : MeasurableSet C) (hab : SampledAccessible P a A B)
    (hbc : SampledAccessible P b B C) : SampledAccessible P (sampleConv a b) A C := by
  obtain ⟨δa, hδa, ha⟩ := hab
  obtain ⟨δb, hδb, hb⟩ := hbc
  refine ⟨δa * δb, ENNReal.mul_pos hδa.ne' hδb.ne', fun x hx => ?_⟩
  rw [lemma_5_5_2_i P a b x hC]
  calc δa * δb ≤ sampledKernel P a x B * δb := by gcongr; exact ha x hx
    _ = ∫⁻ _ in B, δb ∂sampledKernel P a x := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in B, sampledKernel P b y C ∂sampledKernel P a x :=
        setLIntegral_mono (Kernel.measurable_coe _ hC) fun y hy => hb y hy
    _ ≤ ∫⁻ y, sampledKernel P b y C ∂sampledKernel P a x := setLIntegral_le_lintegral _ _

/-- **Lemma 5.5.2 (iii)** (5.47), MT p. 116: `U(x, A) ≥ ∫ U(x, dy) K_a(y, A)`. -/
theorem lemma_5_5_2_iii (P : Kernel X X) {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) (x : X)
    {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ y, sampledKernel P a y A ∂potKernel P x ≤ potKernel P x A := by
  have hU : potKernel P x = Measure.sum fun m => (P ^ (m + 1)) x := by
    rw [potKernel, Kernel.sum_apply]
  rw [hU, lintegral_sum_measure, Measure.sum_apply _ hA]
  simp_rw [sampledKernel_apply P a _ hA]
  calc ∑' m, ∫⁻ y, ∑' n, a n * (P ^ n) y A ∂(P ^ (m + 1)) x
      = ∑' m, ∑' n, a n * (P ^ (m + 1 + n)) x A := by
        refine tsum_congr fun m => ?_
        rw [lintegral_tsum fun n => ((Kernel.measurable_coe _ hA).const_mul _).aemeasurable]
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (Kernel.measurable_coe _ hA),
          Kernel.pow_add_apply_eq_lintegral P (m + 1) n x hA]
    _ = ∑' n, a n * ∑' m, (P ^ (m + n + 1)) x A := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun n => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun m => ?_
        rw [show m + 1 + n = m + n + 1 by omega]
    _ ≤ ∑' n, a n * ∑' k, (P ^ (k + 1)) x A := by
        refine ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl ?_
        exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun m => m + n)
          (add_left_injective n) (fun k => (P ^ (k + 1)) x A)
    _ = ∑' k, (P ^ (k + 1)) x A := by rw [ENNReal.tsum_mul_right, ha, one_mul]

end MeynTweedie.PseudoAtoms
