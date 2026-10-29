/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TransienceRecurrence.CountableClassification
import TransienceRecurrence.ModelRandomWalk
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Random walk on `ℤ` with mean-zero increments (MT Theorem 8.1.5)

Meyn and Tweedie, Theorem 8.1.5, pp. 176–177. The walk is `randomWalkKernel Γ` on `ℤ`, with an
increment law `Γ` of finite mean `∫ w Γ(dw) = 0`; there is no bound on the range.

* `randomWalk_pow_eq_infinitePi`: `Pⁿ(0, A) = P(W₁ + ⋯ + Wₙ ∈ A)` for i.i.d. `Wᵢ ~ Γ`
  (`law_orbit`).
* `randomWalk_wlln` (8.14), the weak law of large numbers: `Pⁿ(0, A(an)) → 1`, in the form
  `Pⁿ(0, {|y| ≤ an}) ≥ ½` for large `n`; it is derived from Mathlib's strong law
  (`ProbabilityTheory.strong_law_ae`) through convergence in measure.
* `randomWalk_pow_translate`: translation invariance, `Pⁿ(x, {0}) = Pⁿ(0, {−x})`.
* `sum_pow_le_sum_pow_zero` (8.15): `Σ_{m=1}^N Pᵐ(x, 0) ≤ Σ_{j=0}^N Pʲ(0, 0)`, from the strong
  Markov property at the first entrance to `0`.
* **Theorem 8.1.5** (`theorem_8_1_5`): an irreducible random walk on `ℤ` whose increments have
  mean zero is recurrent. The proof is (8.16)–(8.17): `Σ_{m ≤ N} Pᵐ(0, 0)` is at least
  `(2aN + 3)⁻¹ Σ_{j ≤ N} Pʲ(0, A(aj)) ≈ (2a)⁻¹`, for every `a > 0`.

**Corrections.** None. The weak law (8.14) is stated by the book without proof; here it is proved
from the strong law.
-/

namespace MeynTweedie.TransienceRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable (Γ : Measure ℤ) [IsProbabilityMeasure Γ]

/-- The `n`-step law from `0` is the law of `W₁ + ⋯ + Wₙ` under the i.i.d. product measure. -/
theorem randomWalk_pow_eq_infinitePi (n : ℕ) (A : Set ℤ) :
    (randomWalkKernel Γ ^ n) 0 A =
      Measure.infinitePi (fun _ : ℕ => Γ) {ω | ∑ i ∈ Finset.range n, ω (i + 1) ∈ A} := by
  have h := law_orbit Γ (measurable_add_step (G := ℤ)) 0 n
  rw [← randomWalkKernel] at h
  have hfun : (fun ω : ℕ → ℤ => orbit (fun p : ℤ × ℤ => p.1 + p.2) 0 ω n) =
      fun ω => ∑ i ∈ Finset.range n, ω (i + 1) := by
    funext ω; rw [orbit_randomWalk, zero_add]
  have hm : Measurable fun ω : ℕ → ℤ => ∑ i ∈ Finset.range n, ω (i + 1) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  rw [hfun] at h
  rw [← h, Measure.map_apply hm (measurableSet_of_countable A)]
  rfl

/-- Translation invariance: `Pⁿ(x, {0}) = Pⁿ(0, {−x})`. -/
theorem randomWalk_pow_translate (n : ℕ) (x : ℤ) :
    (randomWalkKernel Γ ^ n) x {0} = (randomWalkKernel Γ ^ n) 0 {-x} := by
  rw [randomWalkKernel_pow_apply, randomWalkKernel_pow_apply,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext w
  simp only [mem_preimage, mem_singleton_iff, zero_add]
  omega

/-- **The weak law of large numbers (8.14)** (MT p. 176): if `Γ` has a finite mean `0`, then for
every `a > 0`, `Pⁿ(0, {y : |y| ≤ an}) ≥ ½` for all large `n`. -/
theorem randomWalk_wlln (hint : Integrable (fun z : ℤ => (z : ℝ)) Γ)
    (hmean : ∫ z, (z : ℝ) ∂Γ = 0) {a : ℝ} (ha : 0 < a) :
    ∃ k₀, ∀ n : ℕ, k₀ ≤ n → 2⁻¹ ≤ (randomWalkKernel Γ ^ n) 0 {y | |(y : ℝ)| ≤ a * (n : ℝ)} := by
  set μ := Measure.infinitePi fun _ : ℕ => Γ
  set Y : ℕ → (ℕ → ℤ) → ℝ := fun i ω => (ω i : ℝ)
  set X : ℕ → (ℕ → ℤ) → ℝ := fun i ω => Y (i + 1) ω
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (measurable_pi_apply i)
  have hind : iIndepFun Y μ :=
    iIndepFun_infinitePi (P := fun _ => Γ) (X := fun _ z => (z : ℝ))
      fun _ => measurable_of_countable _
  have hmap : ∀ i, μ.map (Y i) = Γ.map fun z : ℤ => (z : ℝ) := fun i => by
    change μ.map ((fun z : ℤ => (z : ℝ)) ∘ fun ω => ω i) = _
    rw [← Measure.map_map (μ := μ) (g := fun z : ℤ => (z : ℝ)) (f := fun ω : ℕ → ℤ => ω i)
      (measurable_of_countable _) (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ⟨(hYm _).aemeasurable, (hYm _).aemeasurable, by rw [hmap, hmap]⟩
  have hX0 : Integrable (X 0) μ := by
    have h1 : Integrable (fun z : ℤ => (z : ℝ)) (μ.map fun ω => ω 1) := by
      rw [Measure.infinitePi_map_eval]; exact hint
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_pi_apply 1).aemeasurable).1 h1
  have hE : ∫ ω, X 0 ω ∂μ = 0 := by
    change ∫ ω, (fun z : ℤ => (z : ℝ)) (ω 1) ∂μ = 0
    rw [← integral_map (measurable_pi_apply 1).aemeasurable
      (measurable_of_countable (fun z : ℤ => (z : ℝ))).aestronglyMeasurable,
      Measure.infinitePi_map_eval]
    exact hmean
  have hslln := strong_law_ae X hX0 (fun i j hij => hind.indepFun (by omega)) hident
  rw [hE] at hslln
  have hmeas := tendstoInMeasure_of_tendsto_ae (μ := μ) (f := fun n ω =>
    (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) (g := fun _ => 0)
    (fun n => (Measurable.const_smul (g := fun ω : ℕ → ℤ => ∑ i ∈ Finset.range n, X i ω)
      (Finset.measurable_sum _ fun i _ => hYm (i + 1)) ((n : ℝ)⁻¹)).aestronglyMeasurable)
    hslln (ENNReal.ofReal a) (ENNReal.ofReal_pos.2 ha)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hmeas.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 2⁻¹
    by simp)))
  refine ⟨max k₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hsmall := hk₀ n (le_of_max_le_left hn)
  rw [randomWalk_pow_eq_infinitePi]
  have hfm : Measurable fun ω : ℕ → ℤ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω :=
    Measurable.const_smul (g := fun ω : ℕ → ℤ => ∑ i ∈ Finset.range n, X i ω)
      (Finset.measurable_sum _ fun i _ => hYm (i + 1)) ((n : ℝ)⁻¹)
  set E := {ω : ℕ → ℤ | ENNReal.ofReal a ≤ edist ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) 0}
    with hEdef
  have hEm : MeasurableSet E := measurableSet_le measurable_const (hfm.edist measurable_const)
  have hsub : Eᶜ ⊆ {ω | ∑ i ∈ Finset.range n, ω (i + 1) ∈ {y : ℤ | |(y : ℝ)| ≤ a * n}} := by
    intro ω hω
    simp only [hEdef, mem_compl_iff, mem_ofPred_eq, not_le, edist_dist, Real.dist_eq,
      sub_zero] at hω
    rw [ENNReal.ofReal_lt_ofReal_iff ha] at hω
    simp only [mem_ofPred_eq, Int.cast_sum]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [smul_eq_mul, abs_mul, abs_inv, abs_of_pos hnpos, inv_mul_lt_iff₀ hnpos] at hω
    exact (by simpa [X, Y, mul_comm] using hω.le)
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - μ E := tsub_le_tsub_left hsmall.le 1
    _ = μ Eᶜ := (prob_compl_eq_one_sub hEm).symm
    _ ≤ _ := measure_mono hsub

/-- (8.15), MT p. 177: `Σ_{m=1}^N Pᵐ(x, 0) ≤ 1 + Σ_{m=1}^N Pᵐ(0, 0) = Σ_{j=0}^N Pʲ(0, 0)`. -/
theorem sum_pow_le_sum_pow_zero {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Kernel X X) [IsMarkovKernel P] (x z : X) (N : ℕ) :
    ∑ n ∈ Finset.range N, (P ^ (n + 1)) x {z} ≤
      1 + ∑ n ∈ Finset.range N, (P ^ (n + 1)) z {z} := by
  have hz := measurableSet_singleton z
  rw [← lintegral_occTimeN P x hz N, ← lintegral_occTimeN P z hz N]
  calc ∫⁻ ω, occTimeN {z} N ω ∂pathKernel P x
      ≤ hitProb P {z} x * (1 + ∫⁻ ω, occTimeN {z} N ω ∂pathKernel P z) :=
        lintegral_occTimeN_le_hitProb P x hz N fun y hy => by rw [mem_singleton_iff.1 hy]
    _ ≤ 1 * (1 + ∫⁻ ω, occTimeN {z} N ω ∂pathKernel P z) :=
        mul_le_mul' (hitProb_le_one P _ x) le_rfl
    _ = _ := one_mul _

/-- **Theorem 8.1.5** (MT p. 176): an irreducible random walk on `ℤ` whose increment law has
finite mean zero is recurrent. -/
theorem theorem_8_1_5 (hint : Integrable (fun z : ℤ => (z : ℝ)) Γ)
    (hmean : ∫ z, (z : ℝ) ∂Γ = 0)
    (hirr : haveI := isMarkovKernel_randomWalkKernel Γ; IsIrreducibleChain (randomWalkKernel Γ)) :
    haveI := isMarkovKernel_randomWalkKernel Γ
    IsRecurrentChain (randomWalkKernel Γ) Measure.count := by
  have := isMarkovKernel_randomWalkKernel Γ
  set P := randomWalkKernel Γ
  have hpow := isMarkovKernel_pow P
  -- `U(0, 0) = ∞`
  have hU : potKernel P 0 {0} = ∞ := by
    by_contra hfin
    set K : ℝ := (1 + potKernel P 0 {0}).toReal with hK
    have hKfin : 1 + potKernel P 0 {0} ≠ ∞ := by simp [hfin]
    have hK1 : 1 ≤ K := by
      rw [hK, ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hKfin le_self_add
    set a : ℝ := 1 / (8 * K) with ha
    have ha0 : 0 < a := by positivity
    obtain ⟨k₀, hk₀⟩ := randomWalk_wlln Γ hint hmean ha0
    -- the total mass of `[−M, M]` along the path
    set N : ℕ := 2 * k₀ + ⌈24 * K⌉₊ + 1 with hN
    set M : ℕ := ⌈a * N⌉₊ with hM
    have hupper : ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 (Finset.Icc (-(M : ℤ)) M : Set ℤ) ≤
        (2 * M + 1 : ℕ) * (1 + potKernel P 0 {0}) := by
      have hG : ∀ y : ℤ, ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 {y} ≤ 1 + potKernel P 0 {0} :=
        fun y => by
          calc ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 {y}
              = ∑ n ∈ Finset.range N, (P ^ (n + 1)) (-y) {0} :=
                Finset.sum_congr rfl fun n _ => by rw [randomWalk_pow_translate, neg_neg]
            _ ≤ 1 + ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 {0} := sum_pow_le_sum_pow_zero P _ 0 N
            _ ≤ 1 + potKernel P 0 {0} :=
                add_le_add le_rfl (sum_pow_le_potKernel P 0 (measurableSet_singleton 0) N)
      calc ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 (Finset.Icc (-(M : ℤ)) M : Set ℤ)
          = ∑ n ∈ Finset.range N, ∑ y ∈ Finset.Icc (-(M : ℤ)) M, (P ^ (n + 1)) 0 {y} :=
            Finset.sum_congr rfl fun n _ => sum_measure_singleton.symm
        _ = ∑ y ∈ Finset.Icc (-(M : ℤ)) M, ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 {y} :=
            Finset.sum_comm
        _ ≤ ∑ _y ∈ Finset.Icc (-(M : ℤ)) M, (1 + potKernel P 0 {0}) := Finset.sum_le_sum
            fun y _ => hG y
        _ = (2 * M + 1 : ℕ) * (1 + potKernel P 0 {0}) := by
            rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
            congr 2
            omega
    have hlower : ((N - k₀ : ℕ) : ℝ≥0∞) * 2⁻¹ ≤
        ∑ n ∈ Finset.range N, (P ^ (n + 1)) 0 (Finset.Icc (-(M : ℤ)) M : Set ℤ) := by
      calc ((N - k₀ : ℕ) : ℝ≥0∞) * 2⁻¹ = ∑ _n ∈ Finset.Ico k₀ N, (2⁻¹ : ℝ≥0∞) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ ∑ n ∈ Finset.Ico k₀ N, (P ^ (n + 1)) 0 (Finset.Icc (-(M : ℤ)) M : Set ℤ) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' := Finset.mem_Ico.1 hn
            refine (hk₀ (n + 1) (by omega)).trans (measure_mono fun y hy => ?_)
            simp only [mem_ofPred_eq] at hy
            have h1 : a * ((n + 1 : ℕ) : ℝ) ≤ M := by
              calc a * ((n + 1 : ℕ) : ℝ) ≤ a * N := by
                    gcongr; exact_mod_cast hn'.2
                _ ≤ M := Nat.le_ceil _
            rw [Finset.coe_Icc, mem_Icc]
            have h2 : |(y : ℝ)| ≤ M := hy.trans h1
            rw [abs_le] at h2
            constructor <;> [exact_mod_cast (by linarith : (-(M : ℝ)) ≤ y);
              exact_mod_cast h2.2]
        _ ≤ _ := Finset.sum_le_sum_of_subset (fun n hn => by
            simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega)
    have hineq := (hlower.trans hupper)
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKfin) hineq
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, ← hK] at hreal
    have hMle : (M : ℝ) ≤ a * N + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hNk : ((N - k₀ : ℕ) : ℝ) = N - k₀ := by rw [Nat.cast_sub (by omega)]
    have hNdef : (N : ℝ) = 2 * k₀ + ⌈24 * K⌉₊ + 1 := by rw [hN]; push_cast; ring
    have hceil : 24 * K ≤ ⌈24 * K⌉₊ := Nat.le_ceil _
    rw [hNk] at hreal
    have hcast : ((2 * M + 1 : ℕ) : ℝ) = 2 * M + 1 := by push_cast; ring
    rw [hcast] at hreal
    have haK : a * K = 1 / 8 := by rw [ha]; field_simp
    have h1 : (2 * (M : ℝ) + 1) * K ≤ (2 * (a * N + 1) + 1) * K := by
      have : 0 ≤ K := by linarith
      gcongr
    have h2 : (2 * (a * N + 1) + 1) * K = N / 4 + 3 * K := by
      have : a * N * K = (a * K) * N := by ring
      nlinarith [this, haK]
    have hk0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
    linarith
  -- hence every state is recurrent
  rcases theorem_8_1_2 P hirr with h | h
  · exact absurd hU (h 0)
  · exact (isRecurrentChain_count_iff P hirr).2 h

end MeynTweedie.TransienceRecurrence
