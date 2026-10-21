/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.SampledChains
import HarrisRecurrence.Cycles

/-!
# Petite sets (MT §5.5.2–5.5.3)

Meyn and Tweedie, §5.5.2–5.5.3, pp. 117–121.

* `IsPetiteSet P a ν C` (p. 117): `C` is `ν_a`-petite, `K_a(x, ·) ≥ ν_a` on `C` for a sampling
  distribution `a` and a nonzero `ν_a`; `IsPetite P C`.
* **Proposition 5.5.3** (`proposition_5_5_3`, p. 118): a `ν_m`-small set is `ν_{δ_m}`-petite.
* `smul_le_comp_of_le_on`: `μ(C) ν ≤ μK` when `K(y, ·) ≥ ν` on `C`; `lintegral_pos_of_pos`.
* **Proposition 5.5.4** (p. 118): (i) `proposition_5_5_4_i`, if `A` is `ν_a`-petite and `D ⇝ᵇ A`
  then `D` is petite for `b ∗ a`, with a multiple of `ν_a`; (ii) `proposition_5_5_4_ii`, the
  petite measure of a petite set in `B⁺(X)` is an irreducibility measure.
* **Proposition 5.5.5** (p. 118), on a countably generated space: (i) `proposition_5_5_5_i`,
  every petite set is `ψ_b`-petite for a maximal irreducibility measure `ψ_b`; (ii)
  `proposition_5_5_5_ii`, the union of two petite sets is petite; (iii) `proposition_5_5_5_iii`,
  `K_c(x, ·) ≥ s(x) ψ_c` with `s > 0` measurable and `ψ_c` maximal, and
  `proposition_5_5_5_iii_cover`: `X` is the increasing union of the `ψ_c`-petite sets
  `{s ≥ (n + 1)⁻¹}`.
* **Proposition 5.5.6 (i)** (`proposition_5_5_6_i`, p. 120): a petite set is petite for a uniform
  sampling distribution on `{1, …, N}` (which has finite mean) and for every geometric `a_ε`.
* **Theorem 5.5.7** (`theorem_5_5_7`, p. 120): for an aperiodic `ψ`-irreducible chain on a
  countably generated space, every petite set is small.

**Corrections and hypotheses.** Propositions 5.5.5–5.5.6 and Theorem 5.5.7 use the existence of a
small set in `B⁺(X)` (Theorem 5.2.2), hence a countably generated `B(X)`. In the proof of
Proposition 5.5.6 (i) the book's bound `Σ_{k ≤ N} Pᵏ(x, A) ≥ ½ ψ_b(A)` follows from a tail bound
on `b`, which is how it is proved here.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- `C` is **`ν_a`-petite** (MT p. 117): `a` is a sampling distribution, `ν ≠ 0`, and
`K_a(x, ·) ≥ ν` for every `x ∈ C`. -/
def IsPetiteSet (P : Kernel X X) (a : ℕ → ℝ≥0∞) (ν : Measure X) (C : Set X) : Prop :=
  MeasurableSet C ∧ IsSamplingDist a ∧ ν ≠ 0 ∧ ∀ x ∈ C, ν ≤ sampledKernel P a x

/-- `C` is **petite** if it is `ν_a`-petite for some `a` and `ν`. -/
def IsPetite (P : Kernel X X) (C : Set X) : Prop := ∃ a ν, IsPetiteSet P a ν C

/-- **Proposition 5.5.3** (MT p. 118): a `ν_m`-small set is `ν_{δ_m}`-petite. -/
theorem proposition_5_5_3 {P : Kernel X X} {m : ℕ} {ν : Measure X} {C : Set X}
    (h : IsSmallSet P m ν C) : IsPetiteSet P (diracDist m) ν C :=
  ⟨h.1, isSamplingDist_diracDist m, h.2.2.1, fun x hx => by
    rw [sampledKernel_diracDist]; exact h.2.2.2 x hx⟩

/-- `μ(C) ν ≤ μK` when `K(y, ·) ≥ ν` for every `y ∈ C`. -/
theorem smul_le_comp_of_le_on {Y : Type*} [MeasurableSpace Y] (K : Kernel X Y) (μ : Measure X)
    {C : Set X} {ν : Measure Y} (h : ∀ y ∈ C, ν ≤ K y) : μ C • ν ≤ K ∘ₘ μ :=
  Measure.le_intro fun B hB _ => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB K.aemeasurable]
    calc μ C * ν B = ∫⁻ _ in C, ν B ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in C, K y B ∂μ := setLIntegral_mono (Kernel.measurable_coe _ hB) fun y hy =>
          h y hy B
      _ ≤ ∫⁻ y, K y B ∂μ := setLIntegral_le_lintegral _ _

/-- The integral of an everywhere positive function against a nonzero measure is positive. -/
theorem lintegral_pos_of_pos {μ : Measure X} (hμ : μ ≠ 0) {f : X → ℝ≥0∞} (hf : Measurable f)
    (h : ∀ x, 0 < f x) : 0 < ∫⁻ x, f x ∂μ := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff hf]
  intro h0
  have : ∀ᵐ x ∂μ, False := h0.mono fun x hx => (h x).ne' hx
  exact hμ (ae_eq_bot.1 (by simpa using this))

/-- **Proposition 5.5.4 (i)** (MT p. 118): if `A` is `ν_a`-petite and `D ⇝ᵇ A`, then `D` is
`ν_{b∗a}`-petite with `ν_{b∗a} = δ ν_a`: `K_{b∗a}(x, B) ≥ ∫_A K_b(x, dy) K_a(y, B) ≥ δ ν_a(B)`
(5.49). -/
theorem proposition_5_5_4_i (P : Kernel X X) {a b : ℕ → ℝ≥0∞} {ν : Measure X} {A D : Set X}
    (hA : IsPetiteSet P a ν A) (hD : MeasurableSet D) (hb : IsSamplingDist b)
    (hDA : SampledAccessible P b D A) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ IsPetiteSet P (sampleConv b a) (δ • ν) D := by
  obtain ⟨δ, hδ, h⟩ := hDA
  refine ⟨δ, hδ, hD, isSamplingDist_sampleConv hb hA.2.1, smul_measure_ne_zero hA.2.2.1 hδ.ne',
    fun x hx => ?_⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply]
  exact (smul_measure_le_smul (h x hx) ν).trans (smul_le_comp_of_le_on _ _ hA.2.2.2)

/-- **Proposition 5.5.4 (ii)** (MT p. 118): for a `ψ`-irreducible chain, the minorizing measure
of a `ν_a`-petite set `A ∈ B⁺(X)` is an irreducibility measure. -/
theorem proposition_5_5_4_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {A : Set X}
    (hA : IsPetiteSet P a ν A) (hψA : 0 < ψ A) : IsPhiIrreducible P ν := by
  intro B hB hνB x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hA.1 x).1 (hψ A hA.1 hψA x)
  -- `Pⁿ⁺¹ K_a(x, B) ≥ Pⁿ⁺¹(x, A) ν(B) > 0`
  have h1 : 0 < ∫⁻ y, sampledKernel P a y B ∂(P ^ (n + 1)) x := by
    have := smul_le_comp_of_le_on (sampledKernel P a) ((P ^ (n + 1)) x) hA.2.2.2
    have h2 := this B
    rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hB (Kernel.aemeasurable _)] at h2
    exact (ENNReal.mul_pos hn.ne' hνB.ne').trans_le h2
  simp_rw [sampledKernel_apply P a _ hB] at h1
  rw [lintegral_tsum fun k => ((Kernel.measurable_coe _ hB).const_mul _).aemeasurable] at h1
  obtain ⟨k, hk⟩ : ∃ k, 0 < ∫⁻ y, a k * (P ^ k) y B ∂(P ^ (n + 1)) x := by
    by_contra hc
    push Not at hc
    exact h1.ne' (ENNReal.tsum_eq_zero.2 fun k => nonpos_iff_eq_zero.1 (hc k))
  rw [lintegral_const_mul _ (Kernel.measurable_coe _ hB),
    ← Kernel.pow_add_apply_eq_lintegral P (n + 1) k x hB] at hk
  refine (hitProb_pos_iff P hB x).2 ⟨n + k, ?_⟩
  rw [show n + k + 1 = n + 1 + k by omega]
  exact pos_of_mul_pos_right hk zero_le

/-! ### Proposition 5.5.5 -/

/-- The geometric distribution `a_{1/2}`: `K_{a_{1/2}}` is `resolventHalf`. -/
theorem sampledKernel_geomDist_half (P : Kernel X X) :
    sampledKernel P (geomDist 2⁻¹) = resolventHalf P := rfl

/-- `a_{1/2}` is a sampling distribution. -/
theorem isSamplingDist_geomDist_half : IsSamplingDist (geomDist 2⁻¹) :=
  isSamplingDist_geomDist (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)

variable [MeasurableSpace.CountablyGenerated X]

/-- **Proposition 5.5.5 (i)** (MT p. 118). On a countably generated space, for a `ψ`-irreducible
chain every `ν_a`-petite set `A` is `ψ_b`-petite for some sampling distribution `b` and some
maximal irreducibility measure `ψ_b`. -/
theorem proposition_5_5_5_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {A : Set X}
    (hA : IsPetiteSet P a ν A) :
    ∃ b ψb, IsPetiteSet P b ψb A ∧ IsMaximalIrreducibility P ψb := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  -- `A ⇝ C` for the sampling distribution `a ∗ a_{1/2}`
  have hKpos : ∀ y, 0 < resolventHalf P y C := fun y =>
    (proposition_4_2_1 P ψ).2.2.1 hψ.2.1 C hC.1 hψC y
  have hδ := lintegral_pos_of_pos hA.2.2.1 (Kernel.measurable_coe _ hC.1) hKpos
  have hacc : SampledAccessible P (sampleConv a (geomDist 2⁻¹)) A C := by
    refine ⟨_, hδ, fun x hx => ?_⟩
    rw [lemma_5_5_2_i P _ _ x hC.1, sampledKernel_geomDist_half]
    exact lintegral_mono' (hA.2.2.2 x hx) le_rfl
  obtain ⟨δ', hδ', hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC) hA.1
    (isSamplingDist_sampleConv hA.2.1 isSamplingDist_geomDist_half) hacc
  -- the petite measure is an irreducibility measure; spread it by `K_{a_{1/2}}`
  have hirr : IsPhiIrreducible P (δ' • νC) :=
    (hC.isPhiIrreducible hψ.2.1 hψC).mono Measure.smul_absolutelyContinuous
  have hmax := isMaximalIrreducibility_maxIrrMeasure P hirr hpet.2.2.1
  refine ⟨sampleConv (sampleConv (sampleConv a (geomDist 2⁻¹)) (diracDist m)) (geomDist 2⁻¹),
    maxIrrMeasure P (δ' • νC), ⟨hA.1, isSamplingDist_sampleConv hpet.2.1
      isSamplingDist_geomDist_half, hmax.1, fun x hx => ?_⟩, hmax⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply, sampledKernel_geomDist_half]
  exact comp_le_comp _ (hpet.2.2.2 x hx)

/-- **Proposition 5.5.5 (ii)** (MT p. 119). On a countably generated space, for a
`ψ`-irreducible chain the union of two petite sets is petite. -/
theorem proposition_5_5_5_ii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A₁ A₂ : Set X} (h₁ : IsPetite P A₁)
    (h₂ : IsPetite P A₂) : IsPetite P (A₁ ∪ A₂) := by
  obtain ⟨a₁, ν₁, h₁⟩ := h₁
  obtain ⟨a₂, ν₂, h₂⟩ := h₂
  obtain ⟨b₁, ψ₁, hp₁, hm₁⟩ := proposition_5_5_5_i P hψ h₁
  obtain ⟨b₂, ψ₂, hp₂, hm₂⟩ := proposition_5_5_5_i P hψ h₂
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hψ₁C : 0 < ψ₁ C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hm₁).1 h0)
  have hψ₂C : 0 < ψ₂ C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hm₂).1 h0)
  have hacc : SampledAccessible P (mixDist b₁ b₂) (A₁ ∪ A₂) C := by
    refine ⟨2⁻¹ * min (ψ₁ C) (ψ₂ C), ENNReal.mul_pos (by simp)
      (lt_min hψ₁C hψ₂C).ne', fun x hx => ?_⟩
    rw [sampledKernel_mixDist_apply P _ _ x hC.1]
    rcases hx with hx | hx
    · calc 2⁻¹ * min (ψ₁ C) (ψ₂ C) ≤ 2⁻¹ * sampledKernel P b₁ x C := by
            gcongr
            exact (min_le_left _ _).trans (hp₁.2.2.2 x hx C)
        _ ≤ _ := le_self_add
    · calc 2⁻¹ * min (ψ₁ C) (ψ₂ C) ≤ 2⁻¹ * sampledKernel P b₂ x C := by
            gcongr
            exact (min_le_right _ _).trans (hp₂.2.2.2 x hx C)
        _ ≤ _ := le_add_self
  obtain ⟨δ, -, hpet⟩ := proposition_5_5_4_i P (proposition_5_5_3 hC) (h₁.1.union h₂.1)
    (isSamplingDist_mixDist hp₁.2.1 hp₂.2.1) hacc
  exact ⟨_, _, hpet⟩

/-- **Proposition 5.5.5 (iii)** (MT p. 118). On a countably generated space, for a
`ψ`-irreducible chain there are a sampling distribution `c`, an everywhere positive measurable
`s` and a maximal irreducibility measure `ψ_c` with `K_c(x, B) ≥ s(x) ψ_c(B)` for all `x`, `B`. -/
theorem proposition_5_5_5_iii (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ (c : ℕ → ℝ≥0∞) (s : X → ℝ≥0∞) (ψc : Measure X), IsSamplingDist c ∧ Measurable s ∧
      (∀ x, 0 < s x) ∧
      IsMaximalIrreducibility P ψc ∧ ∀ x, s x • ψc ≤ sampledKernel P c x := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨b, ψb, hpet, hmax⟩ := proposition_5_5_5_i P hψ (proposition_5_5_3 hC)
  refine ⟨sampleConv (geomDist 2⁻¹) b, fun x => resolventHalf P x C, ψb,
    isSamplingDist_sampleConv isSamplingDist_geomDist_half hpet.2.1,
    Kernel.measurable_coe _ hC.1, fun x => (proposition_4_2_1 P ψ).2.2.1 hψ.2.1 C hC.1 hψC x,
    hmax, fun x => ?_⟩
  rw [sampledKernel_sampleConv, Kernel.comp_apply, sampledKernel_geomDist_half]
  exact smul_le_comp_of_le_on _ _ hpet.2.2.2

/-- Proposition 5.5.5 (iii), the cover (MT p. 119): the sets `Cₙ = {x : s(x) ≥ (n + 1)⁻¹}`
increase, are `ψ_c`-petite with one sampling distribution `c` and minorizing measure a multiple
of `ψ_c`, and cover `X`. -/
theorem proposition_5_5_5_iii_cover (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    ∃ (c : ℕ → ℝ≥0∞) (ψc : Measure X), IsMaximalIrreducibility P ψc ∧ ∃ Cs : ℕ → Set X,
      Monotone Cs ∧ (∀ n : ℕ, IsPetiteSet P c (((n : ℝ≥0∞) + 1)⁻¹ • ψc) (Cs n)) ∧
        ⋃ n, Cs n = univ := by
  obtain ⟨c, s, ψc, hc, hs, hspos, hmax, hle⟩ := proposition_5_5_5_iii P hψ
  refine ⟨c, ψc, hmax, fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ s x}, fun n k hnk x hx => ?_,
    fun n => ⟨measurableSet_le measurable_const hs, hc,
      smul_measure_ne_zero hmax.1 (ENNReal.inv_ne_zero.2 (by simp)), fun x hx =>
        (smul_measure_le_smul hx ψc).trans (hle x)⟩, ?_⟩
  · refine le_trans ?_ (show ((n : ℝ≥0∞) + 1)⁻¹ ≤ s x from hx)
    change ((k : ℝ≥0∞) + 1)⁻¹ ≤ ((n : ℝ≥0∞) + 1)⁻¹
    gcongr
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hspos x).ne'
    refine ⟨n, le_trans ?_ hn.le⟩
    gcongr
    exact le_self_add

/-! ### Tails of sampling distributions -/

omit [MeasurableSpace.CountablyGenerated X] in
/-- The tail of a sampling distribution beyond some `K` is at most any `ε > 0`. -/
theorem exists_tail_le {a : ℕ → ℝ≥0∞} (ha : IsSamplingDist a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, ∑' k, a (k + K) ≤ ε := by
  have h := ENNReal.tendsto_sum_nat_add a (by rw [ha]; exact ENNReal.one_ne_top)
  obtain ⟨K, hK⟩ := (h.eventually (Iio_mem_nhds hε)).exists
  exact ⟨K, le_of_lt hK⟩

omit [MeasurableSpace.CountablyGenerated X] in
/-- If `K_b(x, A) ≥ t`, `2ε ≤ t` and the tail of `b` beyond `K` is at most `ε`, then
`Σ_{k < K} b(k) Pᵏ(x, A) ≥ ε`. -/
theorem le_sum_head (P : Kernel X X) [IsMarkovKernel P] {b : ℕ → ℝ≥0∞} (K : ℕ) (x : X)
    {A : Set X} (hA : MeasurableSet A) {t ε : ℝ≥0∞} (hεt : ε ≠ ∞)
    (htail : ∑' k, b (k + K) ≤ ε) (h2 : 2 * ε ≤ t) (ht : t ≤ sampledKernel P b x A) :
    ε ≤ ∑ k ∈ Finset.range K, b k * (P ^ k) x A := by
  have hsplit : ∑' k, b k * (P ^ k) x A = ∑ k ∈ Finset.range K, b k * (P ^ k) x A +
      ∑' k, b (k + K) * (P ^ (k + K)) x A :=
    (Summable.sum_add_tsum_nat_add' (f := fun k => b k * (P ^ k) x A) (k := K)
      ENNReal.summable).symm
  rw [sampledKernel_apply P b x hA, hsplit] at ht
  have htl : ∑' k, b (k + K) * (P ^ (k + K)) x A ≤ ε := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) htail
    have := isMarkovKernel_pow P (k + K)
    exact mul_le_of_le_one_right' prob_le_one
  have h3 : ε + ε ≤ (∑ k ∈ Finset.range K, b k * (P ^ k) x A) + ε := by
    calc ε + ε = 2 * ε := (two_mul ε).symm
      _ ≤ t := h2
      _ ≤ _ := ht.trans (add_le_add_right htl _)
  exact (ENNReal.add_le_add_iff_right hεt).1 h3

omit [MeasurableSpace.CountablyGenerated X] in
/-- The constant `ε₀ = ½ min(t, 1)` used in the tail estimates. -/
theorem half_min_spec {t : ℝ≥0∞} (ht : 0 < t) :
    0 < 2⁻¹ * min t 1 ∧ 2⁻¹ * min t 1 ≠ ∞ ∧ 2 * (2⁻¹ * min t 1) ≤ t := by
  refine ⟨ENNReal.mul_pos (by simp) (lt_min ht one_pos).ne', ENNReal.mul_ne_top (by simp)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)), ?_⟩
  rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact min_le_left _ _

/-- The core estimate of Proposition 5.5.6 (i) (MT p. 120): for a petite `C` there are `N ≥ 1`,
a constant `ε₀ > 0` and a nonzero `νₙ` with `Σ_{j=1}^{N} Pʲ(x, B) ≥ ε₀ νₙ(B)` for `x ∈ C`. -/
theorem exists_sum_Icc_pow_ge (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {C : Set X}
    (hC : IsPetiteSet P a ν C) :
    ∃ N, 1 ≤ N ∧ ∃ ε₀ : ℝ≥0∞, 0 < ε₀ ∧ ∃ νₙ : Measure X, νₙ ≠ 0 ∧
      ∀ x ∈ C, ∀ B, MeasurableSet B → ε₀ * νₙ B ≤ ∑ j ∈ Finset.Icc 1 N, (P ^ j) x B := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨A, -, n, νₙ, hA, hψA, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨b, ψb, hpet, hmax⟩ := proposition_5_5_5_i P hψ hC
  have ht : 0 < ψb A := pos_iff_ne_zero.2 fun h0 => hψA.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψb A) 1
  obtain ⟨K, hK⟩ := exists_tail_le hpet.2.1 hε0
  refine ⟨K + n, by have := hA.2.1; omega, ε₀, hε0, νₙ, hA.2.2.1, fun x hx B hB => ?_⟩
  have hhead := le_sum_head P K x hA.1 hεt hK h2 (hpet.2.2.2 x hx A)
  have hb1 : ∀ k, b k ≤ 1 := fun k => hpet.2.1 ▸ ENNReal.le_tsum k
  calc ε₀ * νₙ B ≤ (∑ k ∈ Finset.range K, b k * (P ^ k) x A) * νₙ B := by gcongr
    _ = ∑ k ∈ Finset.range K, b k * ((P ^ k) x A * νₙ B) := by
        rw [Finset.sum_mul]; simp_rw [mul_assoc]
    _ ≤ ∑ k ∈ Finset.range K, (P ^ (k + n)) x B := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact (mul_le_of_le_one_left' (hb1 k)).trans (pow_add_ge_of_le P hA.2.2.2 x hB)
    _ = ∑ j ∈ (Finset.range K).image (· + n), (P ^ j) x B :=
        (Finset.sum_image (f := fun j => (P ^ j) x B) (g := (· + n))
          fun i _ j _ h => Nat.add_right_cancel h).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 (K + n), (P ^ j) x B := by
        refine Finset.sum_le_sum_of_subset fun j hj => ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hj
        have := hA.2.1
        rw [Finset.mem_range] at hk
        rw [Finset.mem_Icc]
        omega

/-- **Proposition 5.5.6 (i)** (MT p. 120). On a countably generated space, for a
`ψ`-irreducible chain, a petite set is petite for a uniform sampling distribution
`a(i) = 1/N`, `1 ≤ i ≤ N` (which has finite mean), and for every geometric distribution `a_ε`,
`0 < ε < 1`. -/
theorem proposition_5_5_6_i (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {a : ℕ → ℝ≥0∞} {ν : Measure X} {C : Set X}
    (hC : IsPetiteSet P a ν C) :
    (∃ N, 1 ≤ N ∧ (∃ ν', IsPetiteSet P (uniformDist N) ν' C) ∧
      ∑' n : ℕ, (n : ℝ≥0∞) * uniformDist N n ≠ ∞) ∧
      ∀ ε : ℝ≥0∞, 0 < ε → ε < 1 → ∃ ν'', IsPetiteSet P (geomDist ε) ν'' C := by
  obtain ⟨N, hN, ε₀, hε₀, νₙ, hνₙ, hsum⟩ := exists_sum_Icc_pow_ge P hψ hC
  refine ⟨⟨N, hN, ⟨((N : ℝ≥0∞)⁻¹ * ε₀) • νₙ, hC.1, isSamplingDist_uniformDist hN,
    smul_measure_ne_zero hνₙ (ENNReal.mul_pos (by simp) hε₀.ne').ne', fun x hx =>
      Measure.le_intro fun B hB _ => ?_⟩, tsum_mul_uniformDist_ne_top N⟩, fun ε hε0 hε1 => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, sampledKernel_uniformDist_apply P N x hB, mul_assoc]
    gcongr
    exact hsum x hx B hB
  · refine ⟨((1 - ε) * ε ^ N * ε₀) • νₙ, hC.1, isSamplingDist_geomDist hε1,
      smul_measure_ne_zero hνₙ (ENNReal.mul_pos (ENNReal.mul_pos (tsub_pos_of_lt hε1).ne'
        (pow_ne_zero _ hε0.ne')).ne' hε₀.ne').ne', fun x hx => Measure.le_intro fun B hB _ => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, sampledKernel_geomDist, resolvent_apply P ε x hB,
      mul_assoc, mul_assoc]
    gcongr
    calc ε ^ N * (ε₀ * νₙ B) ≤ ε ^ N * ∑ j ∈ Finset.Icc 1 N, (P ^ j) x B := by
          gcongr; exact hsum x hx B hB
      _ = ∑ j ∈ Finset.Icc 1 N, ε ^ N * (P ^ j) x B := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 N, ε ^ j * (P ^ j) x B := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul' (pow_le_pow_right_of_le_one' hε1.le (Finset.mem_Icc.1 hj).2) le_rfl
      _ ≤ ∑' j, ε ^ j * (P ^ j) x B := ENNReal.sum_le_tsum _

/-- **Theorem 5.5.7** (MT p. 120). On a countably generated space, if a `ψ`-irreducible chain is
aperiodic then every petite set is small. -/
theorem theorem_5_5_7 (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {A : Set X}
    (hA : IsPetite P A) : IsSmall P A := by
  obtain ⟨a', ν', hpet'⟩ := hA
  obtain ⟨a, ψa, hpet, hmax⟩ := proposition_5_5_5_i P hψ hpet'
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, M, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  have ht : 0 < ψa C := pos_iff_ne_zero.2 fun h0 => hψC.ne' ((hψ.equiv hmax).1 h0)
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec ht
  set ε₀ := 2⁻¹ * min (ψa C) 1
  obtain ⟨K, hK⟩ := exists_tail_le hpet.2.1 hε0
  -- the times `n₀ − k`, `k < K`, all lie in `E_C`
  choose δ hδ hδle using fun k => (hN (N + (K - k) + 1) (by omega)).2
  set δ' := min ((Finset.range K).inf δ) 1
  have hδ' : 0 < δ' := lt_min ((Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun k _ => hδ k)
    one_pos
  refine ⟨N + K + 1, (ε₀ * δ') • ν, hpet.1, by omega,
    smul_measure_ne_zero hC.2.2.1 (ENNReal.mul_pos hε0.ne' hδ'.ne').ne', fun x hx =>
      Measure.le_intro fun B hB _ => ?_⟩
  have hbound : ∀ k ∈ Finset.range K, (P ^ k) x C * (δ' * ν B) ≤ (P ^ (N + K + 1)) x B :=
    fun k hk => by
      have hk' := Finset.mem_range.1 hk
      have hle : ∀ y ∈ C, δ' • ν ≤ (P ^ (N + (K - k) + 1)) y := fun y hy =>
        (smul_measure_le_smul ((min_le_left _ _).trans (Finset.inf_le hk)) ν).trans (hδle k y hy)
      have := pow_add_ge_of_le P (m := k) hle x hB
      rw [show k + (N + (K - k) + 1) = N + K + 1 by omega, Measure.smul_apply,
        smul_eq_mul] at this
      exact this
  have hhead := le_sum_head P K x hC.1 hεt hK h2 (hpet.2.2.2 x hx C)
  have hsum1 : ∑ k ∈ Finset.range K, a k ≤ 1 := hpet.2.1 ▸ ENNReal.sum_le_tsum _
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc]
  calc ε₀ * (δ' * ν B) ≤ (∑ k ∈ Finset.range K, a k * (P ^ k) x C) * (δ' * ν B) := by gcongr
    _ = ∑ k ∈ Finset.range K, a k * ((P ^ k) x C * (δ' * ν B)) := by
        rw [Finset.sum_mul]; simp_rw [mul_assoc]
    _ ≤ ∑ k ∈ Finset.range K, a k * (P ^ (N + K + 1)) x B :=
        Finset.sum_le_sum fun k hk => by gcongr; exact hbound k hk
    _ = (∑ k ∈ Finset.range K, a k) * (P ^ (N + K + 1)) x B := (Finset.sum_mul _ _ _).symm
    _ ≤ (P ^ (N + K + 1)) x B := mul_le_of_le_one_left' hsum1

end MeynTweedie.HarrisRecurrence
