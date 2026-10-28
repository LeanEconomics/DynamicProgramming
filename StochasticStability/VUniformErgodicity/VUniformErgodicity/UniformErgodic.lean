/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.VUniformErgodic
import VUniformErgodicity.TChains

/-!
# Uniform ergodicity (MT §16.2, Theorem 16.0.2)

Meyn and Tweedie, pp. 393–395 and §16.2, pp. 400–407. `μ` is an invariant probability; where
`ψ` appears it is a maximal irreducibility measure and the state space is countably generated.

* `IsUniformlyErgodic P μ` (16.6), p. 393: `sup_x ‖Pⁿ(x, ·) − μ‖ → 0`; `vErgDist_one_eq`,
  `isUniformlyErgodic_iff`: it is `V`-uniform ergodicity for `V ≡ 1`.
* **Theorem 16.2.1** (`theorem_16_2_1`, p. 400), with no irreducibility assumption: uniform
  ergodicity, the uniform geometric bound `‖Pⁿ(x, ·) − μ‖ ≤ R ρⁿ` and
  `sup_x ‖Pⁿ(x, ·) − μ‖ < 1` for one `n` are equivalent.
* `isPhiIrreducible_of_isUniformlyErgodic` (p. 401): a uniformly ergodic chain is
  `μ`-irreducible. `isSmallSet_univ_of_isUniformlyErgodic` (the step (i) ⇒ (ii) of Theorem
  16.2.2): for a `ψ`-irreducible chain the whole space is small.
* `isAperiodic_of_isSmallSet_univ`: if `X` is `νₘ`-small the chain is aperiodic (`m` and `m + 1`
  are small times), and so (p. 401) a `ψ`-irreducible uniformly ergodic chain is aperiodic.
* **Theorem 16.2.2** (`theorem_16_2_2`, p. 401): for a `ψ`-irreducible aperiodic chain,
  uniform ergodicity, `X` petite, a petite `C` with `sup_x E_x[τ_C] < ∞`, a petite `C` with
  `sup_x E_x[κ^{τ_C}] < ∞`, and a bounded solution of (16.10) are equivalent;
  `theorem_16_2_2_hitting`: then `sup_x E_x[τ_A] < ∞` and `sup_x E_x[κ_A^{τ_A}] < ∞` for every
  `A ∈ B⁺(X)`.
* `IsDoeblin P` (p. 402), **Theorem 16.2.3** (`theorem_16_2_3`, p. 402): an aperiodic
  `ψ`-irreducible chain satisfies Doeblin's condition iff it is uniformly ergodic.
* `tvNorm_comp_le_of_le`: if `Q(x, ·) ≥ ν` for every `x`, then `‖λQ − λ'Q‖ ≤ (1 − ν(X)) ‖λ − λ'‖`.
  **Theorem 16.2.4** (`theorem_16_2_4`, p. 402): if `X` is `νₘ`-small,
  `‖Pⁿ(x, ·) − μ‖ ≤ 2 ρ^{⌊n/m⌋}` with `ρ = 1 − νₘ(X)`. The proof is this analytic form of the
  coupling argument (16.23).
* **Theorem 16.0.2** (`theorem_16_0_2`, p. 394): the eight equivalent conditions for a
  `ψ`-irreducible chain, and (16.11).
* `isUniformlyErgodic_const` (pp. 404, 408): an i.i.d. chain is uniformly ergodic.
* **Theorem 16.2.5** (`theorem_16_2_5`, p. 406): a `ψ`-irreducible aperiodic T-chain on a compact
  space is uniformly ergodic.

**Corrections.**
* (16.11) and (16.21): `‖Pⁿ(x, ·) − π‖ ≤ 2ρ^{n/m}` holds with the integer part `⌊n/m⌋`, not with
  the real exponent `n/m`: `theorem_16_2_4_counterexample` is the chain `0 ↦ 1 ↦ 2 ↦ 2` on `ℕ`,
  for which `X` is `δ₂`-small with `m = 2`, `ρ = 0`, and `‖P(0, ·) − δ₂‖ = 2 > 2 · 0^{1/2}`.
* Theorem 16.0.2 is stated "for any Markov chain", but (iv)–(viii) refer to aperiodicity and so to
  a `ψ`-irreducible chain; it is proved for `ψ`-irreducible chains, and Theorem 16.2.1 covers
  (i)–(iii) without irreducibility.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ### The definition -/

/-- **Uniform ergodicity** (16.6), MT p. 393: `μ` is invariant and
`sup_x ‖Pⁿ(x, ·) − μ‖ → 0`. -/
def IsUniformlyErgodic (P : Kernel X X) (μ : Measure X) : Prop :=
  IsInvariant P μ ∧
    Tendsto (fun n => ⨆ x, ENNReal.ofReal (tvNorm ((P ^ n) x) μ)) atTop (𝓝 0)

/-- `|||Pⁿ − 1 ⊗ μ|||_1 = sup_x ‖Pⁿ(x, ·) − μ‖`. -/
theorem vErgDist_one_eq (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X) [IsFiniteMeasure μ]
    (n : ℕ) : vErgDist 1 P μ n = ⨆ x, ENNReal.ofReal (tvNorm ((P ^ n) x) μ) := by
  have := isMarkovKernel_pow P n
  unfold vErgDist vOpNorm
  refine iSup_congr fun x => ?_
  rw [Kernel.const_apply, Pi.one_apply, div_one, fNorm_one]

/-- Uniform ergodicity is `V`-uniform ergodicity with `V ≡ 1` (MT p. 393). -/
theorem isUniformlyErgodic_iff (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsFiniteMeasure μ] : IsUniformlyErgodic P μ ↔ IsVUniformlyErgodic 1 P μ := by
  unfold IsUniformlyErgodic IsVUniformlyErgodic
  have : vErgDist 1 P μ = fun n => ⨆ x, ENNReal.ofReal (tvNorm ((P ^ n) x) μ) :=
    funext (vErgDist_one_eq P μ)
  rw [this]

/-- `‖Pⁿ(x, ·) − μ‖ ≤ 2`, so every `|||Pⁿ − 1 ⊗ μ|||_1 ≤ 2`. -/
theorem vErgDist_one_le_two (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) : vErgDist 1 P μ n ≤ 2 := by
  have := isMarkovKernel_pow P n
  rw [vErgDist_one_eq]
  refine iSup_le fun x => ?_
  calc ENNReal.ofReal (tvNorm ((P ^ n) x) μ) ≤ ENNReal.ofReal (((P ^ n) x).real univ +
        μ.real univ) := ENNReal.ofReal_le_ofReal (tvNorm_le_add_measureReal _ _)
    _ = 2 := by rw [probReal_univ, probReal_univ]; norm_num

/-- `‖Pⁿ⁺¹(x, ·) − μ‖ ≤ ‖Pⁿ(x, ·) − μ‖` (Proposition 13.3.2). -/
theorem vErgDist_one_succ_le (P : Kernel X X) [IsMarkovKernel P] {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) (n : ℕ) :
    vErgDist 1 P μ (n + 1) ≤ vErgDist 1 P μ n := by
  rw [vErgDist_one_eq, vErgDist_one_eq]
  refine iSup_mono fun x => ENNReal.ofReal_le_ofReal ?_
  have h := proposition_13_3_2 P hμ (Measure.dirac x) (Nat.le_succ n)
  have := isMarkovKernel_pow P n
  have := isMarkovKernel_pow P (n + 1)
  simpa only [dirac_kernel] using h

/-! ### Theorem 16.2.1 -/

/-- **Theorem 16.2.1** (MT p. 400), without irreducibility: for an invariant probability `μ`, the
following are equivalent: (i) uniform ergodicity; (ii) `‖Pⁿ(x, ·) − μ‖ ≤ R ρⁿ` for all `x`, `n`,
with `ρ < 1`; (iii) `sup_x ‖Pⁿ(x, ·) − μ‖ < 1` for some `n`. -/
theorem theorem_16_2_1 (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : IsInvariant P μ) :
    List.TFAE [IsUniformlyErgodic P μ,
      ∃ ρ R : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x n, tvNorm ((P ^ n) x) μ ≤ R * ρ ^ n,
      ∃ n, ⨆ x, ENNReal.ofReal (tvNorm ((P ^ n) x) μ) < 1] := by
  tfae_have 1 → 3 := fun h => (h.2.eventually (gt_mem_nhds zero_lt_one)).exists
  tfae_have 3 → 2 := by
    rintro ⟨n, hn⟩
    rw [← vErgDist_one_eq] at hn
    have hn1 : vErgDist 1 P μ (n + 1) < 1 := (vErgDist_one_succ_le P hμ n).trans_lt hn
    have hμ1 : ∫⁻ y, (1 : X → ℝ≥0∞) y ∂μ ≠ ∞ := by simp
    obtain ⟨t, ht1, -, K, hK, hb⟩ := vErgDist_le_geometric (V := 1) measurable_one
      (fun _ => le_rfl) (fun _ => ENNReal.one_ne_top) hμ hμ1
      (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (vErgDist_one_le_two P μ 1)) (Nat.succ_pos n) hn1
    have htt : t ≠ ∞ := (ht1.trans ENNReal.one_lt_top).ne
    refine ⟨t.toReal, K.toReal, ENNReal.toReal_nonneg, ENNReal.toReal_lt_of_lt_ofReal (by simpa
      using ht1), fun x k => ?_⟩
    have := isMarkovKernel_pow P k
    have h1 : ENNReal.ofReal (tvNorm ((P ^ k) x) μ) ≤ K * t ^ k := by
      have := hb k
      rw [vErgDist_one_eq] at this
      exact (le_iSup (fun x => ENNReal.ofReal (tvNorm ((P ^ k) x) μ)) x).trans this
    rw [← ENNReal.toReal_pow, ← ENNReal.toReal_mul]
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hK (ENNReal.pow_ne_top htt))).1 h1
  tfae_have 2 → 1 := by
    rintro ⟨ρ, R, hρ0, hρ1, hb⟩
    refine ⟨hμ, ?_⟩
    have hlim : Tendsto (fun n => ENNReal.ofReal (R * ρ ^ n)) atTop (𝓝 0) := by
      have : Tendsto (fun n => R * ρ ^ n) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul R
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp this
      rw [ENNReal.ofReal_zero] at h2
      exact h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun n => iSup_le fun x => ENNReal.ofReal_le_ofReal (hb x n)
  tfae_finish

/-- **A uniformly ergodic chain is `μ`-irreducible** (MT p. 401): if `μ(A) > 0` then
`Pⁿ(x, A) ≥ μ(A)/2 > 0` for all `x` once `sup_x ‖Pⁿ(x, ·) − μ‖ < μ(A)/2`. -/
theorem isPhiIrreducible_of_isUniformlyErgodic {P : Kernel X X} [IsMarkovKernel P]
    {μ : Measure X} [IsProbabilityMeasure μ] (h : IsUniformlyErgodic P μ) :
    IsPhiIrreducible P μ := by
  intro A hA hpos x
  have hlim := ((isUniformlyErgodic_iff P μ).1 h).2
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  have := isMarkovKernel_pow P (n + 1)
  refine (hitProb_pos_iff P hA x).2 ⟨n, ?_⟩
  have hle := measure_le_add_fNorm (f := 1) (fun _ => le_rfl) ((P ^ (n + 1)) x) μ hA
  have hrow := fNorm_pow_le_vErgDist_mul (V := 1) P μ (n + 1) (x := x) one_ne_zero
    ENNReal.one_ne_top
  rw [Pi.one_apply, mul_one] at hrow
  have hlt : vErgDist 1 P μ (n + 1) < μ A := (vErgDist_one_succ_le P h.1 n).trans_lt hn
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  rw [h0, zero_add] at hle
  exact absurd (hle.trans hrow) (not_le.2 hlt)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Step (i) ⇒ (ii) of Theorem 16.2.2** (MT p. 401): for a `ψ`-irreducible uniformly ergodic
chain the whole space is small: for a small `A ∈ B⁺(X)`, `inf_x P^{n₀}(x, A) > 0`
(Proposition 5.2.4). -/
theorem isSmallSet_univ_of_isUniformlyErgodic {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {μ : Measure X} [IsProbabilityMeasure μ]
    (h : IsUniformlyErgodic P μ) : ∃ m ν, IsSmallSet P m ν univ := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hμC : 0 < μ C :=
    h.1.isSubinvariant.pos_of_pos hψ.2.1 (IsProbabilityMeasure.ne_zero μ) hC.1 hψC
  have hμCt : μ C ≠ ∞ := measure_ne_top μ C
  have hlim := ((isUniformlyErgodic_iff P μ).1 h).2
  have hpos : (0 : ℝ≥0∞) < μ C / 2 := ENNReal.half_pos hμC.ne'
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  have := isMarkovKernel_pow P n
  refine ⟨n + m, _, proposition_5_2_4_i P hC MeasurableSet.univ hpos fun x _ => ?_⟩
  have hle := measure_le_add_fNorm (f := 1) (fun _ => le_rfl) ((P ^ n) x) μ hC.1
  have hrow := fNorm_pow_le_vErgDist_mul (V := 1) P μ n (x := x) one_ne_zero ENNReal.one_ne_top
  rw [Pi.one_apply, mul_one] at hrow
  have h4 : μ C ≤ (P ^ n) x C + μ C / 2 := hle.trans (add_le_add le_rfl (hrow.trans hn.le))
  calc μ C / 2 = μ C - μ C / 2 := (ENNReal.sub_half hμCt).symm
    _ ≤ (P ^ n) x C := tsub_le_iff_right.2 h4

/-- **A small state space makes the chain aperiodic**: if `X` is `νₘ`-small it is also
`νₘ`-small at time `m + 1`, so `g.c.d. E_X = 1`. -/
theorem isAperiodic_of_isSmallSet_univ {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {m : ℕ} {ν : Measure X} (h : IsSmallSet P m ν univ) :
    IsAperiodic P ψ := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  have hνu : 0 < ν univ := pos_iff_ne_zero.2 fun h0 => h.2.2.1 (Measure.measure_univ_eq_zero.1 h0)
  have h1 : IsSmallSet P (m + 1) ν univ := by
    refine ⟨MeasurableSet.univ, Nat.succ_pos m, h.2.2.1, fun x _ => Measure.le_intro
      fun B hB _ => ?_⟩
    rw [pow_succ_apply P m x hB]
    calc ν B = ∫⁻ _, ν B ∂P x := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ y, (P ^ m) y B ∂P x := lintegral_mono fun y => h.2.2.2 y (mem_univ y) B
  have hper := isPeriod_gcd P hψ h hψu hνu
  have hS := smallTimes_isAddClosed P hνu
  have hd1 : setGcd (smallTimes P univ ν) ∣ m :=
    setGcd_dvd hS (mem_smallTimes_of_isSmallSet h) h.2.1 (mem_smallTimes_of_isSmallSet h)
  have hd2 : setGcd (smallTimes P univ ν) ∣ m + 1 :=
    setGcd_dvd hS (mem_smallTimes_of_isSmallSet h) h.2.1 (mem_smallTimes_of_isSmallSet h1)
  have hd : setGcd (smallTimes P univ ν) ∣ 1 := by
    have := Nat.dvd_sub hd2 hd1
    rwa [Nat.add_sub_cancel_left] at this
  rwa [Nat.dvd_one.1 hd] at hper

variable [MeasurableSpace.CountablyGenerated X] in
/-- **A `ψ`-irreducible uniformly ergodic chain is aperiodic** (MT p. 401). -/
theorem isAperiodic_of_isUniformlyErgodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {μ : Measure X} [IsProbabilityMeasure μ]
    (h : IsUniformlyErgodic P μ) : IsAperiodic P ψ := by
  obtain ⟨m, ν, hs⟩ := isSmallSet_univ_of_isUniformlyErgodic hψ h
  exact isAperiodic_of_isSmallSet_univ hψ hs

/-! ### Hitting times of the whole space and of `B⁺(X)` -/

omit [MeasurableSpace X] in
/-- `τ_X = 1`. -/
theorem firstReturn_univ (ω : ℕ → X) : firstReturn univ ω = 1 := by
  rw [firstReturn_eq_firstHit_shift, (firstHit_eq_zero_iff univ _).2 (mem_univ _)]
  rfl

/-- `E_x[τ_X] = 1`. -/
theorem meanReturnTime_univ (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    meanReturnTime P univ x = 1 := by
  have := isMarkovKernel_pathKernel P
  simp_rw [meanReturnTime, firstReturn_univ]
  rw [show ENat.toENNReal (1 : WithTop ℕ) = 1 from toENNReal_some 1 |>.trans Nat.cast_one,
    lintegral_const, measure_univ, mul_one]

/-- `E_x[κ^{τ_X}] = κ`. -/
theorem kendallMoment_univ (P : Kernel X X) [IsMarkovKernel P] (κ : ℝ≥0∞) (x : X) :
    kendallMoment P univ κ x = κ := by
  have := isMarkovKernel_pathKernel P
  simp_rw [kendallMoment, firstReturn_univ]
  rw [show tpow κ (1 : WithTop ℕ) = κ from (tpow_coe κ 1).trans (pow_one κ), lintegral_const,
    measure_univ, mul_one]

omit [MeasurableSpace X] in
/-- Bernoulli's inequality in the form `(κ − 1) n ≤ κⁿ`. -/
theorem sub_one_mul_le_pow {κ : ℝ≥0∞} (hκ : 1 ≤ κ) (n : ℕ) : (κ - 1) * n ≤ κ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ κ ^ n := one_le_pow₀ hκ
    calc (κ - 1) * ((n + 1 : ℕ) : ℝ≥0∞) = (κ - 1) * n + (κ - 1) := by push_cast; ring
      _ ≤ κ ^ n + (κ - 1) * κ ^ n := add_le_add ih (le_mul_of_one_le_right' h1)
      _ = (1 + (κ - 1)) * κ ^ n := by ring
      _ = κ ^ (n + 1) := by rw [add_tsub_cancel_of_le hκ, pow_succ, mul_comm]

/-- `E_x[τ_A] ≤ (κ − 1)⁻¹ E_x[κ^{τ_A}]` for `1 < κ < ∞`. -/
theorem meanReturnTime_le_kendallMoment (P : Kernel X X) [IsMarkovKernel P] (A : Set X)
    {κ : ℝ≥0∞} (hκ : 1 < κ) (hκt : κ ≠ ∞) (x : X) :
    meanReturnTime P A x ≤ (κ - 1)⁻¹ * kendallMoment P A κ x := by
  have h0 : κ - 1 ≠ 0 := (tsub_pos_of_lt hκ).ne'
  have ht : κ - 1 ≠ ∞ := ENNReal.sub_ne_top hκt
  unfold meanReturnTime kendallMoment
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0)]
  refine lintegral_mono fun ω => ?_
  cases h : firstReturn A ω with
  | top =>
    rw [tpow_top, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ht)]
    exact le_top
  | coe n =>
    rw [tpow_some, toENNReal_some n]
    calc (n : ℝ≥0∞) = (κ - 1)⁻¹ * ((κ - 1) * n) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
      _ ≤ (κ - 1)⁻¹ * κ ^ n := mul_le_mul' le_rfl (sub_one_mul_le_pow hκ.le n)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Bounded hitting times of `B⁺(X)`** (the "in which case" parts of Theorem 16.2.2 (iii) and
(iv), MT p. 401): under (V4) for a petite set with `V ≤ M` bounded, every `A ∈ B⁺(X)` has
`sup_x E_x[κ_A^{τ_A}] < ∞` for some `κ_A > 1` and `sup_x E_x[τ_A] < ∞` (Theorem 15.2.6 with the
whole space as the bounded set). -/
theorem theorem_16_2_2_hitting {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hVM : ∀ x, V x ≤ M) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞)
    {C : Set X} (hC : IsPetite P C) (h : DriftV4 P V ρ b C) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) :
    (∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x, kendallMoment P A κ x ≤ K) ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x, meanReturnTime P A x ≤ K := by
  obtain ⟨-, hreg⟩ := theorem_15_2_6 hψ hV hV1 hρ hb hC h MeasurableSet.univ hM
    fun x _ => hVM x
  obtain ⟨κ, hκ, hκt, K, hK, hbd⟩ := hreg A hA hψA
  have hκ1 : κ - 1 ≠ ∞ := ENNReal.sub_ne_top hκt
  have hkb : ∀ x, kendallMoment P A κ x ≤ 1 + (κ - 1) * K := fun x => by
    rw [kendallMoment_eq_one_add P hA hκ x]
    exact add_le_add le_rfl (mul_le_mul' le_rfl ((geomSum_mono_f P A κ hV1 x).trans
      (hbd x (mem_univ x))))
  have hK' : 1 + (κ - 1) * K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top hκ1 hK⟩
  refine ⟨⟨κ, hκ, hκt, _, hK', hkb⟩, (κ - 1)⁻¹ * (1 + (κ - 1) * K),
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hκ).ne') hK', fun x => ?_⟩
  exact (meanReturnTime_le_kendallMoment P A hκ hκt x).trans (mul_le_mul' le_rfl (hkb x))

/-! ### Theorem 16.2.2 -/

/-- A bounded solution of (V2) gives a bounded solution of (16.10): if `PW + 1 ≤ W + b 1_C` and
`W ≤ K`, then `V = W + 1` has `PV ≤ (1 − (K + 1)⁻¹) V + b 1_C`. -/
theorem driftV4_of_driftV2_bounded {P : Kernel X X} [IsMarkovKernel P] {W : X → ℝ≥0∞}
    (hW : Measurable W) {K : ℝ≥0∞} (hK : K ≠ ∞) (hWK : ∀ x, W x ≤ K) {b : ℝ≥0∞} {C : Set X}
    (h : ∀ x, ∫⁻ y, W y ∂P x + 1 ≤ W x + C.indicator (fun _ => b) x) :
    DriftV4 P (fun x => W x + 1) (1 - (K + 1)⁻¹) b C := by
  intro x
  set c := (K + 1)⁻¹ with hc
  have hK1 : K + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hK, ENNReal.one_ne_top⟩
  have hc0 : c ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
  have hc1 : c ≤ 1 := ENNReal.inv_le_one.2 le_add_self
  have hVt : W x + 1 ≠ ∞ := ne_top_of_le_ne_top hK1 (add_le_add (hWK x) le_rfl)
  have hcV : c * (W x + 1) ≤ 1 := by
    calc c * (W x + 1) ≤ c * (K + 1) := mul_le_mul' le_rfl (add_le_add (hWK x) le_rfl)
      _ = 1 := ENNReal.inv_mul_cancel (by simp) hK1
  rw [lintegral_add_left hW, lintegral_const, measure_univ, mul_one]
  have hcVt : c * (W x + 1) ≠ ∞ := ENNReal.mul_ne_top hc0 hVt
  refine (ENNReal.add_le_add_iff_right hcVt).1 ?_
  calc ∫⁻ y, W y ∂P x + 1 + c * (W x + 1) ≤ ∫⁻ y, W y ∂P x + 1 + 1 := add_le_add le_rfl hcV
    _ ≤ W x + C.indicator (fun _ => b) x + 1 := add_le_add (h x) le_rfl
    _ = (W x + 1) + C.indicator (fun _ => b) x := by ring
    _ = ((1 - c) * (W x + 1) + c * (W x + 1)) + C.indicator (fun _ => b) x := by
        rw [← add_mul, tsub_add_cancel_of_le hc1, one_mul]
    _ = (1 - c) * (W x + 1) + C.indicator (fun _ => b) x + c * (W x + 1) := by ring

variable [MeasurableSpace.CountablyGenerated X] in
/-- **(v) ⇒ (i) of Theorem 16.2.2**: a bounded solution `V ≥ 1` of (16.10) for a petite set makes
the chain uniformly ergodic, with an invariant probability (Theorem 16.1.2). -/
theorem isUniformlyErgodic_of_bounded_driftV4 {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ)
    {V : X → ℝ≥0∞} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hVM : ∀ x, V x ≤ M) {ρ b : ℝ≥0∞} (hρ : ρ < 1) (hb : b ≠ ∞) {C : Set X}
    (hC : IsPetite P C) (h : DriftV4 P V ρ b C) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsUniformlyErgodic P μ := by
  have hVt : ∀ x, V x ≠ ∞ := fun x => ne_top_of_le_ne_top hM (hVM x)
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact absurd hψ.1 (by simp [Measure.eq_zero_of_isEmpty])
  obtain ⟨hpos, -⟩ := geometric_ergodic_of_driftV4 hψ hap hV hV1 hρ hb hC h (hVt x₀)
  obtain ⟨μ, hμp, hμ⟩ := hpos.2
  refine ⟨μ, hμp, hμ, ?_⟩
  obtain ⟨-, hlim⟩ := theorem_16_1_2 hψ hap hV hV1 hVt hρ hb hC h μ hμ
  have hlim' : Tendsto (fun n => vErgDist V P μ n * M) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hM)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim' (fun _ => zero_le)
    fun n => iSup_le fun x => ?_
  have := isMarkovKernel_pow P n
  have hV0 : V x ≠ 0 := (zero_lt_one.trans_le (hV1 x)).ne'
  calc ENNReal.ofReal (tvNorm ((P ^ n) x) μ) ≤ fNorm V ((P ^ n) x) μ :=
        ofReal_tvNorm_le_fNorm hV1 _ _
    _ ≤ vErgDist V P μ n * V x := fNorm_pow_le_vErgDist_mul P μ n hV0 (hVt x)
    _ ≤ vErgDist V P μ n * M := mul_le_mul' le_rfl (hVM x)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.2.2** (MT p. 401): for a `ψ`-irreducible aperiodic chain the following are
equivalent: (i) `Φ` is uniformly ergodic; (ii) `X` is petite; (iii) some petite `C` has
`sup_x E_x[τ_C] < ∞`; (iv) some petite `C` and `κ > 1` have `sup_x E_x[κ^{τ_C}] < ∞`; (v) there
is a bounded solution `V ≥ 1` of (16.10), `PV ≤ ρV + b 1_C`, for a petite `C`. The "in which case"
parts of (iii) and (iv) are `theorem_16_2_2_hitting`. -/
theorem theorem_16_2_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    List.TFAE [∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsUniformlyErgodic P μ,
      IsPetite P univ,
      ∃ C, IsPetite P C ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x, meanReturnTime P C x ≤ K,
      ∃ C, IsPetite P C ∧ ∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        ∀ x, kendallMoment P C κ x ≤ K,
      ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, 1 ≤ V x) ∧ (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x, V x ≤ M) ∧
        ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite P C ∧ DriftV4 P V ρ b C] := by
  tfae_have 1 → 2 := by
    rintro ⟨μ, hμp, h⟩
    obtain ⟨m, ν, hs⟩ := isSmallSet_univ_of_isUniformlyErgodic hψ h
    exact ⟨_, _, proposition_5_5_3 hs⟩
  tfae_have 2 → 4 := fun h => ⟨univ, h, 2, ENNReal.one_lt_two, ENNReal.ofNat_ne_top, 2,
    ENNReal.ofNat_ne_top, fun x => (kendallMoment_univ P 2 x).le⟩
  tfae_have 4 → 3 := by
    rintro ⟨C, hC, κ, hκ, hκt, K, hK, hb⟩
    exact ⟨C, hC, (κ - 1)⁻¹ * K, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2
      (tsub_pos_of_lt hκ).ne') hK, fun x => (meanReturnTime_le_kendallMoment P C hκ hκt x).trans
        (mul_le_mul' le_rfl (hb x))⟩
  tfae_have 3 → 5 := by
    rintro ⟨C, hC, K, hK, hb⟩
    have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
    have hWK : ∀ x, regV P C x ≤ 1 + K := fun x =>
      (regV_le P hCm x).trans (add_le_add le_rfl (hb x))
    have hK1 : 1 + K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩
    refine ⟨fun x => regV P C x + 1, (measurable_regV P hCm).add_const 1, fun x => le_add_self,
      ⟨1 + K + 1, ENNReal.add_ne_top.2 ⟨hK1, ENNReal.one_ne_top⟩, fun x =>
        add_le_add (hWK x) le_rfl⟩, 1 - (1 + K + 1)⁻¹, K, ENNReal.sub_lt_self
          ENNReal.one_ne_top one_ne_zero (ENNReal.inv_ne_zero.2
            (ENNReal.add_ne_top.2 ⟨hK1, ENNReal.one_ne_top⟩)), hK, C, hC,
      driftV4_of_driftV2_bounded (measurable_regV P hCm) hK1 hWK
        (regV_drift P hCm fun x _ => hb x)⟩
  tfae_have 5 → 1 := by
    rintro ⟨V, hV, hV1, ⟨M, hM, hVM⟩, ρ, b, hρ, hb, C, hC, h⟩
    exact isUniformlyErgodic_of_bounded_driftV4 hψ hap hV hV1 hM hVM hρ hb hC h
  tfae_have 2 → 5 := fun h => ⟨1, measurable_one, fun _ => le_rfl, ⟨1, ENNReal.one_ne_top,
    fun _ => le_rfl⟩, 2⁻¹, 2⁻¹, ENNReal.inv_lt_one.2 ENNReal.one_lt_two,
    ENNReal.inv_ne_top.2 two_ne_zero,
    univ, h, fun x => by
      simp only [Pi.one_apply, lintegral_one, measure_univ, mul_one, indicator_of_mem (mem_univ x)]
      rw [ENNReal.inv_two_add_inv_two]⟩
  tfae_finish

/-! ### Doeblin's condition and Theorem 16.2.3 -/

/-- **Doeblin's condition** (MT p. 402): a probability `φ`, `m`, `ε < 1` and `δ > 0` with
`Pᵐ(x, A) ≥ δ` for every `x` whenever `φ(A) > ε`. -/
def IsDoeblin (P : Kernel X X) : Prop :=
  ∃ φ : Measure X, IsProbabilityMeasure φ ∧ ∃ m : ℕ, ∃ ε δ : ℝ≥0∞, ε < 1 ∧ 0 < δ ∧
    ∀ A, MeasurableSet A → ε < φ A → ∀ x, δ ≤ (P ^ m) x A

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.2.3** (MT p. 402): an aperiodic `ψ`-irreducible chain satisfies Doeblin's
condition iff it is uniformly ergodic. Doeblin's condition makes `X ⇝ C` uniformly for a petite
`C` with `φ(C) > ε` (which exists since `X` is an increasing union of petite sets), so `X` is
petite; conversely `φ = μ` works. -/
theorem theorem_16_2_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    IsDoeblin P ↔ ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsUniformlyErgodic P μ := by
  constructor
  · rintro ⟨φ, hφ, m, ε, δ, hε, hδ, hD⟩
    obtain ⟨c, ψc, -, Cs, hmono, hpet, hcov⟩ := proposition_5_5_5_iii_cover P hψ
    -- some `Cs n` has `φ(Cs n) > ε`
    have hlim : Tendsto (fun n => φ (Cs n)) atTop (𝓝 (φ univ)) := by
      rw [← hcov]; exact tendsto_measure_iUnion_atTop hmono
    rw [measure_univ] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hε)).exists
    have hacc : SampledAccessible P (diracDist m) univ (Cs n) := by
      refine ⟨δ, hδ, fun x _ => ?_⟩
      rw [sampledKernel_diracDist]
      exact hD (Cs n) (hpet n).1 hn x
    obtain ⟨δ', -, hX⟩ := proposition_5_5_4_i P (hpet n) MeasurableSet.univ
      (isSamplingDist_diracDist m) hacc
    have key := (theorem_16_2_2 hψ hap).out 2 1
    exact key.1 ⟨_, _, hX⟩
  · rintro ⟨μ, hμp, h⟩
    have hlim := ((isUniformlyErgodic_iff P μ).1 h).2
    have hq : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hq)).exists
    refine ⟨μ, hμp, n, 2⁻¹, 2⁻¹ - vErgDist 1 P μ n, ENNReal.inv_lt_one.2 ENNReal.one_lt_two,
      tsub_pos_of_lt hn, fun A hA hμA x => ?_⟩
    have := isMarkovKernel_pow P n
    have hle := measure_le_add_fNorm (f := 1) (fun _ => le_rfl) ((P ^ n) x) μ hA
    have hrow := fNorm_pow_le_vErgDist_mul (V := 1) P μ n (x := x) one_ne_zero
      ENNReal.one_ne_top
    rw [Pi.one_apply, mul_one] at hrow
    have h4 : 2⁻¹ ≤ (P ^ n) x A + vErgDist 1 P μ n :=
      hμA.le.trans (hle.trans (add_le_add le_rfl hrow))
    exact tsub_le_iff_right.2 h4

/-! ### Theorem 16.2.4 -/

/-- **The contraction behind Theorem 16.2.4**: if `Q(x, ·) ≥ ν` for every `x`, then
`‖λQ − λ'Q‖ ≤ (1 − ν(X)) ‖λ − λ'‖` for probabilities `λ`, `λ'` (with `Q = (1 − ρ)ν' + ρR`, only
the residual part `R` separates the two laws). -/
theorem tvNorm_comp_le_of_le {Q : Kernel X X} [IsMarkovKernel Q] {ν : Measure X}
    [IsFiniteMeasure ν] (hν : ∀ x, ν ≤ Q x) (l₁ l₂ : Measure X) [IsProbabilityMeasure l₁]
    [IsProbabilityMeasure l₂] :
    tvNorm (Q ∘ₘ l₁) (Q ∘ₘ l₂) ≤ (1 - ν.real univ) * tvNorm l₁ l₂ := by
  refine tvNorm_le fun f hf h1 => ?_
  rw [integral_comp_kernel Q l₁ hf h1, integral_comp_kernel Q l₂ hf h1]
  have hνX : ∀ x, ν univ ≤ 1 := fun x => (hν x univ).trans (by simp)
  set F : X → ℝ := fun x => ∫ y, f y ∂Q x - ∫ y, f y ∂ν with hF
  have hFm : Measurable F :=
    (StronglyMeasurable.integral_kernel (κ := Q) hf.stronglyMeasurable).measurable.sub_const _
  have hFb : ∀ x, |F x| ≤ 1 - ν.real univ := fun x => by
    have hsub : Q x - ν + ν = Q x := Measure.sub_add_cancel_of_le (hν x)
    have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable f m := fun m _ =>
      integrable_of_abs_le_one hf h1
    have : IsFiniteMeasure (Q x - ν) := by
      refine ⟨lt_of_le_of_lt (Measure.sub_le (μ := Q x) (ν := ν) univ) (measure_lt_top _ _)⟩
    have hsplit : ∫ y, f y ∂Q x = ∫ y, f y ∂(Q x - ν) + ∫ y, f y ∂ν := by
      conv_lhs => rw [← hsub]
      exact integral_add_measure (hint _) (hint _)
    have hmass : (Q x - ν).real univ = 1 - ν.real univ := by
      rw [measureReal_def, Measure.sub_apply MeasurableSet.univ (hν x), measure_univ,
        ENNReal.toReal_sub_of_le (hνX x) ENNReal.one_ne_top, ENNReal.toReal_one, measureReal_def]
    rw [hF]
    simp only
    rw [hsplit, add_sub_cancel_right, ← hmass]
    exact abs_integral_le_measureReal h1
  have hc : ∫ x, (∫ y, f y ∂Q x) ∂l₁ - ∫ x, (∫ y, f y ∂Q x) ∂l₂ =
      ∫ x, F x ∂l₁ - ∫ x, F x ∂l₂ := by
    have hFint : ∀ (m : Measure X) [IsProbabilityMeasure m], Integrable F m := fun m _ =>
      Integrable.of_bound hFm.aestronglyMeasurable (1 - ν.real univ)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFb x)
    have he : ∀ (m : Measure X) [IsProbabilityMeasure m],
        ∫ x, (∫ y, f y ∂Q x) ∂m = ∫ x, F x ∂m + ∫ y, f y ∂ν := fun m _ => by
      have hfun : (fun x => ∫ y, f y ∂Q x) = fun x => F x + ∫ y, f y ∂ν := by
        funext x; simp [hF]
      rw [hfun, integral_add (hFint m) (integrable_const _), integral_const, probReal_univ,
        one_smul]
    rw [he l₁, he l₂]; ring
  rw [hc]
  rcases eq_or_lt_of_le (sub_nonneg.2 (show ν.real univ ≤ 1 by
    rw [measureReal_def]
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · simp [Measure.eq_zero_of_isEmpty ν]
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hνX x₀))) with h0 | hpos
  · have hF0 : ∀ x, F x = 0 := fun x => abs_nonpos_iff.1 ((hFb x).trans h0.symm.le)
    simp [hF0, ← h0]
  · exact abs_integral_sub_le_mul_tvNorm l₁ l₂ hFm hpos hFb

/-- Iterating the contraction: if `Pᵐ(x, ·) ≥ ν` for every `x`, then
`‖λP^{mk} − λ'P^{mk}‖ ≤ (1 − ν(X))ᵏ ‖λ − λ'‖`. -/
theorem tvNorm_pow_mul_comp_le {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    [IsFiniteMeasure ν] (hν : ∀ x, ν ≤ (P ^ m) x) (k : ℕ) (l₁ l₂ : Measure X)
    [IsProbabilityMeasure l₁] [IsProbabilityMeasure l₂] :
    tvNorm ((P ^ (m * k) : Kernel X X) ∘ₘ l₁) ((P ^ (m * k) : Kernel X X) ∘ₘ l₂) ≤
      (1 - ν.real univ) ^ k * tvNorm l₁ l₂ := by
  induction k with
  | zero =>
    rw [mul_zero, pow_zero, pow_zero, one_mul]
    change tvNorm ((Kernel.id : Kernel X X) ∘ₘ l₁) ((Kernel.id : Kernel X X) ∘ₘ l₂) ≤ _
    rw [Measure.id_comp, Measure.id_comp]
  | succ k ih =>
    have := isMarkovKernel_pow P m
    have := isMarkovKernel_pow P (m * k)
    have e : P ^ (m * (k + 1)) = (P ^ m) ∘ₖ (P ^ (m * k)) := by rw [mul_add, mul_one, pow_add_eq]
    rw [e, ← measure_kernel_assoc, ← measure_kernel_assoc]
    calc tvNorm ((P ^ m : Kernel X X) ∘ₘ ((P ^ (m * k) : Kernel X X) ∘ₘ l₁))
          ((P ^ m : Kernel X X) ∘ₘ ((P ^ (m * k) : Kernel X X) ∘ₘ l₂))
        ≤ (1 - ν.real univ) * tvNorm ((P ^ (m * k) : Kernel X X) ∘ₘ l₁)
          ((P ^ (m * k) : Kernel X X) ∘ₘ l₂) :=
          tvNorm_comp_le_of_le hν _ _
      _ ≤ (1 - ν.real univ) * ((1 - ν.real univ) ^ k * tvNorm l₁ l₂) := by
          refine mul_le_mul_of_nonneg_left ih ?_
          have hνX : ν univ ≤ 1 := by
            rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
            · simp [Measure.eq_zero_of_isEmpty ν]
            · exact ((hν x₀) univ).trans (by simp)
          rw [sub_nonneg, measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hνX)
      _ = (1 - ν.real univ) ^ (k + 1) * tvNorm l₁ l₂ := by ring

/-- **Theorem 16.2.4** (MT p. 402): if `X` is `νₘ`-small, `Pᵐ(x, ·) ≥ νₘ` for all `x`, then for
every invariant probability `μ`, `‖Pⁿ(x, ·) − μ‖ ≤ 2 ρ^{⌊n/m⌋}` with `ρ = 1 − νₘ(X)` (16.21). -/
theorem theorem_16_2_4 {P : Kernel X X} [IsMarkovKernel P] {m : ℕ} {ν : Measure X}
    (hs : IsSmallSet P m ν univ) [IsFiniteMeasure ν] {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : IsInvariant P μ) (x : X) (n : ℕ) :
    tvNorm ((P ^ n) x) μ ≤ 2 * (1 - ν.real univ) ^ (n / m) := by
  have hν : ∀ y, ν ≤ (P ^ m) y := fun y => hs.2.2.2 y (mem_univ y)
  have := isMarkovKernel_pow P (n % m)
  have := isMarkovKernel_pow P (m * (n / m))
  have e : (P ^ n) x = (P ^ (m * (n / m)) : Kernel X X) ∘ₘ ((P ^ (n % m)) x) := by
    conv_lhs => rw [← Nat.mod_add_div n m, pow_add_eq]
    rfl
  have hμk : (P ^ (m * (n / m)) : Kernel X X) ∘ₘ μ = μ := hμ.pow _
  rw [e]
  conv_lhs => rw [← hμk]
  calc tvNorm ((P ^ (m * (n / m)) : Kernel X X) ∘ₘ ((P ^ (n % m)) x))
        ((P ^ (m * (n / m)) : Kernel X X) ∘ₘ μ)
      ≤ (1 - ν.real univ) ^ (n / m) * tvNorm ((P ^ (n % m)) x) μ :=
        tvNorm_pow_mul_comp_le hν (n / m) _ _
    _ ≤ (1 - ν.real univ) ^ (n / m) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ?_ _)
        · calc tvNorm ((P ^ (n % m)) x) μ ≤ ((P ^ (n % m)) x).real univ + μ.real univ :=
                tvNorm_le_add_measureReal _ _
            _ = 2 := by rw [probReal_univ, probReal_univ]; norm_num
        · have := isMarkovKernel_pow P m
          rw [sub_nonneg, measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (hν x) univ)
    _ = 2 * (1 - ν.real univ) ^ (n / m) := mul_comm _ _

/-- The step of the counterexample to (16.21) with a real exponent: `0 ↦ 1 ↦ 2 ↦ 2`. -/
def climbStep (k : ℕ) : ℕ := min (k + 1) 2

/-- The deterministic chain `P(k, ·) = δ_{min(k + 1, 2)}`. -/
noncomputable def climbKernel : Kernel ℕ ℕ :=
  Kernel.deterministic climbStep (measurable_of_countable _)

/-- **The counterexample to (16.21) with the exponent `n/m`** (MT p. 402): for the chain
`0 ↦ 1 ↦ 2 ↦ 2` the whole space is `δ₂`-small with `m = 2`, so `ρ = 1 − δ₂(X) = 0`, and `δ₂` is
invariant, but `‖P(0, ·) − δ₂‖ = 2 > 2 ρ^{1/2} = 0`. With `⌊1/2⌋ = 0` Theorem 16.2.4 gives the
correct bound `2`. -/
theorem theorem_16_2_4_counterexample :
    IsSmallSet climbKernel 2 (Measure.dirac 2) univ ∧
      IsInvariant climbKernel (Measure.dirac 2) ∧
      ¬ ∀ x (n : ℕ), tvNorm ((climbKernel ^ n) x) (Measure.dirac 2) ≤
        2 * (1 - (Measure.dirac (2 : ℕ)).real univ) ^ ((n : ℝ) / 2) := by
  have hP : ∀ j, climbKernel j = Measure.dirac (climbStep j) := fun j =>
    Kernel.deterministic_apply _ j
  have h2 : ∀ k, (climbKernel ^ 2) k = Measure.dirac 2 := fun k => by
    rw [pow_two]
    change (climbKernel ∘ₖ climbKernel) k = _
    rw [Kernel.comp_apply, hP, Measure.dirac_bind climbKernel.measurable, hP]
    congr 1
    simp only [climbStep]
    omega
  refine ⟨⟨MeasurableSet.univ, two_pos, Measure.dirac_ne_zero, fun x _ => (h2 x).ge⟩, ?_, ?_⟩
  · unfold IsInvariant
    rw [dirac_kernel, hP]
    rfl
  · intro h
    have h1 := h 0 1
    rw [pow_one, hP] at h1
    have hlow := two_mul_abs_sub_le_tvNorm (Measure.dirac (climbStep 0)) (Measure.dirac 2)
      (by simp) (measurableSet_singleton 1)
    have hc : climbStep 0 = 1 := rfl
    rw [hc] at hlow h1
    have hz : (1 - (Measure.dirac (2 : ℕ)).real univ) = 0 := by simp
    rw [hz, Real.zero_rpow (by norm_num), mul_zero] at h1
    have : (Measure.dirac (1 : ℕ)).real {1} - (Measure.dirac (2 : ℕ)).real {1} = 1 := by
      simp [Measure.real]
    rw [this] at hlow
    norm_num at hlow
    linarith

/-! ### Theorem 16.0.2 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.0.2** (MT p. 394), for a `ψ`-irreducible chain: the following are equivalent:
(i) uniform ergodicity; (ii) `‖Pⁿ(x, ·) − π‖ ≤ R ρⁿ` (16.7); (iii) `sup_x ‖Pⁿ(x, ·) − π‖ < 1` for
some `n` (16.8); (iv) aperiodicity and Doeblin's condition (16.9); (v) `X` is `νₘ`-small;
(vi) aperiodicity and a petite `C` with `sup_x E_x[τ_C] < ∞`; (vii) aperiodicity and a petite
`C` with `sup_x E_x[κ^{τ_C}] < ∞`; (viii) aperiodicity and a bounded solution `V ≥ 1` of (16.10)
for a petite set. Under (v), (16.11) is `theorem_16_2_4`. -/
theorem theorem_16_0_2 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) :
    List.TFAE [∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsUniformlyErgodic P μ,
      ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsInvariant P μ ∧
        ∃ ρ R : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x n, tvNorm ((P ^ n) x) μ ≤ R * ρ ^ n,
      ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsInvariant P μ ∧
        ∃ n, ⨆ x, ENNReal.ofReal (tvNorm ((P ^ n) x) μ) < 1,
      IsAperiodic P ψ ∧ IsDoeblin P,
      ∃ m ν, IsSmallSet P m ν univ,
      IsAperiodic P ψ ∧ ∃ C, IsPetite P C ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x, meanReturnTime P C x ≤ K,
      IsAperiodic P ψ ∧ ∃ C, IsPetite P C ∧ ∃ κ : ℝ≥0∞, 1 < κ ∧ κ ≠ ∞ ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        ∀ x, kendallMoment P C κ x ≤ K,
      IsAperiodic P ψ ∧ ∃ V : X → ℝ≥0∞, Measurable V ∧ (∀ x, 1 ≤ V x) ∧
        (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ x, V x ≤ M) ∧
        ∃ ρ b : ℝ≥0∞, ρ < 1 ∧ b ≠ ∞ ∧ ∃ C, IsPetite P C ∧ DriftV4 P V ρ b C] := by
  tfae_have 1 → 2 := by
    rintro ⟨μ, hμp, h⟩
    exact ⟨μ, hμp, h.1, ((theorem_16_2_1 P μ h.1).out 1 2).1 h⟩
  tfae_have 2 → 3 := by
    rintro ⟨μ, hμp, hμ, h⟩
    exact ⟨μ, hμp, hμ, ((theorem_16_2_1 P μ hμ).out 2 3).1 h⟩
  tfae_have 3 → 1 := by
    rintro ⟨μ, hμp, hμ, h⟩
    exact ⟨μ, hμp, ((theorem_16_2_1 P μ hμ).out 3 1).1 h⟩
  tfae_have 1 → 5 := by
    rintro ⟨μ, hμp, h⟩
    exact isSmallSet_univ_of_isUniformlyErgodic hψ h
  tfae_have 5 → 4 := by
    rintro ⟨m, ν, hs⟩
    have hap := isAperiodic_of_isSmallSet_univ hψ hs
    have hνu : 0 < ν univ := pos_iff_ne_zero.2 fun h0 => hs.2.2.1
      (Measure.measure_univ_eq_zero.1 h0)
    have hνt : ν univ ≠ ∞ := by
      rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
      · simp [Measure.eq_zero_of_isEmpty ν]
      · have := isMarkovKernel_pow P m
        exact ne_top_of_le_ne_top (measure_ne_top ((P ^ m) x₀) univ)
          (hs.2.2.2 x₀ (mem_univ x₀) univ)
    refine ⟨hap, (ν univ)⁻¹ • ν, ⟨by rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hνu.ne' hνt]⟩, m, 2⁻¹, ν univ * 2⁻¹,
      ENNReal.inv_lt_one.2 ENNReal.one_lt_two, ENNReal.mul_pos hνu.ne' (by simp),
      fun A hA hφA x => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul] at hφA
    calc ν univ * 2⁻¹ ≤ ν univ * ((ν univ)⁻¹ * ν A) := mul_le_mul' le_rfl hφA.le
      _ = ν A := by rw [← mul_assoc, ENNReal.mul_inv_cancel hνu.ne' hνt, one_mul]
      _ ≤ (P ^ m) x A := hs.2.2.2 x (mem_univ x) A
  tfae_have 4 → 1 := fun ⟨hap, hD⟩ => (theorem_16_2_3 hψ hap).1 hD
  tfae_have 5 → 8 := by
    rintro ⟨m, ν, hs⟩
    have hap := isAperiodic_of_isSmallSet_univ hψ hs
    have key := (theorem_16_2_2 hψ hap).out 2 5
    exact ⟨hap, key.1 ⟨_, _, proposition_5_5_3 hs⟩⟩
  tfae_have 8 → 7 := fun ⟨hap, h⟩ => ⟨hap, ((theorem_16_2_2 hψ hap).out 5 4).1 h⟩
  tfae_have 7 → 6 := fun ⟨hap, h⟩ => ⟨hap, ((theorem_16_2_2 hψ hap).out 4 3).1 h⟩
  tfae_have 6 → 8 := fun ⟨hap, h⟩ => ⟨hap, ((theorem_16_2_2 hψ hap).out 3 5).1 h⟩
  tfae_have 8 → 1 := fun ⟨hap, h⟩ => ((theorem_16_2_2 hψ hap).out 5 1).1 h
  tfae_finish

/-! ### i.i.d. chains -/

/-- **An i.i.d. chain is uniformly ergodic** (MT pp. 404, 408): for `P(x, ·) = μ`,
`Pⁿ(x, ·) = μ` for `n ≥ 1`, whatever the law `μ`. -/
theorem isUniformlyErgodic_const (μ : Measure X) [IsProbabilityMeasure μ] :
    IsUniformlyErgodic (Kernel.const X μ) μ := by
  have hpow : ∀ n x, ((Kernel.const X μ) ^ (n + 1)) x = μ := fun n x => by
    have := isMarkovKernel_pow (Kernel.const X μ) n
    rw [pow_succ']
    change (Kernel.const X μ ∘ₖ (Kernel.const X μ ^ n)) x = μ
    rw [Kernel.const_comp', Kernel.const_apply]
  refine ⟨?_, tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => ?_⟩
  · unfold IsInvariant
    rw [Measure.const_comp, measure_univ, one_smul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    refine le_antisymm (iSup_le fun x => ?_) zero_le
    rw [hpow k x, tvNorm_self, ENNReal.ofReal_zero]

/-! ### Theorem 16.2.5 -/

variable [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] [CompactSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 16.2.5** (MT p. 406): a `ψ`-irreducible aperiodic T-chain on a compact space is
uniformly ergodic: `X` is petite (Theorem 6.2.5 (ii)) and Theorem 16.2.2 applies. -/
theorem theorem_16_2_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) (hT : IsTChain P) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsUniformlyErgodic P μ :=
  ((theorem_16_2_2 hψ hap).out 2 1).1 (theorem_6_2_5_ii hψ.2.1 hψ.1 hT isCompact_univ)

end MeynTweedie.VUniformErgodicity
