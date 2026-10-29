/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.RegenerativeDecomposition
import GeometricErgodicity.Cycles
import GeometricErgodicity.HarrisProperties

/-!
# Ergodic atoms (MT §13.1.2, §13.2.2, Theorem 13.3.1 (i))

Meyn and Tweedie, pp. 318–319, 323 and 326–327.

**Ergodic atoms.**
* `IsErgodicAtom P π α` (13.22), p. 319: `Pⁿ(α, α) → π(α)`.
* `tendsto_atomRenewal_of_aperiodicLaw`: if `π = π(α) μ°_α`, `L(α, α) = 1` and the return-time
  law `p(n) = P_α(τ_α = n)` is aperiodic, then `u(n) = Pⁿ(α, α) → π(α)`: the renewal theorem
  (`renewal_theorem`, Theorem 13.2.3 with `a = δ₀`) with `m_p = E_α[τ_α] = π(α)⁻¹`.
* `dvd_of_atomRenewal_pos`: a common divisor of `{n : p(n) > 0}` divides every `n` with
  `Pⁿ(α, α) > 0`.
* `isAperiodicLaw_entryLaw`: for an accessible atom of an aperiodic chain the return-time law is
  aperiodic (`α` is small with `ν = Pᵐ(α, ·)`, and every element of the set of small times `E_α`
  has `Pⁿ(α, α) > 0`; the g.c.d. of `E_α` is the period `1`, Theorem 5.4.4).
* **Proposition 13.2.4 (i)** (`proposition_13_2_4_i`, p. 323): for a positive aperiodic chain,
  every accessible atom is ergodic.
* `isAperiodic_of_isErgodicAtom` (p. 319, after (13.22)): for a positive chain, an accessible
  atom can be ergodic only if the chain is aperiodic.

**Convergence from an ergodic atom.**
* `tendsto_tvNorm_of_ergodic_atom`: if `π = π(α) μ°_α`, `u(n) → π(α)` and the initial law `λ`
  reaches `α` almost surely (`∫ λ(dx) L(x, α) = 1`), then `‖λPⁿ − π‖ → 0`. This is the
  prescription (E1)–(E3) of pp. 325–326: each of the three terms of `tvNorm_comp_pow_succ_le`
  tends to `0` (`P_λ(τ_α ≥ n) → 0`, (13.56); `|a_λ ∗ u − π(α)| ∗ t₁ → 0` by Lemma D.7.1 twice,
  (13.51), (13.55); the tail of `π(X) = π(α) Σ t₁(j)`, (13.54)).
* **Theorem 13.3.1 (i)** (`theorem_13_3_1_i`, p. 326): a positive Harris chain with an
  accessible ergodic atom satisfies `‖λPⁿ − π‖ → 0` for every initial probability `λ`;
  `theorem_13_3_1_i_aperiodic`: the same for an aperiodic positive Harris chain with an
  accessible atom.

**Corrections.** None. Proposition 13.2.4 (i) is stated for "positive recurrent aperiodic"
chains; positivity already gives recurrence (Proposition 10.1.1).
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- An **ergodic atom** (13.22), MT p. 319: `Pⁿ(a, α) → π(α)` for (every) `a ∈ α`. -/
def IsErgodicAtom (P : Kernel X X) (π : Measure X) (α : Set X) : Prop :=
  ∀ a ∈ α, Tendsto (atomRenewal P α a) atTop (𝓝 (π α).toReal)

/-! ### The renewal theorem at an atom -/

/-- If `π = π(α) μ°_α`, `L(a, α) = 1` and the return-time law is aperiodic, then
`Pⁿ(a, α) → π(α)`. -/
theorem tendsto_atomRenewal_of_aperiodicLaw {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a) (hL : hitProb P α a = 1)
    (hap : IsAperiodicLaw (entryLaw P hα.1 (Measure.dirac a))) :
    Tendsto (atomRenewal P α a) atTop (𝓝 (π α).toReal) := by
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  rw [atomRenewal_eq_realRenewalSeq hα ha, measure_atom_toReal_of_rep P hα.1 a hπ,
    ← incrMean_entryLaw P hα.1 hL hm]
  exact renewal_theorem (isIncrementLaw_entryLaw P hα.1 hL) hap

/-- A positive renewal probability `Pⁿ(a, α) > 0` forces every common divisor of the support of
the return-time law to divide `n`. -/
theorem dvd_of_atomRenewal_pos {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {d : ℕ}
    (hd : ∀ n, 0 < entryLaw P hα.1 (Measure.dirac a) n → d ∣ n) :
    ∀ n, 0 < atomRenewal P α a n → d ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hpos
    rcases n with _ | n
    · exact dvd_zero d
    · have h := comp_pow_succ_atom_toReal hα ha (Measure.dirac a) n
      rw [dirac_kernel] at h
      change 0 < ((P ^ (n + 1) : Kernel X X) a α).toReal at hpos
      rw [h, realConv_eq_sum_range, Finset.sum_pos_iff_of_nonneg (fun k _ =>
        mul_nonneg (entryLaw_nonneg P hα.1 _ k) (atomRenewal_nonneg P α a _))] at hpos
      obtain ⟨k, hk, hkpos⟩ := hpos
      have hk' := Finset.mem_range.1 hk
      have hp : 0 < entryLaw P hα.1 (Measure.dirac a) k := by
        rcases (entryLaw_nonneg P hα.1 (Measure.dirac a) k).lt_or_eq with h0 | h0
        · exact h0
        · rw [← h0, zero_mul] at hkpos; exact absurd hkpos (lt_irrefl 0)
      have hu : 0 < atomRenewal P α a (n + 1 - k) := by
        rcases (atomRenewal_nonneg P α a (n + 1 - k)).lt_or_eq with h0 | h0
        · exact h0
        · rw [← h0, mul_zero] at hkpos; exact absurd hkpos (lt_irrefl 0)
      have hk0 : 0 < k := by
        rcases k with _ | k
        · exact absurd hp (by simp)
        · exact Nat.succ_pos k
      have h1 := hd k hp
      have h2 := ih (n + 1 - k) (by omega) hu
      have := Nat.dvd_add h1 h2
      rwa [show k + (n + 1 - k) = n + 1 by omega] at this

/-- For an accessible atom `α ∋ a`, `α` is `Pᵐ(a, ·)`-small for some `m ≥ 1` with
`Pᵐ(a, α) > 0`. -/
theorem IsAccessibleAtom.exists_isSmallSet {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) {a : X} (ha : a ∈ α) :
    ∃ m, 0 < m ∧ IsSmallSet P m ((P ^ m : Kernel X X) a) α ∧ 0 < (P ^ m : Kernel X X) a α := by
  obtain ⟨m, hm⟩ := (hitProb_pos_iff P h.1.1 a).1 (h.2.1.2.1 α h.1.1 h.2.2 a)
  refine ⟨m + 1, Nat.succ_pos m, ⟨h.1.1, Nat.succ_pos m, fun h0 => ?_, fun x hx => ?_⟩, hm⟩
  · rw [h0, Measure.coe_zero, Pi.zero_apply] at hm; exact lt_irrefl 0 hm
  · rw [h.1.pow_succ_eq hx ha]

/-- **The return-time law is aperiodic** for an accessible atom of an aperiodic chain. -/
theorem isAperiodicLaw_entryLaw {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) (hap : IsAperiodic P ψ) {a : X} (ha : a ∈ α) :
    IsAperiodicLaw (entryLaw P h.1.1 (Measure.dirac a)) := by
  intro d hd
  obtain ⟨m, hm0, hsmall, hmpos⟩ := h.exists_isSmallSet ha
  have hS := smallTimes_isAddClosed P (ν := (P ^ m : Kernel X X) a) hmpos
  have hmem := mem_smallTimes_of_isSmallSet hsmall
  have hg : 1 = setGcd (smallTimes P α ((P ^ m : Kernel X X) a)) :=
    hap.eq_gcd h.2.1 hsmall h.2.2 hmpos
  have hdvd : ∀ s ∈ smallTimes P α ((P ^ m : Kernel X X) a), d ∣ s := by
    rintro s ⟨hs0, δ, hδ, hs⟩
    refine dvd_of_atomRenewal_pos h.1 ha hd s ?_
    have h1 : δ * (P ^ m : Kernel X X) a α ≤ (P ^ s : Kernel X X) a α := by
      have := hs a ha α
      rwa [Measure.smul_apply, smul_eq_mul] at this
    have h2 : 0 < (P ^ s : Kernel X X) a α :=
      lt_of_lt_of_le (ENNReal.mul_pos hδ.ne' hmpos.ne') h1
    have := isMarkovKernel_pow P s
    exact ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
  have := dvd_setGcd hS hmem hm0 hdvd
  rw [← hg] at this
  exact Nat.dvd_one.1 this

/-- **Proposition 13.2.4 (i)** (MT p. 323): for a positive aperiodic chain every accessible atom
is ergodic, `Pⁿ(α, α) → π(α)`. -/
theorem proposition_13_2_4_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (hpos : IsPositive P ψ) (hap : IsAperiodic P ψ) (h : IsAccessibleAtom P ψ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) : IsErgodicAtom P π α := by
  intro a ha
  have hrec := proposition_10_1_1 hpos
  exact tendsto_atomRenewal_of_aperiodicLaw h.1 ha (eq_smul_atomMeasure_of_accessible h hrec ha hπ)
    ((h.isRecurrentChain_iff ha).1 hrec) (isAperiodicLaw_entryLaw h hap ha)

/-- MT p. 319: for a recurrent chain, an accessible atom can be ergodic only if the chain is
aperiodic (since `Pⁿ(α, α) → π(α) > 0`, all large times are small times of `α`). -/
theorem isAperiodic_of_isErgodicAtom {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (h : IsAccessibleAtom P ψ α) (hrec : IsRecurrentChain P ψ) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (herg : IsErgodicAtom P π α) :
    IsAperiodic P ψ := by
  obtain ⟨a, ha⟩ : α.Nonempty := nonempty_of_measure_ne_zero h.2.2.ne'
  have hrep := eq_smul_atomMeasure_of_accessible h hrec ha hπ
  have hc : 0 < (π α).toReal :=
    ENNReal.toReal_pos (measure_atom_ne_zero_of_rep P h.1.1 a hrep) (measure_ne_top π α)
  obtain ⟨N, hN⟩ := (tendsto_order.1 (herg a ha)).1 0 hc |>.exists_forall_of_atTop
  obtain ⟨m, hm0, hsmall, hmpos⟩ := h.exists_isSmallSet ha
  set ν := (P ^ m : Kernel X X) a
  have hS := smallTimes_isAddClosed P (ν := ν) hmpos
  have hmem := mem_smallTimes_of_isSmallSet hsmall
  have hk : ∀ k, N + 1 ≤ k → k + m ∈ smallTimes P α ν := fun k hk => by
    have hu : 0 < (P ^ k : Kernel X X) a α := by
      have := hN k (by omega)
      exact ENNReal.toReal_pos_iff.1 this |>.1
    refine ⟨by omega, (P ^ k : Kernel X X) a α, hu, fun x hx => Measure.le_intro fun B hB _ => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    have h1 := pow_add_ge_of_le P (m := k) (n := m) (C := α)
      (fun y hy => (hsmall.2.2.2 y hy)) x hB
    rw [show (P ^ k : Kernel X X) x α = (P ^ k : Kernel X X) a α by
      rw [show k = (k - 1) + 1 by omega, h.1.pow_succ_eq hx ha]] at h1
    exact h1
  have h1 := setGcd_dvd hS hmem hm0 (hk (N + 1) le_rfl)
  have h2 := setGcd_dvd hS hmem hm0 (hk (N + 2) (by omega))
  have hg : setGcd (smallTimes P α ν) = 1 :=
    Nat.dvd_one.1 (by simpa [show N + 2 + m - (N + 1 + m) = 1 by omega] using Nat.dvd_sub h2 h1)
  have := isPeriod_gcd P h.2.1 hsmall h.2.2 hmpos
  rwa [hg] at this

/-! ### Convergence from an ergodic atom -/

/-- **Convergence from an ergodic atom.** If `π = π(α) μ°_α` is a probability, `Pⁿ(a, α) → π(α)`
and the initial probability `λ` reaches `α` almost surely, then `‖λPⁿ − π‖ → 0`. -/
theorem tendsto_tvNorm_of_ergodic_atom {P : Kernel X X} [IsMarkovKernel P] {α : Set X}
    (hα : IsAtom P α) {a : X} (ha : a ∈ α) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : π = π α • atomMeasure P hα.1 a)
    (herg : Tendsto (atomRenewal P α a) atTop (𝓝 (π α).toReal)) (μ : Measure X)
    [IsProbabilityMeasure μ] (hμ : ∫⁻ x, hitProb P α x ∂μ = 1) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  have hm := meanReturnTime_ne_top_of_rep P hα.1 a hπ
  set c := (π α).toReal
  set t := lastExitSeq P hα.1 a 1
  have h1C : ∀ y, (1 : X → ℝ≥0∞) y ≤ 1 := fun _ => le_rfl
  have hts : Summable t :=
    (summable_nat_add_iff 1).1 (summable_lastExitSeq P hα.1 a hm ENNReal.one_ne_top h1C)
  have hE := hasSum_entryLaw P hα.1 μ
  rw [hμ, ENNReal.toReal_one] at hE
  -- (E2): `P_λ(τ_α ≥ n + 1) → 0`
  have hA : Tendsto (fun n => (tabooSeq P hα.1 μ n univ).toReal) atTop (𝓝 0) := by
    simp_rw [tabooSeq_univ_toReal P hα.1 μ, measureReal_def, measure_univ, ENNReal.toReal_one]
    have := (hE.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub 1
    simpa using this
  -- (E3): `|a_λ ∗ u − π(α)| ∗ t₁ → 0`
  have hau : Tendsto (realConv (entryLaw P hα.1 μ) (atomRenewal P α a)) atTop (𝓝 c) := by
    have := lemma_D_7_1 (entryLaw_nonneg P hα.1 μ) hE.summable herg
    rwa [hE.tsum_eq, mul_one] at this
  have hw : Tendsto (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - c|) atTop
      (𝓝 0) := by
    have := (hau.sub_const c).abs
    simpa using this
  have hB : Tendsto (realConv (fun k => |realConv (entryLaw P hα.1 μ) (atomRenewal P α a) k - c|)
      t) atTop (𝓝 0) := by
    rw [realConv_comm]
    have := lemma_D_7_1 (lastExitSeq_nonneg P hα.1 a 1) hts hw
    simpa using this
  -- (E1): the tail of `π(X) = π(α) Σ t₁(j)`
  have hC : Tendsto (fun n => c * ∑' i, t (i + n + 2)) atTop (𝓝 0) := by
    have := (tendsto_sum_nat_add t).comp (tendsto_add_atTop_nat 2)
    have h2 := this.const_mul c
    simp only [mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    congr 1
  have hbound := ((hA.add (hB.comp (tendsto_add_atTop_nat 1))).add hC)
  simp only [add_zero] at hbound
  rw [← tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_) hbound
  exact tvNorm_comp_pow_succ_le hα ha hπ μ n

/-- Harris recurrence gives `L(x, α) = 1` for every `x` and every `α ∈ B⁺(X)`. -/
theorem IsHarris.hitProb_eq_one [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) (x : X) : hitProb P A x = 1 :=
  le_antisymm (hitProb_le_one P A x)
    ((theorem_9_1_4 hH hA hψA x).symm.le.trans (harrisQ_le_hitProb P A x))

/-- For a Harris chain every initial law reaches `α ∈ B⁺(X)` almost surely. -/
theorem IsHarris.lintegral_hitProb_eq [MeasurableSpace.CountablyGenerated X] {P : Kernel X X}
    [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) (μ : Measure X) [IsProbabilityMeasure μ] : ∫⁻ x, hitProb P A x ∂μ = 1 := by
  simp_rw [hH.hitProb_eq_one hA hψA]
  rw [lintegral_one, measure_univ]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.1 (i)** (MT p. 326): a positive Harris chain with an accessible ergodic atom
satisfies `‖λPⁿ − π‖ → 0` for every initial probability `λ`. -/
theorem theorem_13_3_1_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {α : Set X}
    (hph : IsPositiveHarris P ψ) (h : IsAccessibleAtom P ψ α) {π : Measure X}
    [IsProbabilityMeasure π] (hπ : IsInvariant P π) (herg : IsErgodicAtom P π α)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ : α.Nonempty := nonempty_of_measure_ne_zero h.2.2.ne'
  exact tendsto_tvNorm_of_ergodic_atom h.1 ha
    (eq_smul_atomMeasure_of_accessible h (proposition_10_1_1 hph.2) ha hπ) (herg a ha) μ
    (hph.1.lintegral_hitProb_eq h.1.1 h.2.2 μ)

variable [MeasurableSpace.CountablyGenerated X] in
/-- Theorem 13.3.1 (i) with Proposition 13.2.4 (i): an aperiodic positive Harris chain with an
accessible atom satisfies `‖λPⁿ − π‖ → 0` for every initial probability `λ`. -/
theorem theorem_13_3_1_i_aperiodic {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {α : Set X} (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) (h : IsAccessibleAtom P ψ α)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (μ : Measure X)
    [IsProbabilityMeasure μ] :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) :=
  theorem_13_3_1_i hph h hπ (proposition_13_2_4_i hph.2 hap h hπ) μ

end MeynTweedie.GeometricErgodicity
