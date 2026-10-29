/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.NullRecurrence
import GeneralizedDrift.PeriodicErgodic

/-!
# Null Harris chains of any period (MT §18.1–18.2, the step "from Theorem 18.1.3")

Copied for Chapter 19 from the Chapter 18 project
(`Positivity/NullPeriodic.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to this project's modules.

Meyn and Tweedie, pp. 470–471. Theorems 18.2.1 and 18.2.2 apply Theorem 18.1.3, which is stated
for aperiodic chains, to chains of arbitrary period. This module supplies that step for Harris
chains. The state space is countably generated.

* `IsCycle.absorbKernel_isHarris_isAperiodic`: for a Harris chain of period `d` with `d`-cycle
  `{Dᵢ}`, the chain moving by `Pᵈ` on `Dᵢ` and jumping to a probability carried by `Dᵢ` off `Dᵢ`
  is Harris (for `ψ|_{Dᵢ}`) and aperiodic (the argument of Theorem 13.3.4, with no positivity).
* `tendsto_of_forall_mul_add`: a sequence whose residue classes mod `d` tend to `0` tends to `0`.
* `tendsto_pow_of_isHarris_of_isNull`: for a Harris null chain with a nonzero σ-finite invariant
  `π`, `Pⁿ(x, A) → 0` for every `x` and every `A` with `π(A) < ∞`. Each class `Dᵢ` has
  `π(Dᵢ) = ∞`, so Theorem 18.1.3 (through its core
  `tendsto_iSup_div_of_measure_univ_eq_top`, for the subinvariant `π|_{Dᵢ}`) applies to the
  restricted skeleton; the chain leaves `(⋃ Dᵢ)ᶜ` (`IsCycle.tendsto_compl_iUnion`).
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### The chain `Pᵈ` on a cycle class -/

variable {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ} {D : ZMod d → Set X}

variable [MeasurableSpace.CountablyGenerated X] in
/-- **The `d`-skeleton on a cycle class.** For a Harris chain of period `d` with `d`-cycle
`{Dᵢ}`, the chain that moves by `Pᵈ` on `Dᵢ` and jumps to a probability `σ` carried by `Dᵢ`
off `Dᵢ` is Harris, with maximal irreducibility measure `ψ|_{Dᵢ}`, and aperiodic
(Proposition 5.4.6). No positivity is assumed. -/
theorem IsCycle.absorbKernel_isHarris_isAperiodic (hD : IsCycle P ψ d D)
    (hper : IsPeriod P ψ d) (hH : IsHarris P ψ) (i : ZMod d) (σ : Measure X)
    [IsProbabilityMeasure σ] (hσ : σ (D i)ᶜ = 0) :
    haveI := isMarkovKernel_pow P d
    haveI := isMarkovKernel_absorbKernel (P ^ d) (hD.measurableSet i) σ
    IsHarris (absorbKernel (P ^ d) (hD.measurableSet i) σ) (ψ.restrict (D i)) ∧
      IsAperiodic (absorbKernel (P ^ d) (hD.measurableSet i) σ) (ψ.restrict (D i)) := by
  have hd : 0 < d := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hψ := hH.1
  set H := D i with hHdef
  have hHm : MeasurableSet H := hD.measurableSet i
  have := isMarkovKernel_pow P d
  set Q : Kernel X X := P ^ d with hQdef
  have hQ : ∀ x ∈ H, Q x Hᶜ = 0 := hD.pow_d_compl_eq_zero i
  have := isMarkovKernel_absorbKernel Q hHm σ
  set K := absorbKernel Q hHm σ with hKdef
  have hψH : 0 < ψ H := hD.measure_pos hψ hd i
  have hLH : ∀ x ∈ H, ∀ A, MeasurableSet A → 0 < ψ (A ∩ H) → hitProb K A x = 1 :=
    fun x hx A hA hψA => by
      rw [hitProb_absorbKernel_of_mem hHm hQ hA hx]
      exact le_antisymm (hitProb_le_one _ _ _)
        ((hD.hitProb_pow_eq_one hd hH (hA.inter hHm) inter_subset_right hψA hx).symm.le.trans
          (hitProb_mono _ inter_subset_left x))
  have hLall : ∀ x, ∀ A, MeasurableSet A → 0 < ψ (A ∩ H) → hitProb K A x = 1 :=
    fun x A hA hψA => by
      by_cases hxH : x ∈ H
      · exact hLH x hxH A hA hψA
      · have hKx : K x = σ := absorbKernel_of_notMem Q hHm σ hxH
        rw [hitProb_first_step K hA x, hKx]
        have hae : ∀ᵐ y ∂σ, y ∈ Aᶜ → hitProb K A y = 1 := by
          have : ∀ᵐ y ∂σ, y ∈ H := by rw [ae_iff]; exact hσ
          filter_upwards [this] with y hy _
          exact hLH y hy A hA hψA
        rw [setLIntegral_congr_fun_ae hA.compl hae, setLIntegral_one,
          measure_add_measure_compl hA, measure_univ]
  have hirr : IsPhiIrreducible K (ψ.restrict H) := fun A hA hpos x => by
    rw [Measure.restrict_apply hA] at hpos
    rw [hLall x A hA hpos]; exact one_pos
  have hmax : IsMaximalIrreducibility K (ψ.restrict H) := by
    refine ⟨fun h0 => ?_, hirr, fun φ hφ => Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
    · have := congrArg (fun m : Measure X => m univ) h0
      simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact hψH.ne' this
    · rw [Measure.restrict_apply hA] at h0
      by_contra hne
      have hpos := hφ A hA (pos_iff_ne_zero.2 hne)
      have hnull := hψ.hitSet_null (hA.inter hHm) h0
      obtain ⟨x, hxH, hx⟩ : ∃ x ∈ H, ¬ 0 < hitProb P (A ∩ H) x := by
        by_contra hall
        push Not at hall
        exact hψH.ne' (nonpos_iff_eq_zero.1 (hnull ▸ measure_mono fun y hy => hall y hy))
      have hx0 : hitProb P (A ∩ H) x = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hx)
      have hK0 : hitProb K A x = 0 := by
        rw [hitProb_absorbKernel_of_mem hHm hQ hA hxH, hitProb_eq_tsum _ hA]
        refine ENNReal.tsum_eq_zero.2 fun n => nonpos_iff_eq_zero.1 ?_
        calc tabooKernel Q hA n x A
            ≤ tabooKernel Q hA n x (A ∩ H) + tabooKernel Q hA n x Hᶜ := by
              refine (measure_mono fun y hy => ?_).trans (measure_union_le _ _)
              by_cases h : y ∈ H
              · exact Or.inl ⟨hy, h⟩
              · exact Or.inr h
          _ = tabooKernel Q hA n x (A ∩ H) := by
              rw [tabooKernel_compl_eq_zero_of_absorbing hHm hQ hA n hxH, add_zero]
          _ ≤ (Q ^ (n + 1) : Kernel X X) x (A ∩ H) := tabooKernel_le_pow Q hA n x (hA.inter hHm)
          _ = (P ^ (d * (n + 1) - 1 + 1) : Kernel X X) x (A ∩ H) := by
              rw [hQdef, ← pow_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
                (Nat.mul_ne_zero hd.ne' (Nat.succ_ne_zero n)))]
          _ ≤ hitProb P (A ∩ H) x := pow_le_hitProb P (hA.inter hHm) _ x
          _ = 0 := hx0
      exact absurd hK0 (hpos x).ne'
  have hHK : IsHarris K (ψ.restrict H) := by
    refine ⟨hmax, fun A hA hψA => (proposition_9_1_1 K hA fun x _ => ?_).2⟩
    rw [Measure.restrict_apply hA] at hψA
    exact hLall x A hA hψA
  refine ⟨hHK, ?_⟩
  obtain ⟨C, hCH, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ hHm hψH
  have hgcd : d = setGcd (smallTimes P C ν) := hper.eq_gcd hψ hC hψC hνC
  obtain ⟨N, hN⟩ := exists_isSmallSet_mul_gcd hC hνC
  rw [← hgcd] at hN
  have hKsmall : ∀ n ≥ N, ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ C, δ • ν ≤ (K ^ n : Kernel X X) x :=
    fun n hn => by
      obtain ⟨δ, hδ, hsm⟩ := hN n hn
      refine ⟨δ, hδ, fun x hx => ?_⟩
      have hKn : (K ^ n : Kernel X X) x = (Q ^ n : Kernel X X) x :=
        absorbKernel_pow_of_mem hHm hQ n x (hCH hx)
      rw [hKn, hQdef, ← pow_mul, mul_comm]
      exact hsm.2.2.2 x hx
  have hmem : ∀ n ≥ N + 1, n ∈ smallTimes K C ν := fun n hn => by
    obtain ⟨δ, hδ, h⟩ := hKsmall n (by omega)
    exact ⟨by omega, δ, hδ, h⟩
  obtain ⟨δ₀, hδ₀, h₀⟩ := hKsmall (N + 1) (by omega)
  have hν0 : (δ₀ • ν) ≠ 0 := smul_measure_ne_zero hC.2.2.1 hδ₀.ne'
  have hsC : IsSmallSet K (N + 1) (δ₀ • ν) C := ⟨hC.1, by omega, hν0, h₀⟩
  have hψC' : 0 < (ψ.restrict H) C := by
    rw [Measure.restrict_apply hC.1, inter_eq_left.2 hCH]; exact hψC
  have hδν : 0 < (δ₀ • ν) C := by
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ₀.ne' hνC.ne'
  have hδt : δ₀ ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
    have := isMarkovKernel_pow K (N + 1)
    intro htop
    have h1 := (h₀ x hx C).trans prob_le_one
    rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.top_mul hνC.ne'] at h1
    exact absurd h1 (by simp)
  have hperK := isPeriod_gcd K hmax hsC hψC' hδν
  rw [smallTimes_smul K C ν hδ₀.ne' hδt] at hperK
  have hS := smallTimes_isAddClosed K hνC
  have h1 := setGcd_dvd hS (hmem (N + 1) le_rfl) (by omega) (hmem (N + 1) le_rfl)
  have h2 := setGcd_dvd hS (hmem (N + 1) le_rfl) (by omega) (hmem (N + 2) (by omega))
  have hg : setGcd (smallTimes K C ν) = 1 :=
    Nat.dvd_one.1 (by simpa using Nat.dvd_sub h2 h1)
  rwa [hg] at hperK

/-! ### Null Harris chains of any period -/

omit [MeasurableSpace X] in
/-- If every residue class `n ≡ r (mod d)` of a `[0, ∞]`-sequence tends to `0`, the sequence
does. -/
theorem tendsto_of_forall_mul_add {f : ℕ → ℝ≥0∞} {d : ℕ} (hd : 0 < d)
    (h : ∀ r < d, Tendsto (fun n => f (d * n + r)) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hN : ∀ r < d, ∃ N, ∀ n ≥ N, f (d * n + r) ≤ ε := fun r hr =>
    eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 (h r hr)) ε hε)
  choose! N hN using hN
  set N₀ := (Finset.range d).sup N with hN₀
  refine eventually_atTop.2 ⟨d * N₀, fun n hn => ?_⟩
  have hr : n % d < d := Nat.mod_lt n hd
  have hk : N (n % d) ≤ n / d := by
    have h1 : N (n % d) ≤ N₀ := Finset.le_sup (f := N) (Finset.mem_range.2 hr)
    have h2 : N₀ ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hn)
    omega
  have := hN (n % d) hr (n / d) hk
  rwa [Nat.div_add_mod] at this

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Null Harris chains, any period**: for a Harris null chain with a nonzero σ-finite invariant
measure `π`, `Pⁿ(x, A) → 0` for every `x` and every `A` with `π(A) < ∞`. For an aperiodic chain
this is Theorem 18.1.3; in general it is applied on each cycle class to the `d`-skeleton
(`IsCycle.absorbKernel_isHarris_isAperiodic`), and the chain leaves the null set
`(⋃ Dᵢ)ᶜ` (Harris recurrence). -/
theorem tendsto_pow_of_isHarris_of_isNull (hH : IsHarris P ψ) (hnull : IsNull P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) {A : Set X}
    (hA : MeasurableSet A) (hπA : π A ≠ ∞) (x : X) :
    Tendsto (fun n => (P ^ n : Kernel X X) x A) atTop (𝓝 0) := by
  obtain ⟨d, hper⟩ := exists_isPeriod P hH.1
  obtain ⟨D, hD⟩ := hper.2.1
  have hd : 0 < d := hper.1
  have : NeZero d := ⟨hd.ne'⟩
  have hrec := hH.isRecurrentChain
  have hac := theorem_10_4_9_equiv hrec hπ hπ0
  set U := ⋃ j, D j with hUdef
  have hU : MeasurableSet U := MeasurableSet.iUnion hD.measurableSet
  have hinf := hnull.measure_univ_eq_top hπ.2 hπ0
  -- every class has infinite mass
  have hDinf : ∀ i, π (D i) = ∞ := fun i => by
    by_contra hfin
    have hUc : π Uᶜ = 0 := hac.1 hD.null_compl
    have hle : π univ ≤ ∑ j : ZMod d, π (D j) := by
      calc π univ ≤ π U + π Uᶜ := by
            rw [← measure_union disjoint_compl_right hU.compl, union_compl_self]
        _ = π U := by rw [hUc, add_zero]
        _ ≤ ∑' j, π (D j) := measure_iUnion_le _
        _ = ∑ j : ZMod d, π (D j) := tsum_fintype _
    have heq : ∀ j, π (D j) = π (D i) := fun j => hD.measure_eq hd hπ.2 j i
    simp_rw [heq, Finset.sum_const, Finset.card_univ, ZMod.card] at hle
    rw [hinf, top_le_iff, nsmul_eq_mul] at hle
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin hle
  -- the skeleton on a class
  have hskel : ∀ i, ∀ y ∈ D i, Tendsto (fun n => (P ^ (d * n) : Kernel X X) y A) atTop
      (𝓝 0) := fun i y hy => by
    have := isMarkovKernel_pow P d
    set Q : Kernel X X := P ^ d with hQdef
    have hHm := hD.measurableSet i
    have hQ : ∀ x ∈ D i, Q x (D i)ᶜ = 0 := hD.pow_d_compl_eq_zero i
    set σ := Q y with hσdef
    have hσ : σ (D i)ᶜ = 0 := hQ y hy
    have := isMarkovKernel_absorbKernel Q hHm σ
    obtain ⟨hHK, hapK⟩ := hD.absorbKernel_isHarris_isAperiodic hper hH i σ hσ
    set K := absorbKernel Q hHm σ with hKdef
    set π' := π.restrict (D i) with hπ'
    have hπ'c : π' (D i)ᶜ = 0 := by
      rw [hπ', Measure.restrict_apply hHm.compl, compl_inter_self, measure_empty]
    have hsub : IsSubinvariant K π' := by
      unfold IsSubinvariant
      rw [comp_congr_of_compl_eq_zero hπ'c fun z hz => absorbKernel_of_mem Q hHm σ hz]
      have h := hD.comp_pow_restrict_le hπ.2 d i
      rwa [ZMod.natCast_self, add_zero] at h
    have hπ'inf : π' univ = ∞ := by rw [hπ', Measure.restrict_apply_univ, hDinf i]
    have hcore := tendsto_iSup_div_of_measure_univ_eq_top hHK hapK hsub hπ'inf
      (Measure.dirac y) one_pos
    have hratio : Tendsto (fun n => (K ^ n : Kernel X X) y A / (π' A + 1)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcore
        (fun n => zero_le) fun n => ?_
      have := isMarkovKernel_pow K n
      rw [← dirac_kernel (K ^ n : Kernel X X) y]
      exact le_iSup₂ (f := fun (B : Set X) (_ : MeasurableSet B) =>
        ((K ^ n : Kernel X X) ∘ₘ Measure.dirac y) B / (π' B + 1)) A hA
    have hc0 : π' A + 1 ≠ 0 := by simp
    have hct : π' A + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top hπA
      (by rw [hπ', Measure.restrict_apply hA]; exact measure_mono inter_subset_left),
      ENNReal.one_ne_top⟩
    have hmul := ENNReal.Tendsto.mul_const hratio (Or.inr hct)
    rw [zero_mul] at hmul
    refine hmul.congr fun n => ?_
    rw [ENNReal.div_mul_cancel hc0 hct]
    have hKn : (K ^ n : Kernel X X) y = (Q ^ n : Kernel X X) y :=
      absorbKernel_pow_of_mem hHm hQ n y hy
    rw [hKn, hQdef, ← pow_mul]
  -- from the classes
  have hUconv : ∀ y ∈ U, Tendsto (fun n => (P ^ n : Kernel X X) y A) atTop (𝓝 0) :=
    fun y hy => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      refine tendsto_of_forall_mul_add hd fun r _ => ?_
      have hr := hD.pow_compl_eq_zero r hi
      have hint : ∀ n, (P ^ (d * n + r) : Kernel X X) y A =
          ∫⁻ z, (P ^ (d * n) : Kernel X X) z A ∂(P ^ r : Kernel X X) y := fun n => by
        rw [add_comm, Kernel.pow_add_apply_eq_lintegral P r (d * n) y hA]
      simp_rw [hint]
      have := isMarkovKernel_pow P r
      have h := tendsto_lintegral_of_dominated_convergence (μ := (P ^ r : Kernel X X) y)
        (fun _ => 1) (fun n => Kernel.measurable_coe (P ^ (d * n) : Kernel X X) hA)
        (fun n => Filter.Eventually.of_forall fun z => by
          have := isMarkovKernel_pow P (d * n); exact prob_le_one)
        (by simp)
        (by
          have hae : ∀ᵐ z ∂(P ^ r : Kernel X X) y, z ∈ D (i + r) := by
            rw [ae_iff]; exact hr
          filter_upwards [hae] with z hz
          exact hskel (i + r) z hz)
      simpa using h
  -- from anywhere
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  have hleave := hD.tendsto_compl_iUnion hd hH (Measure.dirac x)
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.1 hleave (ε / 2) hε2).exists
  simp only [dirac_kernel] at hm
  have := isMarkovKernel_pow P (m + 1)
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := (P ^ (m + 1) : Kernel X X) x)
    (fun _ => 1) (F := fun n z => U.indicator (fun z => (P ^ n : Kernel X X) z A) z)
    (fun n => (Kernel.measurable_coe (P ^ n : Kernel X X) hA).indicator hU)
    (fun n => Filter.Eventually.of_forall fun z => by
      have := isMarkovKernel_pow P n
      by_cases hz : z ∈ U
      · simp only [indicator_of_mem hz]; exact prob_le_one
      · simp only [indicator_of_notMem hz]; exact zero_le)
    (by simp)
    (Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp only [indicator_of_mem hz]; exact hUconv z hz
      · simp only [indicator_of_notMem hz]; exact tendsto_const_nhds)
  simp only [lintegral_zero] at hdom
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 hdom (ε / 2) hε2)
  refine eventually_atTop.2 ⟨m + 1 + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsplit : (P ^ (m + 1 + N + k) : Kernel X X) x A ≤ (P ^ (m + 1) : Kernel X X) x Uᶜ +
      ∫⁻ z, U.indicator (fun z => (P ^ (N + k) : Kernel X X) z A) z
        ∂(P ^ (m + 1) : Kernel X X) x := by
    rw [add_assoc, Kernel.pow_add_apply_eq_lintegral P (m + 1) (N + k) x hA]
    calc ∫⁻ z, (P ^ (N + k) : Kernel X X) z A ∂(P ^ (m + 1) : Kernel X X) x
        ≤ ∫⁻ z, (Uᶜ.indicator 1 z + U.indicator (fun z => (P ^ (N + k) : Kernel X X) z A) z)
            ∂(P ^ (m + 1) : Kernel X X) x := lintegral_mono fun z => by
          have := isMarkovKernel_pow P (N + k)
          by_cases hz : z ∈ U
          · simp [hz]
          · simp only [indicator_of_notMem hz, indicator_of_mem (show z ∈ Uᶜ from hz),
              Pi.one_apply, add_zero]
            exact prob_le_one
      _ = _ := by
          rw [lintegral_add_left (measurable_one.indicator hU.compl),
            lintegral_indicator_one hU.compl]
  calc (P ^ (m + 1 + N + k) : Kernel X X) x A ≤ ε / 2 + ε / 2 :=
        hsplit.trans (add_le_add hm (hN (N + k) (Nat.le_add_right N k)))
    _ = ε := ENNReal.add_halves ε

end MeynTweedie.GeneralizedDrift
