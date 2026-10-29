/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.HarrisProperties
import HarrisRecurrence.CountableClassification
import HarrisRecurrence.SplitDichotomy

/-!
# Harris recurrent chains (MT §9.0, §9.1.2–9.1.3)

Meyn and Tweedie, Theorem 9.0.1 (p. 200) and §9.1.2–9.1.3, pp. 203–206. `ψ` is a maximal
irreducibility measure.

**Tools.**
* `ae_stays_of_absorbing`: once in an absorbing set `H`, the chain stays in `H`, `P_x`-a.s.
* `isUniformlyTransient_of_escape`: if `H` is absorbing, `D ∩ H = ∅` and `Pᴹ(x, H) ≥ ε > 0` on
  `D`, then `D` is uniformly transient (`P_x(η_D > M) ≤ 1 − ε` and (8.35)).
* `IsPetiteSet.exists_pow_absorbing_ge`: a petite set whose measure `ν` charges an absorbing
  set `H` enters `H` by a fixed time with probability bounded below.
* `prob_eq_one_of_lintegral_eq_one`: `∫ f dν = 1` with `f ≤ 1` and `ν` a probability forces
  `f = 1` `ν`-a.s.
* `harrisInfty`, `harrisInfty_absorbing` (p. 204): for a Harris recurrent set `D`,
  `D^∞ = {y : L(y, D) = 1}` contains `D` and is absorbing.

**Results.**
* `IsMaximalHarrisSet P ψ H` (p. 204): `H` is non-empty, absorbing, maximal (`H = H^∞`) and the
  chain restricted to `H` is Harris: `Q(x, A) = 1` for `x ∈ H` and `A ∈ B⁺(X)`.
* **Theorem 9.1.5** (`theorem_9_1_5`, p. 204): a recurrent chain has a decomposition
  `X = H ∪ N` with `H` a maximal Harris set and `N = Hᶜ` transient and `ψ`-null.
* **Theorem 9.0.1** (`theorem_9_0_1`, p. 200): the same, with every subset of `H` in `B⁺(X)`
  Harris recurrent.
* `isHarris_of_countable` (p. 200): on a countable space, a recurrent irreducible chain is
  Harris (the null set `N` is empty).
* **Theorem 9.1.6** (`theorem_9_1_6`, p. 205): an aperiodic chain is Harris iff every skeleton
  is; `isHarris_of_skeleton` (if one skeleton is Harris, so is `Φ`) needs no aperiodicity.
* **Proposition 9.1.7** (p. 205): (i) `proposition_9_1_7_i`, a non-empty recurrent petite set
  makes the chain recurrent, and `C ∩ N` is uniformly transient for every maximal Harris set
  `H = Nᶜ`; (ii) `proposition_9_1_7_ii`, a petite `C` with `L(x, C) ≡ 1` makes the chain Harris.
* **Theorem 9.1.8** (`theorem_9_1_8`, p. 206): (V1) with a petite `C` and `V` unbounded off
  petite sets makes the chain Harris.

**Hypotheses.** Theorems 9.0.1, 9.1.5, 9.1.6, 9.1.8 and `isHarris_of_countable` use Proposition
5.5.5, hence a countably generated σ-algebra, as the book assumes throughout.

**Corrections.**
* Proposition 9.1.7 (i) needs `C ≠ ∅`: the empty set is petite and (vacuously) recurrent, so as
  stated every chain would be recurrent (compare `theorem_8_3_6_i_counterexample`).
* In Theorem 9.1.6 the direction "a skeleton is Harris ⇒ `Φ` is Harris" holds without
  aperiodicity.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Absorbing sets and uniform transience -/

/-- Once in an absorbing set, always in it: `P_x`-a.s., `Φₙ ∈ H` and `n ≤ k` imply `Φₖ ∈ H`. -/
theorem ae_stays_of_absorbing (P : Kernel X X) [IsMarkovKernel P] {H : Set X}
    (hH : MeasurableSet H) (habs : IsAbsorbing P H) (x : X) :
    ∀ᵐ ω ∂pathKernel P x, ∀ n k, n ≤ k → ω n ∈ H → ω k ∈ H := by
  have := isMarkovKernel_pathKernel P
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
  by_cases hnk : n ≤ k
  · have hS : MeasurableSet {ω : ℕ → X | ω (k - n) ∈ Hᶜ} := measurable_pi_apply _ hH.compl
    have h0 : pathKernel P x ({ω | ω n ∈ H} ∩ shift n ⁻¹' {ω | ω (k - n) ∈ Hᶜ}) = 0 := by
      have := isMarkovKernel_pow P (k - n)
      have hz : ∀ y ∈ H, pathKernel P y {ω | ω (k - n) ∈ Hᶜ} = 0 := fun y hy => by
        rw [pathKernel_coord_mem P y _ hH.compl, prob_compl_eq_zero_iff hH]
        exact habs.pow_apply hH _ hy
      rw [pathKernel_coord_inter_shift P x n hH hS, setLIntegral_congr_fun hH hz,
        lintegral_zero]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_ofPred_eq, not_forall, exists_prop] at hω
    obtain ⟨-, hn, hk⟩ := hω
    refine ⟨hn, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, shift_apply, mem_compl_iff]
    rwa [show n + (k - n) = k by omega]
  · exact Eventually.of_forall fun ω h => absurd h hnk

/-- **Uniform transience by escape to an absorbing set** ((8.35)): if `H` is absorbing,
`D ⊆ Hᶜ` and `Pᴹ(x, H) ≥ ε > 0` for `x ∈ D`, then `D` is uniformly transient. -/
theorem isUniformlyTransient_of_escape (P : Kernel X X) [IsMarkovKernel P] {H D : Set X}
    (hH : MeasurableSet H) (habs : IsAbsorbing P H) (hD : MeasurableSet D) (hDH : D ⊆ Hᶜ)
    {M : ℕ} {ε : ℝ≥0∞} (hε : 0 < ε) (hesc : ∀ x ∈ D, ε ≤ (P ^ M) x H) :
    IsUniformlyTransient P D := by
  have := isMarkovKernel_pathKernel P
  -- `P_x(η_D ≥ M + 1) ≤ 1 − ε` on `D`
  have hocc : ∀ x ∈ D, pathKernel P x {ω | ((M + 1 : ℕ) : ℝ≥0∞) ≤ occTime D ω} ≤ 1 - ε := by
    intro x hx
    have hstay := ae_stays_of_absorbing P hH habs x
    have hsub : {ω : ℕ → X | ((M + 1 : ℕ) : ℝ≥0∞) ≤ occTime D ω} ≤ᵐ[pathKernel P x]
        {ω | ω M ∈ Hᶜ} := by
      filter_upwards [hstay] with ω hω hocc
      simp only [mem_compl_iff] at hocc ⊢
      intro hM
      have heq : occTime D ω = occTimeN D M ω := by
        unfold occTime occTimeN
        refine tsum_eq_sum fun b hb => ?_
        rw [Finset.mem_range, not_lt] at hb
        exact indicator_of_notMem (fun h => hDH h (hω M (b + 1) (by omega) hM)) _
      have := (occTimeN_le D M ω).trans_lt (show ((M : ℕ) : ℝ≥0∞) < ((M + 1 : ℕ) : ℝ≥0∞) by
        exact_mod_cast Nat.lt_succ_self M)
      rw [← heq] at this
      exact absurd hocc (not_le.2 this)
    have := isMarkovKernel_pow P M
    calc pathKernel P x {ω | ((M + 1 : ℕ) : ℝ≥0∞) ≤ occTime D ω}
        ≤ pathKernel P x {ω | ω M ∈ Hᶜ} := measure_mono_ae hsub
      _ = 1 - (P ^ M) x H := by
          rw [pathKernel_coord_mem P x M hH.compl, prob_compl_eq_one_sub hH]
      _ ≤ 1 - ε := tsub_le_tsub_left (hesc x hx) 1
  have hlt : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  have hret : ∀ x ∈ D, pathKernel P x {ω | returnTimeK D (M + 1) ω ≠ ⊤} ≤ 1 - ε := fun x hx =>
    (measure_mono fun ω hω => le_occTime_of_returnTimeK D (M + 1) hω).trans (hocc x hx)
  obtain ⟨h1, -⟩ := proposition_8_3_1_iv P hD (M + 1) hlt hret
  refine ⟨hD, ((M + 1 : ℕ) : ℝ≥0∞) / (1 - (1 - ε)), ?_, h1⟩
  refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
  exact (tsub_pos_of_lt hlt).ne'

/-- A petite set whose minorizing measure charges an absorbing set `H` enters `H` by a fixed time
`M` with probability at least some `ε > 0`, from every point. -/
theorem IsPetiteSet.exists_pow_absorbing_ge {P : Kernel X X} [IsMarkovKernel P]
    {b : ℕ → ℝ≥0∞} {ν : Measure X} {C : Set X} (hC : IsPetiteSet P b ν C) {H : Set X}
    (hH : MeasurableSet H) (habs : IsAbsorbing P H) (hνH : 0 < ν H) :
    ∃ M : ℕ, ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ x ∈ C, ε ≤ (P ^ M) x H := by
  obtain ⟨-, hb, -, hle⟩ := hC
  obtain ⟨hε0, hεt, h2⟩ := half_min_spec hνH
  set ε := 2⁻¹ * min (ν H) 1
  obtain ⟨K, hK⟩ := exists_tail_le hb hε0
  refine ⟨K, ε, hε0, fun x hx => ?_⟩
  have h := le_sum_head P K x hH hεt hK h2 ((hle x hx) H)
  calc ε ≤ ∑ k ∈ Finset.range K, b k * (P ^ k) x H := h
    _ ≤ ∑ k ∈ Finset.range K, b k * (P ^ K) x H := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul' le_rfl ?_
        exact IsAbsorbing.pow_mono habs hH x (Finset.mem_range.1 hk).le
    _ = (∑ k ∈ Finset.range K, b k) * (P ^ K) x H := by rw [Finset.sum_mul]
    _ ≤ 1 * (P ^ K) x H := by
        gcongr
        exact (ENNReal.sum_le_tsum _).trans (le_of_eq hb)
    _ = (P ^ K) x H := one_mul _

/-- If `∫ f dν = 1` for a probability `ν` and `f ≤ 1`, then `ν{f = 1} = 1`. -/
theorem prob_eq_one_of_lintegral_eq_one {ν : Measure X} [IsProbabilityMeasure ν] {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) (h : ∫⁻ x, f x ∂ν = 1) : ν {x | f x = 1} = 1 := by
  have hsub : ∫⁻ x, (1 - f x) ∂ν = 0 := by
    rw [lintegral_sub' hf.aemeasurable (by rw [h]; exact ENNReal.one_ne_top)
      (Eventually.of_forall hf1), lintegral_const, measure_univ, h]
    simp
  have hm' : Measurable fun x => 1 - f x := measurable_const.sub hf
  rw [lintegral_eq_zero_iff hm'] at hsub
  have hm : MeasurableSet {x | f x = 1} := hf (measurableSet_singleton 1)
  refine (prob_compl_eq_zero_iff hm).1 (measure_mono_null (fun x hx => ?_) (ae_iff.1 hsub))
  simp only [mem_compl_iff, mem_ofPred_eq, Pi.zero_apply] at hx ⊢
  intro h0
  exact hx (le_antisymm (hf1 x) (by simpa [tsub_eq_zero_iff_le] using h0))

/-- `L(x, A) ≥ P(x, A)`. -/
theorem le_hitProb_of_kernel (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) : P x A ≤ hitProb P A x := by
  rw [hitProb_first_step P hA x]; exact le_self_add

/-! ### `D^∞` and maximal Harris sets -/

/-- `D^∞ = {y : L(y, D) = 1}` (MT p. 204). -/
def harrisInfty (P : Kernel X X) [IsMarkovKernel P] (D : Set X) : Set X := {y | hitProb P D y = 1}

/-- For a Harris recurrent set `D`, `D ⊆ D^∞` and `D^∞` is absorbing (MT p. 204). -/
theorem harrisInfty_absorbing (P : Kernel X X) [IsMarkovKernel P] {D : Set X}
    (hD : MeasurableSet D) (hHar : IsHarrisRecurrentSet P D) :
    D ⊆ harrisInfty P D ∧ IsAbsorbing P (harrisInfty P D) := by
  have hsub : D ⊆ harrisInfty P D := fun y hy =>
    le_antisymm (hitProb_le_one P D y) ((hHar y hy).symm.le.trans (harrisQ_le_hitProb P D y))
  refine ⟨hsub, fun y hy => ?_⟩
  have hL := measurable_hitProb P hD
  have hint : ∫⁻ z, hitProb P D z ∂P y = 1 := by
    refine le_antisymm ?_ ?_
    · calc ∫⁻ z, hitProb P D z ∂P y ≤ ∫⁻ _, 1 ∂P y :=
            lintegral_mono fun z => hitProb_le_one P D z
        _ = 1 := by simp
    · refine le_of_eq ?_
      calc (1 : ℝ≥0∞) = hitProb P D y := hy.symm
        _ = P y D + ∫⁻ z in Dᶜ, hitProb P D z ∂P y := hitProb_first_step P hD y
        _ = ∫⁻ z in D, hitProb P D z ∂P y + ∫⁻ z in Dᶜ, hitProb P D z ∂P y := by
            congr 1
            rw [setLIntegral_congr_fun hD fun z hz => hsub hz, setLIntegral_const, one_mul]
        _ = ∫⁻ z, hitProb P D z ∂P y := lintegral_add_compl _ hD
  exact prob_eq_one_of_lintegral_eq_one hL (hitProb_le_one P D) hint

/-- A **maximal Harris set** (MT p. 204): `H` is non-empty, absorbing and maximal absorbing
(`H = H^∞`), and the chain restricted to `H` is Harris recurrent: `Q(x, A) = 1` for every
`x ∈ H` and every `A ∈ B⁺(X)`. -/
def IsMaximalHarrisSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (H : Set X) : Prop :=
  MeasurableSet H ∧ H.Nonempty ∧ IsAbsorbing P H ∧ harrisInfty P H = H ∧
    ∀ A, MeasurableSet A → 0 < ψ A → ∀ x ∈ H, harrisQ P A x = 1

/-! ### Theorem 9.1.5 -/

/-- If every point of `A` reaches `A` (`L ≡ 1` on `A`) and `A` is not Harris at some point, the
set `{x ∈ C : L(x, C) < 1}` is charged by `ψ`: the first step of the proof of Theorem 9.1.5. -/
theorem psi_pos_hitProb_lt_one {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : MeasurableSet C) (hψC : 0 < ψ C)
    (hQ : ∀ x, harrisQ P C x < 1) : 0 < ψ {x | x ∈ C ∧ hitProb P C x < 1} := by
  set C₁ := {x | x ∈ C ∧ hitProb P C x < 1}
  have hC₁ : MeasurableSet C₁ := hC.inter (measurable_hitProb P hC measurableSet_Iio)
  by_contra h0
  have h0' : ψ C₁ = 0 := le_antisymm (not_lt.1 h0) zero_le
  have hfull : IsFull ψ C₁ᶜ := by rw [IsFull, compl_compl]; exact h0'
  obtain ⟨F, hFsub, -, hFm, hFabs, hFfull⟩ := proposition_4_2_3_ii hψ hC₁.compl hfull
  have hCF : 0 < ψ (C ∩ F) := by
    have : ψ C ≤ ψ (C ∩ F) + ψ Fᶜ := by
      calc ψ C = ψ ((C ∩ F) ∪ (C ∩ Fᶜ)) := by rw [inter_union_compl]
        _ ≤ ψ (C ∩ F) + ψ (C ∩ Fᶜ) := measure_union_le _ _
        _ ≤ ψ (C ∩ F) + ψ Fᶜ := by gcongr; exact inter_subset_right
    rw [hFfull, add_zero] at this
    exact hψC.trans_le this
  obtain ⟨x, hxC, hxF⟩ := nonempty_of_measure_ne_zero hCF.ne'
  have hL1 : ∀ y ∈ C ∩ F, hitProb P (C ∩ F) y = 1 := by
    rintro y ⟨hyC, hyF⟩
    have hy1 : hitProb P C y = 1 := by
      by_contra hne
      exact hFsub hyF ⟨hyC, lt_of_le_of_ne (hitProb_le_one P C y) hne⟩
    exact le_antisymm (hitProb_le_one P _ y) (hy1 ▸ hitProb_inter_absorbing P hFm hFabs hyF)
  have hQ1 := (proposition_9_1_1 P (hC.inter hFm) hL1).2 x ⟨hxC, hxF⟩
  have := harrisQ_mono P (inter_subset_left : C ∩ F ⊆ C) x
  rw [hQ1] at this
  exact absurd (hQ x) (not_lt.2 this)

variable [MeasurableSpace.CountablyGenerated X] in
/-- A petite set of positive `ψ`-measure exists. -/
theorem exists_petite_pos {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) : ∃ C, IsPetite P C ∧ 0 < ψ C := by
  obtain ⟨c, ψc, -, Cs, -, hpet, hcov⟩ := proposition_5_5_5_iii_cover P hψ
  have hψu : 0 < ψ (⋃ n, Cs n) := by
    rw [hcov]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨N, hN⟩ := exists_measure_pos_of_iUnion hψu
  exact ⟨Cs N, ⟨_, _, hpet N⟩, hN⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 9.1.5** (MT p. 204): if the chain is recurrent, then `X = H ∪ N` where `H` is a
non-empty maximal Harris set and `N = Hᶜ` is transient (and `ψ`-null). -/
theorem theorem_9_1_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) :
    ∃ H : Set X, IsMaximalHarrisSet P ψ H ∧ IsTransientSet P Hᶜ ∧ ψ Hᶜ = 0 := by
  have hψ := hrec.1
  obtain ⟨C, hCpet, hψC⟩ := exists_petite_pos hψ
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hCpet; exact h.1
  set H := {y | harrisQ P C y = 1} with hHdef
  have hHm : MeasurableSet H := measurable_harrisQ P hCm (measurableSet_singleton 1)
  -- `H` is absorbing
  have habs : IsAbsorbing P H := by
    intro y hy
    have h1 := harrisQ_eq_lintegral_pow P hCm y 1
    rw [pow_one, hy] at h1
    exact prob_eq_one_of_lintegral_eq_one (measurable_harrisQ P hCm) (harrisQ_le_one P C) h1.symm
  -- `H` is maximal absorbing
  have hmax : harrisInfty P H = H := by
    ext y
    constructor
    · intro hy
      refine le_antisymm (harrisQ_le_one P C y) ?_
      have hge := harrisQ_ge_stopping P hCm y (proposition_3_4_4 hHm).1
      have hT := measurableSet_firstReturn_ne_top (X := X) hHm
      calc (1 : ℝ≥0∞) = hitProb P H y := hy.symm
        _ = ∫⁻ _ in {ω | firstReturn H ω ≠ ⊤}, 1 ∂pathKernel P y := by
            rw [setLIntegral_const, one_mul]; rfl
        _ = ∫⁻ ω in {ω | firstReturn H ω ≠ ⊤}, harrisQ P C (stoppedState (firstReturn H) ω)
              ∂pathKernel P y :=
            setLIntegral_congr_fun hT fun ω hω => (stoppedState_firstReturn_mem H hω).symm
        _ ≤ harrisQ P C y := hge
    · intro hy
      exact le_antisymm (hitProb_le_one P H y) ((habs y hy).symm.le.trans
        (le_hitProb_of_kernel P hHm y))
  -- `H` is non-empty
  have hne : H.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hQ : ∀ x, harrisQ P C x < 1 := fun x =>
      lt_of_le_of_ne (harrisQ_le_one P C x) fun h => by
        have : x ∈ H := h
        rw [hemp] at this; exact this
    have hpos := psi_pos_hitProb_lt_one hψ hCm hψC hQ
    have hcov : {x | x ∈ C ∧ hitProb P C x < 1} =
        ⋃ j : ℕ, {x | x ∈ C ∧ hitProb P C x ≤ 1 - (j : ℝ≥0∞)⁻¹} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hx, hlt⟩
        obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hlt).ne'
        refine ⟨j, hx, ?_⟩
        exact ENNReal.le_sub_of_add_le_left (ne_top_of_lt hj)
          (by rw [add_comm]; exact (lt_tsub_iff_left.1 hj).le)
      · rintro ⟨j, hx, hle⟩
        refine ⟨hx, hle.trans_lt ?_⟩
        refine ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_
        simp
    rw [hcov] at hpos
    obtain ⟨j, hj⟩ := exists_measure_pos_of_iUnion hpos
    set B := {x | x ∈ C ∧ hitProb P C x ≤ 1 - (j : ℝ≥0∞)⁻¹}
    have hBm : MeasurableSet B := hCm.inter (measurable_hitProb P hCm measurableSet_Iic)
    have hε : 1 - (j : ℝ≥0∞)⁻¹ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (by simp)
    have hbound := proposition_8_3_1_iii P hBm hε fun x hx =>
      (hitProb_mono P (fun _ h => h.1 : B ⊆ C) x).trans hx.2
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hj.ne'
    have htop := hrec.2 B hBm hj x
    have hfin : (1 - (1 - (j : ℝ≥0∞)⁻¹))⁻¹ ≠ ∞ :=
      ENNReal.inv_ne_top.2 (tsub_pos_of_lt hε).ne'
    exact hfin (top_unique (htop ▸ hbound x))
  -- `H` is full, so `N = Hᶜ` is null and transient
  have hfull := proposition_4_2_3_i hψ.2.1 hHm hne habs
  refine ⟨H, ⟨hHm, hne, habs, hmax, fun A hA hψA x hx => ?_⟩, proposition_8_3_7 P hψ hHm.compl
    hfull, hfull⟩
  have hacc := IsPetite.unifAccessible hψ.2.1 hCpet hA hψA
  exact le_antisymm (harrisQ_le_one P A x)
    ((show harrisQ P C x = 1 from hx) ▸ theorem_9_1_3_i_unifAccessible P hA hacc x)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 9.0.1** (MT p. 200): if the chain is recurrent, then `X = H ∪ N` where `H` is
absorbing and non-empty, every subset of `H` in `B⁺(X)` is Harris recurrent, and `N` is `ψ`-null
and transient. -/
theorem theorem_9_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) :
    ∃ H N : Set X, univ = H ∪ N ∧ MeasurableSet H ∧ H.Nonempty ∧ IsAbsorbing P H ∧
      (∀ A ⊆ H, MeasurableSet A → 0 < ψ A → IsHarrisRecurrentSet P A) ∧
      ψ N = 0 ∧ IsTransientSet P N := by
  obtain ⟨H, ⟨hHm, hne, habs, -, hQ⟩, htr, hnull⟩ := theorem_9_1_5 hrec
  exact ⟨H, Hᶜ, (union_compl_self H).symm, hHm, hne, habs,
    fun A hAH hA hψA x hx => hQ A hA hψA x (hAH hx), hnull, htr⟩

/-- On a countable space a recurrent irreducible chain is Harris recurrent (MT p. 200): the
null set `N` of (9.3) is empty. -/
theorem isHarris_of_countable [Countable X] [MeasurableSingletonClass X] [Nonempty X]
    {P : Kernel X X} [IsMarkovKernel P] (hirr : IsIrreducibleChain P)
    (hrec : IsRecurrentChain P Measure.count) : IsHarris P Measure.count := by
  have hstates := (isRecurrentChain_count_iff P hirr).1 hrec
  refine ⟨hrec.1, fun A hA hψA => ?_⟩
  have hne : A.Nonempty := nonempty_of_measure_ne_zero hψA.ne'
  exact (proposition_9_1_1 P hA fun x _ => hitProb_eq_one_of_recurrent P hirr hstates hne x).2

/-! ### Proposition 9.1.7 and Theorem 9.1.8 -/

/-- **Proposition 9.1.7 (ii)** (MT p. 205): if some petite set `C` has `L(x, C) = 1` for every
`x ∈ X`, the chain is Harris recurrent. -/
theorem proposition_9_1_7_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C)
    (hL : ∀ x, hitProb P C x = 1) : IsHarris P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hQC : ∀ x, harrisQ P C x = 1 := theorem_9_1_3_ii P hCm one_pos fun y =>
    (hL y).symm.le.trans (hitProb_le_hitProbZero P C y)
  refine ⟨hψ, fun A hA hψA x _ => ?_⟩
  have hacc := IsPetite.unifAccessible hψ.2.1 hC hA hψA
  exact le_antisymm (harrisQ_le_one P A x) ((hQC x) ▸ theorem_9_1_3_i_unifAccessible P hA hacc x)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Proposition 9.1.7 (i)** (MT p. 205): if some non-empty petite set `C` is recurrent, the
chain is recurrent, and `C ∩ N` is uniformly transient, where `N = Hᶜ` for any maximal Harris
set `H` (the transient set of (9.11)). The book omits `C ≠ ∅`. -/
theorem proposition_9_1_7_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) (hne : C.Nonempty)
    (hrec : IsRecurrentSet P C) :
    IsRecurrentChain P ψ ∧
      ∀ H, IsMaximalHarrisSet P ψ H → IsUniformlyTransient P (C ∩ Hᶜ) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  refine ⟨?_, fun H hHar => ?_⟩
  · rcases theorem_8_3_4 P hψ with h | h
    · exact h
    · exfalso
      obtain ⟨-, M, hM, hb⟩ := theorem_8_3_5 P h.2 hC
      obtain ⟨x, hx⟩ := hne
      exact hM (top_unique (hrec x hx ▸ hb x hx))
  · obtain ⟨hHm, hHne, habs, -, -⟩ := hHar
    have hnull : ψ Hᶜ = 0 := proposition_4_2_3_i hψ.2.1 hHm hHne habs
    obtain ⟨a, ν, hpet⟩ := hC
    obtain ⟨b, ψb, hpetb, hψb⟩ := proposition_5_5_5_i P hψ hpet
    have hequiv := hψ.equiv hψb
    have hνH : 0 < ψb H := by
      have hn : ψb Hᶜ = 0 := hequiv.2 hnull
      have hu : 0 < ψb univ := pos_iff_ne_zero.2 fun h => hψb.1 (Measure.measure_univ_eq_zero.1 h)
      calc 0 < ψb univ := hu
        _ = ψb (H ∪ Hᶜ) := by rw [union_compl_self]
        _ ≤ ψb H + ψb Hᶜ := measure_union_le _ _
        _ = ψb H := by rw [hn, add_zero]
    obtain ⟨M, ε, hε, hge⟩ := hpetb.exists_pow_absorbing_ge hHm habs hνH
    exact isUniformlyTransient_of_escape P hHm habs (hCm.inter hHm.compl) inter_subset_right hε
      fun x hx => hge x hx.1

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 9.1.8** (MT p. 206): if `C` is petite, `V : X → ℝ₊` is unbounded off petite sets
(every `{V ≤ n}` is petite) and (V1) holds, `ΔV ≤ 0` off `C`, then the chain is Harris
recurrent. -/
theorem theorem_9_1_8 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {C : Set X} (hC : IsPetite P C) {V : X → NNReal}
    (hVm : Measurable V) (hpet : ∀ n : ℕ, IsPetite P {x | V x ≤ n})
    (hdrift : ∀ x ∉ C, drift P (fun y => (V y : ℝ≥0∞)) x ≤ 0) : IsHarris P ψ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hcov : (⋃ n : ℕ, {x | V x ≤ n}) = univ := by
    ext x; simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (V x)
    exact ⟨n, hn⟩
  have hψu : 0 < ψ (⋃ n : ℕ, {x | V x ≤ n}) := by
    rw [hcov]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hψu
  set C' := C ∪ {x | V x ≤ n}
  have hC'm : MeasurableSet C' := hCm.union (hVm measurableSet_Iic)
  have hC'pet : IsPetite P C' := proposition_5_5_5_ii P hψ hC (hpet n)
  have hψC' : 0 < ψ C' := hn.trans_le (measure_mono subset_union_right)
  have hL := lemma_8_4_3_hitProb P hψ.2.1 hC'm hψC' hVm hpet
    (fun x hx => hdrift x fun h => hx (subset_union_left h))
  exact proposition_9_1_7_ii hψ hC'pet hL

/-! ### Theorem 9.1.6: skeletons -/

/-- The law of the `m`-skeleton `(Φ_{mn})ₙ` under `P_x` is the path measure of `Pᵐ`. -/
theorem pathKernel_map_skeleton (P : Kernel X X) [IsMarkovKernel P] (m : ℕ) (x : X) :
    haveI := isMarkovKernel_pow P m
    (pathKernel P x).map (fun ω n => ω (m * n)) = pathKernel (P ^ m) x := by
  have := isMarkovKernel_pow P m
  have h := law_eq_pathMeasure (skeleton P m) (Measure.dirac x)
    (skeleton_isMarkovChain P (Measure.dirac x) m)
  rw [pathMeasure_dirac, pathMeasure_dirac] at h
  exact h

/-- `Qₘ(x, A) ≤ Q(x, A)`: if the skeleton is in `A` infinitely often, so is the chain. -/
theorem harrisQ_skeleton_le (P : Kernel X X) [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m)
    {A : Set X} (hA : MeasurableSet A) (x : X) :
    haveI := isMarkovKernel_pow P m
    harrisQ (P ^ m) A x ≤ harrisQ P A x := by
  have := isMarkovKernel_pow P m
  have hmeas : Measurable fun (ω : ℕ → X) (n : ℕ) => ω (m * n) :=
    measurable_pi_iff.2 fun n => measurable_pi_apply _
  rw [harrisQ, harrisQ, ← pathKernel_map_skeleton P m x, Measure.map_apply hmeas
    (measurableSet_ioSet hA)]
  refine measure_mono fun ω hω N => ?_
  obtain ⟨k, hk, hkA⟩ := hω N
  exact ⟨m * k, le_trans hk (Nat.le_mul_of_pos_left k hm), hkA⟩

/-- If one skeleton `Pᵐ`, `m ≥ 1`, is Harris (with the same maximal irreducibility measure), so is
the chain (MT p. 205). No aperiodicity is needed. -/
theorem isHarris_of_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {m : ℕ} (hm : 1 ≤ m)
    (h : haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ) : IsHarris P ψ := by
  have := isMarkovKernel_pow P m
  refine ⟨hψ, fun A hA hψA x hx => le_antisymm (harrisQ_le_one P A x) ?_⟩
  rw [← h.2 A hA hψA x hx]
  exact harrisQ_skeleton_le P hm hA x

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 9.1.6** (MT p. 205): an aperiodic `ψ`-irreducible chain is Harris iff each skeleton
`Pᵐ`, `m ≥ 1`, is Harris. -/
theorem theorem_9_1_6 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    IsHarris P ψ ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m; IsHarris (P ^ m) ψ := by
  constructor
  · intro hH m hm
    have := isMarkovKernel_pow P m
    have hsk := ((proposition_5_4_5_iii P hψ hap).1 m hm).1
    have hrecm : IsRecurrentChain (P ^ m) ψ :=
      (theorem_8_2_6_ii P hψ hap).2.1 hH.isRecurrentChain m hm
    obtain ⟨Hm, ⟨hHmm, -, -, -, hQm⟩, -, hnullm⟩ := theorem_9_1_5 hrecm
    obtain ⟨H, hHsub, -, hHm, habs, hfull⟩ := proposition_4_2_3_ii hψ hHmm hnullm
    have hψH : 0 < ψ H := by
      have hu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
      calc 0 < ψ univ := hu
        _ = ψ (H ∪ Hᶜ) := by rw [union_compl_self]
        _ ≤ ψ H + ψ Hᶜ := measure_union_le _ _
        _ = ψ H := by rw [show ψ Hᶜ = 0 from hfull, add_zero]
    -- the skeleton enters `Hm` almost surely
    have hLm : ∀ x, hitProb (P ^ m) Hm x = 1 := by
      intro x
      have hQ1 := theorem_9_1_4 hH hHm hψH x
      have hstay := ae_stays_of_absorbing P hHm habs x
      have hmeas : Measurable fun (ω : ℕ → X) (n : ℕ) => ω (m * n) :=
        measurable_pi_iff.2 fun n => measurable_pi_apply _
      have hT := measurableSet_firstReturn_ne_top (X := X) hHmm
      refine le_antisymm (hitProb_le_one _ _ _) ?_
      rw [hitProb, ← pathKernel_map_skeleton P m x, Measure.map_apply hmeas hT, ← hQ1]
      refine measure_mono_ae ?_
      filter_upwards [hstay] with ω hω hio
      obtain ⟨k, hk, hkH⟩ := hio 1
      simp only [mem_preimage, mem_ofPred_eq, firstReturn_ne_top_iff]
      refine ⟨k, by omega, hHsub (hω k (m * k) (Nat.le_mul_of_pos_left k hm) hkH)⟩
    refine ⟨hsk, fun A hA hψA x _ => le_antisymm (harrisQ_le_one _ _ _) ?_⟩
    have hge := harrisQ_ge_stopping (P ^ m) hA x (proposition_3_4_4 hHmm).1
    have hT := measurableSet_firstReturn_ne_top (X := X) hHmm
    calc (1 : ℝ≥0∞) = hitProb (P ^ m) Hm x := (hLm x).symm
      _ = ∫⁻ _ in {ω | firstReturn Hm ω ≠ ⊤}, 1 ∂pathKernel (P ^ m) x := by
          rw [setLIntegral_const, one_mul]; rfl
      _ = ∫⁻ ω in {ω | firstReturn Hm ω ≠ ⊤}, harrisQ (P ^ m) A
            (stoppedState (firstReturn Hm) ω) ∂pathKernel (P ^ m) x :=
          setLIntegral_congr_fun hT fun ω hω =>
            (hQm A hA hψA _ (stoppedState_firstReturn_mem Hm hω)).symm
      _ ≤ harrisQ (P ^ m) A x := hge
  · intro h
    exact isHarris_of_skeleton hψ le_rfl (h 1 le_rfl)

end MeynTweedie.HarrisRecurrence
