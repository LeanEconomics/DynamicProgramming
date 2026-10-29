/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.TChains
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Feller chains, petite sets and T-chains (MT §6.2.3, Theorem 6.0.1)

Meyn and Tweedie, §6.2.3, pp. 132–133, and Theorem 6.0.1, p. 124.

* **Lemma 6.2.7** (`lemma_6_2_7`, p. 132): for a `ψ`-irreducible weak Feller chain the closure of
  a petite set is petite. The book approximates from inside by a *compact* petite set; a *closed*
  one suffices (inner regularity of finite measures by closed sets on metrizable spaces), together
  with the upper semicontinuity of `K_a(·, D)` for closed `D`.
* **Proposition 6.2.8** (p. 133): for a `ψ`-irreducible weak Feller chain all compact sets are
  petite if (i) there is an open petite set of positive `ψ`-measure (`proposition_6_2_8_i`), or
  (ii) `supp ψ` has non-empty interior (`proposition_6_2_8_ii`, by the Baire category theorem).
* **Theorem 6.2.9** (`theorem_6_2_9`, p. 133): a `ψ`-irreducible weak Feller chain with `supp ψ`
  of non-empty interior is a T-chain.
* **Theorem 6.0.1** (`theorem_6_0_1`, p. 124): the summary of Proposition 6.2.2, Theorem 6.2.5
  and Theorem 6.2.9.
* The counterexample of p. 133: `jumpKernel c` jumps from `x` to `0` with probability
  `min(|x|, 1)` and moves to `cx` otherwise (`jumpKernel_apply`, `isMarkovKernel_jumpKernel`,
  `jumpKernel_isWeakFeller`, `jumpKernel_pow_zero_zero`: `0` is absorbing).
  `feller_not_tChain_counterexample`: for `c = 1/2` the chain is weak Feller and `δ₀`-irreducible
  but not a T-chain (`jumpKernel_half_pow_le`: `Pⁿ(x, {0}) ≤ n|x|`, so `K_a(x, {0}) → 0` as
  `x → 0` while `K_a(0, {0}) = 1`).

**Hypotheses.** The space is metrizable with its Borel σ-algebra throughout; Proposition 6.2.8
(ii) and Theorem 6.2.9 also use local compactness (for the Baire property), and Theorem 6.2.9 and
Theorem 6.0.1 second countability (through Theorem 6.2.5 (i)). Theorem 6.0.1 (i) is stated for
non-empty open sets (`L(x, ∅) = 0`).

**Corrections.** The counterexample is stated on `ℝ` with `P(x, {0}) = min(|x|, 1)` rather than on
`[0, 1]`; on `[0, 1]` it is the book's chain with `α = 1/2`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
  [MeasurableSpace.CountablyGenerated X] in
/-- **Lemma 6.2.7** (MT p. 132): for a `ψ`-irreducible weak Feller chain, the closure of a petite
set is petite. -/
theorem lemma_6_2_7 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hP : IsWeakFeller P) {A : Set X} (hA : IsPetite P A) :
    IsPetite P (closure A) := by
  obtain ⟨a, ν, hpet⟩ := hA
  rcases A.eq_empty_or_nonempty with hAe | ⟨x₀, hx₀⟩
  · rw [hAe, closure_empty]
    exact ⟨a, ν, MeasurableSet.empty, hpet.2.1, hpet.2.2.1, fun x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨b, ψb, hpb, hmax⟩ := proposition_5_5_5_i P hψ hpet
  have hKb := isMarkovKernel_sampledKernel P hpb.2.1
  have hfin : IsFiniteMeasure ψb := ⟨lt_of_le_of_lt ((hpb.2.2.2 x₀ hx₀ univ).trans prob_le_one)
    ENNReal.one_lt_top⟩
  have hψu : 0 < ψb univ := pos_iff_ne_zero.2 fun h => hmax.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, νC, hC, hψC, -⟩ := theorem_5_2_2 P hmax MeasurableSet.univ hψu
  obtain ⟨D, hDC, hDc, hlt⟩ := hC.1.exists_isClosed_lt_add (measure_ne_top ψb C) hψC.ne'
  have hψD : 0 < ψb D := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, zero_add] at hlt
    exact lt_irrefl _ hlt
  have hDsmall := hC.mono hDc.measurableSet hDC
  have hcl : closure A ⊆ {x | ψb D ≤ sampledKernel P b x D} := by
    refine closure_minimal (fun x hx => hpb.2.2.2 x hx D) ?_
    exact (hP.usc_sampledKernel_closed hpb.2.1 hDc).isClosed_preimage (ψb D)
  obtain ⟨δ, -, hpet'⟩ := proposition_5_5_4_i P (proposition_5_5_3 hDsmall)
    isClosed_closure.measurableSet hpb.2.1 ⟨ψb D, hψD, fun x hx => hcl hx⟩
  exact ⟨_, _, hpet'⟩

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X] in
/-- **Proposition 6.2.8 (i)** (MT p. 133): if a `ψ`-irreducible weak Feller chain has an open
petite set `A` with `ψ(A) > 0`, every compact set is petite. -/
theorem proposition_6_2_8_i {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsPhiIrreducible P ψ) (hP : IsWeakFeller P) {A : Set X} (hAo : IsOpen A)
    (hA : IsPetite P A) (hψA : 0 < ψ A) {K : Set X} (hK : IsCompact K) : IsPetite P K := by
  obtain ⟨a, ν, hpet⟩ := hA
  have hg : LowerSemicontinuous fun x => resolventHalf P x A :=
    hP.lsc_sampledKernel (geomDist 2⁻¹) hAo
  have hgpos : ∀ x, 0 < resolventHalf P x A := fun x =>
    (proposition_4_2_1 P ψ).2.2.1 hψ A hAo.measurableSet hψA x
  have hacc : SampledAccessible P (geomDist 2⁻¹) K A := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun x hx => by rw [hKe] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, -, hmin⟩ :=
        LowerSemicontinuousOn.exists_isMinOn hKne hK (hg.lowerSemicontinuousOn K)
      exact ⟨_, hgpos x₀, fun x hx => isMinOn_iff.1 hmin x hx⟩
  obtain ⟨δ, -, hpet'⟩ := proposition_5_5_4_i P hpet hK.measurableSet
    isSamplingDist_geomDist_half hacc
  exact ⟨_, _, hpet'⟩

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
  [MeasurableSpace.CountablyGenerated X] [LocallyCompactSpace X] in
/-- **Proposition 6.2.8 (ii)** (MT p. 133): if a `ψ`-irreducible weak Feller chain has `supp ψ`
with non-empty interior (on a locally compact metrizable space), every compact set is petite. -/
theorem proposition_6_2_8_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hP : IsWeakFeller P)
    (hint : (interior ψ.support).Nonempty) {K : Set X} (hK : IsCompact K) : IsPetite P K := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨A, -, m, νA, hAs, hψA, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  have hApet := proposition_5_5_3 hAs
  set F : ℕ → Set X := fun k => closure {x | ((k : ℝ≥0∞) + 1)⁻¹ ≤ resolventHalf P x A}
  have hFpet : ∀ k, IsPetite P (F k) := fun k => by
    have hmeas : MeasurableSet {x | ((k : ℝ≥0∞) + 1)⁻¹ ≤ resolventHalf P x A} :=
      measurableSet_le measurable_const (Kernel.measurable_coe _ hAs.1)
    obtain ⟨δ, -, h⟩ := proposition_5_5_4_i P hApet hmeas isSamplingDist_geomDist_half
      ⟨_, ENNReal.inv_pos.2 (by simp), fun x hx => hx⟩
    exact lemma_6_2_7 hψ hP ⟨_, _, h⟩
  have hFcover : ⋃ k, F k = univ := eq_univ_of_forall fun x => by
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt
      ((proposition_4_2_1 P ψ).2.2.1 hψ.2.1 A hAs.1 hψA x).ne'
    refine mem_iUnion.2 ⟨k, subset_closure ?_⟩
    refine le_trans ?_ hk.le
    change ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹
    gcongr
    exact le_self_add
  set U := interior ψ.support
  have : BaireSpace X := BaireSpace.of_t2Space_locallyCompactSpace
  have hG : Dense (⋃ k, interior (F k ∪ Uᶜ)) := by
    refine dense_iUnion_interior_of_closed (fun k => isClosed_closure.union
      isOpen_interior.isClosed_compl) ?_
    exact eq_univ_of_forall fun x => by
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hFcover ▸ mem_univ x)
      exact mem_iUnion.2 ⟨k, Or.inl hk⟩
  obtain ⟨x, hxU, hxG⟩ := hG.inter_open_nonempty U isOpen_interior hint
  obtain ⟨k, hk⟩ := mem_iUnion.1 hxG
  set V := U ∩ interior (F k ∪ Uᶜ)
  have hVo : IsOpen V := isOpen_interior.inter isOpen_interior
  have hVF : V ⊆ F k := fun y hy => by
    rcases interior_subset hy.2 with h | h
    · exact h
    · exact absurd hy.1 h
  have hVpos : 0 < ψ V :=
    (Measure.mem_support_iff_forall x).1 (interior_subset hxU) V (hVo.mem_nhds ⟨hxU, hk⟩)
  obtain ⟨b, ν, hpetF⟩ := hFpet k
  have hVpet : IsPetite P V :=
    ⟨b, ν, hVo.measurableSet, hpetF.2.1, hpetF.2.2.1, fun y hy => hpetF.2.2.2 y (hVF hy)⟩
  exact proposition_6_2_8_i hψ.2.1 hP hVo hVpet hVpos hK

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] in
/-- **Theorem 6.2.9** (MT p. 133): a `ψ`-irreducible weak Feller chain for which `supp ψ` has
non-empty interior is a T-chain (on a locally compact separable metrizable space). -/
theorem theorem_6_2_9 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hP : IsWeakFeller P)
    (hint : (interior ψ.support).Nonempty) : IsTChain P :=
  theorem_6_2_5_i fun _ hK => proposition_6_2_8_ii hψ hP hint hK

variable [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] in
/-- **Theorem 6.0.1** (MT p. 124), on a locally compact separable metrizable space:
(i) a T-chain with `L(x, O) > 0` for every `x` and every non-empty open `O` is `ψ`-irreducible;
(ii) if every compact set is petite then `P` is a T-chain, and every compact set is petite for a
`ψ`-irreducible T-chain; (iii) a `ψ`-irreducible weak Feller chain with `supp ψ` of non-empty
interior is a `ψ`-irreducible T-chain. -/
theorem theorem_6_0_1 [Nonempty X] (P : Kernel X X) [IsMarkovKernel P] :
    (IsTChain P → (∀ x, ∀ O : Set X, IsOpen O → O.Nonempty → 0 < hitProb P O x) →
      ∃ ψ : Measure X, ψ ≠ 0 ∧ IsPhiIrreducible P ψ) ∧
    ((∀ K : Set X, IsCompact K → IsPetite P K) → IsTChain P) ∧
    (∀ ψ : Measure X, IsPhiIrreducible P ψ → ψ ≠ 0 → IsTChain P →
      ∀ K : Set X, IsCompact K → IsPetite P K) ∧
    (∀ ψ : Measure X, IsMaximalIrreducibility P ψ → IsWeakFeller P →
      (interior ψ.support).Nonempty → IsTChain P) := by
  refine ⟨fun hT hL => proposition_6_2_2 hT fun x O hO hxO y => ?_, theorem_6_2_5_i,
    fun ψ hψ hψ0 hT K hK => theorem_6_2_5_ii hψ hψ0 hT hK,
    fun ψ hψ hP hint => theorem_6_2_9 hψ hP hint⟩
  exact (potKernel_pos_iff P hO.measurableSet y).2
    ((hitProb_pos_iff P hO.measurableSet y).1 (hL y O hO ⟨x, hxO⟩))

/-! ### The counterexample of p. 133 -/

/-! ### A family of jump chains on `ℝ` -/

/-- The jump probability `q(x) = min(|x|, 1)`. -/
noncomputable def jumpProb (x : ℝ) : ℝ := min |x| 1

/-- `0 ≤ q(x) ≤ 1`. -/
theorem jumpProb_mem (x : ℝ) : 0 ≤ jumpProb x ∧ jumpProb x ≤ 1 :=
  ⟨le_min (abs_nonneg x) zero_le_one, min_le_right _ _⟩

/-- `q` is continuous. -/
theorem continuous_jumpProb : Continuous jumpProb := continuous_abs.min continuous_const

/-- The jump chain with multiplier `c`: from `x` it jumps to `0` with probability
`q(x) = min(|x|, 1)` and moves to `c x` otherwise. For `c = 1/2` it is the chain of MT p. 133 (on
`ℝ` instead of `[0, 1]`). -/
noncomputable def jumpKernel (c : ℝ) : Kernel ℝ ℝ where
  toFun x := ENNReal.ofReal (jumpProb x) • Measure.dirac 0 +
    ENNReal.ofReal (1 - jumpProb x) • Measure.dirac (c * x)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    have hq : Measurable jumpProb := continuous_jumpProb.measurable
    exact ((ENNReal.measurable_ofReal.comp hq).mul measurable_const).add
      ((ENNReal.measurable_ofReal.comp (measurable_const.sub hq)).mul
        ((measurable_const.indicator hs).comp (measurable_const.mul measurable_id)))

/-- `P(x, ·) = q(x) δ₀ + (1 − q(x)) δ_{cx}`. -/
theorem jumpKernel_apply (c x : ℝ) : jumpKernel c x =
    ENNReal.ofReal (jumpProb x) • Measure.dirac 0 +
      ENNReal.ofReal (1 - jumpProb x) • Measure.dirac (c * x) := rfl

/-- The jump chain is a transition probability kernel. -/
theorem isMarkovKernel_jumpKernel (c : ℝ) : IsMarkovKernel (jumpKernel c) := by
  refine ⟨fun x => ⟨?_⟩⟩
  obtain ⟨h0, h1⟩ := jumpProb_mem x
  rw [jumpKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add h0 (by linarith), add_sub_cancel, ENNReal.ofReal_one]

/-- `∫ f dP(x) = q(x) f(0) + (1 − q(x)) f(cx)`. -/
theorem lintegral_jumpKernel (c x : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f y ∂jumpKernel c x =
      ENNReal.ofReal (jumpProb x) * f 0 + ENNReal.ofReal (1 - jumpProb x) * f (c * x) := by
  rw [jumpKernel_apply, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]

/-- `Pⁿ⁺¹(x, A) = q(x) Pⁿ(0, A) + (1 − q(x)) Pⁿ(cx, A)`. -/
theorem jumpKernel_pow_succ_apply (c : ℝ) (n : ℕ) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (jumpKernel c ^ (n + 1)) x A = ENNReal.ofReal (jumpProb x) * (jumpKernel c ^ n) 0 A +
      ENNReal.ofReal (1 - jumpProb x) * (jumpKernel c ^ n) (c * x) A := by
  rw [pow_succ_apply _ n x hA, lintegral_jumpKernel]

/-- `0` is absorbing: `Pⁿ(0, {0}) = 1`. -/
theorem jumpKernel_pow_zero_zero (c : ℝ) (n : ℕ) : (jumpKernel c ^ n) 0 {0} = 1 := by
  induction n with
  | zero => rw [pow_zero_apply]; simp
  | succ n ih =>
    rw [jumpKernel_pow_succ_apply c n 0 (measurableSet_singleton 0), mul_zero, ih]
    simp [jumpProb]

/-- `∫ f dP(x) = q(x) f(0) + (1 − q(x)) f(cx)` for bounded continuous real `f`. -/
theorem integral_jumpKernel (c x : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ y, f y ∂jumpKernel c x = jumpProb x * f 0 + (1 - jumpProb x) * f (c * x) := by
  obtain ⟨h0, h1⟩ := jumpProb_mem x
  have hi : ∀ z : ℝ, Integrable (fun y => f y) (Measure.dirac z) := fun z =>
    integrable_dirac enorm_lt_top
  rw [jumpKernel_apply, integral_add_measure ((hi 0).smul_measure ENNReal.ofReal_ne_top)
      ((hi _).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The jump chain is weak Feller. -/
theorem jumpKernel_isWeakFeller (c : ℝ) : IsWeakFeller (jumpKernel c) := by
  have := isMarkovKernel_jumpKernel c
  refine (proposition_6_1_1_i_weak _).2 fun f => ?_
  simp_rw [integral_jumpKernel]
  exact (continuous_jumpProb.mul continuous_const).add
    ((continuous_const.sub continuous_jumpProb).mul
      (f.continuous.comp (continuous_const.mul continuous_id)))

/-- For the halving chain (`c = 1/2`), `Pⁿ(x, {0}) ≤ n |x|` for `x ≠ 0`. -/
theorem jumpKernel_half_pow_le (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (jumpKernel 2⁻¹ ^ n) x {0} ≤ n * ENNReal.ofReal |x| := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton 0)]
    simp [hx]
  | succ n ih =>
    rw [jumpKernel_pow_succ_apply _ n x (measurableSet_singleton 0), jumpKernel_pow_zero_zero,
      mul_one]
    have hx2 : (2⁻¹ : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
    have h1 : ENNReal.ofReal (jumpProb x) ≤ ENNReal.ofReal |x| :=
      ENNReal.ofReal_le_ofReal (min_le_left _ _)
    have h2 : ENNReal.ofReal (1 - jumpProb x) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [(jumpProb_mem x).1])
    have h3 : ENNReal.ofReal |2⁻¹ * x| ≤ ENNReal.ofReal |x| := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul]
      have : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_pos (by norm_num)
      rw [this]
      linarith [abs_nonneg x]
    calc ENNReal.ofReal (jumpProb x) + ENNReal.ofReal (1 - jumpProb x) *
          (jumpKernel 2⁻¹ ^ n) (2⁻¹ * x) {0}
        ≤ ENNReal.ofReal |x| + 1 * (n * ENNReal.ofReal |x|) :=
          add_le_add h1 (mul_le_mul' h2 ((ih hx2).trans (mul_le_mul_right h3 _)))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal |x| := by push_cast; ring

/-- **The counterexample of MT p. 133** (after Theorem 6.2.9): the halving chain on `ℝ`, which from
`x` jumps to `0` with probability `min(|x|, 1)` and moves to `x/2` otherwise, is weak Feller and
`δ₀`-irreducible but not a T-chain. So the hypothesis "supp ψ has non-empty interior" of
Theorem 6.2.9 cannot be dropped (`supp δ₀ = {0}`). -/
theorem feller_not_tChain_counterexample :
    IsWeakFeller (jumpKernel 2⁻¹) ∧
      (haveI := isMarkovKernel_jumpKernel 2⁻¹;
        IsPhiIrreducible (jumpKernel 2⁻¹) (Measure.dirac 0)) ∧ ¬ IsTChain (jumpKernel 2⁻¹) := by
  have hM := isMarkovKernel_jumpKernel 2⁻¹
  set P := jumpKernel 2⁻¹
  refine ⟨jumpKernel_isWeakFeller _, ?_, ?_⟩
  · refine (isPhiIrreducible_dirac_iff P 0).2 fun x => ?_
    refine (hitProb_pos_iff P (measurableSet_singleton 0) x).2 ⟨0, ?_⟩
    rw [jumpKernel_pow_succ_apply _ 0 x (measurableSet_singleton 0), pow_zero_apply,
      pow_zero_apply, Measure.dirac_apply' _ (measurableSet_singleton 0),
      Measure.dirac_apply' _ (measurableSet_singleton 0)]
    by_cases hx : x = 0
    · subst hx
      simp [jumpProb]
    · simp only [mem_singleton_iff, indicator_of_mem, Pi.one_apply, mul_one]
      refine lt_of_lt_of_le ?_ le_self_add
      exact ENNReal.ofReal_pos.2 (lt_min (abs_pos.2 hx) one_pos)
  · rintro ⟨a, T, ha, hT, hpos⟩
    -- `T(0, {0}ᶜ) = 0`, so `T(0, {0}) > 0`
    have hK0 : sampledKernel P a 0 {0}ᶜ = 0 := by
      rw [sampledKernel_apply P a 0 (measurableSet_singleton 0).compl]
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      have := isMarkovKernel_pow P n
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), jumpKernel_pow_zero_zero, tsub_self,
        mul_zero]
    have hT0 : T 0 {0} = T 0 univ := by
      have h1 := measure_add_measure_compl (μ := T 0) (measurableSet_singleton (0 : ℝ))
      have h2 : T 0 {0}ᶜ = 0 := nonpos_iff_eq_zero.1 ((hT.2.1 0 _).trans hK0.le)
      rw [h2, add_zero] at h1
      exact h1
    have hδ : 0 < T 0 {0} := hT0 ▸ hpos 0
    have hδfin : T 0 {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (subset_univ _)).trans (hT.1 0))
    set δ := T 0 {0} / 2
    have hδpos : 0 < δ := ENNReal.half_pos hδ.ne'
    have hev : ∀ᶠ x in 𝓝 (0 : ℝ), δ < sampledKernel P a x {0} :=
      (hT.2.2 _ (measurableSet_singleton 0) 0 δ (ENNReal.half_lt_self hδ.ne' hδfin)).mono
        fun x hx => lt_of_lt_of_le hx (hT.2.1 x _)
    -- along `xⱼ = 2⁻ʲ`, `K_a(xⱼ, {0}) → 0` by dominated convergence
    set xs : ℕ → ℝ := fun j => (2⁻¹ : ℝ) ^ j
    have hxs : Tendsto xs atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hxs0 : ∀ j, xs j ≠ 0 := fun j => pow_ne_zero _ (by norm_num)
    have hlim : Tendsto (fun j => sampledKernel P a (xs j) {0}) atTop (𝓝 0) := by
      have heq : ∀ j, sampledKernel P a (xs j) {0} =
          ∫⁻ n, a n * (P ^ n) (xs j) {0} ∂Measure.count := fun j => by
        rw [lintegral_count, sampledKernel_apply P a _ (measurableSet_singleton 0)]
      simp_rw [heq]
      have h0 : (0 : ℝ≥0∞) = ∫⁻ _ : ℕ, 0 ∂Measure.count := by simp
      rw [h0]
      refine tendsto_lintegral_of_dominated_convergence a (fun j => measurable_of_countable _)
        (fun j => Eventually.of_forall fun n => ?_) (by
          rw [lintegral_count, show ∑' n, a n = 1 from ha]; exact ENNReal.one_ne_top)
        (Eventually.of_forall fun n => ?_)
      · have := isMarkovKernel_pow P n
        exact mul_le_of_le_one_right' prob_le_one
      · have hb : Tendsto (fun j => a n * ((n : ℝ≥0∞) * ENNReal.ofReal |xs j|)) atTop
            (𝓝 0) := by
          have h1 : Tendsto (fun j => ENNReal.ofReal |xs j|) atTop (𝓝 0) := by
            rw [← ENNReal.ofReal_zero]
            exact ENNReal.tendsto_ofReal (by simpa using hxs.abs)
          have h2 := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h1
            (Or.inr (ENNReal.natCast_ne_top n)))
            (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top (ha ▸ ENNReal.le_tsum n)))
          simpa using h2
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
          (fun j => zero_le) fun j => mul_le_mul_right (jumpKernel_half_pow_le n (hxs0 j)) _
    obtain ⟨j, hj1, hj2⟩ :=
      ((hxs.eventually hev).and (hlim.eventually (gt_mem_nhds hδpos))).exists
    exact absurd (hj1.trans hj2) (lt_irrefl _)

end MeynTweedie.Positivity
