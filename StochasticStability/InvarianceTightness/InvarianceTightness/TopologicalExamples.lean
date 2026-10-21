/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.TopologicalRecurrence
import InvarianceTightness.DriftHarris
import Mathlib.Topology.Instances.ENat

/-!
# A counterexample to Theorem 9.3.6 (MT §9.3)

Meyn and Tweedie, §9.3.2, pp. 210–213.

The chain lives on `ℕ∞ ⊕ ℕ` (order topology on `ℕ∞`, discrete on `ℕ`):
* the **Harris part** `aₙ = inl n`: from every `aₙ` the chain jumps with law
  `ν = Σₙ 2^{−(n+1)} δ_{aₙ}`;
* the point `x* = inl ⊤`, the limit of the `aₙ`: from `x*` the chain jumps with law
  `½ ν + ½ δ_{e₀}`;
* the **escape path** `eₖ = inr k`: from `eₖ` the chain moves to `eₖ₊₁` with probability
  `βₖ = (k + 1)(k + 3)/(k + 2)²` and otherwise jumps with law `ν`.

Then:
* `cexKernel` is a `ν`-irreducible T-chain, with `ν` a maximal irreducibility measure
  (`cex_isMaximalIrreducibility`, `cex_isTChain`);
* `x*` is topologically recurrent (`cex_isTopRecurrent`), since every neighbourhood of `x*`
  contains all but finitely many `aₙ`;
* from `x*` the chain escapes along the `eₖ` forever with probability at least `¼`
  (`cex_escape`: `P_{eₖ}(Φ stays on the escape path up to time m) ≥ (k + 1)/(k + 2)`), so
  `Q(x*, A) ≤ ¾` for `A = {aₙ}` and `x*` is not topologically Harris recurrent
  (`cex_not_isTopHarrisRecurrent`): a topologically recurrent state of a T-chain need not be
  topologically Harris recurrent, even for a `ψ`-irreducible chain (the book's (9.22) makes the
  same point for a reducible chain);
* `x*` lies in no maximal Harris set, so it lies in the transient part `N` of every
  decomposition of Theorem 9.3.6, while being topologically recurrent.

**Correction** (`theorem_9_3_6_counterexample`): the last claim of Theorem 9.3.6, that every
state of `N` is topologically transient, is false. The corrected statement is
`theorem_9_3_6` in `TopologicalRecurrence`.

**Further examples.**
* `cex_recurrent_not_harris` (pp. 203–204): the same chain is recurrent but not Harris, the
  phenomenon of the book's example with appended points.
* `example_9_3_6` (p. 213): for `P(x, {0}) = 1` on `ℝ` (a `δ₀`-irreducible strong Feller chain)
  the only topologically Harris recurrent state is `0`, while `ℝ` is a maximal Harris set:
  `R = {0} ⊊ H`.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-- The state space of the counterexample. -/
abbrev CexSpace := ℕ∞ ⊕ ℕ

/-- Every set of `ℕ∞ ⊕ ℕ` is measurable. -/
theorem measurableSet_cex (s : Set CexSpace) : MeasurableSet s := ⟨trivial, trivial⟩

/-- Singletons of `ℕ∞ ⊕ ℕ` are measurable. -/
theorem measurableSingletonClass_cex : MeasurableSingletonClass CexSpace :=
  ⟨fun _ => measurableSet_cex _⟩

/-- The point `x* = inl ⊤`. -/
def cexStar : CexSpace := Sum.inl ⊤

/-- The Harris part `{aₙ} = {inl n : n ∈ ℕ}`. -/
def cexA : Set CexSpace := range fun n : ℕ => Sum.inl (n : ℕ∞)

/-- The jump law `ν = Σₙ 2^{−(n+1)} δ_{aₙ}`. -/
noncomputable def cexNu : Measure CexSpace :=
  Measure.sum fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1) • Measure.dirac (Sum.inl (n : ℕ∞))

/-- `ν(S) = Σ_{aₙ ∈ S} 2^{−(n+1)}`. -/
theorem cexNu_apply (S : Set CexSpace) :
    cexNu S = ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) * S.indicator 1 (Sum.inl (n : ℕ∞)) := by
  rw [cexNu, Measure.sum_apply _ (measurableSet_cex S)]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_cex S), smul_eq_mul]

/-- `ν` is a probability measure. -/
theorem cexNu_univ : cexNu univ = 1 := by
  rw [cexNu_apply]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- `ν` is a probability measure. -/
theorem isProbabilityMeasure_cexNu : IsProbabilityMeasure cexNu := ⟨cexNu_univ⟩

/-- `ν{aₙ} ≥ 2^{−(n+1)} > 0`. -/
theorem cexNu_pos {S : Set CexSpace} {n : ℕ} (hn : Sum.inl (n : ℕ∞) ∈ S) : 0 < cexNu S := by
  rw [cexNu_apply]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum n)
  rw [indicator_of_mem hn, Pi.one_apply, mul_one]
  exact ENNReal.pow_pos (by norm_num) _

/-- `ν` is carried by the Harris part: `ν(S) = 0` if `S` contains no `aₙ`. -/
theorem cexNu_eq_zero {S : Set CexSpace} (hS : ∀ n : ℕ, Sum.inl (n : ℕ∞) ∉ S) : cexNu S = 0 := by
  rw [cexNu_apply]
  simp [indicator_of_notMem (hS _)]

/-- `ν(Aᶜ) = 0`. -/
theorem cexNu_compl_A : cexNu cexAᶜ = 0 :=
  cexNu_eq_zero fun n h => h ⟨n, rfl⟩

/-- The escape probabilities `βₖ = (k + 1)(k + 3)/(k + 2)²`. -/
noncomputable def cexBeta (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((k : ℝ) + 1) * ((k : ℝ) + 3) / ((k : ℝ) + 2) ^ 2)

/-- `βₖ < 1`. -/
theorem cexBeta_lt_one (k : ℕ) : cexBeta k < 1 := by
  rw [cexBeta, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos,
    div_lt_one (by positivity)]
  nlinarith

/-- The transition law of the counterexample. -/
noncomputable def cexLaw : CexSpace → Measure CexSpace
  | Sum.inl e => if e = ⊤ then (2⁻¹ : ℝ≥0∞) • cexNu + (2⁻¹ : ℝ≥0∞) • Measure.dirac (Sum.inr 0)
      else cexNu
  | Sum.inr k => cexBeta k • Measure.dirac (Sum.inr (k + 1)) + (1 - cexBeta k) • cexNu

/-- The kernel of the counterexample. -/
noncomputable def cexKernel : Kernel CexSpace CexSpace where
  toFun := cexLaw
  measurable' := by
    have := measurableSingletonClass_cex
    exact measurable_of_countable _

/-- The kernel is Markov. -/
theorem isMarkovKernel_cexKernel : IsMarkovKernel cexKernel := by
  refine ⟨fun x => ⟨?_⟩⟩
  change cexLaw x univ = 1
  rcases x with e | k
  · by_cases he : e = ⊤
    · simp only [cexLaw, he, ite_true, Measure.add_apply, Measure.smul_apply, cexNu_univ,
        measure_univ, smul_eq_mul, mul_one]
      exact ENNReal.inv_two_add_inv_two
    · simp only [cexLaw, he, ite_false, cexNu_univ]
  · simp only [cexLaw, Measure.add_apply, Measure.smul_apply, cexNu_univ, measure_univ,
      smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (cexBeta_lt_one k).le

/-- The weight `t(x)` of the continuous component: `½` on `inl`, `1 − βₖ` at `eₖ`. -/
noncomputable def cexT : CexSpace → ℝ≥0∞
  | Sum.inl _ => 2⁻¹
  | Sum.inr k => 1 - cexBeta k

/-- `t(x) > 0`. -/
theorem cexT_pos (x : CexSpace) : 0 < cexT x := by
  rcases x with e | k
  · simp [cexT]
  · exact tsub_pos_of_lt (cexBeta_lt_one k)

/-- `t(x) ≤ 1`. -/
theorem cexT_le_one (x : CexSpace) : cexT x ≤ 1 := by
  rcases x with e | k
  · simp only [cexT]; norm_num
  · exact tsub_le_self

/-- The minorization `P(x, ·) ≥ t(x) ν`. -/
theorem cexT_le (x : CexSpace) : cexT x • cexNu ≤ cexKernel x := by
  change cexT x • cexNu ≤ cexLaw x
  rcases x with e | k
  · by_cases he : e = ⊤
    · simp only [cexT, cexLaw, he, ite_true]
      exact Measure.le_add_right le_rfl
    · simp only [cexT, cexLaw, he, ite_false]
      intro s
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_of_le_one_left' (by norm_num)
  · simp only [cexT, cexLaw]
    exact Measure.le_add_left le_rfl

/-- On the Harris part, `P(aₙ, ·) = ν`. -/
theorem cexKernel_A {y : CexSpace} (hy : y ∈ cexA) : cexKernel y = cexNu := by
  obtain ⟨n, rfl⟩ := hy
  change cexLaw (Sum.inl (n : ℕ∞)) = cexNu
  simp [cexLaw]

/-- `ν`-almost every point lies in the Harris part. -/
theorem ae_cexNu_A : ∀ᵐ y ∂cexNu, y ∈ cexA := by
  rw [ae_iff]
  exact cexNu_compl_A

/-- One-step invariance: `∫ P(z, S) ν(dz) = ν(S)`. -/
theorem cexNu_invariant (S : Set CexSpace) : ∫⁻ z, cexKernel z S ∂cexNu = cexNu S := by
  have := isProbabilityMeasure_cexNu
  rw [lintegral_congr_ae (ae_cexNu_A.mono fun z hz => by rw [cexKernel_A hz]),
    lintegral_const, measure_univ, mul_one]

/-- From the Harris part, `Pⁿ⁺¹(y, ·) = ν`. -/
theorem cexKernel_pow_succ_A (n : ℕ) {y : CexSpace} (hy : y ∈ cexA) :
    (cexKernel ^ (n + 1)) y = cexNu := by
  induction n with
  | zero => rw [zero_add, pow_one]; exact cexKernel_A hy
  | succ n ih =>
    ext S hS
    rw [pow_succ_apply' _ (n + 1) y hS, ih, cexNu_invariant]

/-- `ν` is invariant: `∫ Pⁿ(y, S) ν(dy) = ν(S)`. -/
theorem cexNu_pow_invariant (n : ℕ) (S : Set CexSpace) :
    ∫⁻ y, (cexKernel ^ n) y S ∂cexNu = cexNu S := by
  have := isProbabilityMeasure_cexNu
  rcases n with _ | n
  · simp_rw [pow_zero_apply]
    rw [show (fun y => Measure.dirac y S) = S.indicator 1 from funext fun y =>
      Measure.dirac_apply' y (measurableSet_cex S), lintegral_indicator_one (measurableSet_cex S)]
  · rw [lintegral_congr_ae (ae_cexNu_A.mono fun y hy => by rw [cexKernel_pow_succ_A n hy]),
      lintegral_const, measure_univ, mul_one]

/-- `Pⁿ⁺¹(x, S) ≥ t(x) ν(S)` for every `x`. -/
theorem cexKernel_pow_succ_ge (n : ℕ) (x : CexSpace) (S : Set CexSpace) :
    cexT x * cexNu S ≤ (cexKernel ^ (n + 1)) x S := by
  rw [pow_succ_apply _ n x (measurableSet_cex S)]
  calc cexT x * cexNu S = ∫⁻ z, (cexKernel ^ n) z S ∂(cexT x • cexNu) := by
        rw [lintegral_smul_measure, cexNu_pow_invariant, smul_eq_mul]
    _ ≤ ∫⁻ z, (cexKernel ^ n) z S ∂cexKernel x := lintegral_mono' (cexT_le x) le_rfl

/-- **`ν` is a maximal irreducibility measure** for the counterexample. -/
theorem cex_isMaximalIrreducibility :
    haveI := isMarkovKernel_cexKernel
    IsMaximalIrreducibility cexKernel cexNu := by
  have := isMarkovKernel_cexKernel
  refine ⟨fun h => by have := cexNu_univ; rw [h] at this; simp at this, fun A hA hνA x => ?_,
    fun φ hφ => fun B hB => ?_⟩
  · refine lt_of_lt_of_le ?_ (le_hitProb_of_kernel cexKernel hA x)
    calc (0 : ℝ≥0∞) < cexT x * cexNu A := ENNReal.mul_pos (cexT_pos x).ne' hνA.ne'
      _ ≤ cexKernel x A := by
          have := cexKernel_pow_succ_ge 0 x A
          rwa [zero_add, pow_one] at this
  · -- a `ν`-null set is not reachable from the Harris part
    by_contra hφB
    have hpos := hφ B (measurableSet_cex B) (pos_iff_ne_zero.2 hφB) (Sum.inl ((0 : ℕ) : ℕ∞))
    obtain ⟨n, hn⟩ := (hitProb_pos_iff cexKernel (measurableSet_cex B) _).1 hpos
    rw [cexKernel_pow_succ_A n (y := Sum.inl ((0 : ℕ) : ℕ∞)) ⟨0, rfl⟩, hB] at hn
    exact lt_irrefl 0 hn

/-! ### The T-chain property and topological recurrence of `x*` -/

/-- The continuous component `T(x, ·) = t(x) ν`. -/
noncomputable def cexTKernel : Kernel CexSpace CexSpace where
  toFun x := cexT x • cexNu
  measurable' := by
    have := measurableSingletonClass_cex
    exact measurable_of_countable _

/-- **The counterexample is a T-chain**: `T(x, ·) = t(x) ν ≤ P(x, ·)` with `x ↦ T(x, A)`
continuous and `T(x, X) = t(x) > 0`. -/
theorem cex_isTChain :
    haveI := isMarkovKernel_cexKernel
    IsTChain cexKernel := by
  have := isMarkovKernel_cexKernel
  have hT : ∀ x A, cexTKernel x A = cexT x * cexNu A := fun x A => by
    change (cexT x • cexNu) A = _
    rw [Measure.smul_apply, smul_eq_mul]
  refine ⟨diracDist 1, cexTKernel, isSamplingDist_diracDist 1,
    ⟨fun x => ?_, fun x => ?_, fun A _ => ?_⟩, fun x => ?_⟩
  · rw [hT, cexNu_univ, mul_one]; exact cexT_le_one x
  · rw [sampledKernel_diracDist, pow_one]; exact cexT_le x
  · refine Continuous.lowerSemicontinuous ?_
    simp_rw [hT]
    refine continuous_sum_dom.2 ⟨?_, continuous_of_discreteTopology⟩
    have : (fun e : ℕ∞ => cexT (Sum.inl e) * cexNu A) = fun _ => 2⁻¹ * cexNu A := rfl
    simp only [Function.comp_def]
    rw [this]
    exact continuous_const
  · rw [hT, cexNu_univ, mul_one]; exact cexT_pos x

/-- **`x*` is topologically recurrent**: every neighbourhood of `x*` contains all but finitely
many `aₙ`, hence has positive `ν`-measure, and `Pⁿ⁺¹(x*, ·) ≥ ½ ν`. -/
theorem cex_isTopRecurrent : IsTopRecurrent cexKernel cexStar := by
  intro O hO hxO
  have hpre : IsOpen (Sum.inl ⁻¹' O : Set ℕ∞) := hO.preimage continuous_inl
  have hmem : (Sum.inl ⁻¹' O : Set ℕ∞) ∈ 𝓝 (⊤ : ℕ∞) := hpre.mem_nhds hxO
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ENat.tendsto_natCast_nhds_top.eventually hmem)
  have hνO : 0 < cexNu O := cexNu_pos (hN N le_rfl)
  rw [potKernel_apply _ _ (measurableSet_cex O)]
  refine top_unique ?_
  calc (∞ : ℝ≥0∞) = ∑' _ : ℕ, cexT cexStar * cexNu O :=
        (ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.mul_pos (cexT_pos _).ne' hνO.ne').ne').symm
    _ ≤ ∑' n : ℕ, (cexKernel ^ (n + 1)) cexStar O :=
        ENNReal.tsum_le_tsum fun n => cexKernel_pow_succ_ge n cexStar O

/-! ### Escape from `x*` -/

/-- `P(eₖ, {eₖ₊₁}) ≥ βₖ`. -/
theorem cexKernel_step (k : ℕ) : cexBeta k ≤ cexKernel (Sum.inr k) {Sum.inr (k + 1)} := by
  change cexBeta k ≤ cexLaw (Sum.inr k) {Sum.inr (k + 1)}
  simp only [cexLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_cex _), indicator_of_mem (mem_singleton _),
    Pi.one_apply, mul_one]
  exact le_self_add

/-- **Escape along the path**: `P_{eₖ}(Φ₀, …, Φₘ ∈ {eⱼ}) ≥ (k + 1)/(k + 2)`; the bound is preserved
exactly by `βₖ (k + 2)/(k + 3) = (k + 1)/(k + 2)`. -/
theorem cex_escape_finite (m k : ℕ) :
    haveI := isMarkovKernel_cexKernel
    ENNReal.ofReal (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
      pathKernel cexKernel (Sum.inr k) {ω | ∀ n ≤ m, ω n ∈ range Sum.inr} := by
  have := isMarkovKernel_cexKernel
  have := isMarkovKernel_pathKernel cexKernel
  induction m generalizing k with
  | zero =>
    have h1 : pathKernel cexKernel (Sum.inr k) {ω | ∀ n ≤ 0, ω n ∈ range Sum.inr} = 1 := by
      have : {ω : ℕ → CexSpace | ∀ n ≤ 0, ω n ∈ range Sum.inr} = {ω | ω 0 ∈ range Sum.inr} := by
        ext ω; simp
      rw [this, pathKernel_zero_mem _ _ (measurableSet_cex _),
        indicator_of_mem (show Sum.inr k ∈ range (Sum.inr : ℕ → CexSpace) from ⟨k, rfl⟩)]
      rfl
    rw [h1, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one (by positivity)).2 (by linarith))
  | succ m ih =>
    have hE0 : pathKernel cexKernel (Sum.inr k) {ω | ω 0 ∈ range Sum.inr}ᶜ = 0 := by
      have hm0 : MeasurableSet {ω : ℕ → CexSpace | ω 0 ∈ range Sum.inr} :=
        measurable_pi_apply 0 (measurableSet_cex _)
      rw [prob_compl_eq_zero_iff hm0, pathKernel_zero_mem _ _ (measurableSet_cex _),
        indicator_of_mem (show Sum.inr k ∈ range (Sum.inr : ℕ → CexSpace) from ⟨k, rfl⟩)]
      rfl
    have hsub : {ω : ℕ → CexSpace | ω 1 ∈ ({Sum.inr (k + 1)} : Set CexSpace)} ∩
        shift 1 ⁻¹' {ω | ∀ n ≤ m, ω n ∈ range Sum.inr} ∩ {ω | ω 0 ∈ range Sum.inr} ⊆
        {ω | ∀ n ≤ m + 1, ω n ∈ range Sum.inr} := by
      rintro ω ⟨⟨-, h2⟩, h0⟩ n hn
      rcases n with _ | n
      · exact h0
      · have := h2 n (by omega)
        simpa [shift_apply, add_comm] using this
    have hGm : MeasurableSet {ω : ℕ → CexSpace | ∀ n ≤ m, ω n ∈ range Sum.inr} := by
      have : {ω : ℕ → CexSpace | ∀ n ≤ m, ω n ∈ range Sum.inr} =
          ⋂ n ∈ Finset.range (m + 1), {ω | ω n ∈ range Sum.inr} := by ext ω; simp
      rw [this]
      exact Finset.measurableSet_biInter _ fun n _ => measurable_pi_apply n (measurableSet_cex _)
    have hstep := pathKernel_first_step cexKernel (Sum.inr k)
      (measurableSet_cex {Sum.inr (k + 1)}) hGm
    have hmeas : Measurable fun y => pathKernel cexKernel y
        {ω : ℕ → CexSpace | ∀ n ≤ m, ω n ∈ range Sum.inr} := Kernel.measurable_coe _ hGm
    rw [lintegral_singleton' hmeas] at hstep
    have hreal : ((k : ℝ) + 1) * ((k : ℝ) + 3) / ((k : ℝ) + 2) ^ 2 *
        ((((k + 1 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 2)) = ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
      push_cast
      field_simp
      ring
    calc ENNReal.ofReal (((k : ℝ) + 1) / ((k : ℝ) + 2))
        = cexBeta k * ENNReal.ofReal ((((k + 1 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 2)) := by
          rw [cexBeta, ← ENNReal.ofReal_mul (by positivity), hreal]
      _ ≤ cexKernel (Sum.inr k) {Sum.inr (k + 1)} *
            pathKernel cexKernel (Sum.inr (k + 1)) {ω | ∀ n ≤ m, ω n ∈ range Sum.inr} := by
          gcongr
          · exact cexKernel_step k
          · exact ih (k + 1)
      _ = pathKernel cexKernel (Sum.inr k) ({ω | ω 1 ∈ ({Sum.inr (k + 1)} : Set CexSpace)} ∩
            shift 1 ⁻¹' {ω | ∀ n ≤ m, ω n ∈ range Sum.inr}) := by rw [hstep, mul_comm]
      _ = pathKernel cexKernel (Sum.inr k) ({ω | ω 1 ∈ ({Sum.inr (k + 1)} : Set CexSpace)} ∩
            shift 1 ⁻¹' {ω | ∀ n ≤ m, ω n ∈ range Sum.inr} ∩ {ω | ω 0 ∈ range Sum.inr}) :=
          (measure_inter_conull hE0).symm
      _ ≤ _ := measure_mono hsub

/-- **Escape from `x*`**: with probability at least `¼` the chain jumps from `x*` to `e₀` and
then stays on the escape path forever. -/
theorem cex_escape :
    haveI := isMarkovKernel_cexKernel
    2⁻¹ * 2⁻¹ ≤ pathKernel cexKernel cexStar {ω | ∀ n, ω (n + 1) ∈ range Sum.inr} := by
  have := isMarkovKernel_cexKernel
  have := isMarkovKernel_pathKernel cexKernel
  set G : ℕ → Set (ℕ → CexSpace) := fun m => {ω | ∀ n ≤ m, ω n ∈ range Sum.inr}
  have hGm : ∀ m, MeasurableSet (G m) := fun m => by
    have : G m = ⋂ n ∈ Finset.range (m + 1), {ω | ω n ∈ range Sum.inr} := by
      ext ω; simp [G]
    rw [this]
    exact Finset.measurableSet_biInter _ fun n _ => measurable_pi_apply n (measurableSet_cex _)
  have hGanti : Antitone G := fun a b hab ω hω n hn => hω n (hn.trans hab)
  have hinf : 2⁻¹ ≤ pathKernel cexKernel (Sum.inr 0) (⋂ m, G m) := by
    rw [hGanti.measure_iInter (fun m => (hGm m).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    refine le_iInf fun m => ?_
    have h := cex_escape_finite m 0
    have e : ENNReal.ofReal ((((0 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 2)) = 2⁻¹ := by
      rw [Nat.cast_zero, zero_add, zero_add, one_div, ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    rw [e] at h
    exact h
  have hGi : MeasurableSet (⋂ m, G m) := MeasurableSet.iInter hGm
  have hstep := pathKernel_first_step cexKernel cexStar (measurableSet_cex {Sum.inr 0}) hGi
  rw [lintegral_singleton' (Kernel.measurable_coe _ hGi)] at hstep
  have hP0 : 2⁻¹ ≤ cexKernel cexStar {Sum.inr 0} := by
    change 2⁻¹ ≤ cexLaw (Sum.inl ⊤) {Sum.inr 0}
    simp only [cexLaw, ite_true, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_cex _), indicator_of_mem (mem_singleton _),
      Pi.one_apply, mul_one]
    exact le_add_self
  have hsub : {ω : ℕ → CexSpace | ω 1 ∈ ({Sum.inr 0} : Set CexSpace)} ∩
      shift 1 ⁻¹' (⋂ m, G m) ⊆ {ω | ∀ n, ω (n + 1) ∈ range Sum.inr} := by
    rintro ω ⟨-, h⟩ n
    have := mem_iInter.1 h n n le_rfl
    simpa [shift_apply, add_comm] using this
  calc (2⁻¹ : ℝ≥0∞) * 2⁻¹ ≤ pathKernel cexKernel (Sum.inr 0) (⋂ m, G m) *
        cexKernel cexStar {Sum.inr 0} := mul_le_mul' hinf hP0
    _ = _ := hstep.symm
    _ ≤ _ := measure_mono hsub

/-- From `x*` the chain visits the `inl`-part only finitely often with probability at least `¼`:
`Q(x*, O) ≤ 1 − ¼ < 1` for every `O ⊆ range inl`. -/
theorem cex_harrisQ_lt_one {O : Set CexSpace} (hO : O ⊆ range Sum.inl) :
    haveI := isMarkovKernel_cexKernel
    harrisQ cexKernel O cexStar < 1 := by
  have := isMarkovKernel_cexKernel
  have := isMarkovKernel_pathKernel cexKernel
  set E := {ω : ℕ → CexSpace | ∀ n, ω (n + 1) ∈ range Sum.inr}
  have hEm : MeasurableSet E := by
    have : E = ⋂ n, {ω | ω (n + 1) ∈ range Sum.inr} := by ext ω; simp [E]
    rw [this]
    exact MeasurableSet.iInter fun n => measurable_pi_apply _ (measurableSet_cex _)
  have hdisj : ioSet O ⊆ Eᶜ := by
    intro ω hio hE
    obtain ⟨n, hn, hnO⟩ := hio 1
    obtain ⟨a, ha⟩ := hO hnO
    obtain ⟨b, hb⟩ := hE (n - 1)
    rw [show n - 1 + 1 = n by omega, ← ha] at hb
    exact Sum.inr_ne_inl hb
  have hpos : (0 : ℝ≥0∞) < 2⁻¹ * 2⁻¹ := ENNReal.mul_pos (by simp) (by simp)
  calc harrisQ cexKernel O cexStar ≤ pathKernel cexKernel cexStar Eᶜ := measure_mono hdisj
    _ = 1 - pathKernel cexKernel cexStar E := prob_compl_eq_one_sub hEm
    _ ≤ 1 - 2⁻¹ * 2⁻¹ := tsub_le_tsub_left cex_escape 1
    _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'

/-- `x*` is **not topologically Harris recurrent**, although it is topologically recurrent
(`cex_isTopRecurrent`): the open neighbourhood `range inl` has `Q(x*, ·) < 1`. -/
theorem cex_not_isTopHarrisRecurrent :
    haveI := isMarkovKernel_cexKernel
    ¬ IsTopHarrisRecurrent cexKernel cexStar := by
  have := isMarkovKernel_cexKernel
  intro h
  have h1 := h (range Sum.inl) isOpen_range_inl ⟨⊤, rfl⟩
  exact (cex_harrisQ_lt_one subset_rfl).ne h1

/-- **Correction to Theorem 9.3.6** (MT p. 213): the counterexample chain is a `ν`-irreducible
T-chain (`ν` maximal) with a topologically recurrent state `x*` that lies in no maximal Harris
set, hence in the transient part `N` of every decomposition `X = H ∪ N` of Theorem 9.3.6; so the
claim "every state in `N` is topologically transient" fails. -/
theorem theorem_9_3_6_counterexample :
    haveI := isMarkovKernel_cexKernel
    IsMaximalIrreducibility cexKernel cexNu ∧ IsTChain cexKernel ∧
      IsTopRecurrent cexKernel cexStar ∧ ¬ IsTopHarrisRecurrent cexKernel cexStar ∧
      (∀ H : Set CexSpace, (H = ∅ ∨ IsMaximalHarrisSet cexKernel cexNu H) → cexStar ∉ H) ∧
      ¬ ∃ H : Set CexSpace, (H = ∅ ∨ IsMaximalHarrisSet cexKernel cexNu H) ∧
        IsTransientSet cexKernel Hᶜ ∧ ∀ x ∉ H, IsTopTransient cexKernel x := by
  have := isMarkovKernel_cexKernel
  have hnotin : ∀ H : Set CexSpace, (H = ∅ ∨ IsMaximalHarrisSet cexKernel cexNu H) →
      cexStar ∉ H := by
    rintro H (rfl | ⟨-, -, -, -, hQ⟩) hx
    · exact hx
    · have hA : MeasurableSet cexA := measurableSet_cex _
      have h1 := hQ cexA hA
        (cexNu_pos (n := 0) (show Sum.inl ((0 : ℕ) : ℕ∞) ∈ cexA from ⟨0, rfl⟩)) cexStar hx
      have hsub : cexA ⊆ range Sum.inl := by
        rintro y ⟨n, rfl⟩
        exact ⟨(n : ℕ∞), rfl⟩
      exact (cex_harrisQ_lt_one hsub).ne h1
  refine ⟨cex_isMaximalIrreducibility, cex_isTChain, cex_isTopRecurrent,
    cex_not_isTopHarrisRecurrent, hnotin, ?_⟩
  rintro ⟨H, hH, -, htop⟩
  exact htop cexStar (hnotin H hH) cex_isTopRecurrent

/-- Every set of `ℕ∞ ⊕ ℕ` is measurable, so open sets are. -/
theorem opensMeasurableSpace_cex : OpensMeasurableSpace CexSpace :=
  ⟨fun s _ => measurableSet_cex s⟩

/-- **A recurrent chain that is not Harris** (MT pp. 203–204): the counterexample chain is
recurrent (Theorem 9.3.3 at the reachable, topologically recurrent point `x*`) but not Harris
recurrent, since from `x*` the set `{x*} ∪ {aₙ} ∈ B⁺(X)` is visited only finitely often with
positive probability. This is the phenomenon of the book's example with appended points. -/
theorem cex_recurrent_not_harris :
    haveI := isMarkovKernel_cexKernel
    IsRecurrentChain cexKernel cexNu ∧ ¬ IsHarris cexKernel cexNu := by
  have := isMarkovKernel_cexKernel
  have := opensMeasurableSpace_cex
  have hreach : IsReachable cexKernel cexStar := by
    intro O hO hxO y
    have hpre : IsOpen (Sum.inl ⁻¹' O : Set ℕ∞) := hO.preimage continuous_inl
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ENat.tendsto_natCast_nhds_top.eventually
      (hpre.mem_nhds hxO))
    have hνO : 0 < cexNu O := cexNu_pos (hN N le_rfl)
    rw [potKernel_apply _ _ (measurableSet_cex O)]
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 0)
    exact lt_of_lt_of_le (ENNReal.mul_pos (cexT_pos y).ne' hνO.ne')
      (cexKernel_pow_succ_ge 0 y O)
  refine ⟨(theorem_9_3_3 cex_isMaximalIrreducibility cex_isTChain hreach).2 cex_isTopRecurrent,
    fun hH => ?_⟩
  have hsub : insert cexStar cexA ⊆ range Sum.inl := by
    rintro y (rfl | ⟨n, rfl⟩)
    · exact ⟨⊤, rfl⟩
    · exact ⟨(n : ℕ∞), rfl⟩
  have h1 := hH.2 (insert cexStar cexA) (measurableSet_cex _)
    (cexNu_pos (n := 0) (Or.inr ⟨0, rfl⟩)) cexStar (mem_insert _ _)
  exact (cex_harrisQ_lt_one hsub).ne h1

/-! ### The example after Theorem 9.3.6: `R` can be smaller than `H` -/

/-- The chain on `ℝ` that jumps to `0` from every state, `P(x, {0}) = 1`. -/
noncomputable abbrev toZeroKernel : Kernel ℝ ℝ :=
  Kernel.deterministic (fun _ : ℝ => (0 : ℝ)) measurable_const

/-- From any state, `Φₙ = 0` for every `n ≥ 1`, almost surely. -/
theorem ae_toZero (x : ℝ) : ∀ᵐ ω ∂pathKernel toZeroKernel x, ∀ n, ω (n + 1) = 0 := by
  filter_upwards [ae_orbit_deterministic (f := fun _ : ℝ => (0 : ℝ)) measurable_const x]
    with ω hω n
  rw [hω, Function.iterate_succ_apply']

/-- `Q(x, A) = 1` for every `x` and every `A ∋ 0`. -/
theorem toZero_harrisQ {A : Set ℝ} (h0 : (0 : ℝ) ∈ A) (x : ℝ) :
    harrisQ toZeroKernel A x = 1 := by
  have := isMarkovKernel_pathKernel toZeroKernel
  refine le_antisymm (harrisQ_le_one _ _ _) ?_
  rw [harrisQ, ← measure_univ (μ := pathKernel toZeroKernel x)]
  refine measure_mono_ae ?_
  filter_upwards [ae_toZero x] with ω hω _ N
  exact ⟨N + 1, by omega, by rw [hω N]; exact h0⟩

/-- **The example after Theorem 9.3.6** (MT p. 213): the chain `P(x, {0}) = 1` on `ℝ` is
`δ₀`-irreducible (with `δ₀` maximal) and strong Feller; its only topologically Harris recurrent
state is `0`, while the whole space is a maximal Harris set: `R = {0} ⊊ H = ℝ`. -/
theorem example_9_3_6 :
    IsMaximalIrreducibility toZeroKernel (Measure.dirac 0) ∧ IsStrongFeller toZeroKernel ∧
      {x | IsTopHarrisRecurrent toZeroKernel x} = {0} ∧
      IsMaximalHarrisSet toZeroKernel (Measure.dirac 0) univ := by
  have hpow : ∀ n x, (toZeroKernel ^ (n + 1)) x = Measure.dirac 0 := fun n x => by
    rw [toZeroKernel, deterministic_pow_apply, Function.iterate_succ_apply']
  refine ⟨⟨by simp, fun A hA hpos x => ?_, fun φ hφ => fun B hB => ?_⟩, fun f hf _ => ?_,
    ?_, ⟨MeasurableSet.univ, univ_nonempty, fun x _ => measure_univ, ?_, fun A hA hpos x _ => ?_⟩⟩
  · refine (hitProb_pos_iff _ hA x).2 ⟨0, ?_⟩
    rw [hpow]; exact hpos
  · have h0 : (0 : ℝ) ∉ B := fun h => by simp [h] at hB
    by_contra hφB
    set M := toMeasurable φ B \ {0}
    have hM : MeasurableSet M := (measurableSet_toMeasurable φ B).diff (measurableSet_singleton 0)
    have hφM : 0 < φ M := lt_of_lt_of_le (pos_iff_ne_zero.2 hφB)
      (measure_mono fun y hy => ⟨subset_toMeasurable φ B hy, fun h => h0 (h ▸ hy)⟩)
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hM 0).1 (hφ M hM hφM 0)
    rw [hpow, Measure.dirac_apply' _ hM, indicator_of_notMem (fun h => h.2 rfl)] at hn
    exact lt_irrefl 0 hn
  · have : kfunR toZeroKernel f = fun _ => f 0 := by
      funext x
      simp [kfunR, toZeroKernel, Kernel.deterministic_apply, integral_dirac]
    rw [this]; exact continuous_const
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro h
      by_contra hx
      have hO : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
      have hQ := h {0}ᶜ hO hx
      have := isMarkovKernel_pathKernel toZeroKernel
      have h0 : harrisQ toZeroKernel {0}ᶜ x = 0 := by
        rw [harrisQ, measure_eq_zero_iff_ae_notMem]
        filter_upwards [ae_toZero x] with ω hω hio
        obtain ⟨k, hk, hkO⟩ := hio 1
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact hkO (hω j)
      rw [h0] at hQ
      exact zero_ne_one hQ
    · rintro rfl O hO h0
      exact toZero_harrisQ h0 0
  · ext y
    simp only [harrisInfty, mem_ofPred_eq, mem_univ, iff_true]
    refine le_antisymm (hitProb_le_one _ _ _) ?_
    have := le_hitProb_of_kernel toZeroKernel MeasurableSet.univ y
    rwa [measure_univ] at this
  · have h0 : (0 : ℝ) ∈ A := by
      by_contra h; rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hpos
      exact lt_irrefl 0 hpos
    exact toZero_harrisQ h0 x

end MeynTweedie.InvarianceTightness
