/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.NullRecurrence
import Positivity.CountableInvariant
import Positivity.UniqueInvariant
import Positivity.FNormErgodic

/-!
# A null recurrent chain that is not Harris (MT Theorem 18.1.3)

Meyn and Tweedie, p. 468. Theorem 18.1.3 is stated for an "aperiodic and null recurrent" chain,
but its proof uses (18.13) from every starting point, which is Orey's Theorem 18.1.2 for Harris
chains. Without the Harris property the statement is false.

**The chain** `escKernel` on `ℕ ⊕ ℕ`:
* on the **renewal part** `inl j` it is the forward recurrence time chain `escQ` with the renewal
  law `escP = Σₖ 2^{−(k+1)} δ_{2ᵏ}`, which has `p(1) = ½` and infinite mean;
* on the **escape path** `inr k` it moves to `inr (k + 1)` with probability
  `βₖ = aₖ₊₁/aₖ`, `aₖ = ½ + 2^{−(k+1)}`, and otherwise jumps to `inl 0`; so from `inr 0` it is
  still on the escape path at time `n` with probability at least `aₙ ≥ ½`
  (`escKernel_pow_escape`).

**Results.**
* `escKernel_isMaximalIrreducibility`: counting measure on the renewal part, `escPsi`, is a
  maximal irreducibility measure; `escKernel_isRecurrentChain`: the chain is recurrent
  (`U(x, A) = ∞` for every `x` and `ψ(A) > 0`); `escKernel_isAperiodic` (a minorization at
  `inl 0`).
* `isInvariant_escPi`: `π = Σⱼ p{n > j} δ_{inl j}` is invariant, `π(X) = ∞` (`escPi_univ`),
  and `escKernel_isNull`: there is no invariant probability (Theorem 10.0.1).
* **Correction** (`theorem_18_1_3_counterexample`): the chain is recurrent, null and aperiodic
  with invariant `π ≠ 0`, but (18.15) fails for `λ = δ_{inr 0}` and `ε = 1`, since
  `Pⁿ(inr 0, {inr n}) ≥ ½` while `π{inr n} = 0`. Hence it is not Harris. The corrected
  statement, for Harris chains, is `theorem_18_1_3` in `NullRecurrence`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### The renewal law and the escape probabilities -/

/-- The renewal law `p = Σₖ 2^{−(k+1)} δ_{2ᵏ}`: `p(0) = 0`, `p(1) = ½`, unbounded support and
infinite mean. -/
noncomputable def escP : Measure ℕ :=
  Measure.sum fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ (k + 1) • Measure.dirac (2 ^ k)

/-- `p{n} = Σₖ 2^{−(k+1)} 1{2ᵏ = n}`. -/
theorem escP_singleton (n : ℕ) :
    escP {n} = ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ({n} : Set ℕ).indicator 1 (2 ^ k) := by
  rw [escP, Measure.sum_apply _ (measurableSet_singleton n)]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton n), smul_eq_mul]

/-- `p{2ᵐ} = 2^{−(m+1)}`. -/
theorem escP_pow (m : ℕ) : escP {2 ^ m} = (2⁻¹ : ℝ≥0∞) ^ (m + 1) := by
  rw [escP_singleton, tsum_eq_single m fun k hk => by
    rw [indicator_of_notMem (s := {2 ^ m})
      (fun h => hk (Nat.pow_right_injective le_rfl (mem_singleton_iff.1 h))), mul_zero]]
  rw [indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one]

/-- `p{0} = 0`. -/
theorem escP_zero : escP {0} = 0 := by
  rw [escP_singleton]
  refine ENNReal.tsum_eq_zero.2 fun k => ?_
  rw [indicator_of_notMem (s := {0}) (fun h => pow_ne_zero k two_ne_zero (mem_singleton_iff.1 h)),
    mul_zero]

/-- `p` is a probability. -/
theorem isProbabilityMeasure_escP : IsProbabilityMeasure escP := by
  constructor
  rw [escP, Measure.sum_apply _ MeasurableSet.univ]
  have : ∀ k : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (k + 1) • Measure.dirac (2 ^ k)) univ = 2⁻¹ ^ (k + 1) :=
    fun k => by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [this]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- `p` has infinite mean: `Σₙ n p(n) = Σₖ 2ᵏ 2^{−(k+1)} = ∞`. -/
theorem escP_mean : ∫⁻ n, (n : ℝ≥0∞) ∂escP = ∞ := by
  rw [escP, lintegral_sum_measure]
  have : ∀ k : ℕ, ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂((2⁻¹ : ℝ≥0∞) ^ (k + 1) • Measure.dirac (2 ^ k : ℕ)) =
      2⁻¹ :=
    fun k => by
      rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, pow_succ,
        mul_comm ((2⁻¹ : ℝ≥0∞) ^ k), mul_assoc]
      push_cast
      rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
  simp_rw [this]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

/-- `p` has unbounded support. -/
theorem escP_supp (N : ℕ) : ∃ n, N < n ∧ 0 < escP {n} :=
  ⟨2 ^ N, Nat.lt_two_pow_self, by rw [escP_pow]; exact ENNReal.pow_pos (by norm_num) _⟩

/-- The decreasing sequence `aₖ = ½ + 2^{−(k+1)}`, from `a₀ = 1` down to `½`. -/
noncomputable def escA (k : ℕ) : ℝ≥0∞ := 2⁻¹ + 2⁻¹ ^ (k + 1)

/-- `aₖ ≠ 0`. -/
theorem escA_ne_zero (k : ℕ) : escA k ≠ 0 := by
  exact (lt_of_lt_of_le (by norm_num) (show (2⁻¹ : ℝ≥0∞) ≤ escA k from le_self_add)).ne'

/-- `aₖ ≠ ∞`. -/
theorem escA_ne_top (k : ℕ) : escA k ≠ ∞ := by
  rw [escA]
  exact ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.pow_ne_top (by norm_num)⟩

/-- `aₖ₊₁ < aₖ`. -/
theorem escA_succ_lt (k : ℕ) : escA (k + 1) < escA k := by
  rw [escA, escA]
  refine (ENNReal.add_lt_add_iff_left (by norm_num : (2⁻¹ : ℝ≥0∞) ≠ ∞)).2 ?_
  rw [pow_succ _ (k + 1)]
  calc (2⁻¹ : ℝ≥0∞) ^ (k + 1) * 2⁻¹ < 2⁻¹ ^ (k + 1) * 1 :=
        (ENNReal.mul_lt_mul_iff_right (pow_ne_zero _ (by norm_num))
          (ENNReal.pow_ne_top (by norm_num))).2 (by norm_num)
    _ = 2⁻¹ ^ (k + 1) := mul_one _

/-- `aₖ ≥ ½`. -/
theorem escA_ge (k : ℕ) : 2⁻¹ ≤ escA k := le_self_add

/-- The escape probabilities `βₖ = aₖ₊₁/aₖ < 1`, so that `β₀ ⋯ βₖ₋₁ = aₖ ≥ ½`. -/
noncomputable def escBeta (k : ℕ) : ℝ≥0∞ := escA (k + 1) / escA k

/-- `βₖ < 1`. -/
theorem escBeta_lt_one (k : ℕ) : escBeta k < 1 := by
  rw [escBeta, ENNReal.div_lt_iff (Or.inl (escA_ne_zero k)) (Or.inl (escA_ne_top k)), one_mul]
  exact escA_succ_lt k

/-- `aₖ βₖ = aₖ₊₁`. -/
theorem escA_mul_escBeta (k : ℕ) : escA k * escBeta k = escA (k + 1) :=
  ENNReal.mul_div_cancel (escA_ne_zero k) (escA_ne_top k)

/-! ### The chain -/

/-- Every set of `ℕ ⊕ ℕ` is measurable. -/
theorem measurableSet_esc (A : Set (ℕ ⊕ ℕ)) : MeasurableSet A := ⟨trivial, trivial⟩

/-- Singletons of `ℕ ⊕ ℕ` are measurable. -/
theorem measurableSingletonClass_esc : MeasurableSingletonClass (ℕ ⊕ ℕ) :=
  ⟨fun _ => measurableSet_esc _⟩

/-- The forward recurrence time chain with the renewal law `p = escP`. -/
noncomputable abbrev escQ : Kernel ℕ ℕ := fwdRecKernel escP

/-- The transition laws on `ℕ ⊕ ℕ`: on the **renewal part** `inl j` the forward recurrence time
chain `escQ`; on the **escape path** `inr k` a step to `inr (k + 1)` with probability `βₖ` and
otherwise a jump to `inl 0`. -/
noncomputable def escLaw : ℕ ⊕ ℕ → Measure (ℕ ⊕ ℕ)
  | Sum.inl j => (escQ j).map Sum.inl
  | Sum.inr k => escBeta k • Measure.dirac (Sum.inr (k + 1)) +
      (1 - escBeta k) • Measure.dirac (Sum.inl 0)

/-- The null recurrent chain that is not Harris. -/
noncomputable def escKernel : Kernel (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) :=
  ⟨escLaw, fun _ _ => measurableSet_esc _⟩

/-- `P(inl j, ·) = Q(j, ·)` carried to the renewal part. -/
theorem escKernel_inl (j : ℕ) : escKernel (Sum.inl j) = (escQ j).map Sum.inl := rfl

/-- `P(inr k, ·) = βₖ δ_{inr (k+1)} + (1 − βₖ) δ_{inl 0}`. -/
theorem escKernel_inr (k : ℕ) : escKernel (Sum.inr k) =
    escBeta k • Measure.dirac (Sum.inr (k + 1)) + (1 - escBeta k) • Measure.dirac (Sum.inl 0) :=
  rfl

/-- `escQ` is a transition kernel. -/
theorem isMarkovKernel_escQ : IsMarkovKernel escQ := by
  have := isProbabilityMeasure_escP
  exact isMarkovKernel_fwdRecKernel escP

/-- `escKernel` is a transition kernel. -/
theorem isMarkovKernel_escKernel : IsMarkovKernel escKernel := by
  have := isMarkovKernel_escQ
  refine ⟨fun x => ⟨?_⟩⟩
  rcases x with j | k
  · rw [escKernel_inl, Measure.map_apply measurable_inl MeasurableSet.univ, preimage_univ,
      measure_univ]
  · rw [escKernel_inr, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      add_tsub_cancel_of_le (escBeta_lt_one k).le]

/-- **The renewal part is closed**: `Pⁿ(inl j, A) = Qⁿ(j, inl⁻¹ A)`. -/
theorem escKernel_pow_inl (n j : ℕ) (A : Set (ℕ ⊕ ℕ)) :
    (escKernel ^ n) (Sum.inl j) A = (escQ ^ n) j (Sum.inl ⁻¹' A) := by
  induction n generalizing j with
  | zero =>
    rw [pow_zero_apply, pow_zero_apply, Measure.dirac_apply' _ (measurableSet_esc A),
      Measure.dirac_apply' _ (measurableSet_of_countable _)]
    by_cases h : Sum.inl j ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (show j ∈ Sum.inl ⁻¹' A from h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show j ∉ Sum.inl ⁻¹' A from h)]
  | succ n ih =>
    rw [pow_succ_apply _ n _ (measurableSet_esc A), pow_succ_apply _ n _
      (measurableSet_of_countable _), escKernel_inl,
      lintegral_map (Kernel.measurable_coe _ (measurableSet_esc A)) measurable_inl]
    simp_rw [ih]

/-- The renewal law at `0`: `P(inl 0, {inl 0}) = p(1) = ½`. -/
theorem escKernel_inl_zero : escKernel (Sum.inl 0) {Sum.inl 0} = 2⁻¹ := by
  have h := escKernel_pow_inl 1 0 {Sum.inl 0}
  rw [pow_one, pow_one] at h
  rw [h, show (Sum.inl ⁻¹' {Sum.inl 0} : Set ℕ) = {0} from by ext; simp,
    fwdRec_zero_singleton escP_zero, show (0 + 1 : ℕ) = 2 ^ 0 from rfl, escP_pow, zero_add,
    pow_one]

/-- `P(inr k, {inr (k+1)}) = βₖ`. -/
theorem escKernel_inr_step (k : ℕ) : escKernel (Sum.inr k) {Sum.inr (k + 1)} = escBeta k := by
  rw [escKernel_inr, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),
    Measure.dirac_apply' _ (measurableSet_esc _), indicator_of_notMem (by simp), smul_eq_mul,
    smul_eq_mul, mul_one, mul_zero, add_zero]

/-- `P(inr k, {inl 0}) = 1 − βₖ > 0`. -/
theorem escKernel_inr_back (k : ℕ) : escKernel (Sum.inr k) {Sum.inl 0} = 1 - escBeta k := by
  rw [escKernel_inr, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),
    Measure.dirac_apply' _ (measurableSet_esc _), indicator_of_notMem (by simp), smul_eq_mul,
    smul_eq_mul, mul_one, mul_zero, zero_add]

/-- **Escape**: `Pⁿ(inr 0, {inr n}) ≥ aₙ ≥ ½`. -/
theorem escKernel_pow_escape (n : ℕ) : escA n ≤ (escKernel ^ n) (Sum.inr 0) {Sum.inr n} := by
  have := measurableSingletonClass_esc
  induction n with
  | zero =>
    rw [pow_zero_apply, Measure.dirac_apply_of_mem (mem_singleton _), escA, zero_add, pow_one,
      ENNReal.inv_two_add_inv_two]
  | succ n ih =>
    calc escA (n + 1) = escA n * escBeta n := (escA_mul_escBeta n).symm
      _ ≤ (escKernel ^ n) (Sum.inr 0) {Sum.inr n} * (escKernel ^ 1) (Sum.inr n)
          {Sum.inr (n + 1)} := by
          rw [pow_one, escKernel_inr_step]
          exact mul_le_mul_left ih _
      _ ≤ _ := pow_add_singleton_ge _ n 1 _ _ _

/-! ### Irreducibility, recurrence and the invariant measure -/

/-- From the renewal state `0` the forward recurrence time chain reaches every `j`. -/
theorem escQ_reach (j : ℕ) : ∃ m, 0 < (escQ ^ (m + 1)) 0 {j} := by
  have := isProbabilityMeasure_escP
  obtain ⟨n, hn, hpn⟩ := escP_supp (j + 1)
  refine ⟨n - 1 - j, ?_⟩
  rw [add_comm]
  refine lt_of_lt_of_le ?_ (pow_add_singleton_ge _ 1 (n - 1 - j) 0 (n - 1) j)
  rw [pow_one, fwdRec_zero_singleton escP_zero, show n - 1 + 1 = n by omega,
    fwdRec_pow_le (by omega), show n - 1 - (n - 1 - j) = j by omega,
    Measure.dirac_apply_of_mem (mem_singleton j), mul_one]
  exact hpn

/-- `inl⁻¹ {inl j} = {j}`. -/
theorem preimage_inl_singleton (j : ℕ) :
    ((Sum.inl : ℕ → ℕ ⊕ ℕ) ⁻¹' {Sum.inl j} : Set ℕ) = {j} := by
  ext i
  rw [mem_preimage, mem_singleton_iff, mem_singleton_iff, Sum.inl.injEq]

/-- `inl⁻¹ {inr k} = ∅`. -/
theorem preimage_inl_singleton_inr (k : ℕ) :
    ((Sum.inl : ℕ → ℕ ⊕ ℕ) ⁻¹' {Sum.inr k} : Set ℕ) = ∅ := by
  ext i
  rw [mem_preimage, mem_singleton_iff]
  exact iff_of_false Sum.inl_ne_inr (notMem_empty i)

/-- **Every state reaches the renewal part**: `Pⁿ⁺¹(x, {inl j}) > 0` for some `n`. -/
theorem escKernel_reach (x : ℕ ⊕ ℕ) (j : ℕ) : ∃ n, 0 < (escKernel ^ (n + 1)) x {Sum.inl j} := by
  have := measurableSingletonClass_esc
  obtain ⟨m, hm⟩ := escQ_reach j
  have h0 : 0 < (escKernel ^ (m + 1)) (Sum.inl 0) {Sum.inl j} := by
    rwa [escKernel_pow_inl, preimage_inl_singleton]
  rcases x with i | k
  · refine ⟨i + m, ?_⟩
    have h1 : (escKernel ^ i) (Sum.inl i) {Sum.inl 0} = 1 := by
      rw [escKernel_pow_inl, preimage_inl_singleton, fwdRec_pow_self,
        Measure.dirac_apply_of_mem (mem_singleton 0)]
    refine lt_of_lt_of_le ?_ (pow_add_singleton_ge _ i (m + 1) _ (Sum.inl 0) _)
    rwa [h1, one_mul]
  · refine ⟨m + 1, ?_⟩
    have h1 : 0 < (escKernel ^ 1) (Sum.inr k) {Sum.inl 0} := by
      rw [pow_one, escKernel_inr_back]
      exact tsub_pos_of_lt (escBeta_lt_one k)
    have h2 := pow_add_singleton_ge escKernel 1 (m + 1) (Sum.inr k) (Sum.inl 0) (Sum.inl j)
    rw [show 1 + (m + 1) = m + 1 + 1 by ring] at h2
    exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h0.ne') h2

/-- The counting measure on the renewal part. -/
noncomputable def escPsi : Measure (ℕ ⊕ ℕ) := Measure.count.map Sum.inl

/-- `ψ(A) = #(inl⁻¹ A)`. -/
theorem escPsi_apply (A : Set (ℕ ⊕ ℕ)) : escPsi A = Measure.count (Sum.inl ⁻¹' A) :=
  Measure.map_apply measurable_inl (measurableSet_esc A)

/-- **`ψ` is a maximal irreducibility measure.** -/
theorem escKernel_isMaximalIrreducibility :
    haveI := isMarkovKernel_escKernel; IsMaximalIrreducibility escKernel escPsi := by
  have := isMarkovKernel_escKernel
  have hne : ∀ A, 0 < escPsi A → ∃ j, Sum.inl j ∈ A := fun A hA => by
    rw [escPsi_apply, pos_iff_ne_zero, Ne, Measure.count_eq_zero_iff] at hA
    obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hA
    exact ⟨j, hj⟩
  refine ⟨fun h0 => ?_, fun A hA hψA x => ?_, fun φ hφ => ?_⟩
  · have h1 : escPsi {Sum.inl 0} = 1 := by
      rw [escPsi_apply, preimage_inl_singleton, Measure.count_singleton]
    rw [h0, Measure.coe_zero, Pi.zero_apply] at h1
    exact zero_ne_one h1
  · obtain ⟨j, hj⟩ := hne A hψA
    obtain ⟨n, hn⟩ := escKernel_reach x j
    exact (hitProb_pos_iff _ hA x).2 ⟨n, lt_of_lt_of_le hn (measure_mono
      (singleton_subset_iff.2 hj))⟩
  · refine Measure.AbsolutelyContinuous.mk fun A hA hψA => ?_
    by_contra h
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ hA (Sum.inl 0)).1
      (hφ A hA (pos_iff_ne_zero.2 h) (Sum.inl 0))
    rw [escPsi_apply, Measure.count_eq_zero_iff] at hψA
    rw [escKernel_pow_inl, hψA, measure_empty] at hn
    exact lt_irrefl 0 hn

/-- **The chain is recurrent**: `U(x, A) = ∞` for every `x` and `ψ(A) > 0`. From the renewal
part this is the recurrence of the forward recurrence time chain; from the escape path the
chain enters `inl 0` with positive probability. -/
theorem escKernel_isRecurrentChain :
    haveI := isMarkovKernel_escKernel; IsRecurrentChain escKernel escPsi := by
  have := isMarkovKernel_escKernel
  have := isProbabilityMeasure_escP
  have := measurableSingletonClass_esc
  have hQ := (fwdRec_isRecurrentChain escP_zero escP_supp).2
  refine ⟨escKernel_isMaximalIrreducibility, fun A hA hψA x => ?_⟩
  rw [escPsi_apply, pos_iff_ne_zero, Ne, Measure.count_eq_zero_iff] at hψA
  obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hψA
  have hinl : ∀ i, potKernel escKernel (Sum.inl i) {Sum.inl j} = ∞ := fun i => by
    rw [potKernel_apply _ _ (measurableSet_esc _)]
    simp_rw [escKernel_pow_inl, preimage_inl_singleton]
    rw [← potKernel_apply _ _ (measurableSet_singleton j)]
    exact hQ {j} (measurableSet_singleton j) (by rw [Measure.count_singleton]; exact one_pos) i
  refine top_unique ((?_ : ∞ ≤ potKernel escKernel x {Sum.inl j}).trans
    (measure_mono (singleton_subset_iff.2 hj)))
  rcases x with i | k
  · rw [hinl i]
  · have hb : 0 < 1 - escBeta k := tsub_pos_of_lt (escBeta_lt_one k)
    have h0 := hinl 0
    rw [potKernel_apply _ _ (measurableSet_esc _)] at h0 ⊢
    calc ∞ = (1 - escBeta k) * ∑' n, (escKernel ^ (n + 1)) (Sum.inl 0) {Sum.inl j} := by
          rw [h0, ENNReal.mul_top hb.ne']
      _ ≤ (1 - escBeta k) * ∑' n, (escKernel ^ n) (Sum.inl 0) {Sum.inl j} := by
          refine mul_le_mul' le_rfl ?_
          rw [tsum_eq_zero_add' ENNReal.summable
            (f := fun n => (escKernel ^ n) (Sum.inl 0) {Sum.inl j})]
          exact le_add_self
      _ = ∑' n, (escKernel ^ 1) (Sum.inr k) {Sum.inl 0} *
            (escKernel ^ n) (Sum.inl 0) {Sum.inl j} := by
          rw [pow_one, escKernel_inr_back, ENNReal.tsum_mul_left]
      _ ≤ ∑' n, (escKernel ^ (n + 1)) (Sum.inr k) {Sum.inl j} := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          rw [add_comm n 1]
          exact pow_add_singleton_ge _ 1 n _ _ _

/-- The invariant measure `π = Σⱼ p{n > j} δ_{inl j}` on the renewal part (10.16). -/
noncomputable def escPi : Measure (ℕ ⊕ ℕ) := (fwdRecInv escP).map Sum.inl

/-- `π(A) = π_Q(inl⁻¹ A)`. -/
theorem escPi_apply (A : Set (ℕ ⊕ ℕ)) : escPi A = fwdRecInv escP (Sum.inl ⁻¹' A) :=
  Measure.map_apply measurable_inl (measurableSet_esc A)

/-- `π` is invariant. -/
theorem isInvariant_escPi : IsInvariant escKernel escPi := by
  have := isProbabilityMeasure_escP
  unfold IsInvariant
  ext A hA
  have h1 : ∀ j, escKernel (Sum.inl j) A = escQ j (Sum.inl ⁻¹' A) := fun j => by
    have := escKernel_pow_inl 1 j A
    rwa [pow_one, pow_one] at this
  have hinv := isInvariant_fwdRecInv (p := escP) escP_zero
  unfold IsInvariant at hinv
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), escPi,
    lintegral_map (Kernel.measurable_coe _ hA) measurable_inl,
    Measure.map_apply measurable_inl hA]
  simp_rw [h1]
  conv_rhs => rw [← hinv]
  rw [Measure.bind_apply (measurableSet_of_countable _) (Kernel.aemeasurable _)]

/-- `π(X) = Σₙ n p(n) = ∞` (10.17). -/
theorem escPi_univ : escPi univ = ∞ := by
  rw [escPi_apply, preimage_univ, fwdRecInv_univ, escP_mean]

/-- `π ≠ 0`. -/
theorem escPi_ne_zero : escPi ≠ 0 := fun h => by
  have := escPi_univ
  rw [h, Measure.coe_zero, Pi.zero_apply] at this
  exact ENNReal.zero_ne_top this

/-- `π{inr k} = 0`: the escape path carries no invariant mass. -/
theorem escPi_inr (k : ℕ) : escPi {Sum.inr k} = 0 := by
  rw [escPi_apply, preimage_inl_singleton_inr, measure_empty]

/-- `π` is σ-finite. -/
theorem sigmaFinite_escPi : SigmaFinite escPi := by
  have := isProbabilityMeasure_escP
  refine Measure.sigmaFinite_of_countable (S := range fun x : ℕ ⊕ ℕ => ({x} : Set (ℕ ⊕ ℕ)))
    (countable_range _) ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rcases x with j | k
    · rw [escPi_apply, preimage_inl_singleton, fwdRecInv_singleton]
      exact measure_lt_top _ _
    · rw [escPi_inr]; exact ENNReal.zero_lt_top
  · exact sUnion_eq_univ_iff.2 fun x => ⟨{x}, ⟨x, rfl⟩, mem_singleton x⟩

/-- **The chain is null**: by the uniqueness of subinvariant measures of a recurrent chain
(Theorem 10.0.1), an invariant probability would be a finite multiple of `π`, whose total mass
is `∞`. -/
theorem escKernel_isNull : haveI := isMarkovKernel_escKernel; IsNull escKernel escPsi := by
  have := isMarkovKernel_escKernel
  refine ⟨escKernel_isMaximalIrreducibility, fun ⟨μ, hμp, hμinv⟩ => ?_⟩
  obtain ⟨ν₀, -, -, huniq, -⟩ := theorem_10_0_1 escKernel_isRecurrentChain
  obtain ⟨c, -, hμ⟩ := huniq μ ⟨inferInstance, hμinv.isSubinvariant⟩
  obtain ⟨c', hc', hπ⟩ := huniq escPi ⟨sigmaFinite_escPi, isInvariant_escPi.isSubinvariant⟩
  have h1 := escPi_univ
  rw [hπ, Measure.smul_apply, smul_eq_mul] at h1
  have h0 : ν₀ univ = ∞ := by
    rcases ENNReal.mul_eq_top.1 h1 with h | h
    · exact h.2
    · exact absurd h.1 hc'
  have h2 : μ univ = 1 := measure_univ
  rw [hμ, Measure.smul_apply, smul_eq_mul, h0] at h2
  by_cases hc : c = 0
  · rw [hc, zero_mul] at h2
    exact zero_ne_one h2
  · rw [ENNReal.mul_top hc] at h2
    exact ENNReal.top_ne_one h2

/-- **The chain is aperiodic**: `P(inl 0, ·) ≥ ½ δ_{inl 0}` with `ψ{inl 0} > 0`. -/
theorem escKernel_isAperiodic :
    haveI := isMarkovKernel_escKernel; IsAperiodic escKernel escPsi := by
  have := isMarkovKernel_escKernel
  have := measurableSingletonClass_esc
  let M : Minorization escKernel :=
    { C := {Sum.inl 0}
      δ := 2⁻¹
      ν := Measure.dirac (Sum.inl 0)
      measurableSet_C := measurableSet_esc _
      δ_pos := by norm_num
      δ_lt_one := ENNReal.inv_lt_one.2 (by norm_num)
      isProbabilityMeasure_ν := inferInstance
      le := fun x hx => by
        rw [mem_singleton_iff] at hx
        subst hx
        refine Measure.le_intro fun A hA _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
        by_cases h : Sum.inl 0 ∈ A
        · rw [indicator_of_mem h, Pi.one_apply, mul_one, ← escKernel_inl_zero]
          exact measure_mono (singleton_subset_iff.2 h)
        · rw [indicator_of_notMem h, mul_zero]
          exact zero_le }
  refine isAperiodic_of_minorization escKernel_isMaximalIrreducibility M ?_ ?_
  · change 0 < escPsi {Sum.inl 0}
    rw [escPsi_apply, preimage_inl_singleton, Measure.count_singleton]
    exact one_pos
  · change 0 < Measure.dirac (Sum.inl 0 : ℕ ⊕ ℕ) {Sum.inl 0}
    rw [Measure.dirac_apply_of_mem (mem_singleton _)]
    exact one_pos

/-- **(18.15) fails from the escape path**: from `inr 0`, `Pⁿ(inr 0, {inr n}) ≥ ½` while
`π{inr n} = 0`, so `sup_A Pⁿ(inr 0, A)/(π(A) + 1) ≥ ½` for all `n`. -/
theorem escKernel_not_tendsto :
    ¬ Tendsto (fun n => ⨆ (A : Set (ℕ ⊕ ℕ)) (_ : MeasurableSet A),
      ((escKernel ^ n : Kernel (ℕ ⊕ ℕ) (ℕ ⊕ ℕ)) ∘ₘ Measure.dirac (Sum.inr 0)) A / (escPi A + 1))
      atTop (𝓝 0) := by
  intro h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 2⁻¹ by norm_num))).exists
  refine (not_lt.2 ?_) hn
  calc (2⁻¹ : ℝ≥0∞) ≤ escA n := escA_ge n
    _ ≤ (escKernel ^ n) (Sum.inr 0) {Sum.inr n} := escKernel_pow_escape n
    _ = ((escKernel ^ n : Kernel (ℕ ⊕ ℕ) (ℕ ⊕ ℕ)) ∘ₘ Measure.dirac (Sum.inr 0)) {Sum.inr n} /
          (escPi {Sum.inr n} + 1) := by
        rw [Measure.dirac_bind (Kernel.measurable _), escPi_inr, zero_add, div_one]
    _ ≤ _ := le_iSup₂_of_le (f := fun (A : Set (ℕ ⊕ ℕ)) (_ : MeasurableSet A) =>
          ((escKernel ^ n : Kernel (ℕ ⊕ ℕ) (ℕ ⊕ ℕ)) ∘ₘ Measure.dirac (Sum.inr 0)) A /
            (escPi A + 1)) {Sum.inr n} (measurableSet_esc _) le_rfl

/-- **Theorem 18.1.3 needs the Harris property** (MT p. 468): `escKernel` on `ℕ ⊕ ℕ` is
recurrent, null and aperiodic, with the invariant measure `π ≠ 0`, but (18.15) fails for the
initial state `inr 0` and `ε = 1`. In particular it is not Harris, by `theorem_18_1_3`. -/
theorem theorem_18_1_3_counterexample :
    haveI := isMarkovKernel_escKernel
    IsRecurrentChain escKernel escPsi ∧ IsNull escKernel escPsi ∧
      IsAperiodic escKernel escPsi ∧ IsInvariant escKernel escPi ∧ escPi ≠ 0 ∧
      ¬ Tendsto (fun n => ⨆ (A : Set (ℕ ⊕ ℕ)) (_ : MeasurableSet A),
        ((escKernel ^ n : Kernel (ℕ ⊕ ℕ) (ℕ ⊕ ℕ)) ∘ₘ Measure.dirac (Sum.inr 0)) A /
          (escPi A + 1)) atTop (𝓝 0) ∧
      ¬ IsHarris escKernel escPsi := by
  have := isMarkovKernel_escKernel
  refine ⟨escKernel_isRecurrentChain, escKernel_isNull, escKernel_isAperiodic, isInvariant_escPi,
    escPi_ne_zero, escKernel_not_tendsto, fun hH => escKernel_not_tendsto ?_⟩
  exact theorem_18_1_3 hH escKernel_isNull escKernel_isAperiodic isInvariant_escPi escPi_ne_zero
    (Measure.dirac (Sum.inr 0)) one_pos

end MeynTweedie.Positivity
