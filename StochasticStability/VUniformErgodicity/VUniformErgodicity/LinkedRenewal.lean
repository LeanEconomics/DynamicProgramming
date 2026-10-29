/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.AtomErgodic
import VUniformErgodicity.CountableInvariant
import VUniformErgodicity.KendallTheorem

/-!
# The linked forward recurrence time chain and the variation of `u` (MT §13.2.1, §13.4.1)

Meyn and Tweedie, pp. 321 and 329–330. For an increment law `p` on `ℤ₊` the forward recurrence
time chain `V⁺ = fwdRecKernel p` of §10.3.1 has renewal state `0` and return-time law `p`, so its
renewal sequence at `0` is `u`; the linked chain `V* = V⁺ ∥ V⁺` (10.19) runs two independent
copies. The book uses `V*` to couple two renewal processes.

**The forward recurrence chain of a real increment law.**
* `lawMeasure p`: the law `Σₙ p(n) δₙ`; `isProbabilityMeasure_lawMeasure`, `lawMeasure_singleton`.
* `fwdRec_tabooKernel_zero`, `fwdRec_entryLaw`: the return time to `0` has law `p`;
  `fwdRec_atomRenewal`: `Pⁿ(0, 0) = u(n)`; `fwdRec_pow_apply_zero`: `Pⁿ(i, 0) = u(n − i)` for
  `i ≤ n`.

**The linked chain.**
* `linkedFwdRec_pow`, `linkedFwdRec_pow_apply`: `V*ⁿ = V⁺ⁿ ∥ V⁺ⁿ`, so the coordinates move
  independently.
* `eventually_realRenewalSeq_pos`: for an aperiodic law, `u(n) > 0` for all large `n`
  (Lemma D.7.4); hence `linked_isPhiIrreducible`: `V*` reaches `(0, 0)` from every state.
* `linkedInv_spec`: for finite mean `V*` is positive, with invariant probability
  `π* = m_p⁻² (π ⊗ π)` (p. 238).
* `tabooKernel_add_succ`, `mul_meanReturnTime_le`: the taboo kernels compose,
  `_αPⁿ⁺ᵏ⁺¹(x, ·) = ∫_{αᶜ} _αPᵏ⁺¹(x, dy) _αPⁿ⁺¹(y, ·)`, so
  `_αPᵏ⁺¹(x, {y}) E_y[τ_α] ≤ E_x[τ_α]` for `y ∉ α` (as in Proposition 11.1.1).
* `linked_meanReturnTime_ne_top`: `E_{(0,1)}[τ_{(0,0)}] < ∞` (13.68).

**Results.**
* `abs_sub_realRenewalSeq_le` (the coupling bound (13.33) for `a = δ₀`, `b = δ₁`):
  `|u(n + 1) − u(n)| ≤ P_{(0,1)}(τ_{(0,0)} ≥ n + 1)`, from the first-entrance decomposition of
  `V*` at the atom `(0, 0)` and the symmetry of `V*`.
* **(13.69)** (`summable_seqDiff_realRenewalSeq`, p. 330): for an aperiodic increment law with
  finite mean, `Var(u) = Σₙ |u(n) − u(n − 1)| < ∞`.

**Corrections.** None.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

/-! ### The forward recurrence chain of a real increment law -/

/-- The law `Σₙ p(n) δₙ` on `ℕ` of a real sequence `p ≥ 0`. -/
noncomputable def lawMeasure (p : ℕ → ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (p n) • Measure.dirac n

/-- `p{n} = p(n)`. -/
theorem lawMeasure_singleton (p : ℕ → ℝ) (n : ℕ) : lawMeasure p {n} = ENNReal.ofReal (p n) :=
  Measure.sum_smul_dirac_singleton

/-- The law of an increment law is a probability. -/
theorem isProbabilityMeasure_lawMeasure {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    IsProbabilityMeasure (lawMeasure p) := by
  refine ⟨?_⟩
  rw [measure_univ_eq_tsum_singleton]
  simp_rw [lawMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg hp.nonneg hp.hasSum.summable, hp.hasSum.tsum_eq,
    ENNReal.ofReal_one]

/-- `p{0} = 0`. -/
theorem lawMeasure_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) : lawMeasure p {0} = 0 := by
  rw [lawMeasure_singleton, hp.zero, ENNReal.ofReal_zero]

/-- From `i ≥ 1` the forward recurrence chain first hits `0` at time `i`. -/
theorem fwdRec_tabooKernel_pos (q : Measure ℕ) [IsProbabilityMeasure q] (k : ℕ) :
    ∀ i, i ≠ 0 → tabooKernel (fwdRecKernel q) (measurableSet_singleton 0) k i {0} =
      if k + 1 = i then 1 else 0 := by
  have := isMarkovKernel_fwdRecKernel q
  induction k with
  | zero =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [tabooKernel_zero, fwdRec_succ, Measure.dirac_apply' _ (measurableSet_singleton 0)]
    by_cases hj : j = 0 <;> simp [hj]
  | succ k ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [tabooKernel_succ_apply _ _ k _ (measurableSet_singleton 0), fwdRec_succ,
      ← lintegral_indicator (measurableSet_singleton 0).compl, lintegral_dirac]
    by_cases hj : j = 0
    · subst hj
      rw [indicator_of_notMem (by simp)]
      simp
    · rw [indicator_of_mem (by simpa using hj), ih j hj]
      by_cases h : k + 1 = j <;> simp [h]

/-- The return time to `0` has law `p`: `_0Pᵏ⁺¹(0, {0}) = p(k + 1)`. -/
theorem fwdRec_tabooKernel_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) (k : ℕ) :
    haveI := isProbabilityMeasure_lawMeasure hp
    tabooKernel (fwdRecKernel (lawMeasure p)) (measurableSet_singleton 0) k 0 {0} =
      ENNReal.ofReal (p (k + 1)) := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  have hp0 := lawMeasure_zero hp
  rcases k with _ | k
  · rw [tabooKernel_zero, fwdRec_zero_singleton hp0, lawMeasure_singleton]
  · rw [tabooKernel_succ_apply _ _ k _ (measurableSet_singleton 0),
      ← lintegral_indicator (measurableSet_singleton 0).compl, lintegral_countable']
    rw [tsum_eq_single (k + 1) fun j hj => ?_]
    · rw [indicator_of_mem (by simp), fwdRec_tabooKernel_pos _ k (k + 1) (by omega)]
      simp [fwdRec_zero_singleton hp0, lawMeasure_singleton]
    · by_cases hj0 : j = 0
      · subst hj0; rw [indicator_of_notMem (by simp), zero_mul]
      · rw [indicator_of_mem (by simpa using hj0), fwdRec_tabooKernel_pos _ k j hj0]
        have : k + 1 ≠ j := fun h => hj h.symm
        simp [this]

/-- The return-time law of the renewal state `0` is `p`. -/
theorem fwdRec_entryLaw {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    haveI := isProbabilityMeasure_lawMeasure hp
    entryLaw (fwdRecKernel (lawMeasure p)) (measurableSet_singleton 0) (Measure.dirac 0) = p := by
  have := isProbabilityMeasure_lawMeasure hp
  funext n
  rcases n with _ | k
  · rw [entryLaw_zero, hp.zero]
  · rw [entryLaw_dirac_succ, fwdRec_tabooKernel_zero hp, ENNReal.toReal_ofReal (hp.nonneg _)]

/-- `Pⁿ(0, {0}) = u(n)`, the renewal sequence of `p`. -/
theorem fwdRec_atomRenewal {p : ℕ → ℝ} (hp : IsIncrementLaw p) :
    haveI := isProbabilityMeasure_lawMeasure hp
    atomRenewal (fwdRecKernel (lawMeasure p)) {0} 0 = realRenewalSeq p := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  rw [atomRenewal_eq_realRenewalSeq (isAtom_singleton _ 0) (mem_singleton 0), fwdRec_entryLaw hp]

/-- `Pⁿ(i, {0}) = u(n − i)` for `i ≤ n`. -/
theorem fwdRec_pow_apply_zero {p : ℕ → ℝ} (hp : IsIncrementLaw p) {i n : ℕ} (hin : i ≤ n) :
    (fwdRecKernel (lawMeasure p) ^ n : Kernel ℕ ℕ) i {0} =
      ENNReal.ofReal (realRenewalSeq p (n - i)) := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  rw [fwdRec_pow_ge hin, ← fwdRec_atomRenewal hp, atomRenewal, ENNReal.ofReal_toReal]
  have := isMarkovKernel_pow (fwdRecKernel (lawMeasure p)) (n - i)
  exact measure_ne_top _ _

/-! ### The linked chain -/

/-- `V*ⁿ = V⁺ⁿ ∥ V⁺ⁿ`. -/
theorem linkedFwdRec_pow (q : Measure ℕ) [IsProbabilityMeasure q] (n : ℕ) :
    (linkedFwdRec q ^ n : Kernel (ℕ × ℕ) (ℕ × ℕ)) =
      Kernel.parallelComp (fwdRecKernel q ^ n) (fwdRecKernel q ^ n) := by
  have := isMarkovKernel_fwdRecKernel q
  induction n with
  | zero =>
    ext z s hs
    change (Kernel.id : Kernel (ℕ × ℕ) (ℕ × ℕ)) z s =
      Kernel.parallelComp (Kernel.id : Kernel ℕ ℕ) (Kernel.id : Kernel ℕ ℕ) z s
    rw [Kernel.parallelComp_apply, Kernel.id_apply, Kernel.id_apply, Kernel.id_apply,
      Measure.dirac_prod_dirac]
  | succ n ih =>
    have := isMarkovKernel_pow (fwdRecKernel q) n
    rw [pow_succ, ih, pow_succ]
    exact Kernel.parallelComp_comp_parallelComp

/-- `V*ⁿ((i, j), ·) = V⁺ⁿ(i, ·) ⊗ V⁺ⁿ(j, ·)`. -/
theorem linkedFwdRec_pow_apply (q : Measure ℕ) [IsProbabilityMeasure q] (n : ℕ) (z : ℕ × ℕ) :
    (linkedFwdRec q ^ n : Kernel (ℕ × ℕ) (ℕ × ℕ)) z =
      ((fwdRecKernel q ^ n : Kernel ℕ ℕ) z.1).prod ((fwdRecKernel q ^ n : Kernel ℕ ℕ) z.2) := by
  have := isMarkovKernel_fwdRecKernel q
  have := isMarkovKernel_pow (fwdRecKernel q) n
  rw [linkedFwdRec_pow, Kernel.parallelComp_apply]

/-- The linked chain is a transition kernel. -/
theorem isMarkovKernel_linkedFwdRec (q : Measure ℕ) [IsProbabilityMeasure q] :
    IsMarkovKernel (linkedFwdRec q) := by
  have := isMarkovKernel_fwdRecKernel q
  unfold linkedFwdRec
  infer_instance

/-- `u(m + n) ≥ u(m) u(n)`. -/
theorem realRenewalSeq_add_ge {p : ℕ → ℝ} (hp : IsIncrementLaw p) (m n : ℕ) :
    realRenewalSeq p m * realRenewalSeq p n ≤ realRenewalSeq p (m + n) := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  set V := fwdRecKernel (lawMeasure p)
  have h := pow_add_ge_of_le V (m := m) (n := n) (C := {0}) (ν := (V ^ n : Kernel ℕ ℕ) 0)
    (fun y hy => by rw [mem_singleton_iff.1 hy]) 0 (measurableSet_singleton 0)
  rw [← fwdRec_atomRenewal hp]
  unfold atomRenewal
  rw [← ENNReal.toReal_mul]
  have := isMarkovKernel_pow V (m + n)
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

/-- `u(n) ≥ p(n)`. -/
theorem le_realRenewalSeq {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    p n ≤ realRenewalSeq p n := by
  rcases n with _ | n
  · rw [hp.zero, realRenewalSeq_zero hp.zero]; exact zero_le_one
  · rw [realRenewalSeq_succ hp.zero, Finset.sum_range_succ, Nat.sub_self,
      realRenewalSeq_zero hp.zero, mul_one]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ =>
      mul_nonneg (hp.nonneg _) (realRenewalSeq_nonneg hp _))

/-- For an aperiodic increment law, `u(n) > 0` for all large `n` (Lemma D.7.4). -/
theorem eventually_realRenewalSeq_pos {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) : ∃ N, ∀ n ≥ N, 0 < realRenewalSeq p n := by
  obtain ⟨j, hj0, hj⟩ := exists_pos_incr hp
  set S := {n | 0 < realRenewalSeq p n}
  have hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := fun a ha b hb =>
    lt_of_lt_of_le (mul_pos ha hb) (realRenewalSeq_add_ge hp a b)
  have hjS : j ∈ S := lt_of_lt_of_le hj (le_realRenewalSeq hp j)
  exact natAddClosed_eventually_mem hS hjS hj0 fun d hd =>
    hap d fun n hn => hd n (lt_of_lt_of_le hn (le_realRenewalSeq hp n))

/-! ### Composition of taboo kernels -/

variable {X : Type*} [MeasurableSpace X]

/-- `E_x[τ_A] = Σₙ _APⁿ⁺¹(x, X)`. -/
theorem meanReturnTime_eq_tsum (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    meanReturnTime P A x = ∑' n, tabooKernel P hA n x univ := by
  rw [meanReturnTime_eq_tabooPotKernel P hA, tabooPotKernel, Kernel.sum_apply,
    Measure.sum_apply _ MeasurableSet.univ]

/-- The taboo kernels compose: `_APⁿ⁺ᵏ⁺²(x, ·) = ∫_{Aᶜ} _APᵏ⁺¹(x, dy) _APⁿ⁺¹(y, ·)`. -/
theorem tabooKernel_add_succ (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (k : ℕ) : ∀ n (x : X),
    tabooKernel P hA (n + (k + 1)) x =
      tabooKernel P hA n ∘ₘ (tabooKernel P hA k x).restrict Aᶜ := by
  induction k with
  | zero =>
    intro n x
    rw [zero_add, tabooKernel_succ_eq', Kernel.comp_apply, tabooKernel_zero,
      ← comp_indKernel_eq_restrict]
  | succ k ih =>
    intro n x
    have h1 : tabooKernel P hA (k + 1) x = P ∘ₘ (tabooKernel P hA k x).restrict Aᶜ := by
      have := tabooSeq_succ P hA (Measure.dirac x) k
      rwa [tabooSeq, tabooSeq, dirac_kernel, dirac_kernel] at this
    rw [show n + (k + 1 + 1) = (n + 1) + (k + 1) by ring, ih (n + 1) x, tabooKernel_succ_eq',
      ← Measure.comp_assoc]
    congr 1
    rw [← Measure.comp_assoc, indKernel_comp_eq_restrict, ← h1]

/-- For `y ∉ A`, `_APᵏ⁺¹(x, {y}) E_y[τ_A] ≤ E_x[τ_A]`. -/
theorem mul_meanReturnTime_le [MeasurableSingletonClass X] (P : Kernel X X) [IsMarkovKernel P]
    {A : Set X} (hA : MeasurableSet A) (k : ℕ) (x : X) {y : X} (hy : y ∉ A) :
    tabooKernel P hA k x {y} * meanReturnTime P A y ≤ meanReturnTime P A x := by
  have hmeas : ∀ n, Measurable fun w => tabooKernel P hA n w univ := fun n =>
    Kernel.measurable_coe _ MeasurableSet.univ
  calc tabooKernel P hA k x {y} * meanReturnTime P A y
      = ∫⁻ w in {y}, meanReturnTime P A w ∂tabooKernel P hA k x := by
        rw [lintegral_singleton, mul_comm]
    _ ≤ ∫⁻ w in Aᶜ, meanReturnTime P A w ∂tabooKernel P hA k x :=
        lintegral_mono_set (singleton_subset_iff.2 hy)
    _ = ∑' n, tabooKernel P hA (n + (k + 1)) x univ := by
        simp_rw [meanReturnTime_eq_tsum P hA]
        rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
        refine tsum_congr fun n => ?_
        rw [tabooKernel_add_succ P hA k n x, measure_kernel_apply _ _ MeasurableSet.univ]
    _ ≤ ∑' n, tabooKernel P hA n x univ :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => n + (k + 1))
          (add_left_injective _) (fun n => tabooKernel P hA n x univ)
    _ = meanReturnTime P A x := (meanReturnTime_eq_tsum P hA x).symm

/-! ### Irreducibility and positivity of the linked chain -/

/-- `V*ⁿ(z, {(0, 0)}) = V⁺ⁿ(z₁, {0}) V⁺ⁿ(z₂, {0})`. -/
theorem linkedFwdRec_pow_atom (q : Measure ℕ) [IsProbabilityMeasure q] (n : ℕ) (z : ℕ × ℕ) :
    (linkedFwdRec q ^ n : Kernel (ℕ × ℕ) (ℕ × ℕ)) z {((0 : ℕ), (0 : ℕ))} =
      (fwdRecKernel q ^ n : Kernel ℕ ℕ) z.1 {0} * (fwdRecKernel q ^ n : Kernel ℕ ℕ) z.2 {0} := by
  rw [linkedFwdRec_pow_apply, ← singleton_prod_singleton, Measure.prod_prod]

/-- For an aperiodic increment law, the linked chain reaches `(0, 0)` from every state. -/
theorem linked_isPhiIrreducible {p : ℕ → ℝ} (hp : IsIncrementLaw p) (hap : IsAperiodicLaw p) :
    haveI := isProbabilityMeasure_lawMeasure hp
    haveI := isMarkovKernel_linkedFwdRec (lawMeasure p)
    IsPhiIrreducible (linkedFwdRec (lawMeasure p)) (Measure.dirac ((0 : ℕ), (0 : ℕ))) := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  obtain ⟨N, hN⟩ := eventually_realRenewalSeq_pos hp hap
  intro A hA hpos z
  have h0 : ((0 : ℕ), (0 : ℕ)) ∈ A := by
    by_contra h
    rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hpos
    exact lt_irrefl 0 hpos
  refine (hitProb_pos_iff _ hA z).2 ⟨z.1 + z.2 + N, ?_⟩
  refine lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2 h0))
  rw [linkedFwdRec_pow_atom, fwdRec_pow_apply_zero hp (by omega),
    fwdRec_pow_apply_zero hp (by omega)]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (hN _ (by omega))).ne'
    (ENNReal.ofReal_pos.2 (hN _ (by omega))).ne'

/-- The mean of the law: `∫ n dp = m_p`. -/
theorem lintegral_lawMeasure {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    ∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p = ENNReal.ofReal (incrMean p) := by
  rw [lintegral_countable', incrMean,
    ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n) (hp.nonneg n)) hm]
  refine tsum_congr fun n => ?_
  rw [lawMeasure_singleton, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- The invariant probability `π* = m_p⁻² (π ⊗ π)` of the linked chain (p. 238). -/
noncomputable def linkedInv (p : ℕ → ℝ) : Measure (ℕ × ℕ) :=
  ((∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p) ^ 2)⁻¹ •
    (fwdRecInv (lawMeasure p)).prod (fwdRecInv (lawMeasure p))

/-- `π*` is an invariant probability for `V*` when `m_p < ∞`. -/
theorem linkedInv_spec {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    IsProbabilityMeasure (linkedInv p) ∧
      IsInvariant (linkedFwdRec (lawMeasure p)) (linkedInv p) := by
  have := isProbabilityMeasure_lawMeasure hp
  have hmean := lintegral_lawMeasure hp hm
  have h1 : 1 ≤ incrMean p := one_le_incrMean hp hm
  have hne0 : (∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p) ^ 2 ≠ 0 := by
    rw [hmean]; exact pow_ne_zero _ (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hnet : (∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p) ^ 2 ≠ ∞ := by
    rw [hmean]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨⟨?_⟩, ?_⟩
  · rw [linkedInv, Measure.smul_apply, linkedFwdRec_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hne0 hnet]
  · unfold IsInvariant linkedInv
    rw [Measure.comp_smul, isInvariant_linkedFwdRec (lawMeasure_zero hp)]

/-- `π*{(0, 1)} > 0` when `p` charges some `n ≥ 2`. -/
theorem linkedInv_zero_one_pos {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hm : Summable fun n : ℕ => (n : ℝ) * p n) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hpn : 0 < p n₀) :
    0 < linkedInv p {((0 : ℕ), (1 : ℕ))} := by
  have := isProbabilityMeasure_lawMeasure hp
  have hmean := lintegral_lawMeasure hp hm
  have hnet : (∫⁻ n, (n : ℝ≥0∞) ∂lawMeasure p) ^ 2 ≠ ∞ := by
    rw [hmean]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [linkedInv, Measure.smul_apply, ← singleton_prod_singleton, Measure.prod_prod,
    fwdRecInv_singleton, fwdRecInv_singleton, smul_eq_mul]
  have hA : 0 < lawMeasure p {n | 0 < n} := lt_of_lt_of_le
    (by rw [lawMeasure_singleton]; exact ENNReal.ofReal_pos.2 hpn)
    (measure_mono (singleton_subset_iff.2 (show 0 < n₀ by omega)))
  have hB : 0 < lawMeasure p {n | 1 < n} := lt_of_lt_of_le
    (by rw [lawMeasure_singleton]; exact ENNReal.ofReal_pos.2 hpn)
    (measure_mono (singleton_subset_iff.2 (show 1 < n₀ by omega)))
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hnet) (ENNReal.mul_pos hA.ne' hB.ne').ne'

/-- **(13.68)**: `E_{(0,1)}[τ_{(0,0)}] < ∞` for an aperiodic law of finite mean charging some
`n ≥ 2`. -/
theorem linked_meanReturnTime_ne_top {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (hm : Summable fun n : ℕ => (n : ℝ) * p n) {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hpn : 0 < p n₀) :
    haveI := isProbabilityMeasure_lawMeasure hp
    haveI := isMarkovKernel_linkedFwdRec (lawMeasure p)
    meanReturnTime (linkedFwdRec (lawMeasure p)) {((0 : ℕ), (0 : ℕ))} ((0 : ℕ), (1 : ℕ)) ≠ ∞ := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  set W := linkedFwdRec (lawMeasure p)
  set α : Set (ℕ × ℕ) := {((0 : ℕ), (0 : ℕ))}
  have hφ := linked_isPhiIrreducible hp hap
  have hφ0 : Measure.dirac ((0 : ℕ), (0 : ℕ)) ≠ 0 := by simp
  set ψ := maxIrrMeasure W (Measure.dirac ((0 : ℕ), (0 : ℕ)))
  have hψ := isMaximalIrreducibility_maxIrrMeasure W hφ hφ0
  have hψα : 0 < ψ α := by
    by_contra h0
    have := (hψ.2.2 _ hφ) (nonpos_iff_eq_zero.1 (not_lt.1 h0))
    simp [α] at this
  have hacc : IsAccessibleAtom W ψ α := ⟨isAtom_singleton W _, hψ, hψα⟩
  obtain ⟨hπp, hπi⟩ := linkedInv_spec hp hm
  have hpos : IsPositive W ψ := ⟨hψ, linkedInv p, hπp, hπi⟩
  have hrep := eq_smul_atomMeasure_of_accessible hacc (proposition_10_1_1 hpos)
    (mem_singleton _) hπi
  have hEa := meanReturnTime_ne_top_of_rep W hacc.1.1 _ hrep
  have h01 := linkedInv_zero_one_pos hp hm hn₀ hpn
  have hμ : atomMeasure W hacc.1.1 ((0 : ℕ), (0 : ℕ)) {((0 : ℕ), (1 : ℕ))} ≠ 0 := by
    intro h0
    rw [hrep, Measure.smul_apply, h0, smul_zero] at h01
    exact lt_irrefl 0 h01
  rw [atomMeasure, tabooPotKernel, Kernel.sum_apply, Measure.sum_apply _
    (measurableSet_singleton _)] at hμ
  obtain ⟨k, hk⟩ : ∃ k, tabooKernel W hacc.1.1 k ((0 : ℕ), (0 : ℕ)) {((0 : ℕ), (1 : ℕ))} ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (ENNReal.tsum_eq_zero.2 h)
  have hy : ((0 : ℕ), (1 : ℕ)) ∉ α := by simp [α]
  have hle := mul_meanReturnTime_le W hacc.1.1 k ((0 : ℕ), (0 : ℕ)) hy
  intro htop
  rw [htop, ENNReal.mul_top hk] at hle
  exact hEa (top_unique hle)

/-! ### The coupling bound and the variation of `u` -/

/-- **The coupling bound** (13.33) with `a = δ₀`, `b = δ₁`:
`|u(n + 1) − u(n)| ≤ P_{(0,1)}(τ_{(0,0)} ≥ n + 1)`. -/
theorem abs_sub_realRenewalSeq_le {p : ℕ → ℝ} (hp : IsIncrementLaw p) (n : ℕ) :
    haveI := isProbabilityMeasure_lawMeasure hp
    |realRenewalSeq p (n + 1) - realRenewalSeq p n| ≤
      (tabooKernel (linkedFwdRec (lawMeasure p)) (measurableSet_singleton ((0 : ℕ), (0 : ℕ))) n
        ((0 : ℕ), (1 : ℕ)) Set.univ).toReal := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  have := isMarkovKernel_fwdRecKernel (lawMeasure p)
  have hα := isAtom_singleton (linkedFwdRec (lawMeasure p)) ((0 : ℕ), (0 : ℕ))
  have hFE := hα.pow_succ_firstEntrance (mem_singleton _) n ((0 : ℕ), (1 : ℕ))
  have hVm : ∀ m (i : ℕ), (fwdRecKernel (lawMeasure p) ^ m : Kernel ℕ ℕ) i Set.univ = 1 :=
    fun m i => by
      have := isMarkovKernel_pow (fwdRecKernel (lawMeasure p)) m; exact measure_univ
  set T := tabooKernel (linkedFwdRec (lawMeasure p)) hα.1 n ((0 : ℕ), (1 : ℕ)) with hTdef
  set S := ∑ j ∈ range n, tabooKernel (linkedFwdRec (lawMeasure p)) hα.1 j ((0 : ℕ), (1 : ℕ))
    {((0 : ℕ), (0 : ℕ))} * (fwdRecKernel (lawMeasure p) ^ (n - j) : Kernel ℕ ℕ) 0 {0} with hSdef
  have h1 : ENNReal.ofReal (realRenewalSeq p (n + 1)) = T ({0} ×ˢ Set.univ) + S := by
    have := congrArg (fun m : Measure (ℕ × ℕ) => m ({0} ×ˢ Set.univ)) hFE
    simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      linkedFwdRec_pow_apply, Measure.prod_prod, hVm, mul_one] at this
    rw [← this, fwdRec_pow_apply_zero hp (Nat.zero_le _), Nat.sub_zero]
  have h2 : ENNReal.ofReal (realRenewalSeq p n) = T (Set.univ ×ˢ {0}) + S := by
    have := congrArg (fun m : Measure (ℕ × ℕ) => m (Set.univ ×ˢ {0})) hFE
    simp only [Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      linkedFwdRec_pow_apply, Measure.prod_prod, hVm, one_mul] at this
    rw [← this, fwdRec_pow_apply_zero hp (by omega), Nat.add_sub_cancel]
  have hT : ∀ s, T s ≠ ∞ := fun s =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one _ hα.1 n _ s)
  have hS : S ≠ ∞ := ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top (tabooKernel_apply_le_one _ hα.1 j _ _))
    (by have := isMarkovKernel_pow (fwdRecKernel (lawMeasure p)) (n - j); exact measure_ne_top _ _)
  have e1 := congrArg ENNReal.toReal h1
  have e2 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_ofReal (realRenewalSeq_nonneg hp _), ENNReal.toReal_add (hT _) hS] at e1 e2
  rw [e1, e2, add_sub_add_right_eq_sub]
  have hle1 : (T ({0} ×ˢ Set.univ)).toReal ≤ (T Set.univ).toReal :=
    ENNReal.toReal_mono (hT _) (measure_mono (subset_univ _))
  have hle2 : (T (Set.univ ×ˢ {0})).toReal ≤ (T Set.univ).toReal :=
    ENNReal.toReal_mono (hT _) (measure_mono (subset_univ _))
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := T ({0} ×ˢ Set.univ)),
    ENNReal.toReal_nonneg (a := T (Set.univ ×ˢ {0}))]

/-- **(13.69)**, MT p. 330: for an aperiodic increment law with finite mean,
`Var(u) = Σₙ |u(n) − u(n − 1)| < ∞`. -/
theorem summable_seqDiff_realRenewalSeq {p : ℕ → ℝ} (hp : IsIncrementLaw p)
    (hap : IsAperiodicLaw p) (hm : Summable fun n : ℕ => (n : ℝ) * p n) :
    Summable fun n => |seqDiff (realRenewalSeq p) n| := by
  have := isProbabilityMeasure_lawMeasure hp
  have := isMarkovKernel_linkedFwdRec (lawMeasure p)
  by_cases h2 : ∃ n₀, 2 ≤ n₀ ∧ 0 < p n₀
  · obtain ⟨n₀, hn₀, hpn⟩ := h2
    have hE := linked_meanReturnTime_ne_top hp hap hm hn₀ hpn
    have hs := (hasSum_tabooKernel_univ _ (measurableSet_singleton _) _ hE).summable
    refine (summable_nat_add_iff 1).1 ?_
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_) hs
    rw [seqDiff_succ]
    exact abs_sub_realRenewalSeq_le hp n
  · push Not at h2
    have hpz : ∀ n, 2 ≤ n → p n = 0 := fun n hn => le_antisymm (h2 n hn) (hp.nonneg n)
    have hp1 : p 1 = 1 := by
      have h := hp.hasSum.tsum_eq
      rw [tsum_eq_single 1 fun n hn => by
        rcases n with _ | _ | n
        · exact hp.zero
        · exact absurd rfl hn
        · exact hpz _ (by omega)] at h
      exact h
    have hu : ∀ n, realRenewalSeq p n = 1 := fun n => by
      induction n with
      | zero => exact realRenewalSeq_zero hp.zero
      | succ n ih =>
        rw [realRenewalSeq_succ hp.zero, Finset.sum_eq_single 0 (fun j _ hj => by
          rw [hpz (j + 1) (by omega), zero_mul]) (by simp), zero_add, hp1, one_mul,
          Nat.sub_zero, ih]
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rcases n with _ | n
    · simp at hn
    · rw [seqDiff_succ, hu, hu, sub_self, abs_zero]

end MeynTweedie.VUniformErgodicity
