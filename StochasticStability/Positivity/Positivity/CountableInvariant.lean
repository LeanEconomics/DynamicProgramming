/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.PositiveNull
import Positivity.CountableClassification
import Positivity.ForwardRecurrence

/-!
# Invariant measures for countable space models (MT §10.3)

Meyn and Tweedie, §10.3, pp. 236–241. The forward recurrence time chain `fwdRecKernel p` of
`ForwardRecurrence` lives on `ℤ₊ = {0, 1, …}` and its renewal state is `0` (the book's state
`1`): from `0` it jumps to `n − 1` with probability `p(n)`, from `j ≥ 1` it moves to `j − 1`.

**Forward recurrence time chains** (§10.3.1).
* `fwdRecInv p`, `fwdRecInv_singleton`: the measure `π(j) = Σ_{n > j} p(n)` (10.16), and
  `isInvariant_fwdRecInv`: it is invariant (when `p(0) = 0`); `fwdRecInv_univ` (10.17):
  `π(ℤ₊) = Σₙ n p(n)`, the mean of `p`; `sigmaFinite_fwdRecInv`.
* `fwdRec_isIrreducibleChain`: the chain is irreducible when `p` has unbounded support;
  `fwdRec_isRecurrentChain`: it is then recurrent; `fwdRecInv_eq_atomMeasure`: (10.16),
  `π = U₀(0, ·)` is the minimal invariant measure `μ°_{0}` of Theorem 10.2.1;
  `fwdRec_isPositive_iff`: the chain is positive iff `p` has finite mean (10.17).
* Linked forward recurrence time chains: `isInvariant_parallelComp`, the product `π ⊗ σ` of
  invariant measures of two chains is invariant for the chain moving the two coordinates
  independently (`P ∥ₖ Q`); `isInvariant_linkedFwdRec`: for `V* = V⁺ ∥ V⁺` the measure
  `π*(i, j) = π(i)π(j)` is invariant, and `linkedFwdRec_univ`: `π*(X*) = [π(ℤ₊)]²`.

**The counterexample to Theorem 10.0.1 with `C = ∅`.**
* `heavyRenewal`: the renewal law `p(2ᵏ⁺¹) = 2^{−(k+1)}`, with infinite mean;
  `theorem_10_0_1_counterexample`: its forward recurrence time chain is recurrent and has an
  infinite invariant measure (it is null), although `∅` is petite and
  `sup_{x ∈ ∅} E_x[τ_∅] = 0`.

**Hypotheses.** The book states the results for a renewal distribution `p` on `{1, 2, …}`;
here `p` is a probability on `ℤ₊` with `p(0) = 0`. Irreducibility (unbounded support) is
assumed where the general theory (Theorems 10.2.1, 10.2.2) is used. The aperiodicity remarks
(10.18) and the positive Harris property of `V*` (which needs the `ψ`-irreducibility of `V*`,
proved in Part III) are not formalised here.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### Countable spaces -/

/-- A measure on `ℕ` that is finite on points is σ-finite. -/
theorem sigmaFinite_of_singleton_ne_top {μ : Measure ℕ} (h : ∀ j, μ {j} ≠ ∞) : SigmaFinite μ :=
  ⟨⟨{ set := fun j => {j}
      set_mem := fun _ => trivial
      finite := fun j => (h j).lt_top
      spanning := eq_univ_of_forall fun j => mem_iUnion.2 ⟨j, mem_singleton j⟩ }⟩⟩

/-- `Σ_j 1{j < n} = n`. -/
theorem tsum_indicator_Iio (n : ℕ) : ∑' j : ℕ, (Iio n).indicator (1 : ℕ → ℝ≥0∞) j = n := by
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj => by
    simp only [Finset.mem_range, not_lt] at hj
    exact indicator_of_notMem (by simpa using hj) _)]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) (fun j hj => by
    simp only [Finset.mem_range] at hj
    exact indicator_of_mem (by simpa using hj) _)]
  simp

/-! ### The forward recurrence time chain -/

/-- The invariant measure `π(j) = Σ_{n > j} p(n)` of the forward recurrence time chain (10.16). -/
noncomputable def fwdRecInv (p : Measure ℕ) : Measure ℕ :=
  Measure.sum fun j => p {n | j < n} • Measure.dirac j

/-- `π(j) = p{n > j}`. -/
theorem fwdRecInv_singleton (p : Measure ℕ) (k : ℕ) : fwdRecInv p {k} = p {n | k < n} := by
  rw [fwdRecInv, Measure.sum_apply _ (measurableSet_singleton k),
    tsum_eq_single k (fun j hj => by simp [hj])]
  simp

/-- `π` is σ-finite when `p` is finite. -/
theorem sigmaFinite_fwdRecInv (p : Measure ℕ) [IsFiniteMeasure p] : SigmaFinite (fwdRecInv p) :=
  sigmaFinite_of_singleton_ne_top fun j => by rw [fwdRecInv_singleton]; exact measure_ne_top _ _

/-- (10.17): `π(ℤ₊) = Σₙ n p(n)`, the mean of the renewal law. -/
theorem fwdRecInv_univ (p : Measure ℕ) : fwdRecInv p univ = ∫⁻ n, (n : ℝ≥0∞) ∂p := by
  have h1 : fwdRecInv p univ = ∑' j : ℕ, p {n | j < n} := by
    rw [fwdRecInv, Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [h1]
  simp_rw [← tsum_indicator_Iio]
  rw [lintegral_tsum fun j => (measurable_of_countable _).aemeasurable]
  refine tsum_congr fun j => ?_
  rw [← lintegral_indicator_one (measurableSet_of_countable {n : ℕ | j < n})]
  refine lintegral_congr fun n => ?_
  by_cases h : j < n
  · rw [indicator_of_mem (s := {n : ℕ | j < n}) h, indicator_of_mem (s := Iio n) h]
    rfl
  · rw [indicator_of_notMem (s := {n : ℕ | j < n}) h, indicator_of_notMem (s := Iio n) h]

/-- `P(0, {k}) = p(k + 1)` when `p(0) = 0`. -/
theorem fwdRec_zero_singleton {p : Measure ℕ} (hp0 : p {0} = 0) (k : ℕ) :
    fwdRecKernel p 0 {k} = p {k + 1} := by
  change fwdRecMeas p 0 {k} = _
  simp only [fwdRecMeas, ite_true]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k)]
  refine le_antisymm ?_ (measure_mono fun n hn => by simp_all)
  calc p ((fun n => n - 1) ⁻¹' {k}) ≤ p ({k + 1} ∪ {0}) := measure_mono fun n hn => by
        simp only [mem_preimage, mem_singleton_iff] at hn
        simp only [mem_union, mem_singleton_iff]
        omega
    _ ≤ p {k + 1} + p {0} := measure_union_le _ _
    _ = p {k + 1} := by rw [hp0, add_zero]

/-- `P(i + 1, ·) = δᵢ`. -/
theorem fwdRec_succ (p : Measure ℕ) (i : ℕ) : fwdRecKernel p (i + 1) = Measure.dirac i := by
  change fwdRecMeas p (i + 1) = _
  simp [fwdRecMeas]

/-- (10.16): `π(j) = Σ_{n > j} p(n)` is invariant for the forward recurrence time chain. -/
theorem isInvariant_fwdRecInv {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0) :
    IsInvariant (fwdRecKernel p) (fwdRecInv p) := by
  unfold IsInvariant
  refine Measure.ext_of_singleton fun k => ?_
  rw [measure_kernel_apply _ _ (measurableSet_singleton k), lintegral_countable',
    tsum_eq_zero_add' ENNReal.summable, fwdRec_zero_singleton hp0]
  simp_rw [fwdRec_succ]
  rw [tsum_eq_single k (fun j hj => by simp [hj])]
  have h0 : fwdRecInv p {0} = 1 := by
    rw [fwdRecInv_singleton]
    have : {n : ℕ | 0 < n} = {0}ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
    rw [this, prob_compl_eq_one_sub (measurableSet_singleton 0), hp0, tsub_zero]
  rw [h0, mul_one, Measure.dirac_apply_of_mem (mem_singleton k), one_mul, fwdRecInv_singleton,
    fwdRecInv_singleton]
  have hu : {n : ℕ | k < n} = {k + 1} ∪ {n | k + 1 < n} := by
    ext n; simp only [mem_ofPred_eq, mem_union, mem_singleton_iff]; omega
  rw [hu, measure_union (by simp) (measurableSet_of_countable _)]

/-- With unbounded support, the forward recurrence time chain is irreducible. -/
theorem fwdRec_isIrreducibleChain {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) :
    haveI := isMarkovKernel_fwdRecKernel p; IsIrreducibleChain (fwdRecKernel p) := by
  have := isMarkovKernel_fwdRecKernel p
  have hto0 : ∀ k, Leads (fwdRecKernel p) k 0 := fun k =>
    (leads_iff_exists_pow _ k 0).2 ⟨k, by rw [fwdRec_pow_self]; simp⟩
  have hfrom0 : ∀ k, Leads (fwdRecKernel p) 0 k := fun k => by
    obtain ⟨n, hn, hpn⟩ := hsupp (k + 1)
    refine (leads_iff_exists_pow _ 0 k).2 ⟨1 + (n - 1 - k), ?_⟩
    refine lt_of_lt_of_le ?_ (pow_add_singleton_ge _ 1 (n - 1 - k) 0 (n - 1) k)
    rw [pow_one, fwdRec_zero_singleton hp0, show n - 1 + 1 = n by omega,
      fwdRec_pow_le (by omega), show n - 1 - (n - 1 - k) = k by omega]
    simpa using hpn
  exact ⟨0, eq_univ_of_forall fun k => ⟨hfrom0 k, hto0 k⟩⟩

/-- With unbounded support, the forward recurrence time chain is recurrent (for counting
measure, its maximal irreducibility measure). -/
theorem fwdRec_isRecurrentChain {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) :
    haveI := isMarkovKernel_fwdRecKernel p;
      IsRecurrentChain (fwdRecKernel p) Measure.count := by
  have := isMarkovKernel_fwdRecKernel p
  have hirr := fwdRec_isIrreducibleChain hp0 hsupp
  exact (isRecurrentChain_count_iff _ hirr).2 (fwdRec_isRecurrentState p hirr)

/-- The renewal state `0` is an accessible atom. -/
theorem fwdRec_isAccessibleAtom {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) :
    haveI := isMarkovKernel_fwdRecKernel p;
      IsAccessibleAtom (fwdRecKernel p) Measure.count {0} := by
  have := isMarkovKernel_fwdRecKernel p
  exact ⟨isAtom_singleton _ 0, isMaximalIrreducibility_count _
    (fwdRec_isIrreducibleChain hp0 hsupp), by simp⟩

/-- (10.16), MT p. 237: `π = U₀(0, ·)`, the minimal invariant measure `μ°_{0}` of
Theorem 10.2.1. -/
theorem fwdRecInv_eq_atomMeasure {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) :
    haveI := isMarkovKernel_fwdRecKernel p;
      fwdRecInv p = atomMeasure (fwdRecKernel p) (measurableSet_singleton 0) 0 := by
  have := isMarkovKernel_fwdRecKernel p
  have h1 : fwdRecInv p {0} = 1 := by
    rw [fwdRecInv_singleton]
    have : {n : ℕ | 0 < n} = {0}ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
    rw [this, prob_compl_eq_one_sub (measurableSet_singleton 0), hp0, tsub_zero]
  have h := theorem_10_2_1_ii_unique (fwdRec_isAccessibleAtom hp0 hsupp)
    (fwdRec_isRecurrentChain hp0 hsupp) (mem_singleton 0)
    (isInvariant_fwdRecInv hp0).isSubinvariant h1
  exact h

/-- (10.17), MT p. 237: the forward recurrence time chain (with unbounded support) is positive
iff the renewal law has finite mean `Σₙ n p(n) < ∞`. -/
theorem fwdRec_isPositive_iff {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0)
    (hsupp : ∀ N, ∃ n, N < n ∧ 0 < p {n}) :
    haveI := isMarkovKernel_fwdRecKernel p;
      IsPositive (fwdRecKernel p) Measure.count ↔ ∫⁻ n, (n : ℝ≥0∞) ∂p ≠ ∞ := by
  have := isMarkovKernel_fwdRecKernel p
  rw [(theorem_10_2_2 (fwdRec_isAccessibleAtom hp0 hsupp) (mem_singleton 0)).1,
    ← atomMeasure_univ _ (measurableSet_singleton 0), ← fwdRecInv_eq_atomMeasure hp0 hsupp,
    fwdRecInv_univ]

/-! ### Linked chains -/

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] in
/-- MT p. 237: if `π` is invariant for `P` and `σ` for `Q` (both σ-finite), then `π ⊗ σ` is
invariant for the chain `P ∥ₖ Q` moving the two coordinates independently. -/
theorem isInvariant_parallelComp (P : Kernel X X) (Q : Kernel Y Y) [IsSFiniteKernel P]
    [IsSFiniteKernel Q] {π : Measure X} {σ : Measure Y} [SigmaFinite π] [SigmaFinite σ]
    (hP : IsInvariant P π) (hQ : IsInvariant Q σ) :
    IsInvariant (Kernel.parallelComp P Q) (π.prod σ) := by
  unfold IsInvariant
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _)]
  simp_rw [Kernel.parallelComp_apply_prod]
  rw [lintegral_prod_mul (Kernel.measurable_coe _ hs).aemeasurable
    (Kernel.measurable_coe _ ht).aemeasurable]
  rw [← measure_kernel_apply π P hs, ← measure_kernel_apply σ Q ht, hP, hQ]

/-- The linked forward recurrence time chain `V*` (10.19): two independent copies. -/
noncomputable def linkedFwdRec (p : Measure ℕ) : Kernel (ℕ × ℕ) (ℕ × ℕ) :=
  Kernel.parallelComp (fwdRecKernel p) (fwdRecKernel p)

/-- MT p. 237: `π*(i, j) = π(i) π(j)` is invariant for the linked chain `V*`. -/
theorem isInvariant_linkedFwdRec {p : Measure ℕ} [IsProbabilityMeasure p] (hp0 : p {0} = 0) :
    IsInvariant (linkedFwdRec p) ((fwdRecInv p).prod (fwdRecInv p)) := by
  have := isMarkovKernel_fwdRecKernel p
  have := sigmaFinite_fwdRecInv p
  exact isInvariant_parallelComp _ _ (isInvariant_fwdRecInv hp0) (isInvariant_fwdRecInv hp0)

/-- MT p. 238: `π*(X*) = [π(ℤ₊)]²`, so the normalised product is an invariant probability
when `p` has finite mean. -/
theorem linkedFwdRec_univ (p : Measure ℕ) [IsFiniteMeasure p] :
    (fwdRecInv p).prod (fwdRecInv p) univ = (∫⁻ n, (n : ℝ≥0∞) ∂p) ^ 2 := by
  have := sigmaFinite_fwdRecInv p
  rw [← univ_prod_univ, Measure.prod_prod, fwdRecInv_univ, sq]

/-! ### A null recurrent chain -/

/-- The renewal law `p(2ᵏ⁺¹) = 2^{−(k+1)}`, `k ≥ 0`, which has infinite mean. -/
noncomputable def heavyRenewal : Measure ℕ :=
  Measure.sum fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ (k + 1) • Measure.dirac (2 ^ (k + 1))

/-- `Σₖ 2^{−(k+1)} = 1`. -/
theorem tsum_inv_two_pow_succ : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- `heavyRenewal` is a probability. -/
theorem isProbabilityMeasure_heavyRenewal : IsProbabilityMeasure heavyRenewal := by
  refine ⟨?_⟩
  rw [heavyRenewal, Measure.sum_apply _ MeasurableSet.univ]
  simpa using tsum_inv_two_pow_succ

/-- `heavyRenewal{0} = 0`. -/
theorem heavyRenewal_zero : heavyRenewal {0} = 0 := by
  rw [heavyRenewal, Measure.sum_apply _ (measurableSet_singleton 0)]
  refine ENNReal.tsum_eq_zero.2 fun k => ?_
  have : (2 : ℕ) ^ (k + 1) ∉ ({0} : Set ℕ) := by simp
  simp [Measure.dirac_apply' _ (measurableSet_singleton 0), this]

/-- `heavyRenewal` has unbounded support. -/
theorem heavyRenewal_supp (N : ℕ) : ∃ n, N < n ∧ 0 < heavyRenewal {n} := by
  refine ⟨2 ^ (N + 1), lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega)
    (by omega)), ?_⟩
  rw [heavyRenewal, Measure.sum_apply _ (measurableSet_singleton _)]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum N)
  simpa using ENNReal.pow_pos (by simp) _

/-- `heavyRenewal` has infinite mean. -/
theorem heavyRenewal_mean : ∫⁻ n, (n : ℝ≥0∞) ∂heavyRenewal = ∞ := by
  rw [heavyRenewal, lintegral_sum_measure]
  have : ∀ k : ℕ, ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂((2⁻¹ : ℝ≥0∞) ^ (k + 1) •
      Measure.dirac ((2 : ℕ) ^ (k + 1))) = 1 :=
    fun k => by
      rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      push_cast
      rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  exact (tsum_congr this).trans (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero)

/-- The correction to **Theorem 10.0.1** (MT p. 230): the forward recurrence time chain of
`heavyRenewal` is recurrent, `∅` is petite with `sup_{x ∈ ∅} E_x[τ_∅] = 0 < ∞`, but its invariant
measure is infinite and the chain is not positive. So the finiteness criterion needs `C ≠ ∅`. -/
theorem theorem_10_0_1_counterexample :
    haveI := isProbabilityMeasure_heavyRenewal
    haveI := isMarkovKernel_fwdRecKernel heavyRenewal
    IsRecurrentChain (fwdRecKernel heavyRenewal) Measure.count ∧
      IsPetite (fwdRecKernel heavyRenewal) ∅ ∧
      (∀ x ∈ (∅ : Set ℕ), meanReturnTime (fwdRecKernel heavyRenewal) ∅ x ≤ 0) ∧
      IsInvariantMeasure (fwdRecKernel heavyRenewal) (fwdRecInv heavyRenewal) ∧
      fwdRecInv heavyRenewal univ = ∞ ∧
      ¬ IsPositive (fwdRecKernel heavyRenewal) Measure.count := by
  have := isProbabilityMeasure_heavyRenewal
  have := isMarkovKernel_fwdRecKernel heavyRenewal
  refine ⟨fwdRec_isRecurrentChain heavyRenewal_zero heavyRenewal_supp,
    ⟨diracDist 1, Measure.dirac 0, MeasurableSet.empty, isSamplingDist_diracDist 1,
      by simp, fun x hx => absurd hx (notMem_empty x)⟩,
    fun x hx => absurd hx (notMem_empty x),
    ⟨sigmaFinite_fwdRecInv _, isInvariant_fwdRecInv heavyRenewal_zero⟩,
    by rw [fwdRecInv_univ, heavyRenewal_mean], ?_⟩
  rw [fwdRec_isPositive_iff heavyRenewal_zero heavyRenewal_supp, heavyRenewal_mean]
  simp

end MeynTweedie.Positivity
