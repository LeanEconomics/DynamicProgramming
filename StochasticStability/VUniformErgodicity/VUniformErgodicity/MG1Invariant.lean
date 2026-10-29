/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.QueueInvariant

/-!
# Invariant measures of the M/G/1 queue (MT §10.3.2)

Meyn and Tweedie, §10.3.2, pp. 238–239. The number `N*` in an M/G/1 queue at departure times is
the chain on `ℤ₊` with `P(0, j) = q(j)` and `P(i, j) = q(j + 1 − i)` for `i ≥ 1`, `j ≥ i − 1`
(`mg1Matrix`, `mg1Kernel`), where `q(i) = P(Z = i − 1)`.

* `qTail q m = Σ_{n ≥ m} q(n)` (the book's `q̄_{m−1}`); `tsum_qTail_succ`:
  `Σ_{m ≥ 1} q̄ = Σⱼ j q(j)`, the mean `mg1Mean q` (the book's `β + 1`).
* `mg1_row_tail`: `P(0, [k, ∞)) = q̄(k)` and `P(i + 1, [k, ∞)) = q̄(k − i)`;
  `mg1_col_tail`: for any weights `m`,
  `Σᵢ m(i) P(i, [k, ∞)) = m(0) q̄(k) + Σ_{i < k} m(i + 1) q̄(k − i) + Σ_{i > k} m(i)`.
* The cut equations (10.20)–(10.21): `mg1_cut_of_invariant`, every invariant probability `π`
  satisfies `π(k + 1) q(0) = π(0) q̄(k + 1) + Σ_{i < k} π(i + 1) q̄(k + 1 − i)`.
* `mg1Seq q`: the solution of the cut equations with `π(0) = 1`, built recursively;
  `mg1Seq_partial_le`: its partial sums are bounded by `β/(1 − β)` when `β = Σ j q(j) < 1`;
  `isInvariant_mg1Seq`: it is invariant.

**Proposition 10.3.1** (`proposition_10_3_1`, p. 239): a `ψ`-irreducible M/G/1 chain with
`q(0) > 0` is positive iff `Σⱼ j q(j) < 1`; `mg1_invariant_prob_zero`: an invariant probability
has `π(0) = 1 − Σⱼ j q(j)` (the book's `π(0) = −β`).

**Correction.** The book writes the condition as `β = Σ j qⱼ < 1` while defining
`β = Σ_{j ≥ 0} q̄ⱼ − 1`, the mean increment. With the second definition the condition is
`β < 0`; both say `Σⱼ j q(j) < 1`, which is the form proved here.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-! ### The chain -/

/-- The transition matrix of the M/G/1 queue (MT p. 238). -/
noncomputable def mg1Matrix (q : ℕ → ℝ≥0∞) (i j : ℕ) : ℝ≥0∞ :=
  if i = 0 then q j else if i ≤ j + 1 then q (j + 1 - i) else 0

/-- The M/G/1 chain. -/
noncomputable abbrev mg1Kernel (q : ℕ → ℝ≥0∞) : Kernel ℕ ℕ := matKernel (mg1Matrix q)

/-- The tails `q̄(m) = Σ_{n ≥ m} q(n)`. -/
noncomputable def qTail (q : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ := ∑' n, q (n + m)

/-- The mean `Σⱼ j q(j)` of the arrivals per service. -/
noncomputable def mg1Mean (q : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' j : ℕ, (j : ℝ≥0∞) * q j

/-- `q̄(0) = 1`. -/
theorem qTail_zero {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) : qTail q 0 = 1 := by
  simpa [qTail] using hq

/-- `q̄(m) = q(m) + q̄(m + 1)`. -/
theorem qTail_eq (q : ℕ → ℝ≥0∞) (m : ℕ) : qTail q m = q m + qTail q (m + 1) := by
  rw [qTail, tsum_eq_zero_add' ENNReal.summable, zero_add]
  congr 1
  exact tsum_congr fun n => by congr 1; omega

/-- `q̄(m) ≤ 1`. -/
theorem qTail_le_one {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (m : ℕ) : qTail q m ≤ 1 := by
  rw [← hq, tsum_split q m]
  exact le_add_self

/-- `q(0) + q̄(1) = 1`. -/
theorem q_zero_add_qTail_one {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) : q 0 + qTail q 1 = 1 := by
  rw [← qTail_eq, qTail_zero hq]

/-- `Σ_{m ≥ 1} q̄(m) = Σⱼ j q(j)`. -/
theorem tsum_qTail_succ (q : ℕ → ℝ≥0∞) : ∑' m, qTail q (m + 1) = mg1Mean q := by
  have h1 : ∀ m, qTail q (m + 1) = ∑' n, q n * (Iio n).indicator 1 m := fun m => by
    rw [qTail, ← tsum_indicator_Ioi]
    refine tsum_congr fun n => ?_
    by_cases h : m < n
    · rw [indicator_of_mem (show n ∈ Ioi m from h), indicator_of_mem (show m ∈ Iio n from h),
        Pi.one_apply, mul_one]
    · rw [indicator_of_notMem (show n ∉ Ioi m from h),
        indicator_of_notMem (show m ∉ Iio n from h), mul_zero]
  simp_rw [h1]
  rw [ENNReal.tsum_comm, mg1Mean]
  refine tsum_congr fun n => ?_
  rw [ENNReal.tsum_mul_left, tsum_indicator_Iio, mul_comm]

/-- `Σⱼ j q(j) = q̄(1) + Σ_{m ≥ 2} q̄(m)`. -/
theorem mg1Mean_eq (q : ℕ → ℝ≥0∞) :
    mg1Mean q = qTail q 1 + ∑' m, qTail q (m + 2) := by
  rw [← tsum_qTail_succ, tsum_eq_zero_add' ENNReal.summable]

/-- The rows of the M/G/1 matrix sum to one. -/
theorem isTransitionMatrix_mg1 {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) :
    IsTransitionMatrix (mg1Matrix q) := by
  intro i
  cases i with
  | zero => simpa [mg1Matrix] using hq
  | succ i =>
    simp only [mg1Matrix, Nat.succ_ne_zero, ite_false]
    rw [tsum_split _ i, Finset.sum_eq_zero (fun j hj => by
      simp only [Finset.mem_range] at hj
      simp [show ¬ (i + 1 ≤ j + 1) by omega]), zero_add, ← hq]
    exact tsum_congr fun j => by
      simp only [show i + 1 ≤ j + i + 1 by omega, ite_true]
      congr 1
      omega

/-- The row tails: `P(0, [k, ∞)) = q̄(k)`. -/
theorem mg1_row_tail_zero (q : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' j, mg1Matrix q 0 (j + k) = qTail q k := by
  simp [mg1Matrix, qTail]

/-- The row tails: `P(i + 1, [k, ∞)) = q̄(k − i)`. -/
theorem mg1_row_tail_succ {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (i k : ℕ) :
    ∑' j, mg1Matrix q (i + 1) (j + k) = qTail q (k - i) := by
  simp only [mg1Matrix, Nat.succ_ne_zero, ite_false]
  by_cases hik : i ≤ k
  · refine tsum_congr fun j => ?_
    simp only [show i + 1 ≤ j + k + 1 by omega, ite_true]
    congr 1
    omega
  · rw [show k - i = 0 by omega, qTail_zero hq, tsum_split _ (i - k),
      Finset.sum_eq_zero (fun j hj => by
        simp only [Finset.mem_range] at hj
        simp [show ¬ (i + 1 ≤ j + k + 1) by omega]), zero_add, ← hq]
    exact tsum_congr fun j => by
      simp only [show i + 1 ≤ j + (i - k) + k + 1 by omega, ite_true]
      congr 1
      omega

/-- The column tails: for weights `m`,
`Σᵢ m(i) P(i, [k, ∞)) = m(0) q̄(k) + Σ_{i < k} m(i + 1) q̄(k − i) + Σᵢ m(i + k + 1)`. -/
theorem mg1_col_tail {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (m : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' i, m i * ∑' j, mg1Matrix q i (j + k) =
      m 0 * qTail q k + ∑ i ∈ Finset.range k, m (i + 1) * qTail q (k - i) +
        ∑' i, m (i + (k + 1)) := by
  rw [tsum_eq_zero_add' ENNReal.summable, mg1_row_tail_zero]
  simp_rw [mg1_row_tail_succ hq]
  rw [tsum_split _ k, add_assoc]
  congr 2
  exact tsum_congr fun i => by
    rw [show k - (i + k) = 0 by omega, qTail_zero hq, mul_one]
    congr 1

/-- The double sum over `i < k`: `Σₖ Σ_{i < k} f(i, k) = Σᵢ Σₙ f(i, n + i + 1)`. -/
theorem tsum_sum_range_lt (f : ℕ → ℕ → ℝ≥0∞) :
    ∑' k, ∑ i ∈ Finset.range k, f i k = ∑' i, ∑' n, f i (n + (i + 1)) := by
  have h1 : ∀ k, ∑ i ∈ Finset.range k, f i k =
      ∑' i, (Iio k).indicator (fun i => f i k) i := fun k => by
    rw [tsum_eq_sum (s := Finset.range k) (fun i hi => indicator_of_notMem
      (show i ∉ Iio k from fun h => hi (Finset.mem_range.2 h)) _)]
    exact Finset.sum_congr rfl fun i hi =>
      (indicator_of_mem (show i ∈ Iio k from Finset.mem_range.1 hi) (fun i => f i k)).symm
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => ?_
  rw [tsum_split _ (i + 1), Finset.sum_eq_zero (fun k hk => indicator_of_notMem
    (by simp only [Finset.mem_range] at hk; simp only [mem_Iio]; omega) _), zero_add]
  exact tsum_congr fun n => indicator_of_mem (by simp only [mem_Iio]; omega) _

/-- The finite version: `Σ_{k < K} Σ_{i < k} f(i, k) ≤ Σ_{i < K} Σₙ f(i, n + i + 1)`. -/
theorem sum_sum_range_lt_le (f : ℕ → ℕ → ℝ≥0∞) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range k, f i k ≤
      ∑ i ∈ Finset.range K, ∑' n, f i (n + (i + 1)) := by
  have h1 : ∀ k ∈ Finset.range K, ∑ i ∈ Finset.range k, f i k =
      ∑ i ∈ Finset.range K, (Iio k).indicator (fun i => f i k) i := fun k hk => by
    simp only [Finset.mem_range] at hk
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hk.le) (fun i _ hi =>
      indicator_of_notMem (show i ∉ Iio k from fun h => hi (Finset.mem_range.2 h)) _)]
    exact Finset.sum_congr rfl fun i hi =>
      (indicator_of_mem (show i ∈ Iio k from Finset.mem_range.1 hi) (fun i => f i k)).symm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ k ∈ Finset.range K, (Iio k).indicator (fun i => f i k) i
      ≤ ∑' k, (Iio k).indicator (fun i => f i k) i := ENNReal.sum_le_tsum _
    _ = ∑' n, f i (n + (i + 1)) := by
        rw [tsum_split _ (i + 1), Finset.sum_eq_zero (fun k hk => indicator_of_notMem
          (by simp only [Finset.mem_range] at hk; simp only [mem_Iio]; omega) _), zero_add]
        exact tsum_congr fun n => indicator_of_mem (by simp only [mem_Iio]; omega) _

/-- `Σₙ q̄((n + i + 1) + 1 − i) = Σ_{m ≥ 2} q̄(m)`. -/
theorem tsum_qTail_shift (q : ℕ → ℝ≥0∞) (i : ℕ) :
    ∑' n, qTail q (n + (i + 1) + 1 - i) = ∑' m, qTail q (m + 2) :=
  tsum_congr fun n => by congr 1; omega

/-! ### The cut equations for an invariant probability -/

/-- The cut equations (10.20) for an invariant probability `π` (weights `m(i) = π{i}`):
`m(k + 1) q(0) = m(0) q̄(k + 1) + Σ_{i < k} m(i + 1) q̄(k + 1 − i)`. -/
theorem mg1_cut_of_invariant {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) {m : ℕ → ℝ≥0∞}
    (hm1 : ∑' i, m i = 1) (hinv : ∀ j, ∑' i, m i * mg1Matrix q i j = m j) (k : ℕ) :
    m (k + 1) * q 0 =
      m 0 * qTail q (k + 1) + ∑ i ∈ Finset.range k, m (i + 1) * qTail q (k + 1 - i) := by
  have hT : ∀ k, ∑' i, m i * ∑' j, mg1Matrix q i (j + k) = ∑' j, m (j + k) := fun k => by
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun j => hinv (j + k)
  have hfin : ∀ k, ∑' j, m (j + k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top (b := ∑' i, m i) (by rw [hm1]; exact ENNReal.one_ne_top)
      (by rw [tsum_split m k]; exact le_add_self)
  have hsplitT : ∑' j, m (j + (k + 1)) = m (k + 1) + ∑' j, m (j + (k + 1 + 1)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, zero_add]
    congr 1
    exact tsum_congr fun j => by congr 1; omega
  have h := hT (k + 1)
  rw [mg1_col_tail hq, hsplitT, Finset.sum_range_succ,
    show k + 1 - k = 1 by omega] at h
  have h2 := (ENNReal.add_left_inj (hfin (k + 1 + 1))).1 h
  have hmfin : m (k + 1) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hm1]; exact ENNReal.one_ne_top) (ENNReal.le_tsum _)
  have h3 : m (k + 1) * q 0 + m (k + 1) * qTail q 1 = m (k + 1) := by
    rw [← mul_add, q_zero_add_qTail_one hq, mul_one]
  rw [← add_assoc] at h2
  replace h2 := h2.trans h3.symm
  exact ((ENNReal.add_left_inj (ENNReal.mul_ne_top hmfin
    (ne_top_of_le_ne_top ENNReal.one_ne_top (qTail_le_one hq 1)))).1 h2).symm

/-- `π(0) > 0` for an invariant probability, when `q(0) > 0`. -/
theorem mg1_zero_pos {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0) {m : ℕ → ℝ≥0∞}
    (hm1 : ∑' i, m i = 1) (hinv : ∀ j, ∑' i, m i * mg1Matrix q i j = m j) : m 0 ≠ 0 := by
  intro h0
  have hall : ∀ k, m (k + 1) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hc := mg1_cut_of_invariant hq hm1 hinv k
      rw [h0, zero_mul, zero_add, Finset.sum_eq_zero (fun i hi => by
        simp only [Finset.mem_range] at hi
        rw [ih i hi, zero_mul])] at hc
      exact (mul_eq_zero.1 hc).resolve_right hq0
  have : ∑' i, m i = 0 := by
    rw [tsum_eq_zero_add' ENNReal.summable, h0, zero_add]
    exact ENNReal.tsum_eq_zero.2 hall
  rw [hm1] at this
  exact one_ne_zero this

/-- Summing the cut equations: `q(0) Σ_{k ≥ 1} π(k) = π(0) β' + (Σ_{m ≥ 2} q̄(m)) Σ_{k ≥ 1} π(k)`,
with `β' = Σⱼ j q(j)`. -/
theorem mg1_sum_cut {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) {m : ℕ → ℝ≥0∞}
    (hm1 : ∑' i, m i = 1) (hinv : ∀ j, ∑' i, m i * mg1Matrix q i j = m j) :
    q 0 * ∑' k, m (k + 1) =
      m 0 * mg1Mean q + (∑' n, qTail q (n + 2)) * ∑' k, m (k + 1) := by
  rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_comm (q 0), mg1_cut_of_invariant hq hm1 hinv]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_qTail_succ,
    tsum_sum_range_lt (fun i k => m (i + 1) * qTail q (k + 1 - i))]
  congr 1
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [ENNReal.tsum_mul_left, tsum_qTail_shift, mul_comm]

/-- For an invariant probability, `π(0) = 1 − Σⱼ j q(j)`; in particular `Σⱼ j q(j) < 1`. -/
theorem mg1_invariant_prob_zero {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    {m : ℕ → ℝ≥0∞} (hm1 : ∑' i, m i = 1) (hinv : ∀ j, ∑' i, m i * mg1Matrix q i j = m j) :
    mg1Mean q < 1 ∧ m 0 + mg1Mean q = 1 := by
  have h0 := mg1_zero_pos hq hq0 hm1 hinv
  have hs := mg1_sum_cut hq hm1 hinv
  set A := ∑' k, m (k + 1) with hA
  have hmA : m 0 + A = 1 := by rw [hA, ← tsum_eq_zero_add' ENNReal.summable, hm1]
  have hAfin : A ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hmA ▸ le_add_self)
  have hq0fin : q 0 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hq ▸ ENNReal.le_tsum 0)
  have hSfin : mg1Mean q ≠ ∞ := by
    intro hS
    rw [hS, ENNReal.mul_top h0] at hs
    exact ENNReal.mul_ne_top hq0fin hAfin (top_le_iff.1 (hs ▸ le_self_add))
  -- `A = S`
  have hAS : A = mg1Mean q := by
    calc A = (q 0 + qTail q 1) * A := by rw [q_zero_add_qTail_one hq, one_mul]
      _ = q 0 * A + qTail q 1 * A := add_mul _ _ _
      _ = m 0 * mg1Mean q + (∑' n, qTail q (n + 2)) * A + qTail q 1 * A := by rw [hs]
      _ = m 0 * mg1Mean q + (qTail q 1 + ∑' n, qTail q (n + 2)) * A := by ring
      _ = (m 0 + A) * mg1Mean q := by rw [← mg1Mean_eq]; ring
      _ = mg1Mean q := by rw [hmA, one_mul]
  refine ⟨?_, by rw [← hAS, hmA]⟩
  rw [← hAS, ← hmA]
  exact ENNReal.lt_add_right hAfin h0 |>.trans_eq (add_comm _ _)

/-! ### The solution of the cut equations -/

/-- The solution of the cut equations with `π(0) = 1`:
`π(k + 1) = [q̄(k + 1) + Σ_{i < k} π(i + 1) q̄(k + 1 − i)] / q(0)`. -/
noncomputable def mg1Seq (q : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 1
  | k + 1 => (qTail q (k + 1) + ∑ i : Fin k, mg1Seq q (i.1 + 1) * qTail q (k + 1 - i.1)) / q 0
termination_by n => n
decreasing_by exact Nat.succ_lt_succ i.2

/-- The defining recursion of `mg1Seq`. -/
theorem mg1Seq_succ (q : ℕ → ℝ≥0∞) (k : ℕ) :
    mg1Seq q (k + 1) = (qTail q (k + 1) +
      ∑ i ∈ Finset.range k, mg1Seq q (i + 1) * qTail q (k + 1 - i)) / q 0 := by
  rw [mg1Seq, Fin.sum_univ_eq_sum_range (fun i => mg1Seq q (i + 1) * qTail q (k + 1 - i)) k]

/-- `mg1Seq q 0 = 1`. -/
theorem mg1Seq_zero (q : ℕ → ℝ≥0∞) : mg1Seq q 0 = 1 := by rw [mg1Seq]

/-- The cut equations hold for `mg1Seq`. -/
theorem mg1Seq_cut (q : ℕ → ℝ≥0∞) (hq0 : q 0 ≠ 0) (hq0t : q 0 ≠ ∞) (k : ℕ) :
    mg1Seq q (k + 1) * q 0 = mg1Seq q 0 * qTail q (k + 1) +
      ∑ i ∈ Finset.range k, mg1Seq q (i + 1) * qTail q (k + 1 - i) := by
  rw [mg1Seq_succ, ENNReal.div_mul_cancel hq0 hq0t, mg1Seq_zero, one_mul]

/-- The values of `mg1Seq` are finite. -/
theorem mg1Seq_ne_top {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0) (k : ℕ) :
    mg1Seq q k ≠ ∞ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [mg1Seq_zero]; exact ENNReal.one_ne_top
    | succ k =>
      rw [mg1Seq_succ]
      refine ENNReal.div_ne_top (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.one_ne_top
        (qTail_le_one hq _), ENNReal.sum_ne_top.2 fun i hi => ENNReal.mul_ne_top
          (ih (i + 1) (by simp only [Finset.mem_range] at hi; omega))
          (ne_top_of_le_ne_top ENNReal.one_ne_top (qTail_le_one hq _))⟩) hq0

/-- The partial sums `P_K = Σ_{k < K} π(k + 1)` satisfy `P_K ≤ β' + β' P_K`. -/
theorem mg1Seq_partial_le {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0) (K : ℕ) :
    ∑ k ∈ Finset.range K, mg1Seq q (k + 1) ≤
      mg1Mean q + mg1Mean q * ∑ k ∈ Finset.range K, mg1Seq q (k + 1) := by
  have hq0t : q 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hq ▸ ENNReal.le_tsum 0)
  set PK := ∑ k ∈ Finset.range K, mg1Seq q (k + 1)
  set R1 := ∑' n, qTail q (n + 2)
  have h1 : q 0 * PK ≤ mg1Mean q + R1 * PK := by
    rw [Finset.mul_sum]
    simp_rw [mul_comm (q 0), mg1Seq_cut q hq0 hq0t, mg1Seq_zero, one_mul]
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← tsum_qTail_succ]; exact ENNReal.sum_le_tsum _
    · refine (sum_sum_range_lt_le (fun i k => mg1Seq q (i + 1) * qTail q (k + 1 - i)) K).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [ENNReal.tsum_mul_left, tsum_qTail_shift, mul_comm]
  calc PK = (q 0 + qTail q 1) * PK := by rw [q_zero_add_qTail_one hq, one_mul]
    _ = q 0 * PK + qTail q 1 * PK := add_mul _ _ _
    _ ≤ mg1Mean q + R1 * PK + qTail q 1 * PK := add_le_add_left h1 _
    _ = mg1Mean q + (qTail q 1 + R1) * PK := by ring
    _ = mg1Mean q + mg1Mean q * PK := by rw [← mg1Mean_eq]

/-- When `β' = Σⱼ j q(j) < 1`, `Σ_{k ≥ 1} π(k) ≤ β'/(1 − β')`. -/
theorem mg1Seq_tsum_le {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    (hS : mg1Mean q < 1) :
    ∑' k, mg1Seq q (k + 1) ≤ mg1Mean q / (1 - mg1Mean q) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => ?_
  have hPfin : ∑ k ∈ Finset.range K, mg1Seq q (k + 1) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun k _ => mg1Seq_ne_top hq hq0 _
  have hSfin : mg1Mean q ≠ ∞ := (hS.trans ENNReal.one_lt_top).ne
  rw [ENNReal.le_div_iff_mul_le (Or.inl (tsub_pos_of_lt hS).ne') (Or.inr hSfin), mul_comm,
    ENNReal.sub_mul (fun _ _ => hPfin), one_mul, tsub_le_iff_right]
  exact mg1Seq_partial_le hq hq0 K

/-- When `Σⱼ j q(j) < 1`, `mg1Seq` is invariant for the M/G/1 chain: the cut equations imply the
invariant equations (10.20). -/
theorem isInvariant_mg1Seq {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    (hS : mg1Mean q < 1) : ∀ j, ∑' i, mg1Seq q i * mg1Matrix q i j = mg1Seq q j := by
  have hq0t : q 0 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hq ▸ ENNReal.le_tsum 0)
  set a := mg1Seq q
  have hSfin : mg1Mean q ≠ ∞ := (hS.trans ENNReal.one_lt_top).ne
  have htot : ∑' i, a i ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.2 ⟨mg1Seq_ne_top hq hq0 0, ne_top_of_le_ne_top ?_
      (mg1Seq_tsum_le hq hq0 hS)⟩
    exact ENNReal.div_ne_top hSfin (tsub_pos_of_lt hS).ne'
  have hTfin : ∀ k, ∑' i, a (i + k) ≠ ∞ := fun k =>
    ne_top_of_le_ne_top htot (by rw [tsum_split a k]; exact le_add_self)
  -- the column tails are the tails of `a`
  have hcol : ∀ k, ∑' i, a i * ∑' j, mg1Matrix q i (j + k) = ∑' i, a (i + k) := by
    intro k
    rw [mg1_col_tail hq]
    cases k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, qTail_zero hq, mul_one]
      rw [tsum_eq_zero_add' ENNReal.summable (f := a)]
    | succ k =>
      have hc : a (k + 1) * q 0 = a 0 * qTail q (k + 1) +
          ∑ i ∈ Finset.range k, a (i + 1) * qTail q (k + 1 - i) := mg1Seq_cut q hq0 hq0t k
      rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega]
      calc a 0 * qTail q (k + 1) + (∑ i ∈ Finset.range k, a (i + 1) * qTail q (k + 1 - i) +
            a (k + 1) * qTail q 1) + ∑' i, a (i + (k + 1 + 1))
          = (a 0 * qTail q (k + 1) + ∑ i ∈ Finset.range k, a (i + 1) * qTail q (k + 1 - i)) +
            a (k + 1) * qTail q 1 + ∑' i, a (i + (k + 1 + 1)) := by ring
        _ = a (k + 1) * q 0 + a (k + 1) * qTail q 1 + ∑' i, a (i + (k + 1 + 1)) := by rw [hc]
        _ = a (k + 1) + ∑' i, a (i + (k + 1 + 1)) := by
            rw [← mul_add, q_zero_add_qTail_one hq, mul_one]
        _ = ∑' i, a (i + (k + 1)) := by
            rw [tsum_eq_zero_add' ENNReal.summable (f := fun i => a (i + (k + 1))), zero_add]
            congr 1
            exact tsum_congr fun i => by congr 1; omega
  intro j
  have h1 := hcol j
  have h2 : ∑' i, a i * ∑' l, mg1Matrix q i (l + j) =
      ∑' i, a i * mg1Matrix q i j + ∑' i, a i * ∑' l, mg1Matrix q i (l + (j + 1)) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun i => ?_
    rw [tsum_eq_zero_add' ENNReal.summable, zero_add, mul_add]
    congr 2
    exact tsum_congr fun l => by congr 1; omega
  rw [h2, hcol (j + 1)] at h1
  have h3 : ∑' i, a (i + j) = a j + ∑' i, a (i + (j + 1)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, zero_add]
    congr 1
    exact tsum_congr fun i => by congr 1; omega
  rw [h3] at h1
  exact (ENNReal.add_left_inj (hTfin (j + 1))).1 h1

/-! ### Proposition 10.3.1 -/

/-- **Proposition 10.3.1** (MT p. 239): a `ψ`-irreducible M/G/1 chain with `q(0) > 0` is positive
iff `Σⱼ j q(j) < 1`. -/
theorem proposition_10_3_1 {q : ℕ → ℝ≥0∞} (hq : ∑' n, q n = 1) (hq0 : q 0 ≠ 0)
    {ψ : Measure ℕ}
    (hψ : haveI := isMarkovKernel_matKernel (isTransitionMatrix_mg1 hq);
      IsMaximalIrreducibility (mg1Kernel q) ψ) :
    haveI := isMarkovKernel_matKernel (isTransitionMatrix_mg1 hq)
    IsPositive (mg1Kernel q) ψ ↔ mg1Mean q < 1 := by
  have := isMarkovKernel_matKernel (isTransitionMatrix_mg1 hq)
  constructor
  · rintro ⟨-, π, hπ, hinv⟩
    have hπeq : π = pointMeasure fun i => π {i} :=
      Measure.ext_of_singleton fun i => (pointMeasure_singleton (fun i => π {i}) i).symm
    rw [hπeq, isInvariant_matKernel_pointMeasure_iff] at hinv
    have hm1 : ∑' i, π {i} = 1 := by
      rw [← pointMeasure_univ, ← hπeq, measure_univ]
    exact (mg1_invariant_prob_zero hq hq0 hm1 hinv).1
  · intro hS
    have hinv : IsInvariant (mg1Kernel q) (pointMeasure (mg1Seq q)) :=
      (isInvariant_matKernel_pointMeasure_iff _ _).2 (isInvariant_mg1Seq hq hq0 hS)
    set μ := pointMeasure (mg1Seq q)
    have hSfin : mg1Mean q ≠ ∞ := (hS.trans ENNReal.one_lt_top).ne
    have hμfin : μ univ ≠ ∞ := by
      rw [pointMeasure_univ, tsum_eq_zero_add' ENNReal.summable]
      refine ENNReal.add_ne_top.2 ⟨mg1Seq_ne_top hq hq0 0, ne_top_of_le_ne_top ?_
        (mg1Seq_tsum_le hq hq0 hS)⟩
      exact ENNReal.div_ne_top hSfin (tsub_pos_of_lt hS).ne'
    have hμ0 : μ univ ≠ 0 := by
      rw [pointMeasure_univ, tsum_eq_zero_add' ENNReal.summable, mg1Seq_zero]
      exact (lt_of_lt_of_le one_pos le_self_add).ne'
    refine ⟨hψ, (μ univ)⁻¹ • μ, ⟨?_⟩, hinv.smul _⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 hμfin]

end MeynTweedie.VUniformErgodicity
