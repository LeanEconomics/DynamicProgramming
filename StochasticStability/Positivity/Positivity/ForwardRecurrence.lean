/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.Period

/-!
# The period of the forward recurrence time chain (MT §5.4.4)

Meyn and Tweedie, §5.4.4, p. 115: for the forward recurrence time chain on the integers with
renewal distribution `p`, the period of the state `0` is `d = g.c.d.{n : p(n) > 0}` ("a simple
exercise").

* `fwdRecKernel p` (the chain of MT §3.3.1 on `ℤ₊`): from `0`, jump to `n − 1` with probability
  `p(n)`; from `j ≥ 1`, move to `j − 1`.
* `fwdRec_pow_le`, `fwdRec_pow_self`, `fwdRec_pow_ge`: the deterministic descent
  `Pᵏ(j, ·) = δ_{j−k}` for `k ≤ j`, and `Pᵏ(j, ·) = P^{k−j}(0, ·)` for `k ≥ j`.
* `fwdRec_return_pos`: every `n` with `p(n) > 0` is a return time to `0`;
  `fwdRec_return_decomp`: every return time `n` is `m + (n − m)` with `p(m) > 0` and `n − m` a
  return time or `0`.
* `periodAt_fwdRec` (MT p. 115): `d(0) = g.c.d.{n : p(n) > 0}`.

**Corrections.** None (the renewal distribution must have `p(0) = 0`).
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The transition laws of the forward recurrence time chain on `ℤ₊` (MT §3.3.1): from `0` the
chain jumps to `n − 1` with probability `p(n)`; from `j ≥ 1` it moves to `j − 1`. -/
noncomputable def fwdRecMeas (p : Measure ℕ) (j : ℕ) : Measure ℕ :=
  if j = 0 then p.map (fun n => n - 1) else Measure.dirac (j - 1)

/-- The forward recurrence time chain. -/
noncomputable def fwdRecKernel (p : Measure ℕ) : Kernel ℕ ℕ :=
  ⟨fwdRecMeas p, measurable_of_countable _⟩

/-- The forward recurrence time chain is a transition kernel when `p` is a probability. -/
theorem isMarkovKernel_fwdRecKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (fwdRecKernel p) := by
  refine ⟨fun j => ⟨?_⟩⟩
  change fwdRecMeas p j univ = 1
  unfold fwdRecMeas
  split_ifs
  · rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, preimage_univ,
      measure_univ]
  · simp

variable {p : Measure ℕ}

/-- The descent: `Pᵏ(j, ·) = δ_{j−k}` for `k ≤ j`. -/
theorem fwdRec_pow_le {j k : ℕ} (hk : k ≤ j) : (fwdRecKernel p ^ k) j = Measure.dirac (j - k) := by
  induction k with
  | zero => rw [pow_zero_apply, Nat.sub_zero]
  | succ k ih =>
    rw [pow_succ']
    change (fwdRecKernel p ∘ₖ (fwdRecKernel p ^ k)) j = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _)]
    change fwdRecMeas p (j - k) = _
    have hne : j - k ≠ 0 := by omega
    simp only [fwdRecMeas, hne, ite_false]
    rw [show j - k - 1 = j - (k + 1) by omega]

/-- `Pʲ(j, ·) = δ₀`. -/
theorem fwdRec_pow_self (j : ℕ) : (fwdRecKernel p ^ j) j = Measure.dirac 0 := by
  rw [fwdRec_pow_le le_rfl, Nat.sub_self]

/-- `Pᵏ(j, ·) = P^{k−j}(0, ·)` for `k ≥ j`. -/
theorem fwdRec_pow_ge {j k : ℕ} (hk : j ≤ k) :
    (fwdRecKernel p ^ k) j = (fwdRecKernel p ^ (k - j)) 0 := by
  rw [show k = (k - j) + j by omega, Kernel.pow_add, Kernel.comp_apply, fwdRec_pow_self,
    Measure.dirac_bind (Kernel.measurable _), Nat.add_sub_cancel]

/-- `Pⁿ⁺¹(0, {0}) = Σₘ p(m) Pⁿ(m − 1, {0})`. -/
theorem fwdRec_pow_succ_zero (n : ℕ) :
    (fwdRecKernel p ^ (n + 1)) 0 {0} =
      ∑' m, (fwdRecKernel p ^ n) (m - 1) {0} * p {m} := by
  rw [add_comm, Kernel.pow_add_apply_eq_lintegral _ 1 n 0 (measurableSet_singleton 0), pow_one]
  change ∫⁻ y, _ ∂fwdRecMeas p 0 = _
  simp only [fwdRecMeas, ite_true]
  rw [lintegral_map (Kernel.measurable_coe _ (measurableSet_singleton 0))
    (measurable_of_countable _), lintegral_countable']

/-- MT p. 115: every `n` with `p(n) > 0` is a return time to `0`. -/
theorem fwdRec_return_pos (hp0 : p {0} = 0) {n : ℕ} (hn : 0 < p {n}) :
    n ∈ returnSet (fwdRecKernel p) 0 := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => by rw [h, hp0] at hn; exact lt_irrefl _ hn
  refine ⟨hn1, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  rw [fwdRec_pow_succ_zero]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum (k + 1))
  rw [Nat.add_sub_cancel, fwdRec_pow_self]
  simpa using hn

/-- Every return time `n` to `0` splits as `n = m + (n − m)`, with `p(m) > 0` and `n − m` either
`0` or a return time. -/
theorem fwdRec_return_decomp (hp0 : p {0} = 0) {n : ℕ}
    (hn : n ∈ returnSet (fwdRecKernel p) 0) :
    ∃ m, m ≤ n ∧ 0 < p {m} ∧ (m = n ∨ n - m ∈ returnSet (fwdRecKernel p) 0) := by
  obtain ⟨hn1, hpos⟩ := hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn1
  rw [fwdRec_pow_succ_zero] at hpos
  obtain ⟨m, hm⟩ : ∃ m, 0 < (fwdRecKernel p ^ k) (m - 1) {0} * p {m} := by
    by_contra hc
    push Not at hc
    exact hpos.ne' (ENNReal.tsum_eq_zero.2 fun m => nonpos_iff_eq_zero.1 (hc m))
  have hpm : 0 < p {m} := pos_of_mul_pos_right hm zero_le
  have hP : 0 < (fwdRecKernel p ^ k) (m - 1) {0} := pos_of_mul_pos_left hm zero_le
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h => by rw [h, hp0] at hpm; exact lt_irrefl _ hpm
  -- the chain started at `m − 1` is at `0` at time `k` only if `m − 1 ≤ k`
  have hmk : m - 1 ≤ k := by
    by_contra hlt
    rw [fwdRec_pow_le (by omega), Measure.dirac_apply' _ (measurableSet_singleton 0),
      indicator_of_notMem (by simp; omega)] at hP
    exact lt_irrefl _ hP
  refine ⟨m, by omega, hpm, ?_⟩
  rw [fwdRec_pow_ge hmk] at hP
  rcases Nat.eq_or_lt_of_le hmk with h | h
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rwa [show k + 1 - m = k - (m - 1) by omega]

/-- **The period of the forward recurrence time chain** (MT p. 115): if `p(0) = 0`, then
`d(0) = g.c.d.{n : p(n) > 0}`. -/
theorem periodAt_fwdRec (hp0 : p {0} = 0) :
    periodAt (fwdRecKernel p) 0 = setGcd {n | 0 < p {n}} := by
  unfold periodAt setGcd
  congr 1
  ext d
  constructor
  · exact fun h n hn => h n (fwdRec_return_pos hp0 hn)
  · intro h n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      obtain ⟨m, hmn, hpm, hcase⟩ := fwdRec_return_decomp hp0 hn
      rcases hcase with rfl | hrest
      · exact h m hpm
      · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, hp0] at hpm; exact lt_irrefl _ hpm
        have h1 := ih (n - m) (by have := hrest.1; omega) hrest
        rw [show n = m + (n - m) by omega]
        exact dvd_add (h m hpm) h1

end MeynTweedie.Positivity
