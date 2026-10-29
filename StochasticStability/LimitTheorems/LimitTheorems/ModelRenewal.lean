/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.ModelRandomWalk
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Renewal processes and recurrence time chains

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelRenewal.lean`), with the namespace changed to
`MeynTweedie.LimitTheorems` and the imports to `InvariantMeasures.*`.

That module was in turn copied from the `MarkovModels` project (`MarkovModels/Renewal.lean`).

MT, §2.4.1, pp. 38–40, and (RT1)–(RT4) of Appendix C, p. 543.

* `renewalKernel p`: the renewal process `Zₙ₊₁ = Zₙ + Yₙ₊₁` on `ℤ₊` with increment law `p`, a
  random walk on `ℕ`. With `p(0) = 0` it moves up at every step (`renewalKernel_apply_Ioi`), and
  every renewal sequence tends to infinity (`le_renewal`): the chain is evanescent (MT, p. 38).
* `seqConv a b`: the convolution `a ∗ b (n) = Σ_{j ≤ n} a(j) b(n − j)` (MT, p. 39), with both forms
  of the definition (`seqConv_eq_sum_range`, `seqConv_comm`), and `seqConvPow a k = a^{k∗}`.
* `renewal_law`: for a delayed renewal process with delay law `a`,
  `P(Z_k = n) = a ∗ p^{k∗}(n)` (MT, p. 39); `renewal_law_one` is
  `P(Z₁ = n) = Σ_{j ≤ n} a(j) p(n − j)` (MT, p. 38).
* `forwardKernel p`: the forward recurrence time chain (MT, (RT1), p. 39): from `k > 1` it moves
  deterministically to `k − 1`, from `1` it is renewed with law `p`.
  `backwardKernel p`: the backward recurrence time (age) chain (MT, (RT2)): from age `j` it
  drops to `0` with the conditional renewal probability `p(j + 1)/p(j, ∞)` and otherwise ages by
  one.
* The pathwise dynamics described in MT, p. 39, for the recurrence times `fwdTime Z` and
  `bwdTime Z` of a strictly increasing sequence `Z` of renewal epochs (`fwdTime_succ_of_one_lt`,
  `fwdTime_succ_of_eq_one`, `bwdTime_succ_of_renewal`, `bwdTime_succ_of_not_renewal`).
  **Correction:** (RT2) takes an infimum over an empty set for `n < Z₀` (`bwdTime_set_empty`), so
  `V⁻(n)` is only defined from the first renewal on.
* `fwdTimeCts`, `bwdTimeCts` and their `δ`-skeletons: (RT3)–(RT4), p. 543.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### The renewal process -/

/-- The (delayed) renewal process `Zₙ₊₁ = Zₙ + Yₙ₊₁` on `ℤ₊` with i.i.d. increments of law `p`
(MT, p. 38): random walk on `ℕ`. -/
noncomputable def renewalKernel (p : Measure ℕ) : Kernel ℕ ℕ := randomWalkKernel p

/-- The renewal process is a Markov kernel. -/
theorem isMarkovKernel_renewalKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (renewalKernel p) :=
  isMarkovKernel_randomWalkKernel p

/-- `P(z, {n}) = p(n − z)` for `z ≤ n`, and `0` for `z > n`. -/
theorem renewalKernel_apply_singleton (p : Measure ℕ) [SFinite p] (z n : ℕ) :
    renewalKernel p z {n} = if z ≤ n then p {n - z} else 0 := by
  rw [renewalKernel, randomWalkKernel_apply' p z (measurableSet_singleton n)]
  split_ifs with h
  · congr 1
    ext w
    simp only [mem_ofPred_eq, mem_singleton_iff]
    omega
  · convert measure_empty (μ := p)
    ext w
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
    omega

/-- With `p(0) = 0` the renewal process moves up at every step: `P(z, (z, ∞)) = 1`. -/
theorem renewalKernel_apply_Ioi (p : Measure ℕ) [IsProbabilityMeasure p] (hp : p {0} = 0)
    (z : ℕ) : renewalKernel p z (Ioi z) = 1 := by
  rw [renewalKernel, randomWalkKernel_apply' p z measurableSet_Ioi]
  have h : {w : ℕ | z + w ∈ Ioi z} = ({0} : Set ℕ)ᶜ := by
    ext w
    simp only [mem_ofPred_eq, mem_Ioi, mem_compl_iff, mem_singleton_iff]
    omega
  rw [h, prob_compl_eq_one_sub (measurableSet_singleton 0), hp, tsub_zero]

/-- MT, p. 38: a renewal sequence with increments `≥ 1` is strictly increasing, so `Zₙ ≥ n`;
the renewal process is evanescent. -/
theorem le_renewal {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) : n ≤ Z n := hZ.id_le n

/-! ### Convolutions of sequences -/

/-- The convolution `a ∗ b (n) = Σ_{i + j = n} a(i) b(j)` (MT, p. 39), as the coefficients of the
product of generating functions. -/
noncomputable def seqConv (a b : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)

/-- `a ∗ b (n) = Σ_{j=0}^{n} a(j) b(n − j)`. -/
theorem seqConv_eq_sum_range (a b : ℕ → ℝ≥0∞) (n : ℕ) :
    seqConv a b n = ∑ j ∈ Finset.range (n + 1), a j * b (n - j) := by
  rw [seqConv, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]

/-- The two forms of MT, p. 39: `Σ_j b(j) a(n − j) = Σ_j a(j) b(n − j)`. -/
theorem seqConv_comm (a b : ℕ → ℝ≥0∞) : seqConv a b = seqConv b a := by
  funext n
  rw [seqConv, seqConv, mul_comm]

/-- The `k`-th convolution power `a^{k∗}` (MT, p. 39); `a^{0∗}` is the unit mass at `0`. -/
noncomputable def seqConvPow (a : ℕ → ℝ≥0∞) (k : ℕ) (n : ℕ) : ℝ≥0∞ :=
  PowerSeries.coeff n (PowerSeries.mk a ^ k)

/-- Coefficients of a power series rebuild it. -/
theorem mk_coeff_eq (φ : PowerSeries ℝ≥0∞) :
    PowerSeries.mk (fun n => PowerSeries.coeff n φ) = φ := by
  ext n
  simp

/-- The generating function of `a ∗ b` is the product of the generating functions. -/
theorem mk_seqConv (a b : ℕ → ℝ≥0∞) :
    PowerSeries.mk (seqConv a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext n
  rw [PowerSeries.coeff_mk]
  rfl

/-- The generating function of `a^{k∗}` is the `k`-th power of that of `a`. -/
theorem mk_seqConvPow (a : ℕ → ℝ≥0∞) (k : ℕ) :
    PowerSeries.mk (seqConvPow a k) = PowerSeries.mk a ^ k := by
  ext n
  rw [PowerSeries.coeff_mk]
  rfl

/-- `a^{(k+1)∗} = a^{k∗} ∗ a`. -/
theorem seqConvPow_succ (a : ℕ → ℝ≥0∞) (k : ℕ) :
    seqConvPow a (k + 1) = seqConv (seqConvPow a k) a := by
  funext n
  change PowerSeries.coeff n (PowerSeries.mk a ^ (k + 1)) =
    PowerSeries.coeff n (PowerSeries.mk (seqConvPow a k) * PowerSeries.mk a)
  rw [mk_seqConvPow, pow_succ]

/-- One step of the renewal process from an initial law `μ`:
`P(Z₁ = n) = Σ_{j ≤ n} μ(j) p(n − j)`. -/
theorem bind_renewalKernel_singleton (μ : Measure ℕ) (p : Measure ℕ) [SFinite p] (n : ℕ) :
    (μ.bind (renewalKernel p)) {n} = seqConv (fun i => μ {i}) (fun i => p {i}) n := by
  rw [Measure.bind_apply (measurableSet_singleton n) (Kernel.aemeasurable _),
    lintegral_countable', seqConv_eq_sum_range]
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [renewalKernel_apply_singleton,
      ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_comm]
  · intro j hj
    have hj' : ¬ j ≤ n := by
      rw [Finset.mem_range] at hj
      omega
    rw [renewalKernel_apply_singleton, ite_eq_right hj', zero_mul]

/-- **MT, p. 39.** For a delayed renewal process with delay law `a` (the law of `Z₀`) and
increment law `p`, `P(Z_k = n) = a ∗ p^{k∗}(n)`. -/
theorem renewal_law (a : Measure ℕ) (p : Measure ℕ) [IsProbabilityMeasure p] (k n : ℕ) :
    (a.bind (renewalKernel p ^ k)) {n} =
      seqConv (fun i => a {i}) (seqConvPow (fun i => p {i}) k) n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero]
    change (a.bind Kernel.id) {n} = _
    have hid : (⇑(Kernel.id : Kernel ℕ ℕ)) = Measure.dirac := funext Kernel.id_apply
    rw [hid, Measure.bind_dirac]
    change a {n} = PowerSeries.coeff n
      (PowerSeries.mk (fun i => a {i}) * PowerSeries.mk (seqConvPow (fun i => p {i}) 0))
    rw [mk_seqConvPow, pow_zero, mul_one, PowerSeries.coeff_mk]
  | succ k ih =>
    have hstep : a.bind (renewalKernel p ^ (k + 1)) =
        (a.bind (renewalKernel p ^ k)).bind (renewalKernel p) := by
      rw [pow_succ', Measure.bind_bind (Kernel.aemeasurable _) (Kernel.aemeasurable _)]
      rfl
    rw [hstep, bind_renewalKernel_singleton, seqConvPow_succ]
    have hfun : (fun i => (a.bind (renewalKernel p ^ k)) {i}) =
        seqConv (fun i => a {i}) (seqConvPow (fun i => p {i}) k) := funext ih
    rw [hfun]
    change PowerSeries.coeff n (PowerSeries.mk (seqConv (fun i => a {i})
        (seqConvPow (fun i => p {i}) k)) * PowerSeries.mk fun i => p {i}) =
      PowerSeries.coeff n (PowerSeries.mk (fun i => a {i}) *
        PowerSeries.mk (seqConv (seqConvPow (fun i => p {i}) k) fun i => p {i}))
    rw [mk_seqConv, mk_seqConv, mul_assoc]

/-- MT, p. 38: `P(Z₁ = n) = Σ_{j=0}^{n} a(j) p(n − j)`. -/
theorem renewal_law_one (a : Measure ℕ) (p : Measure ℕ) [IsProbabilityMeasure p] (n : ℕ) :
    (a.bind (renewalKernel p)) {n} = ∑ j ∈ Finset.range (n + 1), a {j} * p {n - j} := by
  rw [bind_renewalKernel_singleton, seqConv_eq_sum_range]

/-! ### The forward and backward recurrence time chains -/

/-- The forward recurrence time step: from `k > 1` move to `k − 1`; from `k ≤ 1` (a renewal at
the next time) take a fresh lifetime `y ~ p`. -/
def fwdStep (q : ℕ × ℕ) : ℕ := if 1 < q.1 then q.1 - 1 else q.2

/-- The forward recurrence time (residual lifetime) chain `V⁺` (MT, (RT1), p. 39). -/
noncomputable def forwardKernel (p : Measure ℕ) : Kernel ℕ ℕ := recursionKernel p fwdStep

/-- The forward recurrence time chain is a Markov kernel. -/
theorem isMarkovKernel_forwardKernel (p : Measure ℕ) [IsProbabilityMeasure p] :
    IsMarkovKernel (forwardKernel p) :=
  isMarkovKernel_recursionKernel p (measurable_of_countable _)

/-- MT, p. 39: from `k > 1` the forward recurrence time moves deterministically to `k − 1`. -/
theorem forwardKernel_of_one_lt (p : Measure ℕ) [IsProbabilityMeasure p] {k : ℕ} (hk : 1 < k) :
    forwardKernel p k = Measure.dirac (k - 1) := by
  rw [forwardKernel, recursionKernel_apply p (measurable_of_countable _)]
  have : (fun w => fwdStep (k, w)) = fun _ => k - 1 := by
    funext w
    simp [fwdStep, hk]
  rw [this, Measure.map_const, measure_univ, one_smul]

/-- MT, p. 39: from `1` a renewal occurs and the new forward recurrence time has law `p`. -/
theorem forwardKernel_one (p : Measure ℕ) [SFinite p] : forwardKernel p 1 = p := by
  rw [forwardKernel, recursionKernel_apply p (measurable_of_countable _)]
  have : (fun w => fwdStep (1, w)) = id := by
    funext w
    simp [fwdStep]
  rw [this, Measure.map_id]

/-- The conditional renewal probability (hazard) at age `j`: `p(j + 1)/p(j, ∞)`. -/
noncomputable def hazard (p : Measure ℕ) (j : ℕ) : ℝ≥0∞ := p {j + 1} / p (Ioi j)

/-- The hazard is a probability. -/
theorem hazard_le_one (p : Measure ℕ) (j : ℕ) : hazard p j ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono (by simp))

/-- The backward recurrence time (age) chain `V⁻` (MT, (RT2), p. 39): from age `j` it drops to
`0` with the conditional probability of a renewal and otherwise ages by one. -/
noncomputable def backwardKernel (p : Measure ℕ) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun j =>
    hazard p j • Measure.dirac 0 + (1 - hazard p j) • Measure.dirac (j + 1)

/-- The backward transition law from age `j`. -/
theorem backwardKernel_apply (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j = hazard p j • Measure.dirac 0 + (1 - hazard p j) • Measure.dirac (j + 1) :=
  rfl

/-- The backward recurrence time chain is a Markov kernel. -/
theorem isMarkovKernel_backwardKernel (p : Measure ℕ) : IsMarkovKernel (backwardKernel p) := by
  refine ⟨fun j => ⟨?_⟩⟩
  simp only [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le (hazard_le_one p j)

/-- From age `j` the chain is renewed with probability `p(j + 1)/p(j, ∞)`. -/
theorem backwardKernel_apply_zero (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j {0} = hazard p j := by
  rw [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  simp [indicator]

/-- From age `j` the chain ages by one with probability `1 − p(j + 1)/p(j, ∞)`. -/
theorem backwardKernel_apply_succ (p : Measure ℕ) (j : ℕ) :
    backwardKernel p j {j + 1} = 1 - hazard p j := by
  rw [backwardKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply]
  simp [indicator]

/-! ### Pathwise recurrence times -/

/-- The forward recurrence time `V⁺(n) = inf(Zₘ − n : Zₘ > n)` of a sequence of renewal epochs
(MT, (RT1), p. 39). -/
noncomputable def fwdTime (Z : ℕ → ℕ) (n : ℕ) : ℕ := sInf {d | ∃ m, n < Z m ∧ d = Z m - n}

/-- The backward recurrence time `V⁻(n) = inf(n − Zₘ : Zₘ ≤ n)` (MT, (RT2), p. 39). -/
noncomputable def bwdTime (Z : ℕ → ℕ) (n : ℕ) : ℕ := sInf {d | ∃ m, Z m ≤ n ∧ d = n - Z m}

/-- The set in (RT1) is nonempty for a strictly increasing sequence of epochs. -/
theorem fwdTime_set_nonempty {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) :
    {d | ∃ m, n < Z m ∧ d = Z m - n}.Nonempty :=
  ⟨Z (n + 1) - n, n + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (hZ.id_le (n + 1)), rfl⟩

/-- `V⁺(n) ≥ 1`. -/
theorem one_le_fwdTime {Z : ℕ → ℕ} (hZ : StrictMono Z) (n : ℕ) : 1 ≤ fwdTime Z n := by
  obtain ⟨m, hm, hd⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [fwdTime, hd]
  omega

/-- **MT, p. 39.** If `V⁺(n) = k > 1`, then one time unit later `V⁺(n + 1) = k − 1`. -/
theorem fwdTime_succ_of_one_lt {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ}
    (h : 1 < fwdTime Z n) : fwdTime Z (n + 1) = fwdTime Z n - 1 := by
  have hno : ∀ m, Z m ≠ n + 1 := fun m hm => by
    have := Nat.sInf_le (s := {d | ∃ m, n < Z m ∧ d = Z m - n}) ⟨m, by omega, rfl⟩
    rw [← fwdTime] at this
    omega
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [← fwdTime] at hd₀
  apply le_antisymm
  · refine Nat.sInf_le ⟨m₀, ?_, ?_⟩
    · have := hno m₀
      omega
    · omega
  · obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ (n + 1))
    rw [← fwdTime] at hd₁
    have := Nat.sInf_le (s := {d | ∃ m, n < Z m ∧ d = Z m - n}) ⟨m₁, by omega, rfl⟩
    rw [← fwdTime] at this
    omega

/-- **MT, p. 39.** If `V⁺(n) = 1`, a renewal occurs at `n + 1`, say `Z_{m₀} = n + 1`, and the new
forward recurrence time is the next lifetime `V⁺(n + 1) = Z_{m₀+1} − Z_{m₀}`. -/
theorem fwdTime_succ_of_eq_one {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ} (h : fwdTime Z n = 1) :
    ∃ m₀, Z m₀ = n + 1 ∧ fwdTime Z (n + 1) = Z (m₀ + 1) - Z m₀ := by
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ n)
  rw [← fwdTime, h] at hd₀
  have hZm₀ : Z m₀ = n + 1 := by omega
  refine ⟨m₀, hZm₀, le_antisymm ?_ ?_⟩
  · refine Nat.sInf_le ⟨m₀ + 1, ?_, by rw [hZm₀]⟩
    have := hZ (Nat.lt_add_one m₀)
    omega
  · obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem (fwdTime_set_nonempty hZ (n + 1))
    rw [← fwdTime] at hd₁
    have hlt : m₀ < m₁ := hZ.lt_iff_lt.mp (by omega)
    have := hZ.monotone (show m₀ + 1 ≤ m₁ by omega)
    omega

/-- **Correction to (RT2).** Before the first renewal the set in (RT2) is empty, so `V⁻(n)` is
undefined for `n < Z₀`; e.g. for the epochs `Zₘ = m + 1` at `n = 0`. -/
theorem bwdTime_set_empty {Z : ℕ → ℕ} (hZ : StrictMono Z) {n : ℕ} (hn : n < Z 0) :
    {d | ∃ m, Z m ≤ n ∧ d = n - Z m} = ∅ := by
  ext d
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro m hm
  have := hZ.monotone (Nat.zero_le m)
  omega

/-- The concrete instance: the epochs `Zₘ = m + 1` have no renewal at or before `n = 0`. -/
theorem bwdTime_set_empty_example : {d | ∃ m, m + 1 ≤ 0 ∧ d = 0 - (m + 1)} = (∅ : Set ℕ) :=
  bwdTime_set_empty (Z := fun m => m + 1) (fun _ _ h => by simpa using h) Nat.one_pos

/-- **MT, p. 39.** At a renewal epoch the age drops to `0`. -/
theorem bwdTime_succ_of_renewal {Z : ℕ → ℕ} {n m : ℕ} (hm : Z m = n + 1) :
    bwdTime Z (n + 1) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨m, hm.le, by omega⟩)

/-- **MT, p. 39.** Between renewals the age increases by one: if `Z₀ ≤ n` and no renewal occurs at
`n + 1`, then `V⁻(n + 1) = V⁻(n) + 1`. -/
theorem bwdTime_succ_of_not_renewal {Z : ℕ → ℕ} {n : ℕ} (h0 : Z 0 ≤ n)
    (hno : ∀ m, Z m ≠ n + 1) : bwdTime Z (n + 1) = bwdTime Z n + 1 := by
  have h1 : {d | ∃ m, Z m ≤ n ∧ d = n - Z m}.Nonempty := ⟨n - Z 0, 0, h0, rfl⟩
  have h2 : {d | ∃ m, Z m ≤ n + 1 ∧ d = n + 1 - Z m}.Nonempty := ⟨n + 1 - Z 0, 0, by omega, rfl⟩
  obtain ⟨m₀, hm₀, hd₀⟩ := Nat.sInf_mem h1
  obtain ⟨m₁, hm₁, hd₁⟩ := Nat.sInf_mem h2
  rw [← bwdTime] at hd₀ hd₁
  apply le_antisymm
  · have := Nat.sInf_le (s := {d | ∃ m, Z m ≤ n + 1 ∧ d = n + 1 - Z m}) ⟨m₀, by omega, rfl⟩
    rw [← bwdTime] at this
    omega
  · have hm₁' : Z m₁ ≤ n := by
      have := hno m₁
      omega
    have := Nat.sInf_le (s := {d | ∃ m, Z m ≤ n ∧ d = n - Z m}) ⟨m₁, hm₁', rfl⟩
    rw [← bwdTime] at this
    omega

/-! ### Continuous time recurrence processes and their skeletons -/

/-- The forward recurrence time process `V⁺(t) = inf(Zₙ − t : Zₙ > t, n ≥ 1)` of a renewal process
in continuous time with epochs `Zₙ` (MT, (RT3), p. 543). -/
noncomputable def fwdTimeCts (Z : ℕ → ℝ) (t : ℝ) : ℝ :=
  sInf {d | ∃ n, 1 ≤ n ∧ t < Z n ∧ d = Z n - t}

/-- The backward recurrence time process `V⁻(t) = inf(t − Zₙ : Zₙ ≤ t, n ≥ 1)` (MT, (RT4)). -/
noncomputable def bwdTimeCts (Z : ℕ → ℝ) (t : ℝ) : ℝ :=
  sInf {d | ∃ n, 1 ≤ n ∧ Z n ≤ t ∧ d = t - Z n}

/-- The forward recurrence time `δ`-skeleton `V⁺_δ(n) = V⁺(nδ)` (MT, (RT3)). -/
noncomputable def fwdSkeleton (Z : ℕ → ℝ) (δ : ℝ) (n : ℕ) : ℝ := fwdTimeCts Z (n * δ)

/-- The backward recurrence time `δ`-skeleton `V⁻_δ(n) = V⁻(nδ)` (MT, (RT4)). -/
noncomputable def bwdSkeleton (Z : ℕ → ℝ) (δ : ℝ) (n : ℕ) : ℝ := bwdTimeCts Z (n * δ)

end MeynTweedie.LimitTheorems
