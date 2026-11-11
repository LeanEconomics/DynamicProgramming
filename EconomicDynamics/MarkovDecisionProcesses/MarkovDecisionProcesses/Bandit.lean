/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Objective
import MarkovDecisionProcesses.KernelTools
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The bandit model

Miao, §5.2.3, pp. 149–152, and Exercise 5.4, p. 155. `k` arms with state spaces `X i` and
transition functions `Q^i_{t+1}` (`Bandit.Q i t`); choosing arm `i` pays `u^i_t(s^i_t)`, moves
arm `i` by `Q^i_{t+1}` and freezes the others (`armKernel`). The MDP has state space
`S = X 1 × ⋯ × X k`, actions `A = {1, …, k}` (here `Fin k`) and `Γ(s) = A` (`Bandit.toMDP`).

* `bandit_P_apply`, `bandit_P_rect`: `P_{t+1}(s, i; ·)` is the law of `s` with its `i`-th
  coordinate redrawn from `Q^i_{t+1}(s^i, ·)`; on the sets `{s¹} × ⋯ × Bⁱ × ⋯ × {sᵏ}` of the
  book it is `Q^i_{t+1}(s^i, Bⁱ)` (`bandit_P_rect` uses `{x : xⁱ ∈ Bⁱ}`, which has the same
  measure because the other coordinates are frozen, `bandit_P_frozen`).
* **Correction.** The book adds "`P_{t+1}(s, i; B) = 0` for all other `B`" (p. 150). Taken
  literally this is false: `B = S` is not of the displayed form but has probability one
  (`bandit_book_false`). The correct statement is that `P_{t+1}(s, i; B) = 0` for every
  measurable `B` disjoint from the fibre `{x : xʲ = sʲ for j ≠ i}` (`bandit_P_frozen`).
* `bandit_assumptions`: stochastic kernels, Assumption 5.1.1, and with bounded measurable
  rewards Assumptions 5.1.3 and (stationary, `β < 1`) 5.1.4.
* **A constant arm makes the bandit a stopping problem** (p. 151), proved for a deterministic
  stochastic arm (`ex_bandit_constant_arm`): for any sequence of arm choices over `T` periods
  there is a retirement date `K` such that playing the risky arm `K` times and then the constant
  arm forever does at least as well. The key step is that playing the constant arm once and then
  `K` times the risky arm is the convex combination `β·R_K + (1 − β)·R_0` of two retirement
  payoffs (`retirePay_shift`). (For a stochastic risky arm the same interchange applies along
  each path, but turning it into an inequality between values requires the dynamic programming
  results of Chapters 6–7 and is not formalised.)
* Task selection (p. 151): `taskSelection` with `u^i(s) = R_i p_i(C | s)` on `S_i = [0, 1]`
  (`taskSelection_assumptions`).
* **Exercise 5.4** (Pandora's problem as a bandit): `pandora` (`ex_5_4`, `ex_5_4_collect`).
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {k : ℕ} {X : Fin k → Type*} [∀ i, MeasurableSpace (X i)]

/-- The data of a bandit problem with `k` arms (Miao, p. 150). -/
structure Bandit (k : ℕ) (X : Fin k → Type*) [∀ i, MeasurableSpace (X i)] where
  Q : (i : Fin k) → ℕ → Kernel (X i) (X i)
  r : (i : Fin k) → ℕ → X i → ℝ
  β : ℝ

/-- The kernel of the bandit after choosing arm `i`: redraw `sⁱ` from `Q^i_{t+1}(sⁱ, ·)`, keep
the other coordinates. -/
noncomputable def armKernel (i : Fin k) (Q : Kernel (X i) (X i)) :
    Kernel ((j : Fin k) → X j) ((j : Fin k) → X j) :=
  pushKernel (Q.comap (fun s => s i) (measurable_pi_apply i)) fun p => Function.update p.1 i p.2

/-- The bandit model as a Markov decision process (Miao, p. 150). -/
noncomputable def Bandit.toMDP (b : Bandit k X) : MDP ((j : Fin k) → X j) (Fin k) where
  Γ := fun _ => Set.univ
  P := fun t => famKernel fun i => armKernel i (b.Q i t)
  u := fun t x => b.r x.2 t (x.1 x.2)
  uT := fun _ => 0
  β := b.β

theorem armKernel_apply (i : Fin k) (Q : Kernel (X i) (X i)) [IsMarkovKernel Q]
    (s : (j : Fin k) → X j) : armKernel i Q s = (Q (s i)).map (Function.update s i) :=
  pushKernel_apply _ measurable_update' s

/-- Miao, p. 150: after choosing arm `i`, `P_{t+1}(s, i; C) = Q^i_{t+1}(sⁱ, {y : (s with sⁱ := y)
∈ C})`. -/
theorem bandit_P_apply (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {C : Set ((j : Fin k) → X j)} (hC : MeasurableSet C) :
    b.toMDP.P t (s, i) C = b.Q i t (s i) (Function.update s i ⁻¹' C) := by
  change armKernel i (b.Q i t) s C = _
  rw [armKernel_apply, Measure.map_apply (measurable_update s) hC]

/-- Miao, p. 150: the chosen arm moves by its own transition function,
`P_{t+1}(s, i; {x : xⁱ ∈ Bⁱ}) = Q^i_{t+1}(sⁱ, Bⁱ)`. -/
theorem bandit_P_rect (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {B : Set (X i)} (hB : MeasurableSet B) :
    b.toMDP.P t (s, i) ((fun x => x i) ⁻¹' B) = b.Q i t (s i) B := by
  rw [bandit_P_apply b s (measurable_pi_apply i hB)]
  congr 1
  ext y
  simp

/-- **Correction to Miao, p. 150.** The other arms are frozen: `P_{t+1}(s, i; B) = 0` for every
measurable `B` that contains no point `x` with `xʲ = sʲ` for all `j ≠ i`. -/
theorem bandit_P_frozen (b : Bandit k X) {i : Fin k} {t : ℕ} [IsMarkovKernel (b.Q i t)]
    (s : (j : Fin k) → X j) {B : Set ((j : Fin k) → X j)} (hB : MeasurableSet B)
    (hdisj : ∀ x ∈ B, ∃ j ≠ i, x j ≠ s j) : b.toMDP.P t (s, i) B = 0 := by
  rw [bandit_P_apply b s hB]
  have : Function.update s i ⁻¹' B = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨j, hji, hj⟩ := hdisj _ hy
    exact hj (Function.update_of_ne hji _ _)
  rw [this, measure_empty]

/-- **Correction to Miao, p. 150** (counterexample). With two arms on `Bool` (each moving
deterministically), the whole state space `B = S` is not of the form
`{x : x⁰ ∈ B⁰, x¹ = s¹}` used by the book, yet `P(s, 0; S) = 1 ≠ 0`. -/
theorem bandit_book_false (s : Fin 2 → Bool) :
    (¬ ∃ B : Set Bool, (Set.univ : Set (Fin 2 → Bool)) = {x | x 0 ∈ B ∧ x 1 = s 1}) ∧
      (⟨fun _ _ => Kernel.id, fun _ _ _ => 0, 1 / 2⟩ : Bandit 2 fun _ => Bool).toMDP.P 0 (s, 0)
        Set.univ = 1 := by
  refine ⟨fun ⟨B, hB⟩ => ?_, ?_⟩
  · have hmem : (fun j : Fin 2 => if j = 1 then !s 1 else s 0) ∈
        (Set.univ : Set (Fin 2 → Bool)) := Set.mem_univ _
    rw [hB] at hmem
    have h := hmem.2
    simp at h
  · have : IsMarkovKernel (armKernel (X := fun _ : Fin 2 => Bool) 0 Kernel.id) := by
      unfold armKernel
      exact isMarkovKernel_pushKernel _ measurable_update'
    change (armKernel (X := fun _ : Fin 2 => Bool) 0 Kernel.id) s Set.univ = 1
    exact measure_univ

theorem bandit_isMarkov (b : Bandit k X) (hQ : ∀ i t, IsMarkovKernel (b.Q i t)) :
    b.toMDP.IsMarkov := fun t => by
  change IsMarkovKernel (famKernel fun i => armKernel i (b.Q i t))
  refine isMarkovKernel_famKernel fun i => ?_
  have := hQ i t
  unfold armKernel
  exact isMarkovKernel_pushKernel _ measurable_update'

/-- The bandit MDP satisfies the assumptions of §5.1: stochastic kernels, Assumption 5.1.1, and
with rewards bounded by `B` and measurable, Assumption 5.1.3 for every horizon and, when the arms
are time-homogeneous and `0 ≤ β < 1`, Assumption 5.1.4. -/
theorem bandit_assumptions (b : Bandit k X) (hQ : ∀ i t, IsMarkovKernel (b.Q i t))
    (hr : ∀ i t, Measurable (b.r i t)) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i t x, |b.r i t x| ≤ B) :
    b.toMDP.IsMarkov ∧ (k ≠ 0 → HasMeasurableSelection b.toMDP.Γ) ∧
      (∀ T, Assumption513 b.toMDP T) ∧
      ((∀ i t, b.Q i t = b.Q i 0 ∧ b.r i t = b.r i 0) → 0 ≤ b.β → b.β < 1 →
        Assumption514 b.toMDP) := by
  have hP := bandit_isMarkov b hQ
  have hu : ∀ t x, |b.toMDP.u t x| ≤ B := fun t x => hB _ _ _
  have hmu : ∀ t, Measurable (b.toMDP.u t) := fun t =>
    measurable_from_prod_countable_left fun i => (hr i t).comp (measurable_pi_apply i)
  refine ⟨hP, fun hk => ⟨fun _ => ⟨0, Nat.pos_of_ne_zero hk⟩, measurable_const,
    fun _ => Set.mem_univ _⟩, fun T => assumption_5_1_3_of_bounded hP ⟨hu, fun _ => by
      simpa [Bandit.toMDP] using hB0⟩ hmu measurable_const T,
    fun hst hβ0 hβ1 => assumption_5_1_4_of_bounded hP (fun t => ?_) hu hmu hβ0 hβ1⟩
  have h1 : (fun i => b.Q i t) = fun i => b.Q i 0 := funext fun i => (hst i t).1
  have h2 : (fun i => b.r i t) = fun i => b.r i 0 := funext fun i => (hst i t).2
  refine ⟨?_, ?_⟩
  · change (famKernel fun i => armKernel i (b.Q i t)) = famKernel fun i => armKernel i (b.Q i 0)
    simp only [(hst _ t).1]
  · change (fun x : ((j : Fin k) → X j) × Fin k => b.r x.2 t (x.1 x.2)) =
      fun x => b.r x.2 0 (x.1 x.2)
    simp only [(hst _ t).2]

/-- The payoff of a sequence of arm choices in the two-armed bandit with a constant arm: `a = 0`
plays the risky arm, whose rewards in the order they are drawn are `r 0, r 1, …`; `a = 1` plays
the constant arm, paying `c` and leaving the risky arm frozen. -/
def banditPay (β c : ℝ) : (T : ℕ) → (ℕ → Fin 2) → (ℕ → ℝ) → ℝ
  | 0, _, _ => 0
  | T + 1, a, r => if a 0 = 0 then r 0 + β * banditPay β c T (a ∘ Nat.succ) (r ∘ Nat.succ)
      else c + β * banditPay β c T (a ∘ Nat.succ) r

/-- The payoff of retiring at `K`: the risky arm for `K` periods, then the constant arm. -/
def retirePay (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, β ^ j * r j +
    c * (∑ j ∈ Finset.range T, β ^ j - ∑ j ∈ Finset.range K, β ^ j)

/-- Retirement at `K`: the action sequence `0, …, 0, 1, 1, …`. -/
def retireSeq (K : ℕ) (t : ℕ) : Fin 2 := if t < K then 0 else 1

theorem geom_succ (β : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), β ^ j = 1 + β * ∑ j ∈ Finset.range n, β ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem retirePay_succ (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) :
    retirePay β c (T + 1) r (K + 1) = r 0 + β * retirePay β c T (r ∘ Nat.succ) K := by
  simp only [retirePay, geom_succ]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Function.comp_apply]
  have : ∑ j ∈ Finset.range K, β ^ (j + 1) * r (j + 1) =
      β * ∑ j ∈ Finset.range K, β ^ j * r (j + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- Playing the constant arm first and then retiring at `K` is the convex combination
`β·R_K + (1 − β)·R_0` of retirement payoffs. -/
theorem retirePay_shift (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) (K : ℕ) :
    c + β * retirePay β c T r K =
      β * retirePay β c (T + 1) r K + (1 - β) * retirePay β c (T + 1) r 0 := by
  simp only [retirePay, geom_succ, Finset.range_zero, Finset.sum_empty]
  ring

theorem banditPay_retireSeq (β c : ℝ) (T : ℕ) (r : ℕ → ℝ) {K : ℕ} (hK : K ≤ T) :
    banditPay β c T (retireSeq K) r = retirePay β c T r K := by
  induction T generalizing K r with
  | zero =>
    have : K = 0 := by omega
    subst this
    simp [banditPay, retirePay]
  | succ T ih =>
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · subst hK0
      have hseq : retireSeq 0 ∘ Nat.succ = retireSeq 0 := funext fun t => by simp [retireSeq]
      have h0 : retireSeq 0 0 ≠ 0 := by simp [retireSeq]
      simp only [banditPay, h0, ↓reduceIte, hseq, ih r (Nat.zero_le T)]
      simp only [retirePay, geom_succ, Finset.range_zero, Finset.sum_empty]
      ring
    · obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hseq : retireSeq (K' + 1) ∘ Nat.succ = retireSeq K' := funext fun t => by
        simp only [retireSeq, Function.comp_apply]
        split_ifs <;> omega
      have h0 : retireSeq (K' + 1) 0 = 0 := by simp [retireSeq]
      simp only [banditPay, h0, ↓reduceIte, hseq]
      rw [ih _ (by omega), retirePay_succ]

/-- **The two-armed bandit with a constant arm is an optimal stopping problem** (Miao, p. 151),
for a deterministic risky arm with reward sequence `r` and `β ∈ [0, 1]`: every sequence of arm
choices is weakly dominated by a retirement rule, so the best payoff is attained by stopping. -/
theorem ex_bandit_constant_arm {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (c : ℝ) (T : ℕ)
    (a : ℕ → Fin 2) (r : ℕ → ℝ) :
    ∃ K ≤ T, banditPay β c T a r ≤ banditPay β c T (retireSeq K) r := by
  suffices h : ∃ K ≤ T, banditPay β c T a r ≤ retirePay β c T r K by
    obtain ⟨K, hK, h⟩ := h
    exact ⟨K, hK, h.trans_eq (banditPay_retireSeq β c T r hK).symm⟩
  induction T generalizing a r with
  | zero => exact ⟨0, le_rfl, by simp [banditPay, retirePay]⟩
  | succ T ih =>
    by_cases ha : a 0 = 0
    · obtain ⟨K, hK, h⟩ := ih (a ∘ Nat.succ) (r ∘ Nat.succ)
      refine ⟨K + 1, by omega, ?_⟩
      simp only [banditPay, ha, ↓reduceIte]
      rw [retirePay_succ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hβ0)
    · obtain ⟨K, hK, h⟩ := ih (a ∘ Nat.succ) r
      have hpay : banditPay β c (T + 1) a r ≤
          β * retirePay β c (T + 1) r K + (1 - β) * retirePay β c (T + 1) r 0 := by
        simp only [banditPay, ha, ↓reduceIte]
        rw [← retirePay_shift]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hβ0)
      rcases le_total (retirePay β c (T + 1) r 0) (retirePay β c (T + 1) r K) with hle | hle
      · refine ⟨K, by omega, hpay.trans ?_⟩
        nlinarith
      · refine ⟨0, by omega, hpay.trans ?_⟩
        nlinarith

/-- The task selection problem (Miao, p. 151): `k` tasks with completion states in `[0, 1]`,
reward `u^i(s) = R_i p_i(C | s)` when working on task `i`. -/
def taskSelection (Q : (i : Fin k) → Kernel (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1))
    (R : Fin k → ℝ) (p : Fin k → Set.Icc (0 : ℝ) 1 → ℝ) (β : ℝ) :
    Bandit k fun _ => Set.Icc (0 : ℝ) 1 where
  Q := fun i _ => Q i
  r := fun i _ s => R i * p i s
  β := β

/-- The task selection problem satisfies Assumptions 5.1.1 and 5.1.4 (for `k ≥ 1`,
probabilities `p_i ∈ [0, 1]` measurable, `β ∈ [0, 1)`). -/
theorem taskSelection_assumptions {Q : (i : Fin k) → Kernel (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)}
    (hQ : ∀ i, IsMarkovKernel (Q i)) {R : Fin k → ℝ} {p : Fin k → Set.Icc (0 : ℝ) 1 → ℝ}
    (hp : ∀ i, Measurable (p i)) (hp01 : ∀ i s, 0 ≤ p i s ∧ p i s ≤ 1) (hk : k ≠ 0) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (taskSelection Q R p β).toMDP.IsMarkov ∧
      HasMeasurableSelection (taskSelection Q R p β).toMDP.Γ ∧
      Assumption514 (taskSelection Q R p β).toMDP := by
  have hB : ∀ i t x, |(taskSelection Q R p β).r i t x| ≤ ∑ j, |R j| := by
    intro i t x
    simp only [taskSelection, abs_mul]
    calc |R i| * |p i x| ≤ |R i| * 1 := mul_le_mul_of_nonneg_left
          (by rw [abs_of_nonneg (hp01 i x).1]; exact (hp01 i x).2) (abs_nonneg _)
      _ ≤ ∑ j, |R j| := by
          rw [mul_one]
          exact Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)
  obtain ⟨h1, h2, -, h4⟩ := bandit_assumptions (taskSelection Q R p β) (fun i _ => hQ i)
    (fun i _ => measurable_const.mul (hp i)) (Finset.sum_nonneg fun j _ => abs_nonneg _) hB
  exact ⟨h1, h2 hk, h4 (fun _ _ => ⟨rfl, rfl⟩) hβ0 hβ1⟩

/-- The transitions of a box in Pandora's problem: a closed box (`Sum.inl ()`) is opened and its
prize `y ~ F` revealed; an open box (`Sum.inr y`) stays as it is. -/
noncomputable def pandoraKernel {Y : Type*} [MeasurableSpace Y] (F : Measure Y) :
    Kernel (Unit ⊕ Y) (Unit ⊕ Y) where
  toFun := Sum.elim (fun _ => F.map Sum.inr) fun y => Measure.dirac (Sum.inr y)
  measurable' := measurable_const.sumElim (Measure.measurable_dirac.comp measurable_inr)

/-- **Exercise 5.4** (Miao, p. 155): Pandora's problem as a bandit. Box `i` is an arm with
states "closed" and "open with prize `y`"; pulling a closed box costs `cᵢ` and reveals
`y ~ Fᵢ`; pulling an open box with prize `y` pays `(1 − β) vᵢ(y)` and leaves it unchanged, so
that collecting the prize (pulling it forever) is worth `vᵢ(y)` (`ex_5_4_collect`). The outside
option `x₀` is an arm that starts open. Departures: a common discount factor `β` (the book's
`βᵢ = e^{−r tᵢ}` allows box-specific delays, which a bandit with one discount factor cannot
express without a time change), and "collect and stop" is represented by retiring on the open
box. -/
noncomputable def pandora {Y : Fin k → Type*} [∀ i, MeasurableSpace (Y i)]
    (F : (i : Fin k) → Measure (Y i)) (c : Fin k → ℝ) (v : (i : Fin k) → Y i → ℝ) (β : ℝ) :
    Bandit k fun i => Unit ⊕ Y i where
  Q := fun i _ => pandoraKernel (F i)
  r := fun i _ => Sum.elim (fun _ => -c i) fun y => (1 - β) * v i y
  β := β

/-- **Exercise 5.4**: collecting a prize of value `v` from an open box is worth `v`:
`∑ βᵗ (1 − β) v = v`. -/
theorem ex_5_4_collect {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (v : ℝ) :
    HasSum (fun t : ℕ => β ^ t * ((1 - β) * v)) v := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right ((1 - β) * v)
  have hne : (1 - β) ≠ 0 := by linarith
  convert h using 1
  field_simp

/-- **Exercise 5.4**: with probability distributions `Fᵢ`, measurable bounded prize values and
`β ∈ (0, 1)`, Pandora's bandit satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4. -/
theorem ex_5_4 {Y : Fin k → Type*} [∀ i, MeasurableSpace (Y i)]
    {F : (i : Fin k) → Measure (Y i)} (hF : ∀ i, IsProbabilityMeasure (F i)) (c : Fin k → ℝ)
    {v : (i : Fin k) → Y i → ℝ} (hv : ∀ i, Measurable (v i)) {B : ℝ}
    (hB : ∀ i y, |v i y| ≤ B) (hk : k ≠ 0) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (pandora F c v β).toMDP.IsMarkov ∧ HasMeasurableSelection (pandora F c v β).toMDP.Γ ∧
      Assumption512 (pandora F c v β).toMDP ∧ Assumption514 (pandora F c v β).toMDP := by
  have hQ : ∀ i t, IsMarkovKernel ((pandora F c v β).Q i t) := by
    intro i t
    refine ⟨fun x => ?_⟩
    have := hF i
    cases x with
    | inl _ => exact inferInstanceAs (IsProbabilityMeasure ((F i).map Sum.inr))
    | inr y => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  have hb : ∀ i t x, |(pandora F c v β).r i t x| ≤ ∑ j, |c j| + max B 0 := by
    intro i t x
    have hc : |c i| ≤ ∑ j, |c j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
    have hs : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    cases x with
    | inl _ =>
      simp only [pandora, Sum.elim_inl, abs_neg]
      linarith [le_max_right B 0]
    | inr y =>
      simp only [pandora, Sum.elim_inr, abs_mul]
      have h1 : |1 - β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 : |v i y| ≤ max B 0 := (hB i y).trans (le_max_left _ _)
      nlinarith [abs_nonneg (1 - β), abs_nonneg (v i y), le_max_right B 0]
  obtain ⟨h1, h2, -, h4⟩ := bandit_assumptions (pandora F c v β) hQ
    (fun i _ => measurable_const.sumElim (measurable_const.mul (hv i)))
    (add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (le_max_right B 0)) hb
  exact ⟨h1, h2 hk, ⟨hβ0, hβ1⟩, h4 (fun _ _ => ⟨rfl, rfl⟩) hβ0.le hβ1⟩

end Miao.MarkovDecisionProcesses
