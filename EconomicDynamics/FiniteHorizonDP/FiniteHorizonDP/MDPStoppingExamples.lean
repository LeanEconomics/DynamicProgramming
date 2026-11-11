/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.MDPOptimalStopping
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Examples of optimal stopping problems

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `StoppingExamples`),
with the namespace renamed.

Miao, §5.2.2, pp. 146–149, and Exercises 5.1–5.3, p. 155. Each problem is an instance of
`StoppingProblem`, so `V0_toMDP`/`V_toMDP` identify it with its Markov decision problem, and
`toMDP_assumptions` gives the assumptions of §5.1 once the payoffs are bounded.

* Option exercise (5.7)–(5.8): `g_t(z) = y(z) − I`, `f_t = 0` (`optionExercise`,
  `optionExercise_assumptions`); the American call with `β = 1/(1 + r)` (`americanCall_beta`).
  Payoffs are `y(z_t)` for a measurable payoff function `y` (the book takes `y(z) = z`); the
  assumptions are proved for bounded `y`.
* Exit (5.9)–(5.10): `g_t = ξ`, `f_t = ϕ − c_f` (`exitProblem`, `exitProblem_assumptions`).
* Secretary problem (pp. 147–149): `secretary`, with the book's transition function and rewards,
  dates shifted by one (MDP date `t` is the book's `t + 1`). Its kernels are stochastic kernels
  and Assumption 5.1.3 holds (`secretary_assumptions`). The probability `t/N` is derived in
  `Secretary`. **Note:** the criterion is a probability, so `β = 1`, outside Assumption 5.1.2;
  for finite horizons nothing in §5.1 needs `β < 1` (as the book itself remarks on p. 140).
* **Exercise 5.1** (job search): `jobSearch`; accepting `w` is stopping with payoff
  `w/(1 − β) = ∑ βᵗ w` (`ex_5_1_accept`); assumptions (`ex_5_1`).
* **Exercise 5.2** (American put): `americanPut`, finite horizon with terminal payoff
  `max(K − p(z_T), 0)` (`ex_5_2`).
* **Exercise 5.3** (best-two secretary): `secretaryTwo` (`ex_5_3`); the relative-rank state has
  three values and the rewards are the conditional probabilities that a candidate of relative rank
  1 or 2 among the first `k` is among the two best of `N` (their derivation is in the docstring and
  is not formalised).
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z]

/-- The irreversible investment (option exercise) problem (Miao, pp. 146–147). -/
def optionExercise (Q : Kernel Z Z) (y : Z → ℝ) (I β : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ _ => 0
  g := fun _ z => y z - I
  h := fun _ => 0
  β := β

/-- Miao (5.7)–(5.8): `g_t(z_t) = z_t − I`, `f_t(z_t) = 0`. -/
theorem eq_5_7_5_8 (Q : Kernel Z Z) (y : Z → ℝ) (I β : ℝ) (t : ℕ) (z : Z) :
    (optionExercise Q y I β).g t z = y z - I ∧ (optionExercise Q y I β).f t z = 0 :=
  ⟨rfl, rfl⟩

/-- The option exercise problem satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when the payoff is
measurable and bounded and `β ∈ (0, 1)`. -/
theorem optionExercise_assumptions {Q : Kernel Z Z} [IsMarkovKernel Q] {y : Z → ℝ}
    (hy : Measurable y) {B : ℝ} (hB : ∀ z, |y z| ≤ B) {I β : ℝ} (hI : 0 ≤ I) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (optionExercise Q y I β).toMDP.IsMarkov ∧
      HasMeasurableSelection (optionExercise Q y I β).toMDP.Γ ∧
      Assumption512 (optionExercise Q y I β).toMDP ∧
      Assumption514 (optionExercise Q y I β).toMDP := by
  have hb : (optionExercise Q y I β).Bounded (max B 0 + I) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · simp only [optionExercise, abs_zero]
      positivity
    · calc |y z - I| ≤ |y z| + |I| := abs_sub _ _
        _ ≤ max B 0 + I := by rw [abs_of_nonneg hI]; linarith [hB z, le_max_left B 0]
    · simp only [optionExercise, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (optionExercise Q y I β) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => measurable_const) (fun _ => hy.sub_const I) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- Miao, p. 147: for the American call, `β = 1/(1 + r)`, which lies in `(0, 1)` when the
interest rate `r` is positive. -/
theorem americanCall_beta {r : ℝ} (hr : 0 < r) : 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 :=
  ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩

/-- The exit problem (Miao, p. 147): staying earns `ϕ(z) − c_f`, exiting earns `ξ`. -/
def exitProblem (Q : Kernel Z Z) (φ : Z → ℝ) (cf ξ β : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ z => φ z - cf
  g := fun _ _ => ξ
  h := fun _ => 0
  β := β

/-- Miao (5.9)–(5.10): `g_t(z_t) = ξ`, `f_t(z_t) = ϕ(z_t) − c_f`. -/
theorem eq_5_9_5_10 (Q : Kernel Z Z) (φ : Z → ℝ) (cf ξ β : ℝ) (t : ℕ) (z : Z) :
    (exitProblem Q φ cf ξ β).g t z = ξ ∧ (exitProblem Q φ cf ξ β).f t z = φ z - cf :=
  ⟨rfl, rfl⟩

/-- The exit problem satisfies Assumptions 5.1.1, 5.1.2 and 5.1.4 when profits are measurable
and bounded and `β ∈ (0, 1)`. -/
theorem exitProblem_assumptions {Q : Kernel Z Z} [IsMarkovKernel Q] {φ : Z → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ z, |φ z| ≤ B) {cf ξ β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (exitProblem Q φ cf ξ β).toMDP.IsMarkov ∧
      HasMeasurableSelection (exitProblem Q φ cf ξ β).toMDP.Γ ∧
      Assumption512 (exitProblem Q φ cf ξ β).toMDP ∧
      Assumption514 (exitProblem Q φ cf ξ β).toMDP := by
  have hb : (exitProblem Q φ cf ξ β).Bounded (max B 0 + |cf| + |ξ|) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · calc |φ z - cf| ≤ |φ z| + |cf| := abs_sub _ _
        _ ≤ max B 0 + |cf| + |ξ| := by linarith [hB z, le_max_left B 0, abs_nonneg ξ]
    · simp only [exitProblem]
      linarith [le_max_right B 0, abs_nonneg cf]
    · simp only [exitProblem, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (exitProblem Q φ cf ξ β) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => hφ.sub_const cf) (fun _ => measurable_const) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- A two-point law: `1` with probability `p`, `0` with probability `1 − p`. -/
noncomputable def bern (p : ℝ) : Measure (Fin 2) :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

theorem isProbabilityMeasure_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bern p) := by
  refine ⟨?_⟩
  simp only [bern, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem bern_one (p : ℝ) :
    bern p {1} = ENNReal.ofReal p ∧ bern p {0} = ENNReal.ofReal (1 - p) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [bern, h10, h10.symm, Set.indicator]

/-- The secretary problem with `N` candidates (Miao, pp. 147–149), with dates shifted by one:
MDP date `t` is the book's `t + 1` (the `(t + 1)`-th candidate). The state is `1` if the
current candidate is the best seen so far; `Q_{t+1}(z, 1) = 1/(t + 1)` becomes
`Q t = bern (1/(t + 2))`; stopping at the `k`-th candidate when `z = 1` pays `k/N`; the terminal
date is the `N`-th candidate, with `h(1) = 1`, `h(0) = 0`; `β = 1`. (`min k N` replaces `k` so
that the payoff is bounded at dates past the horizon, where it plays no role.) -/
noncomputable def secretary (N : ℕ) : StoppingProblem (Fin 2) where
  Q := fun t => Kernel.const _ (bern (1 / (t + 2)))
  f := fun _ _ => 0
  g := fun t z => if z = 1 then (min (t + 1) N : ℕ) / (N : ℝ) else 0
  h := fun z => if z = 1 then 1 else 0
  β := 1

/-- Miao, p. 148: `Q_{t+1}(z, 1) = 1/(t + 1)` and `Q_{t+1}(z, 0) = t/(t + 1)` (in shifted dates,
`Q t(z, ·)` gives `1` probability `1/(t + 2)`), independent of `z`. -/
theorem secretary_Q (N t : ℕ) (z : Fin 2) :
    (secretary N).Q t z {1} = ENNReal.ofReal (1 / (t + 2)) ∧
      (secretary N).Q t z {0} = ENNReal.ofReal ((t + 1) / (t + 2)) := by
  have h0 : (0 : ℝ) ≤ 1 / (t + 2) := by positivity
  have h1 : 1 / ((t : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  obtain ⟨e1, e0⟩ := bern_one (1 / ((t : ℝ) + 2))
  refine ⟨e1, ?_⟩
  rw [show (secretary N).Q t z = bern (1 / (t + 2)) from rfl, e0]
  congr 1
  field_simp
  ring

/-- The secretary problem: the kernels are stochastic kernels, Assumption 5.1.1 holds, and
Assumption 5.1.3 holds for every horizon (rewards lie in `[0, 1]`). -/
theorem secretary_assumptions (N : ℕ) :
    (secretary N).toMDP.IsMarkov ∧ HasMeasurableSelection (secretary N).toMDP.Γ ∧
      ∀ T, Assumption513 (secretary N).toMDP T := by
  have hQ : ∀ t, IsMarkovKernel ((secretary N).Q t) := fun t => by
    have : IsProbabilityMeasure (bern (1 / ((t : ℝ) + 2))) :=
      isProbabilityMeasure_bern (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
  have hb : (secretary N).Bounded 1 := by
    refine ⟨zero_le_one, fun t z => by simp [secretary], fun t z => ?_, fun z => ?_⟩
    · simp only [secretary]
      split_ifs
      · rcases Nat.eq_zero_or_pos N with hN | hN
        · simp [hN]
        · rw [abs_of_nonneg (by positivity), div_le_one (by exact_mod_cast hN)]
          exact_mod_cast min_le_right _ _
      · simp
    · simp only [secretary]
      split_ifs <;> simp
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (secretary N) hQ (fun _ => measurable_const)
    (fun _ => measurable_of_finite _) (measurable_of_finite _) hb
  exact ⟨h1, h2, h3⟩

/-- The job search problem of **Exercise 5.1** (McCall): offers `w ~ F` i.i.d. on the wage space
`W`, with wage `w(·)`; rejecting pays `c` and continues; accepting pays the wage forever, i.e. the
lump sum `w/(1 − β)` (`ex_5_1_accept`). -/
noncomputable def jobSearch {W : Type*} [MeasurableSpace W] (F : Measure W) (wage : W → ℝ)
    (c β : ℝ) : StoppingProblem W where
  Q := fun _ => Kernel.const _ F
  f := fun _ _ => c
  g := fun _ w => wage w / (1 - β)
  h := fun _ => 0
  β := β

/-- **Exercise 5.1** (Miao, p. 155): accepting the wage `w` yields `∑ βᵗ w = w/(1 − β)`, the
stopping payoff `g` of `jobSearch`. -/
theorem ex_5_1_accept {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (w : ℝ) :
    HasSum (fun t : ℕ => β ^ t * w) (w / (1 - β)) := by
  convert (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right w using 1
  rw [div_eq_mul_inv, mul_comm]

/-- **Exercise 5.1** (Miao, p. 155): with offers in `[0, B]` (a measurable wage bounded by `B`),
`F` a probability measure and `β ∈ (0, 1)`, the job search MDP satisfies Assumptions 5.1.1,
5.1.2 and 5.1.4. -/
theorem ex_5_1 {W : Type*} [MeasurableSpace W] {F : Measure W} [IsProbabilityMeasure F]
    {wage : W → ℝ} (hw : Measurable wage) {B : ℝ} (hB : ∀ w, |wage w| ≤ B) {c β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    (jobSearch F wage c β).toMDP.IsMarkov ∧ HasMeasurableSelection (jobSearch F wage c β).toMDP.Γ ∧
      Assumption512 (jobSearch F wage c β).toMDP ∧ Assumption514 (jobSearch F wage c β).toMDP := by
  have hpos : 0 < 1 - β := by linarith
  have hb : (jobSearch F wage c β).Bounded (|c| + max B 0 / (1 - β)) := by
    refine ⟨by positivity, fun t z => ?_, fun t w => ?_, fun z => ?_⟩
    · simp only [jobSearch]
      linarith [div_nonneg (le_max_right B 0) hpos.le]
    · simp only [jobSearch, abs_div, abs_of_pos hpos]
      have : |wage w| / (1 - β) ≤ max B 0 / (1 - β) :=
        div_le_div_of_nonneg_right ((hB w).trans (le_max_left B 0)) hpos.le
      linarith [abs_nonneg c]
    · simp only [jobSearch, abs_zero]
      positivity
  obtain ⟨h1, h2, -, h4⟩ := toMDP_assumptions (jobSearch F wage c β)
    (fun _ => inferInstanceAs (IsMarkovKernel (Kernel.const _ _))) (fun _ => measurable_const)
    (fun _ => hw.div_const _) measurable_const hb
  exact ⟨h1, h2, ⟨hβ0, hβ1⟩, h4 (fun _ => ⟨rfl, rfl, rfl⟩) hβ0.le hβ1⟩

/-- The American put of **Exercise 5.2**: the stock price `p(z_t)` is driven by a Markov process
with transition function `Q`; exercising at `t < T` pays `K − p(z_t)`, holding pays nothing, and
at the expiry date `T` the holder exercises if the option is in the money, `h = max(K − p, 0)`;
`β = 1/(1 + r)`. -/
noncomputable def americanPut (Q : Kernel Z Z) (p : Z → ℝ) (K r : ℝ) : StoppingProblem Z where
  Q := fun _ => Q
  f := fun _ _ => 0
  g := fun _ z => K - p z
  h := fun z => max (K - p z) 0
  β := 1 / (1 + r)

/-- **Exercise 5.2** (Miao, p. 155): with a measurable bounded price, the American put's MDP has
stochastic kernels, satisfies Assumption 5.1.1, Assumption 5.1.2 when `r > 0`, and
Assumption 5.1.3 for every expiry date `T`; its value is that of the stopping problem
(`V0_toMDP`). -/
theorem ex_5_2 {Q : Kernel Z Z} [IsMarkovKernel Q] {p : Z → ℝ} (hp : Measurable p) {B : ℝ}
    (hB : ∀ z, |p z| ≤ B) {K r : ℝ} (hr : 0 < r) :
    (americanPut Q p K r).toMDP.IsMarkov ∧ HasMeasurableSelection (americanPut Q p K r).toMDP.Γ ∧
      Assumption512 (americanPut Q p K r).toMDP ∧
      ∀ T, Assumption513 (americanPut Q p K r).toMDP T := by
  have hb : (americanPut Q p K r).Bounded (|K| + max B 0) := by
    refine ⟨by positivity, fun t z => ?_, fun t z => ?_, fun z => ?_⟩
    · simp only [americanPut, abs_zero]
      positivity
    · calc |K - p z| ≤ |K| + |p z| := abs_sub _ _
        _ ≤ |K| + max B 0 := by linarith [hB z, le_max_left B 0]
    · simp only [americanPut]
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      linarith [le_abs_self K, neg_abs_le (p z), hB z, le_max_left B 0, abs_nonneg (p z)]
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (americanPut Q p K r) (fun _ => ‹IsMarkovKernel Q›)
    (fun _ => measurable_const) (fun _ => measurable_const.sub hp)
    ((measurable_const.sub hp).max measurable_const) hb
  exact ⟨h1, h2, americanCall_beta hr, h3⟩

/-- The three-point law of the relative rank of the `(t + 2)`-th candidate among the first
`t + 2`: best so far (`1`) and second best so far (`2`) each with probability `1/(t + 2)`, and
neither (`0`) with probability `t/(t + 2)`. -/
noncomputable def rank3 (t : ℕ) : Measure (Fin 3) :=
  ENNReal.ofReal (1 / (t + 2)) • Measure.dirac 1 + ENNReal.ofReal (1 / (t + 2)) •
    Measure.dirac 2 + ENNReal.ofReal (t / (t + 2)) • Measure.dirac 0

theorem isProbabilityMeasure_rank3 (t : ℕ) : IsProbabilityMeasure (rank3 t) := by
  refine ⟨?_⟩
  simp only [rank3, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 / ((t : ℝ) + 2) + 1 / (t + 2) + t / (t + 2) = 1 by field_simp; ring]
  simp

/-- The best-two secretary problem of **Exercise 5.3**, in shifted dates (date `t` is the
`k = t + 1`-th candidate). The state is the relative rank of the current candidate: `1` (best so
far), `2` (second best so far) or `0`. The first candidate has relative rank `1`; for `t ≥ 1` the
relative rank of the next candidate is `1` or `2` with probability `1/(t + 2)` each (`rank3`; at
`t = 0` the second candidate is best or second best with probability `1/2` each, which `rank3 0`
also gives). Stopping on a candidate of relative rank `1` among the first `k` wins with
probability `k/N + k(N − k)/(N(N − 1)) = k(2N − k − 1)/(N(N − 1))` (it is the best of all, or
the second best with the best among the later `N − k`), on one of relative rank `2` with
probability `k(k − 1)/(N(N − 1))`; at the last candidate (`k = N`) the probabilities are `1`.
(`min k N` keeps the payoffs bounded past the horizon.) -/
noncomputable def secretaryTwo (N : ℕ) : StoppingProblem (Fin 3) where
  Q := fun t => Kernel.const _ (rank3 t)
  f := fun _ _ => 0
  g := fun t z =>
    if z = 1 then ((min (t + 1) N : ℕ) : ℝ) * (2 * N - (min (t + 1) N : ℕ) - 1) / (N * (N - 1))
    else if z = 2 then ((min (t + 1) N : ℕ) : ℝ) * ((min (t + 1) N : ℕ) - 1) / (N * (N - 1))
    else 0
  h := fun z => if z = 0 then 0 else 1
  β := 1

/-- **Exercise 5.3** (Miao, p. 155): the best-two secretary problem is an optimal stopping
problem whose MDP has stochastic kernels and satisfies Assumption 5.1.1 and, for `N ≥ 2`,
Assumption 5.1.3 for every horizon (all payoffs lie in `[0, 1]`). -/
theorem ex_5_3 {N : ℕ} (hN : 2 ≤ N) :
    (secretaryTwo N).toMDP.IsMarkov ∧ HasMeasurableSelection (secretaryTwo N).toMDP.Γ ∧
      ∀ T, Assumption513 (secretaryTwo N).toMDP T := by
  have hQ : ∀ t, IsMarkovKernel ((secretaryTwo N).Q t) := fun t => by
    have := isProbabilityMeasure_rank3 t
    exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * (N - 1) := by nlinarith
  have hb : (secretaryTwo N).Bounded 1 := by
    refine ⟨zero_le_one, fun t z => by simp [secretaryTwo], fun t z => ?_, fun z => ?_⟩
    · set k : ℕ := min (t + 1) N with hk
      have hk1 : 1 ≤ k := le_min (by omega) (by omega)
      have hkN : k ≤ N := min_le_right _ _
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have hcase : (k : ℝ) = N ∨ (k : ℝ) + 1 ≤ N := by
        rcases Nat.lt_or_ge k N with h | h
        · exact Or.inr (by exact_mod_cast h)
        · exact Or.inl (by exact_mod_cast le_antisymm hkN h)
      simp only [secretaryTwo, ← hk]
      split_ifs
      · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
        rcases hcase with h | h
        · rw [h]
          linarith
        · nlinarith
      · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
        nlinarith
      · simp
    · simp only [secretaryTwo]
      split_ifs <;> simp
  obtain ⟨h1, h2, h3, -⟩ := toMDP_assumptions (secretaryTwo N) hQ (fun _ => measurable_const)
    (fun _ => measurable_of_finite _) (measurable_of_finite _) hb
  exact ⟨h1, h2, h3⟩

end Miao.FiniteHorizonDP
