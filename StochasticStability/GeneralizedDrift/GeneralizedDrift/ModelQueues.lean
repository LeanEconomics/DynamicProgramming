/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.ModelRandomWalk
import GeneralizedDrift.ModelCountableModels
import Mathlib.Probability.Distributions.Exponential

/-!
# The GI/G/1, GI/M/1 and M/G/1 queues

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelQueues.lean`), with the namespace changed to
`MeynTweedie.GeneralizedDrift` and the imports to `InvariantMeasures.*`.

That module was in turn copied from the `MarkovModels` project (`MarkovModels/Queues.lean`).

MT, §2.4.2, pp. 40–43, and (Q1)–(Q5) of Appendix C, pp. 544–545. The queue has i.i.d.
interarrival times `T ~ G` (Q1) and independent i.i.d. service times `S ~ H` (Q2), one server
and first-come-first-served service (Q3).

* `waitingTimeKernel H G`: the waiting time of the `n`-th customer (equivalently the residual
  workload found by an arrival) follows Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺`
  (`lindleyStep`); it is random walk on a half line with increment `S − T`
  (`waitingTimeKernel_eq_halfLineWalk`).
* `giM1Kernel q`: the GI/M/1 queue length `Nₙ = N(Tₙ−)` just before arrivals (MT, (2.28), p. 41),
  `Nₙ₊₁ = [Nₙ + 1 − Dₙ₊₁]⁺` with `D` the number of exponential service completions possible in
  an interarrival time, of law `q`. It rises by at most one (`giM1Kernel_apply_up`, MT, p. 41);
  `P(j, {j + 1 − i}) = q{i}` for `i ≤ j` (`giM1Kernel_apply_le`) and `P(j, {0}) = q[j + 1, ∞)`
  (`giM1Kernel_apply_zero`). `giM1Kernel_not_2_28` shows that (2.28), read literally, fails.
* `mG1Kernel a`: the M/G/1 queue length `N*ₙ` just after departures (MT, p. 43),
  `N*ₙ₊₁ = [N*ₙ − 1]⁺ + Aₙ₊₁` with `A` the number of arrivals during a service, of law `a`.
* The memoryless property behind the GI/M/1 and M/G/1 assumptions (MT, (Q4)–(Q5), p. 42):
  `P(S > t + z | S > z) = e^{−μt}` for exponential `S` (`expMeasure_memoryless`), and the
  up-step probability `P(S > T) = ∫ e^{−μt} G(dt)` (`expMeasure_prod_lt`). For other service laws
  the conditional probabilities in (2.30) differ (`dirac_not_memoryless`), which is why `N` is not
  Markov for a general GI/G/1 queue.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ### The GI/G/1 waiting time chain -/

/-- Lindley's recursion `Wₙ₊₁ = [Wₙ + Sₙ − Tₙ₊₁]⁺` with disturbance `(Sₙ, Tₙ₊₁)`. -/
noncomputable def lindleyStep (p : ℝ≥0 × (ℝ × ℝ)) : ℝ≥0 :=
  Real.toNNReal (p.1 + p.2.1 - p.2.2)

/-- Lindley's step is measurable. -/
theorem measurable_lindleyStep : Measurable lindleyStep :=
  (((measurable_coe_nnreal_real.comp measurable_fst).add
    (measurable_fst.comp measurable_snd)).sub (measurable_snd.comp measurable_snd)).real_toNNReal

/-- The GI/G/1 waiting time chain (Lindley's recursion), with service law `H` and interarrival
law `G` independent, so that `(Sₙ, Tₙ₊₁) ~ H ⊗ G`. -/
noncomputable def waitingTimeKernel (H G : Measure ℝ) : Kernel ℝ≥0 ℝ≥0 :=
  recursionKernel (H.prod G) lindleyStep

/-- The waiting time chain is a Markov kernel. -/
theorem isMarkovKernel_waitingTimeKernel (H G : Measure ℝ) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] : IsMarkovKernel (waitingTimeKernel H G) :=
  isMarkovKernel_recursionKernel _ measurable_lindleyStep

/-- The waiting time chain is random walk on a half line with increment `S − T`. -/
theorem waitingTimeKernel_eq_halfLineWalk (H G : Measure ℝ) [SFinite H] [SFinite G] :
    waitingTimeKernel H G = halfLineWalkKernel ((H.prod G).map fun p => p.1 - p.2) := by
  rw [halfLineWalkKernel, ← recursionKernel_comp_noise _ measurable_halfLineStep
    (g := fun p : ℝ × ℝ => p.1 - p.2) (measurable_fst.sub measurable_snd), waitingTimeKernel]
  congr 1
  funext p
  simp only [lindleyStep, halfLineStep, add_sub_assoc]

/-! ### The GI/M/1 queue length at arrivals -/

/-- The GI/M/1 step `(j, d) ↦ [j + 1 − d]⁺`: the arrival joins the `j` customers present and up
to `d` of them are served before the next arrival. -/
def giM1Step (p : ℕ × ℕ) : ℕ := p.1 + 1 - p.2

/-- The GI/M/1 queue length chain at arrival times, with `q` the law of the number of service
completions possible in one interarrival time (a mixed Poisson law under (Q4)). -/
noncomputable def giM1Kernel (q : Measure ℕ) : Kernel ℕ ℕ :=
  recursionKernel q giM1Step

/-- The GI/M/1 chain is a Markov kernel. -/
theorem isMarkovKernel_giM1Kernel (q : Measure ℕ) [IsProbabilityMeasure q] :
    IsMarkovKernel (giM1Kernel q) :=
  isMarkovKernel_recursionKernel q (measurable_of_countable _)

/-- `P(j, A) = q{d : [j + 1 − d]⁺ ∈ A}`. -/
theorem giM1Kernel_apply' (q : Measure ℕ) [SFinite q] (j : ℕ) (A : Set ℕ) :
    giM1Kernel q j A = q {d | j + 1 - d ∈ A} :=
  recursionKernel_apply' q (measurable_of_countable _) j (Set.to_countable A).measurableSet

/-- MT, p. 41: the queue length just before arrivals rises by at most one. -/
theorem giM1Kernel_apply_up (q : Measure ℕ) [SFinite q] (j : ℕ) :
    giM1Kernel q j (Ioi (j + 1)) = 0 := by
  rw [giM1Kernel_apply' q j]
  convert measure_empty (μ := q)
  ext d
  simp only [mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false]
  omega

/-- From `j`, the chain moves to `j + 1 − i` with probability `q{i}`, for `i ≤ j`. -/
theorem giM1Kernel_apply_le (q : Measure ℕ) [SFinite q] {i j : ℕ} (hij : i ≤ j) :
    giM1Kernel q j {j + 1 - i} = q {i} := by
  rw [giM1Kernel_apply' q j]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff]
  omega

/-- From `j`, the queue empties before the next arrival with probability `q[j + 1, ∞)`. -/
theorem giM1Kernel_apply_zero (q : Measure ℕ) [SFinite q] (j : ℕ) :
    giM1Kernel q j {0} = q (Ici (j + 1)) := by
  rw [giM1Kernel_apply' q j]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff, mem_Ici]
  omega

/-- **Correction to (2.28).** If two service completions in an interarrival time have positive
probability, the GI/M/1 chain does not satisfy (2.28) literally: no `p` gives
`P(j, {j + k}) = p_k` for all `k ≥ −j`. -/
theorem giM1Kernel_not_2_28 (q : Measure ℕ) [IsProbabilityMeasure q] (hq : q {2} ≠ 0) :
    ¬ ∃ p : ℤ → ℝ≥0∞, ∀ (j : ℕ) (k : ℤ), -(j : ℤ) ≤ k →
      giM1Kernel q j {((j : ℤ) + k).toNat} = p k := by
  rintro ⟨p, hp⟩
  have := isMarkovKernel_giM1Kernel q
  have h0 := not_down_of_eq_2_28 (giM1Kernel q) p hp 1 0 one_pos
  rw [giM1Kernel_apply_zero] at h0
  exact hq (measure_mono_null (singleton_subset_iff.mpr (mem_Ici.mpr le_rfl)) h0)

/-! ### The M/G/1 queue length at departures -/

/-- The M/G/1 step `(j, a) ↦ [j − 1]⁺ + a`: the departing customer leaves and `a` customers
arrive during the next service. -/
def mG1Step (p : ℕ × ℕ) : ℕ := p.1 - 1 + p.2

/-- The M/G/1 queue length chain at departure times, with `a` the law of the number of arrivals
during one service time (a mixed Poisson law under (Q5)). -/
noncomputable def mG1Kernel (a : Measure ℕ) : Kernel ℕ ℕ :=
  recursionKernel a mG1Step

/-- The M/G/1 chain is a Markov kernel. -/
theorem isMarkovKernel_mG1Kernel (a : Measure ℕ) [IsProbabilityMeasure a] :
    IsMarkovKernel (mG1Kernel a) :=
  isMarkovKernel_recursionKernel a (measurable_of_countable _)

/-- From `j ≥ 1` the chain moves to `j − 1 + i` with probability `a{i}`. -/
theorem mG1Kernel_apply (a : Measure ℕ) [SFinite a] {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    mG1Kernel a j {j - 1 + i} = a {i} := by
  rw [mG1Kernel, recursionKernel_apply' a (measurable_of_countable _) j
    (measurableSet_singleton _)]
  congr 1
  ext d
  simp only [mem_ofPred_eq, mem_singleton_iff, mG1Step]
  omega

/-- An empty queue after a departure behaves as a queue with one customer left: the next
departure is that of the next arrival. -/
theorem mG1Kernel_zero (a : Measure ℕ) [SFinite a] : mG1Kernel a 0 = mG1Kernel a 1 := by
  rw [mG1Kernel, recursionKernel_apply a (measurable_of_countable _),
    recursionKernel_apply a (measurable_of_countable _)]
  rfl

/-! ### Exponential service times and the memoryless property -/

/-- The exponential survival function: `P(S > x) = e^{−μx}` for `x ≥ 0`. -/
theorem expMeasure_Ioi {μ : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure μ (Ioi x) = ENNReal.ofReal (Real.exp (-(μ * x))) := by
  have := isProbabilityMeasure_expMeasure hμ
  have he : Real.exp (-(μ * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, cdf_expMeasure_eq hμ,
    ite_eq_left hx, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

/-- **The memoryless property** (MT, p. 42): for exponential service times,
`P(S > t + z) = e^{−μt} P(S > z)`, i.e. `P(S > t + z | S > z) = e^{−μt}` whatever the elapsed
service `z`. -/
theorem expMeasure_memoryless {μ : ℝ} (hμ : 0 < μ) {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    expMeasure μ (Ioi (t + z)) = ENNReal.ofReal (Real.exp (-(μ * t))) * expMeasure μ (Ioi z) := by
  rw [expMeasure_Ioi hμ (by linarith), expMeasure_Ioi hμ hz,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- MT, p. 42: with exponential service and interarrival law `G` on `[0, ∞)`, the probability
that the job in service outlasts the next interarrival time is `P(S > T) = ∫ e^{−μt} G(dt)`. -/
theorem expMeasure_prod_lt {μ : ℝ} (hμ : 0 < μ) (G : Measure ℝ) [SFinite G]
    (hG : G (Iio 0) = 0) :
    ((expMeasure μ).prod G) {p | p.2 < p.1} =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(μ * t))) ∂G := by
  have := isProbabilityMeasure_expMeasure hμ
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_snd measurable_fst)]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ t ∂G, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hG
  filter_upwards [hae] with t ht
  rw [← expMeasure_Ioi hμ ht]
  rfl

/-- MT, (2.30), p. 42: for most service laws the residual service depends on the elapsed
service. For a deterministic service time `S = 1`, `P(S > 1/2 | S > 0) = 1` but
`P(S > 1 | S > 1/2) = 0`. -/
theorem dirac_not_memoryless :
    (Measure.dirac (1 : ℝ)) (Ioi (1 / 2 + 0)) / (Measure.dirac (1 : ℝ)) (Ioi 0) ≠
      (Measure.dirac (1 : ℝ)) (Ioi (1 / 2 + 1 / 2)) / (Measure.dirac (1 : ℝ)) (Ioi (1 / 2)) := by
  rw [Measure.dirac_apply' _ measurableSet_Ioi, Measure.dirac_apply' _ measurableSet_Ioi,
    Measure.dirac_apply' _ measurableSet_Ioi, Measure.dirac_apply' _ measurableSet_Ioi]
  norm_num [indicator]

end MeynTweedie.GeneralizedDrift
