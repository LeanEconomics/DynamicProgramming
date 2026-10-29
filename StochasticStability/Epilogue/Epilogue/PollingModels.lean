/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Epilogue.IncrementAnalysis
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The gated-limited polling system (MT §16.4.2)

Meyn and Tweedie, §16.4.2, pp. 412–413: `K` infinite capacity queues and one server, which visits
the queues in the order `1, …, K`; at a visit to queue `k` it serves `min(x, ℓ_k)` customers,
`x` the number present when it arrives there (`ℓ_k` is the gate limit). Arrivals at queue `k`
form a Poisson stream of rate `λ_k`, service times at queue `k` are i.i.d. with law `G_k` and mean
`m_k = μ_k⁻¹`, and everything is independent. The chain `Φ` is the vector of queue lengths at the
instants the server arrives back at queue `1`.

**The chain.** The state is `j : Fin K → ℕ`.
* `sumLaw G s`: the law of `S₁ + ⋯ + S_s` for i.i.d. `Sᵢ ~ G`, the total service time of `s`
  customers.
* `arrLaw lam t`: the law of the arrivals `(A_q)_q` during a time `t`, independent
  `Poisson(λ_q t)`.
* `visitMeasure`: a visit to queue `k` from `j` serves `s = min(j_k, ℓ_k)` customers, in time
  `T ~ sumLaw G_k s`, during which `A ~ arrLaw λ T` arrive; the new state is `j − s e_k + A`.
* `pollTail n`: the last `n` visits of a cycle; `pollKernel = pollTail K` is one cycle, the
  transition kernel of `Φ`.

**Precise reading.** The book's description is taken literally: there are no switchover times,
so a visit to an empty queue takes no time and brings no arrivals, the service times of the
`s = min(x, ℓ_k)` customers served at a visit are added up, and the arrivals during the visit are
Poisson in that total time. The empty state `0` is the accessible state used for irreducibility
and aperiodicity.

**Results.**
* `lintegral_visit`, `lintegral_visit_V`, `lintegral_visit_exp`, `lintegral_visit_exp_neg`:
  one visit, with `V(j) = Σ_q w_q j_q`: `E V = V(j) − (1 − ρ) s w_k` for `w_q ∝ m_q`,
  `ρ = Σ λ_q m_q`, and the exponential moments.
* `pollTail_drift`: over a cycle, `E_j V(Φ₁) ≤ V(j) − 1` once some `j_k ≥ ℓ_k`: the queue that
  holds at least `ℓ_k` customers is still that full when the server reaches it. This is the
  drift (16.25) for the book's `V(i) = Σ_k i_k/μ_k`, suitably scaled.
* `pollTail_exp`: the exponential moments over a cycle, `E_j e^{βV(Φ₁)} ≤ e^{βV(j)} F^K` and
  `E_j e^{−V(Φ₁)} ≤ e^{−V(j)} E^K`, which give the increment conditions (16.26)–(16.27).
* `pollTail_drain_pos`, `pollKernel_reach_zero`: with positive probability no customer arrives,
  so the chain reaches the empty state from every state.
* **`theorem_16_4_2`** (p. 412): if `ρ = Σ_k λ_k/μ_k < 1` and the service time laws are in
  `G⁺(γ)`, the chain is positive, aperiodic and `e^{δV}`-uniformly ergodic for some `δ > 0`; in
  particular geometrically ergodic.
-/

namespace MeynTweedie.Epilogue

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Nat

variable {K : ℕ}

/-! ### Poisson arrivals and total service times -/

/-- `∫ f dPo(r) = Σₙ e^{−r} rⁿ/n! f(n)`. -/
theorem lintegral_poissonMeasure (r : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ n, f n ∂poissonMeasure r =
      ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / n !) * f n := by
  rw [poissonMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- **The Poisson mean**: `∫ n dPo(r) = r`. -/
theorem lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂poissonMeasure r = r := by
  rw [lintegral_poissonMeasure, tsum_eq_zero_add' ENNReal.summable]
  have hshift : ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ (n + 1) / (n + 1) !) *
      ((n + 1 : ℕ) : ℝ≥0∞) = (r : ℝ≥0∞) * ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / n !) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have hone : ∑' n, ENNReal.ofReal (Real.exp (-r) * r ^ n / n !) = 1 := by
    have h := measure_univ (μ := poissonMeasure r)
    rw [← lintegral_one, lintegral_poissonMeasure] at h
    simp only [mul_one] at h
    exact h
  rw [Nat.cast_zero, mul_zero, zero_add, hshift, hone, mul_one]

/-- **The Poisson generating function**: `∫ e^{θn} dPo(r) = exp(r(e^θ − 1))`. -/
theorem lintegral_exp_poissonMeasure (r : ℝ≥0) (θ : ℝ) :
    ∫⁻ n, ENNReal.ofReal (Real.exp (θ * n)) ∂poissonMeasure r =
      ENNReal.ofReal (Real.exp (r * (Real.exp θ - 1))) := by
  rw [lintegral_poissonMeasure]
  set x : ℝ := (r : ℝ) with hx
  have hterm : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-x) * x ^ n / n !) *
      ENNReal.ofReal (Real.exp (θ * n)) =
      ENNReal.ofReal (Real.exp (-x) * ((Real.exp θ * x) ^ n / n !)) := fun n => by
    rw [← ENNReal.ofReal_mul (by positivity), mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  simp_rw [hterm]
  have hsum := Real.summable_pow_div_factorial (Real.exp θ * x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsum.mul_left _),
    tsum_mul_left]
  congr 1
  have he : ∑' n : ℕ, (Real.exp θ * x) ^ n / n ! = Real.exp (Real.exp θ * x) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [he, ← Real.exp_add]
  ring_nf

/-- `Po(r){0} = e^{−r} > 0`. -/
theorem poissonMeasure_zero_pos (r : ℝ≥0) : 0 < poissonMeasure r {0} := by
  rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

/-- The law of the total service time `S₁ + ⋯ + S_s` of `s` customers, `Sᵢ ~ G` i.i.d. -/
noncomputable def sumLaw (G : Measure ℝ≥0) (s : ℕ) : Measure ℝ≥0 :=
  (Measure.pi fun _ : Fin s => G).map fun v => ∑ i, v i

/-- The sum map is measurable. -/
theorem measurable_finSum (s : ℕ) : Measurable fun v : Fin s → ℝ≥0 => ∑ i, v i :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- `sumLaw G s` is a probability measure. -/
theorem isProbabilityMeasure_sumLaw (G : Measure ℝ≥0) [IsProbabilityMeasure G] (s : ℕ) :
    IsProbabilityMeasure (sumLaw G s) := by
  rw [sumLaw]
  infer_instance

/-- `E[e^{κT}] = (∫ e^{κt} G(dt))ˢ` for the total service time `T` of `s` customers. -/
theorem lintegral_exp_sumLaw (G : Measure ℝ≥0) [IsProbabilityMeasure G] (s : ℕ) (κ : ℝ) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (κ * t)) ∂sumLaw G s =
      (∫⁻ t, ENNReal.ofReal (Real.exp (κ * t)) ∂G) ^ s := by
  have hf : Measurable fun t : ℝ≥0 => ENNReal.ofReal (Real.exp (κ * t)) := by fun_prop
  rw [sumLaw, lintegral_map hf (measurable_finSum s)]
  have hprod : ∀ v : Fin s → ℝ≥0, ENNReal.ofReal (Real.exp (κ * ((∑ i, v i : ℝ≥0) : ℝ))) =
      ∏ i, ENNReal.ofReal (Real.exp (κ * v i)) := fun v => by
    rw [NNReal.coe_sum, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  simp_rw [hprod]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
      (fun i (v : Fin s → ℝ≥0) => ENNReal.ofReal (Real.exp (κ * v i)))
      (iIndepFun_pi (X := fun _ (t : ℝ≥0) => ENNReal.ofReal (Real.exp (κ * t)))
        fun _ => hf.aemeasurable) fun i => hf.comp (measurable_pi_apply i)]
  rw [Finset.prod_congr rfl fun i _ =>
    (measurePreserving_eval (fun _ : Fin s => G) i).lintegral_comp
    hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `E[T] = s ∫ t G(dt)` for the total service time `T` of `s` customers. -/
theorem lintegral_id_sumLaw (G : Measure ℝ≥0) [IsProbabilityMeasure G] (s : ℕ) :
    ∫⁻ t, (t : ℝ≥0∞) ∂sumLaw G s = s * ∫⁻ t, (t : ℝ≥0∞) ∂G := by
  have hf : Measurable fun t : ℝ≥0 => (t : ℝ≥0∞) := measurable_coe_nnreal_ennreal
  rw [sumLaw, lintegral_map hf (measurable_finSum s)]
  simp_rw [ENNReal.ofNNReal_finsetSum]
  rw [lintegral_finsetSum _ (f := fun i (v : Fin s → ℝ≥0) => ((v i : ℝ≥0) : ℝ≥0∞))
    fun i _ => hf.comp (measurable_pi_apply i)]
  rw [Finset.sum_congr rfl fun i _ => (measurePreserving_eval (fun _ : Fin s => G) i).lintegral_comp
    hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The law of the arrivals during a time `t`: independent `Poisson(λ_q t)` at the queues. -/
noncomputable def arrLaw (lam : Fin K → ℝ≥0) (t : ℝ≥0) : Measure (Fin K → ℕ) :=
  Measure.pi fun q => poissonMeasure (lam q * t)

/-- The arrival law is a probability measure. -/
theorem isProbabilityMeasure_arrLaw (lam : Fin K → ℝ≥0) (t : ℝ≥0) :
    IsProbabilityMeasure (arrLaw lam t) := by
  rw [arrLaw]
  infer_instance

/-- The singletons of the arrival law: `P(A = a) = Π_q Po(λ_q t){a_q}`. -/
theorem arrLaw_singleton (lam : Fin K → ℝ≥0) (t : ℝ≥0) (a : Fin K → ℕ) :
    arrLaw lam t {a} = ∏ q, poissonMeasure (lam q * t) {a q} := by
  rw [arrLaw, ← Set.univ_pi_singleton, Measure.pi_pi]

/-- The arrival law depends measurably on the time. -/
theorem measurable_arrLaw (lam : Fin K → ℝ≥0) : Measurable (arrLaw lam) := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have h : ∀ t, arrLaw lam t B =
      ∑' a : Fin K → ℕ, B.indicator (fun a => ∏ q, poissonMeasure (lam q * t) {a q}) a :=
    fun t => by
      have := isProbabilityMeasure_arrLaw lam t
      conv_lhs => rw [← Measure.sum_smul_dirac (arrLaw lam t)]
      rw [Measure.sum_apply _ hB]
      refine tsum_congr fun a => ?_
      rw [Measure.smul_apply, Measure.dirac_apply' _ hB, smul_eq_mul, arrLaw_singleton]
      by_cases ha : a ∈ B
      · rw [indicator_of_mem ha, indicator_of_mem ha, Pi.one_apply, mul_one]
      · rw [indicator_of_notMem ha, indicator_of_notMem ha, mul_zero]
  simp_rw [h]
  refine Measurable.tsum fun a => ?_
  by_cases ha : a ∈ B
  · simp_rw [indicator_of_mem ha]
    refine Finset.measurable_prod _ fun q _ => ?_
    simp_rw [poissonMeasure_singleton]
    fun_prop
  · simp_rw [indicator_of_notMem ha]
    exact measurable_const

/-- **Product formula** for the arrivals: `E[Π_q f_q(A_q)] = Π_q E[f_q(A_q)]`. -/
theorem lintegral_prod_arrLaw (lam : Fin K → ℝ≥0) (t : ℝ≥0) (f : Fin K → ℕ → ℝ≥0∞) :
    ∫⁻ a, ∏ q, f q (a q) ∂arrLaw lam t = ∏ q, ∫⁻ n, f q n ∂poissonMeasure (lam q * t) := by
  rw [arrLaw, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
      (fun q (a : Fin K → ℕ) => f q (a q))
      (iIndepFun_pi (X := f) fun q => (measurable_of_countable _).aemeasurable)
      fun q => (measurable_of_countable (f q)).comp (measurable_pi_apply q)]
  exact Finset.prod_congr rfl fun q _ =>
    (measurePreserving_eval (fun q => poissonMeasure (lam q * t)) q).lintegral_comp
      (measurable_of_countable (f q))

/-- **Sum formula** for the arrivals: `E[Σ_q f_q(A_q)] = Σ_q E[f_q(A_q)]`. -/
theorem lintegral_sum_arrLaw (lam : Fin K → ℝ≥0) (t : ℝ≥0) (f : Fin K → ℕ → ℝ≥0∞) :
    ∫⁻ a, ∑ q, f q (a q) ∂arrLaw lam t = ∑ q, ∫⁻ n, f q n ∂poissonMeasure (lam q * t) := by
  rw [lintegral_finsetSum _ (f := fun q (a : Fin K → ℕ) => f q (a q))
    fun q _ => (measurable_of_countable (f q)).comp (measurable_pi_apply q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [arrLaw]
  exact (measurePreserving_eval (fun q => poissonMeasure (lam q * t)) q).lintegral_comp
    (measurable_of_countable (f q))

/-! ### One visit -/

/-- The number of customers served at a visit to queue `k` from `j`: `min(j_k, ℓ_k)`. -/
def served (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) : ℕ := min (j k) (ℓ k)

/-- The state after the services of a visit to queue `k`, before the arrivals. -/
def afterServe (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) : Fin K → ℕ :=
  Function.update j k (j k - served ℓ k j)

/-- **One visit to queue `k`** from `j`: `s = min(j_k, ℓ_k)` customers are served in a time
`T ~ sumLaw G_k s`, during which `A ~ arrLaw λ T` customers arrive; the new state is
`j − s e_k + A`. -/
noncomputable def visitMeasure (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0)
    (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) : Measure (Fin K → ℕ) :=
  (fun t => (arrLaw lam t).map fun a => afterServe ℓ k j + a) ∘ₘ sumLaw (G k) (served ℓ k j)

/-- The arrival law shifted by `b` depends measurably on the time. -/
theorem measurable_arrLaw_map (lam : Fin K → ℝ≥0) (b : Fin K → ℕ) :
    Measurable fun t => (arrLaw lam t).map fun a => b + a :=
  (Measure.measurable_map _ (measurable_of_countable _)).comp (measurable_arrLaw lam)

/-- `∫ g d(visit) = ∫∫ g(b + a) arrLaw(t, da) sumLaw(dt)`, `b` the state after service. -/
theorem lintegral_visit (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ)
    (k : Fin K) (j : Fin K → ℕ) (g : (Fin K → ℕ) → ℝ≥0∞) :
    ∫⁻ y, g y ∂visitMeasure lam G ℓ k j = ∫⁻ t, ∫⁻ a, g (afterServe ℓ k j + a) ∂arrLaw lam t
      ∂sumLaw (G k) (served ℓ k j) := by
  rw [visitMeasure, Measure.lintegral_bind (measurable_arrLaw_map lam _).aemeasurable
    (measurable_of_countable g).aemeasurable]
  exact lintegral_congr fun t => lintegral_map (measurable_of_countable g)
    (measurable_of_countable _)

/-- A visit is a probability measure. -/
theorem isProbabilityMeasure_visit (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) :
    IsProbabilityMeasure (visitMeasure lam G ℓ k j) := by
  have := hG k
  have := isProbabilityMeasure_sumLaw (G k) (served ℓ k j)
  constructor
  rw [← lintegral_one, lintegral_visit]
  have h1 : ∀ t, ∫⁻ _, (1 : ℝ≥0∞) ∂arrLaw lam t = 1 := fun t => by
    have := isProbabilityMeasure_arrLaw lam t
    rw [lintegral_const, measure_univ, mul_one]
  exact (lintegral_congr h1).trans (by rw [lintegral_const, measure_univ, mul_one])

/-- The visit kernel to queue `k`. -/
noncomputable def visitKernel (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ)
    (k : Fin K) : Kernel (Fin K → ℕ) (Fin K → ℕ) :=
  ⟨visitMeasure lam G ℓ k, measurable_of_countable _⟩

/-- The linear test function `V(j) = Σ_q w_q j_q`. -/
def pollV (w : Fin K → ℝ) (j : Fin K → ℕ) : ℝ := ∑ q, w q * j q

/-- `V(b + a) = V(b) + Σ_q w_q a_q`. -/
theorem pollV_add (w : Fin K → ℝ) (b a : Fin K → ℕ) :
    pollV w (b + a) = pollV w b + ∑ q, w q * a q := by
  simp only [pollV, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]

/-- `V(j − s e_k) = V(j) − w_k s`. -/
theorem pollV_afterServe (w : Fin K → ℝ) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) :
    pollV w (afterServe ℓ k j) = pollV w j - w k * served ℓ k j := by
  have hs : served ℓ k j ≤ j k := min_le_left _ _
  rw [pollV, pollV, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hrest : ∑ q ∈ Finset.univ.erase k, w q * ((afterServe ℓ k j q : ℕ) : ℝ) =
      ∑ q ∈ Finset.univ.erase k, w q * (j q : ℝ) := Finset.sum_congr rfl fun q hq => by
    rw [afterServe, Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  rw [hrest, afterServe, Function.update_self, Nat.cast_sub hs]
  ring

/-- `V ≥ 0` for nonnegative weights. -/
theorem pollV_nonneg {w : Fin K → ℝ} (hw : ∀ q, 0 ≤ w q) (j : Fin K → ℕ) : 0 ≤ pollV w j :=
  Finset.sum_nonneg fun q _ => mul_nonneg (hw q) (Nat.cast_nonneg _)

/-- **The mean of `V` after one visit**:
`E V = V(j − s e_k) + (Σ_q w_q λ_q) s ∫ t G_k(dt)`. -/
theorem lintegral_visit_V (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ)
    {w : Fin K → ℝ} (hw : ∀ q, 0 ≤ w q) :
    ∫⁻ y, ENNReal.ofReal (pollV w y) ∂visitMeasure lam G ℓ k j =
      ENNReal.ofReal (pollV w (afterServe ℓ k j)) + (∑ q, ENNReal.ofReal (w q) * lam q) *
        ((served ℓ k j : ℝ≥0∞) * ∫⁻ t, (t : ℝ≥0∞) ∂G k) := by
  have := hG k
  have := isProbabilityMeasure_sumLaw (G k) (served ℓ k j)
  set b := afterServe ℓ k j
  have hinner : ∀ t : ℝ≥0, ∫⁻ a, ENNReal.ofReal (pollV w (b + a)) ∂arrLaw lam t =
      ENNReal.ofReal (pollV w b) + ∑ q, ENNReal.ofReal (w q) * lam q * (t : ℝ≥0∞) := fun t => by
    have := isProbabilityMeasure_arrLaw lam t
    have hpt : ∀ a : Fin K → ℕ, ENNReal.ofReal (pollV w (b + a)) =
        ENNReal.ofReal (pollV w b) + ∑ q, ENNReal.ofReal (w q) * (a q : ℝ≥0∞) := fun a => by
      rw [pollV_add, ENNReal.ofReal_add (pollV_nonneg hw b)
        (Finset.sum_nonneg fun q _ => mul_nonneg (hw q) (Nat.cast_nonneg _)),
        ENNReal.ofReal_sum_of_nonneg fun q _ => mul_nonneg (hw q) (Nat.cast_nonneg _)]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ENNReal.ofReal_mul (hw q), ENNReal.ofReal_natCast]
    rw [lintegral_congr hpt, lintegral_add_left measurable_const, lintegral_const, measure_univ,
      mul_one, lintegral_sum_arrLaw lam t (fun q n => ENNReal.ofReal (w q) * (n : ℝ≥0∞))]
    refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
    rw [lintegral_const_mul _ (measurable_of_countable _), lintegral_id_poissonMeasure,
      ENNReal.coe_mul, mul_assoc]
  rw [lintegral_visit, lintegral_congr hinner, lintegral_add_left measurable_const,
    lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum _ (f := fun q (t : ℝ≥0) => ENNReal.ofReal (w q) * lam q * (t : ℝ≥0∞))
      fun q _ => measurable_coe_nnreal_ennreal.const_mul _]
  simp_rw [lintegral_const_mul _ measurable_coe_nnreal_ennreal]
  rw [lintegral_id_sumLaw, Finset.sum_mul]

/-- **The exponential moment after one visit**: with `κ = Σ_q λ_q (e^{βw_q} − 1)`,
`E e^{βV} = e^{βV(j − s e_k)} (∫ e^{κt} G_k(dt))ˢ`. -/
theorem lintegral_visit_exp (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ)
    (w : Fin K → ℝ) (β : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (β * pollV w y)) ∂visitMeasure lam G ℓ k j =
      ENNReal.ofReal (Real.exp (β * pollV w (afterServe ℓ k j))) *
        (∫⁻ t, ENNReal.ofReal (Real.exp ((∑ q, lam q * (Real.exp (β * w q) - 1)) * t)) ∂G k) ^
          served ℓ k j := by
  have := hG k
  set b := afterServe ℓ k j
  have hinner : ∀ t : ℝ≥0, ∫⁻ a, ENNReal.ofReal (Real.exp (β * pollV w (b + a))) ∂arrLaw lam t =
      ENNReal.ofReal (Real.exp (β * pollV w b)) *
        ENNReal.ofReal (Real.exp ((∑ q, lam q * (Real.exp (β * w q) - 1)) * t)) := fun t => by
    have hpt : ∀ a : Fin K → ℕ, ENNReal.ofReal (Real.exp (β * pollV w (b + a))) =
        ENNReal.ofReal (Real.exp (β * pollV w b)) *
          ∏ q, ENNReal.ofReal (Real.exp (β * w q * a q)) := fun a => by
      rw [pollV_add, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
        Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun q _ => (Real.exp_pos _).le]
      congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [mul_assoc]
    rw [lintegral_congr hpt, lintegral_const_mul _ (Finset.measurable_prod _ fun q _ =>
        measurable_of_countable _),
      lintegral_prod_arrLaw lam t (fun q n => ENNReal.ofReal (Real.exp (β * w q * n)))]
    congr 1
    simp_rw [lintegral_exp_poissonMeasure]
    rw [← ENNReal.ofReal_prod_of_nonneg fun q _ => (Real.exp_pos _).le, ← Real.exp_sum,
      Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [NNReal.coe_mul]
    ring
  rw [lintegral_visit, lintegral_congr hinner, lintegral_const_mul _ (by fun_prop),
    lintegral_exp_sumLaw]

/-- **The negative exponential moment after one visit**: `E e^{−V} ≤ e^{−V(j − s e_k)}`, since
arrivals only increase `V`. -/
theorem lintegral_visit_exp_neg (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ)
    {w : Fin K → ℝ} (hw : ∀ q, 0 ≤ w q) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-pollV w y)) ∂visitMeasure lam G ℓ k j ≤
      ENNReal.ofReal (Real.exp (-pollV w (afterServe ℓ k j))) := by
  have := hG k
  have := isProbabilityMeasure_sumLaw (G k) (served ℓ k j)
  rw [lintegral_visit]
  calc ∫⁻ t, ∫⁻ a, ENNReal.ofReal (Real.exp (-pollV w (afterServe ℓ k j + a))) ∂arrLaw lam t
        ∂sumLaw (G k) (served ℓ k j)
      ≤ ∫⁻ t, ∫⁻ _, ENNReal.ofReal (Real.exp (-pollV w (afterServe ℓ k j))) ∂arrLaw lam t
        ∂sumLaw (G k) (served ℓ k j) := by
        refine lintegral_mono fun t => lintegral_mono fun a => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        rw [pollV_add]
        have : 0 ≤ ∑ q, w q * (a q : ℝ) :=
          Finset.sum_nonneg fun q _ => mul_nonneg (hw q) (Nat.cast_nonneg _)
        linarith
    _ = _ := by
        have h : ∀ t, ∫⁻ _, ENNReal.ofReal (Real.exp (-pollV w (afterServe ℓ k j)))
            ∂arrLaw lam t = ENNReal.ofReal (Real.exp (-pollV w (afterServe ℓ k j))) := fun t => by
          have := isProbabilityMeasure_arrLaw lam t
          rw [lintegral_const, measure_univ, mul_one]
        rw [lintegral_congr h, lintegral_const, measure_univ, mul_one]

/-- **A visit to queue `k` does not decrease the other queues**: a.s. `y_m ≥ j_m` for `m ≠ k`. -/
theorem visit_ge (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ) (k : Fin K)
    (j : Fin K → ℕ) : visitMeasure lam G ℓ k j {y | ∃ m, m ≠ k ∧ y m < j m} = 0 := by
  rw [visitMeasure, Measure.bind_apply (measurableSet_of_countable _)
    (measurable_arrLaw_map lam _).aemeasurable]
  refine le_antisymm ?_ zero_le
  calc ∫⁻ t, ((arrLaw lam t).map fun a => afterServe ℓ k j + a) {y | ∃ m, m ≠ k ∧ y m < j m}
        ∂sumLaw (G k) (served ℓ k j) ≤ ∫⁻ _, 0 ∂sumLaw (G k) (served ℓ k j) := by
        refine lintegral_mono fun t => le_of_eq ?_
        rw [Measure.map_apply (measurable_of_countable _) (measurableSet_of_countable _)]
        convert measure_empty (μ := arrLaw lam t)
        ext a
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists,
          not_and, not_lt]
        intro m hm
        rw [Pi.add_apply, afterServe, Function.update_of_ne hm]
        exact Nat.le_add_right _ _
    _ = 0 := lintegral_zero

/-- **No arrivals**: a visit leaves the system at `j − s e_k` with positive probability. -/
theorem visit_afterServe_pos (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) (j : Fin K → ℕ) :
    0 < visitMeasure lam G ℓ k j {afterServe ℓ k j} := by
  have := hG k
  have := isProbabilityMeasure_sumLaw (G k) (served ℓ k j)
  rw [visitMeasure, Measure.bind_apply (measurableSet_singleton _)
    (measurable_arrLaw_map lam _).aemeasurable]
  have h : ∀ t, ((arrLaw lam t).map fun a => afterServe ℓ k j + a) {afterServe ℓ k j} =
      arrLaw lam t {0} := fun t => by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext a
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro ha
      exact add_eq_left.1 ha
    · intro ha
      rw [ha, add_zero]
  simp_rw [h]
  refine lintegral_pos_of_pos (IsProbabilityMeasure.ne_zero _)
    ((Measure.measurable_coe (measurableSet_singleton 0)).comp (measurable_arrLaw lam))
    fun t => ?_
  rw [arrLaw_singleton]
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun q _ => (poissonMeasure_zero_pos _).ne')

/-! ### One cycle -/

/-- The visit to queue `i` (the identity for `i ≥ K`). -/
noncomputable def visitAt (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ)
    (i : ℕ) : Kernel (Fin K → ℕ) (Fin K → ℕ) :=
  if h : i < K then visitKernel lam G ℓ ⟨i, h⟩ else Kernel.id

/-- **The last `n` visits of a cycle**, to the queues `K − n, …, K − 1`. -/
noncomputable def pollTail (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ) :
    ℕ → Kernel (Fin K → ℕ) (Fin K → ℕ)
  | 0 => Kernel.id
  | n + 1 => pollTail lam G ℓ n ∘ₖ visitAt lam G ℓ (K - (n + 1))

/-- **The gated-limited polling chain**: one cycle of visits to the queues `1, …, K`. -/
noncomputable def pollKernel (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ) :
    Kernel (Fin K → ℕ) (Fin K → ℕ) :=
  pollTail lam G ℓ K

/-- A visit kernel is a Markov kernel. -/
theorem isMarkovKernel_visitKernel (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (k : Fin K) :
    IsMarkovKernel (visitKernel lam G ℓ k) :=
  ⟨fun j => isProbabilityMeasure_visit lam hG ℓ k j⟩

/-- The partial cycles are Markov kernels. -/
theorem isMarkovKernel_pollTail (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (n : ℕ) :
    IsMarkovKernel (pollTail lam G ℓ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih =>
    have : IsMarkovKernel (visitAt lam G ℓ (K - (n + 1))) := by
      unfold visitAt
      split_ifs with h
      · exact isMarkovKernel_visitKernel lam hG ℓ _
      · exact inferInstanceAs (IsMarkovKernel Kernel.id)
    exact Kernel.IsMarkovKernel.comp _ _

/-- The polling chain is a Markov kernel. -/
theorem isMarkovKernel_pollKernel (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) :
    IsMarkovKernel (pollKernel lam G ℓ) :=
  isMarkovKernel_pollTail lam hG ℓ K

/-- The visit at index `K − (n + 1)` for `n + 1 ≤ K`. -/
theorem visitAt_eq (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0) (ℓ : Fin K → ℕ) {n : ℕ}
    (hn : n + 1 ≤ K) :
    visitAt lam G ℓ (K - (n + 1)) = visitKernel lam G ℓ ⟨K - (n + 1), by omega⟩ := by
  rw [visitAt, dite_eq_left (by omega)]

/-- `∫ g d(pollTail (n + 1) j) = ∫∫ g d(pollTail n y) visit(j, dy)` for `n + 1 ≤ K`. -/
theorem lintegral_pollTail_succ (lam : Fin K → ℝ≥0) (G : Fin K → Measure ℝ≥0)
    (ℓ : Fin K → ℕ) {n : ℕ} (hn : n + 1 ≤ K) (j : Fin K → ℕ) (g : (Fin K → ℕ) → ℝ≥0∞) :
    ∫⁻ y, g y ∂pollTail lam G ℓ (n + 1) j = ∫⁻ y, ∫⁻ z, g z ∂pollTail lam G ℓ n y
      ∂visitMeasure lam G ℓ ⟨K - (n + 1), by omega⟩ j := by
  rw [pollTail, Kernel.lintegral_comp _ _ _ (measurable_of_countable g), visitAt_eq lam G ℓ hn]
  rfl

/-- Some queue among the last `n` visited holds at least its gate limit. -/
def fullAfter (ℓ : Fin K → ℕ) (n : ℕ) (j : Fin K → ℕ) : Prop :=
  ∃ i : Fin K, K - n ≤ i.1 ∧ ℓ i ≤ j i

open Classical in
/-- **The drift over the last `n` visits** ((16.25), MT p. 412): if each visit to queue `k`
lowers the mean of `V` by `(1 − ρ) w_k s`, `s` the number served, and `(1 − ρ) w_k ℓ_k ≥ 1`, then
`E_j V(Φ) + 1 ≤ V(j)` as soon as one of the last `n` queues holds at least its gate limit, and
`E_j V(Φ) ≤ V(j)` always. -/
theorem pollTail_drift (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) {w : Fin K → ℝ} {c : ℝ}
    (hvis : ∀ k j, ∫⁻ y, ENNReal.ofReal (pollV w y) ∂visitMeasure lam G ℓ k j +
      ENNReal.ofReal (c * w k * served ℓ k j) = ENNReal.ofReal (pollV w j))
    (hcw : ∀ k, 1 ≤ c * w k * ℓ k) (n : ℕ) (hn : n ≤ K) (j : Fin K → ℕ) :
    ∫⁻ y, ENNReal.ofReal (pollV w y) ∂pollTail lam G ℓ n j +
      (if fullAfter ℓ n j then 1 else 0) ≤ ENNReal.ofReal (pollV w j) := by
  classical
  induction n generalizing j with
  | zero =>
    have hf : ¬ fullAfter ℓ 0 j := by
      rintro ⟨i, hi, -⟩
      have := i.2
      omega
    rw [ite_eq_right hf, add_zero, pollTail, Kernel.id_apply, lintegral_dirac]
  | succ n ih =>
    have hnK : n ≤ K := by omega
    set k : Fin K := ⟨K - (n + 1), by omega⟩ with hk
    have := isProbabilityMeasure_visit lam hG ℓ k j
    have hle : ∫⁻ y, ENNReal.ofReal (pollV w y) ∂visitMeasure lam G ℓ k j ≤
        ENNReal.ofReal (pollV w j) := (le_self_add).trans (le_of_eq (hvis k j))
    have hint : ∫⁻ y, ∫⁻ z, ENNReal.ofReal (pollV w z) ∂pollTail lam G ℓ n y
          ∂visitMeasure lam G ℓ k j +
        ∫⁻ y, (if fullAfter ℓ n y then (1 : ℝ≥0∞) else 0) ∂visitMeasure lam G ℓ k j ≤
        ∫⁻ y, ENNReal.ofReal (pollV w y) ∂visitMeasure lam G ℓ k j := by
      rw [← lintegral_add_left (measurable_of_countable _)]
      exact lintegral_mono fun y => ih hnK y
    rw [lintegral_pollTail_succ lam G ℓ hn]
    by_cases hkk : ℓ k ≤ j k
    · -- the queue being visited is full: `s = ℓ_k`
      have hs : served ℓ k j = ℓ k := min_eq_right hkk
      have h1 := le_self_add.trans hint
      have h2 : (if fullAfter ℓ (n + 1) j then (1 : ℝ≥0∞) else 0) ≤
          ENNReal.ofReal (c * w k * served ℓ k j) := by
        split_ifs
        · rw [hs, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hcw k)
        · exact zero_le
      exact (add_le_add h1 h2).trans (le_of_eq (hvis k j))
    · by_cases hfull : fullAfter ℓ (n + 1) j
      · -- a later queue is full, and stays full until it is visited
        obtain ⟨i, hi, hij⟩ := hfull
        have hik : i ≠ k := by
          rintro rfl
          exact hkk hij
        have hi' : K - n ≤ i.1 := by
          have : i.1 ≠ K - (n + 1) := fun h => hik (Fin.ext h)
          omega
        have hae : ∀ᵐ y ∂visitMeasure lam G ℓ k j, fullAfter ℓ n y := by
          refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (visit_ge lam G ℓ k j))
          by_contra hge
          simp only [mem_ofPred_eq] at hge hy
          push Not at hge
          exact hy ⟨i, hi', hij.trans (hge i hik)⟩
        have hone : ∫⁻ y, (if fullAfter ℓ n y then (1 : ℝ≥0∞) else 0)
            ∂visitMeasure lam G ℓ k j = 1 := by
          rw [lintegral_congr_ae (hae.mono fun y hy => ite_eq_left hy), lintegral_const,
            measure_univ,
            mul_one]
        rw [hone] at hint
        rw [ite_eq_left (show fullAfter ℓ (n + 1) j from ⟨i, hi, hij⟩)]
        exact hint.trans hle
      · rw [ite_eq_right hfull, add_zero]
        exact (le_self_add.trans hint).trans hle

/-- **The exponential moment over the last `n` visits**: if each visit multiplies
`E e^{βV}` by at most `F`, then `E_j e^{βV(Φ)} ≤ e^{βV(j)} Fⁿ`. -/
theorem pollTail_exp (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0} (ℓ : Fin K → ℕ)
    (f : (Fin K → ℕ) → ℝ≥0∞) {F : ℝ≥0∞}
    (hvis : ∀ k j, ∫⁻ y, f y ∂visitMeasure lam G ℓ k j ≤ f j * F) (n : ℕ) (hn : n ≤ K)
    (j : Fin K → ℕ) : ∫⁻ y, f y ∂pollTail lam G ℓ n j ≤ f j * F ^ n := by
  induction n generalizing j with
  | zero => rw [pollTail, Kernel.id_apply, lintegral_dirac, pow_zero, mul_one]
  | succ n ih =>
    rw [lintegral_pollTail_succ lam G ℓ hn]
    calc ∫⁻ y, ∫⁻ z, f z ∂pollTail lam G ℓ n y ∂visitMeasure lam G ℓ ⟨K - (n + 1), by omega⟩ j
        ≤ ∫⁻ y, f y * F ^ n ∂visitMeasure lam G ℓ ⟨K - (n + 1), by omega⟩ j :=
          lintegral_mono fun y => ih (by omega) y
      _ = (∫⁻ y, f y ∂visitMeasure lam G ℓ ⟨K - (n + 1), by omega⟩ j) * F ^ n :=
          lintegral_mul_const _ (measurable_of_countable f)
      _ ≤ f j * F * F ^ n := by gcongr; exact hvis _ j
      _ = f j * F ^ (n + 1) := by rw [pow_succ', mul_assoc]

/-- The state after the last `n` visits with no arrivals. -/
def drainAfter (ℓ : Fin K → ℕ) (n : ℕ) (j : Fin K → ℕ) : Fin K → ℕ :=
  fun q => if K - n ≤ q.1 then j q - min (j q) (ℓ q) else j q

/-- **The last `n` visits may bring no arrivals**: `pollTail n (j, {drained j}) > 0`. -/
theorem pollTail_drain_pos (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) (ℓ : Fin K → ℕ) (n : ℕ) (hn : n ≤ K)
    (j : Fin K → ℕ) : 0 < pollTail lam G ℓ n j {drainAfter ℓ n j} := by
  classical
  induction n generalizing j with
  | zero =>
    have hd : drainAfter ℓ 0 j = j := funext fun q => by
      have := q.2
      rw [drainAfter, ite_eq_right (by omega)]
    rw [hd, pollTail, Kernel.id_apply, Measure.dirac_apply_of_mem (mem_singleton j)]
    exact one_pos
  | succ n ih =>
    set k : Fin K := ⟨K - (n + 1), by omega⟩ with hk
    have hd : drainAfter ℓ n (afterServe ℓ k j) = drainAfter ℓ (n + 1) j := funext fun q => by
      by_cases hq : q = k
      · subst hq
        rw [drainAfter, drainAfter, ite_eq_right (by simp only [hk]; omega),
          ite_eq_left (by simp only [hk]; omega), afterServe, Function.update_self, served]
      · have hq' : q.1 ≠ K - (n + 1) := fun h => hq (Fin.ext h)
        rw [drainAfter, drainAfter, afterServe, Function.update_of_ne hq]
        by_cases h1 : K - n ≤ q.1
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    rw [← lintegral_indicator_one (measurableSet_singleton _),
      lintegral_pollTail_succ lam G ℓ hn]
    have hpos := visit_afterServe_pos lam hG ℓ k j
    have hih := ih (by omega) (afterServe ℓ k j)
    rw [hd, ← lintegral_indicator_one (measurableSet_singleton _)] at hih
    refine lt_of_lt_of_le (ENNReal.mul_pos hih.ne' hpos.ne') ?_
    rw [← lintegral_singleton (fun y => ∫⁻ z, ({drainAfter ℓ (n + 1) j} : Set (Fin K → ℕ)).indicator
      1 z ∂pollTail lam G ℓ n y) (afterServe ℓ k j)]
    exact setLIntegral_le_lintegral _ _

/-! ### Irreducibility -/

/-- **Chapman–Kolmogorov from one state**: `Pⁿ⁺²(x, A) ≥ P(x, {y}) Pⁿ⁺¹(y, A)`. -/
theorem poll_pow_succ_ge (P : Kernel (Fin K → ℕ) (Fin K → ℕ)) (n : ℕ) (x y : Fin K → ℕ)
    {A : Set (Fin K → ℕ)} (hA : MeasurableSet A) :
    P x {y} * (P ^ (n + 1)) y A ≤ (P ^ (n + 1 + 1)) x A := by
  rw [pow_succ_apply _ (n + 1) x hA, mul_comm,
    ← lintegral_singleton (fun z => (P ^ (n + 1)) z A) y]
  exact setLIntegral_le_lintegral _ _

/-- **The empty system is reached** from every state: the server may serve `min(j_k, ℓ_k)` at
every queue with no arrivals, which empties the system after finitely many cycles. -/
theorem pollKernel_reach_zero (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) {ℓ : Fin K → ℕ} (hℓ : ∀ k, 1 ≤ ℓ k)
    (j : Fin K → ℕ) : ∃ n, 0 < (pollKernel lam G ℓ ^ (n + 1)) j {0} := by
  set P := pollKernel lam G ℓ
  have hdrain : ∀ x, 0 < P x {drainAfter ℓ K x} := fun x =>
    pollTail_drain_pos lam hG ℓ K le_rfl x
  have hd : ∀ x : Fin K → ℕ, drainAfter ℓ K x = fun q => x q - min (x q) (ℓ q) := fun x =>
    funext fun q => by rw [drainAfter, ite_eq_left (by omega)]
  have key : ∀ N : ℕ, ∀ x : Fin K → ℕ, ∑ q, x q ≤ N → ∃ n, 0 < (P ^ (n + 1)) x {0} := by
    intro N
    induction N with
    | zero =>
      intro x hx
      have hx0 : x = 0 := funext fun q => by
        have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hx)) q (Finset.mem_univ q)
        exact this
      refine ⟨0, ?_⟩
      have h0 : drainAfter ℓ K x = 0 := by
        rw [hd, hx0]
        rfl
      rw [zero_add, pow_one, ← h0]
      exact hdrain x
    | succ N ih =>
      intro x hx
      by_cases hx0 : x = 0
      · exact ih x (by rw [hx0]; simp only [Pi.zero_apply, Finset.sum_const_zero, zero_le])
      · obtain ⟨q₀, hq₀⟩ : ∃ q, x q ≠ 0 := by
          by_contra h
          push Not at h
          exact hx0 (funext h)
        have hlt : ∑ q, drainAfter ℓ K x q < ∑ q, x q := by
          rw [hd]
          refine Finset.sum_lt_sum (fun q _ => Nat.sub_le _ _) ⟨q₀, Finset.mem_univ _, ?_⟩
          have : 1 ≤ min (x q₀) (ℓ q₀) := le_min (Nat.one_le_iff_ne_zero.2 hq₀) (hℓ q₀)
          omega
        obtain ⟨n, hn⟩ := ih (drainAfter ℓ K x) (by omega)
        exact ⟨n + 1, lt_of_lt_of_le (ENNReal.mul_pos (hdrain x).ne' hn.ne')
          (poll_pow_succ_ge P n x _ (measurableSet_singleton 0))⟩
  exact key _ j le_rfl

/-! ### Theorem 16.4.2 -/

/-- Integrals from lintegrals: a nonnegative `f` with `∫ f ≤ B < ∞` (in `[0, ∞]`) is integrable
with `∫ f ≤ B`. -/
theorem poll_integral_le {μ : Measure (Fin K → ℕ)} {f : (Fin K → ℕ) → ℝ} (hf : ∀ y, 0 ≤ f y)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (h : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ B) :
    Integrable f μ ∧ ∫ y, f y ∂μ ≤ B.toReal := by
  have hm : AEStronglyMeasurable f μ := (measurable_of_countable f).aestronglyMeasurable
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf)).2 (lt_of_le_of_lt h hB.lt_top)⟩,
    ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hm]
  exact ENNReal.toReal_mono hB h

/-- **Theorem 16.4.2** (MT p. 412): the gated-limited polling model is geometrically ergodic
provided `ρ = Σ_k λ_k m_k < 1` (`m_k = μ_k⁻¹` the mean service time at queue `k`) and the service
time laws are in `G⁺(γ)`, `∫ e^{γt} G_k(dt) < ∞`. Precisely: with `V(i) = Σ_k i_k m_k/d` for
`d = (1 − ρ) min_k ℓ_k m_k` (the book's `Σ_k i_k/μ_k`, scaled), the chain is positive and
aperiodic, and for some `δ > 0` it is `e^{δV}`-uniformly ergodic with
`Σ rⁿ |||Pⁿ − 1 ⊗ π|||_{e^{δV}} < ∞` for every invariant probability `π`. -/
theorem theorem_16_4_2 (hK : 0 < K) (lam : Fin K → ℝ≥0) {G : Fin K → Measure ℝ≥0}
    (hG : ∀ k, IsProbabilityMeasure (G k)) {ℓ : Fin K → ℕ} (hℓ : ∀ k, 1 ≤ ℓ k) {γ : ℝ}
    (hγ : 0 < γ) (hGγ : ∀ k, ∫⁻ t, ENNReal.ofReal (Real.exp (γ * t)) ∂G k ≠ ∞)
    (hm0 : ∀ k, 0 < (∫⁻ t, (t : ℝ≥0∞) ∂G k).toReal)
    (hρ : ∑ q, (lam q : ℝ) * (∫⁻ t, (t : ℝ≥0∞) ∂G q).toReal < 1) :
    haveI := isMarkovKernel_pollKernel lam hG ℓ
    ∃ w : Fin K → ℝ, (∀ q, 0 < w q) ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : Measure (Fin K → ℕ),
      IsPositive (pollKernel lam G ℓ) ψ ∧ IsAperiodic (pollKernel lam G ℓ) ψ ∧
      ∀ (μ : Measure (Fin K → ℕ)) [IsProbabilityMeasure μ], IsInvariant (pollKernel lam G ℓ) μ →
        IsVUniformlyErgodic (fun y => ENNReal.ofReal (Real.exp (δ * pollV w y)))
          (pollKernel lam G ℓ) μ ∧
        ∃ r : ℝ≥0∞, 1 < r ∧ r ≠ ∞ ∧ ∑' n, r ^ n * vErgDist
          (fun y => ENNReal.ofReal (Real.exp (δ * pollV w y))) (pollKernel lam G ℓ) μ n ≠ ∞ := by
  have hPM := isMarkovKernel_pollKernel lam hG ℓ
  set P := pollKernel lam G ℓ with hPdef
  -- the means
  set m : Fin K → ℝ := fun k => (∫⁻ t, (t : ℝ≥0∞) ∂G k).toReal with hmdef
  have hmfin : ∀ k, ∫⁻ t, (t : ℝ≥0∞) ∂G k ≠ ∞ := fun k => by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := γ⁻¹))
      (hGγ k)) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun t => ?_
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (inv_nonneg.2 hγ.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.add_one_le_exp (γ * t)
    rw [le_inv_mul_iff₀ hγ]
    nlinarith [NNReal.coe_nonneg t]
  have hmk : ∀ k, ∫⁻ t, (t : ℝ≥0∞) ∂G k = ENNReal.ofReal (m k) := fun k =>
    (ENNReal.ofReal_toReal (hmfin k)).symm
  set ρ : ℝ := ∑ q, (lam q : ℝ) * m q with hρdef
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun q _ => mul_nonneg (NNReal.coe_nonneg _)
    ENNReal.toReal_nonneg
  -- the weights
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  set dmin : ℝ := Finset.univ.inf' Finset.univ_nonempty fun k => (ℓ k : ℝ) * m k with hdmin
  have hdmin0 : 0 < dmin := by
    rw [hdmin, Finset.lt_inf'_iff]
    intro k _
    exact mul_pos (by exact_mod_cast hℓ k) (hm0 k)
  set d : ℝ := (1 - ρ) * dmin with hddef
  have hd0 : 0 < d := mul_pos (by linarith) hdmin0
  set w : Fin K → ℝ := fun q => m q / d with hwdef
  have hw0 : ∀ q, 0 < w q := fun q => div_pos (hm0 q) hd0
  have hw : ∀ q, 0 ≤ w q := fun q => (hw0 q).le
  refine ⟨w, hw0, ?_⟩
  -- the drift of one visit
  have hvis : ∀ k j, ∫⁻ y, ENNReal.ofReal (pollV w y) ∂visitMeasure lam G ℓ k j +
      ENNReal.ofReal ((1 - ρ) * w k * served ℓ k j) = ENNReal.ofReal (pollV w j) := fun k j => by
    rw [lintegral_visit_V lam hG ℓ k j hw, hmk k, pollV_afterServe]
    have hs : (served ℓ k j : ℝ) ≤ j k := by exact_mod_cast min_le_left _ _
    have hwj : w k * served ℓ k j ≤ pollV w j := by
      calc w k * served ℓ k j ≤ w k * j k := mul_le_mul_of_nonneg_left hs (hw k)
        _ ≤ pollV w j := Finset.single_le_sum (f := fun q => w q * (j q : ℝ))
            (fun q _ => mul_nonneg (hw q) (Nat.cast_nonneg _)) (Finset.mem_univ k)
    have hsum : ∑ q, ENNReal.ofReal (w q) * (lam q : ℝ≥0∞) =
        ENNReal.ofReal (∑ q, w q * lam q) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun q _ => mul_nonneg (hw q) (NNReal.coe_nonneg _)]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ENNReal.ofReal_mul (hw q), ENNReal.ofReal_coe_nnreal]
    rw [hsum, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (Finset.sum_nonneg fun q _ => mul_nonneg (hw q) (NNReal.coe_nonneg _)),
      ← ENNReal.ofReal_add (by linarith) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg (mul_nonneg (by linarith) (hw k))
        (Nat.cast_nonneg _))]
    congr 1
    have hρw : ∑ q, w q * (lam q : ℝ) = ρ / d := by
      rw [hρdef, Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hwdef]
      ring
    rw [hρw, hwdef]
    field_simp
    ring
  have hcw : ∀ k, 1 ≤ (1 - ρ) * w k * ℓ k := fun k => by
    have hk : dmin ≤ (ℓ k : ℝ) * m k := Finset.inf'_le _ (Finset.mem_univ k)
    have h1ρ : (1 - ρ) ≠ 0 := (show (0 : ℝ) < 1 - ρ by linarith).ne'
    rw [hwdef, hddef]
    rw [show (1 - ρ) * (m k / ((1 - ρ) * dmin)) * (ℓ k : ℝ) = (ℓ k * m k) / dmin by
      field_simp]
    rw [le_div_iff₀ hdmin0, one_mul]
    exact hk
  have hdrift := pollTail_drift lam hG ℓ hvis hcw K le_rfl
  -- the petite set `C`
  set C : Set (Fin K → ℕ) := {j | ∀ k, j k < ℓ k} with hCdef
  have hCfin : C.Finite := Set.Finite.pi' fun k => Set.finite_Iio (ℓ k)
  have hfullC : ∀ j, j ∉ C ↔ fullAfter ℓ K j := fun j => by
    constructor
    · intro hj
      simp only [hCdef, mem_ofPred_eq, not_forall, not_lt] at hj
      obtain ⟨k, hk⟩ := hj
      exact ⟨k, by omega, hk⟩
    · rintro ⟨k, -, hk⟩ hj
      exact absurd (hj k) (not_lt.2 hk)
  -- irreducibility and aperiodicity
  have hreach := pollKernel_reach_zero lam hG hℓ
  have hφ : IsPhiIrreducible P (Measure.dirac 0) := by
    intro A hA hφA x
    have h0 : (0 : Fin K → ℕ) ∈ A := by
      by_contra h
      rw [Measure.dirac_apply' _ hA, indicator_of_notMem h] at hφA
      exact lt_irrefl _ hφA
    obtain ⟨n, hn⟩ := hreach x
    exact lt_of_lt_of_le (lt_of_lt_of_le hn (measure_mono (singleton_subset_iff.2 h0)))
      (pow_le_hitProb _ hA n x)
  have hψ := isMaximalIrreducibility_maxIrrMeasure P hφ Measure.dirac_ne_zero
  set ψ := maxIrrMeasure P (Measure.dirac (0 : Fin K → ℕ)) with hψdef
  have hψ0 : 0 < ψ {0} := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := hψ.2.2 _ hφ h0
    rw [Measure.dirac_apply_of_mem (mem_singleton _)] at this
    exact one_ne_zero this
  have hP00 : 0 < P 0 {0} := by
    have h := pollTail_drain_pos lam hG ℓ K le_rfl 0
    have hd : drainAfter ℓ K 0 = 0 := funext fun q => by
      rw [drainAfter, ite_eq_left (by omega)]
      rfl
    rwa [hd] at h
  obtain ⟨Mn, hMC, hMν, -⟩ := exists_minorization_of_le (P := P) (measurableSet_singleton 0)
    ⟨0, rfl⟩ (ν' := P 0) (fun x hx => by rw [mem_singleton_iff.1 hx]) hP00
  have hap : IsAperiodic P ψ := isAperiodic_of_minorization hψ Mn (by rw [hMC]; exact hψ0)
    (by rw [hMν]; exact one_pos)
  have hC : IsPetite P C := by
    refine Set.Finite.induction_on (motive := fun s _ => IsPetite P s) C hCfin ?_ ?_
    · exact ⟨_, _, proposition_5_5_3 (show IsSmallSet P 1 (P 0) ∅ from
        ⟨MeasurableSet.empty, one_pos, IsProbabilityMeasure.ne_zero _, fun x hx =>
          absurd hx (notMem_empty x)⟩)⟩
    · intro a s _ _ hs
      have hsm : IsSmallSet P 1 (P a) {a} := ⟨measurableSet_singleton a, one_pos,
        IsProbabilityMeasure.ne_zero _, fun x hx => by rw [mem_singleton_iff.1 hx, pow_one]⟩
      rw [insert_eq]
      exact proposition_5_5_5_ii P hψ ⟨_, _, proposition_5_5_3 hsm⟩ hs
  -- the drift conditions
  set V : (Fin K → ℕ) → ℝ := pollV w with hVdef
  have hV0 : ∀ x, 0 ≤ V x := pollV_nonneg hw
  have hVm : Measurable V := measurable_of_countable _
  have hle : ∀ x, ∫⁻ y, ENNReal.ofReal (V y) ∂P x ≤ ENNReal.ofReal (V x) := fun x =>
    le_self_add.trans (hdrift x)
  have hint : ∀ x, Integrable V (P x) := fun x =>
    (poll_integral_le hV0 ENNReal.ofReal_ne_top (hle x)).1
  have hF1 : ∀ x ∉ C, ∫ y, V y ∂P x ≤ V x - 1 := fun x hx => by
    have h : ∫⁻ y, ENNReal.ofReal (V y) ∂P x + 1 ≤ ENNReal.ofReal (V x) := by
      have h0 := hdrift x
      rw [ite_eq_left ((hfullC x).1 hx)] at h0
      exact h0
    have hfin : ∫⁻ y, ENNReal.ofReal (V y) ∂P x ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle x)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_add hfin ENNReal.one_ne_top, ENNReal.toReal_ofReal (hV0 x),
      ENNReal.toReal_one] at h2
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hV0) hVm.aestronglyMeasurable]
    linarith
  have hF2 : ∀ x ∈ C, ∫ y, V y ∂P x ≤ ∑ k, w k * ℓ k := fun x hx => by
    refine (poll_integral_le hV0 ENNReal.ofReal_ne_top (hle x)).2.trans ?_
    rw [ENNReal.toReal_ofReal (hV0 x)]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (by exact_mod_cast (hx k).le) (hw k)
  -- the exponential bound (16.26)
  set κ : ℝ → ℝ := fun β => ∑ q, (lam q : ℝ) * (Real.exp (β * w q) - 1) with hκdef
  have hκc : Continuous κ := by rw [hκdef]; fun_prop
  have hκ0 : κ 0 = 0 := by
    simp only [hκdef, zero_mul, Real.exp_zero, sub_self, mul_zero, Finset.sum_const_zero]
  obtain ⟨β, hβγ, hβ⟩ : ∃ β : ℝ, κ β < γ ∧ 0 < β := by
    have h1 : ∀ᶠ β in 𝓝 (0 : ℝ), κ β < γ :=
      (hκc.tendsto 0).eventually (gt_mem_nhds (by rw [hκ0]; exact hγ))
    exact ((h1.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hκβ : 0 ≤ κ β := Finset.sum_nonneg fun q _ => mul_nonneg (NNReal.coe_nonneg _)
    (by have := Real.one_le_exp (mul_nonneg hβ.le (hw q)); linarith)
  set Mk : Fin K → ℝ≥0∞ := fun k => ∫⁻ t, ENNReal.ofReal (Real.exp (κ β * t)) ∂G k with hMkdef
  have hMk1 : ∀ k, 1 ≤ Mk k := fun k => by
    have := hG k
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂G k := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ Mk k := lintegral_mono fun t => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hκβ (NNReal.coe_nonneg t)))
  have hMkfin : ∀ k, Mk k ≠ ∞ := fun k => ne_top_of_le_ne_top (hGγ k) (lintegral_mono fun t =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβγ.le
      (NNReal.coe_nonneg t))))
  set F : ℝ≥0∞ := ∏ k, Mk k ^ ℓ k with hFdef
  have hFfin : F ≠ ∞ := ENNReal.prod_ne_top fun k _ => ENNReal.pow_ne_top (hMkfin k)
  have hvisexp : ∀ k j, ∫⁻ y, ENNReal.ofReal (Real.exp (β * pollV w y)) ∂visitMeasure lam G ℓ k j ≤
      ENNReal.ofReal (Real.exp (β * pollV w j)) * F := fun k j => by
    have hb : pollV w (afterServe ℓ k j) ≤ pollV w j := by
      rw [pollV_afterServe]
      have : 0 ≤ w k * served ℓ k j := mul_nonneg (hw k) (Nat.cast_nonneg _)
      linarith
    rw [lintegral_visit_exp lam hG ℓ k j w β]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hb hβ.le))) ?_
    calc (∫⁻ t, ENNReal.ofReal (Real.exp ((∑ q, lam q * (Real.exp (β * w q) - 1)) * t)) ∂G k)
          ^ served ℓ k j = Mk k ^ served ℓ k j := rfl
      _ ≤ Mk k ^ ℓ k := pow_le_pow_right₀ (hMk1 k) (min_le_right _ _)
      _ ≤ F := Finset.single_le_prod (fun i _ => one_le_pow₀ (hMk1 i)) (Finset.mem_univ k)
  have hexpP := pollTail_exp lam ℓ (fun y => ENNReal.ofReal (Real.exp (β * pollV w y)))
    hvisexp K le_rfl
  have hFK : F ^ K ≠ ∞ := ENNReal.pow_ne_top hFfin
  have h26all : ∀ x, Integrable (fun y => Real.exp (β * (V y - V x))) (P x) ∧
      ∫ y, Real.exp (β * (V y - V x)) ∂P x ≤ (F ^ K).toReal := fun x => by
    refine poll_integral_le (fun y => (Real.exp_pos _).le) hFK ?_
    have hpt : ∀ y, ENNReal.ofReal (Real.exp (β * (V y - V x))) =
        ENNReal.ofReal (Real.exp (-(β * V x))) * ENNReal.ofReal (Real.exp (β * V y)) := fun y => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [lintegral_congr hpt, lintegral_const_mul _ (measurable_of_countable _)]
    calc ENNReal.ofReal (Real.exp (-(β * V x))) * ∫⁻ y, ENNReal.ofReal (Real.exp (β * V y)) ∂P x
        ≤ ENNReal.ofReal (Real.exp (-(β * V x))) *
            (ENNReal.ofReal (Real.exp (β * V x)) * F ^ K) := by gcongr; exact hexpP x
      _ = F ^ K := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
            Real.exp_zero, ENNReal.ofReal_one, one_mul]
  have h26i : ∀ x, IntegrableOn (fun y => Real.exp (β * (V y - V x))) {y | V x ≤ V y} (P x) :=
    fun x => (h26all x).1.integrableOn
  have h26 : ∀ x, ∫ y in {y | V x ≤ V y}, Real.exp (β * (V y - V x)) ∂P x ≤ (F ^ K).toReal :=
    fun x => (setIntegral_le_integral (h26all x).1
      (ae_of_all _ fun y => (Real.exp_pos _).le)).trans (h26all x).2
  -- the bound on the decreases (16.27)
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (∑ k, w k * ℓ k)) with hEdef
  have hvisneg : ∀ k j, ∫⁻ y, ENNReal.ofReal (Real.exp (-pollV w y)) ∂visitMeasure lam G ℓ k j ≤
      ENNReal.ofReal (Real.exp (-pollV w j)) * E := fun k j => by
    refine (lintegral_visit_exp_neg lam hG ℓ k j hw).trans ?_
    rw [hEdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, pollV_afterServe]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : w k * served ℓ k j ≤ w k * ℓ k :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right _ _) (hw k)
    have h2 : w k * ℓ k ≤ ∑ k, w k * ℓ k := Finset.single_le_sum
      (f := fun k => w k * (ℓ k : ℝ)) (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _))
      (Finset.mem_univ k)
    linarith
  have hnegP := pollTail_exp lam ℓ (fun y => ENNReal.ofReal (Real.exp (-pollV w y)))
    hvisneg K le_rfl
  have hEK : 2 * E ^ K ≠ ∞ := ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h27all : ∀ x, Integrable ({y | V y < V x}.indicator fun y => (V y - V x) ^ 2) (P x) ∧
      ∫ y, {y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y ∂P x ≤ (2 * E ^ K).toReal :=
    fun x => by
      refine poll_integral_le (fun y => indicator_nonneg (fun y _ => sq_nonneg _) y) hEK ?_
      have hpt : ∀ y, ENNReal.ofReal ({y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y) ≤
          2 * (ENNReal.ofReal (Real.exp (V x)) * ENNReal.ofReal (Real.exp (-V y))) := fun y => by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        by_cases hS : y ∈ {y | V y < V x}
        · rw [indicator_of_mem hS]
          have hS' : V y < V x := hS
          have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ V x + -V y by linarith)
          nlinarith
        · rw [indicator_of_notMem hS]
          positivity
      calc ∫⁻ y, ENNReal.ofReal ({y | V y < V x}.indicator (fun y => (V y - V x) ^ 2) y) ∂P x
          ≤ ∫⁻ y, 2 * (ENNReal.ofReal (Real.exp (V x)) * ENNReal.ofReal (Real.exp (-V y))) ∂P x :=
            lintegral_mono hpt
        _ = 2 * (ENNReal.ofReal (Real.exp (V x)) *
              ∫⁻ y, ENNReal.ofReal (Real.exp (-V y)) ∂P x) := by
            rw [lintegral_const_mul _ (measurable_of_countable _),
              lintegral_const_mul _ (measurable_of_countable _)]
        _ ≤ 2 * (ENNReal.ofReal (Real.exp (V x)) *
              (ENNReal.ofReal (Real.exp (-V x)) * E ^ K)) := by gcongr; exact hnegP x
        _ = 2 * E ^ K := by
            rw [← mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  have h27i : ∀ x, IntegrableOn (fun y => (V y - V x) ^ 2) {y | V y < V x} (P x) := fun x =>
    (integrable_indicator_iff (measurableSet_lt hVm measurable_const)).1 (h27all x).1
  have h27 : ∀ x, ∫ y in {y | V y < V x}, (V y - V x) ^ 2 ∂P x ≤ (2 * E ^ K).toReal := fun x => by
    rw [← integral_indicator (measurableSet_lt hVm measurable_const)]
    exact (h27all x).2
  obtain ⟨δ, hδ0, -, hpos, hall⟩ := theorem_16_3_1 hψ hap hVm hV0 hC hβ hint hF1 hF2 h26i h26
    h27i h27
  refine ⟨δ, hδ0, ψ, hpos, hap, fun μ _ hμ => ?_⟩
  obtain ⟨-, hU, hsum⟩ := hall μ hμ
  exact ⟨hU, hsum⟩

end MeynTweedie.Epilogue
