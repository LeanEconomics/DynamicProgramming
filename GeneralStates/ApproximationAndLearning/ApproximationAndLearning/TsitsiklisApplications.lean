/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.Tsitsiklis
import ApproximationAndLearning.QLearning
import ApproximationAndLearning.DampedIteration

/-!
# Applications of asynchronous stochastic approximation

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.1.3.4–§9.1.3.5 (pp. 307–309) and
Theorem 9.2.1 (p. 313), all from `sampled_tsitsiklis`.

* `AssetPricing.batch_converges`: the batch update (9.15) `v_{k+1} = v_k + α_k(T̂v_k − v_k)`, with
  one draw `x'(x) ∼ P(x, ·)` per state, converges to `v*` almost surely (p. 308).
* `AssetPricing.sequential_converges`: the sequential update (9.16), which moves only the
  visited entry `v(X_t)` towards `β[v(X') + d(X')]` with `X' ∼ P(X_t, ·)`, converges to `v*`
  almost surely when every state is updated with `∑ α = ∞` (p. 309).
* `FiniteMDP.theorem_9_2_1`: Q-learning (9.18) converges to `q*` almost surely when every
  state-action pair is updated with `∑ α = ∞` and `∑ α² < ∞` (Watkins–Dayan, Tsitsiklis).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ApproximationAndLearning

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℕ m0}

namespace AssetPricing

variable {X : Type*} [Fintype X] (M : AssetPricing X)

theorem norm_T_sub_le (v w : X → ℝ) : ‖M.T v - M.T w‖ ≤ M.β * ‖v - w‖ := by
  have := M.exercise_9_1_1 v w
  rwa [dist_eq_norm, dist_eq_norm] at this

theorem measurable_T : Measurable M.T :=
  (LipschitzWith.of_dist_le_mul (K := ⟨M.β, M.β_nonneg⟩) M.exercise_9_1_1).continuous.measurable

theorem abs_sample_le (v : X → ℝ) (y : X) :
    |M.β * (v y + M.d y)| ≤ M.β * ‖M.d‖ + M.β * ‖v‖ := by
  rw [abs_mul, abs_of_nonneg M.β_nonneg, ← mul_add, add_comm (‖M.d‖)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) M.β_nonneg
  · simpa using norm_le_pi_norm v y
  · simpa using norm_le_pi_norm M.d y

/-- §9.1.3.4 (p. 308): the batch update (9.15) `v_{k+1} = v_k + α_k(T̂v_k − v_k)` converges to
the fixed point `v*` of `T` almost surely, when the draws `x'_k(x)` are `ℱ_{k+1}`-measurable
with conditional law `P(x, ·)` given `ℱ_k`, and the adapted `α_k ∈ [0, 1]` have `∑ α_k = ∞`
almost surely and `∑ α_k² ≤ C`. -/
theorem batch_converges [DecidableEq X] {vstar : X → ℝ} (hvstar : M.T vstar = vstar)
    {v : ℕ → Ω → X → ℝ} {v0 : X → ℝ} {draw : ℕ → Ω → X → X} {α : ℕ → Ω → ℝ} {C : ℝ}
    (hdm : ∀ k x y, MeasurableSet[ℱ (k + 1)] {ω | draw k ω x = y})
    (hdP : ∀ k x y, P[fun ω => if draw k ω x = y then (1 : ℝ) else 0 | ℱ k] =ᵐ[P]
      fun _ => M.P x y)
    (hαm : ∀ k, Measurable[ℱ k] (α k)) (hα0 : ∀ k ω, 0 ≤ α k ω) (hα1 : ∀ k ω, α k ω ≤ 1)
    (hαsq : ∀ ω T, ∑ k ∈ Finset.range T, α k ω ^ 2 ≤ C)
    (hαdiv : ∀ᵐ ω ∂P, ¬ Summable fun k => α k ω)
    (hv0 : ∀ ω, v 0 ω = v0)
    (hrec : ∀ k ω, v (k + 1) ω = v k ω + α k ω • (M.That (v k ω) (draw k ω) - v k ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => v k ω) atTop (𝓝 vstar) :=
  sampled_tsitsiklis (ℱ := ℱ) (P := P) M.measurable_T M.β_nonneg M.β_lt_one
    (fun z => by have := M.norm_T_sub_le z vstar; rwa [hvstar] at this)
    (h := fun z _ y => M.β * (z y + M.d y))
    (fun _ y => measurable_const.mul ((measurable_pi_apply y).add measurable_const))
    (K := M.P) (fun z x => (M.That_unbiased z x).symm) M.P_sum (fun z _ y => M.abs_sample_le z y)
    (α := fun _ k ω => α k ω) (Ys := draw) (fun _ k => hαm k) (fun _ k ω => hα0 k ω)
    (fun _ k ω => hα1 k ω) (fun _ ω T => hαsq ω T) (fun _ => hαdiv) hdm
    (fun k x y => (hdP k x y).mono fun ω hω _ => hω) hv0 fun k ω x => by
      rw [hrec k ω]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, That]

/-- §9.1.3.5 (p. 309): the sequential update (9.16), which moves only the entry at the visited
state `X_t` (`ℱ_t`-measurable) towards `β[v(X') + d(X')]`, where the next state `X'_t` is
`ℱ_{t+1}`-measurable with conditional law `P(X_t, ·)`, converges to `v*` almost surely
provided every state `x` is updated with `∑_{t : X_t = x} α_t = ∞` almost surely and
`∑_{t : X_t = x} α_t² ≤ C`. For a single trajectory, `X_{t+1} = X'_t`. -/
theorem sequential_converges [DecidableEq X] {vstar : X → ℝ} (hvstar : M.T vstar = vstar)
    {v : ℕ → Ω → X → ℝ} {v0 : X → ℝ} {Xv Xn : ℕ → Ω → X} {α : ℕ → Ω → ℝ} {C : ℝ}
    (hXv : ∀ t x, MeasurableSet[ℱ t] {ω | Xv t ω = x})
    (hXn : ∀ t y, MeasurableSet[ℱ (t + 1)] {ω | Xn t ω = y})
    (hXP : ∀ t y, P[fun ω => if Xn t ω = y then (1 : ℝ) else 0 | ℱ t] =ᵐ[P]
      fun ω => M.P (Xv t ω) y)
    (hαm : ∀ t, Measurable[ℱ t] (α t)) (hα0 : ∀ t ω, 0 ≤ α t ω) (hα1 : ∀ t ω, α t ω ≤ 1)
    (hαsq : ∀ x ω T, ∑ t ∈ Finset.range T, (if Xv t ω = x then α t ω else 0) ^ 2 ≤ C)
    (hαdiv : ∀ x, ∀ᵐ ω ∂P, ¬ Summable fun t => if Xv t ω = x then α t ω else 0)
    (hv0 : ∀ ω, v 0 ω = v0)
    (hrec : ∀ t ω, v (t + 1) ω = update (v t ω) (Xv t ω)
      (v t ω (Xv t ω) + α t ω * (M.β * (v t ω (Xn t ω) + M.d (Xn t ω)) - v t ω (Xv t ω)))) :
    ∀ᵐ ω ∂P, Tendsto (fun t => v t ω) atTop (𝓝 vstar) := by
  refine sampled_tsitsiklis (ℱ := ℱ) (P := P) M.measurable_T M.β_nonneg M.β_lt_one
    (fun z => by have := M.norm_T_sub_le z vstar; rwa [hvstar] at this)
    (h := fun z _ y => M.β * (z y + M.d y))
    (fun _ y => measurable_const.mul ((measurable_pi_apply y).add measurable_const))
    (K := M.P) (fun z x => (M.That_unbiased z x).symm) M.P_sum (fun z _ y => M.abs_sample_le z y)
    (α := fun x t ω => if Xv t ω = x then α t ω else 0) (Ys := fun t ω _ => Xn t ω)
    (fun x t => Measurable.ite (hXv t x) (hαm t) measurable_const)
    (fun x t ω => by split_ifs; exacts [hα0 t ω, le_rfl])
    (fun x t ω => by split_ifs; exacts [hα1 t ω, zero_le_one]) hαsq hαdiv
    (fun t _ y => hXn t y) (fun t x y => ?_) hv0 fun t ω x => ?_
  · filter_upwards [hXP t y] with ω hω hne
    have hx : Xv t ω = x := by
      by_contra hc
      exact hne (by simp [hc])
    rw [hω, hx]
  · rw [hrec t ω]
    by_cases hx : Xv t ω = x
    · subst hx
      simp
    · simp [hx, Ne.symm hx]

end AssetPricing

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

theorem qmax_zero (x : X) : M.qmax 0 x = 0 := Finset.sup'_const _ _

theorem abs_qmax_le {q : M.G → ℝ} {c : ℝ} (h : ∀ p, |q p| ≤ c) (x : X) : |M.qmax q x| ≤ c := by
  have := M.abs_qmax_sub_le (q' := 0) (fun p => by simpa using h p) x
  rwa [qmax_zero, sub_zero] at this

theorem norm_S_sub_le [Fintype M.G] (q q' : M.G → ℝ) : ‖M.S q - M.S q'‖ ≤ M.β * ‖q - q'‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun p => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  refine M.S_contraction (fun p' => ?_) p
  have := norm_le_pi_norm (q - q') p'
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

theorem measurable_qmax [Finite M.G] (x : X) : Measurable fun q : M.G → ℝ => M.qmax q x := by
  let : Fintype M.G := Fintype.ofFinite _
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun q q' => ?_).continuous.measurable
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  refine M.abs_qmax_sub_le (fun p => ?_) x
  have := norm_le_pi_norm (q - q') p
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

/-- **Theorem 9.2.1** (p. 313; Watkins and Dayan, 1992; Tsitsiklis, 1994): let the visited
pair `(X_t, A_t)` be `ℱ_t`-measurable, the next state `X'_t` be `ℱ_{t+1}`-measurable with
conditional law `P(X_t, A_t, ·)` given `ℱ_t`, and the learning rates `α_t ∈ [0, 1]` be adapted.
If every pair `p` is updated with `∑_{t : (X_t, A_t) = p} α_t = ∞` almost surely and
`∑_{t : (X_t, A_t) = p} α_t² ≤ C` (every pair visited infinitely often under the
Robbins–Monro conditions), then the Q-learning iterates (9.18) converge to `q*` almost surely. -/
theorem theorem_9_2_1 [DecidableEq X] [Finite M.G] [DecidableEq M.G] {qstar : M.G → ℝ}
    (hqstar : M.S qstar = qstar) {q : ℕ → Ω → M.G → ℝ} {q0 : M.G → ℝ} {pv : ℕ → Ω → M.G}
    {Xn : ℕ → Ω → X} {α : ℕ → Ω → ℝ} {C : ℝ}
    (hpv : ∀ t p, MeasurableSet[ℱ t] {ω | pv t ω = p})
    (hXn : ∀ t y, MeasurableSet[ℱ (t + 1)] {ω | Xn t ω = y})
    (hXP : ∀ t y, P[fun ω => if Xn t ω = y then (1 : ℝ) else 0 | ℱ t] =ᵐ[P]
      fun ω => M.P (pv t ω).1.1 (pv t ω).1.2 y)
    (hαm : ∀ t, Measurable[ℱ t] (α t)) (hα0 : ∀ t ω, 0 ≤ α t ω) (hα1 : ∀ t ω, α t ω ≤ 1)
    (hαsq : ∀ p ω T, ∑ t ∈ Finset.range T, (if pv t ω = p then α t ω else 0) ^ 2 ≤ C)
    (hαdiv : ∀ p, ∀ᵐ ω ∂P, ¬ Summable fun t => if pv t ω = p then α t ω else 0)
    (hq0 : ∀ ω, q 0 ω = q0)
    (hrec : ∀ t ω, q (t + 1) ω = M.qUpdate (q t ω) (pv t ω) (Xn t ω) (α t ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => q t ω) atTop (𝓝 qstar) := by
  let : Fintype M.G := Fintype.ofFinite _
  set R := ∑ p : M.G, |M.r p.1.1 p.1.2|
  have hR : ∀ z : M.G → ℝ, ∀ p y, |M.Shat z p y| ≤ R + M.β * ‖z‖ := by
    intro z p y
    rw [Shat]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact Finset.single_le_sum (f := fun p : M.G => |M.r p.1.1 p.1.2|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ p)
    · rw [abs_mul, abs_of_nonneg M.β_nonneg]
      refine mul_le_mul_of_nonneg_left (M.abs_qmax_le (fun p' => ?_) y) M.β_nonneg
      simpa using norm_le_pi_norm z p'
  refine sampled_tsitsiklis (ℱ := ℱ) (P := P)
    (LipschitzWith.of_dist_le_mul (K := ⟨M.β, M.β_nonneg⟩) fun q q' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact M.norm_S_sub_le q q').continuous.measurable M.β_nonneg M.β_lt_one
    (fun z => by have := M.norm_S_sub_le z qstar; rwa [hqstar] at this)
    (h := M.Shat) (fun p y => measurable_const.add (measurable_const.mul (M.measurable_qmax y)))
    (K := fun p y => M.P p.1.1 p.1.2 y) (fun z p => (M.Shat_unbiased z p).symm)
    (fun p => M.P_sum _ _ p.2) hR
    (α := fun p t ω => if pv t ω = p then α t ω else 0) (Ys := fun t ω _ => Xn t ω)
    (fun p t => Measurable.ite (hpv t p) (hαm t) measurable_const)
    (fun p t ω => by split_ifs; exacts [hα0 t ω, le_rfl])
    (fun p t ω => by split_ifs; exacts [hα1 t ω, zero_le_one]) hαsq hαdiv
    (fun t _ y => hXn t y) (fun t p y => ?_) hq0 fun t ω p => ?_
  · filter_upwards [hXP t y] with ω hω hne
    have hp : pv t ω = p := by
      by_contra hc
      exact hne (by simp [hc])
    rw [hω, hp]
  · rw [hrec t ω, qUpdate_apply]
    by_cases hp : pv t ω = p
    · subst hp
      simp
    · simp [hp, Ne.symm hp]

end FiniteMDP

end SargentStachurski.ApproximationAndLearning
