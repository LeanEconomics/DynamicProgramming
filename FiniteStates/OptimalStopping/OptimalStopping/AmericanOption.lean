/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Reduction

/-!
# American options

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.2.1 (pp. 119–122).

A finite-horizon American call with expiry `T` is embedded in infinite-horizon
optimal stopping by putting the date into the state: `t ∈ {1, …, T + 1}`
updates by `m(t) = min{t + 1, T + 1}`, the stock price is `Sₜ = Zₜ + Wₜ` with
`Zₜ` `Q`-Markov and `Wₜ` IID with distribution `φ`, the exit reward is
`1{t ≤ T}(z + w − K)`, the continuation reward is zero and `β = 1/(1 + r)`.
The state is `(w, (t, z))`, the IID component first, so that the product
reduction of §4.1.4.2 applies: the continuation value operator (4.16) acts on
`ℝ^{T × Z}` and `σ*(t, w, z) = 1{e(t, w, z) ≥ h*(t, z)}`.

The claim of p. 122 that the exercise region expands with `t` is proved: `v*`
is nonnegative and nonincreasing in the date, so `h*(t, z)` is nonincreasing
in `t` and exercise at `(t, w, z)` implies exercise at `(m(t), w, z)` while
the option is alive.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

/-- The data of the American option model (p. 120): expiry `T`, the IID component `W` with
distribution `φ` and values `wval`, the Markov component `Z` with matrix `Q` and values `zval`,
strike `K` and interest rate `r > 0`. -/
structure AmericanOption (W Z : Type*) [Fintype W] [Fintype Z] where
  T : ℕ
  φ : W → ℝ
  φ_dist : IsDistribution φ
  wval : W → ℝ
  Q : Matrix Z Z ℝ
  Q_markov : IsMarkov Q
  zval : Z → ℝ
  K : ℝ
  r : ℝ
  r_pos : 0 < r

namespace AmericanOption

variable {W Z : Type*} [Fintype W] [Fintype Z] (m : AmericanOption W Z)

/-- The dates `{1, …, T + 1}`, represented zero-based: `t : Fin (T + 1)` stands for the date
`t + 1`. -/
abbrev Time := Fin (m.T + 1)

/-- The date update `m(t) = min{t + 1, T + 1}` (p. 120), zero-based. -/
def next (t : m.Time) : m.Time := ⟨min (t.val + 1) m.T, by omega⟩

/-- The option is alive at date `t` (book: `t ≤ T`), zero-based `t < T`. -/
abbrev alive (t : m.Time) : Prop := t.val < m.T

theorem next_of_alive {t : m.Time} (h : m.alive t) : (m.next t).val = t.val + 1 := by
  unfold next
  simp only
  unfold alive at h
  omega

theorem next_of_not_alive {t : m.Time} (h : ¬ m.alive t) : m.next t = t := by
  unfold alive at h
  apply Fin.ext
  unfold next
  simp only
  have := t.2
  omega

theorem next_next_of_last {t : m.Time} (h : ¬ m.alive (m.next t)) : m.next (m.next t) = m.next t :=
  m.next_of_not_alive h

/-- The discount factor `β = 1/(1 + r)` lies in `(0, 1)`. -/
theorem β_pos : (0 : ℝ) < 1 / (1 + m.r) := div_pos one_pos (by linarith [m.r_pos])

theorem β_lt_one : (1 : ℝ) / (1 + m.r) < 1 := by
  rw [div_lt_one (by linarith [m.r_pos])]
  linarith [m.r_pos]

/-- The deterministic-time kernel on `T × Z`: `1{t' = m(t)} Q(z, z')`. -/
noncomputable def timeKernel : Matrix (m.Time × Z) (m.Time × Z) ℝ :=
  Matrix.of fun x x' => (if x'.1 = m.next x.1 then 1 else 0) * m.Q x.2 x'.2

theorem isMarkov_timeKernel : IsMarkov m.timeKernel where
  nonneg x x' := by
    simp only [timeKernel, Matrix.of_apply]
    split_ifs <;> simp [m.Q_markov.nonneg]
  rowsum x := by
    rw [Fintype.sum_prod_type]
    have h : ∀ (t' : m.Time) (z' : Z),
        m.timeKernel x (t', z') = if t' = m.next x.1 then m.Q x.2 z' else 0 := by
      intro t' z'
      simp only [timeKernel, Matrix.of_apply]
      split_ifs <;> simp
    simp only [h]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq' univ (m.next x.1), mem_univ, ite_true]
    exact m.Q_markov.rowsum x.2

/-- `(Kv)(t, z) = ∑_{z'} v(m(t), z') Q(z, z')` for the time kernel. -/
theorem timeKernel_mulVec (v : m.Time × Z → ℝ) (t : m.Time) (z : Z) :
    (m.timeKernel *ᵥ v) (t, z) = ∑ z', v (m.next t, z') * m.Q z z' := by
  rw [mulVec_apply_eq, Fintype.sum_prod_type]
  have h : ∀ (t' : m.Time) (z' : Z), v (t', z') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then v (m.next t, z') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The exit reward (p. 121): `e(t, w, z) = 1{t ≤ T}(z + w − K)`. -/
noncomputable def e (x : W × (m.Time × Z)) : ℝ :=
  if m.alive x.2.1 then m.zval x.2.2 + m.wval x.1 - m.K else 0

/-- The option as a stopping problem on `W × (T × Z)` (p. 120): transitions
`P((w, t, z), (w', t', z')) = 1{t' = m(t)} φ(w') Q(z, z')`, zero continuation reward,
`β = 1/(1 + r)`. -/
noncomputable def problem : StoppingProblem (W × (m.Time × Z)) :=
  productProblem m.φ_dist m.isMarkov_timeKernel (fun _ => 0) m.e m.β_pos m.β_lt_one

/-- The transition probabilities, as on p. 120. -/
theorem problem_P (w : W) (t : m.Time) (z : Z) (w' : W) (t' : m.Time) (z' : Z) :
    m.problem.P (w, (t, z)) (w', (t', z')) =
      (if t' = m.next t then 1 else 0) * m.φ w' * m.Q z z' := by
  simp only [problem, productProblem, productKernel_apply, timeKernel, Matrix.of_apply]
  ring

/-- `(Pv)(w, t, z) = ∑_{z'} (∑_{w'} v(w', m(t), z') φ(w')) Q(z, z')`: the time component updates
deterministically and `w` does not matter. -/
theorem problem_mulVec (v : W × (m.Time × Z) → ℝ) (w : W) (t : m.Time) (z : Z) :
    (m.problem.P *ᵥ v) (w, (t, z)) =
      ∑ z', (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' := by
  rw [problem, productProblem, productKernel_mulVec, Fintype.sum_prod_type]
  have h : ∀ (t' : m.Time) (z' : Z),
      (∑ w', v (w', (t', z')) * m.φ w') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The Bellman equation (p. 121):
`v(t, w, z) = max{e(t, w, z), β ∑_{w'} ∑_{z'} v(m(t), w', z') φ(w') Q(z, z')}`. -/
theorem bellman_equation [DecidableEq W] [DecidableEq Z] (w : W) (t : m.Time) (z : Z) :
    m.problem.vstar (w, (t, z)) =
      max (m.e (w, (t, z)))
        (1 / (1 + m.r) *
          ∑ z', (∑ w', m.problem.vstar (w', (m.next t, z')) * m.φ w') * m.Q z z') := by
  have := congrFun m.problem.isFixedPt_T_vstar.eq (w, (t, z))
  rw [← this, StoppingProblem.T, StoppingProblem.cont, problem_mulVec]
  simp [problem, productProblem]

variable [DecidableEq W] [DecidableEq Z]

omit [DecidableEq W] [DecidableEq Z] in
/-- The continuation value operator (4.16) on `ℝ^{T × Z}`:
`(Ch)(t, z) = β ∑_{z'} ∑_{w'} max{e(m(t), w', z'), h(m(t), z')} φ(w') Q(z, z')`. -/
theorem reducedC_apply (h : m.Time × Z → ℝ) (t : m.Time) (z : Z) :
    productProblem.reducedC (φ := m.φ) (Q := m.timeKernel) (fun _ => 0) m.e (β := 1 / (1 + m.r))
      h (t, z) =
      1 / (1 + m.r) * ∑ z', (∑ w', max (m.e (w', (m.next t, z'))) (h (m.next t, z')) * m.φ w') *
        m.Q z z' := by
  simp only [productProblem.reducedC, zero_add]
  rw [Fintype.sum_prod_type]
  have hk : ∀ (t' : m.Time) (z' : Z),
      (∑ w', max (m.e (w', (t', z'))) (h (t', z')) * m.φ w') * m.timeKernel (t, z) (t', z') =
      if t' = m.next t then
        (∑ w', max (m.e (w', (m.next t, z'))) (h (m.next t, z')) * m.φ w') * m.Q z z' else 0 := by
    intro t' z'
    simp only [timeKernel, Matrix.of_apply]
    split_ifs with h
    · rw [h]
      ring
    · ring
  simp only [hk]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' univ (m.next t), mem_univ, ite_true]

/-- The continuation value function `h*(t, z)` (p. 121): the unique fixed point of (4.16). -/
noncomputable def hstar : m.Time × Z → ℝ :=
  productProblem.reducedH m.φ_dist m.isMarkov_timeKernel (fun _ => 0) m.e m.β_pos m.β_lt_one

/-- The full continuation value depends on `(t, z)` only, through `h*` (p. 121). -/
theorem hstar_eq (w : W) (t : m.Time) (z : Z) :
    m.problem.hstar (w, (t, z)) = m.hstar (t, z) :=
  productProblem.hstar_eq_reducedH _ _ _ _ _ _ w (t, z)

omit [DecidableEq W] [DecidableEq Z] in
/-- `Cᵏh → h*` for every `h ∈ ℝ^{T × Z}` (p. 121). -/
theorem tendsto_iterate_reducedC (h : m.Time × Z → ℝ) :
    Tendsto (fun k : ℕ => (productProblem.reducedC (φ := m.φ) (Q := m.timeKernel) (fun _ => 0) m.e
      (β := 1 / (1 + m.r)))^[k] h) atTop (𝓝 m.hstar) :=
  productProblem.tendsto_iterate_reducedC _ _ _ _ _ _ h

/-- The optimal policy (p. 121): exercise at `(t, w, z)` iff `e(t, w, z) ≥ h*(t, z)`. -/
theorem sigmaStar_eq_true_iff (w : W) (t : m.Time) (z : Z) :
    m.problem.sigmaStar (w, (t, z)) = true ↔ m.hstar (t, z) ≤ m.e (w, (t, z)) := by
  rw [StoppingProblem.sigmaStar_eq_true_iff, hstar_eq]
  exact Iff.rfl

theorem isOptimal_sigmaStar : m.problem.IsOptimal m.problem.sigmaStar :=
  m.problem.isOptimal_sigmaStar

/-! ### The exercise region expands with the date (p. 122) -/

/-- `v* ≥ 0` and `v*` is nonincreasing in the date: `v*(w, m(t), z) ≤ v*(w, t, z)`. The Bellman
operator preserves this closed set of functions. -/
theorem vstar_nonneg_antitone :
    (∀ x, 0 ≤ m.problem.vstar x) ∧
      ∀ w t z, m.problem.vstar (w, (m.next t, z)) ≤ m.problem.vstar (w, (t, z)) := by
  set A : Set (W × (m.Time × Z) → ℝ) :=
    {v | (∀ x, 0 ≤ v x) ∧ ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} with hA
  have hclosed : IsClosed A := by
    have h1 : IsClosed {v : W × (m.Time × Z) → ℝ | ∀ x, 0 ≤ v x} := by
      have : {v : W × (m.Time × Z) → ℝ | ∀ x, 0 ≤ v x} = ⋂ x, {v | 0 ≤ v x} := by ext; simp
      rw [this]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    have h2 : IsClosed {v : W × (m.Time × Z) → ℝ |
        ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} := by
      have : {v : W × (m.Time × Z) → ℝ | ∀ w t z, v (w, (m.next t, z)) ≤ v (w, (t, z))} =
          ⋂ (w) (t) (z), {v | v (w, (m.next t, z)) ≤ v (w, (t, z))} := by ext; simp
      rw [this]
      exact isClosed_iInter fun w => isClosed_iInter fun t => isClosed_iInter fun z =>
        isClosed_le (continuous_apply _) (continuous_apply _)
    exact h1.inter h2
  have hβ : (0 : ℝ) ≤ 1 / (1 + m.r) := m.β_pos.le
  -- the continuation payoff, written through `problem_mulVec`
  have hcont : ∀ v w t z, m.problem.cont v (w, (t, z)) =
      1 / (1 + m.r) * ∑ z', (∑ w', v (w', (m.next t, z')) * m.φ w') * m.Q z z' := by
    intro v w t z
    rw [StoppingProblem.cont, problem_mulVec]
    simp [problem, productProblem]
  have hmaps : ∀ v ∈ A, m.problem.T v ∈ A := by
    rintro v ⟨hv0, hvm⟩
    have hT0 : ∀ x, 0 ≤ m.problem.T v x := by
      rintro ⟨w, t, z⟩
      refine le_max_of_le_right ?_
      rw [hcont]
      refine mul_nonneg hβ (sum_nonneg fun z' _ => mul_nonneg (sum_nonneg fun w' _ =>
        mul_nonneg (hv0 _) (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z'))
    refine ⟨hT0, fun w t z => ?_⟩
    -- continuation payoffs are ordered because `v` is
    have hc : m.problem.cont v (w, (m.next t, z)) ≤ m.problem.cont v (w, (t, z)) := by
      rw [hcont, hcont]
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right
        (sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right (hvm w' (m.next t) z')
          (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z')) hβ
    by_cases halive : m.alive (m.next t)
    · -- both dates are alive: equal exit rewards
      have ht : m.alive t := by
        unfold alive at halive ⊢
        unfold next at halive
        simp only at halive
        omega
      have he : m.e (w, (m.next t, z)) = m.e (w, (t, z)) := by
        simp [e, halive, ht]
      change max (m.e (w, (m.next t, z))) (m.problem.cont v (w, (m.next t, z))) ≤
        max (m.e (w, (t, z))) (m.problem.cont v (w, (t, z)))
      rw [he]
      exact max_le_max le_rfl hc
    · -- the option is dead at `m(t)`: exit reward `0 ≤ Tv(w, t, z)`
      have he : m.e (w, (m.next t, z)) = 0 := by simp [e, halive]
      change max (m.e (w, (m.next t, z))) (m.problem.cont v (w, (m.next t, z))) ≤
        max (m.e (w, (t, z))) (m.problem.cont v (w, (t, z)))
      rw [he]
      exact max_le (hT0 (w, (t, z))) (hc.trans (le_max_right _ _))
  have h0 : (0 : W × (m.Time × Z) → ℝ) ∈ A := ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩
  have hiter : ∀ k : ℕ, m.problem.T^[k] 0 ∈ A := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact hclosed.mem_of_tendsto (m.problem.tendsto_iterate_T 0) (Eventually.of_forall hiter)

omit [DecidableEq W] [DecidableEq Z] in
/-- The continuation value is nonincreasing in the date: `h*(m(t), z) ≤ h*(t, z)` (p. 122). -/
theorem hstar_antitone (t : m.Time) (z : Z) : m.hstar (m.next t, z) ≤ m.hstar (t, z) := by
  classical
  obtain ⟨w⟩ : Nonempty W := by
    by_contra hW
    rw [not_nonempty_iff] at hW
    exact absurd m.φ_dist.sum_eq_one (by simp)
  rw [← hstar_eq m w, ← hstar_eq m w]
  have := (m.vstar_nonneg_antitone).2
  have hc : ∀ x, m.problem.c x = 0 := fun _ => rfl
  have hβ : m.problem.β = 1 / (1 + m.r) := rfl
  simp only [StoppingProblem.hstar, StoppingProblem.cont, problem_mulVec, hc, hβ, zero_add]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun z' _ => mul_le_mul_of_nonneg_right
    (sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right (this w' (m.next t) z')
      (m.φ_dist.nonneg w')) (m.Q_markov.nonneg z z')) m.β_pos.le

/-- The exercise region expands with `t` (p. 122): while the option is alive at `m(t)`, exercising
at `(t, w, z)` is optimal only if exercising at `(m(t), w, z)` is. -/
theorem exercise_region_expands (w : W) (t : m.Time) (z : Z) (halive : m.alive (m.next t)) :
    m.problem.sigmaStar (w, (t, z)) = true → m.problem.sigmaStar (w, (m.next t, z)) = true := by
  rw [sigmaStar_eq_true_iff, sigmaStar_eq_true_iff]
  intro h
  have ht : m.alive t := by
    unfold alive at halive ⊢
    unfold next at halive
    simp only at halive
    omega
  have he : m.e (w, (m.next t, z)) = m.e (w, (t, z)) := by simp [e, halive, ht]
  rw [he]
  exact (m.hstar_antitone t z).trans h

end AmericanOption

end SargentStachurski.OptimalStopping
