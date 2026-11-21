/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.DiscreteBudget
import EulerTransversality.Sufficiency
import RamseyCassKoopmans.Concavity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The discrete-time Hamiltonian

AKMM, §9.2 (pp. 244–246): the consumption–saving problem
`max Σ_{t≤T} β^t u(c_t)` subject to `a_{t+1} = w + (1 + r)a_t − c_t`, `a_0` given and
`a_{T+1} ≥ 0`, solved through the "discrete Hamiltonian" `H_t = β^t u(c_t) + μ_t(ra_t + w − c_t)`.

* The Lagrangian rewriting `L = Σ H_t − Σ μ_t(a_{t+1} − a_t) + λa_{T+1}`
  (`discreteHamiltonian_lagrangian`); the first-order conditions (9.9), (9.10) as derivatives of
  `H_t`, and the terminal conditions (9.11)–(9.13) with `a_{T+1} = 0`.
* The Euler equation (9.14), `β^T u'(c_T) = u'(c_0)/(1 + r)^T`, and the equivalence of (9.13)
  with `a_{T+1}/(1 + r)^T = 0` and with `a_{T+1} = 0`.
* The book uses Kuhn–Tucker without proving that the conditions are sufficient. With `u`
  concave, a path satisfying the Euler equation and `a_{T+1} = 0` is optimal
  (`discreteHamiltonian_finite_sufficient`). Necessity and the infinite horizon are in
  `DiscreteOptimality`.
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, p. 244: the discrete-time Hamiltonian `H_t = β^t u(c_t) + μ_t(ra_t + w − c_t)`. -/
noncomputable def discreteHamiltonian (β r w : ℝ) (u : ℝ → ℝ) (t : ℕ) (μ a c : ℝ) : ℝ :=
  β ^ t * u c + μ * (r * a + w - c)

/-- AKMM, p. 244: the Lagrangian
`L = Σ_{t≤T} β^t u(c_t) + Σ_{t≤T} μ_t((1 + r)a_t + w − c_t − a_{t+1}) + λa_{T+1}`. -/
noncomputable def discreteLagrangian (β r w : ℝ) (u : ℝ → ℝ) (T : ℕ) (lam : ℝ)
    (μ a c : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) +
    ∑ t ∈ Finset.range (T + 1), μ t * ((1 + r) * a t + w - c t - a (t + 1)) + lam * a (T + 1)

/-- AKMM, (9.8) and p. 244: with the budget in difference form, the Lagrangian is
`L = Σ_{t≤T} H_t − Σ_{t≤T} μ_t(a_{t+1} − a_t) + λa_{T+1}`. -/
theorem discreteHamiltonian_lagrangian (β r w : ℝ) (u : ℝ → ℝ) (T : ℕ) (lam : ℝ)
    (μ a c : ℕ → ℝ) :
    discreteLagrangian β r w u T lam μ a c =
      ∑ t ∈ Finset.range (T + 1), discreteHamiltonian β r w u t (μ t) (a t) (c t) -
        ∑ t ∈ Finset.range (T + 1), μ t * (a (t + 1) - a t) + lam * a (T + 1) := by
  simp only [discreteLagrangian, discreteHamiltonian]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- AKMM, (9.8), p. 244: the budget (9.6) in difference form `a_{t+1} − a_t = ra_t + w − c_t`. -/
theorem eq_9_8 {r w a a' c : ℝ} : a' = w + (1 + r) * a - c ↔ a' - a = r * a + w - c := by
  constructor <;> intro h <;> linarith

/-- AKMM, (9.9), p. 244: `∂H_t/∂c_t = β^t u'(c_t) − μ_t`, so (9.9) is `β^t u'(c_t) = μ_t`. -/
theorem eq_9_9 {β r w μ a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) (t : ℕ) :
    HasDerivAt (fun x => discreteHamiltonian β r w u t μ a x) (β ^ t * u'c - μ) c ∧
      (β ^ t * u'c - μ = 0 ↔ β ^ t * u'c = μ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h := (hu.const_mul (β ^ t)).add (((hasDerivAt_id c).neg.const_add (r * a + w)).const_mul μ)
  change HasDerivAt (fun x => β ^ t * u x + μ * (r * a + w - x)) _ c
  convert h using 1
  · funext x
    simp only [Pi.add_apply, Pi.neg_apply, id]
    ring
  · ring

/-- AKMM, (9.10), p. 245: `∂H_{t+1}/∂a_{t+1} = rμ_{t+1}`, so (9.10),
`∂H_{t+1}/∂a_{t+1} + μ_{t+1} − μ_t = 0`, is `μ_t = (1 + r)μ_{t+1}`. -/
theorem eq_9_10 {β r w μ μ' a c : ℝ} {u : ℝ → ℝ} (t : ℕ) :
    HasDerivAt (fun x => discreteHamiltonian β r w u (t + 1) μ' x c) (μ' * r) a ∧
      (μ' * r + μ' - μ = 0 ↔ μ = (1 + r) * μ') := by
  refine ⟨?_, by constructor <;> intro h <;> linarith⟩
  have h := ((((hasDerivAt_id a).const_mul r).add_const (w - c)).const_mul μ').const_add
    (β ^ (t + 1) * u c)
  change HasDerivAt (fun x => β ^ (t + 1) * u c + μ' * (r * x + w - c)) _ a
  convert h using 1
  · funext x
    simp only [id]
    ring
  · ring

/-- AKMM, (9.11)–(9.13), p. 245: from (9.9) at `T`, `−μ_T + λ = 0` and `λa_{T+1} = 0`, the
transversality condition `β^T u'(c_T)a_{T+1} = 0`; since `β^T u'(c_T) > 0`, `a_{T+1} = 0`. -/
theorem eq_9_13 {β u'T μT lam aT1 : ℝ} {T : ℕ} (h99 : β ^ T * u'T = μT) (h911 : -μT + lam = 0)
    (h912 : lam * aT1 = 0) :
    β ^ T * u'T * aT1 = 0 ∧ (0 < β → 0 < u'T → aT1 = 0) := by
  have hlam : lam = β ^ T * u'T := by linarith
  have h : β ^ T * u'T * aT1 = 0 := by rw [← hlam]; exact h912
  refine ⟨h, fun hβ hu => ?_⟩
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (mul_pos (pow_pos hβ T) hu).ne'
  · exact h

/-- AKMM, (9.14), p. 245: `β^t u'(c_t) = μ_t` and `μ_t = (1 + r)μ_{t+1}` give the Euler
equation `u'(c_t) = β(1 + r)u'(c_{t+1})`. -/
theorem eq_9_14 {β r u't u't1 μt μt1 : ℝ} {t : ℕ} (hβ : β ≠ 0)
    (h1 : β ^ t * u't = μt) (h2 : β ^ (t + 1) * u't1 = μt1) (h3 : μt = (1 + r) * μt1) :
    u't = β * (1 + r) * u't1 := by
  have hp : β ^ t ≠ 0 := pow_ne_zero _ hβ
  apply mul_left_cancel₀ hp
  rw [h1, h3, ← h2, pow_succ]
  ring

/-- AKMM, p. 245: iterating the Euler equation from `0` to `t ≤ T`,
`β^t u'(c_t) = u'(c_0)/(1 + r)^t`. -/
theorem discreteHamiltonian_marginal {β r : ℝ} {mu : ℕ → ℝ} {T : ℕ} (hr : 0 < 1 + r)
    (heuler : ∀ t, t < T → mu t = β * (1 + r) * mu (t + 1)) :
    ∀ t, t ≤ T → β ^ t * mu t = mu 0 / (1 + r) ^ t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    have he := heuler n (by omega)
    rw [he] at h
    rw [pow_succ, pow_succ, eq_div_iff (mul_pos (pow_pos hr n) hr).ne']
    rw [eq_div_iff (pow_pos hr n).ne'] at h
    linarith [h]

/-- AKMM, p. 245: given the Euler equation and `u'(c_0) > 0`, `β > 0`, the TVC (9.13)
`β^T u'(c_T)a_{T+1} = 0` is equivalent to `a_{T+1}/(1 + r)^T = 0` and to `a_{T+1} = 0`. -/
theorem discreteHamiltonian_tvc_iff {β r aT1 : ℝ} {mu : ℕ → ℝ} {T : ℕ} (hr : 0 < 1 + r)
    (hmu : 0 < mu 0) (heuler : ∀ t, t < T → mu t = β * (1 + r) * mu (t + 1)) :
    (β ^ T * mu T * aT1 = 0 ↔ aT1 / (1 + r) ^ T = 0) ∧ (aT1 / (1 + r) ^ T = 0 ↔ aT1 = 0) := by
  have h := discreteHamiltonian_marginal hr heuler T le_rfl
  have hp := pow_pos hr T
  rw [h]
  refine ⟨?_, by rw [div_eq_zero_iff]; simp [hp.ne']⟩
  rw [div_mul_eq_mul_div, div_eq_zero_iff, div_eq_zero_iff, mul_eq_zero]
  simp [hmu.ne', hp.ne']

/-- AKMM, §9.2, pp. 244–245: **sufficiency** of the conditions in the finite horizon. If `u` is
concave on `(0, ∞)` with derivative `u'`, `1 + r > 0`, and a path with positive consumption
satisfies the budget (9.6), the Euler equation (9.14) and `a_{T+1} = 0`, then it maximizes
`Σ_{t≤T} β^t u(c_t)` over every path from the same `a_0` with positive consumption and
`a_{T+1} ≥ 0`. -/
theorem discreteHamiltonian_finite_sufficient {β r w : ℝ} {u u' : ℝ → ℝ} {T : ℕ}
    (hr : 0 < 1 + r) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hβ : 0 ≤ β)
    {a c a' c' : ℕ → ℝ} (hc : ∀ t, 0 < c t) (hb : ∀ t, a (t + 1) = w + (1 + r) * a t - c t)
    (heuler : ∀ t, t < T → u' (c t) = β * (1 + r) * u' (c (t + 1))) (hT : a (T + 1) = 0)
    (hpos : 0 ≤ u' (c 0))
    (hc' : ∀ t, 0 < c' t) (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (h0 : a' 0 = a 0) (hT' : 0 ≤ a' (T + 1)) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) := by
  have hm := discreteHamiltonian_marginal (mu := fun t => u' (c t)) hr heuler
  have hr' : ∀ _ : ℕ, 0 < 1 + r := fun _ => hr
  have B := appendix_9A3_discrete_budget (r := fun _ => r) (w := fun _ => w) hr' hb T
  have B' := appendix_9A3_discrete_budget (r := fun _ => r) (w := fun _ => w) hr' hb' T
  simp only [discreteBudget_const_discount] at B B'
  rw [h0] at B'
  have hstep : ∀ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      β ^ t * u (c t) + u' (c 0) * (c' t / (1 + r) ^ t - c t / (1 + r) ^ t) := by
    intro t ht
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t))
      (Set.mem_Ioi.mpr (hc' t)) (hu (c t) (hc t))
    have hmt := hm t (by simpa [Nat.lt_succ_iff] using ht)
    have hk : u' (c 0) * (c' t / (1 + r) ^ t - c t / (1 + r) ^ t) =
        β ^ t * u' (c t) * (c' t - c t) := by
      rw [hmt]
      ring
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg hβ t)]
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hdiff : ∑ t ∈ Finset.range (T + 1), c' t / (1 + r) ^ t -
      ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t = -(a' (T + 1) / (1 + r) ^ T) := by
    rw [hT, zero_div] at B
    linarith
  rw [hdiff] at hsum
  have : 0 ≤ u' (c 0) * (a' (T + 1) / (1 + r) ^ T) :=
    mul_nonneg hpos (div_nonneg hT' (pow_pos hr T).le)
  linarith

end AKMM.ContinuousTime
