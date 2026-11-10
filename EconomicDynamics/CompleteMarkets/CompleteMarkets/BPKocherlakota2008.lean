/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPNoBubble
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bubbles and debt limits (Kocherlakota 2008, Exercise 13.7)

Miao, §13.9, Exercise 13.7 (p. 454), on the event tree of `BPTree`. A representative agent with
`∑ₜ ∑_{sᵗ} Pr(sᵗ) βᵗ u(c(sᵗ))`, a constant endowment `y`, one share of a long-lived asset with
constant dividend `d` and price `p(sᵗ)`, and complete Arrow securities `b(s^{t+1})` with prices
`q(s^{t+1})` (initial holdings zero). The budget constraint at `sᵗ` is
`c + a p + ∑ q b' ≤ y + a_−(p + d) + b` and the debt constraint is
`a(sᵗ)(p(s^{t+1}) + d) + b(s^{t+1}) ≥ −D(s^{t+1})`.

* `ex_13_7_bubble`: if `b̃` satisfies `b̃_t = βE_t b̃_{t+1}` and the debt limit is
  `D̂ = y/(1 − β) − b̃`, then `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and `p = βd/(1 − β) + b̃` support
  the no-trade equilibrium `c = y + d`, `a = 1`, `b = 0`: the plan is feasible and beats every
  feasible plan with convergent utility. The asset prices solve the Euler equations
  (`ex_13_7_prices`).
* `ex_13_7`: the case `b̃ = 0`, debt limit `D = y/(1 − β)`, price `p^f = βd/(1 − β)`.

The proof is the tree version of the sufficiency argument: deflating by `βᵗ Pr(sᵗ)`, the budget
constraints telescope, and the debt constraint bounds the deflated terminal wealth below by
`−β^{T+1} y/(1 − β) + b̃_0` (the bubble is a discounted martingale), which offsets the bubble in
the initial wealth `p_0 + d`.

**Departure.** The exercise says "prove that the equilibrium price is given by" `q`, `p^f`. We
prove that these prices (and, with the perturbed limit, `p^f + b̃`) support the equilibrium and
solve the Euler equations; uniqueness of the equilibrium price is not formalised. The utility
`u` is any function with a supergradient `u'(c̄) ≥ 0` at `c̄ = y + d`.
-/

open Filter Topology

namespace Miao.CompleteMarkets

/-- The budget and debt constraints of Exercise 13.7 for the plan `(c, a, b)` at prices `(q, p)`
and debt limit `D`: positive consumption, the date-0 budget (one share, no Arrow securities),
the date-`t` budgets and the debt constraints. -/
def bp_k08Budget {S : Type*} [Fintype S] (q p : List S → ℝ) (y dv : ℝ) (D : List S → ℝ)
    (c a b : List S → ℝ) : Prop :=
  (∀ h, 0 < c h) ∧ c [] + a [] * p [] + ∑ s, q [s] * b [s] ≤ y + (p [] + dv) ∧
    (∀ s h, c (s :: h) + a (s :: h) * p (s :: h) + ∑ s', q (s' :: s :: h) * b (s' :: s :: h) ≤
      y + a h * (p (s :: h) + dv) + b (s :: h)) ∧
    ∀ s h, -D (s :: h) ≤ a h * (p (s :: h) + dv) + b (s :: h)

/-- Expected discounted utility `∑ₜ βᵗ ∑_{sᵗ} Pr(sᵗ) u(c(sᵗ))`. -/
noncomputable def bp_k08U {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (u : ℝ → ℝ)
    (c : List S → ℝ) : ℝ :=
  ∑' t, β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))

/-- A discounted martingale `b̃_t = β E_t b̃_{t+1}` satisfies `βᵏ E[b̃_k] = b̃_0`. -/
theorem bp_k08_martingale {S : Type*} [Fintype S] (T : BPTree S) (β : ℝ) (bt : List S → ℝ)
    (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (k : ℕ) :
    β ^ k * bp_nodeSum k (fun h => T.pr h * bt h) = bt [] := by
  have key : ∀ k h, β ^ k * bp_condExp T k bt h = bt h := by
    intro k
    induction k with
    | zero => intro h; simp [bp_condExp_zero]
    | succ k ih =>
      intro h
      rw [show k + 1 = 1 + k by omega, bp_condExp_add, pow_add, pow_one, mul_assoc,
        ← bp_condExp_smul, bp_condExp_congr T 1 _ bt ih, ← hb h]
  rw [← bp_condExp_root]
  exact key k []

/-- `∑_{t≤n} βᵗ x + β^{n+1} x/(1 − β) = x/(1 − β)`. -/
theorem bp_k08_geom (β x : ℝ) (hβ1 : β < 1) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), β ^ t * x + β ^ (n + 1) * x / (1 - β) = x / (1 - β) := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
    field_simp
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ β (n + 1)]
    have e : β ^ (n + 1) * β * x / (1 - β) = β ^ (n + 1) * x / (1 - β) - β ^ (n + 1) * x := by
      field_simp
      ring
    rw [e]
    ring

/-- Exercise 13.7 (Miao, p. 454): the prices of the perturbed economy solve the Euler equations
of the no-trade allocation: `q(s^{t+1}) u'(c̄) = β Pr(s^{t+1} | sᵗ) u'(c̄)` and
`p_t = βE_t[p_{t+1} + d]`. -/
theorem ex_13_7_prices {S : Type*} [Fintype S] (T : BPTree S) (β dv : ℝ) (hβ1 : β < 1)
    (bt : List S → ℝ) (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (h : List S) :
    β * dv / (1 - β) + bt h = β * bp_condExp T 1 (fun g => β * dv / (1 - β) + bt g + dv) h := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  rw [bp_condExp_add_fun, bp_condExp_add_fun, bp_condExp_const, bp_condExp_const]
  rw [hb h]
  field_simp
  ring

/-- **Exercise 13.7**, perturbed debt limit (Kocherlakota 2008, Miao, p. 454). Let `0 < β < 1`,
`y > 0`, `d ≥ 0`, let `b̃` satisfy `b̃_t = βE_t b̃_{t+1}`, and let the debt limit be
`D̂(s^{t+1}) = y/(1 − β) − b̃(s^{t+1})`. With `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and
`p = βd/(1 − β) + b̃`, the no-trade plan `c = y + d`, `a = 1`, `b = 0` is feasible and is optimal
among feasible plans with convergent utility, for any `u` with a supergradient
`u'(y + d) ≥ 0` at `y + d`. -/
theorem ex_13_7_bubble {S : Type*} [Fintype S] (T : BPTree S) (β y dv : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) (hd : 0 ≤ dv) (bt : List S → ℝ)
    (hb : ∀ h, bt h = β * bp_condExp T 1 bt h) (u : ℝ → ℝ) (du : ℝ)
    (hsg : ∀ x, 0 < x → u x ≤ u (y + dv) + du * (x - (y + dv))) (hdu : 0 ≤ du) :
    let q : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: h => β * T.pr (s :: h) / T.pr h
    let p : List S → ℝ := fun h => β * dv / (1 - β) + bt h
    let D : List S → ℝ := fun h => y / (1 - β) - bt h
    bp_k08Budget q p y dv D (fun _ => y + dv) (fun _ => 1) (fun _ => 0) ∧
      ∀ c a b, bp_k08Budget q p y dv D c a b →
        Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))) →
        bp_k08U T β u c ≤ bp_k08U T β u (fun _ => y + dv) := by
  intro q p D
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hpf : 0 ≤ β * dv / (1 - β) := div_nonneg (mul_nonneg hβ.le hd) (by linarith)
  refine ⟨⟨fun _ => by linarith, ?_, fun s h => ?_, fun s h => ?_⟩, ?_⟩
  · simp only [mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · simp only [mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · simp only [p, D, add_zero, neg_sub]
    have : 0 ≤ y / (1 - β) := div_nonneg hy.le (by linarith)
    linarith
  intro c a b hB hs
  obtain ⟨hc, hb0, hbs, hdebt⟩ := hB
  -- deflated wealth `W(sᵗ)` carried into each node
  set W : List S → ℝ := fun g => match g with
    | [] => p [] + dv
    | s :: h => a h * (p (s :: h) + dv) + b (s :: h) with hW
  -- the pricing identity at every node
  have hprice : ∀ h, T.pr h * (a h * p h + ∑ s, q (s :: h) * b (s :: h)) =
      β * ∑ s, T.pr (s :: h) * W (s :: h) := by
    intro h
    have hph : p h = β * bp_condExp T 1 (fun g => p g + dv) h :=
      ex_13_7_prices T β dv hβ1 bt hb h
    have hc1 := bp_pr_mul_condExp_one T (fun g => p g + dv) h
    rw [hph, mul_add, ← mul_assoc, mul_comm (T.pr h) (a h), mul_assoc, mul_left_comm (T.pr h),
      hc1, Finset.mul_sum]
    simp only [q, W, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    field_simp [(T.pr_pos h).ne']
  -- per-node budget in deflated form
  have hnode : ∀ h, T.pr h * c h + β * ∑ s, T.pr (s :: h) * W (s :: h) ≤
      T.pr h * y + T.pr h * W h := by
    intro h
    rw [← hprice h]
    have hpr := (T.pr_pos h).le
    cases h with
    | nil =>
      have := mul_le_mul_of_nonneg_left hb0 hpr
      simp only [W]
      nlinarith
    | cons s h =>
      have := mul_le_mul_of_nonneg_left (hbs s h) hpr
      simp only [W]
      nlinarith
  -- telescoping
  have htel : ∀ n, ∑ t ∈ Finset.range (n + 1), β ^ t * bp_nodeSum t (fun h => T.pr h * c h) +
      β ^ (n + 1) * bp_nodeSum (n + 1) (fun h => T.pr h * W h) ≤
      ∑ t ∈ Finset.range (n + 1), β ^ t * y + W [] := by
    have hdate : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * c h) +
        β ^ (t + 1) * bp_nodeSum (t + 1) (fun h => T.pr h * W h) ≤
        β ^ t * y + β ^ t * bp_nodeSum t (fun h => T.pr h * W h) := by
      intro t
      have hm := bp_nodeSum_mono t _ _ hnode
      rw [bp_nodeSum_add, bp_nodeSum_add, bp_nodeSum_smul, bp_nodeSum_const] at hm
      rw [bp_nodeSum_succ, pow_succ]
      have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le t)
      nlinarith
    intro n
    induction n with
    | zero =>
      have := hdate 0
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, bp_nodeSum_zero,
        T.pr_nil] at this ⊢
      linarith
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => β ^ t * y)]
      have := hdate (n + 1)
      linarith
  -- the debt constraint bounds terminal wealth
  have hterm : ∀ n, -(β ^ (n + 1) * y / (1 - β)) + bt [] ≤
      β ^ (n + 1) * bp_nodeSum (n + 1) (fun h => T.pr h * W h) := by
    intro n
    have hm : bp_nodeSum (n + 1) (fun h => T.pr h * (-(y / (1 - β)) + bt h)) ≤
        bp_nodeSum (n + 1) (fun h => T.pr h * W h) := by
      refine bp_nodeSum_succ_mono n _ _ (fun s h => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (T.pr_pos _).le
      have := hdebt s h
      simp only [W]
      simp only [D] at this
      linarith
    have e : bp_nodeSum (n + 1) (fun h => T.pr h * (-(y / (1 - β)) + bt h)) =
        -(y / (1 - β)) + bp_nodeSum (n + 1) (fun h => T.pr h * bt h) := by
      have hf : (fun h => T.pr h * (-(y / (1 - β)) + bt h)) =
          fun h => T.pr h * (-(y / (1 - β))) + T.pr h * bt h := by
        funext h
        ring
      rw [hf, bp_nodeSum_add, bp_nodeSum_const]
    rw [e] at hm
    have hmart := bp_k08_martingale T β bt hb (n + 1)
    have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le (n + 1))
    rw [mul_add, hmart] at this
    have e2 : β ^ (n + 1) * -(y / (1 - β)) = -(β ^ (n + 1) * y / (1 - β)) := by ring
    linarith
  -- partial sums of deflated consumption
  have hcons : ∀ n, ∑ t ∈ Finset.range (n + 1),
      β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) ≤
      β ^ (n + 1) * (y + dv) / (1 - β) := by
    intro n
    have hg1 := bp_k08_geom β y hβ1 n
    have hg2 := bp_k08_geom β (y + dv) hβ1 n
    have hsplit : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) =
        β ^ t * bp_nodeSum t (fun h => T.pr h * c h) - β ^ t * (y + dv) := by
      intro t
      have : (fun h => T.pr h * (c h - (y + dv))) =
          fun h => T.pr h * c h - T.pr h * (y + dv) := by
        funext h
        ring
      rw [this, bp_nodeSum_sub, bp_nodeSum_const]
      ring
    simp only [hsplit, Finset.sum_sub_distrib]
    have hW0 : W [] = β * dv / (1 - β) + bt [] + dv := rfl
    have := htel n
    have := hterm n
    have e : β * dv / (1 - β) + dv = dv / (1 - β) := by field_simp; ring
    have e2 : (y + dv) / (1 - β) = y / (1 - β) + dv / (1 - β) := by ring
    linarith
  -- utility comparison
  have hsc : Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv))) := by
    simp only [bp_nodeSum_const]
    exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have hutil : ∀ n, ∑ t ∈ Finset.range (n + 1),
      (β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv))) ≤
      du * (β ^ (n + 1) * (y + dv) / (1 - β)) := by
    intro n
    have hle : ∀ t, β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv)) ≤
        du * (β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv)))) := by
      intro t
      have hm : bp_nodeSum t (fun h => T.pr h * u (c h)) ≤
          bp_nodeSum t (fun h => T.pr h * u (y + dv) + du * (T.pr h * (c h - (y + dv)))) := by
        refine bp_nodeSum_mono t _ _ (fun h => ?_)
        have := mul_le_mul_of_nonneg_left (hsg (c h) (hc h)) (T.pr_pos h).le
        nlinarith
      rw [bp_nodeSum_add, bp_nodeSum_smul] at hm
      have := mul_le_mul_of_nonneg_left hm (pow_nonneg hβ.le t)
      nlinarith
    calc _ ≤ ∑ t ∈ Finset.range (n + 1),
          du * (β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv)))) :=
          Finset.sum_le_sum (fun t _ => hle t)
      _ = du * ∑ t ∈ Finset.range (n + 1),
          β ^ t * bp_nodeSum t (fun h => T.pr h * (c h - (y + dv))) := by
          rw [Finset.mul_sum]
      _ ≤ du * (β ^ (n + 1) * (y + dv) / (1 - β)) :=
          mul_le_mul_of_nonneg_left (hcons n) hdu
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1),
      (β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h)) -
        β ^ t * bp_nodeSum t (fun h => T.pr h * u (y + dv)))) atTop
      (𝓝 (bp_k08U T β u c - bp_k08U T β u (fun _ => y + dv))) := by
    unfold bp_k08U
    rw [← hs.tsum_sub hsc]
    exact (tendsto_add_atTop_iff_nat 1).2 (hs.sub hsc).hasSum.tendsto_sum_nat
  have hzero : Tendsto (fun n : ℕ => du * (β ^ (n + 1) * (y + dv) / (1 - β))) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const ((y + dv) / (1 - β))
    have := this.const_mul du
    simp only [zero_mul, mul_zero] at this
    convert this using 2 with n
    simp only [Function.comp_apply]
    ring
  have := le_of_tendsto_of_tendsto' hlim hzero hutil
  linarith

/-- **Exercise 13.7** (Kocherlakota 2008, Miao, p. 454). With the debt limit
`D = y/(1 − β)`, the Arrow prices `q(s^{t+1}) = β Pr(s^{t+1} | sᵗ)` and the fundamental price
`p^f = βd/(1 − β)` support the equilibrium `c = y + d`, `a = 1`, `b = 0`, and `p^f` solves
`p = βE_t[p + d]`. -/
theorem ex_13_7 {S : Type*} [Fintype S] (T : BPTree S) (β y dv : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) (hd : 0 ≤ dv) (u : ℝ → ℝ) (du : ℝ)
    (hsg : ∀ x, 0 < x → u x ≤ u (y + dv) + du * (x - (y + dv))) (hdu : 0 ≤ du) :
    let q : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: h => β * T.pr (s :: h) / T.pr h
    let p : List S → ℝ := fun _ => β * dv / (1 - β)
    let D : List S → ℝ := fun _ => y / (1 - β)
    (∀ h, p h = β * bp_condExp T 1 (fun g => p g + dv) h) ∧
    bp_k08Budget q p y dv D (fun _ => y + dv) (fun _ => 1) (fun _ => 0) ∧
      ∀ c a b, bp_k08Budget q p y dv D c a b →
        Summable (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * u (c h))) →
        bp_k08U T β u c ≤ bp_k08U T β u (fun _ => y + dv) := by
  intro q p D
  have hb0 : ∀ h : List S, (fun _ => (0 : ℝ)) h = β * bp_condExp T 1 (fun _ => 0) h := by
    intro h
    simp [bp_condExp_const]
  have key := ex_13_7_bubble T β y dv hβ hβ1 hy hd (fun _ => 0) hb0 u du hsg hdu
  simp only [add_zero, sub_zero] at key
  refine ⟨fun h => ?_, key⟩
  have := ex_13_7_prices T β dv hβ1 (fun _ => 0) hb0 h
  simpa using this

end Miao.CompleteMarkets
