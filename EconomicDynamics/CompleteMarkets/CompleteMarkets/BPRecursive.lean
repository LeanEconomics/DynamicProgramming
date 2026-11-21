/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPTree

/-!
# Recursive competitive equilibrium with debt constraints

Miao, §13.7, pp. 444–446. Shocks follow a Markov chain `P` on the finite set `S` (the history
probabilities are `bp_markovPr`, with the factorisation `eq_13_7_markov` in `BPTree`).
Endowments `yⁱ(s)`, dividends `d(s) ∈ ℝ^J` and debt limits `D̄ⁱ(s)` are time-invariant
functions of the current shock, the state is `(w, s)` with `w ∈ ℝ^I` the wealth distribution,
the price function is `p(w, s)` and the wealth distribution evolves by `w' = G(w, s, s')`
(13.28).

* `bp_rceFeasible`: the constraints of agent `i`'s problem (13.29),
  `c + p(w, s)·θ ≤ wⁱ + yⁱ(s)` and `wⁱ' = (p(w', s') + d(s'))·θ ≥ −D̄ⁱ(s')` for all `s'`.
* `bp_rceObj`: the objective `uⁱ(c) + β ∑_{s'} Vⁱ(wⁱ', w', s') Pr(s'|s)` of (13.29).
* `BPRCE` (Definition 13.7.1): value, consumption and portfolio functions solving (13.29), market
  clearing and consistency of the law of motion. `definition_13_7_1_instance` is a concrete RCE
  (one agent, a Lucas tree, linear utility).
* `bp_rce_walras`: when budgets bind, market clearing at `(w, s)` forces aggregate wealth to
  equal the value of the trees, `∑ᵢ wⁱ = ∑_j (p_j(w, s) + d_j(s))`.
* `bp_rce_aggregate_wealth`: consistency and clearing give `∑ᵢ Gⁱ(w, s, s') = ∑_j (p_j(w', s') +
  d_j(s'))`, so one agent's wealth can be removed from the state (the remark on p. 446).

**Departures.**
* Definition 13.7.1(ii) imposes market clearing at every `(w, s)`. By `bp_rce_walras` this is
  only possible at states whose aggregate wealth equals the value of the trees; we impose
  clearing and consistency on a state space `Ωs` of wealth distributions that is invariant
  under `G` (in the instance, `Ωs = {∑ᵢ wⁱ = p + d}`).
* Typographical: the clearing conditions read `∑ᵢ hⁱ(wⁱ; w, s)`, `∑ᵢ gⁱ(wⁱ; w, s)` for `cⁱ`,
  `θⁱ`, the law of motion is written `G(w, s, s)` for `G(w, s, s')`, and the stock supplies are
  normalised to one share each.
-/

namespace Miao.CompleteMarkets

variable {ι J S : Type*} [Fintype ι] [Fintype J] [Fintype S]

/-- The constraint set of agent `i`'s dynamic programming problem (13.29) at the state
`(wⁱ; w, s)`: the budget constraint and the debt constraints for every next shock. -/
def bp_rceFeasible (p : (ι → ℝ) → S → J → ℝ) (d : S → J → ℝ) (G : (ι → ℝ) → S → S → ι → ℝ)
    (y : ι → S → ℝ) (Dbar : ι → S → ℝ) (i : ι) (wi : ℝ) (w : ι → ℝ) (s : S) (c : ℝ)
    (θ : J → ℝ) : Prop :=
  c + ∑ j, p w s j * θ j ≤ wi + y i s ∧
    ∀ s', -Dbar i s' ≤ ∑ j, (p (G w s s') s' j + d s' j) * θ j

/-- The objective of (13.29): `uⁱ(c) + β ∑_{s'} Vⁱ(wⁱ', G(w, s, s'), s') Pr(s' | s)` with
`wⁱ' = (p(w', s') + d(s'))·θ`. -/
def bp_rceObj (u : ι → ℝ → ℝ) (β : ℝ) (Pm : S → S → ℝ) (V : ι → ℝ → (ι → ℝ) → S → ℝ)
    (p : (ι → ℝ) → S → J → ℝ) (d : S → J → ℝ) (G : (ι → ℝ) → S → S → ι → ℝ) (i : ι) (w : ι → ℝ)
    (s : S) (c : ℝ) (θ : J → ℝ) : ℝ :=
  u i c + β * ∑ s', V i (∑ j, (p (G w s s') s' j + d s' j) * θ j) (G w s s') s' * Pm s s'

variable (u : ι → ℝ → ℝ) (β : ℝ) (Pm : S → S → ℝ) (y : ι → S → ℝ) (d : S → J → ℝ)
  (Dbar : ι → S → ℝ) (V : ι → ℝ → (ι → ℝ) → S → ℝ) (c : ι → ℝ → (ι → ℝ) → S → ℝ)
  (θ : ι → ℝ → (ι → ℝ) → S → J → ℝ) (p : (ι → ℝ) → S → J → ℝ)
  (G : (ι → ℝ) → S → S → ι → ℝ) (Ωs : Set ((ι → ℝ) × S)) in
/-- **Definition 13.7.1** (Miao, p. 445). A recursive competitive equilibrium with debt
constraints: value functions `Vⁱ(wⁱ; w, s)`, consumption functions `cⁱ(wⁱ; w, s)` and portfolio
functions `θⁱ(wⁱ; w, s)`, a price function `p(w, s)` and a law of motion `G(w, s, s')` such that
(i) given `G` and `p`, `(cⁱ, θⁱ)` solves (13.29) and `Vⁱ` is its value; (ii) markets clear,
`∑ᵢ cⁱ = ∑ᵢ yⁱ(s) + ∑_j d_j(s)` and `∑ᵢ θⁱ_j = 1`; (iii) `Gⁱ(w, s, s') = (p(G(w, s, s'), s') +
d(s'))·θⁱ(wⁱ; w, s)`. (ii) and (iii) are imposed on a state space `Ωs` invariant under `G`. -/
structure BPRCE : Prop where
  feasible : ∀ i wi w s, bp_rceFeasible p d G y Dbar i wi w s (c i wi w s) (θ i wi w s)
  value : ∀ i wi w s, V i wi w s = bp_rceObj u β Pm V p d G i w s (c i wi w s) (θ i wi w s)
  optimal : ∀ i wi w s c' θ', bp_rceFeasible p d G y Dbar i wi w s c' θ' →
    bp_rceObj u β Pm V p d G i w s c' θ' ≤ V i wi w s
  clear_goods : ∀ w s, (w, s) ∈ Ωs → ∑ i, c i (w i) w s = ∑ i, y i s + ∑ j, d s j
  clear_assets : ∀ w s, (w, s) ∈ Ωs → ∀ j, ∑ i, θ i (w i) w s j = 1
  invariant : ∀ w s s', (w, s) ∈ Ωs → (G w s s', s') ∈ Ωs
  consistent : ∀ w s s', (w, s) ∈ Ωs → ∀ i,
    G w s s' i = ∑ j, (p (G w s s') s' j + d s' j) * θ i (w i) w s j

omit [Fintype S] in
/-- Walras's law for Definition 13.7.1 (Miao, p. 445): if every agent's budget binds at
`(w, s)` and the goods and asset markets clear there, then aggregate wealth equals the value of
the trees, `∑ᵢ wⁱ = ∑_j (p_j(w, s) + d_j(s))`. Hence (ii) can hold only on such states. -/
theorem bp_rce_walras (y : ι → S → ℝ) (d : S → J → ℝ) (c : ι → ℝ → (ι → ℝ) → S → ℝ)
    (θ : ι → ℝ → (ι → ℝ) → S → J → ℝ) (p : (ι → ℝ) → S → J → ℝ) (w : ι → ℝ) (s : S)
    (hbind : ∀ i, c i (w i) w s + ∑ j, p w s j * θ i (w i) w s j = w i + y i s)
    (hgoods : ∑ i, c i (w i) w s = ∑ i, y i s + ∑ j, d s j)
    (hassets : ∀ j, ∑ i, θ i (w i) w s j = 1) :
    ∑ i, w i = ∑ j, (p w s j + d s j) := by
  have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hbind i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hgoods, Finset.sum_comm] at h
  simp only [← Finset.mul_sum, hassets, mul_one] at h
  rw [Finset.sum_add_distrib]
  linarith

/-- Miao, p. 446: on the state space, consistency (iii) and asset market clearing give
`∑ᵢ Gⁱ(w, s, s') = ∑_j (p_j(G(w, s, s'), s') + d_j(s'))`: aggregate wealth is the value of the
trees, so one agent's wealth is determined by the others' and can be removed from the state. -/
theorem bp_rce_aggregate_wealth {u : ι → ℝ → ℝ} {β : ℝ} {Pm : S → S → ℝ} {y : ι → S → ℝ}
    {d : S → J → ℝ} {Dbar : ι → S → ℝ} {V : ι → ℝ → (ι → ℝ) → S → ℝ}
    {c : ι → ℝ → (ι → ℝ) → S → ℝ} {θ : ι → ℝ → (ι → ℝ) → S → J → ℝ}
    {p : (ι → ℝ) → S → J → ℝ} {G : (ι → ℝ) → S → S → ι → ℝ} {Ωs : Set ((ι → ℝ) × S)}
    (hR : BPRCE u β Pm y d Dbar V c θ p G Ωs) (w : ι → ℝ) (s s' : S) (hw : (w, s) ∈ Ωs) :
    ∑ i, G w s s' i = ∑ j, (p (G w s s') s' j + d s' j) := by
  simp only [hR.consistent w s s' hw]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hR.clear_assets w s hw, mul_one]

/-- A concrete recursive competitive equilibrium (`BPRCE`): one agent with linear utility
`u(c) = c` and discount factor `0 < β < 1`, one shock, one tree paying `d ≥ 0`, endowment `y`,
debt limit `0`. The price is `p = βd/(1 − β)`, the value function `V(wⁱ) = wⁱ + y/(1 − β)`,
consumption `wⁱ + y − p`, the portfolio `θ = 1`, the law of motion `G = p + d` and the state
space `{w = p + d}`. -/
theorem definition_13_7_1_instance (β y dv : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hd : 0 ≤ dv) :
    BPRCE (ι := Unit) (J := Unit) (S := Unit) (fun _ x => x) β (fun _ _ => 1) (fun _ _ => y)
      (fun _ _ => dv) (fun _ _ => 0) (fun _ wi _ _ => wi + y / (1 - β))
      (fun _ wi _ _ => wi + y - β * dv / (1 - β)) (fun _ _ _ _ _ => 1)
      (fun _ _ _ => β * dv / (1 - β)) (fun _ _ _ _ => β * dv / (1 - β) + dv)
      {x | ∑ i, x.1 i = β * dv / (1 - β) + dv} := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hp : β * (β * dv / (1 - β) + dv) = β * dv / (1 - β) := by field_simp; ring
  have hpd : 0 ≤ β * dv / (1 - β) + dv :=
    add_nonneg (div_nonneg (mul_nonneg hβ.le hd) (by linarith)) hd
  refine ⟨fun i wi w s => ⟨?_, fun s' => ?_⟩, fun i wi w s => ?_, fun i wi w s c' θ' hf => ?_,
    fun w s hw => ?_, fun w s hw j => ?_, fun w s s' hw => ?_, fun w s s' hw i => ?_⟩
  · simp
  · simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, neg_zero]
    exact hpd
  · simp only [bp_rceObj, Finset.univ_unique, Finset.sum_singleton, mul_one]
    field_simp
    ring
  · obtain ⟨hb, -⟩ := hf
    simp only [Finset.univ_unique, Finset.sum_singleton] at hb
    simp only [bp_rceObj, Finset.univ_unique, Finset.sum_singleton, mul_one]
    have e : β * ((β * dv / (1 - β) + dv) * θ' () + y / (1 - β)) =
        β * dv / (1 - β) * θ' () + β * y / (1 - β) := by
      rw [mul_add, ← mul_assoc, hp]
      ring
    rw [e]
    have e2 : wi + y / (1 - β) = wi + y + β * y / (1 - β) := by field_simp; ring
    rw [e2]
    linarith
  · simp only [Set.mem_ofPred_eq, Finset.univ_unique, Finset.sum_singleton] at hw ⊢
    rw [hw]
    ring
  · simp
  · simp
  · simp

end Miao.CompleteMarkets
