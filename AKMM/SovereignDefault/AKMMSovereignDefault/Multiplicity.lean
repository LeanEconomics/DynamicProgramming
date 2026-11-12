/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSovereignDefault.MarkovPerfect

/-!
# Multiple Markov perfect equilibria on a finite debt grid

AKMM, Appendix 24.A.1, p. 901: "Aguiar and Amador (2020) show that there can be multiple
Markov equilibria in the model with long-term debt (`δ ∈ (0, 1)`), implying that the initial
guess plays a non-trivial role in the computation of the equilibrium." Beyond the text.

On the book's computational setting (finite grids, Appendix 24.A.1; the project's `SDModel`
and `IsMPE`, departure D4) we give explicit economies with two Markov perfect equilibria, both
verified analytically against every equilibrium condition (a)–(c) of §24.4.3:

* with long-term debt, `δ = 1/2` (`mu_grid_long_term_two_mpe`);
* and already with **one-period debt**, `δ = 1` (`mu_grid_one_period_two_mpe`). The uniqueness
  theorem for `δ = 1` (`ue_mpe_unique`) therefore needs a continuum of debt choices: on a grid
  it fails (correction 9). The economy satisfies every other hypothesis of `ue_mpe_unique`
  (`u = id` nondecreasing and uniformly continuous, `φ ≥ 0`, `r > 0`, `ψ = 0`).

The economy: one income level `Y = 1`, debt grid `{0, 1}` (`false`, `true`), `u = id`,
`φ = 1/4`, `β = 1/2`, permanent exclusion `ψ = 0`, `r = 1/4`. In the *good* equilibrium the
sovereign borrows `1` and rolls it over forever at the risk-free price; in the *bad* one lenders
expect default on debt `1`, the price of debt `1` is `0`, and a sovereign holding debt `1`
cannot roll it over, so it defaults: the expectation is self-fulfilling. Default yields
`V^D = (3/4)/(1 − 1/2) = 3/2`, between the bad and good values of repaying debt `1`. On a
continuum the sovereign would escape the bad equilibrium by issuing a little less debt
(the replication argument of `ue_replication`); on the grid the nearest lower debt is `0`.

This is not Aguiar–Amador's (2020) multiplicity, which arises with a continuum of debt levels
from debt dilution under long-term debt; that construction is not formalised.
-/

namespace AKMM.SovereignDefault

open Finset SargentStachurski.RecursiveDecisionProcesses

/-- The economy of the multiplicity examples, for a coupon decay `δ ∈ [0, 1]`: one income
level `1`, debt grid `{0, 1}`, `u = id`, `φ = 1/4`, `β = 1/2`, `ψ = 0`. -/
noncomputable def mu_econ (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : SDModel Unit Bool where
  inc := fun _ => 1
  P := fun _ _ => 1
  markov := ⟨fun _ _ => zero_le_one, fun _ => by simp⟩
  bond := fun b => if b then 1 else 0
  b₀ := false
  bond_b₀ := rfl
  u := id
  φ := fun _ => 1 / 4
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  ψ := 0
  ψ_nonneg := le_rfl
  ψ_le_one := zero_le_one
  δ := δ
  δ_nonneg := h0
  δ_le_one := h1

/-- The maximum over the two-point debt grid. -/
theorem mu_sup_bool (f : Bool → ℝ) :
    (univ : Finset Bool).sup' ⟨false, mem_univ _⟩ f = max (f true) (f false) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_)
    (max_le (le_sup' f (mem_univ true)) (le_sup' f (mem_univ false)))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- **Two Markov perfect equilibria with one-period debt on a grid** (`δ = 1`, `r = 1/4`).
Good: no default, `q ≡ 4/5`, the sovereign always issues `1`, `V(0) = 13/5`, `V(1) = 8/5`. Bad:
default on debt `1`, `q(0) = 4/5`, `q(1) = 0`, the sovereign issues `0`, `V(0) = 2`,
`V(1) = V^D = 3/2`, `V^R(1) = 1`. The prices of debt `1` differ. -/
theorem mu_grid_one_period_two_mpe :
    IsMPE (mu_econ 1 zero_le_one le_rfl) (1 / 4) (fun b _ => if b then 8 / 5 else 13 / 5)
        (fun b _ => if b then 8 / 5 else 13 / 5) (fun _ => 3 / 2) (fun _ _ => 0)
        (fun _ _ => true) (fun _ _ => 4 / 5) ∧
      IsMPE (mu_econ 1 zero_le_one le_rfl) (1 / 4) (fun b _ => if b then 3 / 2 else 2)
        (fun b _ => if b then 1 else 2) (fun _ => 3 / 2) (fun b _ => if b then 1 else 0)
        (fun _ _ => false) (fun b _ => if b then 0 else 4 / 5) ∧
      (fun _ _ => (4 / 5 : ℝ)) true () ≠ (fun (b : Bool) (_ : Unit) =>
        if b then (0 : ℝ) else 4 / 5) true () := by
  refine ⟨⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, ⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, by norm_num⟩ <;>
  (try simp only [SDModel.repayValue, SDModel.defaultValue, SDModel.cons, bp_op12, mu_econ,
    mu_sup_bool, univ_unique, sum_singleton, id]) <;>
  first | (cases b <;> norm_num) | (cases m <;> norm_num) | norm_num

/-- **Two Markov perfect equilibria with long-term debt on a grid** (`δ = 1/2`, `r = 1/4`;
AKMM, p. 901, Aguiar–Amador 2020 for the continuum). Good: no default, `q ≡ 2/3` (the
risk-free price `δ/(δ + r)`), the sovereign always issues up to `1`, `V(0) = 5/2`,
`V(1) = 5/3`. Bad: default on debt `1`, `q(0) = 2/3`, `q(1) = 0`, `V(0) = 2`, `V(1) = 3/2`,
`V^R(1) = 5/4`. The prices of debt `1` differ. -/
theorem mu_grid_long_term_two_mpe :
    IsMPE (mu_econ (1 / 2) (by norm_num) (by norm_num)) (1 / 4)
        (fun b _ => if b then 5 / 3 else 5 / 2) (fun b _ => if b then 5 / 3 else 5 / 2)
        (fun _ => 3 / 2) (fun _ _ => 0) (fun _ _ => true) (fun _ _ => 2 / 3) ∧
      IsMPE (mu_econ (1 / 2) (by norm_num) (by norm_num)) (1 / 4)
        (fun b _ => if b then 3 / 2 else 2) (fun b _ => if b then 5 / 4 else 2) (fun _ => 3 / 2)
        (fun b _ => if b then 1 else 0) (fun b _ => b) (fun b _ => if b then 0 else 2 / 3) ∧
      (fun _ _ => (2 / 3 : ℝ)) true () ≠ (fun (b : Bool) (_ : Unit) =>
        if b then (0 : ℝ) else 2 / 3) true () := by
  refine ⟨⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, ⟨fun b y => ?_, fun y => ?_, fun b y => ?_, fun m y => ?_, fun b y => ?_,
    fun b y => ?_⟩, by norm_num⟩ <;>
  (try simp only [SDModel.repayValue, SDModel.defaultValue, SDModel.cons, bp_op12, mu_econ,
    mu_sup_bool, univ_unique, sum_singleton, id]) <;>
  first | (cases b <;> norm_num) | (cases m <;> norm_num) | norm_num

end AKMM.SovereignDefault
