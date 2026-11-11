/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.LCAutarky

/-!
# The sequence problem with one-sided limited commitment (Miao §22.1, pp. 774–776)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1, pp. 774–776. The contract is a
consumption plan on the event tree of endowment histories. A node is a pair `(y_t, past)`: the
current state and the list of earlier states (most recent first); `lc_ext h j` is the successor
node in which the next state is `θⱼ`. `lc_treeExp pl t F h` is the conditional expectation at `h`
of `F` evaluated `t` periods later, and `lc_treeValue` is the discounted value
`E_t Σ_{s ≥ t} β^{s-t} F`.

We prove: the value of the autarky plan at every node is `U_d(y_t)` (so autarky satisfies the
incentive constraints (22.1) with equality); with `v₀ ≥ U_d(y₀)` the participation constraint
(22.2) implies (22.1) at the initial node; and the recursive decomposition behind the Bellman
equation of §22.1.1: for any bounded feasible plan, the date-0 consumption and the continuation
values `wⱼ` satisfy (22.3) and (22.4), the principal's value satisfies the one-step recursion, and
the continuation plan at `θⱼ` is feasible for the promise `wⱼ`.

Departure: the incentive constraint (22.1) is imposed at every node of the tree (not only at
nodes reachable from `y₀`); constraints at other nodes do not affect values at `y₀`.
-/

namespace Miao.RecursiveContracts

open Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The successor node: next period's state is `θⱼ`. -/
def lc_ext (h : ι × List ι) (j : ι) : ι × List ι := (j, h.1 :: h.2)

/-- `E_t[F(h_{t+s})]` on the event tree (Miao, p. 775). -/
def lc_treeExp (pl : ι → ι → ℝ) : ℕ → (ι × List ι → ℝ) → ι × List ι → ℝ
  | 0, F, h => F h
  | t + 1, F, h => ∑ j, pl h.1 j * lc_treeExp pl t F (lc_ext h j)

/-- The discounted value `E_t Σ_{s ≥ 0} β^s F(h_{t+s})` at node `h` (Miao, p. 775). -/
noncomputable def lc_treeValue (β : ℝ) (pl : ι → ι → ℝ) (F : ι × List ι → ℝ)
    (h : ι × List ι) : ℝ :=
  ∑' t : ℕ, β ^ t * lc_treeExp pl t F h

/-- Tree expectations keep bounds. -/
theorem lc_treeExp_abs_le {pl : ι → ι → ℝ} (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ}
    {M : ℝ} (hF : ∀ h, |F h| ≤ M) (t : ℕ) (h : ι × List ι) : |lc_treeExp pl t F h| ≤ M := by
  induction t generalizing h with
  | zero => exact hF h
  | succ t ih =>
    simp only [lc_treeExp]
    exact lc_condExp_abs_le hpl (f := fun j => lc_treeExp pl t F (lc_ext h j)) (fun j => ih _) h.1

/-- The discounted value of a bounded plan converges. -/
theorem lc_treeValue_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ} {M : ℝ} (hF : ∀ h, |F h| ≤ M)
    (h : ι × List ι) : Summable fun t : ℕ => β ^ t * lc_treeExp pl t F h := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (lc_treeExp_abs_le hpl hF t h) (pow_nonneg hβ0 t)

/-- Miao, p. 775: the one-step recursion
`V(h) = F(h) + β Σⱼ π(θⱼ | y_t) V(h, θⱼ)` for the value of a bounded plan. -/
theorem lc_treeValue_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) {F : ι × List ι → ℝ} {M : ℝ} (hF : ∀ h, |F h| ≤ M)
    (h : ι × List ι) :
    lc_treeValue β pl F h = F h + β * ∑ j, pl h.1 j * lc_treeValue β pl F (lc_ext h j) := by
  unfold lc_treeValue
  rw [(lc_treeValue_summable hβ0 hβ1 hpl hF h).tsum_eq_zero_add]
  congr 1
  · simp [lc_treeExp]
  · have hs := fun j => lc_treeValue_summable hβ0 hβ1 hpl hF (lc_ext h j)
    have h1 : ∀ t : ℕ, β ^ (t + 1) * lc_treeExp pl (t + 1) F h =
        β * ∑ j, pl h.1 j * (β ^ t * lc_treeExp pl t F (lc_ext h j)) := by
      intro t
      rw [lc_treeExp, Finset.mul_sum, Finset.mul_sum, pow_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [h1]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hs j).mul_left (pl h.1 j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact tsum_mul_left

/-- Expectations of a function of the current state reduce to the chain's iterates. -/
theorem lc_treeExp_state (pl : ι → ι → ℝ) (r : ι → ℝ) (t : ℕ) (h : ι × List ι) :
    lc_treeExp pl t (fun k => r k.1) h = (lc_condExp pl)^[t] r h.1 := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    rw [lc_treeExp, Function.iterate_succ_apply', lc_condExp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih]
    rfl

/-- Miao, (22.1), p. 775: the incentive constraint at every node,
`E_t Σ_j β^j u(c_{t+j}) ≥ U_d(y_t)`. -/
def lc_IC (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ) : Prop :=
  ∀ h, lc_autarky β pl (fun i => u (θ i)) h.1 ≤ lc_treeValue β pl (fun k => u (c k)) h

/-- Miao, (22.2), p. 775: the participation constraint `E Σ_t β^t u(c_t) ≥ v₀` at node `h`. -/
def lc_PK (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (c : ι × List ι → ℝ) (h : ι × List ι)
    (v₀ : ℝ) : Prop :=
  v₀ ≤ lc_treeValue β pl (fun k => u (c k)) h

/-- A plan with bounded consumption and bounded utility. -/
def lc_BddPlan (u : ℝ → ℝ) (c : ι × List ι → ℝ) : Prop :=
  ∃ M, ∀ h, |c h| ≤ M ∧ |u (c h)| ≤ M

/-- The principal's value `E_t Σ_s β^s (y_{t+s} − c_{t+s})` (Miao, p. 775). -/
noncomputable def lc_principalValue (β : ℝ) (pl : ι → ι → ℝ) (θ : ι → ℝ)
    (c : ι × List ι → ℝ) (h : ι × List ι) : ℝ :=
  lc_treeValue β pl (fun k => θ k.1 - c k) h

/-- Miao, (22.1), p. 775: the value of the autarky plan `c_t = y_t` at every node is the autarky
value `U_d(y_t)`; in particular autarky satisfies every incentive constraint (22.1), with
equality. -/
theorem eq_22_1 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (h : ι × List ι) :
    lc_treeValue β pl (fun k => u (θ k.1)) h = lc_autarky β pl (fun i => u (θ i)) h.1 ∧
      lc_IC β pl u θ (fun k => θ k.1) := by
  have key : ∀ h : ι × List ι, lc_treeValue β pl (fun k => u (θ k.1)) h =
      lc_autarky β pl (fun i => u (θ i)) h.1 := by
    intro h
    unfold lc_treeValue lc_autarky
    congr 1
    funext t
    rw [← lc_treeExp_state pl (fun i => u (θ i)) t h]
  exact ⟨key h, fun h => (key h).ge⟩

/-- Miao, (22.2), p. 775: since `v₀ ≥ U_d(y₀)`, the participation constraint (22.2) implies the
incentive constraint (22.1) at the initial node. -/
theorem eq_22_2 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (h : ι × List ι) (v₀ : ℝ) (hv₀ : lc_autarky β pl (fun i => u (θ i)) h.1 ≤ v₀)
    (hPK : lc_PK β pl u c h v₀) :
    lc_autarky β pl (fun i => u (θ i)) h.1 ≤ lc_treeValue β pl (fun k => u (c k)) h :=
  hv₀.trans hPK

/-- Miao, (22.3), p. 776, derived from the sequence problem: for a plan satisfying (22.1), the
continuation values `wⱼ = E_{t+1} Σ β^s u(c)` after `θⱼ` satisfy `wⱼ ≥ U_d(θⱼ)`. -/
theorem eq_22_3 (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (hIC : lc_IC β pl u θ c) (h : ι × List ι) (j : ι) :
    lc_autarky β pl (fun i => u (θ i)) j ≤ lc_treeValue β pl (fun k => u (c k)) (lc_ext h j) :=
  hIC (lc_ext h j)

/-- Miao, (22.4), p. 776, derived from the sequence problem: for a bounded plan satisfying
(22.2) at `h`, `u(c) + β Σⱼ π(θⱼ | y) wⱼ ≥ v₀` with `wⱼ` the continuation values. -/
theorem eq_22_4 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (u : ℝ → ℝ) (c : ι × List ι → ℝ) (hc : lc_BddPlan u c)
    (h : ι × List ι) (v₀ : ℝ) (hPK : lc_PK β pl u c h v₀) :
    v₀ ≤ u (c h) + β * ∑ j, pl h.1 j * lc_treeValue β pl (fun k => u (c k)) (lc_ext h j) := by
  obtain ⟨M, hM⟩ := hc
  have := lc_treeValue_recursion hβ0 hβ1 hpl (F := fun k => u (c k)) (fun k => (hM k).2) h
  unfold lc_PK at hPK
  rw [this] at hPK
  exact hPK

/-- Miao, p. 776: the principal's value of a bounded plan satisfies the one-step recursion
`Π(h) = y − c + β Σⱼ π(θⱼ | y) Π(h, θⱼ)`, the objective of the Bellman equation. -/
theorem lc_principal_recursion {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {pl : ι → ι → ℝ}
    (hpl : lc_IsStochastic pl) (u : ℝ → ℝ) (θ : ι → ℝ) (c : ι × List ι → ℝ)
    (hc : lc_BddPlan u c) (h : ι × List ι) :
    lc_principalValue β pl θ c h =
      θ h.1 - c h + β * ∑ j, pl h.1 j * lc_principalValue β pl θ c (lc_ext h j) := by
  obtain ⟨M, hM⟩ := hc
  obtain ⟨K, hK⟩ := lc_exists_bound θ
  exact lc_treeValue_recursion hβ0 hβ1 hpl (F := fun k => θ k.1 - c k) (M := K + M)
    (fun k => (abs_sub _ _).trans (add_le_add (hK k.1) (hM k).1)) h

/-- Miao, p. 776: the continuation of a feasible plan after `θⱼ` is feasible for the promise
`wⱼ`: it satisfies (22.1) and the promise-keeping constraint (22.2) with `v₀ = wⱼ` (with
equality), so the problem can be written recursively with the promised value as the state. -/
theorem lc_continuation_feasible (β : ℝ) (pl : ι → ι → ℝ) (u : ℝ → ℝ) (θ : ι → ℝ)
    (c : ι × List ι → ℝ) (hIC : lc_IC β pl u θ c) (h : ι × List ι) (j : ι) :
    lc_IC β pl u θ c ∧
      lc_PK β pl u c (lc_ext h j) (lc_treeValue β pl (fun k => u (c k)) (lc_ext h j)) :=
  ⟨hIC, le_rfl⟩

end Miao.RecursiveContracts
