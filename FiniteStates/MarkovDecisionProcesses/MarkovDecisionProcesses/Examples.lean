/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Bellman
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Examples of MDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.2 (pp. 130–134).

* The renewal problem (§5.1.2.1): action `1` resets the state to `x̄`, action `0`
  lets it move by `Q`. Exercise 5.1.1: the kernel (5.4) is stochastic; the
  renewal Bellman equation (5.3) is the MDP Bellman equation (5.2).
* Optimal inventory management (§5.1.2.2): state `{0, …, K}`, orders
  `Γ(x) = {0, …, K − x}`, IID geometric demand. The reward (5.8) and kernel
  (5.9) are infinite sums over demand; Exercise 5.1.2 gives the kernel in closed
  form and the Bellman operator takes the form (5.12). Exercise 5.1.3 (`T` is a
  `β`-contraction) is the general Exercise 5.1.12.
* Cake eating (§5.1.2.3): Exercise 5.1.4 frames (5.13) as an MDP with wealth as
  the state and next-period wealth as the action; the kernel is deterministic.
* Optimal stopping (§5.1.2.4): Exercise 5.1.5 frames job search with Markov
  wages as an MDP on `{0, 1} × W` with actions reject/accept. Its value function
  satisfies the job search Bellman equation of Vol. 1 (3.23): employed workers
  are worth `w/(1 − β)`, and `v*(0, w) = max{w/(1 − β), c + β ∑ v*(0, w')Q(w, w')}`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- The maximum over `Bool`. -/
theorem sup'_bool (f : Bool → ℝ) :
    (univ : Finset Bool).sup' univ_nonempty f = max (f true) (f false) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact max_le (Finset.le_sup' f (mem_univ true)) (Finset.le_sup' f (mem_univ false))

/-- A deterministic kernel: the next state is `g(x, a)`. -/
def detKernel {X A : Type*} [DecidableEq X] (g : X → A → X) (x : X) (a : A) (x' : X) : ℝ :=
  if x' = g x a then 1 else 0

theorem detKernel_nonneg {X A : Type*} [DecidableEq X] (g : X → A → X) (x : X) (a : A) (x' : X) :
    0 ≤ detKernel g x a x' := by
  unfold detKernel
  split_ifs <;> norm_num

theorem detKernel_rowsum {X A : Type*} [Fintype X] [DecidableEq X] (g : X → A → X) (x : X)
    (a : A) : ∑ x', detKernel g x a x' = 1 := by
  simp [detKernel]

/-- `∑ v(x')·1{x' = g(x, a)} = v(g(x, a))`. -/
theorem sum_mul_detKernel {X A : Type*} [Fintype X] [DecidableEq X] (g : X → A → X) (v : X → ℝ)
    (x : X) (a : A) : ∑ x', v x' * detKernel g x a x' = v (g x a) := by
  simp [detKernel]

/-! ### The renewal problem (§5.1.2.1) -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The renewal kernel (5.4): `P(x, a, x') = a·1{x' = x̄} + (1 − a)Q(x, x')`, with `a : Bool`. -/
def renewalKernel (Q : Matrix X X ℝ) (xbar : X) (x : X) (a : Bool) (x' : X) : ℝ :=
  if a then (if x' = xbar then 1 else 0) else Q x x'

/-- Exercise 5.1.1 (p. 131): the renewal kernel is a stochastic kernel from `G` to `X`. -/
theorem renewalKernel_nonneg {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar x : X) (a : Bool) (x' : X) :
    0 ≤ renewalKernel Q xbar x a x' := by
  unfold renewalKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact hQ.nonneg x x'

theorem renewalKernel_rowsum {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar x : X) (a : Bool) :
    ∑ x', renewalKernel Q xbar x a x' = 1 := by
  unfold renewalKernel
  cases a
  · simp [hQ.rowsum x]
  · simp

/-- The renewal problem as an MDP (p. 131): `A = {0, 1}` with `Γ(x) = A`, rewards `r(x, a)`. -/
noncomputable def renewal {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar : X) (r : X → Bool → ℝ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : MDP X Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := r
  P := renewalKernel Q xbar
  P_nonneg := fun x a x' => renewalKernel_nonneg hQ xbar x a x'
  P_rowsum := fun x a => renewalKernel_rowsum hQ xbar x a

/-- The renewal Bellman equation (5.3), p. 130, as the MDP Bellman equation (5.2):
`v*(x) = max{r(x, 1) + βv*(x̄), r(x, 0) + β ∑ v*(x')Q(x, x')}`. -/
theorem renewal_bellman {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (xbar : X) (r : X → Bool → ℝ)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : X) :
    (renewal hQ xbar r hβ0 hβ1).vstar x =
      max (r x true + β * (renewal hQ xbar r hβ0 hβ1).vstar xbar)
        (r x false + β * ∑ x', (renewal hQ xbar r hβ0 hβ1).vstar x' * Q x x') := by
  rw [MDP.bellman_equation]
  change (univ : Finset Bool).sup' univ_nonempty (fun a => r x a + β *
    ∑ x', (renewal hQ xbar r hβ0 hβ1).vstar x' * renewalKernel Q xbar x a x') = _
  rw [sup'_bool]
  simp [renewalKernel]

/-! ### Optimal inventory management (§5.1.2.2) -/

/-- The inventory update (5.6): `f(x, a, d) = (x − d) ∨ 0 + a`, clamped at the capacity `K` so that
the kernel is a distribution for every pair, feasible or not. -/
def inventoryNext (K x a d : ℕ) : ℕ := min ((x - d) + a) K

theorem inventoryNext_of_feasible {K x a d : ℕ} (h : a ≤ K - x) (hx : x ≤ K) :
    inventoryNext K x a d = (x - d) + a := by
  unfold inventoryNext
  omega

/-- The geometric demand distribution `φ(d) = p(1 − p)ᵈ`. -/
noncomputable def geomPmf (p : ℝ) (d : ℕ) : ℝ := p * (1 - p) ^ d

theorem geomPmf_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) : 0 < geomPmf p d :=
  mul_pos hp0 (pow_pos (by linarith) d)

theorem summable_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Summable (geomPmf p) :=
  (summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left p

theorem tsum_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∑' d, geomPmf p d = 1 := by
  unfold geomPmf
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by linarith) (by linarith)]
  have h1 : (1 : ℝ) - (1 - p) = p := by ring
  rw [h1, inv_eq_one_div, mul_one_div, div_self hp0.ne']

/-- The tail `∑_{d ≥ x} φ(d) = (1 − p)ˣ`. -/
theorem tsum_geomPmf_tail {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ) :
    ∑' d, (if x ≤ d then geomPmf p d else 0) = (1 - p) ^ x := by
  have hs : Summable fun d => if x ≤ d then geomPmf p d else 0 :=
    (summable_geomPmf hp0 hp1).of_nonneg_of_le
      (fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl])
      (fun d => by split_ifs <;> [exact le_rfl; exact (geomPmf_pos hp0 hp1 d).le])
  rw [← hs.sum_add_tsum_nat_add x]
  have h0 : ∑ d ∈ range x, (if x ≤ d then geomPmf p d else 0) = 0 :=
    sum_eq_zero fun d hd => by rw [mem_range] at hd; simp [not_le.2 hd]
  rw [h0, zero_add]
  have h1 : ∀ d, (if x ≤ d + x then geomPmf p (d + x) else 0) = (1 - p) ^ x * geomPmf p d := by
    intro d
    have hd : x ≤ d + x := by omega
    simp only [hd, ite_true]
    unfold geomPmf
    rw [pow_add]
    ring
  simp only [h1]
  rw [tsum_mul_left, tsum_geomPmf hp0 hp1, mul_one]

/-- The inventory kernel (5.9): `P(x, a, x') = P{f(x, a, D) = x'}` for `D ∼ φ`. -/
noncomputable def inventoryKernel (K : ℕ) (p : ℝ) (x a x' : Fin (K + 1)) : ℝ :=
  ∑' d : ℕ, if inventoryNext K x a d = x' then geomPmf p d else 0

theorem summable_inventoryTerm (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    Summable fun d : ℕ => if inventoryNext K x a d = x' then geomPmf p d else 0 :=
  (summable_geomPmf hp0 hp1).of_nonneg_of_le
    (fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl])
    (fun d => by split_ifs <;> [exact le_rfl; exact (geomPmf_pos hp0 hp1 d).le])

theorem inventoryKernel_nonneg (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    0 ≤ inventoryKernel K p x a x' :=
  tsum_nonneg fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl]

theorem inventoryKernel_rowsum (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a : Fin (K + 1)) :
    ∑ x', inventoryKernel K p x a x' = 1 := by
  unfold inventoryKernel
  rw [← Summable.tsum_finsetSum fun x' _ => summable_inventoryTerm K hp0 hp1 x a x',
    ← tsum_geomPmf hp0 hp1]
  refine tsum_congr fun d => ?_
  have hlt : inventoryNext K x a d < K + 1 := by unfold inventoryNext; omega
  rw [Finset.sum_eq_single (⟨inventoryNext K x a d, hlt⟩ : Fin (K + 1))]
  · simp
  · intro i _ hi
    have : ¬ (inventoryNext K x a d = (i : ℕ)) := fun h => hi (Fin.ext h.symm)
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

/-- The expected revenue `∑_d (x ∧ d)φ(d)` of (5.8). -/
noncomputable def expectedRevenue (p : ℝ) (x : ℕ) : ℝ := ∑' d : ℕ, min (x : ℝ) d * geomPmf p d

theorem summable_revenueTerm {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ℕ) :
    Summable fun d : ℕ => min (x : ℝ) d * geomPmf p d :=
  ((summable_geomPmf hp0 hp1).mul_left (x : ℝ)).of_nonneg_of_le
    (fun d => mul_nonneg (le_min (Nat.cast_nonneg x) (Nat.cast_nonneg d))
      (geomPmf_pos hp0 hp1 d).le)
    (fun d => mul_le_mul_of_nonneg_right (min_le_left _ _) (geomPmf_pos hp0 hp1 d).le)

/-- The inventory reward (5.8): `r(x, a) = ∑_d (x ∧ d)φ(d) − ca − κ·1{a > 0}`. -/
noncomputable def inventoryReward (p c κ : ℝ) (x a : ℕ) : ℝ :=
  expectedRevenue p x - c * a - κ * (if 0 < a then 1 else 0)

/-- The optimal inventory model as an MDP (pp. 131–132): states and actions `{0, …, K}`,
`Γ(x) = {0, …, K − x}`, `β = 1/(1 + r)`. -/
noncomputable def inventory (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) {r : ℝ}
    (hr : 0 < r) : MDP (Fin (K + 1)) (Fin (K + 1)) where
  Γ := fun x => univ.filter fun a => (a : ℕ) ≤ K - x
  Γ_nonempty := fun x => ⟨⟨0, by omega⟩, by simp⟩
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  r := fun x a => inventoryReward p c κ x a
  P := inventoryKernel K p
  P_nonneg := inventoryKernel_nonneg K hp0 hp1
  P_rowsum := inventoryKernel_rowsum K hp0 hp1

/-- The feasible orders (5.7): `a ∈ Γ(x) ⟺ a ≤ K − x`. -/
theorem inventory_mem_Γ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) {r : ℝ} (hr : 0 < r)
    (x a : Fin (K + 1)) : a ∈ (inventory K hp0 hp1 c κ hr).Γ x ↔ (a : ℕ) ≤ K - x := by
  simp [inventory]

/-- Exercise 5.1.2 (p. 132): for a feasible order `a ≤ K − x`, the kernel (5.9) is
`P(x, a, x') = (1 − p)ˣ` if `x' = a` (demand at least `x`), `p(1 − p)^{x + a − x'}` if
`a < x' ≤ x + a` (demand exactly `x + a − x'`), and `0` otherwise. -/
theorem inventoryKernel_eq (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {x a x' : Fin (K + 1)}
    (ha : (a : ℕ) ≤ K - x) :
    inventoryKernel K p x a x' =
      if (x' : ℕ) = a then (1 - p) ^ (x : ℕ)
      else if (a : ℕ) < x' ∧ (x' : ℕ) ≤ (x : ℕ) + a then geomPmf p ((x : ℕ) + a - x') else 0 := by
  have hx : (x : ℕ) ≤ K := Nat.le_of_lt_succ x.2
  have hnext : ∀ d, inventoryNext K x a d = (x - d) + a := fun d =>
    inventoryNext_of_feasible ha hx
  unfold inventoryKernel
  simp only [hnext]
  split_ifs with h1 h2
  · -- `x' = a`: exactly the demands `d ≥ x`
    rw [← tsum_geomPmf_tail hp0 hp1 x]
    refine tsum_congr fun d => ?_
    have : (x - d) + a = (x' : ℕ) ↔ x ≤ d := by omega
    simp only [this]
  · -- `a < x' ≤ x + a`: exactly the demand `d = x + a − x'`
    rw [tsum_eq_single ((x : ℕ) + a - x')]
    · have : ((x : ℕ) - ((x : ℕ) + a - x')) + a = (x' : ℕ) := by omega
      simp [this]
    · intro d hd
      have : ¬ (((x : ℕ) - d) + a = (x' : ℕ)) := by omega
      simp [this]
  · -- otherwise no demand leads to `x'`
    refine (tsum_congr fun d => ?_).trans tsum_zero
    have : ¬ ((x - d) + a = (x' : ℕ)) := by omega
    simp [this]

end SargentStachurski.MarkovDecisionProcesses
