/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.ExogenousDiscounting
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Inventory management with time-varying interest rates

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.2 (pp. 197–199).

The inventory model of §5.2.1 (restated from the `FiniteStates/MarkovDecisionProcesses`
project: states and orders in `{0, …, K}`, geometric demand `φ(d) = p(1 − p)ᵈ`,
update `f(y, a, d) = (y − d) ∨ 0 + a`, reward (5.8)) with the constant discount
factor replaced by `β(Zₜ)` for an exogenous `Q`-Markov process. It is an instance of
the exogenous discount model with `R(y, a, y') = P{f(y, a, D) = y'}`, (6.25)–(6.26),
so by Proposition 6.2.3 all the optimality results hold when `ρ(L_Z) < 1` for
`L_Z(z, z') = β(z)Q(z, z')`, the test performed by Listing 6.1.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

/-- The inventory update (5.6): `f(x, a, d) = (x − d) ∨ 0 + a`, clamped at the capacity `K` so that
the kernel is a distribution for every pair, feasible or not. -/
def inventoryNext (K x a d : ℕ) : ℕ := min ((x - d) + a) K

theorem inventoryNext_lt (K x a d : ℕ) : inventoryNext K x a d < K + 1 := by
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

/-- The inventory kernel (5.9), `R(y, a, y') = P{f(y, a, D) = y'}` for `D ∼ φ`. -/
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

/-- `∑_{y'} v(y')R(y, a, y') = ∑_d φ(d) v(f(y, a, d))`: the kernel form (6.26) of the expectation
equals the shock form (6.25). -/
theorem sum_mul_inventoryKernel (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (v : Fin (K + 1) → ℝ) (x a : Fin (K + 1)) :
    ∑ x', v x' * inventoryKernel K p x a x' =
      ∑' d : ℕ, geomPmf p d * v ⟨inventoryNext K x a d, inventoryNext_lt K x a d⟩ := by
  unfold inventoryKernel
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun x' _ => (summable_inventoryTerm K hp0 hp1 x a x').mul_left _]
  refine tsum_congr fun d => ?_
  rw [Finset.sum_eq_single (⟨inventoryNext K x a d, inventoryNext_lt K x a d⟩ : Fin (K + 1))]
  · simp [mul_comm]
  · intro i _ hi
    have : ¬ (inventoryNext K x a d = (i : ℕ)) := fun h => hi (Fin.ext h.symm)
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

theorem inventoryKernel_rowsum (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a : Fin (K + 1)) :
    ∑ x', inventoryKernel K p x a x' = 1 := by
  have := sum_mul_inventoryKernel K hp0 hp1 (fun _ => 1) x a
  simp only [one_mul, mul_one] at this
  rw [this, tsum_geomPmf hp0 hp1]

/-- The expected revenue `∑_d (x ∧ d)φ(d)` of (5.8). -/
noncomputable def expectedRevenue (p : ℝ) (x : ℕ) : ℝ := ∑' d : ℕ, min (x : ℝ) d * geomPmf p d

/-- The inventory reward (5.8): `r(x, a) = ∑_d (x ∧ d)φ(d) − ca − κ·1{a > 0}`. -/
noncomputable def inventoryReward (p c κ : ℝ) (x a : ℕ) : ℝ :=
  expectedRevenue p x - c * a - κ * (if 0 < a then 1 else 0)

variable {Z : Type*} [Fintype Z]

/-- The inventory model with time-varying interest rates (§6.2.2), as an exogenous discount
model: inventory `y ∈ {0, …, K}`, orders `Γ(y, z) = {0, …, K − y}`, discount factor `β(z)` driven
by a `Q`-Markov exogenous state. -/
noncomputable def inventorySDD (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) :
    Exogenous (Fin (K + 1)) Z (Fin (K + 1)) where
  Γ := fun x => univ.filter fun a => (a : ℕ) ≤ K - x.1
  Γ_nonempty := fun _ => ⟨⟨0, by omega⟩, by simp⟩
  β := β
  β_nonneg := hβ
  r := fun y a => inventoryReward p c κ y a
  Q := Q
  Q_markov := hQ
  R := inventoryKernel K p
  R_nonneg := inventoryKernel_nonneg K hp0 hp1
  R_rowsum := inventoryKernel_rowsum K hp0 hp1

/-- The feasible orders: `a ∈ Γ(y, z) ⟺ a ≤ K − y`. -/
theorem inventorySDD_mem_Γ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (y a : Fin (K + 1)) (z : Z) :
    a ∈ (inventorySDD K hp0 hp1 c κ β hβ hQ).Γ (y, z) ↔ (a : ℕ) ≤ K - y := by
  simp [inventorySDD]

/-- (6.26): the action value is
`B((y, z), a, v) = r(y, a) + β(z) ∑_{y', z'} v(y', z')Q(z, z')R(y, a, y')`. -/
theorem inventorySDD_B_apply (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (v : Fin (K + 1) × Z → ℝ)
    (y a : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.B v (y, z) a =
      inventoryReward p c κ y a + β z * ∑ x', v x' * Q z x'.2 * inventoryKernel K p y a x'.1 := by
  change inventoryReward p c κ y a +
    ∑ x', v x' * β z * (Q z x'.2 * inventoryKernel K p y a x'.1) = _
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- (6.25): the action value in terms of the demand shock,
`B((y, z), a, v) = r(y, a) + β(z) ∑_{d, z'} v(f(y, a, d), z')φ(d)Q(z, z')`. -/
theorem inventorySDD_B_apply' (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (v : Fin (K + 1) × Z → ℝ)
    (y a : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.B v (y, z) a =
      inventoryReward p c κ y a + β z * ∑ z',
        (∑' d : ℕ, geomPmf p d * v (⟨inventoryNext K y a d, inventoryNext_lt K y a d⟩, z')) *
          Q z z' := by
  rw [inventorySDD_B_apply, Fintype.sum_prod_type, sum_comm]
  congr 2
  refine sum_congr rfl fun z' _ => ?_
  rw [← sum_mul_inventoryKernel K hp0 hp1 (fun y' => v (y', z')) y a, sum_mul]
  exact sum_congr rfl fun y' _ => by ring

/-- The exogenous discount operator of the inventory model: `L(z, z') = β(z)Q(z, z')`, whose
spectral radius Listing 6.1 tests. -/
theorem inventorySDD_LZ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).LZ = discountOp (fun z _ => β z) Q := rfl

variable [DecidableEq Z] [Nonempty Z]

/-- §6.2.2, p. 198: if `ρ(L) < 1` for `L(z, z') = β(z)Q(z, z')`, all the standard optimality
results hold for the inventory model: `v*` is the unique solution of the Bellman equation (6.24)
with (6.25), a policy is optimal iff it is `v*`-greedy, and an optimal policy exists. -/
theorem inventorySDD_optimality (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ)
    (β : Z → ℝ) (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q)
    (hρ : specRad (discountOp (fun z _ => β z) Q) < 1) :
    let M := (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP
    IsFixedPt M.T M.vstar ∧ (∀ v, IsFixedPt M.T v → v = M.vstar) ∧
      (∀ σ, M.IsOptimal σ ↔ M.IsGreedy M.vstar σ) ∧ ∃ σ, M.IsOptimal σ := by
  intro M
  have hM := (inventorySDD K hp0 hp1 c κ β hβ hQ).spectralCondition hρ
  exact ⟨M.isFixedPt_T_vstar hM, fun v hv => M.eq_vstar_of_isFixedPt hM hv,
    fun σ => M.isOptimal_iff_isGreedy hM σ, M.exists_isOptimal hM⟩

/-- The Bellman equation of the inventory model with time-varying discounting, (6.24) with (6.25):
`v*(y, z) = max_{a ≤ K − y} {r(y, a) + β(z) ∑_{d, z'} v*(f(y, a, d), z')φ(d)Q(z, z')}`. -/
theorem inventorySDD_bellman (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q)
    (hρ : specRad (discountOp (fun z _ => β z) Q) < 1) (y : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.vstar (y, z) =
      (univ.filter fun a : Fin (K + 1) => (a : ℕ) ≤ K - y).sup'
        ((inventorySDD K hp0 hp1 c κ β hβ hQ).Γ_nonempty (y, z)) fun a =>
          inventoryReward p c κ y a + β z * ∑ z', (∑' d : ℕ, geomPmf p d *
            (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.vstar
              (⟨inventoryNext K y a d, inventoryNext_lt K y a d⟩, z')) * Q z z' := by
  rw [(inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.bellman_equation
    ((inventorySDD K hp0 hp1 c κ β hβ hQ).spectralCondition hρ)]
  exact Finset.sup'_congr _ rfl fun a _ => inventorySDD_B_apply' K hp0 hp1 c κ β hβ hQ _ y a z

end SargentStachurski.StochasticDiscounting
