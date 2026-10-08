/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.Algorithms
import ADPTransformations.FiniteMDP
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Group

/-!
# MDPs as ADPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.3 (pp. 82–84).

A finite MDP `(Γ, r, β, P)` is the ADP `(ℝ^X, 𝕋_MDP)` with the policy operators (2.16) and the
pointwise order.

* The ADP is well-posed, order continuous and order stable; **Exercise 2.3.6** (order
  bounded), **Exercises 2.3.7–2.3.8** (greedy policies (2.17) and the Bellman operator (2.18)),
  **Exercise 2.3.9** (regular).
* **Proposition 2.3.1**: the fundamental optimality properties hold, VFI, OPI and HPI converge,
  and HPI converges in finitely many steps (Theorems 2.2.6 and 2.2.8).
* **Exercise 2.3.10**: on `V̂ = [−M, M]`, which is chain complete, the ADP is strongly order
  stable, and Theorem 2.2.7 gives the same conclusions.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- In a subtype of `ℝ^X`, a monotone sequence converging pointwise to a member increases to it. -/
theorem isLUB_of_tendsto_subtype {X : Type*} {S : Set (X → ℝ)} {g : ℕ → S} (hg : Monotone g)
    {w : S} (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsLUB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Monotone.ge_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact le_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

/-- In a subtype of `ℝ^X`, an antitone sequence converging pointwise to a member decreases to
it. -/
theorem isGLB_of_tendsto_subtype {X : Type*} {S : Set (X → ℝ)} {g : ℕ → S} (hg : Antitone g)
    {w : S} (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsGLB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Antitone.le_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact ge_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- A feasible policy. -/
theorem nonempty_policy : Nonempty M.Policy :=
  ⟨⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩⟩

/-- The ADP `(ℝ^X, 𝕋_MDP)` of a finite MDP (§2.3.3.1), with policy operators (2.16). -/
def adp : ADP (X → ℝ) M.Policy where
  T σ := M.Tσ σ.1
  mono σ _ _ h x := M.Q_mono (σ.2 x) h
  nonempty := M.nonempty_policy

/-- §2.3.3.1 (p. 82): the MDP ADP is well-posed (Exercise 1.2.1). -/
theorem adp_wellPosed : M.adp.WellPosed := fun σ => by
  obtain ⟨u, -, hu, huniq, -⟩ := M.toDP.globallyStable σ
  exact ⟨u, hu, fun w hw => huniq w (mem_univ w) hw⟩

/-- §2.3.3.1 (p. 82): the MDP ADP is order stable (Exercise A.4.4). -/
theorem adp_isOrderStable : M.adp.IsOrderStable := fun σ =>
  orderStable_of_up_down (M.toDP.T_vσ σ) (fun v hv => M.toDP.le_vσ (mem_univ v) hv)
    fun v hv => M.toDP.vσ_le (mem_univ v) hv

/-- §2.3.3.1 (p. 82): the MDP ADP is order continuous. -/
theorem adp_isOrderContinuous : M.adp.IsOrderContinuous := by
  intro σ g w hg hw
  have hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (w x)) := fun x =>
    tendsto_atTop_isLUB (fun a b h => hg h x) (by
      have := (isLUB_pi.1 hw) x
      rwa [← range_comp] at this)
  refine isLUB_of_tendsto_atTop (fun a b h => M.adp.mono σ (hg h)) (tendsto_pi_nhds.2 fun x => ?_)
  change Tendsto (fun n => M.Q (g n) x (σ.1 x)) atTop (𝓝 (M.Q w x (σ.1 x)))
  exact tendsto_const_nhds.add ((tendsto_finsetSum _ fun y _ =>
    (hlim y).mul_const _).const_mul _)

/-- A bound on the rewards over the feasible pairs. -/
noncomputable def rbar : ℝ := ∑ x, ∑ a ∈ M.Γ x, |M.r x a|

theorem abs_r_le_rbar {x : X} {a : A} (ha : a ∈ M.Γ x) : |M.r x a| ≤ M.rbar :=
  (Finset.single_le_sum (f := fun a => |M.r x a|) (fun _ _ => abs_nonneg _) ha).trans
    (Finset.single_le_sum (f := fun x => ∑ a ∈ M.Γ x, |M.r x a|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ x))

/-- **Exercise 2.3.6** (p. 82): the MDP ADP is order bounded. -/
theorem adp_orderBounded : M.adp.OrderBounded := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  set K := M.rbar / (1 - M.β)
  have hK : M.rbar + M.β * K = K := by
    have : K * (1 - M.β) = M.rbar := div_mul_cancel₀ _ h1β.ne'
    linarith
  refine ⟨fun _ => K, fun σ x => ?_⟩
  change M.Q (fun _ => K) x (σ.1 x) ≤ K
  simp only [Q, ← Finset.mul_sum, M.P_sum x _ (σ.2 x), mul_one]
  linarith [(abs_le.1 (M.abs_r_le_rbar (σ.2 x))).2]

/-- **Exercise 2.3.7** (p. 82): a policy satisfying (2.17) is `v`-greedy in the ADP sense. -/
theorem exercise_2_3_7 (v : X → ℝ) (σ : M.Policy) (h : M.IsGreedy v σ) : M.adp.IsGreedy v σ :=
  (M.isGreedy_iff v σ).1 h

/-- **Exercise 2.3.9** (p. 83): the MDP ADP is regular. -/
theorem adp_regular : M.adp.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  exact ⟨σ, M.exercise_2_3_7 v σ hσ⟩

/-- **Exercise 2.3.8** (p. 83): the ADP Bellman operator is (2.18),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
theorem adp_bellman_apply (v : X → ℝ) (x : X) :
    M.adp.bellman v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) := by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  refine le_antisymm (Finset.le_sup' (M.Q v x) ((M.adp.greedy v).2 x)) ?_
  exact Finset.sup'_le _ _ fun a ha =>
    (hσ x a ha).trans (M.adp.T_le_bellman σ (M.adp_regular v) x)

/-- **Proposition 2.3.1** (p. 83): for the MDP ADP (i) the fundamental optimality properties
hold, (ii) VFI, OPI and HPI all converge, and (iii) HPI converges in finitely many steps, for
every greedy selector. -/
theorem proposition_2_3_1 :
    M.adp.FundamentalOptimality M.adp_isOrderStable.wellPosed ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isOrderStable.wellPosed g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.adp_isOrderStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h3⟩ := ADP.fundamentalOptimality_of_finite M.adp_isOrderStable M.adp_regular
    (Set.finite_range _)
  obtain ⟨-, h2⟩ := ADP.convergence_of_dedekind M.adp_isOrderStable M.adp_regular
    countablyDedekindComplete_of_conditionallyCompleteLattice M.adp_orderBounded
    M.adp_isOrderContinuous
  exact ⟨h1, h2, h3⟩

/-! ### Exercise 2.3.10: the ADP on `V̂ = [−M, M]` -/

/-- `V̂ = [−M, M]` with `M = r̄/(1 − β)`. -/
def Vhat : Set (X → ℝ) :=
  Icc (fun _ => -(M.rbar / (1 - M.β))) fun _ => M.rbar / (1 - M.β)

theorem mem_Vhat_iff {v : X → ℝ} : v ∈ M.Vhat ↔ ∀ x, |v x| ≤ M.rbar / (1 - M.β) := by
  simp only [Vhat, Set.mem_Icc, Pi.le_def, abs_le]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-- Exercise 1.2.2: each `T_σ` maps `V̂` into itself. -/
theorem Tσ_mapsTo_Vhat (σ : M.Policy) : MapsTo (M.Tσ σ.1) M.Vhat M.Vhat := fun v hv =>
  M.mem_Vhat_iff.2 ((M.abs_vσ_le fun _ _ ha => M.abs_r_le_rbar ha).1 σ v (M.mem_Vhat_iff.1 hv))

/-- The MDP ADP restricted to `V̂` (Exercise 2.3.10). -/
def adpHat : ADP ↥M.Vhat M.Policy where
  T σ v := ⟨M.Tσ σ.1 v.1, M.Tσ_mapsTo_Vhat σ v.2⟩
  mono σ _ _ h x := M.Q_mono (σ.2 x) h
  nonempty := M.nonempty_policy

theorem vσ_mem_Vhat (σ : M.Policy) : M.toDP.vσ σ ∈ M.Vhat :=
  M.mem_Vhat_iff.2 ((M.abs_vσ_le fun _ _ ha => M.abs_r_le_rbar ha).2 σ)

/-- **Exercise 2.3.10** (p. 84): on `V̂` the MDP ADP is strongly order stable. -/
theorem adpHat_isStronglyOrderStable : M.adpHat.IsStronglyOrderStable := by
  intro σ
  have hlim : ∀ v : ↥M.Vhat, ∀ x, Tendsto (fun n => ((M.adpHat.T σ)^[n] v : X → ℝ) x) atTop
      (𝓝 (M.toDP.vσ σ x)) := by
    intro v x
    have hiter : ∀ n, ((M.adpHat.T σ)^[n] v : X → ℝ) = (M.Tσ σ.1)^[n] v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl
    simp only [hiter]
    exact (M.toDP.tendsto_vσ σ (mem_univ _)).tendsto_at x
  have hfix : M.adpHat.T σ ⟨_, M.vσ_mem_Vhat σ⟩ = ⟨_, M.vσ_mem_Vhat σ⟩ :=
    Subtype.ext (M.toDP.T_vσ σ)
  refine ⟨⟨_, M.vσ_mem_Vhat σ⟩, hfix, fun w hw => Subtype.ext (M.toDP.eq_vσ (mem_univ _)
    (congrArg Subtype.val hw)), fun v hv => ?_, fun v hv => ?_⟩
  · have hinc : Monotone fun n => (M.adpHat.T σ)^[n] v := monotone_nat_of_le_succ fun n => by
      have := (M.adpHat.mono σ).iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hinc, isLUB_of_tendsto_subtype hinc (hlim v)⟩
  · have hdec : Antitone fun n => (M.adpHat.T σ)^[n] v := antitone_nat_of_succ_le fun n => by
      have := (M.adpHat.mono σ).iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hdec, isGLB_of_tendsto_subtype hdec (hlim v)⟩

/-- On `V̂` the MDP ADP is regular. -/
theorem adpHat_regular : M.adpHat.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v.1
  exact ⟨σ, fun τ x => hσ x _ (τ.2 x)⟩

/-- **Exercise 2.3.10** (p. 84), via **Theorem 2.2.7**: on the chain complete space `V̂` the MDP
ADP satisfies the fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem exercise_2_3_10 :
    M.adpHat.FundamentalOptimality M.adpHat_isStronglyOrderStable.isOrderStable.wellPosed ∧
      ∃ vstar, M.adpHat.IsValueFunction vstar ∧ M.adpHat.VFIConverges vstar ∧
        ∀ g, M.adpHat.IsSelector g → M.adpHat.OPIConverges g vstar ∧
          M.adpHat.HPIConverges M.adpHat_isStronglyOrderStable.isOrderStable.wellPosed g vstar := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  have hK : 0 ≤ M.rbar / (1 - M.β) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) h1β.le
  exact ADP.convergence_of_chainComplete M.adpHat_isStronglyOrderStable M.adpHat_regular
    (chainComplete_Icc fun _ => by linarith)

end FiniteMDP

end SargentStachurski.ADPTransformations
