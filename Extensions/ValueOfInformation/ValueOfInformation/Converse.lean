/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ValueOfInformation.Blackwell
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Blackwell's theorem: the converse

Blackwell (1951, 1953). If an experiment `P` is at least as valuable as `Q` in **every** decision
problem, then `Q` is a garbling of `P`.

* `blackwell_converse`: if `V_u(Q) ≤ V_u(P)` for every payoff `u` on the action set `Y'`, there is
  a Markov matrix `M` with `π(θ)Q(θ, y') = π(θ)(PM)(θ, y')`. The proof separates the unnormalized
  posteriors of `Q` from the compact convex set of those of garblings of `P`; the separating
  functional is a payoff `u`, and the best garbling for it is the decision rule optimal under `P`.
* `blackwell`: with a full-support prior, `P` is more valuable than `Q` in every decision problem
  iff `Q = PM` for a Markov matrix `M`.
-/

open Finset

namespace DPExtensions.ValueOfInformation

variable {Θ Y Y' : Type*} [Fintype Θ] [Fintype Y] [Fintype Y']

/-- The unnormalized posteriors of the garbling `PM`, as a linear function of `M`. -/
def garbleMap (π : Θ → ℝ) (P : Θ → Y → ℝ) : (Y × Y' → ℝ) →ₗ[ℝ] (Y' × Θ → ℝ) where
  toFun M p := ∑ y, M (y, p.1) * (π p.2 * P p.2 y)
  map_add' M N := by
    funext p
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' c M := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

/-- Markov matrices `Y → Y'`, as functions on `Y × Y'`. -/
def stochSet : Set (Y × Y' → ℝ) := {M | (∀ p, 0 ≤ M p) ∧ ∀ y, ∑ y', M (y, y') = 1}

omit [Fintype Y] in
theorem convex_stochSet : Convex ℝ (stochSet : Set (Y × Y' → ℝ)) := by
  intro M hM N hN a b ha hb hab
  refine ⟨fun p => ?_, fun y => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hM.1 p)) (mul_nonneg hb (hN.1 p))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hM.2 y,
      hN.2 y, mul_one, hab]

omit [Fintype Y] in
theorem isCompact_stochSet [Finite Y] : IsCompact (stochSet : Set (Y × Y' → ℝ)) := by
  have := Fintype.ofFinite Y
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have e : (stochSet : Set (Y × Y' → ℝ)) =
        (⋂ p, {M : Y × Y' → ℝ | 0 ≤ M p}) ∩ ⋂ y, {M : Y × Y' → ℝ | ∑ y', M (y, y') = 1} := by
      ext M
      simp [stochSet]
    rw [e]
    exact (isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)).inter
      (isClosed_iInter fun y => isClosed_eq
        (continuous_finsetSum _ fun y' _ => continuous_apply (y, y')) continuous_const)
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun M hM => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hM.1 p), ← hM.2 p.1]
    exact single_le_sum (f := fun y' => M (p.1, y')) (fun y' _ => hM.1 _) (mem_univ p.2)

/-- **Blackwell's theorem (converse)**: if `P` is at least as valuable as `Q` in every decision
problem with action set `Y'`, then the unnormalized posteriors of `Q` are those of a garbling of
`P`. -/
theorem blackwell_converse [Nonempty Y'] (π : Θ → ℝ) (P : Θ → Y → ℝ)
    (Q : Θ → Y' → ℝ) (h : ∀ u : Y' → Θ → ℝ, value π u Q ≤ value π u P) :
    ∃ M : Y → Y' → ℝ, IsStochastic M ∧ ∀ y' θ, π θ * Q θ y' = π θ * garble P M θ y' := by
  classical
  set L := garbleMap (Y' := Y') π P
  set μQ : Y' × Θ → ℝ := fun p => π p.2 * Q p.2 p.1
  by_cases hmem : μQ ∈ L '' stochSet
  · obtain ⟨M, hM, hLM⟩ := hmem
    refine ⟨fun y y' => M (y, y'), ⟨fun y y' => hM.1 _, hM.2⟩, fun y' θ => ?_⟩
    have := congrFun hLM (y', θ)
    simp only [L, garbleMap, LinearMap.coe_mk, AddHom.coe_mk, μQ] at this
    rw [← this, garble, mul_sum]
    exact sum_congr rfl fun y _ => by ring
  exfalso
  have hconv : Convex ℝ (L '' stochSet) := convex_stochSet.linear_image L
  have hclosed : IsClosed (L '' stochSet) :=
    (isCompact_stochSet.image L.continuous_of_finiteDimensional).isClosed
  obtain ⟨f, c, hfC, hfQ⟩ := geometric_hahn_banach_closed_point hconv hclosed hmem
  -- the separating functional as a payoff
  set w : Y' → Θ → ℝ := fun a θ => f fun p => if (a, θ) = p then 1 else 0
  have hf : ∀ e : Y' × Θ → ℝ, f e = ∑ p, e p * w p.1 p.2 := fun e => by
    have h1 := (f : (Y' × Θ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ e
    simp only [ContinuousLinearMap.coe_coe] at h1
    rw [h1]
    exact sum_congr rfl fun p _ => by simp [w, smul_eq_mul]
  -- `f(μ_Q) ≤ V_w(Q)`
  have hQ : f μQ ≤ value π w Q := by
    rw [hf, Fintype.sum_prod_type, value]
    refine sum_le_sum fun y' _ => le_trans (le_of_eq ?_) (le_sup' (payoff π w Q y') (mem_univ y'))
    simp only [μQ, payoff]
  -- the decision rule optimal under `P` attains `V_w(P)` as a garbling
  have hbest : ∀ y, ∃ a, univ.sup' univ_nonempty (payoff π w P y) = payoff π w P y a := by
    intro y
    obtain ⟨a, -, ha⟩ := exists_max_image univ (payoff π w P y) univ_nonempty
    exact ⟨a, le_antisymm (sup'_le _ _ fun b _ => ha b (mem_univ b))
      (le_sup' (payoff π w P y) (mem_univ a))⟩
  choose act hact using hbest
  set Mstar : Y × Y' → ℝ := fun p => if p.2 = act p.1 then 1 else 0
  have hMstar : Mstar ∈ stochSet := ⟨fun p => by simp only [Mstar]; split_ifs <;> norm_num,
    fun y => by simp [Mstar]⟩
  have hP : f (L Mstar) = value π w P := by
    rw [hf, Fintype.sum_prod_type, value]
    have e1 : ∀ y' θ, L Mstar (y', θ) * w y' θ =
        ∑ y, if y' = act y then π θ * P θ y * w y' θ else 0 := by
      intro y' θ
      simp only [L, garbleMap, LinearMap.coe_mk, AddHom.coe_mk, Mstar, sum_mul]
      refine sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    simp only [e1]
    calc ∑ y', ∑ θ, ∑ y, (if y' = act y then π θ * P θ y * w y' θ else 0)
        = ∑ y', ∑ y, ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) :=
          sum_congr rfl fun y' _ => sum_comm
      _ = ∑ y, ∑ y', ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) := sum_comm
      _ = ∑ y, payoff π w P y (act y) := sum_congr rfl fun y _ => by
          have e2 : ∀ y', ∑ θ, (if y' = act y then π θ * P θ y * w y' θ else 0) =
              if y' = act y then ∑ θ, π θ * P θ y * w y' θ else 0 := fun y' => by
            split_ifs <;> simp
          simp only [e2, sum_ite_eq', mem_univ, ↓reduceIte, payoff]
      _ = ∑ y, univ.sup' univ_nonempty (payoff π w P y) := sum_congr rfl fun y _ => (hact y).symm
  have h1 := hfC (L Mstar) ⟨Mstar, hMstar, rfl⟩
  have h2 := h w
  linarith

/-- **Blackwell's theorem**: with a full-support prior, `P` is at least as valuable as `Q` in
every decision problem with action set `Y'` iff `Q` is a garbling of `P`. -/
theorem blackwell [Nonempty Y'] {π : Θ → ℝ} (hπ : ∀ θ, 0 < π θ)
    (P : Θ → Y → ℝ) (Q : Θ → Y' → ℝ) :
    (∀ u : Y' → Θ → ℝ, value π u Q ≤ value π u P) ↔
      ∃ M : Y → Y' → ℝ, IsStochastic M ∧ Q = garble P M := by
  constructor
  · intro h
    obtain ⟨M, hM, hQ⟩ := blackwell_converse π P Q h
    exact ⟨M, hM, funext fun θ => funext fun y' =>
      mul_left_cancel₀ (hπ θ).ne' (hQ y' θ)⟩
  · rintro ⟨M, hM, rfl⟩ u
    exact value_garble_le π u P hM

end DPExtensions.ValueOfInformation
