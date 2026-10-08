/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Bellman

/-!
# Continuation values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.3.1 (the
definition (4.10)) and §4.1.4.1 (pp. 114, 117–118).

The continuation value function is `h* = c + βPv*`, (4.10); the Bellman
equation becomes `v* = e ∨ h*`, (4.11), and taking expectations gives
`h* = c + βP(e ∨ h*)`, (4.12). The continuation value operator
`Ch = c + βP(e ∨ h)`, (4.13), is a contraction of modulus `β` with unique
fixed point `h*` (Proposition 4.1.5), so `h*` can be computed by successive
approximation and the policy `σ*(x) = 1{e(x) ≥ h*(x)}` is `v*`-greedy, hence
optimal.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] [DecidableEq X] (S : StoppingProblem X)

/-- The continuation value function (4.10), p. 114: `h*(x) = c(x) + β ∑ v*(x')P(x, x')`. -/
noncomputable def hstar : X → ℝ := S.cont S.vstar

theorem hstar_apply (x : X) : S.hstar x = S.c x + S.β * ∑ x', S.vstar x' * S.P x x' :=
  S.cont_apply S.vstar x

/-- (4.11), p. 117: `v* = e ∨ h*`. -/
theorem vstar_eq_max_hstar (x : X) : S.vstar x = max (S.e x) (S.hstar x) :=
  (congrFun S.isFixedPt_T_vstar.eq x).symm

/-- The continuation value operator (4.13), p. 117:
`(Ch)(x) = c(x) + β ∑ max{e(x'), h(x')} P(x, x')`. -/
noncomputable def C (h : X → ℝ) : X → ℝ := S.cont fun x' => max (S.e x') (h x')

omit [DecidableEq X] in
theorem C_apply (h : X → ℝ) (x : X) :
    S.C h x = S.c x + S.β * ∑ x', max (S.e x') (h x') * S.P x x' :=
  S.cont_apply _ x

/-- (4.12), p. 117: `h*(x) = c(x) + β ∑ max{e(x'), h*(x')} P(x, x')`, i.e. `h*` is a fixed point
of `C`. -/
theorem isFixedPt_C_hstar : IsFixedPt S.C S.hstar := by
  change S.C S.hstar = S.hstar
  unfold C hstar
  congr 1
  funext x'
  exact (S.vstar_eq_max_hstar x').symm

omit [DecidableEq X] in
/-- `C` is order preserving. -/
theorem C_monotone : Monotone S.C := by
  intro h h' hhh' x
  unfold C cont
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (S.P_markov.mulVec_le_mulVec
    (fun x' => max_le_max le_rfl (hhh' x')) x) S.β_pos.le)

omit [DecidableEq X] in
/-- `|(Cf)(x) − (Cg)(x)| ≤ β‖f − g‖`, the estimate in the proof of Proposition 4.1.5. -/
theorem abs_C_sub_le (f g : X → ℝ) (x : X) : |S.C f x - S.C g x| ≤ S.β * ‖f - g‖ := by
  unfold C cont
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
  refine mul_le_mul_of_nonneg_left ((S.P_markov.abs_mulVec_sub_le _ _ x).trans ?_) S.β_pos.le
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x'
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [max_comm (S.e x') (f x'), max_comm (S.e x') (g x')]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := norm_le_pi_norm (f - g) x'
  simpa [Real.norm_eq_abs] using this

omit [DecidableEq X] in
/-- **Proposition 4.1.5** (p. 117): `C` is a contraction of modulus `β` on `ℝ^X`. -/
theorem isContractionOn_C : IsContractionOn S.C Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le f _ g _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_C_sub_le f g x

/-- Proposition 4.1.5: `h*` is the unique fixed point of `C` in `ℝ^X`. -/
theorem eq_hstar_of_isFixedPt {h : X → ℝ} (hh : IsFixedPt S.C h) : h = S.hstar :=
  S.isContractionOn_C.fixedPt_unique (Set.mem_univ h) (Set.mem_univ _) hh S.isFixedPt_C_hstar

/-- Successive approximation with `C` converges to `h*` from any `h` (p. 117, step (i)). -/
theorem tendsto_iterate_C (h : X → ℝ) : Tendsto (fun k : ℕ => S.C^[k] h) atTop (𝓝 S.hstar) :=
  S.isContractionOn_C.tendsto_iterate_fixedPt (Set.mem_univ h) (Set.mem_univ _) S.isFixedPt_C_hstar

/-- The policy `σ*(x) = 1{e(x) ≥ h*(x)}` of p. 117, step (ii). -/
noncomputable def sigmaStar : Policy X := fun x => decide (S.hstar x ≤ S.e x)

theorem sigmaStar_eq_greedy : S.sigmaStar = S.greedy S.vstar := rfl

/-- `σ*` is `v*`-greedy, hence optimal (Proposition 4.1.3). -/
theorem isGreedy_sigmaStar : S.IsGreedy S.vstar S.sigmaStar := S.isGreedy_greedy S.vstar

theorem isOptimal_sigmaStar : S.IsOptimal S.sigmaStar := S.isOptimal_greedy_vstar

/-- `σ*` stops exactly where the exit reward is at least the continuation value. -/
theorem sigmaStar_eq_true_iff (x : X) : S.sigmaStar x = true ↔ S.hstar x ≤ S.e x := by
  simp [sigmaStar]

end StoppingProblem

end SargentStachurski.OptimalStopping
