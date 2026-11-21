/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.OCExistence

/-!
# Theorem 6.4.2: monotonicity

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCMonotone`), namespace renamed.

Miao, §6.4, pp. 175–176. Under Assumptions 6.4.1–6.4.9, `V_t(·, z)` is strictly increasing on
`X` for every `z` and `t = 0, 1, …, T` (`theorem_6_4_2`), by backward induction: with `a*`
attaining `V_t(x, z)` and `x < x′`,
`V_t(x, z) = u_t(x, z, a*) + β E V_{t+1} < u_t(x′, z, a*) + β E V_{t+1} ≤ V_t(x′, z)`, using
Assumptions 6.4.7 and 6.4.9 for the strict inequality and `a* ∈ Γ(x′, z)` (Assumption 6.4.8)
for the second.

The order on `E` is any partial order (componentwise on `ℝ^{n_x}`); "strictly increasing" is
`StrictMonoOn`. The proof needs `β ≥ 0` rather than all of Assumption 5.1.2, and does not use
Assumptions 6.4.1–6.4.2. The standing hypotheses (`Standing`) carry Assumptions 6.4.3–6.4.6.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory

namespace OCModel

variable {E F Z : Type*} [MeasurableSpace Z] [MetricSpace E] [MetricSpace F] [MetricSpace Z]
  {M : OCModel E F Z} {P : (E → Z → ℝ) → Prop}

/-- **Theorem 6.4.2 (Monotonicity)** (Miao, p. 175). Under the standing hypotheses
(Assumptions 6.4.3–6.4.6), Assumptions 6.4.7–6.4.9 and `β ≥ 0`, `V_t(·, z)` is strictly
increasing on `X` for each `z ∈ Z` and `t = 0, 1, …, T`. -/
theorem theorem_6_4_2 [PartialOrder E] (h : M.Standing P) (h647 : M.Assumption647)
    (h648 : M.Assumption648) (h649 : M.Assumption649) (hβ : 0 ≤ M.β) :
    ∀ t ≤ M.T, ∀ z, StrictMonoOn (fun x => M.V t x z) M.X := by
  have key : ∀ k ≤ M.T, ∀ z, StrictMonoOn (fun x => M.V (M.T - k) x z) M.X := by
    intro k
    induction k with
    | zero => intro _ z; rw [Nat.sub_zero, M.V_T_eq]; exact h647.1 z
    | succ k ih =>
      intro hk z x hx x' hx' hxx'
      have ht : M.T - (k + 1) < M.T := by omega
      have he : M.T - (k + 1) + 1 = M.T - k := by omega
      set t := M.T - (k + 1)
      obtain ⟨a, haΓ, hval⟩ := h.G_nonempty ht hx z
      have haA := h.a644.1 x hx z haΓ
      have ha' : a ∈ M.Γ x' z := h648 z x hx x' hx' hxx'.le haΓ
      -- the continuation value is nondecreasing in `x`
      have hcont : M.cont (M.V (t + 1)) x a z ≤ M.cont (M.V (t + 1)) x' a z := by
        refine integral_mono (h.integrable ht hx haA z) (h.integrable ht hx' haA z) fun z' => ?_
        have hmono := (ih (by omega) z').monotoneOn
        rw [he]
        exact hmono (h.a645.1 x hx a haA z z') (h.a645.1 x' hx' a haA z z')
          (h649 a haA z z' hx hx' hxx'.le)
      have hu := h647.2 t ht z a haA hx hx' hxx'
      change M.V t x z < M.V t x' z
      rw [← hval]
      refine lt_of_lt_of_le ?_ (h.obj_le_V ht hx' ha')
      simp only [obj]
      exact add_lt_add_of_lt_of_le hu (mul_le_mul_of_nonneg_left hcont hβ)
  intro t ht
  have := key (M.T - t) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self ht] at this

end OCModel

end Miao.IncompleteMarkets
