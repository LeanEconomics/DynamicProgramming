/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Finite

/-!
# The recursive formulation of the stochastic growth model

AKMM, §7.3.3, (7.15)–(7.16), pp. 200–201, in a form reused for Appendix 7.A.1 and §7.6.

A Bellman problem with an endogenous state `k > 0` and an exogenous state `x` that moves to
`nxt x s` with probability `P x s` (finitely many `s`): resources `f(x, k)`, choice `k′`,
`V(x, k) = max_{0 < k′ < f(x, k)} u(f(x, k) − k′) + β Σₛ P(x, s)V(nxt x s, k′)`, attained at
`k′ = g(x, k)` (`rb_Bellman`). For the planner `x = A` is TFP and `nxt A A′ = A′`.

* The first-order condition (7.15) `u′(C) = β Σ π(A′|A)V₂(A′, K′)` (`rb_foc`, `eq_7_15`).
* The envelope condition `V₂(A, K) = u′(C)f₂(A, K)` (`rb_envelope`, `rec_envelope`), proved
  from the Bellman equation for a differentiable `V` (comparing with the plan that keeps `K′`).
* The functional Euler equation (7.16)
  `u′(f(A, K) − g(A, K)) = β Σ π(A′|A)u′(f(A′, g(A, K)) − g(A′, g(A, K)))f₂(A′, g(A, K))`
  (`rb_euler`, `eq_7_16`).
* The Euler equation printed after the envelope condition, with `f₂(A, K)` in place of
  `f₂(A′, K′)`, is false (`rec_euler_printed_counterexample`: a two-state log/linear economy
  whose Bellman solution satisfies (7.16) but not the printed equation).

Departure: the existence and differentiability of `V` are hypotheses (the book assumes them; in
SLP's setting they are Theorems 9.6–9.10 of `StochasticDP`), and choices are interior
(`0 < k′ < f`).
-/

namespace AKMM.Uncertainty

open Filter Topology

variable {X S : Type*} [Fintype S]

/-- The Bellman equation with endogenous state `k > 0`, exogenous state `x` with transitions
`nxt x s` (probability `P x s`), resources `f(x, k)` and policy `g`: `g(x, k)` is interior,
attains the maximum, and `V` is the maximum value. -/
def rb_Bellman (u : ℝ → ℝ) (β : ℝ) (P : X → S → ℝ) (nxt : X → S → X) (f V g : X → ℝ → ℝ) :
    Prop :=
  ∀ x k, 0 < k → (0 < g x k ∧ g x k < f x k) ∧
    V x k = u (f x k - g x k) + β * ∑ s, P x s * V (nxt x s) (g x k) ∧
    ∀ k', 0 < k' → k' < f x k → u (f x k - k') + β * ∑ s, P x s * V (nxt x s) k' ≤ V x k

/-- **AKMM, (7.15), p. 201: the first-order condition.** With `u` differentiable at
`C = f(x, k) − g(x, k)` and each `V(nxt x s, ·)` differentiable at `k′ = g(x, k)`,
`u′(C) = β Σₛ P(x, s)V₂(nxt x s, k′)`. -/
theorem rb_foc {u : ℝ → ℝ} {β : ℝ} {P : X → S → ℝ} {nxt : X → S → X} {f V g : X → ℝ → ℝ}
    (hB : rb_Bellman u β P nxt f V g) {x : X} {k : ℝ} (hk : 0 < k) {du : ℝ} {V2 : S → ℝ}
    (hu : HasDerivAt u du (f x k - g x k))
    (hV : ∀ s, HasDerivAt (V (nxt x s)) (V2 s) (g x k)) :
    du = β * ∑ s, P x s * V2 s := by
  obtain ⟨⟨hg0, hgf⟩, hval, hle⟩ := hB x k hk
  have hd : HasDerivAt (fun k' => u (f x k - k') + β * ∑ s, P x s * V (nxt x s) k')
      (du * (-1) + β * ∑ s, P x s * V2 s) (g x k) := by
    refine (hu.comp (g x k) ((hasDerivAt_id' (g x k)).const_sub (f x k))).add
      (HasDerivAt.const_mul β ?_)
    exact HasDerivAt.fun_sum fun s _ => (hV s).const_mul (P x s)
  have hmax : IsLocalMax (fun k' => u (f x k - k') + β * ∑ s, P x s * V (nxt x s) k')
      (g x k) := by
    filter_upwards [lt_mem_nhds hg0, gt_mem_nhds hgf] with k' h1 h2
    rw [← hval]
    exact hle k' h1 h2
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, p. 201: the envelope condition** `V₂(x, k) = u′(C)f₂(x, k)`, for `V(x, ·)`, `f(x, ·)`
differentiable at `k` and `u` at `C = f(x, k) − g(x, k)`. -/
theorem rb_envelope {u : ℝ → ℝ} {β : ℝ} {P : X → S → ℝ} {nxt : X → S → X} {f V g : X → ℝ → ℝ}
    (hB : rb_Bellman u β P nxt f V g) {x : X} {k : ℝ} (hk : 0 < k) {du V2 f2 : ℝ}
    (hV : HasDerivAt (V x) V2 k) (hf : HasDerivAt (f x) f2 k)
    (hu : HasDerivAt u du (f x k - g x k)) : V2 = du * f2 := by
  obtain ⟨⟨hg0, hgf⟩, hval, -⟩ := hB x k hk
  set k' := g x k
  -- `V(x, j) ≥ u(f(x, j) − k′) + β Σ P V(·, k′)` near `k`, with equality at `k`
  have hd : HasDerivAt (fun j => V x j - (u (f x j - k') + β * ∑ s, P x s * V (nxt x s) k'))
      (V2 - du * f2) k := by
    have h1 : HasDerivAt (fun j => u (f x j - k')) (du * f2) k :=
      hu.comp k (hf.sub_const k')
    exact hV.sub (h1.add_const _)
  have hmin : IsLocalMin (fun j => V x j - (u (f x j - k') + β * ∑ s, P x s * V (nxt x s) k'))
      k := by
    have hcont : ContinuousAt (f x) k := hf.continuousAt
    filter_upwards [lt_mem_nhds hk, (continuousAt_const.eventually_lt hcont hgf)] with j hj hfj
    have := ((hB x j hj).2.2 k' hg0 hfj)
    have h0 : V x k - (u (f x k - k') + β * ∑ s, P x s * V (nxt x s) k') = 0 := by
      rw [hval]; ring
    change V x k - _ ≤ V x j - _
    rw [h0]
    linarith
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- **AKMM, (7.16), p. 201: the functional Euler equation.** If `u` is differentiable on
`(0, ∞)` with derivative `u′`, and `V(x, ·)`, `f(x, ·)` are differentiable on `(0, ∞)`, then
for every `x` and `k > 0`, with `k′ = g(x, k)`,
`u′(f(x, k) − g(x, k)) = β Σₛ P(x, s)u′(f(x′, k′) − g(x′, k′))f₂(x′, k′)`, `x′ = nxt x s`. -/
theorem rb_euler {u u' : ℝ → ℝ} {β : ℝ} {P : X → S → ℝ} {nxt : X → S → X}
    {f V g V2 f2 : X → ℝ → ℝ} (hB : rb_Bellman u β P nxt f V g)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hV : ∀ x k, 0 < k → HasDerivAt (V x) (V2 x k) k)
    (hf : ∀ x k, 0 < k → HasDerivAt (f x) (f2 x k) k) {x : X} {k : ℝ} (hk : 0 < k) :
    u' (f x k - g x k) = β * ∑ s, P x s *
      (u' (f (nxt x s) (g x k) - g (nxt x s) (g x k)) * f2 (nxt x s) (g x k)) := by
  have hg := (hB x k hk).1
  have hC : 0 < f x k - g x k := by linarith [hg.2]
  rw [rb_foc hB hk (hu _ hC) (fun s => hV (nxt x s) (g x k) hg.1)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have hg' := (hB (nxt x s) (g x k) hg.1).1
  have hC' : 0 < f (nxt x s) (g x k) - g (nxt x s) (g x k) := by linarith [hg'.2]
  rw [rb_envelope hB hg.1 (hV _ _ hg.1) (hf _ _ hg.1) (hu _ hC')]

/-! ### The planner -/

/-- **AKMM, (7.15), p. 201**, for the planner: `u′(C) = β Σ_{A′} π(A′|A)V₂(A′, K′)`. -/
theorem eq_7_15 {u : ℝ → ℝ} {β : ℝ} {P : S → S → ℝ} {f V g : S → ℝ → ℝ}
    (hB : rb_Bellman u β P (fun _ s => s) f V g) {A : S} {K : ℝ} (hK : 0 < K) {du : ℝ}
    {V2 : S → ℝ} (hu : HasDerivAt u du (f A K - g A K))
    (hV : ∀ A', HasDerivAt (V A') (V2 A') (g A K)) : du = β * ∑ A', P A A' * V2 A' :=
  rb_foc hB hK hu hV

/-- AKMM, p. 201: the planner's envelope condition `V₂(A, K) = u′(C)f₂(A, K)`. -/
theorem rec_envelope {u : ℝ → ℝ} {β : ℝ} {P : S → S → ℝ} {f V g : S → ℝ → ℝ}
    (hB : rb_Bellman u β P (fun _ s => s) f V g) {A : S} {K : ℝ} (hK : 0 < K) {du V2 f2 : ℝ}
    (hV : HasDerivAt (V A) V2 K) (hf : HasDerivAt (f A) f2 K)
    (hu : HasDerivAt u du (f A K - g A K)) : V2 = du * f2 :=
  rb_envelope hB hK hV hf hu

/-- **AKMM, (7.16), p. 201**, for the planner:
`u′(f(A, K) − g(A, K)) = β Σ_{A′} π(A′|A)u′(f(A′, g(A, K)) − g(A′, g(A, K)))f₂(A′, g(A, K))`. -/
theorem eq_7_16 {u u' : ℝ → ℝ} {β : ℝ} {P : S → S → ℝ} {f V g V2 f2 : S → ℝ → ℝ}
    (hB : rb_Bellman u β P (fun _ s => s) f V g) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hV : ∀ A K, 0 < K → HasDerivAt (V A) (V2 A K) K)
    (hf : ∀ A K, 0 < K → HasDerivAt (f A) (f2 A K) K) (A : S) {K : ℝ} (hK : 0 < K) :
    u' (f A K - g A K) = β * ∑ A', P A A' *
      (u' (f A' (g A K) - g A' (g A K)) * f2 A' (g A K)) :=
  rb_euler hB hu hV hf hK

/-! ### The printed Euler equation -/

/-- The two-state counterexample: TFP `a = (1, 2)`, state `1` absorbing and reached from state
`0` for sure, `f(A, K) = aK`, `u = log`, `β = 1/2`. -/
noncomputable def recEx_a : Fin 2 → ℝ := ![1, 2]

theorem recEx_bellman :
    rb_Bellman Real.log (1 / 2) (fun _ s' => if s' = 1 then 1 else 0) (fun _ s => s)
      (fun s K => recEx_a s * K)
      (fun s K => 2 * Real.log K + ![2 * Real.log (1 / 2), 0] s)
      (fun s K => 1 / 2 * recEx_a s * K) := by
  intro s K hK
  have ha : 0 < recEx_a s := by fin_cases s <;> norm_num [recEx_a]
  have haK : 0 < recEx_a s * K := mul_pos ha hK
  have hsum : ∀ k : ℝ, ∑ s' : Fin 2, (if s' = 1 then (1 : ℝ) else 0) *
      (2 * Real.log k + ![2 * Real.log (1 / 2), 0] s') = 2 * Real.log k := fun k => by
    simp
  -- the maximised value is `2 log(aK/2)`
  have hval : 2 * Real.log K + ![2 * Real.log (1 / 2), 0] s = 2 * Real.log (recEx_a s * K / 2) := by
    rw [show recEx_a s * K / 2 = K * (recEx_a s / 2) by ring,
      Real.log_mul hK.ne' (div_pos ha two_pos).ne']
    fin_cases s <;> (simp [recEx_a]; try ring)
  refine ⟨⟨by positivity, by nlinarith⟩, ?_, fun k' hk' hk'f => ?_⟩
  · beta_reduce
    rw [hsum, hval, show recEx_a s * K - 1 / 2 * recEx_a s * K = recEx_a s * K / 2 by ring,
      show 1 / 2 * recEx_a s * K = recEx_a s * K / 2 by ring]
    ring
  · beta_reduce at hk'f ⊢
    rw [hsum, hval]
    -- `log x + log y ≤ 2 log((x + y)/2)`
    have hx : 0 < recEx_a s * K - k' := by linarith
    have hxy : (recEx_a s * K - k') * k' ≤ (recEx_a s * K / 2) ^ 2 := by
      nlinarith [sq_nonneg (recEx_a s * K - 2 * k')]
    have hl := Real.log_le_log (mul_pos hx hk') hxy
    rw [Real.log_mul hx.ne' hk'.ne', Real.log_pow] at hl
    push_cast at hl
    linarith

/-- **AKMM, p. 201: the Euler equation printed after the envelope condition is false.** In the
two-state economy of `recEx_bellman`, whose Bellman solution has the policy `K′ = aK/2`, at
`A = 0`, `K = 1` the functional Euler equation (7.16) holds (`u′(C) = 2` on both sides) while
the printed `u′(C) = β Σ π(A′|A)[u′(C′)f₂(A, K)]` has right-hand side `1`. -/
theorem rec_euler_printed_counterexample :
    let f : Fin 2 → ℝ → ℝ := fun s K => recEx_a s * K
    let g : Fin 2 → ℝ → ℝ := fun s K => 1 / 2 * recEx_a s * K
    let P : Fin 2 → Fin 2 → ℝ := fun _ s' => if s' = 1 then 1 else 0
    (f 0 1 - g 0 1)⁻¹ = 1 / 2 * ∑ s, P 0 s * ((f s (g 0 1) - g s (g 0 1))⁻¹ * recEx_a s) ∧
      (f 0 1 - g 0 1)⁻¹ ≠ 1 / 2 * ∑ s, P 0 s * ((f s (g 0 1) - g s (g 0 1))⁻¹ * recEx_a 0) := by
  intro f g P
  simp only [f, g, P, Fin.sum_univ_two, recEx_a]
  norm_num

end AKMM.Uncertainty
