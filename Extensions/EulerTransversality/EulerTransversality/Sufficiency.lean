/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Euler equations and transversality are sufficient

Stokey and Lucas (1989), Thm 4.15; Ekeland and Scheinkman (1986).

A reduced-form problem chooses a path `x_0, x_1, …` in a real vector space with
`(x_t, x_{t+1}) ∈ G` and `x_0` given, to maximize `∑ β^t F(x_t, x_{t+1})`. Concavity and
differentiability enter only through **supergradients**: linear `p_t`, `q_t` with
`F(a, b) ≤ F(x*_t, x*_{t+1}) + p_t(a − x*_t) + q_t(b − x*_{t+1})` for `(a, b) ∈ G`.

* `finite_horizon_bound`: with the **Euler equation** `q_t + βp_{t+1} = 0`, every feasible path
  satisfies `∑_{t<T} β^tF(x_t, x_{t+1}) + β^Tp_T(x_T)`
  `≤ ∑_{t<T} β^tF(x*_t, x*_{t+1}) + β^Tp_T(x*_T)`.
* `euler_tvc_sufficient`: if moreover `p_t(x_t) ≥ 0` along feasible paths (shadow prices and
  states nonnegative) and the **transversality condition** `β^tp_t(x*_t) → 0` holds, then `x*` is
  optimal in the catching-up sense, and its value is the largest whenever values are finite.

No differentiability, interiority or boundedness is assumed.
-/

open Filter Topology

namespace DPExtensions.EulerTransversality

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The value of the first `T` periods of a path, `∑_{t<T} β^tF(x_t, x_{t+1})`. -/
noncomputable def partialValue (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * F (x t) (x (t + 1))

/-- A path is feasible from `x_0` if it starts there and stays in the graph `G`. -/
def Feasible (G : Set (X × X)) (x0 : X) (x : ℕ → X) : Prop :=
  x 0 = x0 ∧ ∀ t, (x t, x (t + 1)) ∈ G

/-- **Catching-up optimality**: no feasible path is eventually ahead by more than any `ε > 0`. -/
def CatchingUp (G : Set (X × X)) (F : X → X → ℝ) (β : ℝ) (xs : ℕ → X) : Prop :=
  ∀ x, Feasible G (xs 0) x → ∀ ε > 0, ∀ᶠ T in atTop,
    partialValue F β x T ≤ partialValue F β xs T + ε

omit [AddCommGroup X] [Module ℝ X] in
theorem partialValue_succ (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (T : ℕ) :
    partialValue F β x (T + 1) = partialValue F β x T + β ^ T * F (x T) (x (T + 1)) :=
  Finset.sum_range_succ _ _

/-- **The finite-horizon bound** from supergradients and the Euler equation. -/
theorem finite_horizon_bound {G : Set (X × X)} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → X} {p q : ℕ → X →ₗ[ℝ] ℝ}
    (hsup : ∀ t, ∀ a b, (a, b) ∈ G →
      F a b ≤ F (xs t) (xs (t + 1)) + p t (a - xs t) + q t (b - xs (t + 1)))
    (heuler : ∀ t v, q t v + β * p (t + 1) v = 0) {x : ℕ → X} (hx : Feasible G (xs 0) x)
    (T : ℕ) :
    partialValue F β x T + β ^ T * p T (x T) ≤ partialValue F β xs T + β ^ T * p T (xs T) := by
  induction T with
  | zero => simp [partialValue, hx.1]
  | succ T ih =>
    rw [partialValue_succ, partialValue_succ]
    have h1 := hsup T (x T) (x (T + 1)) (hx.2 T)
    have h2 := heuler T (x (T + 1) - xs (T + 1))
    simp only [map_sub] at h1 h2
    have hb : 0 ≤ β ^ T := pow_nonneg hβ T
    have h3 := mul_le_mul_of_nonneg_left h1 hb
    rw [pow_succ]
    nlinarith

/-- **Euler equation and transversality are sufficient** for catching-up optimality, and for
optimality whenever the values are finite. -/
theorem euler_tvc_sufficient {G : Set (X × X)} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    {xs : ℕ → X} {p q : ℕ → X →ₗ[ℝ] ℝ}
    (hsup : ∀ t, ∀ a b, (a, b) ∈ G →
      F a b ≤ F (xs t) (xs (t + 1)) + p t (a - xs t) + q t (b - xs (t + 1)))
    (heuler : ∀ t v, q t v + β * p (t + 1) v = 0)
    (hnn : ∀ x, Feasible G (xs 0) x → ∀ t, 0 ≤ p t (x t))
    (htvc : Tendsto (fun t => β ^ t * p t (xs t)) atTop (𝓝 0)) :
    CatchingUp G F β xs ∧ ∀ x, Feasible G (xs 0) x →
      (Summable fun t => β ^ t * F (x t) (x (t + 1))) →
      (Summable fun t => β ^ t * F (xs t) (xs (t + 1))) →
      ∑' t, β ^ t * F (x t) (x (t + 1)) ≤ ∑' t, β ^ t * F (xs t) (xs (t + 1)) := by
  have hbound : ∀ x, Feasible G (xs 0) x → ∀ T,
      partialValue F β x T ≤ partialValue F β xs T + β ^ T * p T (xs T) := fun x hx T => by
    have h := finite_horizon_bound hβ hsup heuler hx T
    have := mul_nonneg (pow_nonneg hβ T) (hnn x hx T)
    linarith
  refine ⟨fun x hx ε hε => ?_, fun x hx hs hss => ?_⟩
  · filter_upwards [htvc.eventually (gt_mem_nhds hε)] with T hT
    linarith [hbound x hx T]
  · have h1 : Tendsto (partialValue F β x) atTop (𝓝 (∑' t, β ^ t * F (x t) (x (t + 1)))) :=
      hs.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun T => partialValue F β xs T + β ^ T * p T (xs T)) atTop
        (𝓝 (∑' t, β ^ t * F (xs t) (xs (t + 1)) + 0)) :=
      hss.hasSum.tendsto_sum_nat.add htvc
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 (hbound x hx)

end DPExtensions.EulerTransversality
