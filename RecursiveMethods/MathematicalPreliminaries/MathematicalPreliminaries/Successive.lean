/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.Blackwell
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Iterate

/-!
# The method of successive approximations

SLP Chapter 3 introduction, pp. 39–43.

* `policyValue`, `exercise_3_1` (Ex 3.1): the lifetime utility `w₀` of a feasible policy `g₀`
  satisfies `w₀(k) = U[f(k) − g₀(k)] + βw₀[g₀(k)]`.
* `policyValue_le_bellmanOp` ((4), p. 41): starting from `v₀ = w₀`, the first approximation is an
  improvement, `v₁ ≥ v₀`.
* `iterate_mono` (pp. 41–42): if `T` is monotone and `v₁ ≥ v₀`, the successive approximations
  increase, `v_{n+1} ≥ v_n`.
* `fixedPoint_eq_limit` (p. 40, "(Why?)"): if the successive approximations converge to the same
  limit from every initial guess, that limit is the only solution of the functional equation.
-/

open Filter Topology

namespace StokeyLucasPrescott.MathematicalPreliminaries

variable {X : Type*}

/-- The lifetime utility `w₀(k) = ∑ βᵗ R(k_t)` of the policy `g₀` from `k`, with `k_{t+1} = g₀(k_t)`
and per-period utility `R(k) = U[f(k) − g₀(k)]`. -/
noncomputable def policyValue (R : X → ℝ) (g : X → X) (β : ℝ) (k : X) : ℝ :=
  ∑' t, β ^ t * R (g^[t] k)

/-- **Ex 3.1.** `w₀(k) = R(k) + βw₀(g₀(k))`, whenever the series defining `w₀(k)` converges. -/
theorem exercise_3_1 {R : X → ℝ} {g : X → X} {β : ℝ} {k : X}
    (hs : Summable fun t => β ^ t * R (g^[t] k)) :
    policyValue R g β k = R k + β * policyValue R g β (g k) := by
  have e : ∀ t, β ^ (t + 1) * R (g^[t + 1] k) = β * (β ^ t * R (g^[t] (g k))) := fun t => by
    rw [Function.iterate_succ_apply, pow_succ]
    ring
  unfold policyValue
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Function.iterate_zero_apply, e, tsum_mul_left]

/-- **(4), p. 41.** If `g₀(k)` is feasible, `R(k) = F(k, g₀(k))` and `w₀` satisfies Ex 3.1, the
first successive approximation from `w₀` improves on it: `w₀ ≤ Tw₀`. -/
theorem policyValue_le_bellmanOp {Γ : X → Set X} {F : X → X → ℝ} {M : ℝ}
    (hF : ∀ x y, |F x y| ≤ M) {g : X → X} (hg : ∀ k, g k ∈ Γ k) {β : ℝ}
    (hs : ∀ k, Summable fun t => β ^ t * F (g^[t] k) (g (g^[t] k)))
    (hbdd : IsBdd (policyValue (fun k => F k (g k)) g β)) (k : X) :
    policyValue (fun k => F k (g k)) g β k ≤
      bellmanOp Γ F β (policyValue (fun k => F k (g k)) g β) k := by
  have h := exercise_3_1 (R := fun k => F k (g k)) (g := g) (β := β) (k := k) (hs k)
  rw [h]
  exact le_bellmanOp hF hbdd (hg k)

/-- **pp. 41–42.** If `T` is monotone and `v₀ ≤ Tv₀`, the successive approximations `vₙ = Tⁿv₀`
increase. -/
theorem iterate_mono {α : Type*} [Preorder α] {T : α → α} (hT : Monotone T) {v₀ : α}
    (h : v₀ ≤ T v₀) : Monotone fun n => T^[n] v₀ :=
  hT.monotone_iterate_of_le_map h

/-- **p. 40, "(Why?)".** If `Tⁿv₀ → L` for every initial guess `v₀`, every fixed point of `T` is
`L`: the functional equation has exactly one solution. -/
theorem fixedPoint_eq_limit {α : Type*} [TopologicalSpace α] [T2Space α] {T : α → α} {L : α}
    (h : ∀ v₀, Tendsto (fun n => T^[n] v₀) atTop (𝓝 L)) {v : α} (hv : T v = v) : v = L := by
  have hconst : Tendsto (fun n => T^[n] v) atTop (𝓝 v) := by
    simp only [Function.iterate_fixed hv]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst (h v)

end StokeyLucasPrescott.MathematicalPreliminaries
