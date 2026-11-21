/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.PlannerSufficiency

/-!
# Competitive equilibrium in the stochastic growth model

AKMM, §7.5, Definition 15, (7.26)–(7.29), pp. 210–212. Notation of `PlannerTree`: histories
`h = ωᵗ` of Miao's `BPTree`, capital `k h = kₜ₊₁(ωᵗ)` chosen at `h`, `pt_prevK k₀ k h = kₜ(ωᵗ⁻¹)`.
`F(k) = F(k, 1)`, `F_K`, `F_L` its partial derivatives at `(k, 1)`.

* The household's budget (7.29) `cₜ + kₜ₊₁ = (rₜ + 1 − δ)kₜ + wₜ` is the resource constraint of
  `PlannerTree` with "TFP" `(rₜ, wₜ)` and `f((r, w), k) = (r + 1 − δ)k + w`, so the household's
  problem is `pt_Optimal` at those prices.
* **Definition 15** (`definition_15`): the household optimises, prices are (7.26)–(7.27), and the
  aggregate resource constraint holds.
* **(7.28)** `u′(cₜ) = Eₜ[βu′(cₜ₊₁)(rₜ₊₁ + 1 − δ)]`: from the Lagrangian (`eq_7_28_lagrangian`) and
  at every optimum with `kₜ₊₁ > 0` (`eq_7_28`, from `eq_7_13`).
* Condition 3 is superfluous: with Euler's theorem `F(k) = F_K(k)k + F_L(k)` the budget and prices
  give the resource constraint (`definition_15_resource_redundant`).
* With (7.26), (7.28) is the planner's Euler equation (7.13) for `f(A, K) = AF(K) + (1 − δ)K`
  (`ce_euler_is_planner`), and under the concavity and transversality conditions of
  `pt_euler_tvc_optimal` the equilibrium allocation solves the planner's problem
  (`ce_planner_optimal`).

Departures: the household's problem includes `kₜ₊₁ ≥ 0` (the book assumes it does not bind; the
equilibrium results use `kₜ₊₁ > 0`); the no-Ponzi condition is not needed with `k ≥ 0`.
-/

namespace AKMM.Uncertainty

open Miao.CompleteMarkets Filter Topology

variable {S : Type*} [Fintype S]

/-- AKMM, (7.29), p. 211: the household's resources `(r + 1 − δ)k + w`. -/
def ce_hf (δ : ℝ) (q : ℝ × ℝ) (k : ℝ) : ℝ := (q.1 + 1 - δ) * k + q.2

/-- AKMM, (7.11), p. 211: the aggregate resources `AF(k, 1) + (1 − δ)k`. -/
def ce_f (δ : ℝ) (F : ℝ → ℝ) (a k : ℝ) : ℝ := a * F k + (1 - δ) * k

/-- **AKMM, Definition 15, p. 212: a sequential competitive equilibrium** of the stochastic growth
model: (1) `(c, k)` solves the household's problem at the prices `(r, w)` (7.29); (2) prices are
(7.26)–(7.27), `r = AF_K(k, 1)`, `w = AF_L(k, 1)`; (3) the resource constraint holds. -/
def definition_15 (T : BPTree S) (β : ℝ) (u : ℝ → ℝ) (δ : ℝ) (A : List S → ℝ)
    (F FK FL : ℝ → ℝ) (k0 : ℝ) (r w c k : List S → ℝ) : Prop :=
  pt_Optimal T β u (ce_hf δ) (fun h => (r h, w h)) k0 c k ∧
    (∀ h, r h = A h * FK (pt_prevK k0 k h) ∧ w h = A h * FL (pt_prevK k0 k h)) ∧
    pt_Resource (ce_f δ F) A k0 c k

/-- **AKMM, (7.28), p. 211, from the Lagrangian.** The conditions `βᵗπₜu′(cₜ) = λₜ` and
`λₜ = Σ_{ωᵗ⁺¹|ωᵗ}(rₜ₊₁ + 1 − δ)λₜ₊₁` give
`u′(cₜ) = β Σ πₜ₊₁(ωᵗ⁺¹|ωᵗ)u′(cₜ₊₁)(rₜ₊₁ + 1 − δ)`. -/
theorem eq_7_28_lagrangian (T : BPTree S) {β δ : ℝ} (hβ : 0 < β) {du : ℝ → ℝ}
    {r c lam : List S → ℝ} (hC : ∀ h, T.pr h * β ^ h.length * du (c h) = lam h)
    (hk : ∀ h, lam h = ∑ s, (r (s :: h) + 1 - δ) * lam (s :: h)) (h : List S) :
    du (c h) = β * ∑ s, T.pr (s :: h) / T.pr h * du (c (s :: h)) * (r (s :: h) + 1 - δ) :=
  eq_7_12_7_13 T hβ (f2 := fun a _ => a + 1 - δ) (A := r) (K := c) hC
    (fun g => by rw [hk g]; exact Finset.sum_congr rfl fun s _ => by ring) h

/-- **AKMM, (7.28), p. 211: the household's Euler equation holds at the optimum.** If `(c, k)`
solves the household's problem at the prices `(r, w)`, `u` is differentiable on `(0, ∞)` and
`kₜ₊₁(ωᵗ) > 0`, then `u′(cₜ) = β Σ πₜ₊₁(ωᵗ⁺¹|ωᵗ)u′(cₜ₊₁)(rₜ₊₁ + 1 − δ)` at `ωᵗ`. -/
theorem eq_7_28 (T : BPTree S) {β δ : ℝ} (hβ : 0 < β) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c) {k0 : ℝ} {r w c k : List S → ℝ}
    (hopt : pt_Optimal T β u (ce_hf δ) (fun h => (r h, w h)) k0 c k) (h : List S)
    (hk : 0 < k h) :
    du (c h) = β * ∑ s, T.pr (s :: h) / T.pr h * du (c (s :: h)) * (r (s :: h) + 1 - δ) := by
  have hf : ∀ (q : ℝ × ℝ) (x : ℝ), 0 < x → HasDerivAt (ce_hf δ q) (q.1 + 1 - δ) x :=
    fun q x _ => (((hasDerivAt_id' x).const_mul (q.1 + 1 - δ)).add_const q.2).congr_deriv
      (mul_one _)
  exact eq_7_13 T hβ hu (f2 := fun q _ => q.1 + 1 - δ) hf hopt h hk

omit [Fintype S] in
/-- **AKMM, p. 212: condition 3 of Definition 15 is superfluous.** If the budget (7.29) holds at
the prices (7.26)–(7.27) and `F(k) = F_K(k)k + F_L(k)` (Euler's theorem for constant returns,
Chapter 5's `euler_crs`) at the capital stocks used, the resource constraint holds. -/
theorem definition_15_resource_redundant {δ : ℝ} {A : List S → ℝ} {F FK FL : ℝ → ℝ} {k0 : ℝ}
    {r w c k : List S → ℝ} (hbud : pt_Resource (ce_hf δ) (fun h => (r h, w h)) k0 c k)
    (hprice : ∀ h, r h = A h * FK (pt_prevK k0 k h) ∧ w h = A h * FL (pt_prevK k0 k h))
    (heuler : ∀ h, F (pt_prevK k0 k h) =
      FK (pt_prevK k0 k h) * pt_prevK k0 k h + FL (pt_prevK k0 k h)) :
    pt_Resource (ce_f δ F) A k0 c k := by
  intro h
  rw [hbud h]
  simp only [ce_hf, ce_f, (hprice h).1, (hprice h).2, heuler h]
  ring

omit [Fintype S] in
/-- **AKMM, p. 212: the equilibrium Euler equation is the planner's.** Substituting (7.26) into
(7.28) gives (7.13) with `f₂(A, K) = AF_K(K) + 1 − δ`. -/
theorem ce_euler_is_planner [Fintype S] (T : BPTree S) {β δ : ℝ} {du : ℝ → ℝ}
    {A : List S → ℝ} {FK : ℝ → ℝ} {k0 : ℝ} {r c k : List S → ℝ}
    (hprice : ∀ h, r h = A h * FK (pt_prevK k0 k h)) (h : List S)
    (h728 : du (c h) =
      β * ∑ s, T.pr (s :: h) / T.pr h * du (c (s :: h)) * (r (s :: h) + 1 - δ)) :
    du (c h) =
      β * ∑ s, T.pr (s :: h) / T.pr h * du (c (s :: h)) * (A (s :: h) * FK (k h) + 1 - δ) := by
  rw [h728]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by rw [hprice (s :: h)]; rfl

/-- **AKMM, p. 212: the competitive equilibrium allocation solves the planner's problem.** Let
`(r, w, c, k)` be an equilibrium (Definition 15) with `kₜ₊₁ > 0` at every history, `u`
differentiable with `u(c′) ≤ u(c) + u′(c)(c′ − c)` and `u′ > 0`, `k₀ ≥ 0`, and the planner's
`f(A, ·) = AF + (1 − δ)·` below its tangent at the equilibrium capital stocks. If the
transversality condition `βᵗ Σ πₜu′(cₜ)kₜ₊₁ → 0` holds, `(c, k)` solves the planner's problem. -/
theorem ce_planner_optimal (T : BPTree S) {β δ : ℝ} (hβ : 0 < β) {u du : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (du c) c)
    (htan : ∀ c c', 0 < c → 0 < c' → u c' ≤ u c + du c * (c' - c))
    (hdu : ∀ c, 0 < c → 0 < du c) {A : List S → ℝ} {F FK FL : ℝ → ℝ} {k0 : ℝ} (hk0 : 0 ≤ k0)
    {r w c k : List S → ℝ} (heq : definition_15 T β u δ A F FK FL k0 r w c k)
    (hk : ∀ h, 0 < k h)
    (hf : ∀ h k', 0 ≤ k' → ce_f δ F (A h) k' ≤ ce_f δ F (A h) (pt_prevK k0 k h) +
      (A h * FK (pt_prevK k0 k h) + 1 - δ) * (k' - pt_prevK k0 k h))
    (htvc : Tendsto (fun t => β ^ t * bp_nodeSum t (fun h => T.pr h * du (c h) * k h)) atTop
      (𝓝 0)) :
    pt_Optimal T β u (ce_f δ F) A k0 c k := by
  obtain ⟨hopt, hprice, hres⟩ := heq
  obtain ⟨hc, hknn, -, hsum⟩ := hopt.1
  refine pt_euler_tvc_optimal T hβ htan (f2 := fun a K => a * FK K + 1 - δ) hk0 hf
    (fun h => hdu _ (hc h)) ⟨hc, hknn, hres, hsum⟩ (fun h => ?_) htvc
  exact ce_euler_is_planner T (fun g => (hprice g).1) h (eq_7_28 T hβ hu hopt h (hk h))

end AKMM.Uncertainty
