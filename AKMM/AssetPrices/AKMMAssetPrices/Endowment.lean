/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.Portfolio
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The endowment economy: planner, Arrow–Debreu equilibrium and the First Welfare Theorem

AKMM, §16.3, pp. 469–472. A finite set `I` of agents with utilities `Uᵢ` over consumption plans
`cᵢ : H → ℝ`, where `H` is the (finite) set of date–history pairs `(t, ωᵗ)`; the aggregate
endowment is `y`. Marginal utilities are the partial derivatives `∂Uᵢ/∂cᵢ(h) = DUᵢ(e_h)` of a
Fréchet derivative `DUᵢ`.

* **Planner** (16.1)/(16.6): at an optimum of `Σᵢ λᵢUᵢ(cᵢ)` subject to feasibility, the weighted
  marginal utilities are equal across agents, `λᵢ∂Uᵢ/∂cᵢ(h) = μ(h)` (`eq_16_1_pair`, `eq_16_1`),
  proved from optimality by moving consumption between two agents.
* **Envelope** (16.2): if the planner value `U_λ` is differentiable, `∂U_λ/∂y(h) = μ(h)`
  (`eq_16_2`), for the value function defined as a supremum (`en_plannerValue`); and (16.3)
  (`eq_16_3`).
* **Arrow–Debreu** (16.4)/(16.7): at an optimum on the budget set, `∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)`
  (`eq_16_4_pair`, `eq_16_4`), `αᵢ > 0` when marginal utilities are positive (`eq_16_4_pos`), and
  (16.5) (`eq_16_5`).
* **First Welfare Theorem** (p. 471): with `λᵢ = 1/αᵢ` the equilibrium satisfies the planner's
  conditions with `μ = p⁰` (`en_weights_match`), and with concave utilities the equilibrium
  allocation solves the planner problem with those weights (`en_fwt_planner`), hence is Pareto
  optimal (`en_fwt_pareto`). The gradient inequality for concave utilities is
  `en_concave_le_fderiv`.

Departures: finitely many agents and a finite set of date–history pairs (a finite horizon); the
first-order conditions are derived at an optimum with differentiable utilities and positive
prices; the welfare theorem is proved for concave utilities (and in Pareto form for strictly
increasing ones it is Miao's `theorem_13_3_1`, for expected utility on the infinite tree). See
`docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Filter Topology

variable {I H : Type} [Fintype I] [Fintype H]

/-- The derivative of `t ↦ U(c + t v)` at `0` is `DU v`. -/
theorem en_line_deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → ℝ}
    {DU : E →L[ℝ] ℝ} {c : E} (hU : HasFDerivAt U DU c) (v : E) :
    HasDerivAt (fun t : ℝ => U (c + t • v)) (DU v) 0 := by
  have hU' : HasFDerivAt U DU (c + (0 : ℝ) • v) := by simpa using hU
  have hl : HasDerivAt (fun t : ℝ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  exact hU'.comp_hasDerivAt (0 : ℝ) hl

/-- AKMM, p. 470: a feasible allocation, `Σᵢ cᵢ(h) ≤ y(h)` for every date and history. -/
def enFeasible (c : I → H → ℝ) (y : H → ℝ) : Prop := ∀ h, ∑ i, c i h ≤ y h

/-- AKMM, p. 470: `c` solves the planner problem with weights `λ`. -/
def enPlannerOpt (lam : I → ℝ) (U : I → (H → ℝ) → ℝ) (y : H → ℝ) (c : I → H → ℝ) : Prop :=
  enFeasible c y ∧ ∀ c', enFeasible c' y → ∑ i, lam i * U i (c' i) ≤ ∑ i, lam i * U i (c i)

omit [Fintype H] in
/-- AKMM, (16.1) and (16.6), p. 470: at a planner optimum, for any two agents,
`λᵢ ∂Uᵢ/∂cᵢ(h) = λⱼ ∂Uⱼ/∂cⱼ(h)`. -/
theorem eq_16_1_pair [Finite H] [DecidableEq H] {lam : I → ℝ} {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c)
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) (i j : I) (h : H) :
    lam i * DU i (Pi.single h 1) = lam j * DU j (Pi.single h 1) := by
  have := Fintype.ofFinite H
  classical
  by_cases hij : i = j
  · rw [hij]
  set w : I → H → ℝ := fun k =>
    (if k = i then Pi.single h 1 else 0) - (if k = j then Pi.single h 1 else 0) with hw
  have hsum : ∀ h', ∑ k, w k h' = 0 := fun h' => by
    simp only [hw, Pi.sub_apply, Finset.sum_sub_distrib]
    simp [apply_ite (fun f : H → ℝ => f h')]
  have hmax : IsLocalMax (fun t : ℝ => ∑ k, lam k * U k (c k + t • w k)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero]
    refine hopt.2 _ fun h' => ?_
    have := hopt.1 h'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum h', mul_zero, add_zero]
    exact this
  have hd : HasDerivAt (fun t : ℝ => ∑ k, lam k * U k (c k + t • w k))
      (∑ k, lam k * DU k (w k)) 0 :=
    HasDerivAt.fun_sum fun k _ => (en_line_deriv (hU k) (w k)).const_mul (lam k)
  have h0 := hmax.hasDerivAt_eq_zero hd
  simp only [hw, map_sub, apply_ite (DU _), map_zero, mul_sub, Finset.sum_sub_distrib] at h0
  simp only [mul_ite, mul_zero] at h0
  rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j] at h0
  simp only [Finset.mem_univ, ↓reduceIte] at h0
  linarith

omit [Fintype H] in
/-- AKMM, (16.1), p. 470: the weighted marginal utility of every agent equals a Lagrange
multiplier `μ(h)` independent of the agent. -/
theorem eq_16_1 [Finite H] [DecidableEq H] [Nonempty I] {lam : I → ℝ}
    {U : I → (H → ℝ) → ℝ} {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ}
    (hopt : enPlannerOpt lam U y c) (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) :
    ∃ μ : H → ℝ, ∀ i h, lam i * DU i (Pi.single h 1) = μ h := by
  have := Fintype.ofFinite H
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  exact ⟨fun h => lam i₀ * DU i₀ (Pi.single h 1), fun i h => eq_16_1_pair hopt hU i i₀ h⟩

/-- AKMM, p. 470: the planner's value `U_λ(y) = sup {Σᵢ λᵢUᵢ(cᵢ) : c feasible for y}`. -/
noncomputable def en_plannerValue (lam : I → ℝ) (U : I → (H → ℝ) → ℝ) (y : H → ℝ) : ℝ :=
  sSup {v | ∃ c, enFeasible c y ∧ v = ∑ i, lam i * U i (c i)}

omit [Fintype H] in
/-- At a planner optimum, `U_λ(y) = Σᵢ λᵢUᵢ(cᵢ)`. -/
theorem en_plannerValue_eq {lam : I → ℝ} {U : I → (H → ℝ) → ℝ} {y : H → ℝ}
    {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c) :
    en_plannerValue lam U y = ∑ i, lam i * U i (c i) := by
  refine IsGreatest.csSup_eq ⟨⟨c, hopt.1, rfl⟩, ?_⟩
  rintro v ⟨c', hc', rfl⟩
  exact hopt.2 c' hc'

omit [Fintype H] in
/-- `U_λ(y′) ≥ Σᵢ λᵢUᵢ(cᵢ′)` for every allocation feasible at `y′` (when the values are bounded
above). -/
theorem en_plannerValue_ge {lam : I → ℝ} {U : I → (H → ℝ) → ℝ} {y : H → ℝ}
    (hb : BddAbove {v | ∃ c, enFeasible c y ∧ v = ∑ i, lam i * U i (c i)})
    {c : I → H → ℝ} (hc : enFeasible c y) :
    ∑ i, lam i * U i (c i) ≤ en_plannerValue lam U y :=
  le_csSup hb ⟨c, hc, rfl⟩

omit [Fintype H] in
/-- AKMM, (16.2), p. 470 (envelope theorem): if the planner's value `U_λ` is differentiable at
`y`, its derivative with respect to the endowment of `h` is the multiplier,
`∂U_λ(y)/∂y(h) = λᵢ ∂Uᵢ/∂cᵢ(h) = μ(h)`, for every agent `i`. (Giving `h` to agent `i` is
feasible for `y + t e_h`, so `U_λ(y + t e_h) − λᵢUᵢ(cᵢ + t e_h) − Σ_{k≠i}λₖUₖ(cₖ)` has a minimum
at `t = 0`.) -/
theorem eq_16_2 [Finite H] [DecidableEq H] {lam : I → ℝ} {U : I → (H → ℝ) → ℝ}
    {DU : I → (H → ℝ) →L[ℝ] ℝ} {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c)
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i))
    (hb : ∀ y', BddAbove {v | ∃ c, enFeasible c y' ∧ v = ∑ i, lam i * U i (c i)})
    {DW : (H → ℝ) →L[ℝ] ℝ} (hW : HasFDerivAt (en_plannerValue lam U) DW y) (i : I) (h : H) :
    DW (Pi.single h 1) = lam i * DU i (Pi.single h 1) := by
  have := Fintype.ofFinite H
  classical
  set w : I → H → ℝ := fun k => if k = i then Pi.single h 1 else 0 with hw
  have hmin : IsLocalMin (fun t : ℝ => en_plannerValue lam U (y + t • Pi.single h 1) -
      ∑ k, lam k * U k (c k + t • w k)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero, en_plannerValue_eq hopt, sub_self, sub_nonneg]
    refine en_plannerValue_ge (hb _) fun h' => ?_
    have := hopt.1 h'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have e : ∑ k, w k h' = (Pi.single h 1 : H → ℝ) h' := by
      simp [hw, apply_ite (fun f : H → ℝ => f h')]
    rw [e]
    linarith
  have hd : HasDerivAt (fun t : ℝ => en_plannerValue lam U (y + t • Pi.single h 1) -
      ∑ k, lam k * U k (c k + t • w k)) (DW (Pi.single h 1) - ∑ k, lam k * DU k (w k)) 0 :=
    (en_line_deriv hW _).sub
      (HasDerivAt.fun_sum fun k _ => (en_line_deriv (hU k) (w k)).const_mul (lam k))
  have h0 := hmin.hasDerivAt_eq_zero hd
  simp only [hw, apply_ite (DU _), map_zero, mul_ite, mul_zero] at h0
  rw [Finset.sum_ite_eq' Finset.univ i] at h0
  simp only [Finset.mem_univ, ↓reduceIte] at h0
  linarith

/-- AKMM, (16.3), p. 470: the planner equalises every agent's marginal rate of substitution with
the planner's, `(∂Uᵢ/∂cᵢ(h′))/(∂Uᵢ/∂cᵢ(h)) = (∂U_λ/∂y(h′))/(∂U_λ/∂y(h))`. -/
theorem eq_16_3 {lam MUh MUh' DWh DWh' : ℝ} (hlam : lam ≠ 0)
    (h1 : DWh = lam * MUh) (h2 : DWh' = lam * MUh') : MUh' / MUh = DWh' / DWh := by
  rw [h1, h2, mul_div_mul_left _ _ hlam]

/-- AKMM, p. 470: the Arrow–Debreu budget set `{c : Σ p⁰c ≤ Σ p⁰yᵢ}`. -/
def enBudgetAD (p yi : H → ℝ) : Set (H → ℝ) := {c | ∑ h, p h * c h ≤ ∑ h, p h * yi h}

/-- AKMM, (16.4), p. 471: at an optimum on the Arrow–Debreu budget set, with positive prices,
`(∂Uᵢ/∂cᵢ(h))/p⁰(h)` is the same for all `h` (moving value between two histories). -/
theorem eq_16_4_pair [DecidableEq H] {p yi ci : H → ℝ} {U : (H → ℝ) → ℝ}
    {DU : (H → ℝ) →L[ℝ] ℝ} (hp : ∀ h, 0 < p h) (hci : ci ∈ enBudgetAD p yi)
    (hopt : ∀ c ∈ enBudgetAD p yi, U c ≤ U ci) (hU : HasFDerivAt U DU ci) (h h' : H) :
    DU (Pi.single h 1) / p h = DU (Pi.single h' 1) / p h' := by
  set v : H → ℝ := (1 / p h) • Pi.single h 1 - (1 / p h') • Pi.single h' 1 with hv
  have hpv : ∑ k, p k * v k = 0 := by
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    field_simp [(hp h).ne', (hp h').ne']
    ring
  have hmax : IsLocalMax (fun t : ℝ => U (ci + t • v)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_smul, add_zero]
    refine hopt _ ?_
    have := hci
    simp only [enBudgetAD, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib] at this ⊢
    have e : ∑ k, p k * (t * v k) = t * ∑ k, p k * v k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hpv, mul_zero, add_zero]
    exact this
  have h0 := hmax.hasDerivAt_eq_zero (en_line_deriv hU v)
  simp only [hv, map_sub, map_smul, smul_eq_mul] at h0
  rw [div_eq_inv_mul, div_eq_inv_mul]
  simp only [one_div] at h0
  linarith

/-- AKMM, (16.4), p. 471: `∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)` for a multiplier `αᵢ` independent of `h`. -/
theorem eq_16_4 [DecidableEq H] [Nonempty H] {p yi ci : H → ℝ} {U : (H → ℝ) → ℝ}
    {DU : (H → ℝ) →L[ℝ] ℝ} (hp : ∀ h, 0 < p h) (hci : ci ∈ enBudgetAD p yi)
    (hopt : ∀ c ∈ enBudgetAD p yi, U c ≤ U ci) (hU : HasFDerivAt U DU ci) :
    ∃ α : ℝ, ∀ h, DU (Pi.single h 1) = α * p h := by
  obtain ⟨h₀⟩ := ‹Nonempty H›
  refine ⟨DU (Pi.single h₀ 1) / p h₀, fun h => ?_⟩
  rw [← eq_16_4_pair hp hci hopt hU h h₀]
  field_simp [(hp h).ne']

omit [Fintype H] in
/-- AKMM, p. 471: when marginal utility is positive (the budget constraint binds) the multiplier
is strictly positive, `αᵢ > 0`. -/
theorem eq_16_4_pos {p MU : H → ℝ} {α : ℝ} (hp : ∀ h, 0 < p h) (h : H) (hMU : 0 < MU h)
    (hα : ∀ h, MU h = α * p h) : 0 < α := by
  have := hα h
  rw [this] at hMU
  exact pos_of_mul_pos_left hMU (hp h).le

omit [Fintype H] in
/-- AKMM, (16.5), p. 471: the agent's marginal rate of substitution equals the price ratio,
`(∂Uᵢ/∂cᵢ(h′))/(∂Uᵢ/∂cᵢ(h)) = p⁰(h′)/p⁰(h)`. -/
theorem eq_16_5 {p MU : H → ℝ} {α : ℝ} (hα0 : α ≠ 0) (hα : ∀ h, MU h = α * p h) (h h' : H) :
    MU h' / MU h = p h' / p h := by
  rw [hα, hα, mul_div_mul_left _ _ hα0]

omit [Fintype I] [Fintype H] in
/-- AKMM, (16.6)–(16.7), p. 471: with the weights `λᵢ = 1/αᵢ` the equilibrium conditions
`∂Uᵢ/∂cᵢ(h) = αᵢp⁰(h)` are the planner's conditions with `μ = p⁰`. -/
theorem en_weights_match {MU : I → H → ℝ} {α : I → ℝ} {p : H → ℝ} (hα0 : ∀ i, α i ≠ 0)
    (hα : ∀ i h, MU i h = α i * p h) : ∀ i h, 1 / α i * MU i h = p h := by
  intro i h
  rw [hα, ← mul_assoc, one_div_mul_cancel (hα0 i), one_mul]

/-- The gradient inequality for a concave differentiable function, `U(x) ≤ U(c) + DU(x − c)`. -/
theorem en_concave_le_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ℝ} (hU : ConcaveOn ℝ Set.univ U) {DU : E →L[ℝ] ℝ} {c : E}
    (hD : HasFDerivAt U DU c) (x : E) : U x ≤ U c + DU (x - c) := by
  have hs := (en_line_deriv hD (x - c)).tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      U x - U c ≤ t⁻¹ • (U (c + (0 + t) • (x - c)) - U (c + (0 : ℝ) • (x - c))) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hcv := hU.2 (Set.mem_univ c) (Set.mem_univ x) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    have hpt : (1 - t) • c + t • x = c + t • (x - c) := by module
    rw [hpt, smul_eq_mul, smul_eq_mul] at hcv
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    linarith
  have := ge_of_tendsto hs hev
  linarith

/-- **First Welfare Theorem** (AKMM, pp. 471–472). In an Arrow–Debreu equilibrium with concave,
differentiable utilities, first-order conditions `∂Uᵢ/∂cᵢ = αᵢp⁰` with `αᵢ > 0`, nonnegative
prices and market clearing, the equilibrium allocation solves the planner problem with weights
`λᵢ = 1/αᵢ`. -/
theorem en_fwt_planner {U : I → (H → ℝ) → ℝ} {DU : I → (H → ℝ) →L[ℝ] ℝ} {c : I → H → ℝ}
    {y : H → ℝ} {p : H → ℝ} {α : I → ℝ} (hconc : ∀ i, ConcaveOn ℝ Set.univ (U i))
    (hU : ∀ i, HasFDerivAt (U i) (DU i) (c i)) (hα0 : ∀ i, 0 < α i)
    (hα : ∀ i v, DU i v = α i * ∑ h, p h * v h) (hp : ∀ h, 0 ≤ p h)
    (hclear : ∀ h, ∑ i, c i h = y h) :
    enPlannerOpt (fun i => 1 / α i) U y c := by
  refine ⟨fun h => (hclear h).le, fun c' hc' => ?_⟩
  have hi : ∀ i, 1 / α i * U i (c' i) ≤ 1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h) :=
    fun i => by
      have := en_concave_le_fderiv (hconc i) (hU i) (c' i)
      rw [hα i] at this
      have ha := hα0 i
      have : 1 / α i * U i (c' i) ≤ 1 / α i * (U i (c i) + α i * ∑ h, p h * (c' i - c i) h) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      rw [mul_add, ← mul_assoc, one_div_mul_cancel ha.ne', one_mul] at this
      simpa using this
  have hsum : ∑ i, ∑ h, p h * (c' i h - c i h) ≤ 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_nonpos fun h _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hclear h]
    exact mul_nonpos_of_nonneg_of_nonpos (hp h) (by linarith [hc' h])
  calc ∑ i, 1 / α i * U i (c' i)
      ≤ ∑ i, (1 / α i * U i (c i) + ∑ h, p h * (c' i h - c i h)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = ∑ i, 1 / α i * U i (c i) + ∑ i, ∑ h, p h * (c' i h - c i h) := Finset.sum_add_distrib
    _ ≤ ∑ i, 1 / α i * U i (c i) := by linarith

omit [Fintype H] in
/-- AKMM, p. 471: a solution of the planner problem with positive weights is Pareto optimal: no
feasible allocation makes every agent at least as well off and one strictly better off. -/
theorem en_fwt_pareto {lam : I → ℝ} (hlam : ∀ i, 0 < lam i) {U : I → (H → ℝ) → ℝ}
    {y : H → ℝ} {c : I → H → ℝ} (hopt : enPlannerOpt lam U y c) :
    ¬ ∃ c', enFeasible c' y ∧ (∀ i, U i (c i) ≤ U i (c' i)) ∧ ∃ i, U i (c i) < U i (c' i) := by
  rintro ⟨c', hc', hle, i, hlt⟩
  have h1 := hopt.2 c' hc'
  have h2 : ∑ k, lam k * U k (c k) < ∑ k, lam k * U k (c' k) :=
    Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hlam k).le)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt (hlam i)⟩
  linarith

end AKMM.AssetPrices
