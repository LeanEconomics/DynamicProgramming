/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Consumption/portfolio choice: the budget constraint (8.17) and the Euler equations

Miao, §8.4, pp. 259–262. There are `J` stocks (`Fin J`) with prices `P_j`, dividends `D_j` and
holdings `ψ_j`, and a riskless bond `B` with gross return `R^f`.

* `od_portfolio_bond_share` (p. 260): with `π_j = P_jψ_j/(W − C)`, the budget constraint gives
  `B/(W − C) = 1 − ∑ π_j`.
* `eq_8_17` (p. 260): `W_{t+1} = ∑ (P_{j,t+1} + D_{j,t+1})ψ_j + R^f B = ∑ R_j P_jψ_j + R^f B
  = R_w(W − C)`, with `R_j = (P_{j,t+1} + D_{j,t+1})/P_j` and
  `R_w = R^f + ∑ π_j(R_j − R^f)` (`od_Rw`).
* `od_portfolio_foc` (p. 261): the first-order conditions for `C` and `π_j` at an unconstrained
  maximum of `u(C) + βE V_{t+1}(R_w(W − C))`, for differentiable `u`, `V_{t+1}`.
* `od_portfolio_envelope` (p. 261): the envelope condition
  `V_t′(W) = βE[V_{t+1}′(R_w(W − C))R_w]` when `V_t` is differentiable (Benveniste–Scheinkman).
* `od_portfolio_euler` (p. 261): combining these, `u′(C_t) = βE[u′(C_{t+1})R_w] = V_t′(W_t)`,
  `0 = E[u′(C_{t+1})(R_j − R^f)]`, and the Euler equations
  `E[βu′(C_{t+1})/u′(C_t) R^f] = 1`, `E[βu′(C_{t+1})/u′(C_t) R_j] = 1`.

The conditional expectation `E_t` is the integral over the next-period states `ω` under a
probability measure `μ` (the conditional law given the date-`t` state, which the book
suppresses); `R^f = R^f_{t+1}` is known at `t`. The first-order and envelope conditions are
proved for finitely many states, where differentiating under `E` is differentiating a finite sum;
the Euler step holds for any `μ`. The "combining" step uses the envelope identity
`V′_{t+1}(W_{t+1}) = u′(C_{t+1})` at date `t + 1` (the date-`t` identity `u′(C_t) = V_t′(W_t)`
moved forward one period), as in the book. Dividing the `π_j` condition by `W − C` needs
`W ≠ C`, and the Euler equations need `u′(C_t) ≠ 0`; the book leaves both implicit. The book's
wealth `W_t = ∑ (P_{jt} + D_{jt})ψ_{j,t−1} + R_t B_{t−1}` has `R_t` for `R^f_t`.
-/

namespace Miao.Applications

open MeasureTheory

/-- The portfolio return `R_w = R^f + ∑ π_j(R_j − R^f)` in state `ω`. -/
def od_Rw {J : ℕ} {Ω : Type*} (Rf : ℝ) (R : Fin J → Ω → ℝ) (pi : Fin J → ℝ) (ω : Ω) : ℝ :=
  Rf + ∑ j, pi j * (R j ω - Rf)

/-- Miao, p. 260: from the budget constraint `C + ∑ P_jψ_j + B = W` and `π_j = P_jψ_j/(W − C)`,
`B/(W − C) = 1 − ∑ π_j`. -/
theorem od_portfolio_bond_share {J : ℕ} (P ψ : Fin J → ℝ) {B C W : ℝ} (hWC : W - C ≠ 0)
    (hbudget : C + ∑ j, P j * ψ j + B = W) :
    B / (W - C) = 1 - ∑ j, P j * ψ j / (W - C) := by
  rw [← Finset.sum_div, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hWC]
  linarith

/-- **(8.17)** (Miao, p. 260): the budget constraint in terms of returns. With
`R_j = (P_{j,t+1} + D_{j,t+1})/P_j` and `π_j = P_jψ_j/(W − C)`, `B = (1 − ∑ π_j)(W − C)`,
`W_{t+1} = ∑ (P_{j,t+1} + D_{j,t+1})ψ_j + R^f B = ∑ R_jP_jψ_j + R^f B = R_w(W − C)`. -/
theorem eq_8_17 {J : ℕ} (P ψ P' D' : Fin J → ℝ) (hP : ∀ j, P j ≠ 0) {B C W Rf : ℝ}
    (hWC : W - C ≠ 0) (hbudget : C + ∑ j, P j * ψ j + B = W) :
    ∑ j, (P' j + D' j) * ψ j + Rf * B = ∑ j, (P' j + D' j) / P j * (P j * ψ j) + Rf * B ∧
      ∑ j, (P' j + D' j) / P j * (P j * ψ j) + Rf * B =
        od_Rw (Ω := Unit) Rf (fun j _ => (P' j + D' j) / P j) (fun j => P j * ψ j / (W - C)) ()
          * (W - C) := by
  refine ⟨?_, ?_⟩
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hP j]
  · have hB : B = W - C - ∑ j, P j * ψ j := by linarith
    unfold od_Rw
    rw [add_mul, Finset.sum_mul, hB]
    have : ∀ j, P j * ψ j / (W - C) * ((P' j + D' j) / P j - Rf) * (W - C) =
        (P' j + D' j) / P j * (P j * ψ j) - Rf * (P j * ψ j) := fun j => by
      have := hP j
      field_simp
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

/-- The objective `u(C) + β E V_{t+1}(R_w(W − C))` of the Bellman equation (p. 261). -/
noncomputable def od_portObj {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u V₁ : ℝ → ℝ) (β Rf : ℝ) (R : Fin J → Ω → ℝ) (W C : ℝ) (pi : Fin J → ℝ) : ℝ :=
  u C + β * ∫ ω, V₁ (od_Rw Rf R pi ω * (W - C)) ∂μ

/-- Differentiating `x ↦ ∫ V(a ω + x b ω) dμ` over finitely many states. -/
theorem od_hasDerivAt_integral_fintype {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {V V' : ℝ → ℝ}
    {a b : Ω → ℝ} (hV : ∀ ω, HasDerivAt V (V' (a ω)) (a ω)) :
    HasDerivAt (fun x => ∫ ω, V (a ω + x * b ω) ∂μ) (∫ ω, V' (a ω) * b ω ∂μ) 0 := by
  have := Fintype.ofFinite Ω
  have hfun : (fun x => ∫ ω, V (a ω + x * b ω) ∂μ) =
      fun x => ∑ ω, μ.real {ω} • V (a ω + x * b ω) := by
    funext x; exact integral_fintype Integrable.of_finite
  rw [hfun, integral_fintype Integrable.of_finite]
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have hin : HasDerivAt (fun x => a ω + x * b ω) (b ω) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (b ω)).const_add (a ω)
  have h := HasDerivAt.comp (0 : ℝ)
    (by simpa using hV ω : HasDerivAt V (V' (a ω)) (a ω + 0 * b ω)) hin
  exact h.const_smul (μ.real {ω})

/-- Miao, p. 261, the first-order conditions. If `(C, π)` maximises
`u(C) + βE V_{t+1}(R_w(W − C))` without binding constraints (finitely many states), `u` and
`V_{t+1}` are differentiable and `β ≠ 0`, then `u′(C) = βE[V′_{t+1}(R_w(W − C))R_w]` and
`0 = E[V′_{t+1}(R_w(W − C))(W − C)(R_j − R^f)]` for every `j`. -/
theorem od_portfolio_foc {J : ℕ} {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {u V₁ V₁' : ℝ → ℝ}
    {du β Rf W C : ℝ} {R : Fin J → Ω → ℝ} {pi : Fin J → ℝ} (hβ : β ≠ 0) (hu : HasDerivAt u du C)
    (hV : ∀ ω, HasDerivAt V₁ (V₁' (od_Rw Rf R pi ω * (W - C))) (od_Rw Rf R pi ω * (W - C)))
    (hmax : ∀ C₁ pi₁, od_portObj μ u V₁ β Rf R W C₁ pi₁ ≤ od_portObj μ u V₁ β Rf R W C pi) :
    du = β * ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * od_Rw Rf R pi ω ∂μ ∧
      ∀ j, 0 = ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * (W - C) * (R j ω - Rf) ∂μ := by
  refine ⟨?_, fun j => ?_⟩
  · -- perturb consumption: `C + x`
    have hE := od_hasDerivAt_integral_fintype (μ := μ) (V := V₁) (V' := V₁')
      (a := fun ω => od_Rw Rf R pi ω * (W - C)) (b := fun ω => -od_Rw Rf R pi ω) hV
    have hu' : HasDerivAt (fun x => u (C + x)) du 0 := by
      have := HasDerivAt.comp (0 : ℝ) (by simpa using hu : HasDerivAt u du (C + 0))
        ((hasDerivAt_id (0 : ℝ)).const_add C)
      simpa [Function.comp_def] using this
    have hg := hu'.add (hE.const_mul β)
    have hloc : IsLocalMax (fun x => u (C + x) + β * ∫ ω, V₁ (od_Rw Rf R pi ω * (W - C) +
        x * -od_Rw Rf R pi ω) ∂μ) 0 := Filter.Eventually.of_forall fun x => by
      have h := hmax (C + x) pi
      simp only [od_portObj, add_zero] at h ⊢
      have heq : ∀ ω, od_Rw Rf R pi ω * (W - (C + x)) =
          od_Rw Rf R pi ω * (W - C) + x * -od_Rw Rf R pi ω := fun ω => by ring
      simp only [heq] at h
      simpa using h
    have h0 := hloc.hasDerivAt_eq_zero hg
    have : ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * -od_Rw Rf R pi ω ∂μ =
        -∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * od_Rw Rf R pi ω ∂μ := by
      rw [← integral_neg]; simp only [mul_neg]
    rw [this] at h0
    linarith
  · -- perturb the share of stock `j`: `π + x eⱼ`
    have hE := od_hasDerivAt_integral_fintype (μ := μ) (V := V₁) (V' := V₁')
      (a := fun ω => od_Rw Rf R pi ω * (W - C)) (b := fun ω => (W - C) * (R j ω - Rf)) hV
    have hg := (hasDerivAt_const (0 : ℝ) (u C)).add (hE.const_mul β)
    have hRw : ∀ x ω, od_Rw Rf R (pi + x • (Pi.single j 1 : Fin J → ℝ)) ω * (W - C) =
        od_Rw Rf R pi ω * (W - C) + x * ((W - C) * (R j ω - Rf)) := fun x ω => by
      unfold od_Rw
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      have : ∑ i, x * (Pi.single j (1 : ℝ) : Fin J → ℝ) i * (R i ω - Rf) = x * (R j ω - Rf) := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij; simp [hij]
        · simp
      rw [this]; ring
    have hloc : IsLocalMax (fun x => u C + β * ∫ ω, V₁ (od_Rw Rf R pi ω * (W - C) +
        x * ((W - C) * (R j ω - Rf))) ∂μ) 0 := Filter.Eventually.of_forall fun x => by
      have h := hmax C (pi + x • (Pi.single j 1 : Fin J → ℝ))
      simp only [od_portObj, hRw] at h
      simpa using h
    have h0 := hloc.hasDerivAt_eq_zero hg
    have hint : ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * ((W - C) * (R j ω - Rf)) ∂μ = 0 := by
      have : β * ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * ((W - C) * (R j ω - Rf)) ∂μ = 0 := by
        linarith
      exact (mul_eq_zero.1 this).resolve_left hβ
    rw [← hint]
    congr 1; funext ω; ring

/-- Miao, p. 261, the envelope condition. If `V_t(W₁) ≥ u(C₁) + βE V_{t+1}(R_w(π₁)(W₁ − C₁))` for
all `W₁, C₁, π₁`, with equality at the optimum `(C, π)` for `W`, and `V_t` is differentiable at `W`
(finitely many states), then `V_t′(W) = βE[V′_{t+1}(R_w(W − C))R_w]`. -/
theorem od_portfolio_envelope {J : ℕ} {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {u V₀ V₁ V₁' : ℝ → ℝ}
    {dV β Rf W C : ℝ} {R : Fin J → Ω → ℝ} {pi : Fin J → ℝ} (hV₀ : HasDerivAt V₀ dV W)
    (hV : ∀ ω, HasDerivAt V₁ (V₁' (od_Rw Rf R pi ω * (W - C))) (od_Rw Rf R pi ω * (W - C)))
    (hle : ∀ W₁ C₁ pi₁, od_portObj μ u V₁ β Rf R W₁ C₁ pi₁ ≤ V₀ W₁)
    (heq : V₀ W = od_portObj μ u V₁ β Rf R W C pi) :
    dV = β * ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * od_Rw Rf R pi ω ∂μ := by
  have hE := od_hasDerivAt_integral_fintype (μ := μ) (V := V₁) (V' := V₁')
    (a := fun ω => od_Rw Rf R pi ω * (W - C)) (b := fun ω => od_Rw Rf R pi ω) hV
  have hV₀' : HasDerivAt (fun x => V₀ (W + x)) dV 0 := by
    have := HasDerivAt.comp (0 : ℝ) (by simpa using hV₀ : HasDerivAt V₀ dV (W + 0))
      ((hasDerivAt_id (0 : ℝ)).const_add W)
    simpa [Function.comp_def] using this
  have hg := hV₀'.sub ((hasDerivAt_const (0 : ℝ) (u C)).add (hE.const_mul β))
  have hloc : IsLocalMin (fun x => V₀ (W + x) - (u C + β * ∫ ω, V₁ (od_Rw Rf R pi ω * (W - C) +
      x * od_Rw Rf R pi ω) ∂μ)) 0 := Filter.Eventually.of_forall fun x => by
    have h := hle (W + x) C pi
    have heq' : ∀ ω, od_Rw Rf R pi ω * (W + x - C) =
        od_Rw Rf R pi ω * (W - C) + x * od_Rw Rf R pi ω := fun ω => by ring
    simp only [od_portObj, heq'] at h heq
    simp only [add_zero, zero_mul]
    linarith
  have h0 := hloc.hasDerivAt_eq_zero hg
  linarith

/-- Miao, p. 261, the Euler equations. Suppose the first-order conditions for `C` and `π_j`, the
envelope condition at `t`, and the envelope identity `V′_{t+1}(W_{t+1}) = u′(C_{t+1})` at `t + 1`
hold, `W ≠ C` and `u′(C_t) ≠ 0`. Then `u′(C_t) = βE[u′(C_{t+1})R_w] = V_t′(W_t)`,
`0 = E[u′(C_{t+1})(R_j − R^f)]`, `E[βu′(C_{t+1})/u′(C_t) R^f] = 1` and
`E[βu′(C_{t+1})/u′(C_t) R_j] = 1` for every `j`. -/
theorem od_portfolio_euler {J : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {du' : ℝ → ℝ} {V₁' : ℝ → ℝ} {C' : Ω → ℝ} {dV₀ β Rf W C : ℝ}
    {R : Fin J → Ω → ℝ} {pi : Fin J → ℝ} (hWC : W - C ≠ 0) (hu0 : du' C ≠ 0)
    (hiu : Integrable (fun ω => du' (C' ω)) μ)
    (hiR : ∀ j, Integrable (fun ω => du' (C' ω) * R j ω) μ)
    (hfocC : du' C = β * ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * od_Rw Rf R pi ω ∂μ)
    (hfocπ : ∀ j, 0 = ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * (W - C) * (R j ω - Rf) ∂μ)
    (henv : dV₀ = β * ∫ ω, V₁' (od_Rw Rf R pi ω * (W - C)) * od_Rw Rf R pi ω ∂μ)
    (hnext : ∀ ω, V₁' (od_Rw Rf R pi ω * (W - C)) = du' (C' ω)) :
    du' C = β * ∫ ω, du' (C' ω) * od_Rw Rf R pi ω ∂μ ∧ du' C = dV₀ ∧
      (∀ j, 0 = ∫ ω, du' (C' ω) * (R j ω - Rf) ∂μ) ∧
      ∫ ω, β * du' (C' ω) / du' C * Rf ∂μ = 1 ∧
      ∀ j, ∫ ω, β * du' (C' ω) / du' C * R j ω ∂μ = 1 := by
  simp only [hnext] at hfocC hfocπ henv
  have hiD : ∀ j, Integrable (fun ω => du' (C' ω) * (R j ω - Rf)) μ := fun j => by
    refine ((hiR j).sub (hiu.mul_const Rf)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  have hπ : ∀ j, 0 = ∫ ω, du' (C' ω) * (R j ω - Rf) ∂μ := fun j => by
    have h := hfocπ j
    have : ∫ ω, du' (C' ω) * (W - C) * (R j ω - Rf) ∂μ =
        (W - C) * ∫ ω, du' (C' ω) * (R j ω - Rf) ∂μ := by
      rw [← integral_const_mul]; congr 1; funext ω; ring
    rw [this] at h
    exact ((mul_eq_zero.1 h.symm).resolve_left hWC).symm
  have hRw : ∫ ω, du' (C' ω) * od_Rw Rf R pi ω ∂μ = Rf * ∫ ω, du' (C' ω) ∂μ := by
    have hfun : (fun ω => du' (C' ω) * od_Rw Rf R pi ω) =
        fun ω => Rf * du' (C' ω) + ∑ j, pi j * (du' (C' ω) * (R j ω - Rf)) := by
      funext ω; unfold od_Rw; rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun, integral_add (hiu.const_mul Rf)
      (integrable_finsetSum _ fun j _ => (hiD j).const_mul (pi j)),
      integral_finsetSum _ fun j _ => (hiD j).const_mul (pi j), integral_const_mul]
    simp only [integral_const_mul, ← hπ, mul_zero, Finset.sum_const_zero, add_zero]
  have hC : du' C = β * (Rf * ∫ ω, du' (C' ω) ∂μ) := by rw [hfocC, hRw]
  refine ⟨hfocC, hfocC.trans henv.symm, hπ, ?_, fun j => ?_⟩
  · have : ∫ ω, β * du' (C' ω) / du' C * Rf ∂μ = β * Rf / du' C * ∫ ω, du' (C' ω) ∂μ := by
      rw [← integral_const_mul]
      congr 1; funext ω; ring
    rw [this, div_mul_eq_mul_div, div_eq_one_iff_eq hu0, hC]; ring
  · have hsplit : ∫ ω, du' (C' ω) * R j ω ∂μ =
        Rf * ∫ ω, du' (C' ω) ∂μ + ∫ ω, du' (C' ω) * (R j ω - Rf) ∂μ := by
      rw [← integral_const_mul, ← integral_add (hiu.const_mul Rf) (hiD j)]
      congr 1; funext ω; ring
    have : ∫ ω, β * du' (C' ω) / du' C * R j ω ∂μ =
        β / du' C * ∫ ω, du' (C' ω) * R j ω ∂μ := by
      rw [← integral_const_mul]
      congr 1; funext ω; ring
    rw [this, hsplit, ← hπ j, add_zero, div_mul_eq_mul_div, div_eq_one_iff_eq hu0, hC]

end Miao.Applications
