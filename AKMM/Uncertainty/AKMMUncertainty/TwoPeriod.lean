/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Finite

/-!
# The two-period stochastic growth model

AKMM, §7.3.1, (7.7)–(7.9), pp. 196–198. Date-1 TFP `A₁(ω₁)` takes finitely many values with
probabilities `π₁(ω₁)`. Given `K₁`, the constraints (7.8)–(7.9) bind:
`C₀ = K₀^α + (1 − δ)K₀ − K₁` and `C₁(ω₁) = A₁(ω₁)K₁^α + (1 − δ)K₁` (`tp_C0`, `tp_C1`), and the
planner maximises `U = u(C₀) + β Σ π₁(ω₁)u(C₁(ω₁))` (7.7) (`tp_U`) over the feasible `K₁`
(`tp_Feasible`, `tp_Optimal`): the choice is the contingent plan `{C₁(ω₁)}`.

* The Lagrangian first-order conditions `u′(C₀) = λ₀`,
  `λ₀ = Σ λ₁(ω₁)(αA₁(ω₁)K₁^{α−1} + 1 − δ)`, `βπ₁(ω₁)u′(C₁(ω₁)) = λ₁(ω₁)` give the stochastic Euler
  equation `u′(C₀) = β Σ π₁(ω₁)u′(C₁(ω₁))(αA₁(ω₁)K₁^{α−1} + 1 − δ)` (`two_period_lagrangian`).
* The stochastic Euler equation holds at every interior optimum (`two_period_euler`), proved
  from optimality by differentiating `U` in `K₁`.
-/

namespace AKMM.Uncertainty

open Real Filter Topology

variable {S : Type*} [Fintype S]

/-- AKMM, (7.8), p. 197: `C₀ = K₀^α + (1 − δ)K₀ − K₁`. -/
noncomputable def tp_C0 (α δ K0 K1 : ℝ) : ℝ := K0 ^ α + (1 - δ) * K0 - K1

/-- AKMM, (7.9), p. 197: `C₁(ω₁) = A₁(ω₁)K₁^α + (1 − δ)K₁`. -/
noncomputable def tp_C1 (α δ : ℝ) (A1 : S → ℝ) (K1 : ℝ) (ω : S) : ℝ :=
  A1 ω * K1 ^ α + (1 - δ) * K1

/-- AKMM, (7.7), p. 196: `U = u(C₀) + β Σ π₁(ω₁)u(C₁(ω₁))` as a function of `K₁`. -/
noncomputable def tp_U (u : ℝ → ℝ) (β α δ K0 : ℝ) (p A1 : S → ℝ) (K1 : ℝ) : ℝ :=
  u (tp_C0 α δ K0 K1) + β * ∑ ω, p ω * u (tp_C1 α δ A1 K1 ω)

/-- Feasibility: `K₁ ≥ 0` and positive consumption at both dates. -/
def tp_Feasible (α δ K0 : ℝ) (A1 : S → ℝ) (K1 : ℝ) : Prop :=
  0 ≤ K1 ∧ 0 < tp_C0 α δ K0 K1 ∧ ∀ ω, 0 < tp_C1 α δ A1 K1 ω

/-- AKMM, p. 197: the planner's problem, maximise (7.7) subject to (7.8)–(7.9). -/
def tp_Optimal (u : ℝ → ℝ) (β α δ K0 : ℝ) (p A1 : S → ℝ) (K1 : ℝ) : Prop :=
  tp_Feasible α δ K0 A1 K1 ∧
    ∀ K, tp_Feasible α δ K0 A1 K → tp_U u β α δ K0 p A1 K ≤ tp_U u β α δ K0 p A1 K1

omit [Fintype S] in
/-- **AKMM, pp. 197–198: the stochastic consumption Euler equation from the Lagrangian.** The
first-order conditions for `C₀`, `K₁` and each `C₁(ω₁)` imply
`u′(C₀) = β Σ π₁(ω₁)u′(C₁(ω₁))(αA₁(ω₁)K₁^{α−1} + 1 − δ)`. -/
theorem two_period_lagrangian [Fintype S] {du0 β α δ K1 lam0 : ℝ} {p A1 du1 lam1 : S → ℝ}
    (hC0 : du0 = lam0) (hK1 : lam0 = ∑ ω, lam1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ))
    (hC1 : ∀ ω, β * p ω * du1 ω = lam1 ω) :
    du0 = β * ∑ ω, p ω * du1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ) := by
  rw [hC0, hK1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by rw [← hC1 ω]; ring

/-- **AKMM, p. 198: the stochastic Euler equation holds at the optimum.** If `K₁ > 0` solves the
planner's problem and `u` is differentiable at `C₀` and at each `C₁(ω₁)`, then
`u′(C₀) = β Σ π₁(ω₁)u′(C₁(ω₁))(αA₁(ω₁)K₁^{α−1} + 1 − δ)`. -/
theorem two_period_euler {u : ℝ → ℝ} {β α δ K0 K1 du0 : ℝ} {p A1 du1 : S → ℝ}
    (hopt : tp_Optimal u β α δ K0 p A1 K1) (hK1 : 0 < K1)
    (hd0 : HasDerivAt u du0 (tp_C0 α δ K0 K1))
    (hd1 : ∀ ω, HasDerivAt u (du1 ω) (tp_C1 α δ A1 K1 ω)) :
    du0 = β * ∑ ω, p ω * du1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ) := by
  obtain ⟨⟨-, hc0, hc1⟩, hmax⟩ := hopt
  -- derivatives of the constraints in `K₁`
  have hpow : HasDerivAt (fun K : ℝ => K ^ α) (α * K1 ^ (α - 1)) K1 :=
    hasDerivAt_rpow_const (Or.inl hK1.ne')
  have hdC0 : HasDerivAt (fun K => tp_C0 α δ K0 K) (-1) K1 := by
    have := (hasDerivAt_id' K1).const_sub (K0 ^ α + (1 - δ) * K0)
    exact this
  have hdC1 : ∀ ω, HasDerivAt (fun K => tp_C1 α δ A1 K ω)
      (α * A1 ω * K1 ^ (α - 1) + 1 - δ) K1 := fun ω => by
    have := (hpow.const_mul (A1 ω)).add ((hasDerivAt_id' K1).const_mul (1 - δ))
    exact this.congr_deriv (by ring)
  have hdU : HasDerivAt (fun K => tp_U u β α δ K0 p A1 K)
      (du0 * (-1) + β * ∑ ω, p ω * (du1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ))) K1 := by
    unfold tp_U
    refine (hd0.comp K1 hdC0).add (HasDerivAt.const_mul β ?_)
    exact HasDerivAt.fun_sum fun ω _ => ((hd1 ω).comp K1 (hdC1 ω)).const_mul (p ω)
  -- nearby `K` are feasible, so `K₁` is a local maximum
  have hloc : IsLocalMax (fun K => tp_U u β α δ K0 p A1 K) K1 := by
    have hcont0 : ContinuousAt (fun K => tp_C0 α δ K0 K) K1 := hdC0.continuousAt
    have hev0 := continuousAt_const.eventually_lt hcont0 hc0
    have hev1 : ∀ᶠ K in 𝓝 K1, ∀ ω, 0 < tp_C1 α δ A1 K ω :=
      eventually_all.2 fun ω => continuousAt_const.eventually_lt (hdC1 ω).continuousAt (hc1 ω)
    have hevK : ∀ᶠ K in 𝓝 K1, 0 ≤ K := (lt_mem_nhds hK1).mono fun K hK => hK.le
    filter_upwards [hev0, hev1, hevK] with K h0 h1 hK
    exact hmax K ⟨hK, h0, h1⟩
  have h := hloc.hasDerivAt_eq_zero hdU
  rw [Finset.mul_sum] at h ⊢
  have e : ∑ ω, β * (p ω * (du1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ))) =
      ∑ ω, β * (p ω * du1 ω * (α * A1 ω * K1 ^ (α - 1) + 1 - δ)) :=
    Finset.sum_congr rfl fun ω _ => by ring
  linarith

end AKMM.Uncertainty
