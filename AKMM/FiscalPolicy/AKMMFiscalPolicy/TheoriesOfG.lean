/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.DistortionaryTaxes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theories of government spending

AKMM, §15.3.5, pp. 454–455.

* Public goods: with utility `u(c, g)` and lump-sum finance, the first best splits resources
  `c + g = Y` so that `u₁(c, g) = u₂(c, g)` (`tg_first_best`).
* Public capital: `f(k, k_g, ℓ) = Ak^αℓ^{1−α}k_g^θ` (`tgF`) is homogeneous of degree `1 + θ`
  (`tg_homogeneous`): constant returns in `(k, ℓ)` (`tg_crs_private`) and increasing returns
  overall when `θ > 0` (`tg_irs`). The law of motion `k_{g,t+1} = i_{g,t} + (1 − δ_g)k_{g,t}` is
  `tgLaw`.
* With non-distortionary finance, the planner's split of a given amount of saving between private
  and public capital equates the net marginal products, `f_k − δ = f_g − δ_g`
  (`tg_net_returns_equal`).

Departures: the last item is stated for the split of next period's capital stocks with a fixed
total (the margin on which the two Euler equations of the planner differ); the full dynamic
planner is not restated.
-/

namespace AKMM.FiscalPolicy

open Real

/-- AKMM, p. 454: "The first best solution … prescribes equating the marginal utility of
private consumption to the marginal utility of public consumption": if `(c, g)` maximises
`u` on `{c + g = Y}` and `u` is differentiable there, `u₁(c, g) = u₂(c, g)`. -/
theorem tg_first_best {u : ℝ → ℝ → ℝ} {c g Y u1 u2 : ℝ} (hcg : c + g = Y)
    (hmax : ∀ c' g', c' + g' = Y → u c' g' ≤ u c g) (hu : DTPartials u c g u1 u2) :
    u1 = u2 := by
  have hd := dt_curve_hasDerivAt (h := fun ε => ε) (g := fun ε => -ε) hu (hasDerivAt_id 0)
    ((hasDerivAt_id 0).neg) rfl (by simp)
  have hloc : IsLocalMax (fun ε => u (c + ε) (g + -ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [add_zero, neg_zero]
      exact hmax _ _ (by linarith)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- Output with public capital `f(k, k_g, ℓ) = Ak^αℓ^{1−α}k_g^θ` (AKMM, p. 455). -/
noncomputable def tgF (A α θ k kg l : ℝ) : ℝ := A * k ^ α * l ^ (1 - α) * kg ^ θ

/-- The law of motion of public capital `k_{g,t+1} = i_{g,t} + (1 − δ_g)k_{g,t}` (AKMM, p. 455). -/
def tgLaw (δg : ℝ) (ig kg : ℕ → ℝ) : Prop := ∀ t, kg (t + 1) = ig t + (1 - δg) * kg t

/-- AKMM, p. 455: `f(λk, λk_g, λℓ) = λ^{1+θ}f(k, k_g, ℓ)` for `λ, k, k_g, ℓ ≥ 0`. -/
theorem tg_homogeneous {A α θ k kg l lam : ℝ} (hlam : 0 ≤ lam) (hk : 0 ≤ k) (hkg : 0 ≤ kg)
    (hl : 0 ≤ l) (hlam0 : 0 < lam) :
    tgF A α θ (lam * k) (lam * kg) (lam * l) = lam ^ (1 + θ) * tgF A α θ k kg l := by
  unfold tgF
  rw [Real.mul_rpow hlam hk, Real.mul_rpow hlam hl, Real.mul_rpow hlam hkg,
    Real.rpow_add hlam0, Real.rpow_one]
  have : lam ^ α * lam ^ (1 - α) = lam := by
    rw [← Real.rpow_add hlam0]
    simp
  linear_combination (A * k ^ α * l ^ (1 - α) * kg ^ θ * lam ^ θ) * this

/-- AKMM, p. 455: constant returns in the private inputs `(k, ℓ)`. -/
theorem tg_crs_private {A α θ k kg l lam : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (hlam0 : 0 < lam) :
    tgF A α θ (lam * k) kg (lam * l) = lam * tgF A α θ k kg l := by
  unfold tgF
  rw [Real.mul_rpow hlam0.le hk, Real.mul_rpow hlam0.le hl]
  have : lam ^ α * lam ^ (1 - α) = lam := by
    rw [← Real.rpow_add hlam0]
    simp
  linear_combination (A * k ^ α * l ^ (1 - α) * kg ^ θ) * this

/-- AKMM, p. 455: "If `θ > 0`, there are increasing returns to scale": scaling all inputs by
`λ > 1` multiplies positive output by more than `λ`. -/
theorem tg_irs {A α θ k kg l lam : ℝ} (hθ : 0 < θ) (hlam : 1 < lam) (hk : 0 ≤ k)
    (hkg : 0 ≤ kg) (hl : 0 ≤ l) (hf : 0 < tgF A α θ k kg l) :
    lam * tgF A α θ k kg l < tgF A α θ (lam * k) (lam * kg) (lam * l) := by
  have hlam0 : 0 < lam := by linarith
  rw [tg_homogeneous hlam0.le hk hkg hl hlam0]
  refine mul_lt_mul_of_pos_right ?_ hf
  calc lam = lam ^ (1 : ℝ) := (Real.rpow_one lam).symm
    _ < lam ^ (1 + θ) := Real.rpow_lt_rpow_of_exponent_lt hlam (by linarith)

/-- AKMM, p. 455: "If revenue can be raised in a non-distortionary way, then it is optimal to
equate the marginal products of private and public capital, net of depreciation": if
`(k', k_g')` maximises next period's resources `f(k', k_g') + (1 − δ)k' + (1 − δ_g)k_g'` among
splits with `k' + k_g'` fixed, and `f` (at the given hours) is differentiable there with partials
`f_k`, `f_g`, then `f_k − δ = f_g − δ_g`. -/
theorem tg_net_returns_equal {f : ℝ → ℝ → ℝ} {k kg S δ δg fk fg : ℝ} (hS : k + kg = S)
    (hmax : ∀ k' kg', k' + kg' = S →
      f k' kg' + (1 - δ) * k' + (1 - δg) * kg' ≤ f k kg + (1 - δ) * k + (1 - δg) * kg)
    (hf : DTPartials f k kg fk fg) :
    fk - δ = fg - δg := by
  have hd := dt_curve_hasDerivAt (h := fun ε => ε) (g := fun ε => -ε) hf (hasDerivAt_id 0)
    ((hasDerivAt_id 0).neg) rfl (by simp)
  have hd2 : HasDerivAt (fun ε => f (k + ε) (kg + -ε) + (1 - δ) * (k + ε) + (1 - δg) * (kg + -ε))
      (fk * 1 + fg * -1 + (1 - δ) * 1 + (1 - δg) * -1) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_add k).const_mul (1 - δ)
    have h2 := ((hasDerivAt_id (0 : ℝ)).neg.const_add kg).const_mul (1 - δg)
    exact (hd.add h1).add h2
  have hloc : IsLocalMax
      (fun ε => f (k + ε) (kg + -ε) + (1 - δ) * (k + ε) + (1 - δg) * (kg + -ε)) 0 :=
    Filter.Eventually.of_forall fun ε => by
      simp only [add_zero, neg_zero]
      exact hmax _ _ (by linarith)
  have := hloc.hasDerivAt_eq_zero hd2
  linarith

end AKMM.FiscalPolicy
