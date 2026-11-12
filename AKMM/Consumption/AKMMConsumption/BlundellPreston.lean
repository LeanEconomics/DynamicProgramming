/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Basic.Real.Basic

/-!
# Blundell and Preston: inequality in consumption and income

AKMM, §11.3.2, box "Using the PIH to learn about the nature of the rise in inequality",
(11.28), p. 300.

Within a cohort, income and consumption evolve as
`yₜ₊₁ = yₜ + uₜ₊₁ − uₜ + vₜ₊₁` and `cₜ₊₁ = cₜ + kuₜ₊₁ + vₜ₊₁` with `k = r/(1 + r)` ((11.26)
and (11.27)). The cross-sectional covariance is any symmetric bilinear form `B` on the space `V`
of random variables (the population covariance on `L²`, or a finite cross-section's covariance),
and the shocks of date `t + 1` are orthogonal to everything dated `t` and to each other.

* The exact laws of motion: `ΔVar(c) = k²Var(uₜ₊₁) + Var(vₜ₊₁)` (`bp_var_cons`) and
  `ΔCov(c, y) = k(Var(uₜ₊₁) − Var(uₜ)) + Var(vₜ₊₁)` (`bp_cov_cons_income`), using
  `Cov(cₜ, uₜ) = kVar(uₜ)` (`bp_cov_cons_trans`).
* **(11.28)** at `r = 0` (`k = 0`), `ΔVar(c) = ΔCov(c, y) = Var(v)` exactly (`eq_11_28`); with a
  stationary transitory variance, `ΔCov(c, y) = Var(v)` for every `r`
  (`bp_cov_stationary`).

Departure: the book's "`r ≃ 0`, … `≃ Var(v)`" becomes the exact statement at `r = 0`, together
with the exact error terms for `r ≠ 0`.
-/

namespace AKMM.Consumption

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- AKMM, p. 300: `Cov(cₜ, uₜ) = kVar(uₜ)` when `cₜ = cₜ₋₁ + kuₜ + vₜ` and `uₜ` is orthogonal
to `cₜ₋₁` and `vₜ`. -/
theorem bp_cov_cons_trans (B : LinearMap.BilinForm ℝ V) {k : ℝ}
    {c₀ c u v : V} (hc : c = c₀ + k • u + v) (h1 : B c₀ u = 0) (h2 : B v u = 0) :
    B c u = k * B u u := by
  subst hc
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- AKMM, p. 300: the cross-sectional variance of consumption under (11.27),
`Var(cₜ₊₁) = Var(cₜ) + k²Var(uₜ₊₁) + Var(vₜ₊₁)`. -/
theorem bp_var_cons (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c c' u' v' : V} (hc : c' = c + k • u' + v') (h1 : B c u' = 0) (h2 : B c v' = 0)
    (h3 : B u' v' = 0) : B c' c' - B c c = k ^ 2 * B u' u' + B v' v' := by
  subst hc
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hB u' c, hB v' c, hB v' u', h1, h2, h3]
  ring

/-- AKMM, p. 300: the cross-sectional covariance of consumption and income under (11.26) and
(11.27): `ΔCov(c, y) = k(Var(uₜ₊₁) − Var(uₜ)) + Var(vₜ₊₁)`, when the date-`t + 1` shocks are
orthogonal to `cₜ, yₜ, uₜ` and to each other, and `Cov(cₜ, uₜ) = kVar(uₜ)`. -/
theorem bp_cov_cons_income (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c y u c' y' u' v' : V} (hc : c' = c + k • u' + v') (hy : y' = y + u' - u + v')
    (hcu : B c u = k * B u u) (h1 : B c u' = 0) (h2 : B c v' = 0) (h3 : B y u' = 0)
    (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0) :
    B c' y' - B c y = k * (B u' u' - B u u) + B v' v' := by
  subst hc hy
  simp only [map_add, map_sub, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hB u' y, hB u' u, hB v' y, hB v' u, hB v' u', hcu, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- **AKMM, (11.28), p. 300 (Blundell and Preston 1998).** At `r = 0` the PIH laws of motion
(11.26)–(11.27) (`cₜ₊₁ = cₜ + vₜ₊₁`, since `k = r/(1 + r) = 0`) give
`ΔVar(c) = ΔCov(c, y) = Var(v)` exactly. -/
theorem eq_11_28 (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {c y u c' y' u' v' : V} (hc : c' = c + (0 / (1 + 0) : ℝ) • u' + v')
    (hy : y' = y + u' - u + v') (hcu : B c u = 0) (h1 : B c u' = 0) (h2 : B c v' = 0)
    (h3 : B y u' = 0) (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0) :
    B c' c' - B c c = B v' v' ∧ B c' y' - B c y = B v' v' := by
  have hk : (0 / (1 + 0) : ℝ) = 0 := by norm_num
  rw [hk] at hc
  refine ⟨by simpa using bp_var_cons B hB hc h1 h2 h7, ?_⟩
  have := bp_cov_cons_income B hB hc hy (by rw [hcu, zero_mul]) h1 h2 h3 h4 h5 h6 h7
  simpa using this

/-- AKMM, p. 300: if the transitory variance is the same at `t` and `t + 1`, the covariance
identity `ΔCov(c, y) = Var(v)` holds for every `r`, and the variance identity holds up to
`k²Var(u)`. -/
theorem bp_cov_stationary (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {k : ℝ}
    {c y u c' y' u' v' : V} (hc : c' = c + k • u' + v') (hy : y' = y + u' - u + v')
    (hcu : B c u = k * B u u) (h1 : B c u' = 0) (h2 : B c v' = 0) (h3 : B y u' = 0)
    (h4 : B y v' = 0) (h5 : B u u' = 0) (h6 : B u v' = 0) (h7 : B u' v' = 0)
    (hstat : B u' u' = B u u) :
    B c' y' - B c y = B v' v' ∧ B c' c' - B c c = k ^ 2 * B u u + B v' v' := by
  refine ⟨?_, by rw [bp_var_cons B hB hc h1 h2 h7, hstat]⟩
  rw [bp_cov_cons_income B hB hc hy hcu h1 h2 h3 h4 h5 h6 h7, hstat]
  ring

end AKMM.Consumption
