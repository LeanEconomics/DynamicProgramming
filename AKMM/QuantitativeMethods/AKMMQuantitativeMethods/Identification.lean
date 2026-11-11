/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFMoments
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The identification challenge, natural experiments and the recursive form

AKMM, §8.2, p. 219 (the identification challenge); §8.3, p. 220 (natural experiments: an
instrument `z` correlated with `G` but not with `A`); §8.4, (8.5)–(8.6) and (8.8)–(8.9),
pp. 222–224; and §8.7, p. 232 ("any changes in `G/y` are due to fiscal shocks").

The log-linear system (8.5)–(8.6) is
`ŷ = χ/(1+χ)·Ĝ + 1/(1+χ)·Â`, `Ĝ = ŷ + η̂/(1+γ)`. Random vectors are square-integrable maps
`Ω → I → ℝ`, and second moments `E[vw']` are Miao's `var_mom` with the calculus of
`PartialInformation.KFMoments` (`kf_L2`, `kf_app`, `kf_mom_app_left`, `kf_mom_app_right`).

* (8.5)–(8.6) iff (8.8)–(8.9) with `ĝ = Ĝ − ŷ` (`eq_8_8_8_9`), and the solved system expresses
  `(ŷ, Ĝ)` in terms of the structural shocks `(η̂, Â)` through `id_impact` (`id_solution`), so
  `Ĝ` is correlated with `Â` (`id_G_correlated_with_A`): the endogeneity of p. 223.
* **The identification challenge**: with uncorrelated shocks, the least-squares slope of `ŷ` on
  `Ĝ` equals the causal effect `χ/(1+χ)` iff `Var(Â) = 0` (`id_ols_slope`).
* **Natural experiments** (§8.3): an instrument `z` uncorrelated with `Â` and correlated with
  `η̂` recovers it, `Cov(ŷ, z)/Cov(Ĝ, z) = χ/(1+χ)` (`id_iv`).
* **The restriction identifies** (§8.4, p. 223): imposing the coefficient `1` on `ŷ` in (8.6),
  `Var(ĝ) = Var(η̂)/(1+γ)²` and `χ` are functions of the second moments of `(ŷ, Ĝ)`
  (`id_restriction_identifies`); and `ĝ = Ĝ − ŷ` is uncorrelated with `Â`, so movements in
  `G/y` are fiscal shocks (`id_g_exogenous`, §8.7, p. 232).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **(8.8)–(8.9)** (AKMM, pp. 223–224): for `1 + χ ≠ 0` and `1 + γ ≠ 0`, the system
(8.5)–(8.6) holds iff, with `ĝ = Ĝ − ŷ`, `ŷ = χĝ + Â` and `ĝ = η̂/(1+γ)`. -/
theorem eq_8_8_8_9 {χ γ yh Gh Ah eh : ℝ} (hχ : 1 + χ ≠ 0) :
    (yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ∧ Gh = yh + 1 / (1 + γ) * eh) ↔
      (yh = χ * (Gh - yh) + Ah ∧ Gh - yh = 1 / (1 + γ) * eh) := by
  have h1 : yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ↔ yh = χ * (Gh - yh) + Ah := by
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp; linarith
  rw [h1]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, by linarith⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by linarith⟩

/-- AKMM, (8.8)–(8.9): the impact matrix from the structural shocks `(η̂, Â)` to the observables
`(ŷ, Ĝ)`: `ŷ = χη̂/(1+γ) + Â`, `Ĝ = (1+χ)η̂/(1+γ) + Â`. -/
noncomputable def id_impact (γ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![χ / (1 + γ), 1; (1 + χ) / (1 + γ), 1]

/-- AKMM, p. 223: the solution of (8.5)–(8.6). For `1 + χ ≠ 0`, `(ŷ, Ĝ)` solves the system with
shocks `(η̂, Â)` iff `(ŷ, Ĝ) = id_impact γ χ · (η̂, Â)`. -/
theorem id_solution {χ γ yh Gh Ah eh : ℝ} (hχ : 1 + χ ≠ 0) :
    (yh = χ / (1 + χ) * Gh + 1 / (1 + χ) * Ah ∧ Gh = yh + 1 / (1 + γ) * eh) ↔
      ![yh, Gh] = id_impact γ χ *ᵥ ![eh, Ah] := by
  rw [eq_8_8_8_9 hχ]
  have hv : ∀ a b c d : ℝ, ![a, b] = ![c, d] ↔ a = c ∧ b = d := by
    intro a b c d
    constructor
    · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have hm : id_impact γ χ *ᵥ ![eh, Ah] = ![χ / (1 + γ) * eh + Ah, (1 + χ) / (1 + γ) * eh + Ah] := by
    ext i; fin_cases i <;> simp [id_impact, mulVec, dotProduct, Fin.sum_univ_two]
  rw [hm, hv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, h2]; ring
    · have : Gh = yh + 1 / (1 + γ) * eh := by linarith
      rw [this, h1, h2]; ring
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring

/-- Second moments of the observables: `E[(Me)(Me)'] = M E[ee'] M'`. -/
theorem id_mom_obs {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    var_mom μ (kf_app M e) (kf_app M e) = M * var_mom μ e e * Mᵀ := by
  rw [kf_mom_app_left he (kf_L2_app he M), kf_mom_app_right he he]
  rw [Matrix.mul_assoc]

/-- AKMM, p. 223: "`G_t` is correlated with `A_t`": with uncorrelated shocks of variances
`σ²_η, σ²_A`, `Cov(Ĝ, Â) = σ²_A`. -/
theorem id_G_correlated_with_A {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) :
    var_mom μ (kf_app (id_impact γ χ) e) e 1 1 = sA := by
  rw [kf_mom_app_left he he, hD]
  simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The identification challenge** (AKMM, p. 219): with uncorrelated shocks of variances
`σ²_η, σ²_A ≥ 0`, `a = σ²_η/(1+γ)²`, the moments are `Cov(ŷ, Ĝ) = χ(1+χ)a + σ²_A`,
`Var(Ĝ) = (1+χ)²a + σ²_A`; when `Var(Ĝ) > 0` and `1 + χ > 0`, the least-squares slope
`Cov(ŷ, Ĝ)/Var(Ĝ)` equals the causal effect `χ/(1+χ)` iff `σ²_A = 0`. -/
theorem id_ols_slope {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) (hγ : 1 + γ ≠ 0) (hχ : 0 < 1 + χ) :
    let V := var_mom μ (kf_app (id_impact γ χ) e) (kf_app (id_impact γ χ) e)
    V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA ∧
      V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA ∧
      (0 < V 1 1 → (V 0 1 / V 1 1 = χ / (1 + χ) ↔ sA = 0)) := by
  intro V
  have hV : V = id_impact γ χ * !![sη, 0; 0, sA] * (id_impact γ χ)ᵀ := by
    simp only [V]; rw [id_mom_obs he, hD]
  have h01 : V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h11 : V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  refine ⟨h01, h11, fun hpos => ?_⟩
  rw [div_eq_div_iff hpos.ne' hχ.ne', h01, h11]
  constructor
  · intro h
    have : sA * (1 + χ - χ) = 0 := by nlinarith
    simpa using this
  · intro h; rw [h]; ring

/-- **Natural experiments** (AKMM, §8.3, p. 220): an instrument `z` uncorrelated with the TFP
shock (`Cov(Â, z) = 0`) and correlated with the fiscal shock (`Cov(η̂, z) ≠ 0`) identifies the
causal effect: `Cov(ŷ, z)/Cov(Ĝ, z) = χ/(1+χ)`. -/
theorem id_iv {ι : Type*} {e : Ω → Fin 2 → ℝ} {z : Ω → ι → ℝ} (he : kf_L2 μ e)
    (hz : kf_L2 μ z) {γ χ : ℝ} (hγ : 1 + γ ≠ 0) (hχ : 1 + χ ≠ 0) (j : ι)
    (hexog : var_mom μ e z 1 j = 0) (hrel : var_mom μ e z 0 j ≠ 0) :
    var_mom μ (kf_app (id_impact γ χ) e) z 0 j / var_mom μ (kf_app (id_impact γ χ) e) z 1 j =
      χ / (1 + χ) := by
  rw [kf_mom_app_left he hz]
  simp only [id_impact, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, hexog, mul_zero, add_zero]
  field_simp

/-- **The restriction identifies `χ`** (AKMM, §8.4, p. 223): with the coefficient on `ŷ` in
(8.6) restricted to `1` and uncorrelated shocks, the second moments `V` of `(ŷ, Ĝ)` determine
`Var(ĝ) = σ²_η/(1+γ)² = V₁₁ − 2V₀₁ + V₀₀` and, when it is nonzero,
`χ = (V₁₁ − V₀₁)/(V₁₁ − 2V₀₁ + V₀₀) − 1`. -/
theorem id_restriction_identifies {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) (hγ : 1 + γ ≠ 0) :
    let V := var_mom μ (kf_app (id_impact γ χ) e) (kf_app (id_impact γ χ) e)
    V 1 1 - 2 * V 0 1 + V 0 0 = sη / (1 + γ) ^ 2 ∧
      (sη ≠ 0 → χ = (V 1 1 - V 0 1) / (V 1 1 - 2 * V 0 1 + V 0 0) - 1) := by
  intro V
  have hV : V = id_impact γ χ * !![sη, 0; 0, sA] * (id_impact γ χ)ᵀ := by
    simp only [V]; rw [id_mom_obs he, hD]
  have h00 : V 0 0 = χ ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h01 : V 0 1 = χ * (1 + χ) * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have h11 : V 1 1 = (1 + χ) ^ 2 * (sη / (1 + γ) ^ 2) + sA := by
    rw [hV]; simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]; field_simp
  have hvar : V 1 1 - 2 * V 0 1 + V 0 0 = sη / (1 + γ) ^ 2 := by rw [h00, h01, h11]; ring
  refine ⟨hvar, fun hs => ?_⟩
  rw [hvar, h01, h11]
  have : sη / (1 + γ) ^ 2 ≠ 0 := div_ne_zero hs (pow_ne_zero 2 hγ)
  field_simp
  ring

/-- AKMM, §8.4, p. 224 and §8.7, p. 232: `ĝ = Ĝ − ŷ = η̂/(1+γ)` is uncorrelated with `Â`, "so
we can attribute any movements in `g_t` to fiscal shocks". -/
theorem id_g_exogenous {e : Ω → Fin 2 → ℝ} (he : kf_L2 μ e) {γ χ sη sA : ℝ}
    (hD : var_mom μ e e = !![sη, 0; 0, sA]) :
    var_mom μ (kf_app (!![(-1 : ℝ), 1] * id_impact γ χ) e) e 0 1 = 0 := by
  rw [kf_mom_app_left he he, hD]
  simp [id_impact, Matrix.mul_apply, Fin.sum_univ_two]

end AKMM.QuantitativeMethods
