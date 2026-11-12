/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPAssetPricing
import CompleteMarkets.BPLognormal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The excess volatility puzzle: iid growth and a constant price–dividend ratio

AKMM, §16.8, pp. 490–492, (16.31)–(16.32). Growth `G` is iid. In the finite-support version the
growth rate takes the values `G_k` with probabilities `w_k` each period (a Markov chain whose rows
are all `w`), and `a = βE[G^{1−γ}] = Σ_k w_kβG_k^{1−γ}`.

* Every solution of `vᵢ = Σ_k w_kβG_k^{1−γ}(1 + v_k)` is constant in the current state
  (`iid_pd_const`) and, for `a ≠ 1`, equals `a/(1 − a)` (`iid_pd_unique`, `iid_pd_solves`);
  (16.31), the series `Σ_{t≥1} aᵗ = a/(1 − a)` for `0 ≤ a < 1` (`eq_16_31`).
* (16.32): the log return is `rˢ = g + log((1 + v)/v)` (`eq_16_32`), so its variance equals the
  variance of log growth (`iid_return_var`).
* The lognormal case of the book: with `g ~ N(μ_g, σ_g²)`,
  `a = β exp((1 − γ)μ_g + (1 − γ)²σ_g²/2)` and the constant `v = a/(1 − a)` solves
  `v = E[βG^{1−γ}(1 + v)]` (`iid_lognormal_pd`).

Departure: the uniqueness argument is made for finitely many growth states (the book's growth is
lognormal; for it the constant solution is verified). See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Miao.CompleteMarkets MeasureTheory ProbabilityTheory

variable {K : Type} [Fintype K]

/-- AKMM, (16.31), p. 490: with iid growth the right side of
`vᵢ = Σ_k w_kβG_k^{1−γ}(1 + v_k)` does not depend on the current state, so every solution is
constant. -/
theorem iid_pd_const {w b v : K → ℝ} (hv : ∀ i, v i = ∑ k, w k * b k * (1 + v k)) (i j : K) :
    v i = v j := by
  rw [hv i, hv j]

/-- AKMM, p. 490: with `a = Σ_k w_k b_k ≠ 1` (`b_k = βG_k^{1−γ}`) the only solution
is the constant `a/(1 − a)`. -/
theorem iid_pd_unique {w b v : K → ℝ}
    (hv : ∀ i, v i = ∑ k, w k * b k * (1 + v k)) (ha : ∑ k, w k * b k ≠ 1) (i : K) :
    v i = (∑ k, w k * b k) / (1 - ∑ k, w k * b k) := by
  have hc : ∀ k, v k = v i := fun k => iid_pd_const hv k i
  have h := hv i
  simp only [hc] at h
  rw [← Finset.sum_mul] at h
  have h1 : (1 : ℝ) - ∑ k, w k * b k ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [eq_div_iff h1]
  linarith

/-- AKMM, p. 490: the constant `a/(1 − a)` solves the price–dividend equation. -/
theorem iid_pd_solves {w b : K → ℝ} (ha : ∑ k, w k * b k ≠ 1) (i : K) :
    (fun _ : K => (∑ k, w k * b k) / (1 - ∑ k, w k * b k)) i =
      ∑ k, w k * b k * (1 + (∑ k, w k * b k) / (1 - ∑ k, w k * b k)) := by
  have h1 : (1 : ℝ) - ∑ k, w k * b k ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [← Finset.sum_mul]
  field_simp
  ring

/-- AKMM, (16.31), p. 490: by recursive substitution
`v = Eₜ[βG^{1−γ}ₜ₊₁ + β²G^{1−γ}ₜ₊₁G^{1−γ}ₜ₊₂ + ⋯] = Σ_{t≥1} aᵗ`, which is `a/(1 − a)` for
`0 ≤ a < 1`. -/
theorem eq_16_31 {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) : ∑' t : ℕ, a ^ (t + 1) = a / (1 - a) := by
  simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  ring

/-- AKMM, (16.32), p. 490: with a constant ratio `v > 0` the log return is
`rˢ = log(G(1 + v)/v) = g + log((1 + v)/v)`. -/
theorem eq_16_32 {G v : ℝ} (hG : 0 < G) (hv : 0 < v) :
    Real.log (G * ((1 + v) / v)) = Real.log G + Real.log ((1 + v) / v) :=
  Real.log_mul hG.ne' (div_pos (by linarith) hv).ne'

/-- AKMM, p. 490: since the second term of (16.32) is constant, the variance of the stock return
equals the variance of log growth. -/
theorem iid_return_var {w g : K → ℝ} (hw : ∑ k, w k = 1) (c : ℝ) :
    bp_Var w (fun k => g k + c) = bp_Var w g := by
  have hE : bp_E w (fun k => g k + c) = bp_E w g + c := by
    rw [bp_E_add, bp_E_const w hw]
  rw [bp_Var, bp_Var, bp_Cov_eq_dev w hw, bp_Cov_eq_dev w hw, hE]
  congr 1
  funext k
  ring

/-- AKMM, (16.31), p. 490, the lognormal case: with `g ~ N(μ_g, σ_g²)` and
`a = β exp((1 − γ)μ_g + (1 − γ)²σ_g²/2) ≠ 1`, the constant `v = a/(1 − a)` solves
`v = E[βe^{(1−γ)g}(1 + v)]`. -/
theorem iid_lognormal_pd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ}
    {μ : ℝ} {σ2 : NNReal} (hg : HasLaw g (gaussianReal μ σ2) P) (β γ : ℝ)
    (ha : β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) ≠ 1) :
    ∫ ω, β * Real.exp ((1 - γ) * g ω) *
        (1 + β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) /
          (1 - β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2))) ∂P =
      β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) /
        (1 - β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2)) := by
  set a := β * Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) with hadef
  have hm := gaussianReal_const_mul hg (1 - γ)
  have hE : ∫ ω, Real.exp ((1 - γ) * g ω) ∂P =
      Real.exp ((1 - γ) * μ + (1 - γ) ^ 2 * σ2 / 2) := by
    rw [bp_integral_exp_gaussian hm]
    congr 1
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [integral_mul_const, integral_const_mul, hE, ← hadef]
  field_simp
  ring

end AKMM.AssetPrices
