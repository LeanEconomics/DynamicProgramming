/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.Dynamic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Estimating the Frisch elasticity; optimisation frictions

AKMM, §12.4.2, pp. 347–352.

* **The structural equations** as exact identities: (12.24) `log c = −(1/σ) log λ`
  (`eq_12_24`); (12.25) `log ℓ = const + γ log w + γ log λ` with `const = γ log((1 − τ)/ψ)`
  (`eq_12_25`); its first difference (12.26) (`eq_12_26`); the Euler equation with a borrowing
  multiplier in logs (12.27) (`eq_12_27`); the log-normal identity (12.28),
  `log E[λ′] = E[log λ′] + Var(log λ′)/2`, and `Var(ξ) = Var(log λ′)` for the prediction error
  (`eq_12_28`).
* **The first-order approximation** `log(λ − φ) ≈ log λ − φ/λ`: exactly
  `log(λ − φ) = log λ + log(1 − φ/λ)`, with `−x/(1 − x) ≤ log(1 − x) ≤ −x` and the error at most
  `x²/(1 − x)`, `x = φ/λ`, and the derivative `−1/λ` at `φ = 0` (`fe_log_approx`). (12.29) holds
  exactly with `log(1 − φ/λ)` in place of `−φ/λ` and with the constant of (12.27)
  (`eq_12_29`).
* (12.30)–(12.31) (`eq_12_31`) and the consumption-data equation
  `Δ log ℓ = γΔ log w − γσΔ log c` (`fe_consumption_data`).
* **Optimisation frictions** with GHH utility `log(c − ψℓ^{1+1/γ}/(1 + 1/γ))`, `c = wℓ`
  (12.32): the optimum (12.33) `ℓ* = (w/ψ)^γ`, unique (`eq_12_33`), and the optimal utility
  `−log(1 + γ) − γ log ψ + (1 + γ) log w` (`fr_value`); the decomposition of the utility gain and
  (12.34) (`eq_12_34`); the gain is nonnegative and increasing in `ε > 0` (`fr_gain_pos`,
  `fr_gain_strictMono`); its second-order expansion (12.35) with an explicit cubic error bound
  (`eq_12_35`); the threshold `ε_min = (2Δ/(γ(1 + γ)))^{1/2}` and the hours threshold
  `γε_min = (2Δγ/(1 + γ))^{1/2}` (`fr_threshold`).

Departures: (12.28) is stated for a Gaussian law of `log λ′` (the conditional law of the book);
the conditional expectations of (12.27)–(12.31) are represented by their values.
-/

namespace AKMM.LaborSupply

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

/-! ### The structural equations -/

/-- AKMM, (12.24), p. 347: `c^{−σ} = λ` gives `log c = −(1/σ) log λ` (`σ ≠ 0`). -/
theorem eq_12_24 {σ c lam : ℝ} (hσ : σ ≠ 0) (hc : 0 < c) (h : c ^ (-σ) = lam) :
    Real.log c = -(1 / σ) * Real.log lam := by
  rw [← h, Real.log_rpow hc]
  field_simp

/-- AKMM, (12.25), p. 347: `ψℓ^{1/γ} = λ(1 − τ)w` gives
`log ℓ = γ log((1 − τ)/ψ) + γ log w + γ log λ`. -/
theorem eq_12_25 {ψ γ τ w l lam : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hτ : τ < 1) (hw : 0 < w)
    (hl : 0 < l) (hlam : 0 < lam) (h : ψ * l ^ (1 / γ) = lam * (1 - τ) * w) :
    Real.log l = γ * Real.log ((1 - τ) / ψ) + γ * Real.log w + γ * Real.log lam := by
  have ht : 0 < 1 - τ := by linarith
  have e := congrArg Real.log h
  rw [Real.log_mul hψ.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
    Real.log_mul (by positivity) hw.ne', Real.log_mul hlam.ne' ht.ne'] at e
  rw [Real.log_div ht.ne' hψ.ne']
  have : Real.log l = γ * (1 / γ * Real.log l) := by field_simp
  rw [this]
  have : 1 / γ * Real.log l = Real.log lam + Real.log (1 - τ) + Real.log w - Real.log ψ := by
    linarith
  rw [this]
  ring

/-- AKMM, (12.26), p. 348: first-differencing (12.25) (the constant cancels):
`Δ log ℓ = γΔ log w + γΔ log λ`. -/
theorem eq_12_26 {γ k l₀ l₁ w₀ w₁ m₀ m₁ : ℝ} (h₀ : l₀ = k + γ * w₀ + γ * m₀)
    (h₁ : l₁ = k + γ * w₁ + γ * m₁) : l₁ - l₀ = γ * (w₁ - w₀) + γ * (m₁ - m₀) := by
  rw [h₀, h₁]; ring

/-- AKMM, (12.27), p. 348: the Euler equation with borrowing multiplier `φ`,
`λ − φ = βR·E[λ′]`, in logs: `log(λ − φ) = log(βR) + log E[λ′]`. -/
theorem eq_12_27 {β R lam φ m : ℝ} (hβR : 0 < β * R) (hm : 0 < m) (h : lam - φ = β * R * m) :
    Real.log (lam - φ) = Real.log (β * R) + Real.log m := by
  rw [h, Real.log_mul hβR.ne' hm.ne']

/-- AKMM, (12.28), p. 348: **the log-normal identity**. If `log λ′` is Gaussian with mean `μ`
and variance `v`, then `log E[λ′] = E[log λ′] + Var(log λ′)/2`; and the prediction error
`ξ = log λ′ − E[log λ′]` has `Var(ξ) = Var(log λ′)`. -/
theorem eq_12_28 (μ : ℝ) (v : ℝ≥0) :
    Real.log (∫ x, Real.exp x ∂gaussianReal μ v) =
        (∫ x, x ∂gaussianReal μ v) + Var[id; gaussianReal μ v] / 2 ∧
      Var[fun x => x - ∫ y, y ∂gaussianReal μ v; gaussianReal μ v] =
        Var[id; gaussianReal μ v] := by
  refine ⟨?_, ?_⟩
  · have h := congrFun (mgf_id_gaussianReal (μ := μ) (v := v)) 1
    simp only [mgf, id, one_mul, mul_one, one_pow] at h
    rw [h, Real.log_exp, integral_id_gaussianReal, variance_id_gaussianReal]
  · exact variance_sub_const measurable_id.aestronglyMeasurable _

/-- AKMM, p. 348, **the first-order approximation** `log(λ − φ) ≈ log λ − φ/λ` around
`φ = 0`: exactly `log(λ − φ) = log λ + log(1 − φ/λ)`, and for `x = φ/λ ∈ [0, 1)`,
`−x/(1 − x) ≤ log(1 − x) ≤ −x`, so the error `|log(1 − x) + x| ≤ x²/(1 − x)`; and the
derivative of `φ ↦ log(λ − φ)` at `0` is `−1/λ`. -/
theorem fe_log_approx {lam φ : ℝ} (hlam : 0 < lam) (hφ0 : 0 ≤ φ) (hφ : φ < lam) :
    Real.log (lam - φ) = Real.log lam + Real.log (1 - φ / lam) ∧
      -(φ / lam) / (1 - φ / lam) ≤ Real.log (1 - φ / lam) ∧
      Real.log (1 - φ / lam) ≤ -(φ / lam) ∧
      |Real.log (1 - φ / lam) + φ / lam| ≤ (φ / lam) ^ 2 / (1 - φ / lam) ∧
      HasDerivAt (fun x => Real.log (lam - x)) (-(1 / lam)) 0 := by
  have hx1 : φ / lam < 1 := by rw [div_lt_one hlam]; exact hφ
  have hx0 : 0 ≤ φ / lam := div_nonneg hφ0 hlam.le
  have hpos : 0 < 1 - φ / lam := by linarith
  have hne : lam - φ ≠ 0 := (sub_pos.2 hφ).ne'
  have hne' : -φ + lam ≠ 0 := by rw [neg_add_eq_sub]; exact hne
  have up : Real.log (1 - φ / lam) ≤ -(φ / lam) := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have lo : -(φ / lam) / (1 - φ / lam) ≤ Real.log (1 - φ / lam) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - φ / lam)⁻¹ = -(φ / lam) / (1 - φ / lam) := by field_simp; ring
    linarith
  refine ⟨?_, lo, up, ?_, ?_⟩
  · rw [← Real.log_mul hlam.ne' hpos.ne']
    congr 1
    field_simp
  · rw [abs_le]
    have e : -(φ / lam) / (1 - φ / lam) + φ / lam = -((φ / lam) ^ 2 / (1 - φ / lam)) := by
      field_simp; ring
    have hsq : 0 ≤ (φ / lam) ^ 2 / (1 - φ / lam) := by positivity
    constructor <;> linarith
  · have := ((hasDerivAt_id (0 : ℝ)).const_sub lam).log
      (by simp only [id_eq, sub_zero, ne_eq]; exact hlam.ne')
    refine this.congr_deriv ?_
    simp only [id, sub_zero]
    ring

/-- AKMM, (12.29), p. 348, **exactly**: if (12.26) holds and, from (12.27)–(12.28) at `t − 1`,
`log λ_{t−1} + log(1 − φ_{t−1}/λ_{t−1}) = κ + log λ_t − ξ_t + V/2` (`V` the conditional
variance of `ξ_t`, `κ` the constant), then
`Δ log ℓ_t = γΔ log w_t + γ(ξ_t + log(1 − φ_{t−1}/λ_{t−1}) − V/2) − γκ`. Replacing
`log(1 − φ/λ)` by `−φ/λ` (error at most `(φ/λ)²/(1 − φ/λ)`, `fe_log_approx`) and dropping the
constant gives the printed (12.29). -/
theorem eq_12_29 {γ κ V ξ dl dw m₀ m₁ L : ℝ} (h26 : dl = γ * dw + γ * (m₁ - m₀))
    (h27 : m₀ + L = κ + m₁ - ξ + V / 2) :
    dl = γ * dw + γ * (ξ + L - V / 2) - γ * κ := by
  rw [h26]
  have : m₁ - m₀ = ξ + L - V / 2 - κ := by linarith
  rw [this]; ring

/-- AKMM, (12.30)–(12.31), p. 349: writing `Δ log w = E_{t−1}[Δ log w] + ε` in (12.26),
`Δ log ℓ = γE_{t−1}[Δ log w] + γ(ε + Δ log λ)`. -/
theorem eq_12_31 {γ dl dw Edw ε dm : ℝ} (h26 : dl = γ * dw + γ * dm) (h30 : dw = Edw + ε) :
    dl = γ * Edw + γ * (ε + dm) := by
  rw [h26, h30]; ring

/-- AKMM, p. 349, **consumption data**: combining (12.24) (`log λ = −σ log c`) with (12.26),
`Δ log ℓ = γΔ log w − γσΔ log c`. -/
theorem fe_consumption_data {γ σ dl dw m₀ m₁ c₀ c₁ : ℝ} (h26 : dl = γ * dw + γ * (m₁ - m₀))
    (h₀ : m₀ = -σ * c₀) (h₁ : m₁ = -σ * c₁) : dl = γ * dw - γ * σ * (c₁ - c₀) := by
  rw [h26, h₀, h₁]; ring

/-! ### Optimisation frictions -/

/-- The tangent inequality for `x^p`, `p > 1`: `x^p ≥ y^p + py^{p−1}(x − y)` for `x ≥ 0`,
`y > 0`, strict for `x ≠ y`. -/
theorem fr_rpow_tangent {p x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    y ^ p + p * y ^ (p - 1) * (x - y) < x ^ p := by
  have hs : -1 ≤ x / y - 1 := by have := div_nonneg hx hy.le; linarith
  have hs' : x / y - 1 ≠ 0 := by
    intro h; apply hxy; field_simp at h; linarith
  have := one_add_mul_self_lt_rpow_one_add hs hs' hp
  rw [show 1 + (x / y - 1) = x / y by ring, Real.div_rpow hx hy.le] at this
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  rw [lt_div_iff₀ hyp] at this
  have e : y ^ (p - 1) = y ^ p / y := Real.rpow_sub_one hy.ne' p
  rw [e]
  have : y ^ p + p * (y ^ p / y) * (x - y) = (1 + p * (x / y - 1)) * y ^ p := by
    field_simp
  linarith

/-- GHH utility with consumption `c = wℓ` substituted: `log(wℓ − ψℓ^{1+1/γ}/(1 + 1/γ))`
(AKMM, (12.32), p. 350). -/
noncomputable def frV (ψ γ w l : ℝ) : ℝ := Real.log (w * l - disutil ψ γ l)

/-- At `ℓ* = (w/ψ)^γ`: `ψℓ*^{1/γ} = w` and `wℓ* − v(ℓ*) = wℓ*/(1 + γ)`. -/
theorem fr_opt_facts {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    ψ * ((w / ψ) ^ γ) ^ (1 / γ) = w ∧
      w * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) = w * (w / ψ) ^ γ / (1 + γ) := by
  have hk : 0 < w / ψ := by positivity
  have h1 : ((w / ψ) ^ γ) ^ (1 / γ) = w / ψ := by
    rw [← Real.rpow_mul hk.le, mul_one_div_cancel hγ.ne', Real.rpow_one]
  refine ⟨by rw [h1]; field_simp, ?_⟩
  unfold disutil
  have h2 : ((w / ψ) ^ γ) ^ (1 + 1 / γ) = (w / ψ) ^ γ * (w / ψ) := by
    rw [Real.rpow_add (Real.rpow_pos_of_pos hk _), Real.rpow_one, h1]
  rw [h2]
  have hp : 0 < (w / ψ) ^ γ := Real.rpow_pos_of_pos hk _
  field_simp
  ring

/-- AKMM, (12.33), p. 351: with `c = wℓ`, `ℓ* = (w/ψ)^γ` (and `c* = wℓ*`) uniquely maximises
the GHH utility `log(wℓ − v(ℓ))` over `ℓ ≥ 0` with `wℓ − v(ℓ) > 0`. -/
theorem eq_12_33 {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    0 < w * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) ∧
      ∀ l, 0 ≤ l → l ≠ (w / ψ) ^ γ → 0 < w * l - disutil ψ γ l →
        frV ψ γ w l < frV ψ γ w ((w / ψ) ^ γ) := by
  obtain ⟨h1, h2⟩ := fr_opt_facts hψ hγ hw
  have hk : 0 < w / ψ := by positivity
  set ls := (w / ψ) ^ γ
  have hls : 0 < ls := Real.rpow_pos_of_pos hk _
  refine ⟨by rw [h2]; positivity, fun l hl hne hpos => ?_⟩
  unfold frV
  apply Real.log_lt_log hpos
  -- the tangent inequality for `v`
  have hγ' : 0 < 1 / γ := by positivity
  have hp : 1 < 1 + 1 / γ := by linarith
  have ht := fr_rpow_tangent hp hl hls hne
  rw [show 1 + 1 / γ - 1 = 1 / γ by ring] at ht
  unfold disutil
  have hg : 0 < 1 + 1 / γ := by linarith
  have : ψ * ls ^ (1 + 1 / γ) / (1 + 1 / γ) + w * (l - ls) < ψ * l ^ (1 + 1 / γ) / (1 + 1 / γ) := by
    rw [div_add' _ _ _ hg.ne', div_lt_div_iff_of_pos_right hg, ← h1]
    nlinarith [mul_lt_mul_of_pos_left ht hψ]
  linarith

/-- AKMM, p. 351: the optimal utility is `U(c*, ℓ*) = −log(1 + γ) − γ log ψ + (1 + γ) log w`. -/
theorem fr_value {ψ γ w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) :
    frV ψ γ w ((w / ψ) ^ γ) = -Real.log (1 + γ) - γ * Real.log ψ + (1 + γ) * Real.log w := by
  unfold frV
  rw [(fr_opt_facts hψ hγ hw).2]
  have hk : 0 < w / ψ := by positivity
  rw [Real.log_div (by positivity : (0 : ℝ) < w * (w / ψ) ^ γ).ne'
    (by positivity : (0 : ℝ) < 1 + γ).ne', Real.log_mul hw.ne'
    (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_div hw.ne' hψ.ne']
  ring

/-- AKMM, p. 351 and (12.34): the gain from a wage rise `w → w(1 + ε)` splits into the gain at
the old hours, `log(1 + ε(1 + γ))` (with consumption updated to `w(1 + ε)ℓ*`), and the gain from
re-optimising hours, `(1 + γ) log(1 + ε) − log(1 + ε(1 + γ))` (12.34); the total is
`(1 + γ) log(1 + ε)`. Here `1 + ε(1 + γ) > 0`. -/
theorem eq_12_34 {ψ γ w ε : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) (hε : -1 < ε)
    (hε' : 0 < 1 + ε * (1 + γ)) :
    frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) - frV ψ γ w ((w / ψ) ^ γ) =
        Real.log (1 + ε * (1 + γ)) ∧
      frV ψ γ (w * (1 + ε)) ((w * (1 + ε) / ψ) ^ γ) - frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) =
        (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) := by
  have h1e : 0 < 1 + ε := by linarith
  have hw' : 0 < w * (1 + ε) := by positivity
  have hk : 0 < w / ψ := by positivity
  have hls : 0 < (w / ψ) ^ γ := Real.rpow_pos_of_pos hk _
  have hold : frV ψ γ (w * (1 + ε)) ((w / ψ) ^ γ) =
      Real.log (w * (w / ψ) ^ γ / (1 + γ)) + Real.log (1 + ε * (1 + γ)) := by
    unfold frV
    have e : w * (1 + ε) * (w / ψ) ^ γ - disutil ψ γ ((w / ψ) ^ γ) =
        w * (w / ψ) ^ γ / (1 + γ) * (1 + ε * (1 + γ)) := by
      have := (fr_opt_facts hψ hγ hw).2
      have e2 : disutil ψ γ ((w / ψ) ^ γ) = w * (w / ψ) ^ γ - w * (w / ψ) ^ γ / (1 + γ) := by
        linarith
      rw [e2]; field_simp; ring
    rw [e, Real.log_mul (by positivity) hε'.ne']
  have h0 : frV ψ γ w ((w / ψ) ^ γ) = Real.log (w * (w / ψ) ^ γ / (1 + γ)) := by
    unfold frV; rw [(fr_opt_facts hψ hγ hw).2]
  refine ⟨by rw [hold, h0]; ring, ?_⟩
  rw [hold, fr_value hψ hγ hw', Real.log_mul hw.ne' h1e.ne']
  have : Real.log (w * (w / ψ) ^ γ / (1 + γ)) =
      -Real.log (1 + γ) - γ * Real.log ψ + (1 + γ) * Real.log w := by
    rw [← h0]; exact fr_value hψ hγ hw
  rw [this]; ring

/-- AKMM, p. 351: the gain from re-optimising hours (12.34) is positive for `ε ≠ 0` (it is the
gain of the optimum `ℓ*_ε` over `ℓ*`). -/
theorem fr_gain_pos {γ ε : ℝ} (hγ : 0 < γ) (hε : -1 < ε) (hε0 : ε ≠ 0)
    (hpos : 0 < 1 + ε * (1 + γ)) :
    0 < (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) := by
  -- Bernoulli: `(1 + ε)^{1+γ} > 1 + (1 + γ)ε`
  have hB := one_add_mul_self_lt_rpow_one_add (by linarith : (-1 : ℝ) ≤ ε) hε0
    (by linarith : (1 : ℝ) < 1 + γ)
  have h1e : 0 < 1 + ε := by linarith
  have := Real.log_lt_log hpos (by linarith : 1 + ε * (1 + γ) < (1 + ε) ^ (1 + γ))
  rw [Real.log_rpow h1e] at this
  linarith

/-- AKMM, p. 351: the gain `(1 + γ) log(1 + ε) − log(1 + ε(1 + γ))` is strictly increasing in
`ε ≥ 0`, so the agent re-optimises exactly for `ε` above a threshold. -/
theorem fr_gain_strictMono {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (fun ε => (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)))
      (Set.Ici 0) := by
  have hder : ∀ ε, 0 ≤ ε → HasDerivAt
      (fun ε => (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)))
      ((1 + γ) * (1 / (1 + ε)) - (1 + γ) / (1 + ε * (1 + γ))) ε := by
    intro ε hε
    have h1 := (((hasDerivAt_id ε).const_add 1).log (by simp; linarith)).const_mul (1 + γ)
    have h2 := (((hasDerivAt_id ε).mul_const (1 + γ)).const_add 1).log
      (by simp; nlinarith)
    exact (h1.sub h2).congr_deriv (by simp)
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hder x hx0.le).deriv]
    have ha : 0 < 1 + x := by linarith
    have hb : 0 < 1 + x * (1 + γ) := by nlinarith
    rw [one_div, ← div_eq_mul_inv, sub_pos, div_lt_div_iff_of_pos_left (by linarith) hb ha]
    nlinarith

/-- AKMM, (12.35), p. 351, **with an explicit error bound**: for `|ε|(1 + γ) < 1`,
`|(1 + γ) log(1 + ε) − log(1 + ε(1 + γ)) − ½γ(1 + γ)ε²|
≤ (1 + γ)|ε|³/(1 − |ε|) + ((1 + γ)|ε|)³/(1 − (1 + γ)|ε|)`. -/
theorem eq_12_35 {γ ε : ℝ} (hγ : 0 < γ) (hε : |ε| * (1 + γ) < 1) :
    |(1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) - 1 / 2 * γ * (1 + γ) * ε ^ 2| ≤
      (1 + γ) * (|ε| ^ 3 / (1 - |ε|)) + (|ε| * (1 + γ)) ^ 3 / (1 - |ε| * (1 + γ)) := by
  have hg : 1 ≤ 1 + γ := by linarith
  have hε1 : |ε| < 1 := by
    have : |ε| ≤ |ε| * (1 + γ) := le_mul_of_one_le_right (abs_nonneg _) hg
    linarith
  have hA := Real.abs_log_sub_add_sum_range_le (x := -ε) (by rwa [abs_neg]) 2
  have hB := Real.abs_log_sub_add_sum_range_le (x := -(ε * (1 + γ)))
    (by rw [abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + γ)]; exact hε) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hA hB
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + γ)] at hB
  norm_num at hA hB
  have key : (1 + γ) * Real.log (1 + ε) - Real.log (1 + ε * (1 + γ)) -
      1 / 2 * γ * (1 + γ) * ε ^ 2 =
      (1 + γ) * (-ε + ε ^ 2 / 2 + Real.log (1 + ε)) -
        (-(ε * (1 + γ)) + (ε * (1 + γ)) ^ 2 / 2 + Real.log (1 + ε * (1 + γ))) := by ring
  rw [key]
  have hpos : 0 < 1 + γ := by linarith
  calc _ ≤ |(1 + γ) * (-ε + ε ^ 2 / 2 + Real.log (1 + ε))| +
        |(-(ε * (1 + γ)) + (ε * (1 + γ)) ^ 2 / 2 + Real.log (1 + ε * (1 + γ)))| :=
        abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos hpos]
      gcongr

/-- AKMM, p. 352, **the thresholds**: for `ε > 0`, the second-order gain `½γ(1 + γ)ε²` exceeds
the cost `Δ > 0` iff `ε > ε_min = (2Δ/(γ(1 + γ)))^{1/2}`; hours change by
`log ℓ*_ε − log ℓ* = γ log(1 + ε) ≈ γε` (exactly, by (12.33)), and
`γε_min = (2Δγ/(1 + γ))^{1/2}`. -/
theorem fr_threshold {ψ γ w Δ ε : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hw : 0 < w) (hΔ : 0 < Δ)
    (hε : 0 < ε) :
    (Δ < 1 / 2 * γ * (1 + γ) * ε ^ 2 ↔ Real.sqrt (2 * Δ / (γ * (1 + γ))) < ε) ∧
      Real.log ((w * (1 + ε) / ψ) ^ γ) - Real.log ((w / ψ) ^ γ) = γ * Real.log (1 + ε) ∧
      γ * Real.sqrt (2 * Δ / (γ * (1 + γ))) = Real.sqrt (2 * Δ * γ / (1 + γ)) := by
  have hg : 0 < γ * (1 + γ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sqrt_lt' hε, div_lt_iff₀ hg]
    constructor <;> intro h <;> nlinarith
  · have hk : 0 < w / ψ := by positivity
    have h1e : 0 < 1 + ε := by linarith
    rw [Real.log_rpow (by positivity), Real.log_rpow hk,
      show w * (1 + ε) / ψ = w / ψ * (1 + ε) by ring, Real.log_mul hk.ne' h1e.ne']
    ring
  · rw [show γ = Real.sqrt (γ ^ 2) by rw [Real.sqrt_sq hγ.le], ← Real.sqrt_mul (by positivity),
      Real.sqrt_sq hγ.le]
    congr 1
    field_simp

end AKMM.LaborSupply
