/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSolow.GrowingEconomy
import AKMMSolow.OtherDynamics
import DiscreteTime.SolowConvergence

/-!
# The speed of convergence

AKMM, §3.4.1 and §3.4.3, pp. 82–88. The book's linearisations (3.10) and (3.12) are statements
about the derivative of the Solow map at its fixed point; they are proved as exact derivatives,
reusing EconomicGrowth's `next_hasDerivAt`, `slope_at_steady`, `contraction_steady` and
`cobbDouglas_contraction`.

* (3.10): the slope of (3.5) at `k̄` is `1 − δ + s f'(k̄) = 1 − λ`, `λ = δ − s f'(k̄) ∈ (0, 1)`
  (`eq_3_10`), and the relative-deviation form (`solow_linearised_relative`).
* Cobb–Douglas: slope `1 − δ(1 − α)` and (3.11) `λ = δ(1 − α)` (`eq_3_11`); `s` does not affect
  `λ` (`solow_speed_independent_of_saving`) because the two forces cancel exactly: `f'(k̄)` falls
  with `s` (`solow_marginal_product_falls_with_saving`) while `s f'(k̄) = αδ`
  (`solow_cobbDouglas_forces_offset`).
* (3.12) with growth: slope `(1 − δ + s f'(k̃̄))/((1 + γ)(1 + n))` (`eq_3_12`); Cobb–Douglas slope
  `α + (1 − α)(1 − δ)/((1 + γ)(1 + n))` and (3.13) `λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))`
  (`eq_3_13`).
* Local stability of the steady state from the slope (`solow_steady_locally_stable`,
  `solow_steady_locallyAttracting`).
* §3.4.3: on the balanced path `(1 + γ)(1 + n) = 1 − δ + I/K` (`solow_bgp_investment_rate`);
  doubling `s` multiplies balanced-growth output by `2^{α/(1−α)}`, which is `√2` at `α = 1/3`:
  a 41% rise, not the 17% printed on p. 88 (`solow_saving_output_ratio`,
  `solow_p88_doubling_saving`).
-/

namespace AKMM.Solow

open Filter Topology Solow1956.Neoclassical Solow1956.DiscreteTime

variable {F : ℝ → ℝ → ℝ}

/-- AKMM, (3.10), p. 82: the derivative of `k ↦ (1 − δ)k + s f(k)` at the steady state is
`1 − δ + s f'(k̄) = 1 − λ` with the convergence speed `λ = δ − s f'(k̄)`, and `0 < λ < 1`
(EconomicGrowth's `next_hasDerivAt` and `slope_at_steady`). -/
theorem eq_3_10 (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1) :
    HasDerivAt (fun k => (1 - δ) * k + s * intensive F k)
        (1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ 1))
        (steady (solow_technology hF) s δ 1) ∧
      1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ 1) =
        1 - (δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1)) ∧
      0 < δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1) ∧
      δ - s * deriv (intensive F) (steady (solow_technology hF) s δ 1) < 1 := by
  have P := solow_params_basic hs hδ hδ1
  have h := solow_technology hF
  have hk := (steady_spec h P).1
  have hd := next_hasDerivAt h s δ 1 hk
  have hsl := slope_at_steady h P
  rw [div_one] at hd hsl
  refine ⟨?_, by ring, by linarith [hsl.2], by linarith [hsl.1]⟩
  have e : next (intensive F) s δ 1 = fun k => (1 - δ) * k + s * intensive F k := by
    funext k; rw [next_acemoglu]; ring
  rw [e] at hd
  convert hd using 1
  ring

/-- AKMM, p. 82: the linearised law `Δk_{t+1} = (1 − λ)Δk_t`, `Δk_t = k_t − k̄`, in relative
deviations: `(k_{t+1} − k̄)/k̄ = (1 − λ)(k_t − k̄)/k̄`. -/
theorem solow_linearised_relative {kbar lam : ℝ} {k : ℕ → ℝ}
    (hlin : ∀ t, k (t + 1) - kbar = (1 - lam) * (k t - kbar)) (t : ℕ) :
    (k (t + 1) - kbar) / kbar = (1 - lam) * ((k t - kbar) / kbar) := by
  rw [hlin, mul_div_assoc]

/-- AKMM, p. 82 and (3.11), p. 82: with `f(k) = k^α` the slope of (3.5) at `k̄` is
`1 − δ(1 − α)`, so `λ = δ − s f'(k̄) = δ(1 − α)` (EconomicGrowth's `cobbDouglas_contraction`). -/
theorem eq_3_11 {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ + s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) =
        1 - δ * (1 - α) ∧
      δ - s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) =
        δ * (1 - α) := by
  have P := solow_params_basic hs hδ hδ1
  have h1 := contraction_steady (technology_rpow hα hα1) P
  rw [cobbDouglas_contraction hα hα1 P, div_one] at h1
  constructor <;> linarith

/-- AKMM, p. 83: in the Cobb–Douglas case `s` does not affect the convergence speed `λ`. -/
theorem solow_speed_independent_of_saving {α s₁ s₂ δ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hδ : 0 < δ) (hδ1 : δ < 1) :
    δ - s₁ * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s₁ δ 1) =
      δ - s₂ * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s₂ δ 1) := by
  rw [(eq_3_11 hα hα1 hs₁ hδ hδ1).2, (eq_3_11 hα hα1 hs₂ hδ hδ1).2]

/-- AKMM, p. 83 (the second of the two opposing forces): a higher saving rate raises `k̄` and so
lowers the marginal product `f'(k̄)` at the steady state. -/
theorem solow_marginal_product_falls_with_saving (hF : SolowAssumptions F) {s₁ s₂ δ : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ < s₂) (hδ : 0 < δ) :
    deriv (intensive F) (steady (solow_technology hF) s₂ δ 1) <
      deriv (intensive F) (steady (solow_technology hF) s₁ δ 1) := by
  have hm : (0 : ℝ) < 1 - 1 + δ := by linarith
  exact (solow_technology hF).marginal_strictAnti (steadyCapital_spec _ hs₁ hm).1
    (steadyCapital_spec _ (hs₁.trans hs) hm).1 (solow_steady_strictMono_saving hF hs₁ hs hδ).1

/-- AKMM, p. 83: "these two opposing forces exactly offset each other when the production
function is in the Cobb–Douglas form": `s f'(k̄) = αδ` at every saving rate. -/
theorem solow_cobbDouglas_forces_offset {α s δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    s * deriv (fun k : ℝ => k ^ α) (steady (technology_rpow hα hα1) s δ 1) = α * δ := by
  have := (eq_3_11 hα hα1 hs hδ hδ1).2
  linarith

/-- AKMM, (3.12), p. 83: with growth, the derivative of the map of (3.7) at `k̃̄` is
`(1 − δ + s f'(k̃̄))/((1 + γ)(1 + n)) = 1 − λ` with
`λ = 1 − (1 − δ + s f'(k̃̄))/((1 + γ)(1 + n)) ∈ (0, 1)`. -/
theorem eq_3_12 (hF : SolowAssumptions F) {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    HasDerivAt (next (intensive F) s δ ((1 + γ) * (1 + n)))
        ((1 - δ + s * deriv (intensive F) (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))))
          / ((1 + γ) * (1 + n)))
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n))) ∧
      0 < 1 - (1 - δ + s * deriv (intensive F)
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) ∧
      1 - (1 - δ + s * deriv (intensive F)
        (steady (solow_technology hF) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) < 1 := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h := solow_technology hF
  have hd := next_hasDerivAt h s δ ((1 + γ) * (1 + n)) (steady_spec h P).1
  have hsl := slope_at_steady h P
  rw [add_comm (s * _)] at hd hsl
  exact ⟨hd, by linarith [hsl.2], by linarith [hsl.1]⟩

/-- AKMM, p. 83 and (3.13), p. 83: with `f(k) = k^α` the slope at `k̃̄` is
`α + (1 − α)(1 − δ)/((1 + γ)(1 + n))`, so
`λ = (1 − α)(1 − (1 − δ)/((1 + γ)(1 + n)))`, which does not involve `s` (p. 86). -/
theorem eq_3_13 {α s δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    (1 - δ + s * deriv (fun k : ℝ => k ^ α)
        (steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) =
        α + (1 - α) * (1 - δ) / ((1 + γ) * (1 + n)) ∧
      1 - (1 - δ + s * deriv (fun k : ℝ => k ^ α)
        (steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)))) / ((1 + γ) * (1 + n)) =
        (1 - α) * (1 - (1 - δ) / ((1 + γ) * (1 + n))) := by
  have P := solow_params_growth hs hδ hδ1 hγ hn
  have h1 := contraction_steady (technology_rpow hα hα1) P
  rw [cobbDouglas_contraction hα hα1 P, add_comm (s * _)] at h1
  rw [← h1]
  have hG : (1 + γ) * (1 + n) ≠ 0 := ne_of_gt P.growth_pos
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- AKMM, §3.4.1 with footnote a of p. 78: the steady state of (3.5) is locally stable; paths
started within `ε` of `k̄` approach it at least geometrically, with ratio `ρ < 1`. -/
theorem solow_steady_locally_stable (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε > 0, ∃ ρ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x₀, |x₀ - steady (solow_technology hF) s δ 1| < ε →
      (∀ t, |(fun k => (1 - δ) * k + s * intensive F k)^[t] x₀ -
          steady (solow_technology hF) s δ 1| ≤ ρ ^ t * |x₀ - steady (solow_technology hF) s δ 1|) ∧
        Tendsto (fun t => (fun k => (1 - δ) * k + s * intensive F k)^[t] x₀) atTop
          (𝓝 (steady (solow_technology hF) s δ 1)) := by
  obtain ⟨hd, _, hl0, hl1⟩ := eq_3_10 hF hs hδ hδ1
  have hfix : (fun k => (1 - δ) * k + s * intensive F k) (steady (solow_technology hF) s δ 1) =
      steady (solow_technology hF) s δ 1 := by
    have := (solow_steady_spec hF hs hδ hδ1).2
    simp only
    linarith
  exact solow_local_stability hd hfix (by rw [abs_lt]; constructor <;> linarith)

/-- AKMM, §3.4.1 and pp. 76–77: the steady state of the basic model is locally attracting in the
sense used for poverty traps (`SolowLocallyAttracting`). -/
theorem solow_steady_locallyAttracting (hF : SolowAssumptions F) {s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    SolowLocallyAttracting (fun k => (1 - δ) * k + s * intensive F k)
      (steady (solow_technology hF) s δ 1) := by
  obtain ⟨ε, hε, ρ, _, _, h⟩ := solow_steady_locally_stable hF hs hδ hδ1
  exact ⟨ε, hε, fun x₀ hx => (h x₀ hx).2⟩

/-- AKMM, §3.4.3, p. 87: on the balanced growth path (3.7) reads
`(1 + γ)(1 + n) = 1 − δ + I/K`, with `I/K = s f(k̃)/k̃`. -/
theorem solow_bgp_investment_rate {f : ℝ → ℝ} {s δ γ n k : ℝ} (hk : 0 < k)
    (hbgp : (1 + γ) * (1 + n) * k = (1 - δ) * k + s * f k) :
    (1 + γ) * (1 + n) = 1 - δ + s * f k / k := by
  field_simp
  linarith

/-- AKMM, §3.4.3, pp. 87–88: with `f(k) = k^α`, balanced-growth output per efficiency unit is
`f(k̃̄) = (s/((1 + γ)(1 + n) + δ − 1))^{α/(1−α)}`, so raising saving from `s₁` to `s₂` multiplies it
by `(s₂/s₁)^{α/(1−α)}`. -/
theorem solow_saving_output_ratio {α s₁ s₂ δ γ n : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs₁ : 0 < s₁)
    (hs₂ : 0 < s₂) (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow hα hα1) s₂ δ ((1 + γ) * (1 + n)) ^ α /
        steady (technology_rpow hα hα1) s₁ δ ((1 + γ) * (1 + n)) ^ α =
      (s₂ / s₁) ^ (α / (1 - α)) := by
  have hm : 0 < (1 + γ) * (1 + n) + δ - 1 := by
    have := (solow_params_growth hs₁ hδ hδ1 hγ hn).dilution_pos; linarith
  have hy : ∀ s, 0 < s → steady (technology_rpow hα hα1) s δ ((1 + γ) * (1 + n)) ^ α =
      (s / ((1 + γ) * (1 + n) + δ - 1)) ^ (α / (1 - α)) := by
    intro s hs
    rw [eq_3_8 hα hα1 hs hδ hδ1 hγ hn, ← Real.rpow_mul (div_pos hs hm).le]
    congr 1
    ring
  rw [hy s₁ hs₁, hy s₂ hs₂, ← Real.div_rpow (div_pos hs₂ hm).le (div_pos hs₁ hm).le]
  congr 1
  field_simp

/-- AKMM, §3.4.3, p. 88, corrected. With the calibrated `α = 1/3`, doubling the saving rate
(from 10% to 20%) multiplies balanced-growth output per efficiency unit by `2^{1/2} = √2 > 1.41`:
a 41% increase, not the printed 17% (`1.24/1.06`). The other calibrated parameters do not
matter. -/
theorem solow_p88_doubling_saving {s δ γ n : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 ≤ γ) (hn : 0 ≤ n) :
    steady (technology_rpow (α := 1 / 3) (by norm_num) (by norm_num)) (2 * s) δ
          ((1 + γ) * (1 + n)) ^ (1 / 3 : ℝ) /
        steady (technology_rpow (α := 1 / 3) (by norm_num) (by norm_num)) s δ
          ((1 + γ) * (1 + n)) ^ (1 / 3 : ℝ) = Real.sqrt 2 ∧
      (1.41 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 ≠ 1.24 / 1.06 := by
  have h := solow_saving_output_ratio (α := 1 / 3) (by norm_num) (by norm_num) hs
    (by positivity : 0 < 2 * s) hδ hδ1 hγ hn
  rw [show 2 * s / s = 2 by field_simp, show (1 / 3 : ℝ) / (1 - 1 / 3) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow] at h
  have hlt : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  refine ⟨h, hlt, ?_⟩
  intro heq
  rw [heq] at hlt
  norm_num at hlt

end AKMM.Solow
