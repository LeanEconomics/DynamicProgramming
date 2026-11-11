/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DynamicGames.DGFishProblem

/-!
# The Great Fish War

Miao, §21.3, pp. 755–757, and Exercise 21.3, p. 771: the Levhari–Mirman (1980) model. The fish
stock follows `x_{t+1} = (x_t − c_{1t} − c_{2t})^α` (21.1) and country `i` maximises
`∑ β_iᵗ ln c_{it}`.

Markov perfect equilibrium. With value functions `V_i(x) = κ_i ln x + ν_i` the first-order
conditions (`dg_fish_foc_deriv`, `eq_21_2`) give the linear rules of the text
(`dg_fish_foc_solve`); coefficient matching gives `κ_i = 1/(1 − αβ_i)` (`dg_fish_mpe_kappa`); the
closed form `c_1 = αβ₂(1 − αβ₁)x/(1 − (1 − αβ₁)(1 − αβ₂))` (`dg_fish_mpe_closed_form`), the law
of motion `x_{t+1} = (αβ₁β₂x_t/(β₁ + β₂ − αβ₁β₂))^α` (`eq_21_1_mpe`) and the steady state
(`dg_fish_mpe_steady_state`). The pair of rules is a Markov perfect equilibrium: each rule is a
best response to the other among all feasible catch sequences with convergent utility, with
value `V_i(x₀)` (`dg_fish_mpe`).

Stackelberg. The follower's reaction to a catch `c₁` is `c₂ = (x − c₁)/(1 + αβ₂κ₂)`
(`dg_fish_follower_reaction`); the text prints `c₂ = αβ₂κ₂(x − c₁)/(1 + αβ₂κ₂)`, which violates
(21.2) (`dg_fish_follower_printed_false`). The misprint does not affect the leader: the leader's
rule is `c₁ = x/(1 + αβ₁κ₁)` (`dg_fish_leader_foc`), `κ₁ = 1/(1 − αβ₁)` and `c₁ = (1 − αβ₁)x`
(`dg_fish_leader`). Exercise 21.3: the follower's equilibrium catch is `c₂ = αβ₁(1 − αβ₂)x`
(`ex_21_3`).

The cooperative comparison is not carried out in the text; we add it for symmetric countries:
the planner catches `(1 − αβ)x`, split equally (`dg_fish_cooperative`), less than the MPE total
`2(1 − αβ)x/(2 − αβ)`, and the MPE steady-state stock is lower (`dg_fish_overfishing`).
-/

namespace Miao.DynamicGames

/-- (21.1) (Miao, p. 755): the fish stock evolves as `x_{t+1} = (x_t − c_{1t} − c_{2t})^α`. -/
noncomputable def dg_fishLaw (α x c₁ c₂ : ℝ) : ℝ := (x - c₁ - c₂) ^ α

/-- Under `V(x) = κ ln x + ν`, `V((x − c₁ − c₂)^α) = κα ln(x − c₁ − c₂) + ν`. -/
theorem dg_fish_V_law {α κ ν x c₁ c₂ : ℝ} (h : 0 < x - c₁ - c₂) :
    κ * Real.log (dg_fishLaw α x c₁ c₂) + ν = κ * α * Real.log (x - c₁ - c₂) + ν := by
  unfold dg_fishLaw
  rw [Real.log_rpow h]
  ring

/-- Miao, p. 756: the first-order condition of country 1. The derivative of
`c₁ ↦ ln c₁ + β₁(κ₁α ln(x − c₁ − c₂) + ν₁)` is `1/c₁ − αβ₁κ₁/(x − c₁ − c₂)`. -/
theorem dg_fish_foc_deriv {α β₁ κ₁ ν₁ x c₁ c₂ : ℝ} (hc : 0 < c₁) (hs : 0 < x - c₁ - c₂) :
    HasDerivAt (fun c => Real.log c + β₁ * (κ₁ * α * Real.log (x - c - c₂) + ν₁))
      (1 / c₁ - α * β₁ * κ₁ / (x - c₁ - c₂)) c₁ := by
  have h1 := Real.hasDerivAt_log hc.ne'
  have h2 : HasDerivAt (fun c => x - c - c₂) (-1) c₁ := by
    simpa using ((hasDerivAt_id c₁).const_sub x).sub_const c₂
  have h3 := (h2.log hs.ne').const_mul (κ₁ * α) |>.add_const ν₁ |>.const_mul β₁
  convert h1.add h3 using 1
  field_simp
  ring

/-- (21.2) (Miao, p. 756): the first-order condition of country 2. The derivative of
`c₂ ↦ ln c₂ + β₂(κ₂α ln(x − c₁ − c₂) + ν₂)` is `1/c₂ − αβ₂κ₂/(x − c₁ − c₂)`, so it vanishes iff
`1/c₂ = αβ₂κ₂/(x − c₁ − c₂)`. -/
theorem eq_21_2 {α β₂ κ₂ ν₂ x c₁ c₂ : ℝ} (hc : 0 < c₂) (hs : 0 < x - c₁ - c₂) :
    HasDerivAt (fun c => Real.log c + β₂ * (κ₂ * α * Real.log (x - c₁ - c) + ν₂))
      (1 / c₂ - α * β₂ * κ₂ / (x - c₁ - c₂)) c₂ ∧
    (1 / c₂ - α * β₂ * κ₂ / (x - c₁ - c₂) = 0 ↔ 1 / c₂ = α * β₂ * κ₂ / (x - c₁ - c₂)) := by
  refine ⟨?_, sub_eq_zero⟩
  have h1 := Real.hasDerivAt_log hc.ne'
  have h2 : HasDerivAt (fun c => x - c₁ - c) (-1) c₂ := by
    simpa using (hasDerivAt_id c₂).const_sub (x - c₁)
  have h3 := (h2.log hs.ne').const_mul (κ₂ * α) |>.add_const ν₂ |>.const_mul β₂
  convert h1.add h3 using 1
  field_simp
  ring

/-- Miao, p. 756 ("using the above two equations, we can solve"): for `κ₁, κ₂ > 0`, positive
catches with `x − c₁ − c₂ > 0` satisfy both first-order conditions iff
`c₁ = β₂κ₂x/((1 + αβ₁κ₁)β₂κ₂ + β₁κ₁)` and `c₂ = β₁κ₁x/((1 + αβ₁κ₁)β₂κ₂ + β₁κ₁)`. -/
theorem dg_fish_foc_solve {α β₁ β₂ κ₁ κ₂ x c₁ c₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : 0 < x - c₁ - c₂) :
    (1 / c₁ = α * β₁ * κ₁ / (x - c₁ - c₂) ∧ 1 / c₂ = α * β₂ * κ₂ / (x - c₁ - c₂)) ↔
      (c₁ = β₂ * κ₂ * x / ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁) ∧
        c₂ = β₁ * κ₁ * x / ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) := by
  have hD : 0 < (1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁ := by positivity
  rw [div_eq_div_iff hc₁.ne' hs.ne', div_eq_div_iff hc₂.ne' hs.ne',
    eq_div_iff hD.ne', eq_div_iff hD.ne']
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : α * (c₁ * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) = α * (β₂ * κ₂ * x) := by
        nlinarith
      exact mul_left_cancel₀ hα.ne' this
    · have : α * (c₂ * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)) = α * (β₁ * κ₁ * x) := by
        nlinarith
      exact mul_left_cancel₀ hα.ne' this
  · rintro ⟨h1, h2⟩
    constructor
    · have : (1 * (x - c₁ - c₂) - c₁ * (α * β₁ * κ₁)) * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)
          = 0 := by linear_combination (-(1 + α * β₁ * κ₁)) * h1 - h2
      have := (mul_eq_zero.mp this).resolve_right hD.ne'
      linarith
    · have : (1 * (x - c₁ - c₂) - c₂ * (α * β₂ * κ₂)) * ((1 + α * β₁ * κ₁) * β₂ * κ₂ + β₁ * κ₁)
          = 0 := by linear_combination (-1 : ℝ) * h1 - (1 + α * β₂ * κ₂) * h2
      have := (mul_eq_zero.mp this).resolve_right hD.ne'
      linarith

/-- Miao, p. 756: substituting linear rules `c₁ = k₁x`, `c₂ = k₂x` into country 1's Bellman
equation `κ₁ ln x + ν₁ = ln(k₁x) + β₁(κ₁α ln((1 − k₁ − k₂)x) + ν₁)` (for all `x > 0`) forces
`κ₁ = 1/(1 − αβ₁)`; likewise for country 2. -/
theorem dg_fish_mpe_kappa {α β₁ κ₁ ν₁ k₁ k₂ : ℝ} (hab : α * β₁ < 1) (hk₁ : 0 < k₁)
    (hs : 0 < 1 - k₁ - k₂)
    (h : ∀ x : ℝ, 0 < x → κ₁ * Real.log x + ν₁ =
      Real.log (k₁ * x) + β₁ * (κ₁ * α * Real.log ((1 - k₁ - k₂) * x) + ν₁)) :
    κ₁ = 1 / (1 - α * β₁) :=
  dg_fp_kappa_forced hab hk₁ hs h

/-- The equilibrium catch rate `k = αβ_t(1 − αβ_o)/(1 − (1 − αβ_o)(1 − αβ_t))` of a country with
discount factor `β_o` whose rival has `β_t` (Miao, p. 757). -/
noncomputable def dg_fishK (α βo βt : ℝ) : ℝ :=
  α * βt * (1 - α * βo) / (1 - (1 - α * βo) * (1 - α * βt))

/-- The MPE saving rate `s = αβ₁β₂/(β₁ + β₂ − αβ₁β₂)`. -/
noncomputable def dg_fishS (α β₁ β₂ : ℝ) : ℝ := α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂)

/-- Miao, p. 757: with `κ_i = 1/(1 − αβ_i)` the solved first-order conditions are the MPE
`c₁ = αβ₂(1 − αβ₁)x/(1 − (1 − αβ₁)(1 − αβ₂))`, `c₂ = αβ₁(1 − αβ₂)x/(1 − (1 − αβ₁)(1 − αβ₂))`. -/
theorem dg_fish_mpe_closed_form {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) (x : ℝ) :
    β₂ * (1 / (1 - α * β₂)) * x / ((1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
        β₁ * (1 / (1 - α * β₁))) = dg_fishK α β₁ β₂ * x ∧
    β₁ * (1 / (1 - α * β₁)) * x / ((1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
        β₁ * (1 / (1 - α * β₁))) = dg_fishK α β₂ β₁ * x := by
  have e1 : 1 - α * β₁ ≠ 0 := by linarith
  have e2 : 1 - α * β₂ ≠ 0 := by linarith
  have hpos : 0 < β₁ + β₂ - α * β₁ * β₂ := by
    have := mul_pos hβ₂ (sub_pos.mpr h₁)
    nlinarith
  have hp' : β₁ + β₂ - α * β₁ * β₂ ≠ 0 := hpos.ne'
  have hΔ : 1 - (1 - α * β₁) * (1 - α * β₂) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hΔ' : 1 - (1 - α * β₂) * (1 - α * β₁) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hD : (1 + α * β₁ * (1 / (1 - α * β₁))) * β₂ * (1 / (1 - α * β₂)) +
      β₁ * (1 / (1 - α * β₁)) = (β₁ + β₂ - α * β₁ * β₂) / ((1 - α * β₁) * (1 - α * β₂)) := by
    field_simp; ring
  unfold dg_fishK
  rw [hD, hΔ, hΔ']
  have hα' : α ≠ 0 := hα.ne'
  obtain ⟨Q, hQ⟩ : ∃ Q, β₁ + β₂ - α * β₁ * β₂ = Q := ⟨_, rfl⟩
  rw [hQ] at hp' ⊢
  have e1' : 1 - β₁ * α ≠ 0 := by rwa [mul_comm]
  have e2' : 1 - β₂ * α ≠ 0 := by rwa [mul_comm]
  constructor <;> field_simp

/-- The catch rates are positive and leave a positive remainder:
`1 − k₁ − k₂ = αβ₁β₂/(β₁ + β₂ − αβ₁β₂)`, and each country's rule is the policy `(1 − αβ_i)` times
what the rival leaves: `(1 − αβ₁)(1 − k₂) = k₁`, `αβ₁(1 − k₂) = s`. -/
theorem dg_fish_rates {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) :
    0 < dg_fishK α β₁ β₂ ∧ 0 < dg_fishK α β₂ β₁ ∧
    1 - dg_fishK α β₁ β₂ - dg_fishK α β₂ β₁ = dg_fishS α β₁ β₂ ∧ 0 < dg_fishS α β₁ β₂ ∧
    (1 - α * β₁) * (1 - dg_fishK α β₂ β₁) = dg_fishK α β₁ β₂ ∧
    (1 - α * β₂) * (1 - dg_fishK α β₁ β₂) = dg_fishK α β₂ β₁ ∧
    α * β₁ * (1 - dg_fishK α β₂ β₁) = dg_fishS α β₁ β₂ ∧
    α * β₂ * (1 - dg_fishK α β₁ β₂) = dg_fishS α β₁ β₂ := by
  have e1 : 0 < 1 - α * β₁ := by linarith
  have e2 : 0 < 1 - α * β₂ := by linarith
  have hpos : 0 < β₁ + β₂ - α * β₁ * β₂ := by
    have := mul_pos hβ₂ (sub_pos.mpr h₁)
    nlinarith
  have hp' : β₁ + β₂ - α * β₁ * β₂ ≠ 0 := hpos.ne'
  have hα' : α ≠ 0 := hα.ne'
  have hΔ : 1 - (1 - α * β₁) * (1 - α * β₂) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  have hΔ' : 1 - (1 - α * β₂) * (1 - α * β₁) = α * (β₁ + β₂ - α * β₁ * β₂) := by ring
  unfold dg_fishK dg_fishS
  rw [hΔ, hΔ']
  obtain ⟨Q, hQ⟩ : ∃ Q, β₁ + β₂ - α * β₁ * β₂ = Q := ⟨_, rfl⟩
  rw [hQ] at hp' hpos ⊢
  refine ⟨by positivity, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_⟩ <;>
    field_simp <;> rw [← hQ] <;> ring

/-- (21.1) under the MPE (Miao, p. 757): `x_{t+1} = (αβ₁β₂x_t/(β₁ + β₂ − αβ₁β₂))^α`. -/
theorem eq_21_1_mpe {α β₁ β₂ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (h₁ : α * β₁ < 1) (h₂ : α * β₂ < 1) (x : ℝ) :
    dg_fishLaw α x (dg_fishK α β₁ β₂ * x) (dg_fishK α β₂ β₁ * x) =
      (α * β₁ * β₂ * x / (β₁ + β₂ - α * β₁ * β₂)) ^ α := by
  obtain ⟨-, -, h3, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  unfold dg_fishLaw
  congr 1
  have : x - dg_fishK α β₁ β₂ * x - dg_fishK α β₂ β₁ * x =
      (1 - dg_fishK α β₁ β₂ - dg_fishK α β₂ β₁) * x := by ring
  rw [this, h3]
  unfold dg_fishS
  ring

/-- The Great Fish War MPE (Miao, pp. 756–757). Let `k₁ = dg_fishK α β₁ β₂`,
`k₂ = dg_fishK α β₂ β₁` and `V_i(x) = κ_i ln x + ν_i`, `κ_i = 1/(1 − αβ_i)`. Against `c₂ = k₂x`,
every feasible catch sequence of country 1 (`c_t > 0`, `x_t − c_t − k₂x_t > 0`, (21.1)) with
convergent discounted utility yields at most `V₁(x₀)`, and `c₁ = k₁x` attains `V₁(x₀)` along
`x_{t+1} = (sx_t)^α`; symmetrically for country 2. -/
theorem dg_fish_mpe {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hβ₁1 : β₁ < 1) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    let k₁ := dg_fishK α β₁ β₂
    let k₂ := dg_fishK α β₂ β₁
    let V₁ := dg_fpV α β₁ (1 - k₂) 1
    let V₂ := dg_fpV α β₂ (1 - k₁) 1
    let xs := dg_fpPath α β₁ (1 - k₂) 1 x₀
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - c t - k₂ * x t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (c t) (k₂ * x t)) →
      Summable (fun t => β₁ ^ t * Real.log (c t)) → ∑' t, β₁ ^ t * Real.log (c t) ≤ V₁ x₀) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - k₁ * x t - c t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (k₁ * x t) (c t)) →
      Summable (fun t => β₂ ^ t * Real.log (c t)) → ∑' t, β₂ ^ t * Real.log (c t) ≤ V₂ x₀) ∧
    (∀ t, xs (t + 1) = dg_fishLaw α (xs t) (k₁ * xs t) (k₂ * xs t)) ∧
    HasSum (fun t => β₁ ^ t * Real.log (k₁ * xs t)) (V₁ x₀) ∧
    HasSum (fun t => β₂ ^ t * Real.log (k₂ * xs t)) (V₂ x₀) ∧
    dg_fpKappa α β₁ = 1 / (1 - α * β₁) ∧ dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
  intro k₁ k₂ V₁ V₂ xs
  have h₁ : α * β₁ < 1 := by nlinarith
  have h₂ : α * β₂ < 1 := by nlinarith
  obtain ⟨hk₁, hk₂, h3, hs, h5, h6, h7, h8⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  have hR₂ : 0 < 1 - k₂ := by simp only [k₂]; linarith
  have hR₁ : 0 < 1 - k₁ := by simp only [k₁]; linarith
  -- the two best-response problems have the same stock path
  have hpath : ∀ t, dg_fpPath α β₂ (1 - k₁) 1 x₀ t = xs t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        change (1 * α * β₂ * (1 - k₁) * dg_fpPath α β₂ (1 - k₁) 1 x₀ t) ^ α =
          (1 * α * β₁ * (1 - k₂) * xs t) ^ α
        rw [ih]
        congr 1
        have e : 1 * α * β₂ * (1 - k₁) = 1 * α * β₁ * (1 - k₂) := by
          simp only [k₁, k₂]; linarith
        rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro x c hx0 hfeas hlaw hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₁ h₁ hβ₁1 hR₂ one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hlaw t]; unfold dg_fishLaw dg_fpNext; congr 1; ring
  · intro x c hx0 hfeas hlaw hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₂ h₂ hβ₂1 hR₁ one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hlaw t]; unfold dg_fishLaw dg_fpNext; congr 1; ring
  · intro t
    change (1 * α * β₁ * (1 - k₂) * xs t) ^ α = _
    unfold dg_fishLaw
    congr 1
    have e : xs t - k₁ * xs t - k₂ * xs t = (1 - k₁ - k₂) * xs t := by ring
    rw [e, h3, ← h7]
    ring
  · have := dg_fp_policy_value hα hα1 hβ₁ h₁ hβ₁1 hR₂ one_pos hx₀
    convert this using 3 with t
    simp only [k₁, k₂, xs]
    rw [h5]
  · have := dg_fp_policy_value hα hα1 hβ₂ h₂ hβ₂1 hR₁ one_pos hx₀
    convert this using 3 with t
    rw [hpath]
    simp only [k₁, k₂, xs]
    rw [h6]

/-- Miao, p. 757 ("in the steady state"): under the MPE the stock converges, from any `x₀ > 0`,
to `x̄ = (αβ₁β₂/(β₁ + β₂ − αβ₁β₂))^{α/(1−α)}`. -/
theorem dg_fish_mpe_steady_state {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₁1 : β₁ < 1) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Filter.Tendsto (dg_fpPath α β₁ (1 - dg_fishK α β₂ β₁) 1 x₀) Filter.atTop
      (nhds ((α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂)) ^ (α / (1 - α)))) := by
  have h₁ : α * β₁ < 1 := by nlinarith
  have h₂ : α * β₂ < 1 := by nlinarith
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
  have hR : 0 < 1 - dg_fishK α β₂ β₁ := by
    obtain ⟨hk₁, hk₂, h3, hs, -⟩ := dg_fish_rates hα hβ₁ hβ₂ h₁ h₂
    linarith
  have := (dg_fp_path_tendsto hα hα1 hβ₁ hR one_pos hx₀).2
  have e : 1 * α * β₁ * (1 - dg_fishK α β₂ β₁) = α * β₁ * β₂ / (β₁ + β₂ - α * β₁ * β₂) := by
    have h7' := h7
    unfold dg_fishS at h7'
    rw [← h7']
    ring
  rwa [e] at this

/-- Stackelberg, the follower (Miao, p. 757, from (21.2)): with `V₂(x) = κ₂ ln x + ν₂`, `κ₂ > 0`,
the follower's best reply to a catch `c₁ < x` is `c₂ = (x − c₁)/(1 + αβ₂κ₂)`, the unique
maximiser of `ln c₂ + β₂(κ₂α ln(x − c₁ − c₂) + ν₂)` on `0 < c₂ < x − c₁`. -/
theorem dg_fish_follower_reaction {α β₂ κ₂ ν₂ x c₁ c₂ : ℝ} (hα : 0 < α) (hβ₂ : 0 < β₂)
    (hκ₂ : 0 < κ₂) (hc₁ : c₁ < x) (hc₂ : 0 < c₂) (hc₂' : c₂ < x - c₁) :
    Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂) + ν₂) ≤
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂)) + ν₂) ∧
    (c₂ ≠ (x - c₁) / (1 + α * β₂ * κ₂) →
      Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂) + ν₂) <
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂)) + ν₂)) := by
  have hK : 0 < α * β₂ * κ₂ := by positivity
  have hm := dg_log_max (sub_pos.mpr hc₁) hK hc₂ hc₂'
  constructor
  · nlinarith [hm.1]
  · intro hne
    nlinarith [hm.2 hne]

/-- Miao, p. 757: the printed follower rule `c₂ = αβ₂κ₂(x − c₁)/(1 + αβ₂κ₂)` is wrong. For
`α = β₂ = 1/2`, `κ₂ = 1/(1 − αβ₂) = 4/3`, `x = 2`, `c₁ = 1` it gives `c₂ = 1/4`, which violates
(21.2) (`1/c₂ = 4 ≠ αβ₂κ₂/(x − c₁ − c₂) = 4/9`) and does strictly worse than the correct
reply `(x − c₁)/(1 + αβ₂κ₂) = 3/4`. -/
theorem dg_fish_follower_printed_false :
    let α : ℝ := 1 / 2
    let β₂ : ℝ := 1 / 2
    let κ₂ : ℝ := 4 / 3
    let x : ℝ := 2
    let c₁ : ℝ := 1
    let c₂ : ℝ := α * β₂ * κ₂ / (1 + α * β₂ * κ₂) * (x - c₁)
    κ₂ = 1 / (1 - α * β₂) ∧ c₂ = 1 / 4 ∧ 1 / c₂ ≠ α * β₂ * κ₂ / (x - c₁ - c₂) ∧
    (x - c₁) / (1 + α * β₂ * κ₂) = 3 / 4 ∧
    Real.log c₂ + β₂ * (κ₂ * α * Real.log (x - c₁ - c₂)) <
      Real.log ((x - c₁) / (1 + α * β₂ * κ₂)) +
        β₂ * (κ₂ * α * Real.log (x - c₁ - (x - c₁) / (1 + α * β₂ * κ₂))) := by
  intro α β₂ κ₂ x c₁ c₂
  have hc₂ : c₂ = 1 / 4 := by simp only [c₂, α, β₂, κ₂, x, c₁]; norm_num
  have hstar : (x - c₁) / (1 + α * β₂ * κ₂) = 3 / 4 := by
    simp only [α, β₂, κ₂, x, c₁]; norm_num
  refine ⟨by simp only [α, β₂, κ₂]; norm_num, hc₂, ?_, hstar, ?_⟩
  · rw [hc₂]; simp only [α, β₂, κ₂, x, c₁]; norm_num
  · have := (dg_fish_follower_reaction (α := α) (β₂ := β₂) (κ₂ := κ₂) (ν₂ := 0) (x := x)
      (c₁ := c₁) (c₂ := c₂) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hc₂]; norm_num) (by rw [hc₂]; norm_num)).2 (by rw [hc₂, hstar]; norm_num)
    simpa using this

/-- Stackelberg, the leader (Miao, p. 757): if the follower replies `c₂ = (x − c₁)/(1 + K₂)`,
`K₂ > 0`, then `x − c₁ − c₂ = K₂(x − c₁)/(1 + K₂)` and the leader's objective
`ln c₁ + β₁(κ₁α ln(x − c₁ − c₂) + ν₁)` has the unique maximiser `c₁ = x/(1 + αβ₁κ₁)`, the
first-order condition `1/c₁ = αβ₁κ₁/(x − c₁)`. The same holds for the printed follower rule,
which is also proportional to `x − c₁`. -/
theorem dg_fish_leader_foc {α β₁ κ₁ ν₁ K₂ x c₁ : ℝ} (hα : 0 < α) (hβ₁ : 0 < β₁)
    (hκ₁ : 0 < κ₁) (hK₂ : 0 < K₂) (hc₁ : 0 < c₁) (hcx : c₁ < x) :
    (Real.log c₁ + β₁ * (κ₁ * α * Real.log (x - c₁ - (x - c₁) / (1 + K₂)) + ν₁) ≤
      Real.log (x / (1 + α * β₁ * κ₁)) + β₁ * (κ₁ * α * Real.log (x - x / (1 + α * β₁ * κ₁) -
        (x - x / (1 + α * β₁ * κ₁)) / (1 + K₂)) + ν₁)) ∧
    (c₁ ≠ x / (1 + α * β₁ * κ₁) →
      Real.log c₁ + β₁ * (κ₁ * α * Real.log (x - c₁ - (x - c₁) / (1 + K₂)) + ν₁) <
      Real.log (x / (1 + α * β₁ * κ₁)) + β₁ * (κ₁ * α * Real.log (x - x / (1 + α * β₁ * κ₁) -
        (x - x / (1 + α * β₁ * κ₁)) / (1 + K₂)) + ν₁)) := by
  have hx : 0 < x := hc₁.trans hcx
  have hK : 0 < α * β₁ * κ₁ := by positivity
  have hθ : 0 < K₂ / (1 + K₂) := by positivity
  have hrem : ∀ c, c < x → x - c - (x - c) / (1 + K₂) = K₂ / (1 + K₂) * (x - c) := by
    intro c _; field_simp; ring
  have hlog : ∀ c, c < x → Real.log (x - c - (x - c) / (1 + K₂)) =
      Real.log (K₂ / (1 + K₂)) + Real.log (x - c) := by
    intro c hc
    rw [hrem c hc, Real.log_mul hθ.ne' (by linarith)]
  have hstar : x / (1 + α * β₁ * κ₁) < x := div_lt_self hx (by linarith)
  have hm := dg_log_max hx hK hc₁ hcx
  rw [hlog c₁ hcx, hlog _ hstar]
  constructor
  · nlinarith [hm.1]
  · intro hne
    nlinarith [hm.2 hne]

/-- Stackelberg, the leader (Miao, p. 757): with the follower's equilibrium reply
`c₂ = (1 − αβ₂)(x − c₁)` (`K₂ = αβ₂/(1 − αβ₂)`), the leader's problem is the fishing problem with
`R = 1`, `θ = αβ₂`; its value is `κ₁ ln x + ν₁` with `κ₁ = 1/(1 − αβ₁)` and its rule is
`c₁ = (1 − αβ₁)x = x/(1 + αβ₁κ₁)`, optimal among all feasible sequences. -/
theorem dg_fish_leader {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₁1 : β₁ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∀ x : ℝ, 0 < x → x / (1 + α * β₁ * dg_fpKappa α β₁) = (1 - α * β₁) * x) ∧
    (∀ x c₁ : ℝ, c₁ < x → dg_fishLaw α x c₁ ((1 - α * β₂) * (x - c₁)) =
      dg_fpNext α 1 (α * β₂) x c₁) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ c t < x t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) (c t) ((1 - α * β₂) * (x t - c t))) →
      Summable (fun t => β₁ ^ t * Real.log (c t)) →
      ∑' t, β₁ ^ t * Real.log (c t) ≤ dg_fpV α β₁ 1 (α * β₂) x₀) ∧
    HasSum (fun t => β₁ ^ t * Real.log ((1 - α * β₁) * dg_fpPath α β₁ 1 (α * β₂) x₀ t))
      (dg_fpV α β₁ 1 (α * β₂) x₀) := by
  have h₁ : α * β₁ < 1 := by nlinarith
  have hθ : 0 < α * β₂ := by positivity
  have hlaw : ∀ x c₁ : ℝ, c₁ < x → dg_fishLaw α x c₁ ((1 - α * β₂) * (x - c₁)) =
      dg_fpNext α 1 (α * β₂) x c₁ := by
    intro x c₁ _
    unfold dg_fishLaw dg_fpNext
    congr 1
    ring
  refine ⟨?_, hlaw, ?_, ?_⟩
  · intro x _
    have : 1 + α * β₁ * dg_fpKappa α β₁ = 1 / (1 - α * β₁) := by
      rw [dg_fpKappa_eq h₁]; rfl
    rw [this]
    have : 1 - α * β₁ ≠ 0 := by linarith
    field_simp
  · intro x c hx0 hfeas hl hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₁ h₁ hβ₁1 one_pos hθ x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · rw [one_mul]; exact (hfeas t).2
    · rw [hl t, hlaw _ _ (hfeas t).2]
  · have := dg_fp_policy_value hα hα1 hβ₁ h₁ hβ₁1 one_pos hθ hx₀
    simpa using this

/-- **Exercise 21.3** (Miao, p. 771): country 2's equilibrium catch in the linear Stackelberg
equilibrium. Given the leader's rule `c₁ = (1 − αβ₁)x`, the follower's problem is the fishing
problem with `R = αβ₁`, `θ = 1`: its value is `κ₂ ln x + ν₂` with `κ₂ = 1/(1 − αβ₂)`, and its
catch `c₂ = αβ₁(1 − αβ₂)x` is optimal among all feasible sequences. This catch is the follower's
reaction `(x − c₁)/(1 + αβ₂κ₂)` at `c₁ = (1 − αβ₁)x`, and the stock then evolves as
`x_{t+1} = (α²β₁β₂x_t)^α`. -/
theorem ex_21_3 {α β₁ β₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∀ x : ℝ, (x - (1 - α * β₁) * x) / (1 + α * β₂ * dg_fpKappa α β₂) =
      (1 - α * β₂) * (α * β₁) * x) ∧
    (∀ x : ℝ, dg_fishLaw α x ((1 - α * β₁) * x) ((1 - α * β₂) * (α * β₁) * x) =
      (α * α * β₁ * β₂ * x) ^ α) ∧
    (∀ x c : ℕ → ℝ, x 0 = x₀ → (∀ t, 0 < c t ∧ 0 < x t - (1 - α * β₁) * x t - c t) →
      (∀ t, x (t + 1) = dg_fishLaw α (x t) ((1 - α * β₁) * x t) (c t)) →
      Summable (fun t => β₂ ^ t * Real.log (c t)) →
      ∑' t, β₂ ^ t * Real.log (c t) ≤ dg_fpV α β₂ (α * β₁) 1 x₀) ∧
    HasSum (fun t => β₂ ^ t * Real.log ((1 - α * β₂) * (α * β₁) *
      dg_fpPath α β₂ (α * β₁) 1 x₀ t)) (dg_fpV α β₂ (α * β₁) 1 x₀) ∧
    dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
  have h₂ : α * β₂ < 1 := by nlinarith
  have hR : 0 < α * β₁ := by positivity
  refine ⟨?_, ?_, ?_, dg_fp_policy_value hα hα1 hβ₂ h₂ hβ₂1 hR one_pos hx₀, rfl⟩
  · intro x
    have : 1 + α * β₂ * dg_fpKappa α β₂ = 1 / (1 - α * β₂) := by
      rw [dg_fpKappa_eq h₂]; rfl
    rw [this]
    have : 1 - α * β₂ ≠ 0 := by linarith
    field_simp
    ring
  · intro x
    unfold dg_fishLaw
    congr 1
    ring
  · intro x c hx0 hfeas hl hsum
    rw [← hx0]
    refine dg_fp_optimal hα hβ₂ h₂ hβ₂1 hR one_pos x c (fun t => ⟨(hfeas t).1, ?_⟩)
      (fun t => ?_) hsum
    · linarith [(hfeas t).2]
    · rw [hl t]; unfold dg_fishLaw dg_fpNext; congr 1; ring

/-- `ln c₁ + ln c₂ ≤ 2 ln((c₁ + c₂)/2)` for positive catches, with equality iff `c₁ = c₂`. -/
theorem dg_log_add_le {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    Real.log c₁ + Real.log c₂ ≤ 2 * Real.log ((c₁ + c₂) / 2) := by
  rw [← Real.log_mul h₁.ne' h₂.ne', ← Real.log_rpow (by positivity)]
  refine Real.log_le_log (mul_pos h₁ h₂) ?_
  rw [show ((c₁ + c₂) / 2) ^ (2 : ℝ) = ((c₁ + c₂) / 2) ^ (2 : ℕ) by norm_cast]
  nlinarith [sq_nonneg (c₁ - c₂)]

/-- The cooperative solution for symmetric countries (`β₁ = β₂ = β`; not carried out in the text).
With `W(x) = 2V(x) − 2 ln 2/(1 − β)`, `V` the value of the fishing problem with `R = θ = 1`,
every feasible pair satisfies `ln c₁ + ln c₂ + βW((x − c₁ − c₂)^α) ≤ W(x)`, with equality at
`c₁ = c₂ = (1 − αβ)x/2`: the planner catches `(1 − αβ)x` in total. -/
theorem dg_fish_cooperative {α β x c₁ c₂ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hx : 0 < x) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hs : 0 < x - c₁ - c₂) :
    let W : ℝ → ℝ := fun y => 2 * dg_fpV α β 1 1 y - 2 * Real.log 2 / (1 - β)
    Real.log c₁ + Real.log c₂ + β * W (dg_fishLaw α x c₁ c₂) ≤ W x ∧
    Real.log ((1 - α * β) * x / 2) + Real.log ((1 - α * β) * x / 2) +
      β * W (dg_fishLaw α x ((1 - α * β) * x / 2) ((1 - α * β) * x / 2)) = W x := by
  intro W
  have h1 : 0 < 1 - α * β := by linarith
  have hb : 1 - β ≠ 0 := by linarith
  have hlaw : ∀ a b : ℝ, dg_fishLaw α x a b = dg_fpNext α 1 1 x (a + b) := by
    intro a b; unfold dg_fishLaw dg_fpNext; congr 1; ring
  have hC : 0 < c₁ + c₂ := by linarith
  have hb1 := dg_fp_bellman hα hβ hab hβ1 one_pos one_pos hx hC (by linarith)
  have hb2 := dg_fp_bellman_eq hα hβ hab hβ1 one_pos one_pos hx
  have hlog2 := dg_log_add_le hc₁ hc₂
  have hl2 : Real.log ((c₁ + c₂) / 2) = Real.log (c₁ + c₂) - Real.log 2 :=
    Real.log_div hC.ne' two_ne_zero
  unfold dg_fpRHS at hb1 hb2
  simp only [W]
  rw [hlaw, hlaw]
  have e : (1 - α * β) * x / 2 + (1 - α * β) * x / 2 = (1 - α * β) * 1 * x := by ring
  rw [e]
  have hl3 : Real.log ((1 - α * β) * x / 2) = Real.log ((1 - α * β) * 1 * x) - Real.log 2 := by
    rw [mul_one]; exact Real.log_div (by positivity) two_ne_zero
  have hk : 2 * Real.log 2 / (1 - β) = 2 * Real.log 2 + β * (2 * Real.log 2 / (1 - β)) := by
    field_simp; ring
  constructor
  · nlinarith
  · rw [hl3]
    nlinarith

/-- Overfishing (supplementary to Miao, §21.3): with `β₁ = β₂ = β`, the MPE total catch
`(k₁ + k₂)x = 2(1 − αβ)x/(2 − αβ)` exceeds the cooperative catch `(1 − αβ)x`, and the MPE
saving rate `αβ/(2 − αβ)` is below the cooperative `αβ`, so the steady-state stock is lower. -/
theorem dg_fish_overfishing {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    dg_fishK α β β + dg_fishK α β β = 2 * (1 - α * β) / (2 - α * β) ∧
    1 - α * β < dg_fishK α β β + dg_fishK α β β ∧
    dg_fishS α β β = α * β / (2 - α * β) ∧ dg_fishS α β β < α * β ∧
    dg_fishS α β β ^ (α / (1 - α)) < (α * β) ^ (α / (1 - α)) := by
  have hab : α * β < 1 := by nlinarith
  have hab0 : 0 < α * β := by positivity
  have h2 : 0 < 2 - α * β := by linarith
  have hK : dg_fishK α β β = (1 - α * β) / (2 - α * β) := by
    unfold dg_fishK
    have : 1 - (1 - α * β) * (1 - α * β) = α * β * (2 - α * β) := by ring
    rw [this]
    field_simp
  have hS : dg_fishS α β β = α * β / (2 - α * β) := by
    unfold dg_fishS
    have : β + β - α * β * β = β * (2 - α * β) := by ring
    rw [this]
    field_simp
  have hlt : α * β / (2 - α * β) < α * β := by
    rw [div_lt_iff₀ h2]; nlinarith
  refine ⟨by rw [hK]; ring, ?_, hS, by rw [hS]; exact hlt, ?_⟩
  · rw [hK, ← two_mul, mul_div_assoc', lt_div_iff₀ h2]
    nlinarith
  · rw [hS]
    exact Real.rpow_lt_rpow (by positivity) hlt (div_pos hα (by linarith))

end Miao.DynamicGames
