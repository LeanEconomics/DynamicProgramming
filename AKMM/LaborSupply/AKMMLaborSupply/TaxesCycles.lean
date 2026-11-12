/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.BalancedGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Taxes, income effects, business cycles and human capital

AKMM, §12.6–12.7, pp. 353–359.

* **Prescott** (12.38)–(12.39): from the household's intratemporal conditions
  `1/C = μ(1 + τ_c)`, `ψL^{1/γ} = μ(1 − τ_ℓ)w` and `w = (1 − α)Y/L` (`bg_mpl_eq`),
  `L = [(1 − τ)(1 − α)/(χψ)]^{γ/(1+γ)}` with `τ = (τ_ℓ + τ_c)/(1 + τ_c)` and `χ = C/Y`
  (`eq_12_39`). The U.S./Italy ratio is `[(0.60/0.81)/(0.36/0.69)]^{γ/(1+γ)}`; at `γ = 1` it lies
  in `(1.19, 1.20)`, not `1.42`; `1.42` is the limit `γ → ∞` (`eq_12_39_us_italy`).
* **Income effects** (§12.6.1): in the benchmark the ratio of the income to the substitution
  effect is `(ε^H − ε^M)/ε^H = σ(1 − s_I)` (`ti_effect_ratio`). With subsistence consumption
  `log(C − C̄)` the problem is the benchmark at `σ = 1` with income `−C̄`; the ratio is
  `C/(C − C̄) > 1`, decreasing in `C` and tending to `1` (`ti_subsistence`), and hours fall with
  the wage (`ti_subsistence_marshallian`). With `σ > 1` and no non-labour income the ratio is
  `σ > 1` at every wage, and along wages growing by `G` hours fall at the constant factor
  `G^{(1−σ)/(1/γ+σ)}` (`ti_sigma_gt_one`).
* **Business cycles** (12.40): `log L_t = const − (γ/(1 + γ)) log(C_t/Y_t)` (`eq_12_40`); the
  coefficient is `1/2` at `γ = 1` and tends to `1` as `γ → ∞` (`ti_cycle_coefficient`); without
  capital (`Y = ZL`, `C = Y`) hours do not depend on productivity (`ti_no_capital`).
* **Imai–Keane** (12.41): with `w_t = (1 + κΣ_{j<t}ℓ_j)w₀`, the marginal effect of `ℓ_s` on the
  present value of earnings is `R^{−s}(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`
  (`ik_marginal_earnings`), and the first-order conditions of the lifetime problem give (12.41)
  (`eq_12_41`).

Departure: (12.41) is derived for perfect foresight (no expectation operator).
-/

namespace AKMM.LaborSupply

open Filter Topology

/-! ### Prescott (2004) -/

/-- With Cobb–Douglas technology the marginal product of labour is `(1 − α)Y/L`. -/
theorem bg_mpl_eq {α Z K L : ℝ} (hL : 0 < L) :
    bgMPL α Z K L = (1 - α) * bgF α Z K L / L := by
  unfold bgMPL bgF
  have e : L ^ (1 - α) = L * L ^ (-α) := by
    rw [show 1 - α = 1 + -α by ring, Real.rpow_add hL, Real.rpow_one]
  rw [e]
  field_simp

/-- AKMM, (12.39), p. 354: from `1/C = μ(1 + τ_c)`, `ψL^{1/γ} = μ(1 − τ_ℓ)w` and
`w = (1 − α)Y/L`, with `χ = C/Y` and `τ = (τ_ℓ + τ_c)/(1 + τ_c)` (so that
`1 − τ = (1 − τ_ℓ)/(1 + τ_c)`): `L = [(1 − τ)(1 − α)/(χψ)]^{γ/(1+γ)}`. -/
theorem eq_12_39 {ψ γ α τl τc μ C Y L w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hτc : 0 < 1 + τc)
    (hC : 0 < C) (hY : 0 < Y) (hL : 0 < L)
    (hc : 1 / C = μ * (1 + τc)) (hl : ψ * L ^ (1 / γ) = μ * (1 - τl) * w)
    (hw : w = (1 - α) * Y / L) :
    1 - (τl + τc) / (1 + τc) = (1 - τl) / (1 + τc) ∧
      L = ((1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ)) ^ (γ / (1 + γ)) := by
  have htax : 1 - (τl + τc) / (1 + τc) = (1 - τl) / (1 + τc) := by field_simp; ring
  refine ⟨htax, ?_⟩
  have hμ : μ = 1 / (C * (1 + τc)) := by
    rw [eq_div_iff (by positivity)]
    have := hc; field_simp at this; linarith
  have key : L ^ ((1 + γ) / γ) = (1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ) := by
    have e : L ^ ((1 + γ) / γ) = L * L ^ (1 / γ) := by
      rw [show (1 + γ) / γ = 1 + 1 / γ by rw [add_div, div_self hγ.ne', add_comm],
        Real.rpow_add hL, Real.rpow_one]
    have hl' : L ^ (1 / γ) = μ * (1 - τl) * w / ψ := by rw [← hl]; field_simp
    rw [e, hl', hμ, hw, htax]
    field_simp
  have hpos : 0 < (1 - (τl + τc) / (1 + τc)) * (1 - α) / (C / Y * ψ) := by
    rw [← key]; exact Real.rpow_pos_of_pos hL _
  rw [← key, ← Real.rpow_mul hL.le, show (1 + γ) / γ * (γ / (1 + γ)) = 1 by field_simp,
    Real.rpow_one]

/-- AKMM, p. 354, **the U.S./Italy ratio, corrected**. By (12.39) with common `α, ψ, γ`, hours
in two countries are in the ratio `[((1 − τ₁)/χ₁)/((1 − τ₂)/χ₂)]^{γ/(1+γ)}`. With
`τ = 0.40, 0.64` and `χ = 0.81, 0.69` the base `r = (0.60/0.81)/(0.36/0.69)` lies in
`(1.41, 1.43)`; at `γ = 1` the ratio is `r^{1/2} ∈ (1.19, 1.20)`, not the printed `1.42`, which
is the limit as `γ → ∞`. -/
theorem eq_12_39_us_italy :
    (1.41 : ℝ) < (0.60 / 0.81) / (0.36 / 0.69) ∧ (0.60 / 0.81) / (0.36 / 0.69) < (1.43 : ℝ) ∧
      (1.19 : ℝ) < ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ ((1 : ℝ) / (1 + 1)) ∧
      ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ ((1 : ℝ) / (1 + 1)) < 1.20 ∧
      Tendsto (fun γ : ℝ => ((0.60 / 0.81) / (0.36 / 0.69) : ℝ) ^ (γ / (1 + γ))) atTop
        (𝓝 ((0.60 / 0.81) / (0.36 / 0.69))) := by
  set r : ℝ := (0.60 / 0.81) / (0.36 / 0.69) with hr
  have hr1 : (1.41 : ℝ) < r := by rw [hr]; norm_num
  have hr2 : r < (1.43 : ℝ) := by rw [hr]; norm_num
  have hsq : r ^ ((1 : ℝ) / (1 + 1)) = Real.sqrt r := by
    rw [show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  refine ⟨hr1, hr2, ?_, ?_, ?_⟩
  · rw [hsq, Real.lt_sqrt (by norm_num)]
    rw [hr]; norm_num
  · rw [hsq, Real.sqrt_lt' (by norm_num)]
    rw [hr]; norm_num
  · have hexp : Tendsto (fun γ : ℝ => γ / (1 + γ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun γ : ℝ => 1 - 1 / (1 + γ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_left _ _ tendsto_id))
      rw [sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with γ hγ
      have : 0 < 1 + γ := by linarith
      field_simp; ring
    have hc := ((continuous_const.rpow continuous_id
      (fun _ => Or.inl (by rw [hr]; norm_num : (0 : ℝ) < r).ne')).tendsto (1 : ℝ)).comp hexp
    simpa [Function.comp_def, Real.rpow_one] using hc

/-! ### Income and substitution effects -/

/-- AKMM, pp. 355–356: in the benchmark the size of the income effect relative to the
substitution effect, `(ε^H − ε^M)/ε^H`, is `σ(1 − s_I)`. -/
theorem ti_effect_ratio {γ σ sI : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (hs : sI < 1) :
    (1 / (1 / γ + σ * (1 - sI)) - (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI))) /
      (1 / (1 / γ + σ * (1 - sI))) = σ * (1 - sI) := by
  have hden : 0 < 1 / γ + σ * (1 - sI) := by
    have : 0 ≤ σ * (1 - sI) := mul_nonneg hσ (by linarith)
    have : 0 < 1 / γ := by positivity
    linarith
  have e : 1 / (1 / γ + σ * (1 - sI)) - (1 - σ * (1 - sI)) / (1 / γ + σ * (1 - sI)) =
      σ * (1 - sI) / (1 / γ + σ * (1 - sI)) := by ring
  rw [e, div_div_div_cancel_right₀ hden.ne', div_one]

/-- AKMM, p. 355, **subsistence consumption**: `log(C − C̄)` with `C = wL` is the benchmark with
`σ = 1` and non-labour income `−C̄`, so `s_I = −C̄/(C − C̄)` and the income/substitution ratio
`σ(1 − s_I) = C/(C − C̄)` exceeds `1`, decreases in `C` and tends to `1` as `C → ∞`. -/
theorem ti_subsistence {Cbar : ℝ} (hCbar : 0 < Cbar) :
    (∀ C, Cbar < C → 1 * (1 - -Cbar / (C - Cbar)) = C / (C - Cbar)) ∧
      (∀ C, Cbar < C → 1 < C / (C - Cbar)) ∧
      StrictAntiOn (fun C => C / (C - Cbar)) (Set.Ioi Cbar) ∧
      Tendsto (fun C => C / (C - Cbar)) atTop (𝓝 1) := by
  refine ⟨fun C hC => ?_, fun C hC => ?_, fun x hx y hy hxy => ?_, ?_⟩
  · have : C - Cbar ≠ 0 := by linarith
    field_simp; ring
  · rw [one_lt_div (by linarith)]; linarith
  · have hx' : 0 < x - Cbar := sub_pos.2 hx
    have hy' : 0 < y - Cbar := sub_pos.2 hy
    simp only
    rw [div_lt_div_iff₀ hy' hx']
    nlinarith
  · have h : Tendsto (fun C => 1 + Cbar * (1 / (C - Cbar))) atTop (𝓝 (1 + Cbar * 0)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_id)).const_mul Cbar)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop Cbar] with C hC
    have : C - Cbar ≠ 0 := by linarith
    field_simp; ring

/-- AKMM, p. 355: with subsistence consumption, **hours fall with the wage**: along `w(s) = we^s`
with (12.1) for `u = log` and income `−C̄` near `0`, `d log L/d log w = −C̄/(C + (C − C̄)/γ) < 0`,
`C = wL`. -/
theorem ti_subsistence_marshallian {ψ γ w Cbar L' : ℝ} {L : ℝ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hw : 0 < w) (hCbar : 0 < Cbar) (hL : 0 < L 0) (hc : 0 < w * L 0 + -Cbar)
    (hdL : HasDerivAt L L' 0)
    (hfoc : ∀ᶠ s in 𝓝 (0 : ℝ), ψ * L s ^ (1 / γ) /
      (w * Real.exp s * L s + -Cbar) ^ (-(1 : ℝ)) = w * Real.exp s) :
    HasDerivAt (fun s => Real.log (L s))
      (-Cbar / (w * L 0 + (w * L 0 - Cbar) / γ)) 0 ∧
      -Cbar / (w * L 0 + (w * L 0 - Cbar) / γ) < 0 := by
  have h := eq_12_3 hψ hγ zero_le_one hw hL hc hdL hfoc
  have hc' : w * L 0 - Cbar ≠ 0 := by linarith
  have hD : 0 < w * L 0 + (w * L 0 - Cbar) / γ := by
    have : 0 < (w * L 0 - Cbar) / γ := div_pos (by linarith) hγ
    have : 0 < w * L 0 := by positivity
    linarith
  refine ⟨h.congr_deriv ?_, div_neg_of_neg_of_pos (by linarith) hD⟩
  rw [div_eq_div_iff (by
    have : 1 - -Cbar / (w * L 0 + -Cbar) = w * L 0 / (w * L 0 - Cbar) := by
      rw [← sub_eq_add_neg]; field_simp; ring
    rw [this]; positivity) hD.ne']
  rw [← sub_eq_add_neg]
  field_simp
  ring

/-- AKMM, p. 355, **`σ > 1`** (Boppart–Krusell): with no non-labour income the
income/substitution ratio is `σ > 1` at every wage; the optimal hours
`ℓ(w) = (w^{1−σ}/ψ)^{1/(1/γ+σ)}` solve (12.1) with `I = 0`, and along wages `Gᵗw₀` hours change
by the constant factor `G^{(1−σ)/(1/γ+σ)} < 1` (`G > 1`): they fall at a constant rate. -/
theorem ti_sigma_gt_one {ψ γ σ G w : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hσ : 1 < σ) (hG : 1 < G)
    (hw : 0 < w) :
    1 < σ * (1 - 0) ∧
      ψ * ((w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹) ^ (1 / γ) /
        (w * (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ + 0) ^ (-σ) = w ∧
      ((G * w) ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ =
        G ^ ((1 - σ) / (1 / γ + σ)) * (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹ ∧
      G ^ ((1 - σ) / (1 / γ + σ)) < 1 := by
  have he : 0 < 1 / γ + σ := by have : 0 < 1 / γ := by positivity
                                linarith
  have hk : 0 < w ^ (1 - σ) / ψ := by positivity
  set l := (w ^ (1 - σ) / ψ) ^ (1 / γ + σ)⁻¹
  have hl : 0 < l := Real.rpow_pos_of_pos hk _
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [add_zero, st_foc_form (by positivity), Real.mul_rpow hw.le hl.le]
    have h1 : l ^ (1 / γ) * l ^ σ = w ^ (1 - σ) / ψ := by
      rw [← Real.rpow_add hl, Real.rpow_inv_rpow hk.le he.ne']
    have h3 : w ^ σ * w ^ (1 - σ) = w := by
      rw [← Real.rpow_add hw, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    calc ψ * l ^ (1 / γ) * (w ^ σ * l ^ σ) = ψ * w ^ σ * (l ^ (1 / γ) * l ^ σ) := by ring
      _ = w := by
        rw [h1]
        have h4 : ψ * w ^ σ * (w ^ (1 - σ) / ψ) = w ^ σ * w ^ (1 - σ) := by field_simp
        rw [h4, h3]
  · have hG0 : 0 < G := by linarith
    rw [Real.mul_rpow hG0.le hw.le, mul_div_assoc, Real.mul_rpow (by positivity) hk.le,
      ← Real.rpow_mul hG0.le, div_eq_mul_inv]
    rfl
  · exact Real.rpow_lt_one_of_one_lt_of_neg hG (div_neg_of_neg_of_pos (by linarith) he)

/-! ### Business cycles -/

/-- AKMM, (12.40), p. 356: when (12.39) holds with a time-varying consumption-output ratio
`χ_t`, `log L_t = const − (γ/(1 + γ)) log(C_t/Y_t)` with
`const = (γ/(1 + γ)) log((1 − τ)(1 − α)/ψ)`. -/
theorem eq_12_40 {ψ γ α τ χ L : ℝ} (hψ : 0 < ψ) (hα : α < 1) (hτ : τ < 1)
    (hχ : 0 < χ) (hL : L = ((1 - τ) * (1 - α) / (χ * ψ)) ^ (γ / (1 + γ))) :
    Real.log L = γ / (1 + γ) * Real.log ((1 - τ) * (1 - α) / ψ) - γ / (1 + γ) * Real.log χ := by
  have h1 : 0 < (1 - τ) * (1 - α) := mul_pos (by linarith) (by linarith)
  rw [hL, Real.log_rpow (by positivity), show (1 - τ) * (1 - α) / (χ * ψ) =
    (1 - τ) * (1 - α) / ψ / χ by field_simp, Real.log_div (by positivity) hχ.ne']
  ring

/-- AKMM, p. 356: the coefficient `γ/(1 + γ)` of (12.40) is `1/2` at `γ = 1` (half the
infinite-elasticity response) and tends to `1` as `γ → ∞` (indivisible labour). -/
theorem ti_cycle_coefficient :
    (1 : ℝ) / (1 + 1) = 1 / 2 ∧ Tendsto (fun γ : ℝ => γ / (1 + γ)) atTop (𝓝 1) := by
  refine ⟨by norm_num, ?_⟩
  have h1 : Tendsto (fun γ : ℝ => 1 - 1 / (1 + γ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_id))
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with γ hγ
  have : 0 < 1 + γ := by linarith
  field_simp; ring

/-- AKMM, p. 356, **no capital**: with `Y = ZL` (so `w = Z`) and `C = Y`, the intratemporal
condition `ψL^{1/γ} = (1 − τ)w/C` gives `L = ((1 − τ)/ψ)^{γ/(1+γ)}` for every productivity
`Z > 0`: hours are invariant to productivity. -/
theorem ti_no_capital {ψ γ τ Z L : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) (hZ : 0 < Z)
    (hL : 0 < L) (hfoc : ψ * L ^ (1 / γ) = (1 - τ) * Z / (Z * L)) :
    L = ((1 - τ) / ψ) ^ (γ / (1 + γ)) := by
  have key : L ^ ((1 + γ) / γ) = (1 - τ) / ψ := by
    rw [show (1 + γ) / γ = 1 + 1 / γ by rw [add_div, div_self hγ.ne', add_comm],
      Real.rpow_add hL, Real.rpow_one]
    have : L ^ (1 / γ) = (1 - τ) / (ψ * L) := by
      rw [eq_div_iff (by positivity)]
      have h2 : ψ * L ^ (1 / γ) = (1 - τ) / L := by rw [hfoc]; field_simp
      rw [show L ^ (1 / γ) * (ψ * L) = ψ * L ^ (1 / γ) * L by ring, h2]
      field_simp
    rw [this]; field_simp
  rw [← key, ← Real.rpow_mul hL.le, show (1 + γ) / γ * (γ / (1 + γ)) = 1 by field_simp,
    Real.rpow_one]

/-! ### Imai–Keane: dynamic returns to work -/

/-- The wage with learning by doing, `w_t = (1 + κΣ_{j<t}ℓ_j)w₀` (AKMM, p. 357). -/
noncomputable def ikWage (κ w₀ : ℝ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 + κ * ∑ j ∈ Finset.range t, l j) * w₀

/-- The present value of after-tax earnings `Σ_{t≤T} R^{−t}(1 − τ)w_tℓ_t`. -/
noncomputable def ikEarnings (R τ κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), (R⁻¹) ^ t * ((1 - τ) * ikWage κ w₀ l t * l t)

/-- AKMM, p. 357, **the return to an hour of work**: for `s ≤ T`, the derivative of the present
value of earnings with respect to `ℓ_s` is
`R^{−s}(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`: the wage plus the human-capital term. -/
theorem ik_marginal_earnings {R τ κ w₀ : ℝ} {T s : ℕ} (hs : s ≤ T) (l : ℕ → ℝ) :
    HasDerivAt (fun x => ikEarnings R τ κ w₀ T (Function.update l s x))
      ((R⁻¹) ^ s * ((1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
        ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)))) (l s) := by
  classical
  have hu : ∀ j, HasDerivAt (fun x => Function.update l s x j) (if j = s then 1 else 0) (l s) := by
    intro j
    by_cases hj : j = s
    · subst hj
      simp only [Function.update_self, ↓reduceIte]
      exact hasDerivAt_id _
    · simp only [Function.update_of_ne hj, hj, ↓reduceIte]
      exact hasDerivAt_const _ _
  have hw : ∀ t, HasDerivAt (fun x => ikWage κ w₀ (Function.update l s x) t)
      ((κ * ∑ j ∈ Finset.range t, (if j = s then (1 : ℝ) else 0)) * w₀) (l s) := by
    intro t
    have := ((HasDerivAt.fun_sum (u := Finset.range t) (fun j _ => hu j)).const_mul κ).const_add 1
    exact this.mul_const w₀ |>.congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (u := Finset.range (T + 1)) (fun t _ =>
    ((((hw t).const_mul (1 - τ)).mul (hu t)).const_mul ((R⁻¹) ^ t)))
  refine hsum.congr_deriv ?_
  simp only [Function.update_eq_self]
  -- split the sum
  have hind : ∀ t, (∑ j ∈ Finset.range t, (if j = s then (1 : ℝ) else 0)) =
      if s < t then 1 else 0 := by
    intro t
    rw [Finset.sum_ite_eq' (Finset.range t) s (fun _ => (1 : ℝ))]
    simp only [Finset.mem_range]
  simp only [hind]
  have hsplit : ∀ t ∈ Finset.range (T + 1),
      (R⁻¹) ^ t * ((1 - τ) * ((κ * (if s < t then (1 : ℝ) else 0)) * w₀) * l t +
        (1 - τ) * ikWage κ w₀ l t * (if t = s then 1 else 0)) =
      (if s < t then (R⁻¹) ^ t * ((1 - τ) * κ * w₀ * l t) else 0) +
        (if t = s then (R⁻¹) ^ t * ((1 - τ) * ikWage κ w₀ l t) else 0) := by
    intro t _
    split_ifs <;> ring
  have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (by omega)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (T + 1)) s]
  simp only [hmem, ↓reduceIte]
  -- reindex the human-capital term
  have hT : T + 1 = (s + 1) + (T - s) := by omega
  rw [hT, Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range (s + 1),
      (if s < x then (R⁻¹) ^ x * ((1 - τ) * κ * w₀ * l x) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_range] at hx
      have : ¬ s < x := by omega
      simp only [this, ↓reduceIte]
  rw [hzero, zero_add]
  have hterm : ∀ j ∈ Finset.range (T - s),
      (if s < s + 1 + j then (R⁻¹) ^ (s + 1 + j) * ((1 - τ) * κ * w₀ * l (s + 1 + j)) else 0) =
        (R⁻¹) ^ s * ((1 - τ) * κ * w₀) * ((R⁻¹) ^ (j + 1) * l (s + j + 1)) := by
    intro j _
    have h1 : s < s + 1 + j := by omega
    have h2 : (R⁻¹) ^ (s + j + 1) = (R⁻¹) ^ s * (R⁻¹) ^ (j + 1) := by rw [← pow_add, add_assoc]
    simp only [h1, ↓reduceIte]
    rw [show s + 1 + j = s + j + 1 by ring, h2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- AKMM, (12.41), p. 357: with perfect foresight, the lifetime problem's first-order conditions
with multiplier `μ` on the present-value budget, `β^s c_s^{−σ} = μR^{−s}` and
`β^sψℓ_s^{1/γ} = μ·∂(PV earnings)/∂ℓ_s`, give, with `λ_s = c_s^{−σ}`,
`ψℓ_s^{1/γ} = λ_s(1 − τ)[w_s + κw₀Σ_{j=1}^{T−s}R^{−j}ℓ_{s+j}]`. -/
theorem eq_12_41 {R τ κ w₀ β σ ψ γ μ cs D : ℝ} {T s : ℕ} (hs : s ≤ T) (l : ℕ → ℝ)
    (hβ : 0 < β)
    (hD : HasDerivAt (fun x => ikEarnings R τ κ w₀ T (Function.update l s x)) D (l s))
    (hc : β ^ s * cs ^ (-σ) = μ * (R⁻¹) ^ s) (hl : β ^ s * (ψ * l s ^ (1 / γ)) = μ * D) :
    ψ * l s ^ (1 / γ) = cs ^ (-σ) * (1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
      ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)) := by
  have hD' := hD.unique (ik_marginal_earnings hs l)
  rw [hD'] at hl
  have hβs : 0 < β ^ s := pow_pos hβ s
  apply mul_left_cancel₀ hβs.ne'
  rw [hl]
  have : μ * (R⁻¹) ^ s = β ^ s * cs ^ (-σ) := hc.symm
  linear_combination (1 - τ) * (ikWage κ w₀ l s + κ * w₀ *
      ∑ j ∈ Finset.range (T - s), (R⁻¹) ^ (j + 1) * l (s + j + 1)) * this

end AKMM.LaborSupply
