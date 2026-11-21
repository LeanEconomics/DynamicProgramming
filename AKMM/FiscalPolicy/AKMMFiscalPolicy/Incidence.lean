/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFiscalPolicy.LongRun
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Tax incidence

AKMM, §15.3.2, (15.13), p. 449, footnote 2.

Steady states of the GHH economy with Cobb–Douglas technology. Write `s = (k/ℓ)^{1−α}` for the
base of (15.11) (`lrS`), `θ = (1 − τ_ℓ)/(1 + τ_c)` and `ρ = (1 − β)/β`.

* **Worker–capitalist equivalence** (p. 449, footnote 2): the representative-agent steady state
  and the worker–capitalist steady state impose the same conditions on `(k, ℓ, r, w)`, and any
  aggregate consumption of the one is split between workers and capitalists in the other
  (`inc_wk_iff_ra`).
* Hours in terms of the capital–labour ratio, `ℓ = (θ(1 − α)(k/ℓ)^α)^φ` (`inc_hours_ratio`), and
  **(15.13)** `y = (θ(1 − α))^φ s^{α(1+φ)/(1−α)}` (`eq_15_13`, `incOutput`). Output is strictly
  decreasing in `τ_ℓ`, `τ_c` and `τ_k` (`inc_output_strictAntiOn_labour`,
  `inc_output_strictAntiOn_cons`, `inc_output_strictAntiOn_capital`).
* Consumption of workers `c_w = θ(1 − α)y` and capitalists `c_k = ρ/(1 + τ_c)·α(1 − τ_k)/(ρ +
  (1 − τ_k)δ)·y` (`inc_cw`, `inc_ck`).
* `k = sy` (`inc_ratio_eq`).

The budget locus (15.14), the flow-utility identity and the excess cost of taxation are in
`ExcessCost`.

Departures: none.
-/

namespace AKMM.FiscalPolicy

open Real

/-! ### Worker–capitalist equivalence (footnote 2) -/

/-- The steady-state conditions common to both decentralisations of the GHH economy, with
Cobb–Douglas technology (AKMM, pp. 448–449): `r = α(k/ℓ)^{α−1}`, `w = (1 − α)(k/ℓ)^α`, (15.8),
and the GHH hours condition `ℓ^{1/φ} = θw`. -/
def incSSCore (α β δ φ τl τc τk k l r w : ℝ) : Prop :=
  r = α * (k / l) ^ (α - 1) ∧ w = (1 - α) * (k / l) ^ α ∧
    1 = β * (1 + (1 - τk) * (r - δ)) ∧ l ^ (1 / φ) = (1 - τl) / (1 + τc) * w

/-- The representative-agent steady state: the core conditions and the steady-state budget
`(1 + τ_c)C = (1 − τ_ℓ)wℓ + (1 − τ_k)(r − δ)k + T`. -/
def incRASteady (α β δ φ τl τc τk T k l r w C : ℝ) : Prop :=
  incSSCore α β δ φ τl τc τk k l r w ∧
    (1 + τc) * C = (1 - τl) * w * l + (1 - τk) * (r - δ) * k + T

/-- The worker–capitalist steady state: the core conditions (the capitalists' Euler equation is
(15.8), the workers' hours condition is GHH) and the two budgets
`(1 + τ_c)c_w = (1 − τ_ℓ)wℓ + T_w`, `(1 + τ_c)c_k = (1 − τ_k)(r − δ)k + T_k`. -/
def incWKSteady (α β δ φ τl τc τk Tw Tk k l r w cw ck : ℝ) : Prop :=
  incSSCore α β δ φ τl τc τk k l r w ∧ (1 + τc) * cw = (1 - τl) * w * l + Tw ∧
    (1 + τc) * ck = (1 - τk) * (r - δ) * k + Tk

/-- AKMM, p. 449 and footnote 2: "the steady state of the representative agent model … is
identical, at the aggregate level, to … workers … and capitalists": `(k, ℓ, r, w, C)` is a
representative-agent steady state iff it is a worker–capitalist steady state for some split
`C = c_w + c_k` of consumption and `T = T_w + T_k` of transfers. Consumption appears in neither
condition of `incSSCore`. -/
theorem inc_wk_iff_ra {α β δ φ τl τc τk T k l r w C : ℝ} (hτc : 1 + τc ≠ 0) :
    incRASteady α β δ φ τl τc τk T k l r w C ↔
      ∃ cw ck Tw Tk, cw + ck = C ∧ Tw + Tk = T ∧
        incWKSteady α β δ φ τl τc τk Tw Tk k l r w cw ck := by
  constructor
  · rintro ⟨hcore, hb⟩
    refine ⟨((1 - τl) * w * l + T) / (1 + τc), (1 - τk) * (r - δ) * k / (1 + τc), T, 0,
      ?_, by ring, hcore, by field_simp, by field_simp; ring⟩
    field_simp
    linarith
  · rintro ⟨cw, ck, Tw, Tk, hC, hT, hcore, hw, hk⟩
    refine ⟨hcore, ?_⟩
    rw [← hC, ← hT]
    linear_combination hw + hk

/-! ### Output and consumption, (15.13) -/

/-- Steady-state output (15.13) as a function of `θ(1 − α)` (`m`) and `s = (k/ℓ)^{1−α}`:
`y = m^φ s^{α(1+φ)/(1−α)}`. -/
noncomputable def incOutput (α φ m s : ℝ) : ℝ := m ^ φ * s ^ (α * (1 + φ) / (1 - α))

/-- AKMM, p. 449: from (15.10) and (15.12), `ℓ = (θ(1 − α)(k/ℓ)^α)^φ`. -/
theorem inc_hours_ratio {α φ θ x l : ℝ} (hα : α < 1) (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hl : l = θ ^ φ * ((1 - α) * x ^ α) ^ φ) : l = (θ * (1 - α) * x ^ α) ^ φ := by
  have h1 : 0 ≤ (1 - α) * x ^ α := mul_nonneg (by linarith) (Real.rpow_nonneg hx α)
  rw [hl, ← Real.mul_rpow hθ h1, mul_assoc]

/-- **(15.13)** (AKMM, p. 449): with `k/ℓ = s^{1/(1−α)}` (15.11) and hours (15.12) at the
wage (15.10), steady-state output is `y = (k/ℓ)^αℓ = (θ(1 − α))^φ s^{α(1+φ)/(1−α)}`
(`α < 1`, `θ ≥ 0`, `s > 0`). -/
theorem eq_15_13 {α φ θ s l : ℝ} (hα1 : α < 1) (hθ : 0 ≤ θ) (hs : 0 < s)
    (hl : l = θ ^ φ * ((1 - α) * (s ^ (1 / (1 - α))) ^ α) ^ φ) :
    (s ^ (1 / (1 - α))) ^ α * l = incOutput α φ (θ * (1 - α)) s := by
  have h1α : 0 < 1 - α := by linarith
  have hxa : (s ^ (1 / (1 - α))) ^ α = s ^ (α / (1 - α)) := by
    rw [← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [hl, hxa, ← Real.mul_rpow hθ (mul_nonneg h1α.le (Real.rpow_nonneg hs.le _))]
  unfold incOutput
  rw [← mul_assoc, Real.mul_rpow (mul_nonneg hθ h1α.le) (Real.rpow_nonneg hs.le _),
    ← Real.rpow_mul hs.le]
  have : α * (1 + φ) / (1 - α) = α / (1 - α) + α / (1 - α) * φ := by ring
  rw [this, Real.rpow_add hs]
  ring

/-- AKMM, p. 449: output (15.13) is strictly increasing in `m = θ(1 − α) > 0` and in `s > 0`. -/
theorem inc_output_lt {α φ m m' s s' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hm : 0 < m) (hmm : m ≤ m') (hs : 0 < s) (hss : s ≤ s') (hne : m < m' ∨ s < s') :
    incOutput α φ m s < incOutput α φ m' s' := by
  have he : 0 < α * (1 + φ) / (1 - α) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hm' : 0 < m' := by linarith
  unfold incOutput
  rcases hne with h | h
  · calc m ^ φ * s ^ (α * (1 + φ) / (1 - α)) < m' ^ φ * s ^ (α * (1 + φ) / (1 - α)) :=
          mul_lt_mul_of_pos_right (Real.rpow_lt_rpow hm.le h hφ) (Real.rpow_pos_of_pos hs _)
      _ ≤ m' ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hss he.le)
            (Real.rpow_nonneg hm'.le _)
  · calc m ^ φ * s ^ (α * (1 + φ) / (1 - α)) < m ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hs.le h he) (Real.rpow_pos_of_pos hm _)
      _ ≤ m' ^ φ * s' ^ (α * (1 + φ) / (1 - α)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le hmm hφ.le)
            (Real.rpow_nonneg (by linarith) _)

/-- AKMM, p. 449: "the level of output is decreasing in each tax rate": in the labour tax
(`τ_c > −1`, on `τ_ℓ < 1`, for `s > 0`). -/
theorem inc_output_strictAntiOn_labour {α φ τc s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hτc : 0 < 1 + τc) (hs : 0 < s) :
    StrictAntiOn (fun τl => incOutput α φ ((1 - τl) / (1 + τc) * (1 - α)) s) (Set.Iio 1) := by
  intro a _ b hb hab
  have hb' : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
  have h1α : 0 < 1 - α := by linarith
  refine inc_output_lt hα0 hα1 hφ (by positivity) ?_ hs le_rfl (Or.inl ?_)
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hτc.le) h1α.le
  · exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by linarith) hτc) h1α

/-- AKMM, p. 449: output is decreasing in the consumption tax (`τ_ℓ < 1`, on `τ_c > −1`). -/
theorem inc_output_strictAntiOn_cons {α φ τl s : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hφ : 0 < φ)
    (hτl : τl < 1) (hs : 0 < s) :
    StrictAntiOn (fun τc => incOutput α φ ((1 - τl) / (1 + τc) * (1 - α)) s) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have := Set.mem_Ioi.mp ha; linarith
  have hb' : 0 < 1 + b := by have := Set.mem_Ioi.mp hb; linarith
  have h1α : 0 < 1 - α := by linarith
  have hl : 0 < 1 - τl := by linarith
  refine inc_output_lt hα0 hα1 hφ (by positivity) ?_ hs le_rfl (Or.inl ?_)
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hl.le ha' (by linarith)) h1α.le
  · exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_left hl ha' (by linarith)) h1α

/-- AKMM, p. 449: output is decreasing in the capital tax (through `s`, for `0 < β < 1`,
`δ ≥ 0`, `θ > 0`, on `τ_k < 1`). -/
theorem inc_output_strictAntiOn_capital {α β δ φ θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hφ : 0 < φ) (hθ : 0 < θ) :
    StrictAntiOn (fun τk => incOutput α φ (θ * (1 - α)) (lrS α β δ τk)) (Set.Iio 1) := by
  intro a ha b hb hab
  have hρ : 0 < lrRho β := div_pos (by linarith) hβ0
  have hsb : 0 < lrS α β δ b := by
    have : 0 < 1 - b := by have := Set.mem_Iio.mp hb; linarith
    unfold lrS
    positivity
  have h1α : 0 < 1 - α := by linarith
  have hlt := lr_s_strictAntiOn hα0 hβ0 hβ1 hδ ha hb hab
  exact inc_output_lt hα0 hα1 hφ (by positivity) le_rfl hsb hlt.le (Or.inr hlt)

/-- AKMM, p. 449: workers consume `c_w = θwℓ = θ(1 − α)y`, using `wℓ = (1 − α)(k/ℓ)^αℓ`. -/
theorem inc_cw {α θ x l : ℝ} :
    θ * ((1 - α) * x ^ α) * l = θ * (1 - α) * (x ^ α * l) := by
  ring

/-- `s^{1/(1−α)} = s·(s^{1/(1−α)})^α`, i.e. `k/ℓ = s(k/ℓ)^α`, so `k = sy`. -/
theorem inc_ratio_eq {α s : ℝ} (hα1 : α < 1) (hs : 0 < s) :
    s ^ (1 / (1 - α)) = s * (s ^ (1 / (1 - α))) ^ α := by
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [← Real.rpow_mul hs.le]
  conv_lhs => rw [show 1 / (1 - α) = 1 + 1 / (1 - α) * α by field_simp; ring]
  rw [Real.rpow_add hs, Real.rpow_one]

/-- AKMM, p. 449: capitalists consume `c_k = (1 − τ_k)(r − δ)k/(1 + τ_c)
= (ρ/(1 + τ_c))·α(1 − τ_k)/(ρ + (1 − τ_k)δ)·y`, with `r` from (15.8), `k = (k/ℓ)ℓ`,
`k/ℓ = s^{1/(1−α)}` (15.11) and `y = (k/ℓ)^αℓ`. -/
theorem inc_ck {α β δ τk τc l : ℝ} (hα1 : α < 1) (hτk : τk < 1) (hs : 0 < lrS α β δ τk) :
    (1 - τk) * (lrRent β δ τk - δ) * (lrS α β δ τk ^ (1 / (1 - α)) * l) / (1 + τc) =
      lrRho β / (1 + τc) * (α * (1 - τk) / (lrRho β + (1 - τk) * δ)) *
        ((lrS α β δ τk ^ (1 / (1 - α))) ^ α * l) := by
  have h1τ : (1 - τk) ≠ 0 := by linarith
  have hr : (1 - τk) * (lrRent β δ τk - δ) = lrRho β := by
    unfold lrRent
    field_simp
    ring
  have hS : α * (1 - τk) / (lrRho β + (1 - τk) * δ) = lrS α β δ τk := by
    unfold lrS
    rw [mul_comm δ]
  rw [hr, hS]
  nth_rewrite 1 [inc_ratio_eq hα1 hs]
  ring

end AKMM.FiscalPolicy
