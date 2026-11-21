/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMMatching
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# §18.1: values of jobs and workers, free entry, Nash bargaining and the wage equation

Miao, §18.1, pp. 589–592, equations (18.4)–(18.15) and the definition of a search equilibrium.
All value functions are real sequences indexed by `t : ℕ`.

* `eq_18_6`, `eq_18_7`, `eq_18_8`: free entry `V_t = 0` in the vacancy equation (18.5) gives
  `J^F_{t+1} = κ/(βq^v_t)` (18.6); with the filled-job equation (18.4) it gives (18.7) and the
  job creation (Euler) equation (18.8).
* `dm_amgm2_strict`, `dm_nash_bound`, `dm_nash_solution`: the Nash product
  `(x₀ + w)^η (y₀ − w)^{1−η}` (surpluses affine in the wage, with constant total surplus) is
  maximised exactly where `η(y₀ − w) = (1 − η)(x₀ + w)` (weighted AM–GM, with its strict form for
  uniqueness).
* `eq_18_11`: the bargaining problem (18.11) — with the continuation values taken as given, the
  wage `w_t` solves (18.11) iff the first-order condition `ηJ^F_t = (1 − η)(J^W_t − J^U_t)`
  holds. The book only states the first-order condition; here it is shown to be necessary and
  sufficient for the constrained maximum.
* `eq_18_12`, `eq_18_13`: surplus sharing `ηS_t = J^W_t − J^U_t`, `(1 − η)S_t = J^F_t`,
  and `(1 − η)S_{t+1} = κ/(βq^v_t)`.
* `eq_18_14`: the surplus equation (all three lines); `dm_worker_surplus`: the worker-surplus
  equation on p. 591; `eq_18_15`: the wage equation `w_t = η(A + κθ_t) + (1 − η)b`.
* `dm_IsSearchEqm`: a search equilibrium (p. 592); `dm_bellman_implies_eqm`: the Bellman
  equations, free entry and Nash bargaining imply the equilibrium conditions (18.8), (18.15).
-/

namespace Miao.SearchAndMatching

/-- Miao, (18.6), p. 590: free entry `V_t = 0` in the vacancy equation (18.5)
`V_t = −κ + β(q^v_t J^F_{t+1} + (1 − q^v_t)V_{t+1})` gives `J^F_{t+1} = κ/(βq^v_t)`. -/
theorem eq_18_6 {κ β : ℝ} {JF V qv : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) : JF (t + 1) = κ / (β * qv t) := by
  have h := h5 t
  rw [hV t, hV (t + 1)] at h
  have hq' := hq t
  field_simp
  linarith

/-- Miao, (18.7), p. 590: substituting (18.6) into the filled-job equation (18.4)
`J^F_t = A − w_t + β(ρV_{t+1} + (1 − ρ)J^F_{t+1})` gives `J^F_t = A − w_t + (1 − ρ)κ/q^v_t`. -/
theorem eq_18_7 {A κ β ρ : ℝ} {JF V qv w : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) : JF t = A - w t + (1 - ρ) * κ / qv t := by
  rw [h4 t, hV (t + 1), eq_18_6 hV h5 hβ hq t]
  have hq' := hq t
  field_simp
  ring

/-- Miao, (18.8), p. 590: the **job creation equation**
`κ/q^v_t = β(A − w_{t+1} + (1 − ρ)κ/q^v_{t+1})`. -/
theorem eq_18_8 {A κ β ρ : ℝ} {JF V qv w : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) := by
  rw [← eq_18_7 hV h4 h5 hβ hq (t + 1), eq_18_6 hV h5 hβ hq t]
  have hq' := hq t
  field_simp

/-- Strict weighted AM–GM for two terms: `p₁^w p₂^{1−w} < wp₁ + (1 − w)p₂` when `p₁ ≠ p₂`. -/
theorem dm_amgm2_strict {w p₁ p₂ : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hp₁ : 0 ≤ p₁)
    (hp₂ : 0 ≤ p₂) (hne : p₁ ≠ p₂) : p₁ ^ w * p₂ ^ (1 - w) < w * p₁ + (1 - w) * p₂ := by
  have h := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos (Finset.univ : Finset (Fin 2))
    ![w, 1 - w] ![p₁, p₂] ?_ ?_ ?_).mpr
    ⟨0, Finset.mem_univ _, 1, Finset.mem_univ _, by simpa using hne⟩
  · simpa [Fin.prod_univ_two, Fin.sum_univ_two] using h
  · intro i _
    fin_cases i
    · simpa using hw0
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · simp [Fin.sum_univ_two]
  · intro i _
    fin_cases i
    · simpa using hp₁
    · simpa using hp₂

/-- Miao, (18.11), p. 590: the Nash product with nonnegative surpluses `x, y` is at most
`η^η(1 − η)^{1−η}(x + y)`, with equality only at the split `x = η(x + y)`. -/
theorem dm_nash_bound {η x y : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ η * y ^ (1 - η) ≤ η ^ η * (1 - η) ^ (1 - η) * (x + y) ∧
      (x ^ η * y ^ (1 - η) = η ^ η * (1 - η) ^ (1 - η) * (x + y) → x = η * (x + y)) := by
  have hη1' : 0 < 1 - η := by linarith
  have hp₁ : 0 ≤ x / η := div_nonneg hx hη0.le
  have hp₂ : 0 ≤ y / (1 - η) := div_nonneg hy hη1'.le
  have ex : x ^ η = η ^ η * (x / η) ^ η := by
    rw [← Real.mul_rpow hη0.le hp₁]; congr 1; field_simp
  have ey : y ^ (1 - η) = (1 - η) ^ (1 - η) * (y / (1 - η)) ^ (1 - η) := by
    rw [← Real.mul_rpow hη1'.le hp₂]; congr 1; field_simp
  have hsum : η * (x / η) + (1 - η) * (y / (1 - η)) = x + y := by field_simp
  have hprod : x ^ η * y ^ (1 - η) =
      η ^ η * (1 - η) ^ (1 - η) * ((x / η) ^ η * (y / (1 - η)) ^ (1 - η)) := by
    rw [ex, ey]; ring
  have hc : 0 < η ^ η * (1 - η) ^ (1 - η) := by positivity
  have amgm := Real.geom_mean_le_arith_mean2_weighted hη0.le hη1'.le hp₁ hp₂ (by ring)
  refine ⟨?_, fun heq ↦ ?_⟩
  · rw [hprod, ← hsum]
    exact mul_le_mul_of_nonneg_left amgm hc.le
  · by_contra hne
    have hne' : x / η ≠ y / (1 - η) := by
      intro h
      apply hne
      field_simp at h
      linarith
    have hlt := dm_amgm2_strict hη0 hη1 hp₁ hp₂ hne'
    rw [hprod, ← hsum] at heq
    have := mul_lt_mul_of_pos_left hlt hc
    linarith

/-- Miao, (18.11), p. 590: if the worker's surplus is `x₀ + w` and the firm's is `y₀ − w`, with
positive total surplus `x₀ + y₀`, then `w` maximises the Nash product
`(x₀ + w)^η(y₀ − w)^{1−η}` subject to both surpluses being nonnegative iff
`η(y₀ − w) = (1 − η)(x₀ + w)`. -/
theorem dm_nash_solution {η x₀ y₀ w : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hs : 0 < x₀ + y₀) :
    (0 ≤ x₀ + w ∧ 0 ≤ y₀ - w ∧
      IsMaxOn (fun w' ↦ (x₀ + w') ^ η * (y₀ - w') ^ (1 - η))
        {w' | 0 ≤ x₀ + w' ∧ 0 ≤ y₀ - w'} w) ↔ η * (y₀ - w) = (1 - η) * (x₀ + w) := by
  set c := η ^ η * (1 - η) ^ (1 - η) with hcdef
  have hη1' : 0 < 1 - η := by linarith
  -- the value at the split `x = ηs`
  have hval : ∀ w', x₀ + w' = η * (x₀ + y₀) →
      (x₀ + w') ^ η * (y₀ - w') ^ (1 - η) = c * (x₀ + y₀) := by
    intro w' hw'
    have hy : y₀ - w' = (1 - η) * (x₀ + y₀) := by linarith
    rw [hw', hy, Real.mul_rpow hη0.le hs.le, Real.mul_rpow hη1'.le hs.le]
    have : (x₀ + y₀) ^ η * (x₀ + y₀) ^ (1 - η) = x₀ + y₀ := by
      rw [← Real.rpow_add hs]; simp
    rw [hcdef]
    calc η ^ η * (x₀ + y₀) ^ η * ((1 - η) ^ (1 - η) * (x₀ + y₀) ^ (1 - η))
        = η ^ η * (1 - η) ^ (1 - η) * ((x₀ + y₀) ^ η * (x₀ + y₀) ^ (1 - η)) := by ring
      _ = _ := by rw [this]
  have hsum : ∀ w', (x₀ + w') + (y₀ - w') = x₀ + y₀ := fun w' ↦ by ring
  constructor
  · rintro ⟨h1, h2, hmax⟩
    set w₀ := η * (x₀ + y₀) - x₀ with hw₀
    have hw₀' : x₀ + w₀ = η * (x₀ + y₀) := by rw [hw₀]; ring
    have hmem : w₀ ∈ {w' | 0 ≤ x₀ + w' ∧ 0 ≤ y₀ - w'} := by
      refine ⟨?_, ?_⟩
      · rw [hw₀']; positivity
      · have : y₀ - w₀ = (1 - η) * (x₀ + y₀) := by rw [hw₀]; ring
        rw [this]; positivity
    have hge : (x₀ + w₀) ^ η * (y₀ - w₀) ^ (1 - η) ≤ (x₀ + w) ^ η * (y₀ - w) ^ (1 - η) :=
      hmax hmem
    rw [hval w₀ hw₀'] at hge
    obtain ⟨hle, heq⟩ := dm_nash_bound hη0 hη1 h1 h2
    rw [hsum] at hle heq
    have hx := heq (le_antisymm hle hge)
    linarith
  · intro hfoc
    have hx : x₀ + w = η * (x₀ + y₀) := by linarith
    have hy : y₀ - w = (1 - η) * (x₀ + y₀) := by linarith
    refine ⟨by rw [hx]; positivity, by rw [hy]; positivity, ?_⟩
    intro w' hw'
    dsimp only
    rw [hval w hx]
    have := (dm_nash_bound hη0 hη1 hw'.1 hw'.2).1
    rwa [hsum] at this

/-- Miao, (18.11) and the first-order condition, pp. 590–591: given the continuation values
`J^W_{t+1}, J^U_{t+1}, J^F_{t+1}, V_{t+1}` and `J^U_t` (which do not depend on `w_t`), the
worker's value `J^W_t(w) = w + β(ρJ^U_{t+1} + (1 − ρ)J^W_{t+1})` (18.9) and the firm's value
`J^F_t(w) = A − w + β(ρV_{t+1} + (1 − ρ)J^F_{t+1})` (18.4), the wage `w` solves the Nash
bargaining problem `max (J^W_t − J^U_t)^η (J^F_t − V_t)^{1−η}` subject to `J^W_t ≥ J^U_t` and
`J^F_t ≥ V_t` iff `η(J^F_t − V_t) = (1 − η)(J^W_t − J^U_t)` (when the total surplus is
positive). -/
theorem eq_18_11 {A β ρ η JWn JUn JFn Vn JU V w : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hS : 0 < A + β * (ρ * Vn + (1 - ρ) * JFn) - V + (β * (ρ * JUn + (1 - ρ) * JWn) - JU)) :
    (JU ≤ w + β * (ρ * JUn + (1 - ρ) * JWn) ∧ V ≤ A - w + β * (ρ * Vn + (1 - ρ) * JFn) ∧
      IsMaxOn (fun w' ↦ (w' + β * (ρ * JUn + (1 - ρ) * JWn) - JU) ^ η *
          (A - w' + β * (ρ * Vn + (1 - ρ) * JFn) - V) ^ (1 - η))
        {w' | JU ≤ w' + β * (ρ * JUn + (1 - ρ) * JWn) ∧
          V ≤ A - w' + β * (ρ * Vn + (1 - ρ) * JFn)} w) ↔
      η * (A - w + β * (ρ * Vn + (1 - ρ) * JFn) - V) =
        (1 - η) * (w + β * (ρ * JUn + (1 - ρ) * JWn) - JU) := by
  set X := β * (ρ * JUn + (1 - ρ) * JWn) with hX
  set Y := A + β * (ρ * Vn + (1 - ρ) * JFn) - V with hY
  have e1 : ∀ w', w' + X - JU = (X - JU) + w' := fun w' ↦ by ring
  have e2 : ∀ w', A - w' + β * (ρ * Vn + (1 - ρ) * JFn) - V = Y - w' := fun w' ↦ by
    rw [hY]; ring
  have i1 : ∀ w', (JU ≤ w' + X) ↔ 0 ≤ (X - JU) + w' := fun w' ↦ by
    constructor <;> intro h <;> linarith
  have i2 : ∀ w', (V ≤ A - w' + β * (ρ * Vn + (1 - ρ) * JFn)) ↔ 0 ≤ Y - w' := fun w' ↦ by
    rw [hY]; constructor <;> intro h <;> linarith
  simp only [e1, e2, i1, i2]
  have hS' : 0 < (X - JU) + Y := by rw [hY]; linarith
  exact dm_nash_solution hη0 hη1 hS'

/-- Miao, p. 591: the **total surplus** `S_t = J^F_t + J^W_t − J^U_t`. -/
def dm_surplus (JF JW JU : ℕ → ℝ) (t : ℕ) : ℝ := JF t + JW t - JU t

/-- Miao, (18.12)–(18.13), p. 591: the bargaining first-order condition
`ηJ^F_t = (1 − η)(J^W_t − J^U_t)` is equivalent to the surplus split `ηS_t = J^W_t − J^U_t`,
`(1 − η)S_t = J^F_t`. -/
theorem eq_18_12 {η : ℝ} {JF JW JU : ℕ → ℝ} (t : ℕ) :
    η * JF t = (1 - η) * (JW t - JU t) ↔
      η * dm_surplus JF JW JU t = JW t - JU t ∧ (1 - η) * dm_surplus JF JW JU t = JF t := by
  unfold dm_surplus
  constructor
  · intro h
    exact ⟨by linear_combination h, by linear_combination (-1 : ℝ) * h⟩
  · rintro ⟨h, -⟩
    linear_combination h

/-- Miao, (18.13), p. 591: `(1 − η)S_{t+1} = J^F_{t+1} = κ/(βq^v_t)`, by the free entry condition
(18.6). -/
theorem eq_18_13 {κ β η : ℝ} {JF JW JU V qv : ℕ → ℝ} (hV : ∀ t, V t = 0)
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0)
    (hfoc : ∀ t, η * JF t = (1 - η) * (JW t - JU t)) (t : ℕ) :
    (1 - η) * dm_surplus JF JW JU (t + 1) = JF (t + 1) ∧ JF (t + 1) = κ / (β * qv t) :=
  ⟨((eq_18_12 (t + 1)).mp (hfoc (t + 1))).2, eq_18_6 hV h5 hβ hq t⟩

/-- Miao, (18.14), p. 591: by (18.4) (with `V = 0`), (18.9) and (18.10),
`S_t = A − b + β(1 − ρ)S_{t+1} − βq^u_t(J^W_{t+1} − J^U_{t+1})`; by (18.12) this is
`A − b + β(1 − ρ − ηq^u_t)S_{t+1}`, and by (18.13) it is
`A − b + κ(1 − ρ − ηq^u_t)/((1 − η)q^v_t)`. -/
theorem eq_18_14 {A b κ β ρ η : ℝ} {JF JW JU w qv qu : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    dm_surplus JF JW JU t = A - b + β * (1 - ρ) * dm_surplus JF JW JU (t + 1) -
        β * qu t * (JW (t + 1) - JU (t + 1)) ∧
      dm_surplus JF JW JU t = A - b + β * (1 - ρ - η * qu t) * dm_surplus JF JW JU (t + 1) ∧
      dm_surplus JF JW JU t = A - b + κ * (1 - ρ - η * qu t) / ((1 - η) * qv t) := by
  have first : dm_surplus JF JW JU t = A - b + β * (1 - ρ) * dm_surplus JF JW JU (t + 1) -
      β * qu t * (JW (t + 1) - JU (t + 1)) := by
    unfold dm_surplus
    rw [h4, h9, h10]
    ring
  have second : dm_surplus JF JW JU t =
      A - b + β * (1 - ρ - η * qu t) * dm_surplus JF JW JU (t + 1) := by
    rw [first, ← h12]; ring
  refine ⟨first, second, ?_⟩
  have hη' : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη1)
  have hS : dm_surplus JF JW JU (t + 1) = κ / ((1 - η) * β * qv t) := by
    field_simp
    field_simp at h13
    linear_combination h13
  rw [second, hS]
  field_simp

/-- Miao, p. 591: by (18.9), (18.10) and (18.12),
`ηS_t = J^W_t − J^U_t = w_t − b + β(1 − ρ − q^u_t)(J^W_{t+1} − J^U_{t+1})
  = w_t − b + β(1 − ρ − q^u_t)ηS_{t+1}`. -/
theorem dm_worker_surplus {b β ρ η : ℝ} {JF JW JU w qu : ℕ → ℝ} (t : ℕ)
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1)) :
    η * dm_surplus JF JW JU t = w t - b + β * (1 - ρ - qu t) * (JW (t + 1) - JU (t + 1)) ∧
      η * dm_surplus JF JW JU t =
        w t - b + β * (1 - ρ - qu t) * (η * dm_surplus JF JW JU (t + 1)) := by
  have first : η * dm_surplus JF JW JU t =
      w t - b + β * (1 - ρ - qu t) * (JW (t + 1) - JU (t + 1)) := by
    rw [h12t, h9, h10]; ring
  exact ⟨first, by rw [first, h12]⟩

/-- Miao, (18.15), p. 591: substituting (18.14) for `S_t` and (18.13) for `S_{t+1}` into the
worker-surplus equation and using `q^u_t = θ_tq^v_t` (18.1) gives the **wage equation**
`w_t = η(A + κθ_t) + (1 − η)b`. -/
theorem eq_18_15 {A b κ β ρ η : ℝ} {JF JW JU w qv qu θ : ℕ → ℝ} (t : ℕ)
    (h4 : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)))
    (h9 : JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (h12t : η * dm_surplus JF JW JU t = JW t - JU t)
    (h12 : η * dm_surplus JF JW JU (t + 1) = JW (t + 1) - JU (t + 1))
    (h13 : (1 - η) * dm_surplus JF JW JU (t + 1) = κ / (β * qv t))
    (hqu : qu t = θ t * qv t) (hβ : β ≠ 0) (hq : qv t ≠ 0) (hη1 : η ≠ 1) :
    w t = η * (A + κ * θ t) + (1 - η) * b := by
  have hη' : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη1)
  have hSt := (eq_18_14 (A := A) t h4 h9 h10 h12 h13 hβ hq hη1).2.2
  have hW := (dm_worker_surplus (w := w) t h9 h10 h12t h12).2
  have hS : dm_surplus JF JW JU (t + 1) = κ / ((1 - η) * β * qv t) := by
    field_simp
    field_simp at h13
    linear_combination h13
  rw [hSt, hS, hqu] at hW
  field_simp at hW
  have key : ((1 - η) * qv t) * (w t - (η * (A + κ * θ t) + (1 - η) * b)) = 0 := by
    linear_combination (-1 : ℝ) * hW
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero hη' hq)
  · linarith

/-- Miao, p. 592: a **search equilibrium**: sequences `N, u, v, θ, w, q^v` with `u, v > 0`
satisfying (18.1) (`θ_t = v_t/u_t`, `q^v_t = q(θ_t)`), (18.2), (18.3), (18.8) and (18.15). -/
def dm_IsSearchEqm (MF : DMMatchingFn) (A b κ β ρ η : ℝ) (N u v θ w qv : ℕ → ℝ) : Prop :=
  ∀ t, 0 < u t ∧ 0 < v t ∧ θ t = v t / u t ∧ qv t = dm_q MF (θ t) ∧
    N (t + 1) = (1 - ρ) * N t + MF.M (u t) (v t) ∧ u t = 1 - N t ∧
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
    w t = η * (A + κ * θ t) + (1 - η) * b

/-- Miao, pp. 590–592: the Bellman equations (18.4), (18.5), (18.9), (18.10), free entry and the
Nash bargaining first-order condition imply the equilibrium conditions (18.8) and (18.15) at
every date. -/
theorem dm_bellman_implies_eqm {A b κ β ρ η : ℝ} {JF JW JU V w qv qu θ : ℕ → ℝ}
    (hV : ∀ t, V t = 0)
    (h4 : ∀ t, JF t = A - w t + β * (ρ * V (t + 1) + (1 - ρ) * JF (t + 1)))
    (h5 : ∀ t, V t = -κ + β * (qv t * JF (t + 1) + (1 - qv t) * V (t + 1)))
    (h9 : ∀ t, JW t = w t + β * (ρ * JU (t + 1) + (1 - ρ) * JW (t + 1)))
    (h10 : ∀ t, JU t = b + β * (qu t * JW (t + 1) + (1 - qu t) * JU (t + 1)))
    (hfoc : ∀ t, η * JF t = (1 - η) * (JW t - JU t))
    (hqu : ∀ t, qu t = θ t * qv t) (hβ : β ≠ 0) (hq : ∀ t, qv t ≠ 0) (hη1 : η ≠ 1) (t : ℕ) :
    κ / qv t = β * (A - w (t + 1) + (1 - ρ) * κ / qv (t + 1)) ∧
      w t = η * (A + κ * θ t) + (1 - η) * b := by
  refine ⟨eq_18_8 hV h4 h5 hβ hq t, ?_⟩
  have h4' : JF t = A - w t + β * (ρ * 0 + (1 - ρ) * JF (t + 1)) := by
    rw [h4 t, hV (t + 1)]
  obtain ⟨h13a, h13b⟩ := eq_18_13 hV h5 hβ hq hfoc t
  exact eq_18_15 t h4' (h9 t) (h10 t) ((eq_18_12 t).mp (hfoc t)).1
    ((eq_18_12 (t + 1)).mp (hfoc (t + 1))).1 (h13a.trans h13b) (hqu t) hβ (hq t) hη1

end Miao.SearchAndMatching
