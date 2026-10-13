/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.BellmanLog
import Mathlib.Probability.ProductMeasure

/-!
# The stochastic log/Cobb–Douglas economy

SLP §2.2, pp. 16–19, and Exercise 2.6, p. 19.

Output is `z f(k) = z k^α` with i.i.d. shocks `z ∼ μ`, `z > 0`, `ln z` integrable, `U = ln`.

* `log_tradeoff`, `log_tradeoff_unique`: for `Y > 0`, `ln(Y − y) + (αβ/(1 − αβ)) ln y` is
  maximized over `y ∈ (0, Y)` exactly at `y = αβY`.
* `stochValue`: `v(k, z) = A + B ln k + C ln z`, `B = α/(1 − αβ)`, `C = 1/(1 − αβ)`.
* `integral_stochValue`: `E[v(y, z′)] = A + B ln y + C E[ln z]`.
* `stoch_bellman_isGreatest`, `stoch_argmax_unique` (Ex 2.6): `v` satisfies the functional
  equation (3) and `y = αβ z k^α` (policy (5)) is the unique maximizer.
* `hasSum_expected_utility` (Ex 2.6): along policy (5), with the shocks after period 0 i.i.d. under
  the product measure, `∑ βᵗ E[ln c_t] = v(k, z)`.
-/

open Finset Set Filter Topology Real MeasureTheory ProbabilityTheory

namespace StokeyLucasPrescott.Overview

/-- **The log trade-off.** For `Y > 0` and `0 < αβ < 1`, every `y ∈ (0, Y)` has
`ln(Y − y) + (αβ/(1 − αβ)) ln y ≤ ln((1 − αβ)Y) + (αβ/(1 − αβ)) ln(αβY)`. -/
theorem log_tradeoff {α β Y y : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (hY : 0 < Y) (hy : 0 < y)
    (hyY : y < Y) :
    log (Y - y) + α * β / (1 - α * β) * log y ≤
      log ((1 - α * β) * Y) + α * β / (1 - α * β) * log (α * β * Y) := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have hcs : 0 < (1 - α * β) * Y := mul_pos h1ab hY
  have hys : 0 < α * β * Y := mul_pos h0 hY
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyY)) (hasDerivAt_log hcs.ne')
  have t2 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (hasDerivAt_log hys.ne')
  have hw : 0 ≤ α * β / (1 - α * β) := div_nonneg h0.le h1ab.le
  have hfoc : ((1 - α * β) * Y)⁻¹ * (Y - y - (1 - α * β) * Y) +
      α * β / (1 - α * β) * ((α * β * Y)⁻¹ * (y - α * β * Y)) = 0 := by
    have hα0 : α ≠ 0 := left_ne_zero_of_mul h0.ne'
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul h0.ne'
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left t2 hw
  nlinarith

/-- **The maximizer is unique.** -/
theorem log_tradeoff_unique {α β Y y : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (hY : 0 < Y)
    (hy : 0 < y) (hyY : y < Y)
    (hmax : log ((1 - α * β) * Y) + α * β / (1 - α * β) * log (α * β * Y) ≤
      log (Y - y) + α * β / (1 - α * β) * log y) : y = α * β * Y := by
  by_contra hne
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have hcs : 0 < (1 - α * β) * Y := mul_pos h1ab hY
  have hys : 0 < α * β * Y := mul_pos h0 hY
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyY)) (hasDerivAt_log hcs.ne')
  have t2 := strictConcave_lt_tangent strictConcaveOn_log_Ioi (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (fun h => hne h.symm) (hasDerivAt_log hys.ne')
  have hw : 0 < α * β / (1 - α * β) := div_pos h0 h1ab
  have hfoc : ((1 - α * β) * Y)⁻¹ * (Y - y - (1 - α * β) * Y) +
      α * β / (1 - α * β) * ((α * β * Y)⁻¹ * (y - α * β * Y)) = 0 := by
    have hα0 : α ≠ 0 := left_ne_zero_of_mul h0.ne'
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul h0.ne'
    field_simp
    ring
  have := mul_lt_mul_of_pos_left t2 hw
  nlinarith

/-- The coefficient `C = 1/(1 − αβ)` on `ln z`. -/
noncomputable def coefC (α β : ℝ) : ℝ := 1 / (1 - α * β)

/-- The constant `A = [ln(1 − αβ) + βB ln(αβ) + βC m]/(1 − β)`, `m = E[ln z]`. -/
noncomputable def coefAs (α β m : ℝ) : ℝ :=
  (log (1 - α * β) + β * coefB α β * log (α * β) + β * coefC α β * m) / (1 - β)

/-- The value function `v(k, z) = A + B ln k + C ln z`. -/
noncomputable def stochValue (α β m k z : ℝ) : ℝ :=
  coefAs α β m + coefB α β * log k + coefC α β * log z

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- `E[v(y, z′)] = A + B ln y + C E[ln z]`. -/
theorem integral_stochValue (hint : Integrable log μ) (α β y : ℝ) :
    ∫ z', stochValue α β (∫ z, log z ∂μ) y z' ∂μ =
      coefAs α β (∫ z, log z ∂μ) + coefB α β * log y + coefC α β * ∫ z, log z ∂μ := by
  unfold stochValue
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul]
  simp

/-- The right side of (3): `ln(z k^α − y) + β E[v(y, z′)]`. -/
noncomputable def stochRHS (μ : Measure ℝ) (α β k z y : ℝ) : ℝ :=
  log (z * k ^ α - y) + β * ∫ z', stochValue α β (∫ z, log z ∂μ) y z' ∂μ

/-- The value at the maximizer `y = αβ z k^α` is `v(k, z)`. -/
theorem stochRHS_attained (hint : Integrable log μ) {α β k z : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) :
    stochRHS μ α β k z (α * β * (z * k ^ α)) = stochValue α β (∫ z, log z ∂μ) k z := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  unfold stochRHS
  rw [integral_stochValue hint]
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring]
  simp only [stochValue, coefAs, coefB, coefC]
  rw [log_mul h1ab.ne' (mul_pos hz hK).ne', log_mul h0.ne' (mul_pos hz hK).ne',
    log_mul hz.ne' hK.ne', log_rpow hk]
  field_simp
  ring

/-- The objective in (3) equals the log trade-off plus terms independent of `y`. -/
theorem stochRHS_eq (hint : Integrable log μ) (α β k z y : ℝ) :
    stochRHS μ α β k z y = (log (z * k ^ α - y) + α * β / (1 - α * β) * log y) +
      β * (coefAs α β (∫ z, log z ∂μ) + coefC α β * ∫ z, log z ∂μ) := by
  unfold stochRHS
  rw [integral_stochValue hint]
  simp only [coefB]
  ring

/-- **Ex 2.6.** `v` satisfies the stochastic functional equation (3):
`v(k, z) = max_{0 < y < z k^α} {ln(z k^α − y) + β E[v(y, z′)]}`. -/
theorem stoch_bellman_isGreatest (hint : Integrable log μ) {α β k z : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) :
    IsGreatest (stochRHS μ α β k z '' Ioo 0 (z * k ^ α)) (stochValue α β (∫ z, log z ∂μ) k z) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hY : 0 < z * k ^ α := mul_pos hz (rpow_pos_of_pos hk α)
  refine ⟨⟨α * β * (z * k ^ α), ⟨mul_pos h0 hY, by nlinarith⟩,
    stochRHS_attained hint hα hβ hβ1 h1 hk hz⟩, ?_⟩
  rintro _ ⟨y, ⟨hy0, hyY⟩, rfl⟩
  rw [← stochRHS_attained hint hα hβ hβ1 h1 hk hz, stochRHS_eq hint, stochRHS_eq hint]
  have := log_tradeoff h0 h1 hY hy0 hyY
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring]
  linarith

/-- **Ex 2.6.** The policy (5), `y = αβ z k^α`, is the unique maximizer in (3). -/
theorem stoch_argmax_unique (hint : Integrable log μ) {α β k z y : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) (hy : 0 < y) (hyY : y < z * k ^ α)
    (hmax : stochValue α β (∫ z, log z ∂μ) k z ≤ stochRHS μ α β k z y) :
    y = α * β * (z * k ^ α) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hY : 0 < z * k ^ α := mul_pos hz (rpow_pos_of_pos hk α)
  rw [← stochRHS_attained hint hα hβ hβ1 h1 hk hz, stochRHS_eq hint, stochRHS_eq hint] at hmax
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring] at hmax
  exact log_tradeoff_unique h0 h1 hY hy hyY (by linarith)

/-! ### Expected utility along the policy -/

/-- The shock in period `t`: the known `z` in period `0`, the coordinate `ω t` afterwards. -/
def shock (z : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then z else ω t

/-- Capital along policy (5): `k_{t+1} = αβ z_t k_t^α`. -/
noncomputable def stochPath (α β k z : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => k
  | t + 1 => α * β * shock z ω t * stochPath α β k z ω t ^ α

/-- Consumption along (5): `c_t = (1 − αβ) z_t k_t^α`. -/
noncomputable def stochCons (α β k z : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℝ :=
  shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1)

/-- The product measure of i.i.d. shocks. -/
noncomputable abbrev shockMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => μ

theorem ae_shock_pos (hpos : ∀ᵐ z ∂μ, 0 < z) : ∀ᵐ ω ∂shockMeasure μ, ∀ t, 0 < ω t := by
  rw [ae_all_iff]
  intro t
  have h : ∀ᵐ x ∂(shockMeasure μ).map (fun ω => ω t), 0 < x := by
    rwa [Measure.infinitePi_map_eval]
  exact ae_of_ae_map (measurable_pi_apply t).aemeasurable h

theorem integrable_log_coord (hint : Integrable log μ) (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ => log (ω t)) (shockMeasure μ) := by
  have h : Integrable log ((shockMeasure μ).map (fun ω => ω t)) := by
    rwa [Measure.infinitePi_map_eval]
  exact h.comp_aemeasurable (measurable_pi_apply t).aemeasurable

theorem integral_log_coord (t : ℕ) :
    ∫ ω, log (ω t) ∂shockMeasure μ = ∫ z, log z ∂μ := by
  rw [← integral_map (measurable_pi_apply t).aemeasurable
    measurable_log.aestronglyMeasurable, Measure.infinitePi_map_eval]

/-- The expected log shock: `ln z` in period `0`, `E[ln z]` afterwards. -/
noncomputable def meanShock (μ : Measure ℝ) (z : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then log z else ∫ z, log z ∂μ

theorem integrable_log_shock (hint : Integrable log μ) (z : ℝ) (t : ℕ) :
    Integrable (fun ω => log (shock z ω t)) (shockMeasure μ) := by
  rcases t with _ | t
  · simp [shock]
  · simpa [shock] using integrable_log_coord hint (t + 1)

theorem integral_log_shock (z : ℝ) (t : ℕ) :
    ∫ ω, log (shock z ω t) ∂shockMeasure μ = meanShock μ z t := by
  rcases t with _ | t
  · simp [shock, meanShock]
  · simpa [shock, meanShock] using integral_log_coord (μ := μ) (t + 1)

/-- Almost surely, along (5), `ln k_{t+1} = ln(αβ) + ln z_t + α ln k_t` and capital is positive. -/
theorem ae_log_path (hpos : ∀ᵐ z ∂μ, 0 < z) {α β k z : ℝ} (h0 : 0 < α * β) (hk : 0 < k)
    (hz : 0 < z) :
    ∀ᵐ ω ∂shockMeasure μ, ∀ t, 0 < shock z ω t ∧ 0 < stochPath α β k z ω t ∧
      log (stochPath α β k z ω (t + 1)) =
        log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
  filter_upwards [ae_shock_pos hpos] with ω hω t
  have hsh : ∀ s, 0 < shock z ω s := fun s => by
    unfold shock; split_ifs
    · exact hz
    · exact hω s
  have hkp : ∀ s, 0 < stochPath α β k z ω s := fun s => by
    induction s with
    | zero => exact hk
    | succ s ih => exact mul_pos (mul_pos h0 (hsh s)) (rpow_pos_of_pos ih α)
  refine ⟨hsh t, hkp t, ?_⟩
  simp only [stochPath]
  rw [log_mul (mul_pos h0 (hsh t)).ne' (rpow_pos_of_pos (hkp t) α).ne', log_mul h0.ne' (hsh t).ne',
    log_rpow (hkp t)]

/-- The expected log capital, by the recursion `M_{t+1} = ln(αβ) + αM_t + E[ln z_t]`. -/
noncomputable def meanLogK (μ : Measure ℝ) (α β k z : ℝ) : ℕ → ℝ
  | 0 => log k
  | t + 1 => log (α * β) + α * meanLogK μ α β k z t + meanShock μ z t

/-- `ln k_t` is integrable with mean `M_t`. -/
theorem integral_log_path (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (h0 : 0 < α * β) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    Integrable (fun ω => log (stochPath α β k z ω t)) (shockMeasure μ) ∧
      ∫ ω, log (stochPath α β k z ω t) ∂shockMeasure μ = meanLogK μ α β k z t := by
  have hae := ae_log_path hpos h0 hk hz
  induction t with
  | zero => simp [stochPath, meanLogK]
  | succ t ih =>
    have heq : (fun ω => log (stochPath α β k z ω (t + 1))) =ᵐ[shockMeasure μ]
        fun ω => log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
      filter_upwards [hae] with ω hω
      exact (hω t).2.2
    have hint' : Integrable (fun ω => log (α * β) + log (shock z ω t) +
        α * log (stochPath α β k z ω t)) (shockMeasure μ) :=
      ((integrable_const _).add (integrable_log_shock hint z t)).add (ih.1.const_mul α)
    refine ⟨hint'.congr heq.symm, ?_⟩
    have hA : Integrable (fun ω => log (α * β) + log (shock z ω t)) (shockMeasure μ) :=
      (integrable_const _).add (integrable_log_shock hint z t)
    have e1 := integral_add hA (ih.1.const_mul α)
    have e2 := integral_add (integrable_const (log (α * β))) (integrable_log_shock hint z t)
    beta_reduce at e1 e2
    rw [integral_congr_ae heq, e1, e2, integral_const, integral_const_mul, ih.2,
      integral_log_shock]
    simp [meanLogK]
    ring

/-- Expected log consumption: `E[ln c_t] = ln(1 − αβ) + E[ln z_t] + αM_t`. -/
theorem integral_log_cons (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (h0 : 0 < α * β) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ =
      log (1 - α * β) + meanShock μ z t + α * meanLogK μ α β k z t := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have heq : (fun ω => log (stochCons α β k z ω t)) =ᵐ[shockMeasure μ]
      fun ω => log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
    filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
    obtain ⟨hs, hp, -⟩ := hω t
    unfold stochCons
    rw [show shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1) =
      (1 - α * β) * shock z ω t * stochPath α β k z ω t ^ α by simp only [stochPath]; ring,
      log_mul (mul_pos h1ab hs).ne' (rpow_pos_of_pos hp α).ne', log_mul h1ab.ne' hs.ne',
      log_rpow hp]
  have hi := (integral_log_path hpos hint h0 hk hz t).1
  have hA : Integrable (fun ω => log (1 - α * β) + log (shock z ω t)) (shockMeasure μ) :=
    (integrable_const _).add (integrable_log_shock hint z t)
  have e1 := integral_add hA (hi.const_mul α)
  have e2 := integral_add (integrable_const (log (1 - α * β))) (integrable_log_shock hint z t)
  beta_reduce at e1 e2
  rw [integral_congr_ae heq, e1, e2, integral_const, integral_const_mul,
    (integral_log_path hpos hint h0 hk hz t).2, integral_log_shock]
  simp

omit [IsProbabilityMeasure μ] in
/-- After period `0`, `M_{s+1} = αˢ M_1 + (ln(αβ) + m)(1 − αˢ)/(1 − α)`. -/
theorem meanLogK_succ {α β k z : ℝ} (hα1 : α < 1) (s : ℕ) :
    meanLogK μ α β k z (s + 1) = α ^ s * meanLogK μ α β k z 1 +
      (log (α * β) + ∫ z, log z ∂μ) * (1 - α ^ s) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + 1 = (s + 1) + 1 by rfl]
    conv_lhs => rw [meanLogK]
    rw [ih]
    simp only [meanShock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    field_simp
    ring

/-- **Ex 2.6.** Along policy (5), the expected discounted utility `∑ βᵗ E[ln c_t]` from `(k, z)`
is `v(k, z)`. -/
theorem hasSum_expected_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k) (hz : 0 < z) :
    HasSum (fun t => β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ)
      (stochValue α β (∫ z, log z ∂μ) k z) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  have h1ab : (1 - α * β) ≠ 0 := (sub_pos.2 h1).ne'
  set m := ∫ z, log z ∂μ
  set M1 := meanLogK μ α β k z 1
  -- the terms after period 0, as geometric series
  have hterm : ∀ s, β ^ (s + 1) * ∫ ω, log (stochCons α β k z ω (s + 1)) ∂shockMeasure μ =
      β * (log (1 - α * β) + m + α * (log (α * β) + m) / (1 - α)) * β ^ s +
        β * (α * M1 - α * (log (α * β) + m) / (1 - α)) * (α * β) ^ s := fun s => by
    rw [integral_log_cons hpos hint h0 h1 hk hz, meanLogK_succ hα1 s]
    simp only [meanShock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, mul_pow,
      pow_succ]
    field_simp
    ring
  have hg1 := hasSum_geometric_of_lt_one hβ.le hβ1
  have hg2 := hasSum_geometric_of_lt_one h0.le h1
  have htail := (hg1.mul_left (β * (log (1 - α * β) + m + α * (log (α * β) + m) / (1 - α)))).add
    (hg2.mul_left (β * (α * M1 - α * (log (α * β) + m) / (1 - α))))
  rw [← hasSum_nat_add_iff' 1]
  convert htail using 1
  · funext s
    exact hterm s
  · rw [sum_range_one, pow_zero, one_mul, integral_log_cons hpos hint h0 h1 hk hz]
    simp only [M1, meanLogK, meanShock, ↓reduceIte, stochValue, coefAs, coefB, coefC, m]
    field_simp
    ring

end StokeyLucasPrescott.Overview
