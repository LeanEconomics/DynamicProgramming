/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMLaborSupply.TaxesCycles
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Life-cycle profiles in the Imai–Keane model (Figure 12.6)

AKMM, §12.7, pp. 357–358, Figure 12.6. The model is the one of p. 357 with perfect foresight:
the wage `w_t = (1 + κΣ_{j<t}ℓ_j)w₀` (`ikWage`), the human-capital term
`H_t = κw₀Σ_{j=1}^{T−t}R^{−j}ℓ_{t+j}` (`ikfHC`) and the return to work `w_t + H_t`
(`ikfReturn`), linked to hours by (12.41), `ψℓ_t^{1/γ} = λ_t(1 − τ)(w_t + H_t)` (`eq_12_41`),
and the Euler equation `λ_t = βRλ_{t+1}`.

* **Backward induction for the human-capital term**: `H_T = 0` and
  `H_t = R^{−1}(κw₀ℓ_{t+1} + H_{t+1})` (`ikf_hc_last`, `ikf_hc_succ`); hence
  `H_t − H_{t+1} = R^{−1}(κw₀ℓ_{t+1} − (R − 1)H_{t+1})` (`ikf_hc_diff`). The wage rises by
  `κw₀ℓ_t` each period and never falls (`ikf_wage_succ`, `ikf_wage_step`); the return to work
  exceeds the wage before `T` and equals it at `T` (`ikf_return_vs_wage`).
* **"The human capital term … declines with age"** (p. 358): true for every hours path when
  `R ≤ 1` (`ikf_hc_antitone`, strict steps `ikf_hc_step_le_one`); for any `R > 0` at every age
  from which future hours do not exceed next period's (the declining phase of hours,
  `ikf_hc_step_peak`), and for constant hours, which is the text's argument "as clear from the
  sum" (`ikf_hc_const_hours`). It is **not** true in general when `R > 1`: in an explicit
  three-period economy (`R = 10`, `β = 1/10`, `σ = 2`, `γ = ψ = κ = w₀ = 1`, `τ = 0`) the
  optimum, proved globally optimal, has `H₀ < H₁` (`ikf_hc_rises`).
* **Hours profiles**: along any interior path satisfying (12.41) and the Euler equation, hours
  are nondecreasing when `R ≥ 1` and `βR ≤ 1`, strictly increasing if moreover `R > 1` or
  `βR < 1` (`ikf_hours_up`, `ikf_hours_up_strict`); nonincreasing when `R ≤ 1` and `βR ≥ 1`,
  strictly if `R < 1` or `βR > 1` (`ikf_hours_down`, `ikf_hours_down_strict`). At `R = β = 1`
  hours and the return to work are constant, the wage rises linearly and the human-capital term
  falls linearly to zero (`ikf_flat`): exactly "hours relatively flat while wages grow steeply"
  with a flat return to work, and a naive regression of hours on current wages recovers an
  elasticity of zero (`ikf_naive_gamma`, `ikf_flat_naive`). Instances: `ikf_instance_up`,
  `ikf_instance_down`, `ikf_instance_flat`.

Departures: the hump in hours and the fall of the wage late in life in Figure 12.6 are not
features of the model of p. 357 (the wage never falls; hours are monotone whenever `R − 1` and
`1 − βR` have the same weak sign); they are calibrated features of the plotted curves.
-/

namespace AKMM.LaborSupply

/-- The human-capital term of (12.41), `H_t = κw₀Σ_{j=1}^{T−t}R^{−j}ℓ_{t+j}` (AKMM, p. 357). -/
noncomputable def ikfHC (R κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  κ * w₀ * ∑ j ∈ Finset.range (T - t), (R⁻¹) ^ (j + 1) * l (t + j + 1)

/-- The return to work, wage plus human-capital term (AKMM, p. 357, Figure 12.6). -/
noncomputable def ikfReturn (R κ w₀ : ℝ) (T : ℕ) (l : ℕ → ℝ) (t : ℕ) : ℝ :=
  ikWage κ w₀ l t + ikfHC R κ w₀ T l t

/-- AKMM, p. 358, Figure 12.6: the human-capital term is zero in the last period (and after). -/
theorem ikf_hc_last (R κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (ht : T ≤ t) :
    ikfHC R κ w₀ T l t = 0 := by
  unfold ikfHC
  rw [Nat.sub_eq_zero_of_le ht, Finset.sum_range_zero, mul_zero]

/-- AKMM, p. 358 (backward induction for (12.41)): for `t < T`,
`H_t = R^{−1}(κw₀ℓ_{t+1} + H_{t+1})`. -/
theorem ikf_hc_succ (R κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (ht : t < T) :
    ikfHC R κ w₀ T l t = R⁻¹ * (κ * w₀ * l (t + 1) + ikfHC R κ w₀ T l (t + 1)) := by
  unfold ikfHC
  rw [show T - t = (T - (t + 1)) + 1 by omega, Finset.sum_range_succ']
  have hs : ∀ j ∈ Finset.range (T - (t + 1)), (R⁻¹) ^ (j + 1 + 1) * l (t + (j + 1) + 1) =
      R⁻¹ * ((R⁻¹) ^ (j + 1) * l (t + 1 + j + 1)) := by
    intro j _
    rw [show t + (j + 1) + 1 = t + 1 + j + 1 by ring]
    ring
  rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
  simp only [zero_add, pow_one, add_zero]
  ring

/-- AKMM, p. 358: the one-period change of the human-capital term,
`H_t − H_{t+1} = R^{−1}(κw₀ℓ_{t+1} − (R − 1)H_{t+1})` for `t < T`, `R ≠ 0`. -/
theorem ikf_hc_diff {R : ℝ} (κ w₀ : ℝ) {T t : ℕ} (l : ℕ → ℝ) (hR : R ≠ 0) (ht : t < T) :
    ikfHC R κ w₀ T l t - ikfHC R κ w₀ T l (t + 1) =
      R⁻¹ * (κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1)) := by
  rw [ikf_hc_succ R κ w₀ l ht]
  field_simp
  ring

/-- AKMM, p. 357: the wage rises by `κw₀ℓ_t`, `w_{t+1} = w_t + κw₀ℓ_t`. -/
theorem ikf_wage_succ (κ w₀ : ℝ) (l : ℕ → ℝ) (t : ℕ) :
    ikWage κ w₀ l (t + 1) = ikWage κ w₀ l t + κ * w₀ * l t := by
  unfold ikWage
  rw [Finset.sum_range_succ]
  ring

/-- AKMM, p. 357, Figure 12.6: with `κw₀ ≥ 0` and `ℓ_t ≥ 0` the wage never falls, and it
rises strictly when `κw₀ > 0` and `ℓ_t > 0`. -/
theorem ikf_wage_step {κ w₀ : ℝ} {l : ℕ → ℝ} {t : ℕ} (hκ : 0 ≤ κ * w₀) (hl : 0 ≤ l t) :
    ikWage κ w₀ l t ≤ ikWage κ w₀ l (t + 1) ∧
      (0 < κ * w₀ → 0 < l t → ikWage κ w₀ l t < ikWage κ w₀ l (t + 1)) := by
  rw [ikf_wage_succ]
  exact ⟨by nlinarith, fun h1 h2 => by nlinarith⟩

/-- AKMM, p. 358: the human-capital term is nonnegative when `R > 0`, `κw₀ ≥ 0` and hours are
nonnegative up to `T`. -/
theorem ikf_hc_nonneg {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) (t : ℕ) : 0 ≤ ikfHC R κ w₀ T l t := by
  unfold ikfHC
  refine mul_nonneg hκ (Finset.sum_nonneg fun j hj => ?_)
  rw [Finset.mem_range] at hj
  exact mul_nonneg (pow_nonneg (inv_nonneg.2 hR.le) _) (hl _ (by omega))

/-- AKMM, p. 357, Figure 12.6: the return to work equals the wage in the last period, and
exceeds it before when `κw₀ > 0` and next period's hours are positive. -/
theorem ikf_return_vs_wage {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 < κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) :
    ikfReturn R κ w₀ T l T = ikWage κ w₀ l T ∧
      ∀ t < T, 0 < l (t + 1) → ikWage κ w₀ l t < ikfReturn R κ w₀ T l t := by
  refine ⟨by rw [ikfReturn, ikf_hc_last R κ w₀ l le_rfl, add_zero], fun t ht hpos => ?_⟩
  rw [ikfReturn, ikf_hc_succ R κ w₀ l ht]
  have h0 := ikf_hc_nonneg hR hκ.le hl (t + 1)
  have : 0 < R⁻¹ * (κ * w₀ * l (t + 1) + ikfHC R κ w₀ T l (t + 1)) :=
    mul_pos (inv_pos.2 hR) (by nlinarith)
  linarith

/-- AKMM, p. 358, "the human capital term is high early on, but it declines with age", one step,
for `0 < R ≤ 1`: `H_{t+1} ≤ H_t`, strictly when `κw₀ > 0` and `ℓ_{t+1} > 0`. -/
theorem ikf_hc_step_le_one {R κ w₀ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 ≤ l s) (ht : t < T) :
    ikfHC R κ w₀ T l (t + 1) ≤ ikfHC R κ w₀ T l t ∧
      (0 < κ * w₀ → 0 < l (t + 1) → ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t) := by
  have hd := ikf_hc_diff κ w₀ l hR.ne' ht
  have hH := ikf_hc_nonneg hR hκ hl (t + 1)
  have hlt := hl (t + 1) (by omega)
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have hA : 0 ≤ κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  refine ⟨by nlinarith [mul_nonneg hRi.le hA], fun h1 h2 => ?_⟩
  have hA' : 0 < κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  nlinarith [mul_pos hRi hA']

/-- AKMM, p. 358, "the human capital term … declines with age": for `0 < R ≤ 1`, `κw₀ ≥ 0` and
nonnegative hours, the human-capital term is antitone in age over the whole life cycle. -/
theorem ikf_hc_antitone {R κ w₀ : ℝ} {T : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 ≤ l s) : Antitone (ikfHC R κ w₀ T l) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rcases lt_or_ge n T with hn | hn
  · exact (ikf_hc_step_le_one hR hR1 hκ hl hn).1
  · rw [ikf_hc_last R κ w₀ l (by omega)]
    exact ikf_hc_nonneg hR hκ hl n

/-- The geometric identity `(R − 1)Σ_{j<n}R^{−(j+1)} = 1 − R^{−n}` used for the human-capital
term (AKMM, p. 358). -/
theorem ikf_geom {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (R - 1) * ∑ j ∈ Finset.range n, (R⁻¹) ^ (j + 1) = 1 - (R⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have : R * (R⁻¹) ^ (n + 1) = (R⁻¹) ^ n := by
      rw [pow_succ]; field_simp
    linear_combination this

/-- AKMM, p. 358, the decline of the human-capital term for any `R > 0`, in the declining phase
of hours: if no hours after `t + 1` exceed `ℓ_{t+1}`, then `H_{t+1} ≤ H_t`, strictly when
`κw₀ > 0` and `ℓ_{t+1} > 0`. (For `R ≤ 1` no condition is needed: `ikf_hc_step_le_one`.) -/
theorem ikf_hc_step_peak {R κ w₀ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 ≤ l s) (ht : t < T) (hpeak : ∀ s, t + 1 < s → s ≤ T → l s ≤ l (t + 1)) :
    ikfHC R κ w₀ T l (t + 1) ≤ ikfHC R κ w₀ T l t ∧
      (0 < κ * w₀ → 0 < l (t + 1) → ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t) := by
  rcases le_total R 1 with hR1 | hR1
  · exact ikf_hc_step_le_one hR hR1 hκ hl ht
  have hd := ikf_hc_diff κ w₀ l hR.ne' ht
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  set n := T - (t + 1) with hn
  have hbound : ikfHC R κ w₀ T l (t + 1) ≤
      κ * w₀ * (l (t + 1) * ∑ j ∈ Finset.range n, (R⁻¹) ^ (j + 1)) := by
    unfold ikfHC
    refine mul_le_mul_of_nonneg_left ?_ hκ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 := hpeak (t + 1 + j + 1) (by omega) (by omega)
    have h2 : 0 ≤ (R⁻¹) ^ (j + 1) := pow_nonneg hRi.le _
    nlinarith
  have hg := ikf_geom hR.ne' n
  have hpow : 0 < (R⁻¹) ^ n := pow_pos hRi n
  have hlt := hl (t + 1) (by omega)
  -- `(R − 1)H_{t+1} ≤ κw₀ℓ_{t+1}(1 − R^{−n})`
  have hkey : (R - 1) * ikfHC R κ w₀ T l (t + 1) ≤
      κ * w₀ * l (t + 1) * (1 - (R⁻¹) ^ n) := by
    have := mul_le_mul_of_nonneg_left hbound (by linarith : (0 : ℝ) ≤ R - 1)
    rw [← hg] at *
    nlinarith
  have hA : κ * w₀ * l (t + 1) * (R⁻¹) ^ n ≤
      κ * w₀ * l (t + 1) - (R - 1) * ikfHC R κ w₀ T l (t + 1) := by nlinarith
  refine ⟨?_, fun h1 h2 => ?_⟩
  · have : 0 ≤ κ * w₀ * l (t + 1) * (R⁻¹) ^ n := mul_nonneg (mul_nonneg hκ hlt) hpow.le
    nlinarith [mul_nonneg hRi.le (le_trans this hA)]
  · have : 0 < κ * w₀ * l (t + 1) * (R⁻¹) ^ n := mul_pos (mul_pos h1 h2) hpow
    nlinarith [mul_pos hRi (lt_of_lt_of_le this hA)]

/-- AKMM, p. 358, "the return to working more in order to increase future wages is larger when
the individual is young … as clear from the sum in equation (12.41)": with constant positive
hours and `κw₀ > 0`, the human-capital term strictly decreases every period, for every `R > 0`.
-/
theorem ikf_hc_const_hours {R κ w₀ ℓ : ℝ} {T t : ℕ} {l : ℕ → ℝ} (hR : 0 < R)
    (hκ : 0 < κ * w₀) (hℓ : 0 < ℓ) (hl : ∀ s ≤ T, l s = ℓ) (ht : t < T) :
    ikfHC R κ w₀ T l (t + 1) < ikfHC R κ w₀ T l t := by
  have hl0 : ∀ s ≤ T, 0 ≤ l s := fun s hs => (hl s hs).symm ▸ hℓ.le
  refine (ikf_hc_step_peak hR hκ.le hl0 ht fun s _ hs => ?_).2 hκ ?_
  · rw [hl s hs, hl (t + 1) (by omega)]
  · rw [hl (t + 1) (by omega)]; exact hℓ

/-- AKMM, (12.41), p. 357: along an interior path satisfying (12.41), the return to work is
positive at every age `s ≤ T` (when `ψ > 0`, `τ < 1`, `λ_s > 0`, `ℓ_s > 0`). -/
theorem ikf_return_pos {R κ w₀ ψ γ τ : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hτ : τ < 1)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    {s : ℕ} (hs : s ≤ T) : 0 < ikfReturn R κ w₀ T l s := by
  have h1 : 0 < ψ * l s ^ (1 / γ) := mul_pos hψ (Real.rpow_pos_of_pos (hl s hs) _)
  rw [hfoc s hs] at h1
  exact pos_of_mul_pos_right h1 (mul_pos (hlam s hs) (by linarith)).le

/-- AKMM, p. 358, Figure 12.6, hours over the life cycle: along any interior path satisfying
(12.41) and the Euler equation `λ_t = βRλ_{t+1}`, if `R ≥ 1` and `βR ≤ 1`, hours never fall:
`ℓ_t ≤ ℓ_{t+1}`. -/
theorem ikf_hours_up {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR1 : 1 ≤ R) (hβR : β * R ≤ 1) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l t ≤ l (t + 1) := by
  refine le_of_not_gt fun h => ?_
  have hR : 0 < R := by linarith
  have h1 := Real.rpow_lt_rpow (hl (t + 1) (by omega)).le h (by positivity : 0 < 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ0 := ikf_return_pos hψ hτ hl hlam hfoc ht.le
  have hl1 := hlam (t + 1) ht
  have hlt : lam t ≤ lam (t + 1) := by rw [heul t ht]; nlinarith
  -- `λ_{t+1}Q_{t+1} < λ_tQ_t ≤ λ_{t+1}Q_t`
  have hA : lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) < lam t * ikfReturn R κ w₀ T l t := by
    have : lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) <
        lam t * (1 - τ) * ikfReturn R κ w₀ T l t := by nlinarith
    nlinarith
  have hQ : ikfReturn R κ w₀ T l (t + 1) < ikfReturn R κ w₀ T l t := by nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hRi0 : 0 < R⁻¹ := inv_pos.2 hR
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hB : 0 ≤ l t - R⁻¹ * l (t + 1) := by nlinarith [hl (t + 1) (by omega)]
  nlinarith [mul_nonneg hκ hB, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - R⁻¹) hH]

/-- AKMM, p. 358, Figure 12.6: under the hypotheses of `ikf_hours_up`, hours rise strictly if
moreover `R > 1` (with `κw₀ > 0`) or `βR < 1`. -/
theorem ikf_hours_up_strict {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR1 : 1 ≤ R) (hβR : β * R ≤ 1) (hκ : 0 ≤ κ * w₀)
    (hstrict : (1 < R ∧ 0 < κ * w₀) ∨ β * R < 1)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l t < l (t + 1) := by
  refine lt_of_not_ge fun h => ?_
  have hR : 0 < R := by linarith
  have h1 := Real.rpow_le_rpow (hl (t + 1) (by omega)).le h (by positivity : 0 ≤ 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ0 := ikf_return_pos hψ hτ hl hlam hfoc ht.le
  have hl1 := hlam (t + 1) ht
  have hA : lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) ≤ lam t * ikfReturn R κ w₀ T l t := by
    have : lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) ≤
        lam t * (1 - τ) * ikfReturn R κ w₀ T l t := by nlinarith
    nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hRi0 : 0 < R⁻¹ := inv_pos.2 hR
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hlt1 := hl (t + 1) (by omega)
  have hH' : 0 ≤ (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) :=
    mul_nonneg (by linarith) hH
  rcases hstrict with ⟨hR1', hκ'⟩ | hβR'
  · have hlt : lam t ≤ lam (t + 1) := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l (t + 1) ≤ ikfReturn R κ w₀ T l t := by nlinarith
    have hRi1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR1'
    have hB : 0 < l t - R⁻¹ * l (t + 1) := by nlinarith
    nlinarith [mul_pos hκ' hB]
  · have hlt : lam t < lam (t + 1) := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l (t + 1) < ikfReturn R κ w₀ T l t := by nlinarith
    have hB : 0 ≤ l t - R⁻¹ * l (t + 1) := by nlinarith
    nlinarith [mul_nonneg hκ hB]

/-- AKMM, p. 358, Figure 12.6, hours over the life cycle: along any interior path satisfying
(12.41) and the Euler equation, if `0 < R ≤ 1` and `βR ≥ 1`, hours never rise:
`ℓ_{t+1} ≤ ℓ_t`. -/
theorem ikf_hours_down {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR : 0 < R) (hR1 : R ≤ 1) (hβR : 1 ≤ β * R) (hκ : 0 ≤ κ * w₀)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l (t + 1) ≤ l t := by
  refine le_of_not_gt fun h => ?_
  have h1 := Real.rpow_lt_rpow (hl t ht.le).le h (by positivity : 0 < 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ1 := ikf_return_pos hψ hτ hl hlam hfoc (s := t + 1) ht
  have hl1 := hlam (t + 1) ht
  have hlt : lam (t + 1) ≤ lam t := by rw [heul t ht]; nlinarith
  have hA : lam t * ikfReturn R κ w₀ T l t < lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) := by
    have : lam t * (1 - τ) * ikfReturn R κ w₀ T l t <
        lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    nlinarith
  have hl0 := hlam t ht.le
  have hQ : ikfReturn R κ w₀ T l t < ikfReturn R κ w₀ T l (t + 1) := by nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : 1 ≤ R⁻¹ := one_le_inv₀ hR |>.2 hR1
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hB : l t - R⁻¹ * l (t + 1) ≤ 0 := by nlinarith [hl (t + 1) (by omega)]
  nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ -(l t - R⁻¹ * l (t + 1))),
    mul_nonneg (by linarith : (0 : ℝ) ≤ R⁻¹ - 1) hH]

/-- AKMM, p. 358, Figure 12.6: under the hypotheses of `ikf_hours_down`, hours fall strictly if
moreover `R < 1` (with `κw₀ > 0`) or `βR > 1`. -/
theorem ikf_hours_down_strict {R β κ w₀ ψ γ τ : ℝ} {T t : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ)
    (hγ : 0 < γ) (hτ : τ < 1) (hR : 0 < R) (hR1 : R ≤ 1) (hβR : 1 ≤ β * R) (hκ : 0 ≤ κ * w₀)
    (hstrict : (R < 1 ∧ 0 < κ * w₀) ∨ 1 < β * R)
    (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = β * R * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn R κ w₀ T l s)
    (ht : t < T) : l (t + 1) < l t := by
  refine lt_of_not_ge fun h => ?_
  have h1 := Real.rpow_le_rpow (hl t ht.le).le h (by positivity : 0 ≤ 1 / γ)
  have hf0 := hfoc t ht.le
  have hf1 := hfoc (t + 1) ht
  have hτ' : 0 < 1 - τ := by linarith
  have hQ1 := ikf_return_pos hψ hτ hl hlam hfoc (s := t + 1) ht
  have hl1 := hlam (t + 1) ht
  have hl0 := hlam t ht.le
  have hA : lam t * ikfReturn R κ w₀ T l t ≤ lam (t + 1) * ikfReturn R κ w₀ T l (t + 1) := by
    have : lam t * (1 - τ) * ikfReturn R κ w₀ T l t ≤
        lam (t + 1) * (1 - τ) * ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    nlinarith
  have hD : ikfReturn R κ w₀ T l (t + 1) - ikfReturn R κ w₀ T l t =
      κ * w₀ * (l t - R⁻¹ * l (t + 1)) + (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) := by
    unfold ikfReturn; rw [ikf_wage_succ, ikf_hc_succ R κ w₀ l ht]; ring
  have hRi : 1 ≤ R⁻¹ := one_le_inv₀ hR |>.2 hR1
  have hH := ikf_hc_nonneg hR hκ (fun s hs => (hl s hs).le) (t + 1)
  have hH' : (1 - R⁻¹) * ikfHC R κ w₀ T l (t + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hH
  have hlt1 := hl (t + 1) (by omega)
  rcases hstrict with ⟨hR1', hκ'⟩ | hβR'
  · have hlt : lam (t + 1) ≤ lam t := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l t ≤ ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    have hRi1 : 1 < R⁻¹ := one_lt_inv₀ hR |>.2 hR1'
    have hB : l t - R⁻¹ * l (t + 1) < 0 := by nlinarith
    nlinarith [mul_pos hκ' (by linarith : (0 : ℝ) < -(l t - R⁻¹ * l (t + 1)))]
  · have hlt : lam (t + 1) < lam t := by rw [heul t ht]; nlinarith
    have hQ : ikfReturn R κ w₀ T l t < ikfReturn R κ w₀ T l (t + 1) := by nlinarith
    have hB : l t - R⁻¹ * l (t + 1) ≤ 0 := by nlinarith
    nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ -(l t - R⁻¹ * l (t + 1)))]

/-- AKMM, p. 358, Figure 12.6, "hours are relatively flat while wages grow steeply" and the
return to work is "much flatter": at `R = β = 1`, along any interior path satisfying (12.41) and
the Euler equation, for every `t ≤ T`: hours are constant, `ℓ_t = ℓ₀`; the wage rises linearly,
`w_t = (1 + κℓ₀t)w₀`; the human-capital term falls linearly to zero, `H_t = κw₀ℓ₀(T − t)`; and
the return to work is constant, `w_t + H_t = (1 + κℓ₀T)w₀`. -/
theorem ikf_flat {κ w₀ ψ γ τ : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hτ : τ < 1) (hκ : 0 ≤ κ * w₀) (hl : ∀ s ≤ T, 0 < l s) (hlam : ∀ s ≤ T, 0 < lam s)
    (heul : ∀ s < T, lam s = 1 * 1 * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn 1 κ w₀ T l s) :
    ∀ t ≤ T, l t = l 0 ∧ ikWage κ w₀ l t = (1 + κ * l 0 * t) * w₀ ∧
      ikfHC 1 κ w₀ T l t = κ * w₀ * l 0 * ((T : ℝ) - t) ∧
      ikfReturn 1 κ w₀ T l t = (1 + κ * l 0 * T) * w₀ := by
  have hstep : ∀ s < T, l (s + 1) = l s := fun s hs =>
    le_antisymm
      (ikf_hours_down hψ hγ hτ one_pos le_rfl (by norm_num) hκ hl hlam heul hfoc hs)
      (ikf_hours_up hψ hγ hτ le_rfl (by norm_num) hκ hl hlam heul hfoc hs)
  have hconst : ∀ t ≤ T, l t = l 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ n ih => intro hn; rw [hstep n (by omega), ih (by omega)]
  have hwage : ∀ t ≤ T, ikWage κ w₀ l t = (1 + κ * l 0 * t) * w₀ := by
    intro t ht
    unfold ikWage
    rw [Finset.sum_congr rfl fun j hj => hconst j (by rw [Finset.mem_range] at hj; omega),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hhc : ∀ t ≤ T, ikfHC 1 κ w₀ T l t = κ * w₀ * l 0 * ((T : ℝ) - t) := by
    intro t ht
    unfold ikfHC
    rw [Finset.sum_congr rfl fun j hj => by
        rw [inv_one, one_pow, one_mul, hconst (t + j + 1) (by rw [Finset.mem_range] at hj; omega)],
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub ht]
    ring
  intro t ht
  refine ⟨hconst t ht, hwage t ht, hhc t ht, ?_⟩
  rw [ikfReturn, hwage t ht, hhc t ht]
  ring

/-- AKMM, p. 358, "naively estimating `γ` from the relation between current wages and current
hours would lead one to underestimate its true value": if the same hours `ℓ` satisfy
`ℓ = A w^g` at two different wages `0 < w < w′` (`A ≠ 0`), the fitted elasticity is `g = 0`. -/
theorem ikf_naive_gamma {A g w w' ℓ : ℝ} (hA : A ≠ 0) (hw : 0 < w) (hww : w < w')
    (h0 : ℓ = A * w ^ g) (h1 : ℓ = A * w' ^ g) : g = 0 := by
  have he : w ^ g = w' ^ g := mul_left_cancel₀ hA (h0.symm.trans h1)
  rcases lt_trichotomy g 0 with hg | hg | hg
  · exact absurd he (Real.rpow_lt_rpow_of_neg hw hww hg).ne'
  · exact hg
  · exact absurd he (Real.rpow_lt_rpow hw.le hww hg).ne

/-- AKMM, p. 358: at `R = β = 1` with `κ > 0`, `w₀ > 0` and `T ≥ 1`, the profile of `ikf_flat`
makes the naive estimate of the elasticity of hours with respect to the current wage zero,
whatever the true `γ > 0`: if `ℓ_t = Aw_t^g` for all `t ≤ T`, `A ≠ 0`, then `g = 0`. -/
theorem ikf_flat_naive {κ w₀ ψ γ τ A g : ℝ} {T : ℕ} {l lam : ℕ → ℝ} (hψ : 0 < ψ) (hγ : 0 < γ)
    (hτ : τ < 1) (hκ : 0 < κ) (hw₀ : 0 < w₀) (hT : 1 ≤ T) (hl : ∀ s ≤ T, 0 < l s)
    (hlam : ∀ s ≤ T, 0 < lam s) (heul : ∀ s < T, lam s = 1 * 1 * lam (s + 1))
    (hfoc : ∀ s ≤ T, ψ * l s ^ (1 / γ) = lam s * (1 - τ) * ikfReturn 1 κ w₀ T l s)
    (hA : A ≠ 0) (hfit : ∀ t ≤ T, l t = A * ikWage κ w₀ l t ^ g) : g = 0 := by
  have hf := ikf_flat hψ hγ hτ (mul_pos hκ hw₀).le hl hlam heul hfoc
  have h0 := hf 0 (Nat.zero_le _)
  have h1 := hf 1 hT
  have hl0 := hl 0 (Nat.zero_le _)
  refine ikf_naive_gamma hA (w := ikWage κ w₀ l 0) (w' := ikWage κ w₀ l 1) ?_ ?_
    (hfit 0 (Nat.zero_le _)) (h1.1 ▸ hfit 1 hT)
  · rw [h0.2.1]; norm_num; exact hw₀
  · rw [h0.2.1, h1.2.1]; push_cast
    nlinarith [mul_pos (mul_pos hκ hl0) hw₀]

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_hours_up_strict` are satisfiable
(`T = 1`, `R = 2`, `β = 1/2`, `λ ≡ 1`, `ψ = γ = κ = w₀ = 1`, `τ = 0`, `ℓ = (3, 4)`). -/
theorem ikf_instance_up :
    let l : ℕ → ℝ := fun t => if t = 0 then 3 else 4
    (∀ s ≤ 1, (1 : ℝ) * l s ^ (1 / (1 : ℝ)) = 1 * (1 - 0) * ikfReturn 2 1 1 1 l s) ∧
      (1 : ℝ) = 1 / 2 * 2 * 1 ∧ l 0 < l 1 := by
  intro l
  refine ⟨fun s hs => ?_, by norm_num, by norm_num [l]⟩
  interval_cases s <;>
    simp [l, ikfReturn, ikfHC, ikWage] <;> norm_num

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_hours_down_strict` are satisfiable
(`T = 1`, `R = 1/2`, `β = 2`, `λ ≡ 1`, `ψ = 3`, `γ = κ = w₀ = 1`, `τ = 0`,
`ℓ = (5/7, 4/7)`). -/
theorem ikf_instance_down :
    let l : ℕ → ℝ := fun t => if t = 0 then 5 / 7 else 4 / 7
    (∀ s ≤ 1, (3 : ℝ) * l s ^ (1 / (1 : ℝ)) = 1 * (1 - 0) * ikfReturn (1 / 2) 1 1 1 l s) ∧
      (1 : ℝ) = 2 * (1 / 2) * 1 ∧ l 1 < l 0 := by
  intro l
  refine ⟨fun s hs => ?_, by norm_num, by norm_num [l]⟩
  interval_cases s <;>
    simp [l, ikfReturn, ikfHC, ikWage] <;> norm_num

/-- AKMM, p. 358, Figure 12.6: the hypotheses of `ikf_flat` are satisfiable
(`T = 1`, `R = β = 1`, `λ ≡ 1`, `ψ = 2`, `γ = κ = w₀ = 1`, `τ = 0`, `ℓ ≡ 1`). -/
theorem ikf_instance_flat :
    (∀ s ≤ 1, (2 : ℝ) * (fun _ => (1 : ℝ)) s ^ (1 / (1 : ℝ)) =
      1 * (1 - 0) * ikfReturn 1 1 1 1 (fun _ => 1) s) := by
  intro s hs
  interval_cases s <;>
    simp [ikfReturn, ikfHC, ikWage] <;> norm_num

/-- The hours of the counterexample of `ikf_hc_rises`: `ℓ = (103/77, 20/7, 400/77)`. -/
noncomputable def ikfCexHours (t : ℕ) : ℝ :=
  if t = 0 then 103 / 77 else if t = 1 then 20 / 7 else 400 / 77

/-- AKMM, p. 358, "the human capital term … declines with age" **fails for `R > 1`** in
general. Three periods (`T = 2`), `R = 10`, `β = 1/10`, `u = crraU 2` (`σ = 2`),
`v = disutil 1 1` (`ψ = γ = 1`), `κ = w₀ = 1`, `τ = 0`: the plan `c ≡ 1`,
`ℓ = (103/77, 20/7, 400/77)` (i) satisfies (12.41) with `λ ≡ 1` and the Euler equation,
(ii) is globally optimal among all plans `(c, ℓ)` with `c > 0` that satisfy the same lifetime
budget, and (iii) has `H₀ = 26/77 < 40/77 = H₁`: the human-capital term rises from age 0 to 1. -/
theorem ikf_hc_rises :
    (∀ s ≤ 2, (1 : ℝ) * ikfCexHours s ^ (1 / (1 : ℝ)) =
      1 * (1 - 0) * ikfReturn 10 1 1 2 ikfCexHours s) ∧
    (1 : ℝ) = 1 / 10 * 10 * 1 ∧
    (∀ c l : ℕ → ℝ, (∀ t ≤ 2, 0 < c t) →
      ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * c t - ikEarnings 10 0 1 1 2 l ≤
        ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * 1 - ikEarnings 10 0 1 1 2 ikfCexHours →
      ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * (crraU 2 (c t) - disutil 1 1 (l t)) ≤
        ∑ t ∈ Finset.range 3, (10⁻¹ : ℝ) ^ t * (crraU 2 1 - disutil 1 1 (ikfCexHours t))) ∧
    ikfHC 10 1 1 2 ikfCexHours 0 = 26 / 77 ∧ ikfHC 10 1 1 2 ikfCexHours 1 = 40 / 77 := by
  refine ⟨fun s hs => ?_, by norm_num, fun c l hc hbud => ?_, ?_, ?_⟩
  · interval_cases s <;>
      simp [ikfCexHours, ikfReturn, ikfHC, ikWage, Finset.sum_range_succ] <;> norm_num
  · have hu : ∀ x : ℝ, 0 < x → crraU 2 x ≤ x - 2 := by
      intro x hx
      have : crraU 2 x = -x⁻¹ := by
        unfold crraU
        simp only [show (2 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
        rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
        ring
      rw [this]
      have : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
      nlinarith [sq_nonneg (x - 1), inv_pos.2 hx]
    have hu1 : crraU 2 1 = -1 := by
      unfold crraU
      simp only [show (2 : ℝ) ≠ 1 by norm_num, ↓reduceIte]
      rw [Real.one_rpow]
      norm_num
    have hv : ∀ x : ℝ, disutil 1 1 x = x ^ 2 / 2 := by
      intro x
      unfold disutil
      rw [show (1 : ℝ) + 1 / 1 = 2 by norm_num, Real.rpow_two]
      ring
    have h0 := hu (c 0) (hc 0 (by norm_num))
    have h1 := hu (c 1) (hc 1 (by norm_num))
    have h2 := hu (c 2) (hc 2 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ikEarnings, ikWage, hv, hu1,
      ikfCexHours] at hbud ⊢
    norm_num at hbud ⊢
    nlinarith [sq_nonneg (l 0 - 103 / 77 - (l 1 - 20 / 7) / 10 - (l 2 - 400 / 77) / 100),
      sq_nonneg (l 1 - 20 / 7 - 11 / 90 * (l 2 - 400 / 77)), sq_nonneg (l 2 - 400 / 77)]
  · simp [ikfCexHours, ikfHC, Finset.sum_range_succ]; norm_num
  · simp [ikfCexHours, ikfHC]; norm_num

end AKMM.LaborSupply
