/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The log fishing problem behind the Great Fish War

Miao, §21.3, pp. 755–757. Every best-response problem of §21.3 (each country in the Markov
perfect equilibrium, the Stackelberg leader, and the Stackelberg follower of Exercise 21.3)
reduces to one problem: given the stock `x`, catch `c ∈ (0, Rx)`, leaving the stock
`x' = (θ(Rx − c))^α` for next period, to maximise `∑ βᵗ ln c_t`. Here `R x` is what the other
country leaves and `θ` the share of the remainder that survives its reaction.

We solve it by the guess-and-verify method of the text: `V(x) = κ ln x + ν` with
`κ = 1/(1 − αβ)` solves the Bellman equation, the unique maximiser being `c = (1 − αβ) R x`
(`dg_fp_bellman`, `dg_fp_bellman_eq`, `dg_fp_bellman_unique`). Coefficient matching forces
`κ = 1/(1 − αβ)` (`dg_fp_kappa_forced`). Then `V(x₀)` is the value of the problem: every
feasible plan whose discounted utility series converges does no better (`dg_fp_optimal`), and
the policy plan attains it (`dg_fp_policy_value`). Along the policy plan the stock converges to
`x̄ = (θαβR)^{α/(1−α)}` (`dg_fp_path_tendsto`).

The maximisation step is the elementary fact that `ln c + K ln(R − c)` has its unique maximum on
`(0, R)` at `c = R/(1 + K)` (`dg_log_max`), proved from `ln y ≤ y − 1`.
-/

namespace Miao.DynamicGames

/-- The maximisation step of §21.3 (Miao, pp. 756–757): for `R, K > 0` and `0 < c < R`,
`ln c + K ln(R − c) ≤ ln c* + K ln(R − c*)` with `c* = R/(1 + K)`, strictly unless `c = c*`. -/
theorem dg_log_max {R K c : ℝ} (hR : 0 < R) (hK : 0 < K) (hc0 : 0 < c) (hcR : c < R) :
    Real.log c + K * Real.log (R - c) ≤
      Real.log (R / (1 + K)) + K * Real.log (R - R / (1 + K)) ∧
    (c ≠ R / (1 + K) → Real.log c + K * Real.log (R - c) <
      Real.log (R / (1 + K)) + K * Real.log (R - R / (1 + K))) := by
  have h1K : 0 < 1 + K := by linarith
  have hcs : 0 < R / (1 + K) := div_pos hR h1K
  have hds : R - R / (1 + K) = K * R / (1 + K) := by field_simp; ring
  have hdp : 0 < R - R / (1 + K) := by rw [hds]; positivity
  have hRc : 0 < R - c := by linarith
  have e1 : Real.log c - Real.log (R / (1 + K)) = Real.log (c / (R / (1 + K))) :=
    (Real.log_div hc0.ne' hcs.ne').symm
  have e2 : Real.log (R - c) - Real.log (R - R / (1 + K)) =
      Real.log ((R - c) / (R - R / (1 + K))) := (Real.log_div hRc.ne' hdp.ne').symm
  have hsum : (c / (R / (1 + K)) - 1) + K * ((R - c) / (R - R / (1 + K)) - 1) = 0 := by
    rw [hds]; field_simp; ring
  have hq1 : 0 < c / (R / (1 + K)) := div_pos hc0 hcs
  have hq2 : 0 < (R - c) / (R - R / (1 + K)) := div_pos hRc hdp
  have l2 := Real.log_le_sub_one_of_pos hq2
  constructor
  · have l1 := Real.log_le_sub_one_of_pos hq1
    nlinarith [mul_le_mul_of_nonneg_left l2 hK.le]
  · intro hne
    have hne1 : c / (R / (1 + K)) ≠ 1 := by
      intro h
      exact hne ((div_eq_one_iff_eq hcs.ne').mp h)
    have l1 := Real.log_lt_sub_one_of_pos hq1 hne1
    nlinarith [mul_le_mul_of_nonneg_left l2 hK.le]

/-- The next stock `x' = (θ(Rx − c))^α` of the fishing problem. -/
noncomputable def dg_fpNext (α R θ x c : ℝ) : ℝ := (θ * (R * x - c)) ^ α

/-- The coefficient `κ = 1/(1 − αβ)` of `ln x` in the value function. -/
noncomputable def dg_fpKappa (α β : ℝ) : ℝ := 1 / (1 - α * β)

/-- The constant `ν = (ln((1 − αβ)R) + K ln(αβR) + K ln θ)/(1 − β)` of the value function, with
`K = αβκ = αβ/(1 − αβ)`. -/
noncomputable def dg_fpNu (α β R θ : ℝ) : ℝ :=
  (Real.log ((1 - α * β) * R) + α * β * dg_fpKappa α β * Real.log (α * β * R) +
    α * β * dg_fpKappa α β * Real.log θ) / (1 - β)

/-- The conjectured value function `V(x) = κ ln x + ν` (Miao, p. 756). -/
noncomputable def dg_fpV (α β R θ x : ℝ) : ℝ := dg_fpKappa α β * Real.log x + dg_fpNu α β R θ

/-- The right side of the Bellman equation, `ln c + β V((θ(Rx − c))^α)`. -/
noncomputable def dg_fpRHS (α β R θ x c : ℝ) : ℝ :=
  Real.log c + β * dg_fpV α β R θ (dg_fpNext α R θ x c)

/-- The Bellman right side in reduced form: `ln c + K ln(Rx − c) + K ln θ + βν`, `K = αβκ`. -/
theorem dg_fpRHS_eq {α β R θ x c : ℝ} (hθ : 0 < θ) (hc : c < R * x) :
    dg_fpRHS α β R θ x c = Real.log c + α * β * dg_fpKappa α β * Real.log (R * x - c) +
      α * β * dg_fpKappa α β * Real.log θ + β * dg_fpNu α β R θ := by
  have hp : 0 < θ * (R * x - c) := mul_pos hθ (by linarith)
  unfold dg_fpRHS dg_fpV dg_fpNext
  rw [Real.log_rpow hp, Real.log_mul hθ.ne' (by linarith)]
  ring

/-- `K = αβκ` satisfies `1 + K = κ`. -/
theorem dg_fpKappa_eq {α β : ℝ} (hab : α * β < 1) :
    1 + α * β * dg_fpKappa α β = dg_fpKappa α β := by
  unfold dg_fpKappa
  have : 1 - α * β ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, p. 757 ("substituting this rule back into the Bellman equation"): at the policy
`c = (1 − αβ)Rx` the Bellman equation `V(x) = ln c + βV(x')` holds with `κ = 1/(1 − αβ)`. -/
theorem dg_fp_bellman_eq {α β R θ x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) :
    dg_fpRHS α β R θ x ((1 - α * β) * R * x) = dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hab0 : 0 < α * β := mul_pos hα hβ
  rw [dg_fpRHS_eq hθ (by nlinarith [mul_pos hab0 (mul_pos hR hx)])]
  have e1 : R * x - (1 - α * β) * R * x = (α * β * R) * x := by ring
  rw [e1, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hx.ne']
  unfold dg_fpV dg_fpNu dg_fpKappa
  have hb : 1 - β ≠ 0 := by linarith
  field_simp
  ring

/-- The guess-and-verify step (Miao, pp. 756–757): `V(x) = κ ln x + ν` solves the Bellman
inequality `ln c + βV((θ(Rx − c))^α) ≤ V(x)` for every feasible catch `0 < c < Rx`. -/
theorem dg_fp_bellman {α β R θ x c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) (hc0 : 0 < c) (hc : c < R * x) :
    dg_fpRHS α β R θ x c ≤ dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hK : 0 < α * β * dg_fpKappa α β := by unfold dg_fpKappa; positivity
  have hstar : (R * x) / (1 + α * β * dg_fpKappa α β) = (1 - α * β) * R * x := by
    rw [dg_fpKappa_eq hab]; unfold dg_fpKappa; field_simp
  have hm := (dg_log_max (mul_pos hR hx) hK hc0 hc).1
  rw [hstar] at hm
  have hlt : (1 - α * β) * R * x < R * x := by
    nlinarith [mul_pos (mul_pos hα hβ) (mul_pos hR hx)]
  rw [← dg_fp_bellman_eq hα hβ hab hβ1 hR hθ hx, dg_fpRHS_eq hθ hc, dg_fpRHS_eq hθ hlt]
  linarith

/-- The maximiser of the Bellman equation is unique: any catch `c ≠ (1 − αβ)Rx` gives strictly
less (Miao, p. 757, "the first-order condition"). -/
theorem dg_fp_bellman_unique {α β R θ x c : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx : 0 < x) (hc0 : 0 < c) (hc : c < R * x)
    (hne : c ≠ (1 - α * β) * R * x) : dg_fpRHS α β R θ x c < dg_fpV α β R θ x := by
  have h1 : 0 < 1 - α * β := by linarith
  have hK : 0 < α * β * dg_fpKappa α β := by unfold dg_fpKappa; positivity
  have hstar : (R * x) / (1 + α * β * dg_fpKappa α β) = (1 - α * β) * R * x := by
    rw [dg_fpKappa_eq hab]; unfold dg_fpKappa; field_simp
  have hm := (dg_log_max (mul_pos hR hx) hK hc0 hc).2 (by rw [hstar]; exact hne)
  rw [hstar] at hm
  have hlt : (1 - α * β) * R * x < R * x := by
    nlinarith [mul_pos (mul_pos hα hβ) (mul_pos hR hx)]
  rw [← dg_fp_bellman_eq hα hβ hab hβ1 hR hθ hx, dg_fpRHS_eq hθ hc, dg_fpRHS_eq hθ hlt]
  linarith

/-- Miao, p. 756 ("substituting these decision rules back into the value functions, we can
solve `κ_i = 1/(1 − αβ_i)`"): if `κ ln x + ν = ln(kx) + β(κα ln(sx) + ν)` for all `x > 0`
(a linear catch `kx` leaving `sx`), then `κ = 1/(1 − αβ)`. -/
theorem dg_fp_kappa_forced {α β κ ν k s : ℝ} (hab : α * β < 1) (hk : 0 < k) (hs : 0 < s)
    (h : ∀ x : ℝ, 0 < x → κ * Real.log x + ν =
      Real.log (k * x) + β * (κ * α * Real.log (s * x) + ν)) :
    κ = 1 / (1 - α * β) := by
  have h1 := h 1 one_pos
  have he := h (Real.exp 1) (Real.exp_pos 1)
  rw [Real.log_mul hk.ne' (Real.exp_pos 1).ne', Real.log_mul hs.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at he
  rw [mul_one, mul_one, Real.log_one] at h1
  have hk1 : κ = 1 + α * β * κ := by linarith
  have : 1 - α * β ≠ 0 := by linarith
  field_simp
  linarith

/-- Telescoping the Bellman inequality along a feasible plan:
`∑_{t<T} βᵗ ln c_t + βᵀ V(x_T) ≤ V(x₀)`. -/
theorem dg_fp_telescope {α β R θ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (x c : ℕ → ℝ)
    (hfeas : ∀ t, 0 < c t ∧ c t < R * x t) (hlaw : ∀ t, x (t + 1) = dg_fpNext α R θ (x t) (c t))
    (T : ℕ) : ∑ t ∈ Finset.range T, β ^ t * Real.log (c t) + β ^ T * dg_fpV α β R θ (x T) ≤
      dg_fpV α β R θ (x 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hxT : 0 < x T := by
        have := (hfeas T).1.trans (hfeas T).2
        exact pos_of_mul_pos_right this hR.le
      have hb := dg_fp_bellman hα hβ hab hβ1 hR hθ hxT (hfeas T).1 (hfeas T).2
      unfold dg_fpRHS at hb
      rw [← hlaw T] at hb
      rw [Finset.sum_range_succ]
      have := mul_le_mul_of_nonneg_left hb (pow_nonneg hβ.le T)
      rw [pow_succ]
      nlinarith

/-- Optimality of the guess (Miao, p. 756): every feasible plan (`0 < c_t < Rx_t`,
`x_{t+1} = (θ(Rx_t − c_t))^α`) whose discounted utility series converges yields at most
`V(x₀)`. -/
theorem dg_fp_optimal {α β R θ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (x c : ℕ → ℝ)
    (hfeas : ∀ t, 0 < c t ∧ c t < R * x t) (hlaw : ∀ t, x (t + 1) = dg_fpNext α R θ (x t) (c t))
    (hsum : Summable fun t => β ^ t * Real.log (c t)) :
    ∑' t, β ^ t * Real.log (c t) ≤ dg_fpV α β R θ (x 0) := by
  have hκ : 0 < dg_fpKappa α β := by unfold dg_fpKappa; exact one_div_pos.mpr (by linarith)
  let e : ℕ → ℝ := fun T => dg_fpKappa α β * (β ^ T * Real.log (c T)) -
    dg_fpKappa α β * Real.log R * β ^ T + dg_fpNu α β R θ * β ^ T
  have hlow : ∀ T, e T ≤ β ^ T * dg_fpV α β R θ (x T) := by
    intro T
    have hxT : 0 < x T := pos_of_mul_pos_right ((hfeas T).1.trans (hfeas T).2) hR.le
    have hl : Real.log (c T) ≤ Real.log R + Real.log (x T) := by
      rw [← Real.log_mul hR.ne' hxT.ne']
      exact Real.log_le_log (hfeas T).1 (hfeas T).2.le
    have hbT := pow_nonneg hβ.le T
    simp only [e]
    unfold dg_fpV
    nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg hκ.le hbT)]
  have hβT := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
    have h1 := (hsum.tendsto_atTop_zero.const_mul (dg_fpKappa α β))
    have h2 := hβT.const_mul (dg_fpKappa α β * Real.log R)
    have h3 := hβT.const_mul (dg_fpNu α β R θ)
    have := (h1.sub h2).add h3
    simpa using this
  have hS := hsum.hasSum.tendsto_sum_nat
  have hR' : Filter.Tendsto (fun T => dg_fpV α β R θ (x 0) - e T) Filter.atTop
      (nhds (dg_fpV α β R θ (x 0) - 0)) := tendsto_const_nhds.sub he
  rw [sub_zero] at hR'
  refine le_of_tendsto_of_tendsto' hS hR' fun T => ?_
  have := dg_fp_telescope hα hβ hab hβ1 hR hθ x c hfeas hlaw T
  linarith [hlow T]

/-- The stock path under the policy `c = (1 − αβ)Rx`: `x_{t+1} = (θαβR x_t)^α`. -/
noncomputable def dg_fpPath (α β R θ x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => (θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α

/-- The stock stays positive along the policy path. -/
theorem dg_fpPath_pos {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hR : 0 < R) (hθ : 0 < θ)
    (hx₀ : 0 < x₀) (t : ℕ) : 0 < dg_fpPath α β R θ x₀ t := by
  induction t with
  | zero => exact hx₀
  | succ t ih => exact Real.rpow_pos_of_pos (by positivity) _

/-- Along the policy path `ln x_{t+1} = α(ln(θαβR) + ln x_t)`. -/
theorem dg_fpPath_log {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hR : 0 < R) (hθ : 0 < θ)
    (hx₀ : 0 < x₀) (t : ℕ) : Real.log (dg_fpPath α β R θ x₀ (t + 1)) =
      α * (Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)) := by
  have hp := dg_fpPath_pos hα hβ hR hθ hx₀ t
  change Real.log ((θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α) = _
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) hp.ne']

/-- The policy plan is feasible: `0 < (1 − αβ)Rx_t < Rx_t` and `x_{t+1}` follows the law. -/
theorem dg_fpPath_feasible {α β R θ x₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α * β < 1)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) (t : ℕ) :
    (0 < (1 - α * β) * R * dg_fpPath α β R θ x₀ t ∧
      (1 - α * β) * R * dg_fpPath α β R θ x₀ t < R * dg_fpPath α β R θ x₀ t) ∧
    dg_fpPath α β R θ x₀ (t + 1) =
      dg_fpNext α R θ (dg_fpPath α β R θ x₀ t) ((1 - α * β) * R * dg_fpPath α β R θ x₀ t) := by
  have hp := dg_fpPath_pos hα hβ hR hθ hx₀ t
  have h1 : 0 < 1 - α * β := by linarith
  have hab0 : 0 < α * β := mul_pos hα hβ
  refine ⟨⟨by positivity, ?_⟩, ?_⟩
  · have := mul_pos hR hp
    nlinarith
  · change (θ * α * β * R * dg_fpPath α β R θ x₀ t) ^ α = _
    unfold dg_fpNext
    congr 1
    ring

/-- `|ln x_t|` stays bounded along the policy path. -/
theorem dg_fpPath_log_bound {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) (t : ℕ) :
    |Real.log (dg_fpPath α β R θ x₀ t)| ≤
      |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α) := by
  have h1 : 0 < 1 - α := by linarith
  have hB : 0 ≤ |Real.log (θ * α * β * R)| / (1 - α) := div_nonneg (abs_nonneg _) h1.le
  induction t with
  | zero => change |Real.log x₀| ≤ _; linarith
  | succ t ih =>
      rw [dg_fpPath_log hα hβ hR hθ hx₀, abs_mul, abs_of_pos hα]
      have ht := abs_add_le (Real.log (θ * α * β * R)) (Real.log (dg_fpPath α β R θ x₀ t))
      have key : α * (|Real.log (θ * α * β * R)| + (|Real.log x₀| +
          |Real.log (θ * α * β * R)| / (1 - α))) ≤
          |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α) := by
        have hB1 : (1 - α) * (|Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α)) =
            (1 - α) * |Real.log x₀| + |Real.log (θ * α * β * R)| := by field_simp
        have hL := mul_le_of_le_one_left (abs_nonneg (Real.log (θ * α * β * R))) hα1.le
        have hx0 := mul_nonneg h1.le (abs_nonneg (Real.log x₀))
        nlinarith
      calc α * |Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)|
          ≤ α * (|Real.log (θ * α * β * R)| + (|Real.log x₀| +
              |Real.log (θ * α * β * R)| / (1 - α))) := by
            refine mul_le_mul_of_nonneg_left ?_ hα.le
            linarith
        _ ≤ _ := key

/-- The policy plan attains `V(x₀)` (Miao, p. 757): the utility series of
`c_t = (1 − αβ)Rx_t` converges and `∑ βᵗ ln c_t = V(x₀)`. -/
theorem dg_fp_policy_value {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hab : α * β < 1) (hβ1 : β < 1) (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) :
    HasSum (fun t => β ^ t * Real.log ((1 - α * β) * R * dg_fpPath α β R θ x₀ t))
      (dg_fpV α β R θ x₀) := by
  set x := dg_fpPath α β R θ x₀
  set B := |Real.log x₀| + |Real.log (θ * α * β * R)| / (1 - α)
  have h1 : 0 < 1 - α * β := by linarith
  have hlb := dg_fpPath_log_bound hα hα1 hβ hR hθ hx₀
  have hlc : ∀ t, |Real.log ((1 - α * β) * R * x t)| ≤ |Real.log ((1 - α * β) * R)| + B := by
    intro t
    rw [Real.log_mul (by positivity) (dg_fpPath_pos hα hβ hR hθ hx₀ t).ne']
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hlb t))
  have hsum : Summable fun t => β ^ t * Real.log ((1 - α * β) * R * x t) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right
        (|Real.log ((1 - α * β) * R)| + B)) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hlc t) (pow_nonneg hβ.le t)
  have htel : ∀ T, ∑ t ∈ Finset.range T, β ^ t * Real.log ((1 - α * β) * R * x t) =
      dg_fpV α β R θ x₀ - β ^ T * dg_fpV α β R θ (x T) := by
    intro T
    induction T with
    | zero => simp [x, dg_fpPath]
    | succ T ih =>
        rw [Finset.sum_range_succ, ih]
        have hf := dg_fpPath_feasible hα hβ hab hR hθ hx₀ T
        have hb := dg_fp_bellman_eq hα hβ hab hβ1 hR hθ (dg_fpPath_pos hα hβ hR hθ hx₀ T)
        unfold dg_fpRHS at hb
        rw [← hf.2] at hb
        rw [pow_succ]
        have : β ^ T * dg_fpV α β R θ (x T) = β ^ T * (Real.log ((1 - α * β) * R * x T) +
            β * dg_fpV α β R θ (x (T + 1))) := by rw [hb]
        linarith
  have hV : ∀ T, |dg_fpV α β R θ (x T)| ≤ dg_fpKappa α β * B + |dg_fpNu α β R θ| := by
    intro T
    have hκ : 0 < dg_fpKappa α β := by unfold dg_fpKappa; exact one_div_pos.mpr h1
    unfold dg_fpV
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_pos hκ]
    exact mul_le_mul_of_nonneg_left (hlb T) hκ.le
  have hz : Filter.Tendsto (fun T => β ^ T * dg_fpV α β R θ (x T)) Filter.atTop (nhds 0) := by
    have hβT := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
    refine squeeze_zero_norm (a := fun T => β ^ T * (dg_fpKappa α β * B + |dg_fpNu α β R θ|))
      (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ]
      exact mul_le_mul_of_nonneg_left (hV T) (pow_nonneg hβ.le T)
    · simpa using hβT.mul_const (dg_fpKappa α β * B + |dg_fpNu α β R θ|)
  have hlim : Filter.Tendsto (fun T => ∑ t ∈ Finset.range T,
      β ^ t * Real.log ((1 - α * β) * R * x t)) Filter.atTop (nhds (dg_fpV α β R θ x₀)) := by
    have := (tendsto_const_nhds (x := dg_fpV α β R θ x₀)).sub hz
    rw [sub_zero] at this
    exact this.congr fun T => (htel T).symm
  have := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hsum.hasSum

/-- Along the policy path the stock converges to `x̄ = (θαβR)^{α/(1−α)}` (Miao, p. 757, "in the
steady state"), from any `x₀ > 0`; explicitly `ln x_t − ln x̄ = αᵗ (ln x₀ − ln x̄)`. -/
theorem dg_fp_path_tendsto {α β R θ x₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hR : 0 < R) (hθ : 0 < θ) (hx₀ : 0 < x₀) :
    (∀ t, Real.log (dg_fpPath α β R θ x₀ t) - α / (1 - α) * Real.log (θ * α * β * R) =
      α ^ t * (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R))) ∧
    Filter.Tendsto (dg_fpPath α β R θ x₀) Filter.atTop
      (nhds ((θ * α * β * R) ^ (α / (1 - α)))) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hlog : ∀ t, Real.log (dg_fpPath α β R θ x₀ t) - α / (1 - α) * Real.log (θ * α * β * R) =
      α ^ t * (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R)) := by
    intro t
    induction t with
    | zero => simp [dg_fpPath]
    | succ t ih =>
        rw [dg_fpPath_log hα hβ hR hθ hx₀, pow_succ]
        have e : α * (Real.log (θ * α * β * R) + Real.log (dg_fpPath α β R θ x₀ t)) -
            α / (1 - α) * Real.log (θ * α * β * R) = α * (Real.log (dg_fpPath α β R θ x₀ t) -
            α / (1 - α) * Real.log (θ * α * β * R)) := by field_simp; ring
        rw [e, ih]
        ring
  refine ⟨hlog, ?_⟩
  have hαt := tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1
  have hL : Filter.Tendsto (fun t => Real.log (dg_fpPath α β R θ x₀ t)) Filter.atTop
      (nhds (α / (1 - α) * Real.log (θ * α * β * R))) := by
    have := (hαt.mul_const (Real.log x₀ - α / (1 - α) * Real.log (θ * α * β * R))).add_const
      (α / (1 - α) * Real.log (θ * α * β * R))
    rw [zero_mul, zero_add] at this
    refine this.congr fun t => ?_
    rw [← hlog t]
    ring
  have hE := (Real.continuous_exp.tendsto _).comp hL
  have hpos : 0 < θ * α * β * R := by positivity
  rw [Real.rpow_def_of_pos hpos, mul_comm]
  refine hE.congr fun t => ?_
  simp only [Function.comp_apply]
  exact Real.exp_log (dg_fpPath_pos hα hβ hR hθ hx₀ t)

end Miao.DynamicGames
