/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Continuous discounting and the continuous-time lifetime budget

AKMM, §9.2 (pp. 246–248: (9.16)–(9.18), the box "The discount rate ρ", the nPg (9.17)) and
Appendix 9.A.3, continuous part (pp. 845–846).

* (9.18): `β = 1/(1 + ρ)`; `β ∈ (0, 1) ⇔ ρ > 0`, and a larger `ρ` is a smaller `β`.
* The discount box: `(1/(1 + ρΔ))^{t/Δ} → e^{−ρt}` as `Δ → 0⁺` (`continuousBudget_discount_limit`);
  the same limit maps the nPg `a_{T+1}/(1 + r)^T` to `e^{−rT}a(T)`.
* Appendix 9.A.3, the integrating factor: with `R(t) = ∫_0^t r`, a solution of
  `ȧ = w + ra − c` satisfies `d/dt[e^{−R(t)}a(t)] = e^{−R(t)}(w(t) − c(t))` and
  `e^{−R(T)}a(T) = a(0) + ∫_0^T e^{−R(t)}(w(t) − c(t))dt` (`appendix_9A3_continuous_budget`);
  equivalently the book's intermediate form `a(T) − e^{R(T)}a(0) = ∫_0^T e^{∫_t^T r}(w − c)dt`
  (`appendix_9A3_continuous_budget_forward`).
* The book's final display, with the kernel `e^{∫_t^T r}` multiplying `e^{−R(T)}a(T)`, is false
  (`appendix_9A3_printed_budget_false`); the correct kernel is `e^{−∫_0^t r}`.
* As `T → ∞` the nPg `lim e^{−R(T)}a(T) ≥ 0` is equivalent to the lifetime budget constraint
  `∫_0^∞ e^{−R}c ≤ a(0) + ∫_0^∞ e^{−R}w`, with equality iff the limit is zero
  (`appendix_9A3_continuous_npg_iff_lbc`). The book says only "necessary".
* Constant `r`: `R(T) = rT`, the nPg (9.17) and the budget of (9.16) (`eq_9_17_budget`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.18), p. 247: with `β = 1/(1 + ρ)` and `ρ > −1`, `β ∈ (0, 1)` iff `ρ > 0`, and `β`
is strictly decreasing in `ρ`: a larger discount rate is a smaller discount factor. -/
theorem eq_9_18 {ρ : ℝ} (hρ : -1 < ρ) :
    (0 < 1 / (1 + ρ) ∧ 1 / (1 + ρ) < 1 ↔ 0 < ρ) ∧
      StrictAntiOn (fun x : ℝ => 1 / (1 + x)) (Set.Ioi (-1)) := by
  have hpos : 0 < 1 + ρ := by linarith
  refine ⟨⟨fun h => ?_, fun h => ⟨by positivity, ?_⟩⟩, ?_⟩
  · have := h.2
    rw [div_lt_one hpos] at this
    linarith
  · rw [div_lt_one hpos]
    linarith
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- AKMM, box "The discount rate ρ", p. 247: splitting a period into subperiods of length `Δ`
and discounting each by `ρΔ`, the discount factor `f(Δ, t) = (1/(1 + ρΔ))^{t/Δ}` tends to
`e^{−ρt}` as `Δ → 0⁺`. -/
theorem continuousBudget_discount_limit (ρ t : ℝ) :
    Tendsto (fun Δ : ℝ => (1 / (1 + ρ * Δ)) ^ (t / Δ)) (𝓝[>] 0) (𝓝 (Real.exp (-ρ * t))) := by
  have hlim : Tendsto (fun Δ : ℝ => Δ⁻¹ * Real.log (1 + ρ / Δ⁻¹)) (𝓝[>] 0) (𝓝 ρ) :=
    (Real.tendsto_mul_log_one_add_div_atTop ρ).comp tendsto_inv_nhdsGT_zero
  have hexp : Tendsto (fun Δ : ℝ => Real.exp (-(t * (Δ⁻¹ * Real.log (1 + ρ / Δ⁻¹)))))
      (𝓝[>] 0) (𝓝 (Real.exp (-ρ * t))) := by
    have := ((hlim.const_mul t).neg).rexp
    rwa [show -(t * ρ) = -ρ * t by ring] at this
  refine hexp.congr' ?_
  have hsmall : ∀ᶠ Δ : ℝ in 𝓝[>] 0, 0 < 1 + ρ * Δ := by
    have h : Tendsto (fun Δ : ℝ => 1 + ρ * Δ) (𝓝[>] 0) (𝓝 (1 + ρ * 0)) :=
      (tendsto_const_nhds.add (tendsto_id.const_mul ρ)).mono_left nhdsWithin_le_nhds
    rw [mul_zero, add_zero] at h
    exact h.eventually (lt_mem_nhds one_pos)
  filter_upwards [hsmall, self_mem_nhdsWithin] with Δ h1 hΔ
  have hΔ' : (0 : ℝ) < Δ := hΔ
  rw [Real.rpow_def_of_pos (by positivity), one_div, Real.log_inv, div_inv_eq_mul]
  congr 1
  field_simp

/-- AKMM, p. 248, nPg (9.17): the same limit maps the discrete discount factor of the nPg,
`(1 + rΔ)^{−T/Δ}`, to the continuous one `e^{−rT}`. -/
theorem continuousBudget_npg_discount_limit (r T : ℝ) :
    Tendsto (fun Δ : ℝ => (1 / (1 + r * Δ)) ^ (T / Δ)) (𝓝[>] 0) (𝓝 (Real.exp (-r * T))) :=
  continuousBudget_discount_limit r T

/-- The cumulative interest `R(t) = ∫_0^t r(s) ds` has derivative `r(t)` for continuous `r`. -/
theorem continuousBudget_hasDerivAt_cumulative {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, r s) (r t) t :=
  (hr.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- AKMM, Appendix 9.A.3, p. 845: the integrating factor. If `ȧ = w + ra − c`, then
`d/dt[e^{−R(t)}a(t)] = e^{−R(t)}(w(t) − c(t))`, `R(t) = ∫_0^t r`. -/
theorem appendix_9A3_integrating_factor {r w c a : ℝ → ℝ} (hr : Continuous r) {t : ℝ}
    (ha : HasDerivAt a (w t + r t * a t - c t) t) :
    HasDerivAt (fun x => Real.exp (-∫ s in (0 : ℝ)..x, r s) * a x)
      (Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t)) t := by
  have hR := (continuousBudget_hasDerivAt_cumulative hr t).neg.exp
  convert hR.mul ha using 1
  simp only [Pi.neg_apply]
  ring

/-- AKMM, Appendix 9.A.3, pp. 845–846: the continuous-time lifetime budget. For continuous
`r, w, c` and `ȧ = w + ra − c` on `[0, ∞)`,
`e^{−R(T)}a(T) = a(0) + ∫_0^T e^{−R(t)}(w(t) − c(t))dt`, `R(t) = ∫_0^t r`. -/
theorem appendix_9A3_continuous_budget {r w c a : ℝ → ℝ} (hr : Continuous r)
    (hw : Continuous w) (hc : Continuous c)
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w t + r t * a t - c t) t) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-∫ s in (0 : ℝ)..T, r s) * a T =
      a 0 + ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t) := by
  have hcont : Continuous fun t => Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t) := by
    have : Continuous fun t => ∫ s in (0 : ℝ)..t, r s :=
      continuous_iff_continuousAt.mpr fun t =>
        (continuousBudget_hasDerivAt_cumulative hr t).continuousAt
    exact (this.neg.rexp).mul (hw.sub hc)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.exp (-∫ s in (0 : ℝ)..x, r s) * a x)
    (fun x hx => appendix_9A3_integrating_factor hr (ha x (by
      rw [Set.uIcc_of_le hT] at hx; exact hx.1)))
    (hcont.intervalIntegrable 0 T)
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at h
  linarith

/-- AKMM, Appendix 9.A.3, p. 845, the book's intermediate form:
`a(T) − e^{R(T)}a(0) = ∫_0^T e^{∫_t^T r(s)ds}(w(t) − c(t))dt`. -/
theorem appendix_9A3_continuous_budget_forward {r w c a : ℝ → ℝ} (hr : Continuous r)
    (hw : Continuous w) (hc : Continuous c)
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w t + r t * a t - c t) t) {T : ℝ} (hT : 0 ≤ T) :
    a T - Real.exp (∫ s in (0 : ℝ)..T, r s) * a 0 =
      ∫ t in (0 : ℝ)..T, Real.exp (∫ s in t..T, r s) * (w t - c t) := by
  have h := appendix_9A3_continuous_budget hr hw hc ha hT
  have hk : ∀ t, Real.exp (∫ s in t..T, r s) =
      Real.exp (∫ s in (0 : ℝ)..T, r s) * Real.exp (-∫ s in (0 : ℝ)..t, r s) := by
    intro t
    rw [← Real.exp_add, ← intervalIntegral.integral_interval_sub_left
      (hr.intervalIntegrable 0 T) (hr.intervalIntegrable 0 t)]
    ring_nf
  have hi : ∫ t in (0 : ℝ)..T, Real.exp (∫ s in t..T, r s) * (w t - c t) =
      ∫ t in (0 : ℝ)..T, Real.exp (∫ s in (0 : ℝ)..T, r s) *
        (Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t)) :=
    intervalIntegral.integral_congr fun t _ => by
      rw [hk t, mul_assoc]
  have hI : ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t) =
      Real.exp (-∫ s in (0 : ℝ)..T, r s) * a T - a 0 := by linarith
  rw [hi, intervalIntegral.integral_const_mul, hI, mul_sub, ← mul_assoc, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero, one_mul]

/-- AKMM, Appendix 9.A.3, p. 846: the book's final display
`e^{−∫_0^T r}a(T) = ∫_0^T e^{∫_t^T r}w dt + a(0) − ∫_0^T e^{∫_t^T r}c dt` is false. With
`r ≡ 1`, `w ≡ 1`, `c ≡ 0`, `a(t) = e^t − 1` (which solves `ȧ = w + ra − c`, `a(0) = 0`) and
`T = 1`, the left side is `1 − e^{−1}` and the right side `e − 1`. -/
theorem appendix_9A3_printed_budget_false :
    (∀ t : ℝ, HasDerivAt (fun x => Real.exp x - 1) (1 + 1 * (Real.exp t - 1) - 0) t) ∧
      Real.exp (-∫ _ in (0 : ℝ)..1, (1 : ℝ)) * (Real.exp 1 - 1) = 1 - Real.exp (-1) ∧
      (∫ t in (0 : ℝ)..1, Real.exp (∫ _ in t..1, (1 : ℝ)) * 1) + (Real.exp 0 - 1) -
        (∫ t in (0 : ℝ)..1, Real.exp (∫ _ in t..1, (1 : ℝ)) * 0) = Real.exp 1 - 1 ∧
      1 - Real.exp (-1) ≠ Real.exp 1 - 1 := by
  refine ⟨fun t => ?_, ?_, ?_, ?_⟩
  · convert (Real.hasDerivAt_exp t).sub_const 1 using 1
    ring
  · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    rw [mul_sub, mul_one, ← Real.exp_add]
    norm_num
  · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_zero,
      intervalIntegral.integral_zero, Real.exp_zero, sub_self, add_zero, sub_zero]
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x => -Real.exp (1 - x)) (Real.exp (1 - x)) x := by
      intro x _
      have h := ((hasDerivAt_id x).const_sub 1).exp.neg
      convert h using 1
      · funext y
        simp
      · simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (1 - x)).intervalIntegrable 0 1)]
    norm_num
    ring
  · have h1 : Real.exp (-1) < 1 := by
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    have h2 : 2 < Real.exp 1 := by
      have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
      linarith
    intro h
    linarith [Real.exp_pos (-1)]

/-- AKMM, Appendix 9.A.3, p. 846, as `T → ∞`: if the discounted wage and consumption integrals
converge, `e^{−R(T)}a(T)` converges to `a(0) + ∫_0^∞ e^{−R}w − ∫_0^∞ e^{−R}c`; so the nPg
`lim e^{−R(T)}a(T) ≥ 0` is equivalent to the lifetime budget constraint
`∫_0^∞ e^{−R}c ≤ a(0) + ∫_0^∞ e^{−R}w`, with equality iff the limit is zero. -/
theorem appendix_9A3_continuous_npg_iff_lbc {r w c a : ℝ → ℝ} (hr : Continuous r)
    (hw : Continuous w) (hc : Continuous c)
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w t + r t * a t - c t) t) {Iw Ic : ℝ}
    (hIw : Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * w t)
      atTop (𝓝 Iw))
    (hIc : Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * c t)
      atTop (𝓝 Ic)) :
    Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * a T) atTop (𝓝 (a 0 + Iw - Ic)) ∧
      (0 ≤ a 0 + Iw - Ic ↔ Ic ≤ a 0 + Iw) ∧ (a 0 + Iw - Ic = 0 ↔ Ic = a 0 + Iw) := by
  refine ⟨?_, by constructor <;> intro h <;> linarith, by constructor <;> intro h <;> linarith⟩
  have hR : Continuous fun t => Real.exp (-∫ s in (0 : ℝ)..t, r s) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (continuousBudget_hasDerivAt_cumulative hr t).continuousAt).neg.rexp
  have h := (hIw.const_add (a 0)).sub hIc
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [appendix_9A3_continuous_budget hr hw hc ha hT]
  have hs : ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * (w t - c t) =
      (∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * w t) -
        ∫ t in (0 : ℝ)..T, Real.exp (-∫ s in (0 : ℝ)..t, r s) * c t := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub ((hR.mul hw).intervalIntegrable 0 T)
      ((hR.mul hc).intervalIntegrable 0 T)
  rw [hs]
  ring

/-- AKMM, (9.16)–(9.17), pp. 247–248: with a constant interest rate, `R(T) = rT`, so the nPg
(9.17) is `lim e^{−rT}a(T) ≥ 0`, and the budget `ȧ = w + ra − c` gives
`e^{−rT}a(T) = a(0) + ∫_0^T e^{−rt}(w − c(t))dt`. -/
theorem eq_9_17_budget {r w : ℝ} {c a : ℝ → ℝ} (hc : Continuous c)
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w + r * a t - c t) t) {T : ℝ} (hT : 0 ≤ T) :
    (∫ _ in (0 : ℝ)..T, r) = r * T ∧
      Real.exp (-r * T) * a T = a 0 + ∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (w - c t) := by
  have hR : ∀ x : ℝ, (∫ _ in (0 : ℝ)..x, r) = r * x := fun x => by simp [mul_comm]
  refine ⟨hR T, ?_⟩
  have h := appendix_9A3_continuous_budget (r := fun _ => r) (w := fun _ => w) continuous_const
    continuous_const hc ha hT
  simp only [hR, neg_mul] at h ⊢
  exact h

end AKMM.ContinuousTime
