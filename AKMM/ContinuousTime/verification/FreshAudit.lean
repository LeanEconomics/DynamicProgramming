import ContinuousTime.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import EulerTransversality.Sufficiency
import RamseyCassKoopmans.Concavity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Solow1956.Growth.GeneralSolowApplications
import RamseyCassKoopmans.Stationary
import RamseyCassKoopmans.CassGeneral
import RamseyCassKoopmans.CassPolicy
import RamseyCassKoopmans.CassRate
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Growth rates in continuous time

AKMM, §9.1 (pp. 242–243) and Appendices 9.A.1–9.A.2 (pp. 843–844).

* (9.1)–(9.2): `X_t = (1 + γ)^t X_0` solves the difference equation, and is its only solution.
* (9.3)–(9.4): `X(t) = e^{γt}X(0)` solves `Ẋ/X = γ`, and is its only solution on `[0, ∞)`; the
  uniqueness is Sargent–Stachurski's Example 10.1.1 (`eq_exp_of_hasDerivAt`, imported).
* (9.5): `Ẋ/X = d log X/dt`, the growth-accounting equation for `Y = zK^αL^{1−α}`, and the log
  of an exponential path is linear.
* Footnote 1: `log X_{t+1} − log X_t = log(1 + γ)`, and `log(1 + x) ≈ x` made precise by
  `x/(1 + x) ≤ log(1 + x) ≤ x` and `|log(1 + x) − x| ≤ x²/(1 − |x|)`.
* Appendices 9.A.1–9.A.2: the log/exp identities and the chain-rule examples. The second example
  of 9.A.2 prints `d/dt X(t)` on the left where `d/dt Z(t) = d/dt log X(t)` is meant
  (`appendix_9A2_log`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.1)–(9.2), p. 242: `X_t = (1 + γ)^t X_0` satisfies `(X_{t+1} − X_t)/X_t = γ`. -/
theorem eq_9_2 {γ X₀ : ℝ} (hX₀ : X₀ ≠ 0) (hγ : 1 + γ ≠ 0) (t : ℕ) :
    ((1 + γ) ^ (t + 1) * X₀ - (1 + γ) ^ t * X₀) / ((1 + γ) ^ t * X₀) = γ := by
  have h : (1 + γ) ^ t * X₀ ≠ 0 := mul_ne_zero (pow_ne_zero _ hγ) hX₀
  rw [div_eq_iff h]
  ring

/-- AKMM, (9.1)–(9.2), p. 242: every nonvanishing solution of (9.1) is `X_t = (1 + γ)^t X_0`. -/
theorem growthRates_discrete_unique {γ : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t ≠ 0)
    (h : ∀ t, (X (t + 1) - X t) / X t = γ) (t : ℕ) : X t = (1 + γ) ^ t * X 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    have h1 := h n
    rw [div_eq_iff (hX n)] at h1
    rw [pow_succ, show X (n + 1) = (1 + γ) * X n by linarith, ih]
    ring

/-- AKMM, (9.4), p. 242: `X(t) = e^{γt}X(0)` has derivative `γX(t)`, so it solves (9.3):
`Ẋ(t)/X(t) = γ` whenever `X(0) ≠ 0`. -/
theorem eq_9_4 (γ X₀ t : ℝ) (hX₀ : X₀ ≠ 0) :
    HasDerivAt (fun s => Real.exp (γ * s) * X₀) (γ * (Real.exp (γ * t) * X₀)) t ∧
      γ * (Real.exp (γ * t) * X₀) / (Real.exp (γ * t) * X₀) = γ := by
  refine ⟨SargentStachurski.ContinuousTime.hasDerivAt_exp_mul γ X₀ t, ?_⟩
  have h : Real.exp (γ * t) * X₀ ≠ 0 := mul_ne_zero (Real.exp_pos _).ne' hX₀
  field_simp

/-- AKMM, (9.3)–(9.4), p. 242: a solution of (9.3), `Ẋ = γX` on `[0, ∞)`, is `X(t) = e^{γt}X(0)`.
The uniqueness is Sargent–Stachurski's Example 10.1.1, imported. -/
theorem eq_9_4_unique {γ : ℝ} {X : ℝ → ℝ} (hX : ∀ t, 0 ≤ t → HasDerivAt X (γ * X t) t)
    {t : ℝ} (ht : 0 ≤ t) : X t = Real.exp (γ * t) * X 0 :=
  SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt rfl hX ht

/-- AKMM, (9.3), p. 242, in the book's quotient form: if `X ≠ 0` and `Ẋ(t)/X(t) = γ` for every
`t ≥ 0`, then `X(t) = e^{γt}X(0)`. -/
theorem eq_9_3_unique {γ : ℝ} {X X' : ℝ → ℝ} (hX0 : ∀ t, 0 ≤ t → X t ≠ 0)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (X' t) t) (hγ : ∀ t, 0 ≤ t → X' t / X t = γ)
    {t : ℝ} (ht : 0 ≤ t) : X t = Real.exp (γ * t) * X 0 := by
  refine eq_9_4_unique (fun s hs => ?_) ht
  have h := hγ s hs
  rw [div_eq_iff (hX0 s hs)] at h
  rw [← h]
  exact hd s hs

/-- AKMM, (9.5), p. 243: the growth rate is the derivative of the log, `Ẋ/X = d log X/dt`. -/
theorem eq_9_5 {X : ℝ → ℝ} {X' t : ℝ} (hX : HasDerivAt X X' t) (hpos : X t ≠ 0) :
    HasDerivAt (fun s => Real.log (X s)) (X' / X t) t :=
  hX.log hpos

/-- AKMM, p. 243: the log of an exponential path is linear, `log X(t) = γt + log X(0)`, and
its derivative is the constant growth rate `γ`. -/
theorem growthRates_log_exponential {γ X₀ : ℝ} (hX₀ : 0 < X₀) (t : ℝ) :
    Real.log (Real.exp (γ * t) * X₀) = γ * t + Real.log X₀ ∧
      HasDerivAt (fun s => Real.log (Real.exp (γ * s) * X₀)) γ t := by
  have hlin : (fun s => Real.log (Real.exp (γ * s) * X₀)) = fun s => γ * s + Real.log X₀ := by
    funext s
    rw [Real.log_mul (Real.exp_pos _).ne' hX₀.ne', Real.log_exp]
  refine ⟨congrFun hlin t, ?_⟩
  rw [hlin]
  simpa using ((hasDerivAt_id t).const_mul γ).add_const (Real.log X₀)

/-- AKMM, p. 243: growth accounting. If `Y(t) = z(t)K(t)^αL(t)^{1−α}` with positive factors,
then `log Y = log z + α log K + (1 − α) log L` and
`Ẏ/Y = ż/z + α K̇/K + (1 − α) L̇/L`. -/
theorem growthRates_growth_accounting {z K L : ℝ → ℝ} {z' K' L' α t : ℝ}
    (hz : HasDerivAt z z' t) (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t)
    (hz0 : 0 < z t) (hK0 : 0 < K t) (hL0 : 0 < L t) :
    Real.log (z t * K t ^ α * L t ^ (1 - α)) =
        Real.log (z t) + α * Real.log (K t) + (1 - α) * Real.log (L t) ∧
      HasDerivAt (fun s => z s * K s ^ α * L s ^ (1 - α))
        ((z t * K t ^ α * L t ^ (1 - α)) * (z' / z t + α * (K' / K t) + (1 - α) * (L' / L t)))
        t := by
  have hlog : ∀ s, 0 < z s → 0 < K s → 0 < L s →
      Real.log (z s * K s ^ α * L s ^ (1 - α)) =
        Real.log (z s) + α * Real.log (K s) + (1 - α) * Real.log (L s) := by
    intro s h1 h2 h3
    rw [Real.log_mul (mul_pos h1 (Real.rpow_pos_of_pos h2 _)).ne'
      (Real.rpow_pos_of_pos h3 _).ne', Real.log_mul h1.ne' (Real.rpow_pos_of_pos h2 _).ne',
      Real.log_rpow h2, Real.log_rpow h3]
  refine ⟨hlog t hz0 hK0 hL0, ?_⟩
  set g : ℝ → ℝ := fun s => Real.log (z s) + α * Real.log (K s) + (1 - α) * Real.log (L s)
  have hg : HasDerivAt g (z' / z t + α * (K' / K t) + (1 - α) * (L' / L t)) t :=
    ((hz.log hz0.ne').add ((hK.log hK0.ne').const_mul α)).add
      ((hL.log hL0.ne').const_mul (1 - α))
  have hev : (fun s => Real.exp (g s)) =ᶠ[𝓝 t] fun s => z s * K s ^ α * L s ^ (1 - α) := by
    filter_upwards [hz.continuousAt.eventually (lt_mem_nhds hz0),
      hK.continuousAt.eventually (lt_mem_nhds hK0),
      hL.continuousAt.eventually (lt_mem_nhds hL0)] with s h1 h2 h3
    simp only [g]
    rw [← hlog s h1 h2 h3, Real.exp_log]
    exact mul_pos (mul_pos h1 (Real.rpow_pos_of_pos h2 _)) (Real.rpow_pos_of_pos h3 _)
  have hY : Real.exp (g t) = z t * K t ^ α * L t ^ (1 - α) := hev.eq_of_nhds
  have h := hg.exp.congr_of_eventuallyEq hev.symm
  rwa [hY] at h

/-- AKMM, p. 243: the growth-accounting equation in the book's form
`Ẏ/Y = ż/z + α K̇/K + (1 − α) L̇/L`, from (9.5) applied to `log Y`. -/
theorem growthRates_growth_accounting_rate {z K L : ℝ → ℝ} {z' K' L' α t : ℝ}
    (hz : HasDerivAt z z' t) (hK : HasDerivAt K K' t) (hL : HasDerivAt L L' t)
    (hz0 : 0 < z t) (hK0 : 0 < K t) (hL0 : 0 < L t) :
    HasDerivAt (fun s => Real.log (z s * K s ^ α * L s ^ (1 - α)))
      (z' / z t + α * (K' / K t) + (1 - α) * (L' / L t)) t := by
  have h := (growthRates_growth_accounting (α := α) hz hK hL hz0 hK0 hL0).2
  have hY : 0 < z t * K t ^ α * L t ^ (1 - α) :=
    mul_pos (mul_pos hz0 (Real.rpow_pos_of_pos hK0 _)) (Real.rpow_pos_of_pos hL0 _)
  have h2 := eq_9_5 h hY.ne'
  rwa [mul_div_cancel_left₀ _ hY.ne'] at h2

/-- AKMM, footnote 1, p. 243: on `X_t = (1 + γ)^t X_0`, the log difference is
`log X_{t+1} − log X_t = log(1 + γ)`. -/
theorem growthRates_log_difference {γ X₀ : ℝ} (hγ : 0 < 1 + γ) (hX₀ : 0 < X₀) (t : ℕ) :
    Real.log ((1 + γ) ^ (t + 1) * X₀) - Real.log ((1 + γ) ^ t * X₀) = Real.log (1 + γ) := by
  rw [Real.log_mul (pow_pos hγ _).ne' hX₀.ne', Real.log_mul (pow_pos hγ _).ne' hX₀.ne',
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- AKMM, footnote 1, p. 243: `log(1 + x) ≈ x` for small `x`, made precise: for `x > −1`,
`x/(1 + x) ≤ log(1 + x) ≤ x`, and for `|x| < 1`, `|log(1 + x) − x| ≤ x²/(1 − |x|)`. -/
theorem growthRates_log_one_add_approx {x : ℝ} (hx : -1 < x) :
    x / (1 + x) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x ∧
      (|x| < 1 → |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - |x|)) := by
  have hpos : 0 < 1 + x := by linarith
  refine ⟨?_, ?_, fun h1 => ?_⟩
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have he : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  · linarith [Real.log_le_sub_one_of_pos hpos]
  · have h1' : |-x| < 1 := by rwa [abs_neg]
    have h := Real.abs_log_sub_add_sum_range_le h1' 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_one, zero_add, Nat.cast_zero,
      div_one, abs_neg] at h
    have he : Real.log (1 + x) - x = -x + Real.log (1 - -x) := by ring_nf
    rw [he, ← sq_abs]
    convert h using 2

/-- AKMM, Appendix 9.A.1, p. 843: `e^{log x} = x` (`x > 0`), `log e^x = x`,
`log(xy) = log x + log y`, `log x^α = α log x` (`x, y > 0`), `d log x/dx = 1/x` and
`d e^x/dx = e^x`. -/
theorem appendix_9A1 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (α : ℝ) :
    Real.exp (Real.log x) = x ∧ Real.log (Real.exp x) = x ∧
      Real.log (x * y) = Real.log x + Real.log y ∧ Real.log (x ^ α) = α * Real.log x ∧
      HasDerivAt Real.log (1 / x) x ∧ HasDerivAt Real.exp (Real.exp x) x :=
  ⟨Real.exp_log hx, Real.log_exp x, Real.log_mul hx.ne' hy.ne', Real.log_rpow hx α,
    by simpa [one_div] using Real.hasDerivAt_log hx.ne', Real.hasDerivAt_exp x⟩

/-- AKMM, Appendix 9.A.2, p. 843: the chain rule `dz/dx = g'(f(x))f'(x)`, and its first example
`d e^{γt}/dt = γe^{γt}`. -/
theorem appendix_9A2_exp {f g : ℝ → ℝ} {f' g' x : ℝ} (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' (f x)) (γ t : ℝ) :
    HasDerivAt (fun s => g (f s)) (g' * f') x ∧
      HasDerivAt (fun s => Real.exp (γ * s)) (γ * Real.exp (γ * t)) t := by
  refine ⟨hg.comp x hf, ?_⟩
  have h := ((hasDerivAt_id t).const_mul γ).exp
  simp only [id, mul_one] at h
  rwa [mul_comm] at h

/-- AKMM, Appendix 9.A.2, p. 844, second example (corrected): for `Z(t) = log X(t)`,
`dZ/dt = Ẋ/X`. The book prints `d/dt X(t)` on the left. -/
theorem appendix_9A2_log {X : ℝ → ℝ} {X' t : ℝ} (hX : HasDerivAt X X' t) (hpos : 0 < X t) :
    HasDerivAt (fun s => Real.log (X s)) (1 / X t * X') t := by
  have h := eq_9_5 hX hpos.ne'
  rwa [div_eq_inv_mul, ← one_div] at h

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The discrete-time lifetime budget and the no-Ponzi-game condition

AKMM, §9.2 (pp. 245–246, (9.15)) and Appendix 9.A.3, discrete part (p. 844).

With `a_{t+1} = w_t + (1 + r_t)a_t − c_t` and the discount factor `D_s = ∏_{t=1}^s (1 + r_t)`:

* the telescoped lifetime budget
  `a_{T+1}/D_T = Σ_{s≤T} w_s/D_s + (1 + r_0)a_0 − Σ_{s≤T} c_s/D_s`
  (`appendix_9A3_discrete_budget`);
* the no-Ponzi-game condition `a_{T+1}/D_T ≥ 0` gives the lifetime budget constraint, finite
  and infinite horizon, and in the limit the two are equivalent (`appendix_9A3_discrete_lbc`,
  `appendix_9A3_discrete_lbc_infinite`, `appendix_9A3_discrete_npg_iff_lbc`);
* with a constant rate `D_s = (1 + r)^s` (`discreteBudget_const_discount`);
* p. 246: in the finite horizon `a_{T+1}/(1 + r)^T ≥ 0 ⇔ a_{T+1} ≥ 0`, but in the infinite
  horizon `lim a_{T+1}/(1 + r)^T ≥ 0` does not imply `lim a_{T+1} ≥ 0`. The book's example
  `a_t = a > 0` satisfies both conditions; the counterexample is `a_t = a < 0` with `r > 0`,
  debt rolled over forever (`discreteBudget_npg_printed_example`,
  `discreteBudget_npg_counterexample`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, Appendix 9.A.3, p. 844: the discount factor `D_s = ∏_{t=1}^s (1 + r_t)`. -/
noncomputable def discreteDiscount (r : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∏ i ∈ Finset.range s, (1 + r (i + 1))

/-- The discount factor is positive when every gross rate is positive. -/
theorem discreteBudget_discount_pos {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (s : ℕ) :
    0 < discreteDiscount r s :=
  Finset.prod_pos fun i _ => hr (i + 1)

/-- AKMM, Appendix 9.A.3, p. 844: with a constant rate, `D_s = (1 + r)^s`. -/
theorem discreteBudget_const_discount (r : ℝ) (s : ℕ) :
    discreteDiscount (fun _ => r) s = (1 + r) ^ s := by
  simp [discreteDiscount]

/-- AKMM, Appendix 9.A.3, p. 844: dividing `a_{t+1} = w_t + (1 + r_t)a_t − c_t` by `D_t` and
summing from `0` to `T` gives
`a_{T+1}/D_T = Σ_{s≤T} w_s/D_s + (1 + r_0)a_0 − Σ_{s≤T} c_s/D_s`. -/
theorem appendix_9A3_discrete_budget {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t) (T : ℕ) :
    a (T + 1) / discreteDiscount r T =
      ∑ s ∈ Finset.range (T + 1), w s / discreteDiscount r s + (1 + r 0) * a 0 -
        ∑ s ∈ Finset.range (T + 1), c s / discreteDiscount r s := by
  induction T with
  | zero => simp [discreteDiscount, hb 0]
  | succ T ih =>
    have hD := discreteBudget_discount_pos hr T
    have hsucc : discreteDiscount r (T + 1) = discreteDiscount r T * (1 + r (T + 1)) :=
      Finset.prod_range_succ _ _
    rw [Finset.sum_range_succ (fun s => w s / discreteDiscount r s) (T + 1),
      Finset.sum_range_succ (fun s => c s / discreteDiscount r s) (T + 1), hsucc, hb (T + 1)]
    have h1 := hr (T + 1)
    have key : (w (T + 1) + (1 + r (T + 1)) * a (T + 1) - c (T + 1)) /
        (discreteDiscount r T * (1 + r (T + 1))) =
        a (T + 1) / discreteDiscount r T + w (T + 1) / (discreteDiscount r T * (1 + r (T + 1)))
          - c (T + 1) / (discreteDiscount r T * (1 + r (T + 1))) := by
      field_simp
      ring
    rw [key, ih]
    ring

/-- AKMM, Appendix 9.A.3, p. 844: the finite-horizon no-Ponzi condition `a_{T+1}/D_T ≥ 0`
guarantees the lifetime budget constraint
`Σ_{s≤T} c_s/D_s ≤ Σ_{s≤T} w_s/D_s + (1 + r_0)a_0`, and conversely. -/
theorem appendix_9A3_discrete_lbc {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t) (T : ℕ) :
    0 ≤ a (T + 1) / discreteDiscount r T ↔
      ∑ s ∈ Finset.range (T + 1), c s / discreteDiscount r s ≤
        ∑ s ∈ Finset.range (T + 1), w s / discreteDiscount r s + (1 + r 0) * a 0 := by
  rw [appendix_9A3_discrete_budget hr hb T]
  constructor <;> intro h <;> linarith

/-- AKMM, Appendix 9.A.3, p. 844, the limit `T → ∞`: if the discounted wage and consumption
series converge, the discounted terminal asset converges to
`Σ w_s/D_s + (1 + r_0)a_0 − Σ c_s/D_s`. -/
theorem appendix_9A3_discrete_limit {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) :
    Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop
      (𝓝 (∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0 -
        ∑' s, c s / discreteDiscount r s)) := by
  have hW := (hw.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hC := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h := (hW.add_const ((1 + r 0) * a 0)).sub hC
  refine h.congr fun T => ?_
  simp only [Function.comp]
  rw [appendix_9A3_discrete_budget hr hb T]

/-- AKMM, Appendix 9.A.3, p. 844: the infinite-horizon no-Ponzi condition
`lim a_{T+1}/D_T ≥ 0` guarantees the lifetime budget constraint
`Σ c_s/D_s ≤ Σ w_s/D_s + (1 + r_0)a_0`. -/
theorem appendix_9A3_discrete_lbc_infinite {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) {L : ℝ}
    (hL : Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop (𝓝 L)) (hnpg : 0 ≤ L) :
    ∑' s, c s / discreteDiscount r s ≤ ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0 := by
  have h := tendsto_nhds_unique hL (appendix_9A3_discrete_limit hr hb hw hc)
  linarith

/-- AKMM, Appendix 9.A.3, p. 844: in the limit the no-Ponzi condition and the lifetime budget
constraint are equivalent, and the lifetime budget holds with equality iff the discounted
terminal asset tends to zero. -/
theorem appendix_9A3_discrete_npg_iff_lbc {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) :
    ∃ L, Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop (𝓝 L) ∧
      (0 ≤ L ↔ ∑' s, c s / discreteDiscount r s ≤
        ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0) ∧
      (L = 0 ↔ ∑' s, c s / discreteDiscount r s =
        ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0) := by
  refine ⟨_, appendix_9A3_discrete_limit hr hb hw hc, ?_, ?_⟩ <;>
    constructor <;> intro h <;> linarith

/-- AKMM, p. 246: in the finite horizon `a_{T+1}/(1 + r)^T ≥ 0` is equivalent to `a_{T+1} ≥ 0`,
because `(1 + r)^T > 0`. -/
theorem discreteBudget_finite_npg_iff {r x : ℝ} (hr : 0 < 1 + r) (T : ℕ) :
    0 ≤ x / (1 + r) ^ T ↔ 0 ≤ x :=
  div_nonneg_iff.trans ⟨fun h => h.elim (fun h => h.1) fun h => absurd h.2
    (not_le.mpr (pow_pos hr T)), fun h => Or.inl ⟨h, (pow_pos hr T).le⟩⟩

/-- AKMM, p. 246, the printed example: a constant positive asset `a_t = a > 0` satisfies both
`lim a_{T+1}/(1 + r)^T ≥ 0` and `lim a_{T+1} ≥ 0` (for `r > 0`), so it does not separate them,
contrary to the text. -/
theorem discreteBudget_npg_printed_example {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Tendsto (fun T : ℕ => a / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a) ∧ 0 ≤ (0 : ℝ) ∧ 0 ≤ a := by
  refine ⟨?_, tendsto_const_nhds, le_rfl, ha.le⟩
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a
  simpa [div_eq_mul_inv, inv_pow] using h

/-- AKMM, p. 246, the corrected counterexample: with `r > 0`, the constant debt `a_t = a < 0`
(consumption `c_t = w + ra`, so the budget holds) satisfies the no-Ponzi condition
`lim a_{T+1}/(1 + r)^T = 0 ≥ 0` but violates `lim a_{T+1} ≥ 0`. -/
theorem discreteBudget_npg_counterexample {r a w : ℝ} (hr : 0 < r) (ha : a < 0) :
    (∀ t : ℕ, (fun _ : ℕ => a) (t + 1) =
      w + (1 + r) * (fun _ : ℕ => a) t - (fun _ : ℕ => w + r * a) t) ∧
      Tendsto (fun T : ℕ => a / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a) ∧ ¬ 0 ≤ a := by
  refine ⟨fun t => by ring, ?_, tendsto_const_nhds, not_le.mpr ha⟩
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a
  simpa [div_eq_mul_inv, inv_pow] using h

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The discrete-time Hamiltonian

AKMM, §9.2 (pp. 244–246): the consumption–saving problem
`max Σ_{t≤T} β^t u(c_t)` subject to `a_{t+1} = w + (1 + r)a_t − c_t`, `a_0` given and
`a_{T+1} ≥ 0`, solved through the "discrete Hamiltonian" `H_t = β^t u(c_t) + μ_t(ra_t + w − c_t)`.

* The Lagrangian rewriting `L = Σ H_t − Σ μ_t(a_{t+1} − a_t) + λa_{T+1}`
  (`discreteHamiltonian_lagrangian`); the first-order conditions (9.9), (9.10) as derivatives of
  `H_t`, and the terminal conditions (9.11)–(9.13) with `a_{T+1} = 0`.
* The Euler equation (9.14), `β^T u'(c_T) = u'(c_0)/(1 + r)^T`, and the equivalence of (9.13)
  with `a_{T+1}/(1 + r)^T = 0` and with `a_{T+1} = 0`.
* The book uses Kuhn–Tucker without proving that the conditions are sufficient. With `u`
  concave, a path satisfying the Euler equation and `a_{T+1} = 0` is optimal
  (`discreteHamiltonian_finite_sufficient`). Necessity and the infinite horizon are in
  `DiscreteOptimality`.
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, p. 244: the discrete-time Hamiltonian `H_t = β^t u(c_t) + μ_t(ra_t + w − c_t)`. -/
noncomputable def discreteHamiltonian (β r w : ℝ) (u : ℝ → ℝ) (t : ℕ) (μ a c : ℝ) : ℝ :=
  β ^ t * u c + μ * (r * a + w - c)

/-- AKMM, p. 244: the Lagrangian
`L = Σ_{t≤T} β^t u(c_t) + Σ_{t≤T} μ_t((1 + r)a_t + w − c_t − a_{t+1}) + λa_{T+1}`. -/
noncomputable def discreteLagrangian (β r w : ℝ) (u : ℝ → ℝ) (T : ℕ) (lam : ℝ)
    (μ a c : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) +
    ∑ t ∈ Finset.range (T + 1), μ t * ((1 + r) * a t + w - c t - a (t + 1)) + lam * a (T + 1)

/-- AKMM, (9.8) and p. 244: with the budget in difference form, the Lagrangian is
`L = Σ_{t≤T} H_t − Σ_{t≤T} μ_t(a_{t+1} − a_t) + λa_{T+1}`. -/
theorem discreteHamiltonian_lagrangian (β r w : ℝ) (u : ℝ → ℝ) (T : ℕ) (lam : ℝ)
    (μ a c : ℕ → ℝ) :
    discreteLagrangian β r w u T lam μ a c =
      ∑ t ∈ Finset.range (T + 1), discreteHamiltonian β r w u t (μ t) (a t) (c t) -
        ∑ t ∈ Finset.range (T + 1), μ t * (a (t + 1) - a t) + lam * a (T + 1) := by
  simp only [discreteLagrangian, discreteHamiltonian]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- AKMM, (9.8), p. 244: the budget (9.6) in difference form `a_{t+1} − a_t = ra_t + w − c_t`. -/
theorem eq_9_8 {r w a a' c : ℝ} : a' = w + (1 + r) * a - c ↔ a' - a = r * a + w - c := by
  constructor <;> intro h <;> linarith

/-- AKMM, (9.9), p. 244: `∂H_t/∂c_t = β^t u'(c_t) − μ_t`, so (9.9) is `β^t u'(c_t) = μ_t`. -/
theorem eq_9_9 {β r w μ a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) (t : ℕ) :
    HasDerivAt (fun x => discreteHamiltonian β r w u t μ a x) (β ^ t * u'c - μ) c ∧
      (β ^ t * u'c - μ = 0 ↔ β ^ t * u'c = μ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h := (hu.const_mul (β ^ t)).add (((hasDerivAt_id c).neg.const_add (r * a + w)).const_mul μ)
  change HasDerivAt (fun x => β ^ t * u x + μ * (r * a + w - x)) _ c
  convert h using 1
  · funext x
    simp only [Pi.add_apply, Pi.neg_apply, id]
    ring
  · ring

/-- AKMM, (9.10), p. 245: `∂H_{t+1}/∂a_{t+1} = rμ_{t+1}`, so (9.10),
`∂H_{t+1}/∂a_{t+1} + μ_{t+1} − μ_t = 0`, is `μ_t = (1 + r)μ_{t+1}`. -/
theorem eq_9_10 {β r w μ μ' a c : ℝ} {u : ℝ → ℝ} (t : ℕ) :
    HasDerivAt (fun x => discreteHamiltonian β r w u (t + 1) μ' x c) (μ' * r) a ∧
      (μ' * r + μ' - μ = 0 ↔ μ = (1 + r) * μ') := by
  refine ⟨?_, by constructor <;> intro h <;> linarith⟩
  have h := ((((hasDerivAt_id a).const_mul r).add_const (w - c)).const_mul μ').const_add
    (β ^ (t + 1) * u c)
  change HasDerivAt (fun x => β ^ (t + 1) * u c + μ' * (r * x + w - c)) _ a
  convert h using 1
  · funext x
    simp only [id]
    ring
  · ring

/-- AKMM, (9.11)–(9.13), p. 245: from (9.9) at `T`, `−μ_T + λ = 0` and `λa_{T+1} = 0`, the
transversality condition `β^T u'(c_T)a_{T+1} = 0`; since `β^T u'(c_T) > 0`, `a_{T+1} = 0`. -/
theorem eq_9_13 {β u'T μT lam aT1 : ℝ} {T : ℕ} (h99 : β ^ T * u'T = μT) (h911 : -μT + lam = 0)
    (h912 : lam * aT1 = 0) :
    β ^ T * u'T * aT1 = 0 ∧ (0 < β → 0 < u'T → aT1 = 0) := by
  have hlam : lam = β ^ T * u'T := by linarith
  have h : β ^ T * u'T * aT1 = 0 := by rw [← hlam]; exact h912
  refine ⟨h, fun hβ hu => ?_⟩
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (mul_pos (pow_pos hβ T) hu).ne'
  · exact h

/-- AKMM, (9.14), p. 245: `β^t u'(c_t) = μ_t` and `μ_t = (1 + r)μ_{t+1}` give the Euler
equation `u'(c_t) = β(1 + r)u'(c_{t+1})`. -/
theorem eq_9_14 {β r u't u't1 μt μt1 : ℝ} {t : ℕ} (hβ : β ≠ 0)
    (h1 : β ^ t * u't = μt) (h2 : β ^ (t + 1) * u't1 = μt1) (h3 : μt = (1 + r) * μt1) :
    u't = β * (1 + r) * u't1 := by
  have hp : β ^ t ≠ 0 := pow_ne_zero _ hβ
  apply mul_left_cancel₀ hp
  rw [h1, h3, ← h2, pow_succ]
  ring

/-- AKMM, p. 245: iterating the Euler equation from `0` to `t ≤ T`,
`β^t u'(c_t) = u'(c_0)/(1 + r)^t`. -/
theorem discreteHamiltonian_marginal {β r : ℝ} {mu : ℕ → ℝ} {T : ℕ} (hr : 0 < 1 + r)
    (heuler : ∀ t, t < T → mu t = β * (1 + r) * mu (t + 1)) :
    ∀ t, t ≤ T → β ^ t * mu t = mu 0 / (1 + r) ^ t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    have he := heuler n (by omega)
    rw [he] at h
    rw [pow_succ, pow_succ, eq_div_iff (mul_pos (pow_pos hr n) hr).ne']
    rw [eq_div_iff (pow_pos hr n).ne'] at h
    linarith [h]

/-- AKMM, p. 245: given the Euler equation and `u'(c_0) > 0`, `β > 0`, the TVC (9.13)
`β^T u'(c_T)a_{T+1} = 0` is equivalent to `a_{T+1}/(1 + r)^T = 0` and to `a_{T+1} = 0`. -/
theorem discreteHamiltonian_tvc_iff {β r aT1 : ℝ} {mu : ℕ → ℝ} {T : ℕ} (hr : 0 < 1 + r)
    (hmu : 0 < mu 0) (heuler : ∀ t, t < T → mu t = β * (1 + r) * mu (t + 1)) :
    (β ^ T * mu T * aT1 = 0 ↔ aT1 / (1 + r) ^ T = 0) ∧ (aT1 / (1 + r) ^ T = 0 ↔ aT1 = 0) := by
  have h := discreteHamiltonian_marginal hr heuler T le_rfl
  have hp := pow_pos hr T
  rw [h]
  refine ⟨?_, by rw [div_eq_zero_iff]; simp [hp.ne']⟩
  rw [div_mul_eq_mul_div, div_eq_zero_iff, div_eq_zero_iff, mul_eq_zero]
  simp [hmu.ne', hp.ne']

/-- AKMM, §9.2, pp. 244–245: **sufficiency** of the conditions in the finite horizon. If `u` is
concave on `(0, ∞)` with derivative `u'`, `1 + r > 0`, and a path with positive consumption
satisfies the budget (9.6), the Euler equation (9.14) and `a_{T+1} = 0`, then it maximizes
`Σ_{t≤T} β^t u(c_t)` over every path from the same `a_0` with positive consumption and
`a_{T+1} ≥ 0`. -/
theorem discreteHamiltonian_finite_sufficient {β r w : ℝ} {u u' : ℝ → ℝ} {T : ℕ}
    (hr : 0 < 1 + r) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hβ : 0 ≤ β)
    {a c a' c' : ℕ → ℝ} (hc : ∀ t, 0 < c t) (hb : ∀ t, a (t + 1) = w + (1 + r) * a t - c t)
    (heuler : ∀ t, t < T → u' (c t) = β * (1 + r) * u' (c (t + 1))) (hT : a (T + 1) = 0)
    (hpos : 0 ≤ u' (c 0))
    (hc' : ∀ t, 0 < c' t) (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (h0 : a' 0 = a 0) (hT' : 0 ≤ a' (T + 1)) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) := by
  have hm := discreteHamiltonian_marginal (mu := fun t => u' (c t)) hr heuler
  have hr' : ∀ _ : ℕ, 0 < 1 + r := fun _ => hr
  have B := appendix_9A3_discrete_budget (r := fun _ => r) (w := fun _ => w) hr' hb T
  have B' := appendix_9A3_discrete_budget (r := fun _ => r) (w := fun _ => w) hr' hb' T
  simp only [discreteBudget_const_discount] at B B'
  rw [h0] at B'
  have hstep : ∀ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      β ^ t * u (c t) + u' (c 0) * (c' t / (1 + r) ^ t - c t / (1 + r) ^ t) := by
    intro t ht
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t))
      (Set.mem_Ioi.mpr (hc' t)) (hu (c t) (hc t))
    have hmt := hm t (by simpa [Nat.lt_succ_iff] using ht)
    have hk : u' (c 0) * (c' t / (1 + r) ^ t - c t / (1 + r) ^ t) =
        β ^ t * u' (c t) * (c' t - c t) := by
      rw [hmt]
      ring
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg hβ t)]
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hdiff : ∑ t ∈ Finset.range (T + 1), c' t / (1 + r) ^ t -
      ∑ t ∈ Finset.range (T + 1), c t / (1 + r) ^ t = -(a' (T + 1) / (1 + r) ^ T) := by
    rw [hT, zero_div] at B
    linarith
  rw [hdiff] at hsum
  have : 0 ≤ u' (c 0) * (a' (T + 1) / (1 + r) ^ T) :=
    mul_nonneg hpos (div_nonneg hT' (pow_pos hr T).le)
  linarith

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Necessity and the infinite horizon for the discrete Hamiltonian

AKMM, §9.2 (pp. 244–246). The first-order conditions of the discrete consumption–saving
problem are derived in the book from the Kuhn–Tucker theorem without proof. Here:

* **Necessity** by a direct perturbation: moving `ε` of consumption from period `t` to period
  `t + 1` (`c_t − ε`, `a_{t+1} + ε`, `c_{t+1} + (1 + r)ε`) keeps the path feasible
  (`discreteOptimality_perturb_budget`) and changes lifetime utility only in two terms
  (`discreteOptimality_perturb_sum`), so at an optimum the Euler equation (9.14) holds, both in
  the finite horizon (`discreteHamiltonian_euler_necessary`) and for catching-up optimality in
  the infinite horizon (`discreteHamiltonian_euler_necessary_infinite`); and `a_{T+1} = 0` at a
  finite-horizon optimum when `u` is strictly increasing (`discreteHamiltonian_tvc_necessary`).
* **Infinite horizon** (p. 246): the TVC `lim β^T u'(c_T)a_{T+1} = 0` is equivalent to
  `lim a_{T+1}/(1 + r)^T = 0` (`discreteHamiltonian_tvc_infinite_iff`); the Euler equation and
  the TVC are sufficient for catching-up optimality against every path satisfying the no-Ponzi
  condition (9.15) (`discreteHamiltonian_infinite_sufficient`), using the finite-horizon bound
  `EulerTransversality.finite_horizon_bound`; and an instance: with `β(1 + r) = 1`, keeping the
  asset constant is optimal (`discreteHamiltonian_constant_path_optimal`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- The perturbed consumption path: `c_t − ε` at `t`, `c_{t+1} + (1 + r)ε` at `t + 1`. -/
noncomputable def discreteOptimality_pc (r : ℝ) (c : ℕ → ℝ) (t : ℕ) (ε : ℝ) (s : ℕ) : ℝ :=
  if s = t then c t - ε else if s = t + 1 then c (t + 1) + (1 + r) * ε else c s

/-- The perturbed asset path: `a_{t+1} + ε`. -/
noncomputable def discreteOptimality_pa (a : ℕ → ℝ) (t : ℕ) (ε : ℝ) (s : ℕ) : ℝ :=
  if s = t + 1 then a (t + 1) + ε else a s

/-- The perturbation keeps the budget (9.6): moving `ε` of consumption from `t` to `t + 1` is
financed by saving `ε` more at `t`. -/
theorem discreteOptimality_perturb_budget {r w : ℝ} {a c : ℕ → ℝ}
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (t : ℕ) (ε : ℝ) (s : ℕ) :
    discreteOptimality_pa a t ε (s + 1) =
      w + (1 + r) * discreteOptimality_pa a t ε s - discreteOptimality_pc r c t ε s := by
  simp only [discreteOptimality_pa, discreteOptimality_pc]
  by_cases h1 : s = t
  · subst h1
    simp only [↓reduceIte, show s ≠ s + 1 by omega]
    rw [hb s]
    ring
  · by_cases h2 : s = t + 1
    · subst h2
      simp only [↓reduceIte, h1, show t + 1 + 1 ≠ t + 1 by omega]
      rw [hb (t + 1)]
      ring
    · simp only [show s + 1 ≠ t + 1 by omega, h1, h2, ↓reduceIte]
      exact hb s

/-- The perturbation changes lifetime utility over any horizon `N > t + 1` only through the two
perturbed periods. -/
theorem discreteOptimality_perturb_sum (β r : ℝ) (u : ℝ → ℝ) (c : ℕ → ℝ) {t N : ℕ}
    (hN : t + 1 < N) (ε : ℝ) :
    ∑ s ∈ Finset.range N, β ^ s * u (discreteOptimality_pc r c t ε s) =
      ∑ s ∈ Finset.range N, β ^ s * u (c s) +
        ((β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + (1 + r) * ε)) -
          (β ^ t * u (c t) + β ^ (t + 1) * u (c (t + 1)))) := by
  have hsub : ({t, t + 1} : Finset ℕ) ⊆ Finset.range N := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_range]
    omega
  have hz : ∀ s ∈ Finset.range N, s ∉ ({t, t + 1} : Finset ℕ) →
      β ^ s * u (discreteOptimality_pc r c t ε s) - β ^ s * u (c s) = 0 := by
    intro s _ hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    simp [discreteOptimality_pc, hs.1, hs.2]
  have h := Finset.sum_subset hsub hz
  have e1 : discreteOptimality_pc r c t ε t = c t - ε := by simp [discreteOptimality_pc]
  have e2 : discreteOptimality_pc r c t ε (t + 1) = c (t + 1) + (1 + r) * ε := by
    simp [discreteOptimality_pc]
  rw [Finset.sum_pair (show t ≠ t + 1 by omega), e1, e2] at h
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- The two-period perturbation value `g(ε) = β^t u(c_t − ε) + β^{t+1}u(c_{t+1} + (1 + r)ε)` has
a local maximum at `0` only if the Euler equation `u'(c_t) = β(1 + r)u'(c_{t+1})` holds. -/
theorem discreteOptimality_euler_of_localMax {β r : ℝ} {u u' : ℝ → ℝ} {x y : ℝ} {t : ℕ}
    (hβ : β ≠ 0) (hx : HasDerivAt u (u' x) x) (hy : HasDerivAt u (u' y) y)
    (hmax : ∀ᶠ ε in 𝓝 (0 : ℝ), β ^ t * u (x - ε) + β ^ (t + 1) * u (y + (1 + r) * ε) ≤
      β ^ t * u x + β ^ (t + 1) * u y) :
    u' x = β * (1 + r) * u' y := by
  set g : ℝ → ℝ := fun ε => β ^ t * u (x - ε) + β ^ (t + 1) * u (y + (1 + r) * ε)
  have hg1 : HasDerivAt (fun ε : ℝ => u (x - ε)) (u' x * (-1)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => x - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub x
    exact hx.comp_of_eq (0 : ℝ) hin (by simp)
  have hg2 : HasDerivAt (fun ε : ℝ => u (y + (1 + r) * ε)) (u' y * (1 + r)) 0 := by
    have hin : HasDerivAt (fun ε : ℝ => y + (1 + r) * ε) (1 + r) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add y
    exact hy.comp_of_eq (0 : ℝ) hin (by simp)
  have hg : HasDerivAt g (β ^ t * (u' x * (-1)) + β ^ (t + 1) * (u' y * (1 + r))) 0 :=
    (hg1.const_mul _).add (hg2.const_mul _)
  have hloc : IsLocalMax g 0 := by
    filter_upwards [hmax] with ε hε
    simpa [g] using hε
  have h0 := hloc.hasDerivAt_eq_zero hg
  have hp : β ^ t ≠ 0 := pow_ne_zero _ hβ
  apply mul_left_cancel₀ hp
  rw [pow_succ] at h0
  linear_combination -h0

/-- Positivity of the perturbed consumption for small `ε`. -/
theorem discreteOptimality_perturb_pos {r : ℝ} {c : ℕ → ℝ} (hc : ∀ s, 0 < c s) (t : ℕ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < discreteOptimality_pc r c t ε s := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c t - ε := by
    have : Tendsto (fun ε : ℝ => c t - ε) (𝓝 0) (𝓝 (c t - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.eventually (lt_mem_nhds (hc t))
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c (t + 1) + (1 + r) * ε := by
    have : Tendsto (fun ε : ℝ => c (t + 1) + (1 + r) * ε) (𝓝 0) (𝓝 (c (t + 1) + (1 + r) * 0)) :=
      tendsto_const_nhds.add (tendsto_id.const_mul _)
    rw [mul_zero, add_zero] at this
    exact this.eventually (lt_mem_nhds (hc (t + 1)))
  filter_upwards [h1, h2] with ε e1 e2 s
  simp only [discreteOptimality_pc]
  split_ifs
  · exact e1
  · exact e2
  · exact hc s

/-- AKMM, (9.14), p. 245, **necessity** in the finite horizon: if a path with positive
consumption maximizes `Σ_{s≤T} β^s u(c_s)` over all paths from `a_0` with positive consumption
satisfying (9.6) and `a_{T+1} ≥ 0`, then the Euler equation holds for every `t < T`. -/
theorem discreteHamiltonian_euler_necessary {β r w : ℝ} {u u' : ℝ → ℝ} {T : ℕ} (hβ : β ≠ 0)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (hT : 0 ≤ a (T + 1))
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 → (∀ s, a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, 0 < c' s) → 0 ≤ a' (T + 1) →
      ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤ ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s))
    {t : ℕ} (ht : t < T) : u' (c t) = β * (1 + r) * u' (c (t + 1)) := by
  refine discreteOptimality_euler_of_localMax (t := t) hβ (hu _ (hc t)) (hu _ (hc (t + 1))) ?_
  filter_upwards [discreteOptimality_perturb_pos (r := r) hc t] with ε hε
  have h := hopt (discreteOptimality_pa a t ε) (discreteOptimality_pc r c t ε)
    (by simp [discreteOptimality_pa]) (discreteOptimality_perturb_budget hb t ε) hε
    (by simpa [discreteOptimality_pa, show T ≠ t by omega] using hT)
  rw [discreteOptimality_perturb_sum β r u c (by omega) ε] at h
  linarith

/-- AKMM, p. 245, **necessity** of `a_{T+1} = 0`: at a finite-horizon optimum, with `u` strictly
increasing on `(0, ∞)`, the terminal asset is zero (otherwise consume it in period `T`). -/
theorem discreteHamiltonian_tvc_necessary {β r w : ℝ} {u : ℝ → ℝ} {T : ℕ} (hβ : 0 < β)
    (hmono : StrictMonoOn u (Set.Ioi 0)) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s) (hT : 0 ≤ a (T + 1))
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 →
      (∀ s, s ≤ T → a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, s ≤ T → 0 < c' s) → 0 ≤ a' (T + 1) →
      ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤ ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s)) :
    a (T + 1) = 0 := by
  by_contra hne
  have hpos : 0 < a (T + 1) := lt_of_le_of_ne hT (Ne.symm hne)
  set c' : ℕ → ℝ := fun s => if s = T then c T + a (T + 1) else c s
  set a' : ℕ → ℝ := fun s => if s = T + 1 then 0 else a s
  have hb' : ∀ s, s ≤ T → a' (s + 1) = w + (1 + r) * a' s - c' s := by
    intro s hs
    simp only [a', c']
    by_cases h : s = T
    · subst h
      simp only [↓reduceIte, show s ≠ s + 1 by omega]
      rw [hb s]
      ring
    · simp only [show s + 1 ≠ T + 1 by omega, h, show s ≠ T + 1 by omega, ↓reduceIte]
      exact hb s
  have hc' : ∀ s, s ≤ T → 0 < c' s := by
    intro s _
    simp only [c']
    split_ifs
    · linarith [hc T]
    · exact hc s
  have h := hopt a' c' (by simp [a']) hb' hc' (by simp [a'])
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  have hsame : ∑ s ∈ Finset.range T, β ^ s * u (c' s) = ∑ s ∈ Finset.range T, β ^ s * u (c s) :=
    Finset.sum_congr rfl fun s hs => by
      simp [c', (Finset.mem_range.mp hs).ne]
  rw [hsame] at h
  have hlt : u (c T) < u (c' T) := by
    simp only [c', ↓reduceIte]
    exact hmono (Set.mem_Ioi.mpr (hc T)) (Set.mem_Ioi.mpr (by linarith [hc T])) (by linarith)
  have := mul_lt_mul_of_pos_left hlt (pow_pos hβ T)
  linarith

/-- AKMM, p. 246: given the Euler equation for every `t` and `u'(c_0) ≠ 0`, the TVC
`lim β^T u'(c_T)a_{T+1} = 0` is equivalent to `lim a_{T+1}/(1 + r)^T = 0`. -/
theorem discreteHamiltonian_tvc_infinite_iff {β r : ℝ} {mu a : ℕ → ℝ} (hr : 0 < 1 + r)
    (hmu : mu 0 ≠ 0) (heuler : ∀ t, mu t = β * (1 + r) * mu (t + 1)) :
    Tendsto (fun T => β ^ T * mu T * a (T + 1)) atTop (𝓝 0) ↔
      Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 0) := by
  have hm : ∀ T, β ^ T * mu T * a (T + 1) = mu 0 * (a (T + 1) / (1 + r) ^ T) := fun T => by
    rw [discreteHamiltonian_marginal (T := T) hr (fun t _ => heuler t) T le_rfl]
    ring
  simp only [hm]
  constructor
  · intro h
    have := h.const_mul (mu 0)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hmu] using this
  · intro h
    simpa using h.const_mul (mu 0)

/-- AKMM, p. 246, **sufficiency** in the infinite horizon. If `u` is concave on `(0, ∞)`, `β ≥ 0`,
`1 + r > 0`, and a path with positive consumption satisfies (9.6), the Euler equation (9.14) for
every `t`, and the TVC `lim a_{T+1}/(1 + r)^T = 0`, then it is catching-up optimal against every
path from `a_0` with positive consumption that satisfies the no-Ponzi condition (9.15), stated as
`liminf a'_{T+1}/(1 + r)^T ≥ 0`: for every `δ > 0`, eventually
`Σ_{t≤T} β^t u(c'_t) ≤ Σ_{t≤T} β^t u(c_t) + δ`. -/
theorem discreteHamiltonian_infinite_sufficient {β r w : ℝ} {u u' : ℝ → ℝ} (hβ : 0 ≤ β)
    (hr : 0 < 1 + r) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (hb : ∀ t, a (t + 1) = w + (1 + r) * a t - c t)
    (heuler : ∀ t, u' (c t) = β * (1 + r) * u' (c (t + 1))) (hpos : 0 ≤ u' (c 0))
    (htvc : Tendsto (fun T => a (T + 1) / (1 + r) ^ T) atTop (𝓝 0))
    {a' c' : ℕ → ℝ} (h0 : a' 0 = a 0) (hc' : ∀ t, 0 < c' t)
    (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (c t) + δ := by
  set G : Set (ℝ × ℝ) := {p | 0 < w + (1 + r) * p.1 - p.2}
  set F : ℝ → ℝ → ℝ := fun x y => u (w + (1 + r) * x - y)
  set p : ℕ → ℝ →ₗ[ℝ] ℝ := fun t => ((1 + r) * u' (c t)) • LinearMap.id
  set q : ℕ → ℝ →ₗ[ℝ] ℝ := fun t => (-u' (c t)) • LinearMap.id
  have hcx : ∀ t, w + (1 + r) * a t - a (t + 1) = c t := fun t => by rw [hb t]; ring
  have hsup : ∀ t, ∀ x y, (x, y) ∈ G →
      F x y ≤ F (a t) (a (t + 1)) + p t (x - a t) + q t (y - a (t + 1)) := by
    intro t x y hxy
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t))
      (Set.mem_Ioi.mpr hxy) (hu (c t) (hc t))
    simp only at hs
    simp only [F, p, q, hcx, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    have e : w + (1 + r) * x - y - c t = (1 + r) * (x - a t) - (y - a (t + 1)) := by
      rw [← hcx t]; ring
    rw [e] at hs
    linarith [hs, show u' (c t) * ((1 + r) * (x - a t) - (y - a (t + 1))) =
      (1 + r) * u' (c t) * (x - a t) + -u' (c t) * (y - a (t + 1)) by ring]
  have hE : ∀ t v, q t v + β * p (t + 1) v = 0 := by
    intro t v
    simp only [p, q, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [heuler t]
    ring
  have hfeas : DPExtensions.EulerTransversality.Feasible G (a 0) a' := by
    refine ⟨h0, fun t => ?_⟩
    change 0 < w + (1 + r) * a' t - a' (t + 1)
    have := hc' t
    rw [hb' t] at *
    linarith
  have hbound := DPExtensions.EulerTransversality.finite_horizon_bound hβ hsup hE hfeas
  have hpv : ∀ (x y : ℕ → ℝ), (∀ t, x (t + 1) = w + (1 + r) * x t - y t) → ∀ T,
      DPExtensions.EulerTransversality.partialValue F β x T =
        ∑ t ∈ Finset.range T, β ^ t * u (y t) := by
    intro x y hxy T
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [F]
    rw [hxy t]
    ring_nf
  have hm := fun T => discreteHamiltonian_marginal (mu := fun t => u' (c t)) (T := T) hr
    (fun t _ => heuler t) T le_rfl
  intro δ hδ
  set K := u' (c 0)
  set η := δ / (2 * (K + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  filter_upwards [hnpg η hη, (htvc.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < η by
    simpa using hη)))] with T hT1 hT2
  have h := hbound (T + 1)
  rw [hpv a' c' hb', hpv a c hb] at h
  simp only [p, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  have hk : ∀ x, β ^ (T + 1) * ((1 + r) * u' (c (T + 1)) * x) = K * (x / (1 + r) ^ T) := by
    intro x
    have e := hm (T + 1)
    have hp := pow_pos hr T
    rw [show β ^ (T + 1) * ((1 + r) * u' (c (T + 1)) * x) =
        (β ^ (T + 1) * u' (c (T + 1))) * (1 + r) * x by ring, e, pow_succ]
    field_simp
  rw [hk, hk] at h
  have habs := abs_lt.mp hT2
  have hK : K * (a (T + 1) / (1 + r) ^ T) - K * (a' (T + 1) / (1 + r) ^ T) ≤ K * (2 * η) := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith [habs.2]) hpos
  have hKη : K * (2 * η) ≤ δ := by
    have e : K * (2 * η) = δ * (K / (K + 1)) := by
      simp only [η]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right hδ.le ((div_le_one (by linarith)).mpr (by linarith))
  linarith

/-- AKMM, p. 246, an instance of the infinite-horizon sufficiency theorem: if `β(1 + r) = 1` with
`r > 0`, the path that keeps the asset constant, `a_t = a_0` and `c_t = w + ra_0 > 0`, is
catching-up optimal against every no-Ponzi path. -/
theorem discreteHamiltonian_constant_path_optimal {β r w a₀ : ℝ} {u u' : ℝ → ℝ}
    (hr : 0 < r) (hβr : β * (1 + r) = 1) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hc0 : 0 < w + r * a₀)
    (hpos : 0 ≤ u' (w + r * a₀)) {a' c' : ℕ → ℝ} (h0 : a' 0 = a₀) (hc' : ∀ t, 0 < c' t)
    (hb' : ∀ t, a' (t + 1) = w + (1 + r) * a' t - c' t)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), β ^ t * u (c' t) ≤
      ∑ t ∈ Finset.range (T + 1), β ^ t * u (w + r * a₀) + δ := by
  have hβ : 0 ≤ β := by
    by_contra h
    have : β * (1 + r) < 0 := mul_neg_of_neg_of_pos (not_le.mp h) (by linarith)
    linarith
  have htvc : Tendsto (fun T : ℕ => a₀ / (1 + r) ^ T) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a₀
    simpa [div_eq_mul_inv, inv_pow] using h
  exact discreteHamiltonian_infinite_sufficient (a := fun _ => a₀) (c := fun _ => w + r * a₀)
    hβ (by linarith) hconc hu (fun _ => hc0) (fun _ => by ring)
    (fun _ => by rw [hβr, one_mul]) hpos htvc h0 hc' hb' hnpg

/-- AKMM, (9.14), p. 246, **necessity** in the infinite horizon: if a path with positive
consumption is catching-up optimal against every path from `a_0` with positive consumption that
satisfies the no-Ponzi condition, and itself satisfies it, then the Euler equation holds at every
`t`. -/
theorem discreteHamiltonian_euler_necessary_infinite {β r w : ℝ} {u u' : ℝ → ℝ} (hβ : β ≠ 0)
    (hu : ∀ x, 0 < x → HasDerivAt u (u' x) x) {a c : ℕ → ℝ} (hc : ∀ s, 0 < c s)
    (hb : ∀ s, a (s + 1) = w + (1 + r) * a s - c s)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ a (T + 1) / (1 + r) ^ T)
    (hopt : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 → (∀ s, a' (s + 1) = w + (1 + r) * a' s - c' s) →
      (∀ s, 0 < c' s) → (∀ η > 0, ∀ᶠ T in atTop, -η ≤ a' (T + 1) / (1 + r) ^ T) →
      ∀ δ > 0, ∀ᶠ T in atTop, ∑ s ∈ Finset.range (T + 1), β ^ s * u (c' s) ≤
        ∑ s ∈ Finset.range (T + 1), β ^ s * u (c s) + δ)
    (t : ℕ) : u' (c t) = β * (1 + r) * u' (c (t + 1)) := by
  refine discreteOptimality_euler_of_localMax (t := t) hβ (hu _ (hc t)) (hu _ (hc (t + 1))) ?_
  filter_upwards [discreteOptimality_perturb_pos (r := r) hc t] with ε hε
  have hnpg' : ∀ η > 0, ∀ᶠ T in atTop,
      -η ≤ discreteOptimality_pa a t ε (T + 1) / (1 + r) ^ T := by
    intro η hη
    filter_upwards [hnpg η hη, eventually_gt_atTop t] with T hT hT'
    simpa [discreteOptimality_pa, show T ≠ t by omega] using hT
  have h := hopt (discreteOptimality_pa a t ε) (discreteOptimality_pc r c t ε)
    (by simp [discreteOptimality_pa]) (discreteOptimality_perturb_budget hb t ε) hε hnpg'
  set D := (β ^ t * u (c t - ε) + β ^ (t + 1) * u (c (t + 1) + (1 + r) * ε)) -
    (β ^ t * u (c t) + β ^ (t + 1) * u (c (t + 1)))
  have hD : ∀ δ > 0, D ≤ δ := by
    intro δ hδ
    obtain ⟨T, hT⟩ := ((h δ hδ).and (eventually_gt_atTop (t + 1))).exists
    rw [discreteOptimality_perturb_sum β r u c (by omega) ε] at hT
    linarith [hT.1]
  have : D ≤ 0 := le_of_forall_pos_le_add fun δ hδ => by linarith [hD δ hδ]
  linarith

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Products of one-period discount factors and their continuous limit

AKMM, Appendix 9.A.3 (pp. 844–845): dividing one period into subperiods of length `Δ` and
discounting each by `1 + r(tΔ)Δ`, `t = 1, …, T/Δ`, the book takes logs and argues
`−log ∏(1 + r(tΔ)Δ) = −Σ log(1 + r(tΔ)Δ) ≈ −Σ r(tΔ)Δ → −∫_0^T r`. Here, with `Δ = T/n`:

* the Riemann sums `Σ_{t=1}^n r(tΔ)Δ` converge to `∫_0^T r` for continuous `r`
  (`productLimits_riemann`), by uniform continuity on `[0, T]`;
* `|Σ log(1 + r(tΔ)Δ) − Σ r(tΔ)Δ| ≤ 2M²T²/n` (`M` a bound of `|r|`), using
  `|log(1 + x) − x| ≤ x²/(1 − |x|)` from `GrowthRates`, so
  `∏_{t=1}^n (1 + r(tΔ)Δ) → e^{∫_0^T r}` (`productLimits_product`);
* hence the continuous-time nPg discount `1/∏(1 + r(tΔ)Δ) → e^{−∫_0^T r}`
  (`appendix_9A3_product_limit`), and, for §9.4, the probability of no success in `n`
  independent trials with probabilities `λ(tΔ)Δ` tends to `e^{−∫_0^T λ}`
  (`productLimits_survival`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, Appendix 9.A.3, p. 845: for continuous `r` and `T > 0`, the Riemann sums with
right endpoints, `Σ_{i<n} r((i + 1)T/n)·T/n`, converge to `∫_0^T r`. -/
theorem productLimits_riemann {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, r ((i + 1) * (T / n)) * (T / n)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, r s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn r (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hr.continuousOn
  obtain ⟨δ, hδ, hδr⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / (2 * T)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith
  set Δ := T / n with hΔdef
  have hΔ0 : 0 < Δ := div_pos hT hn0
  have hΔ : Δ < δ := by
    rw [hΔdef, div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hnΔ : (n : ℝ) * Δ = T := by rw [hΔdef]; field_simp
  have hsplit : ∑ i ∈ Finset.range n, ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s =
      ∫ s in (0 : ℝ)..T, r s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * Δ)
      (n := n) (f := r) (μ := MeasureTheory.volume) fun i _ => hr.intervalIntegrable _ _
    simpa [hnΔ] using this
  have hterm : ∀ i ∈ Finset.range n, |r ((i + 1) * Δ) * Δ -
      ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s| ≤ ε / (2 * T) * Δ := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.mp hi
      exact_mod_cast this
    have hlen : ((i + 1 : ℕ) : ℝ) * Δ - i * Δ = Δ := by push_cast; ring
    have hconst : ∫ _ in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r ((i + 1) * Δ) = r ((i + 1) * Δ) * Δ := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul, mul_comm]
    have hdiff : r ((i + 1) * Δ) * Δ - ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s =
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), (r ((i + 1) * Δ) - r s) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hr.intervalIntegrable _ _),
        hconst]
    rw [hdiff]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (i : ℝ) * Δ) (b := ((i + 1 : ℕ) : ℝ) * Δ) (C := ε / (2 * T))
      (f := fun s => r ((i + 1) * Δ) - r s) (fun s hs => ?_)
    · rw [Real.norm_eq_abs] at hb
      rw [abs_of_pos (by linarith : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) * Δ - i * Δ), hlen] at hb
      exact hb
    · rw [Set.uIoc_of_le (by push_cast; nlinarith)] at hs
      push_cast at hs
      have hs0 : 0 ≤ s := le_trans (by positivity) hs.1.le
      have hsT : s ≤ T := by rw [← hnΔ]; nlinarith [hs.2]
      have hiT : ((i : ℝ) + 1) * Δ ≤ T := by rw [← hnΔ]; nlinarith
      have hd : dist ((i + 1) * Δ) s < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> nlinarith [hs.1, hs.2]
      have := hδr ((i + 1) * Δ) ⟨by positivity, hiT⟩ s ⟨hs0, hsT⟩ hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]
      exact this.le
  rw [Real.dist_eq, ← hsplit, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range n, (r ((i + 1) * Δ) * Δ -
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s)|
      ≤ ∑ i ∈ Finset.range n, |r ((i + 1) * Δ) * Δ -
        ∫ s in (i * Δ : ℝ)..((i + 1 : ℕ) * Δ), r s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε / (2 * T) * Δ := Finset.sum_le_sum hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm (n : ℝ),
          mul_assoc, hnΔ]
        field_simp
    _ < ε := half_lt_self hε

/-- AKMM, Appendix 9.A.3, pp. 844–845: for continuous `r` and `T > 0`, with `Δ = T/n`,
`∏_{t=1}^n (1 + r(tΔ)Δ) → e^{∫_0^T r}` as `n → ∞`. -/
theorem productLimits_product {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 + r ((i + 1) * (T / n)) * (T / n))) atTop
      (𝓝 (Real.exp (∫ s in (0 : ℝ)..T, r s))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hr.continuousOn (s := Set.Icc 0 T))
  set B := |M| + 1
  have hB : 0 < B := by positivity
  set x : ℕ → ℕ → ℝ := fun n i => r ((i + 1) * (T / n)) * (T / n)
  have hxb : ∀ n : ℕ, 0 < n → ∀ i ∈ Finset.range n, |x n i| ≤ B * (T / n) := by
    intro n hn i hi
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hi
    have hmem : (i + 1) * (T / n) ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [mul_div_assoc', div_le_iff₀ hn']
      nlinarith
    have h := hM _ hmem
    rw [Real.norm_eq_abs] at h
    simp only [x, abs_mul, abs_of_pos (div_pos hT hn')]
    exact mul_le_mul_of_nonneg_right (h.trans (by simp [B]; linarith [le_abs_self M]))
      (div_pos hT hn').le
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, x n i
  set L : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, Real.log (1 + x n i)
  have hsmall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ B * (T / n) ≤ 1 / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * B * T)
    filter_upwards [eventually_gt_atTop N] with n hn
    have hn' : (N : ℝ) < n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt N.cast_nonneg hn'
    refine ⟨by exact_mod_cast hn0, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ hn0]
    nlinarith
  have hLS : ∀ᶠ n : ℕ in atTop, |L n - S n| ≤ 2 * (B * T) ^ 2 / n := by
    filter_upwards [hsmall] with n ⟨hn, hsm⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hterm : ∀ i ∈ Finset.range n, |Real.log (1 + x n i) - x n i| ≤ 2 * (B * (T / n)) ^ 2 := by
      intro i hi
      have hx := hxb n hn i hi
      have hx1 : |x n i| ≤ 1 / 2 := hx.trans hsm
      have hgt : -1 < x n i := by linarith [neg_abs_le (x n i)]
      have h := (growthRates_log_one_add_approx hgt).2.2 (by linarith)
      have hden : 1 / 2 ≤ 1 - |x n i| := by linarith
      have hsq : x n i ^ 2 ≤ (B * (T / n)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      calc |Real.log (1 + x n i) - x n i| ≤ x n i ^ 2 / (1 - |x n i|) := h
        _ ≤ x n i ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
        _ = 2 * x n i ^ 2 := by ring
        _ ≤ 2 * (B * (T / n)) ^ 2 := by linarith
    calc |L n - S n| = |∑ i ∈ Finset.range n, (Real.log (1 + x n i) - x n i)| := by
          simp only [L, S, Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.range n, |Real.log (1 + x n i) - x n i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, 2 * (B * (T / n)) ^ 2 := Finset.sum_le_sum hterm
      _ = 2 * (B * T) ^ 2 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hdiff : Tendsto (fun n : ℕ => L n - S n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 2 * (B * T) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hLS] with n hn
    rwa [Real.norm_eq_abs]
  have hL : Tendsto L atTop (𝓝 (∫ s in (0 : ℝ)..T, r s)) := by
    have := (productLimits_riemann hr hT).add hdiff
    rw [add_zero] at this
    refine this.congr fun n => ?_
    simp only [S, x]
    ring
  refine ((Real.continuous_exp.tendsto _).comp hL).congr' ?_
  filter_upwards [hsmall] with n ⟨hn, hsm⟩
  simp only [Function.comp, L, Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hx1 : |x n i| ≤ 1 / 2 := (hxb n hn i hi).trans hsm
  have hpos : 0 < 1 + x n i := by linarith [neg_abs_le (x n i)]
  exact Real.exp_log hpos

/-- AKMM, Appendix 9.A.3, p. 845: the continuous-time limit of the nPg discount factor,
`1/∏_{t=1}^{T/Δ}(1 + r(tΔ)Δ) → e^{−∫_0^T r(t)dt}` as `Δ = T/n → 0`. -/
theorem appendix_9A3_product_limit {r : ℝ → ℝ} (hr : Continuous r) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (∏ i ∈ Finset.range n, (1 + r ((i + 1) * (T / n)) * (T / n)))⁻¹)
      atTop (𝓝 (Real.exp (-∫ s in (0 : ℝ)..T, r s))) := by
  rw [Real.exp_neg]
  exact (productLimits_product hr hT).inv₀ (Real.exp_pos _).ne'

/-- AKMM, p. 259: with independent trials in subintervals of length `Δ = T/n` with success
probabilities `λ(tΔ)Δ`, the probability of no success, `∏_{t=1}^n (1 − λ(tΔ)Δ)`, tends to
`e^{−∫_0^T λ}`. -/
theorem productLimits_survival {lam : ℝ → ℝ} (hlam : Continuous lam) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 - lam ((i + 1) * (T / n)) * (T / n))) atTop
      (𝓝 (Real.exp (-∫ s in (0 : ℝ)..T, lam s))) := by
  have h := productLimits_product (r := fun s => -lam s) hlam.neg hT
  rw [intervalIntegral.integral_neg] at h
  refine h.congr fun n => Finset.prod_congr rfl fun i _ => ?_
  ring

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The continuous-time Hamiltonian and the Euler equation

AKMM, §9.2 (pp. 248–250): (9.19)–(9.26), the box on present- versus current-value
Hamiltonians and the box comparing discrete and continuous Euler equations.

* (9.19)–(9.21): the present-value Hamiltonian `H = e^{−ρt}u(c) + μ(ra + w − c)` and its
  derivatives; (9.20) is (9.24) `e^{−ρt}u'(c) = μ`, and (9.21) is (9.25) `rμ + μ̇ = 0`.
* The integration-by-parts step of the heuristic derivation, on a finite horizon
  (`continuousHamiltonian_integration_by_parts`).
* The current-value Hamiltonian `Ĥ = u(c) + μ̂(ra + w − c)` with `μ = e^{−ρt}μ̂`: `H = e^{−ρt}Ĥ`,
  and (9.22)–(9.23) are equivalent to (9.20)–(9.21).
* (9.26): the Euler equation `−(u''(c)c/u'(c))(ċ/c) = r − ρ`, derived from (9.24)–(9.25) by
  the growth-rate trick (9.5); proved for a time-varying `r(t)`, which (9.35) and (9.37) need.
* The coefficient of relative risk aversion is positive, and equals `σ` for CRRA utility
  `u(c) = (c^{1−σ} − 1)/(1 − σ)`.
* The discrete-continuous box: the linearized discrete Euler equation gives
  `−(u''(c_t)c_t/u'(c_t))((c_{t+1} − c_t)/c_t) = (r − ρ)/(1 + r)`, and the exact Euler equation
  gives it up to the Taylor remainder of `u'`, which is `o(c_{t+1} − c_t)`.

These are the first-order conditions as calculus. That they are necessary for optimality is
the Pontryagin maximum principle, not in Mathlib and not formalised; their sufficiency is
`Mangasarian`.
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.19), p. 248: the present-value Hamiltonian
`H(t) = e^{−ρt}u(c) + μ(ra + w − c)`. -/
noncomputable def ctHamiltonian (ρ r w : ℝ) (u : ℝ → ℝ) (t μ a c : ℝ) : ℝ :=
  Real.exp (-ρ * t) * u c + μ * (r * a + w - c)

/-- AKMM, box p. 249: the current-value Hamiltonian `Ĥ(t) = u(c) + μ̂(ra + w − c)`. -/
noncomputable def ctCurrentHamiltonian (r w : ℝ) (u : ℝ → ℝ) (μh a c : ℝ) : ℝ :=
  u c + μh * (r * a + w - c)

/-- AKMM, (9.20) and (9.24), pp. 248–249: `∂H/∂c = e^{−ρt}u'(c) − μ`, so (9.20) is
`e^{−ρt}u'(c(t)) = μ(t)`. -/
theorem eq_9_20 {ρ r w t μ a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) :
    HasDerivAt (fun x => ctHamiltonian ρ r w u t μ a x) (Real.exp (-ρ * t) * u'c - μ) c ∧
      (Real.exp (-ρ * t) * u'c - μ = 0 ↔ Real.exp (-ρ * t) * u'c = μ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h := (hu.const_mul (Real.exp (-ρ * t))).add
    (((hasDerivAt_id c).const_sub (r * a + w)).const_mul μ)
  change HasDerivAt (fun x => Real.exp (-ρ * t) * u x + μ * (r * a + w - x)) _ c
  convert h using 1
  · funext x
    simp only [Pi.add_apply, id]
  · ring

/-- AKMM, (9.21) and (9.25), pp. 248–249: `∂H/∂a = rμ`, so (9.21) `∂H/∂a + μ̇ = 0` is
`rμ(t) + μ̇(t) = 0`, i.e. `μ̇/μ = −r`. -/
theorem eq_9_21 {ρ r w t μ μdot a c : ℝ} {u : ℝ → ℝ} :
    HasDerivAt (fun x => ctHamiltonian ρ r w u t μ x c) (r * μ) a ∧
      (r * μ + μdot = 0 ↔ μdot = -r * μ) ∧ (μ ≠ 0 → (r * μ + μdot = 0 ↔ μdot / μ = -r)) := by
  refine ⟨?_, by constructor <;> intro h <;> linarith, fun hμ => ?_⟩
  · have h := ((((hasDerivAt_id a).const_mul r).add_const (w - c)).const_mul μ).const_add
      (Real.exp (-ρ * t) * u c)
    change HasDerivAt (fun x => Real.exp (-ρ * t) * u c + μ * (r * x + w - c)) _ a
    convert h using 1
    · funext x
      simp only [id]
      ring
    · ring
  · rw [div_eq_iff hμ]
    constructor <;> intro h <;> linarith

/-- AKMM, p. 248: the integration-by-parts step of the heuristic derivation, on `[0, T]`:
`∫_0^T μȧ = μ(T)a(T) − μ(0)a(0) − ∫_0^T μ̇a`, so the Lagrangian
`∫_0^T e^{−ρt}u(c) + ∫_0^T μ(ra + w − c − ȧ)` equals
`∫_0^T H − [μ(T)a(T) − μ(0)a(0)] + ∫_0^T μ̇a`. -/
theorem continuousHamiltonian_integration_by_parts {ρ r w T : ℝ} {u : ℝ → ℝ}
    {μ μ' a a' c : ℝ → ℝ} (hμ : ∀ t, HasDerivAt μ (μ' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hμ' : Continuous μ') (ha' : Continuous a')
    (hint1 : IntervalIntegrable (fun t => Real.exp (-ρ * t) * u (c t)) MeasureTheory.volume 0 T)
    (hint2 : IntervalIntegrable (fun t => μ t * (r * a t + w - c t)) MeasureTheory.volume 0 T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) +
        ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t - a' t) =
      (∫ t in (0 : ℝ)..T, ctHamiltonian ρ r w u t (μ t) (a t) (c t)) -
        (μ T * a T - μ 0 * a 0) + ∫ t in (0 : ℝ)..T, μ' t * a t := by
  have hμc : Continuous μ := continuous_iff_continuousAt.mpr fun t => (hμ t).continuousAt
  have hac : Continuous a := continuous_iff_continuousAt.mpr fun t => (ha t).continuousAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (fun t _ => hμ t) (fun t _ => ha t) (hμ'.intervalIntegrable 0 T) (ha'.intervalIntegrable 0 T)
  have hint3 : IntervalIntegrable (fun t => μ t * a' t) MeasureTheory.volume 0 T :=
    (hμc.mul ha').intervalIntegrable 0 T
  have hsplit : ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t - a' t) =
      (∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t)) - ∫ t in (0 : ℝ)..T, μ t * a' t := by
    rw [← intervalIntegral.integral_sub hint2 hint3]
    congr 1
    funext t
    ring
  have hH : ∫ t in (0 : ℝ)..T, ctHamiltonian ρ r w u t (μ t) (a t) (c t) =
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) +
        ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t) := by
    rw [← intervalIntegral.integral_add hint1 hint2]
    rfl
  rw [hsplit, hH, hibp]
  ring

/-- AKMM, box p. 249: with `μ = e^{−ρt}μ̂`, the present-value Hamiltonian is the discounted
current-value Hamiltonian, `H(t) = e^{−ρt}Ĥ(t)`. -/
theorem continuousHamiltonian_present_current (ρ r w : ℝ) (u : ℝ → ℝ) (t μh a c : ℝ) :
    ctHamiltonian ρ r w u t (Real.exp (-ρ * t) * μh) a c =
      Real.exp (-ρ * t) * ctCurrentHamiltonian r w u μh a c := by
  simp only [ctHamiltonian, ctCurrentHamiltonian]
  ring

/-- AKMM, (9.22), p. 249: with `μ = e^{−ρt}μ̂`, `∂H/∂c = e^{−ρt}∂Ĥ/∂c`, so (9.22) `∂Ĥ/∂c = 0`
is equivalent to (9.20). -/
theorem eq_9_22 {ρ r w t μh a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) :
    HasDerivAt (fun x => ctCurrentHamiltonian r w u μh a x) (u'c - μh) c ∧
      (Real.exp (-ρ * t) * u'c - Real.exp (-ρ * t) * μh = 0 ↔ u'c - μh = 0) := by
  refine ⟨?_, ?_⟩
  · have h := hu.add (((hasDerivAt_id c).const_sub (r * a + w)).const_mul μh)
    change HasDerivAt (fun x => u x + μh * (r * a + w - x)) _ c
    convert h using 1
    · funext x
      simp only [Pi.add_apply, id]
    · ring
  · rw [← mul_sub, mul_eq_zero]
    simp [(Real.exp_pos _).ne']

/-- AKMM, (9.23), p. 249: with `μ = e^{−ρt}μ̂`, `μ̇ = e^{−ρt}(μ̂' − ρμ̂)`, so
`∂H/∂a + μ̇ = e^{−ρt}(∂Ĥ/∂a + μ̂' − ρμ̂)` and (9.21) is equivalent to (9.23)
`∂Ĥ/∂a + μ̂' − ρμ̂ = 0`. -/
theorem eq_9_23 {ρ r t μh' : ℝ} {μh : ℝ → ℝ} (hμh : HasDerivAt μh μh' t) :
    HasDerivAt (fun s => Real.exp (-ρ * s) * μh s) (Real.exp (-ρ * t) * (μh' - ρ * μh t)) t ∧
      (r * (Real.exp (-ρ * t) * μh t) + Real.exp (-ρ * t) * (μh' - ρ * μh t) = 0 ↔
        r * μh t + μh' - ρ * μh t = 0) := by
  refine ⟨?_, ?_⟩
  · have he : HasDerivAt (fun s => Real.exp (-ρ * s)) (Real.exp (-ρ * t) * -ρ) t := by
      have := ((hasDerivAt_id t).const_mul (-ρ)).exp
      simpa using this
    convert he.mul hμh using 1
    ring
  · rw [show r * (Real.exp (-ρ * t) * μh t) + Real.exp (-ρ * t) * (μh' - ρ * μh t) =
      Real.exp (-ρ * t) * (r * μh t + μh' - ρ * μh t) by ring, mul_eq_zero]
    simp [(Real.exp_pos _).ne']

/-- AKMM, (9.24)–(9.26), p. 249: the continuous-time Euler equation, for a possibly time-varying
interest rate. If `μ(s) = e^{−ρs}u'(c(s))` near `t` (9.24), `r(t)μ(t) + μ̇(t) = 0` (9.25), and
`u'` has derivative `u''(c(t))` at `c(t)`, then `−ρ + (u''(c)/u'(c))ċ = μ̇/μ = −r` (the growth
trick (9.5)) and `−(u''(c)c/u'(c))(ċ/c) = r − ρ`. -/
theorem eq_9_26 {ρ r t cdot μdot u''c : ℝ} {c μ u' : ℝ → ℝ} (hc : HasDerivAt c cdot t)
    (hu' : HasDerivAt u' u''c (c t)) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * u' (c s))
    (hμd : HasDerivAt μ μdot t) (h925 : r * μ t + μdot = 0) (hpos : u' (c t) ≠ 0)
    (hc0 : c t ≠ 0) :
    μdot = Real.exp (-ρ * t) * (-ρ * u' (c t) + u''c * cdot) ∧
      -ρ + u''c / u' (c t) * cdot = μdot / μ t ∧ μdot / μ t = -r ∧
      -(u''c * c t / u' (c t)) * (cdot / c t) = r - ρ := by
  have he : HasDerivAt (fun s => Real.exp (-ρ * s)) (Real.exp (-ρ * t) * -ρ) t := by
    have := ((hasDerivAt_id t).const_mul (-ρ)).exp
    simpa using this
  have hcomp : HasDerivAt (fun s => Real.exp (-ρ * s) * u' (c s))
      (Real.exp (-ρ * t) * -ρ * u' (c t) + Real.exp (-ρ * t) * (u''c * cdot)) t :=
    he.mul (hu'.comp t hc)
  have hμt : μ t = Real.exp (-ρ * t) * u' (c t) := hμ.eq_of_nhds
  have h1 : μdot = Real.exp (-ρ * t) * (-ρ * u' (c t) + u''c * cdot) := by
    rw [hμd.unique (hcomp.congr_of_eventuallyEq hμ)]
    ring
  have hE := (Real.exp_pos (-ρ * t)).ne'
  have hμ0 : μ t ≠ 0 := by rw [hμt]; exact mul_ne_zero hE hpos
  have h2 : -ρ + u''c / u' (c t) * cdot = μdot / μ t := by
    rw [h1, hμt]
    field_simp
  have h3 : μdot / μ t = -r := by
    rw [div_eq_iff hμ0]
    linarith
  refine ⟨h1, h2, h3, ?_⟩
  have h4 : u''c / u' (c t) * cdot = ρ - r := by linarith
  calc -(u''c * c t / u' (c t)) * (cdot / c t) = -(u''c / u' (c t) * cdot) := by
        field_simp
    _ = r - ρ := by rw [h4]; ring

/-- AKMM, p. 249: the coefficient of relative risk aversion `−u''(c)c/u'(c)` is positive when
`u'' < 0`, `c > 0` and `u' > 0`. -/
theorem continuousHamiltonian_crra_coefficient_pos {c u'c u''c : ℝ} (hc : 0 < c)
    (hu' : 0 < u'c) (hu'' : u''c < 0) : 0 < -(u''c * c / u'c) := by
  have : u''c * c / u'c < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hu'' hc) hu'
  linarith

/-- AKMM, p. 249 (Section 4.2.4): CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`, `σ ≠ 1`. -/
noncomputable def crraUtility (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, p. 249: for CRRA utility and `c > 0`, `u'(c) = c^{−σ}` and `u''(c) = −σc^{−σ−1}`. -/
theorem continuousHamiltonian_crra_derivs {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (crraUtility σ) (c ^ (-σ)) c ∧
      HasDerivAt (fun x : ℝ => x ^ (-σ)) (-σ * c ^ (-σ - 1)) c := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  refine ⟨?_, ?_⟩
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
      (1 - σ)
    convert h using 1
    · rfl
    · rw [show 1 - σ - 1 = -σ by ring]
      field_simp
  · exact Real.hasDerivAt_rpow_const (Or.inl hc.ne')

/-- AKMM, p. 249: for CRRA utility the coefficient of relative risk aversion is constant,
`−u''(c)c/u'(c) = σ`. -/
theorem continuousHamiltonian_crra_relative_risk_aversion {σ c : ℝ} (hc : 0 < c) :
    -((-σ * c ^ (-σ - 1)) * c / c ^ (-σ)) = σ := by
  have hpos : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have hsplit : c ^ (-σ - 1) * c = c ^ (-σ) := by
    rw [Real.rpow_sub_one hc.ne']
    field_simp
  rw [mul_assoc, hsplit]
  field_simp

/-- AKMM, box p. 250: replacing `u'(c_{t+1})` by its first-order expansion
`u'(c_t) + u''(c_t)(c_{t+1} − c_t)` in the Euler equation (9.14) with `β = 1/(1 + ρ)` gives
`−(u''(c_t)c_t/u'(c_t))((c_{t+1} − c_t)/c_t) = (r − ρ)/(1 + r)`. -/
theorem continuousHamiltonian_discrete_euler_linearized {r ρ c dc u'c u''c : ℝ}
    (hρ : 1 + ρ ≠ 0) (hr : 1 + r ≠ 0) (hu' : u'c ≠ 0) (hc : c ≠ 0)
    (heuler : u'c = 1 / (1 + ρ) * (1 + r) * (u'c + u''c * dc)) :
    -(u''c * c / u'c) * (dc / c) = (r - ρ) / (1 + r) := by
  field_simp at heuler ⊢
  linarith

/-- AKMM, box p. 250, with the remainder: if `u'(c_t) = β(1 + r)u'(c_t + Δ)` exactly, with
`β = 1/(1 + ρ)`, then
`−(u''(c_t)c_t/u'(c_t))(Δ/c_t) = (r − ρ)/(1 + r) + E(Δ)/u'(c_t)`, where the Taylor remainder
`E(Δ) = u'(c_t + Δ) − u'(c_t) − u''(c_t)Δ` is `o(Δ)` as `Δ → 0`. -/
theorem continuousHamiltonian_discrete_euler_remainder {r ρ c dc u''c : ℝ} {u' : ℝ → ℝ}
    (hρ : 1 + ρ ≠ 0) (hr : 1 + r ≠ 0) (hu' : u' c ≠ 0) (hc : c ≠ 0)
    (hd : HasDerivAt u' u''c c) (heuler : u' c = 1 / (1 + ρ) * (1 + r) * u' (c + dc)) :
    -(u''c * c / u' c) * (dc / c) =
        (r - ρ) / (1 + r) + (u' (c + dc) - u' c - u''c * dc) / u' c ∧
      (fun x => u' (c + x) - u' c - u''c * x) =o[𝓝 0] fun x => x := by
  refine ⟨?_, ?_⟩
  · have key : u' (c + dc) = (1 + ρ) / (1 + r) * u' c := by
      field_simp at heuler ⊢
      linarith
    rw [key]
    field_simp
    ring
  · have h := hd.isLittleO
    have hc' : Tendsto (fun x : ℝ => c + x) (𝓝 0) (𝓝 c) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add c
    have := h.comp_tendsto hc'
    refine this.congr (fun x => ?_) (fun x => ?_)
    · simp [smul_eq_mul, mul_comm]
    · simp

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Mangasarian–Arrow sufficiency in the book's setting

AKMM, §9.2 (pp. 246–249) and §9.3.2 (pp. 253–255). The book uses the first-order conditions
of the maximum principle as if they characterized the optimum. Mathlib has no Pontryagin
maximum principle, so their necessity is not formalised. Their sufficiency (Mangasarian 1966,
Arrow) is proved here, for the class of problems of Chapter 9:
`max ∫_0^∞ e^{−ρt}u(c(t))dt` subject to `ẋ = G(t, x) − c`, with `u` concave and `G(t, ·)`
concave.

* `mangasarian`: if a path satisfies the state equation, the costate equation
  `μ̇ = −μ ∂G/∂x` ((9.21)/(9.25)/(9.A.2)), the first-order condition `μ = e^{−ρt}u'(c)`
  ((9.20)/(9.24)/(9.A.1)) with `μ ≥ 0`, then for every competitor from the same initial state,
  `∫_0^T e^{−ρt}u(c') ≤ ∫_0^T e^{−ρt}u(c) + μ(T)(x(T) − x'(T))`. The proof differentiates
  `∫_0^t e^{−ρs}(u(c') − u(c)) + μ(t)(x'(t) − x(t))` and shows it is nonincreasing.
* `mangasarian_catching_up`: if the terminal term is eventually at most any `δ > 0`, the path
  is catching-up optimal, and its welfare is the largest whenever welfare limits exist.
* `mangasarian_consumption_saving`: the household problem (9.16)–(9.17): (9.24), (9.25) and the
  TVC `lim e^{−ρT}u'(c(T))a(T) = 0` imply catching-up optimality against every path satisfying
  the nPg (9.17); instance `mangasarian_consumption_saving_constant` (`r = ρ`).
* `mangasarian_planner`: the planner's problem (9.33): the conditions of p. 254 and the TVC
  (9.34) imply catching-up optimality against every path with `k ≥ 0`; instance
  `mangasarian_planner_steady_state` (the modified-golden-rule steady state is optimal).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- `e^{−ρT} → 0` as `T → ∞` for `ρ > 0`. -/
theorem mangasarian_exp_neg_tendsto {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun T : ℝ => Real.exp (-ρ * T)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hρ)
  refine h.congr fun T => ?_
  simp [neg_mul]

/-- **Mangasarian–Arrow sufficiency, finite horizon** (AKMM, §9.2, pp. 248–249, for the
problems of Chapter 9). Let `u` be concave on `(0, ∞)` with derivative `u'`, and let the
candidate `(x, c)` and costate `μ ≥ 0` satisfy, for `t ≥ 0`, `ẋ = G(t, x) − c`,
`μ̇ = −μ G_x(t, x)` and `μ = e^{−ρt}u'(c)`. If the competitor `(x', c')` has the same initial
state, positive continuous consumption, `ẋ' = G(t, x') − c'`, and
`G(t, x') ≤ G(t, x) + G_x(t, x)(x' − x)` (concavity of `G(t, ·)`), then for every `T ≥ 0`
`∫_0^T e^{−ρt}u(c') ≤ ∫_0^T e^{−ρt}u(c) + μ(T)(x(T) − x'(T))`. -/
theorem mangasarian {ρ : ℝ} {u u' : ℝ → ℝ} {G Gx : ℝ → ℝ → ℝ} {x c μ x' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (G t (x t) - c t) t)
    (hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * Gx t (x t))) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t)) (hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (G t (x' t) - c' t) t) (h0 : x' 0 = x 0)
    (hG : ∀ t, 0 ≤ t → G t (x' t) ≤ G t (x t) + Gx t (x t) * (x' t - x t))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + μ T * (x T - x' T) := by
  have hucont : ContinuousOn u (Set.Ioi 0) := fun y hy =>
    (hu y hy).continuousAt.continuousWithinAt
  have hE : Continuous fun t : ℝ => Real.exp (-ρ * t) := by fun_prop
  have huc : ContinuousOn (fun t => Real.exp (-ρ * t) * u (c t)) (Set.Ici 0) :=
    hE.continuousOn.mul (hucont.comp hcc fun t ht => hc t ht)
  have huc' : ContinuousOn (fun t => Real.exp (-ρ * t) * u (c' t)) (Set.Ici 0) :=
    hE.continuousOn.mul (hucont.comp hcc' fun t ht => hc' t ht)
  set f : ℝ → ℝ := fun t => Real.exp (-ρ * t) * u (c' t) - Real.exp (-ρ * t) * u (c t)
  have hf : ContinuousOn f (Set.Ici 0) := huc'.sub huc
  have hsub : ∀ s : ℝ, 0 ≤ s → Set.uIcc 0 s ⊆ Set.Ici 0 := fun s hs => by
    rw [Set.uIcc_of_le hs]
    exact Set.Icc_subset_Ici_self
  have hint : ∀ s : ℝ, 0 ≤ s → IntervalIntegrable f MeasureTheory.volume 0 s := fun s hs =>
    (hf.mono (hsub s hs)).intervalIntegrable
  set Φ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, f s) + μ t * (x' t - x t)
  have hD : ∀ t, 0 < t → HasDerivAt Φ (f t + (-(μ t * Gx t (x t)) * (x' t - x t) +
      μ t * ((G t (x' t) - c' t) - (G t (x t) - c t)))) t := by
    intro t ht
    have hfo : ContinuousOn f (Set.Ioi 0) := hf.mono Set.Ioi_subset_Ici_self
    have h1 := intervalIntegral.integral_hasDerivAt_right (hint t ht.le)
      (hfo.stronglyMeasurableAtFilter isOpen_Ioi t ht)
      (hfo.continuousAt (Ioi_mem_nhds ht))
    exact h1.add ((hμ t ht.le).mul ((hx' t ht.le).sub (hx t ht.le)))
  have hneg : ∀ t, 0 < t → f t + (-(μ t * Gx t (x t)) * (x' t - x t) +
      μ t * ((G t (x' t) - c' t) - (G t (x t) - c t))) ≤ 0 := by
    intro t ht
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ioi.mpr (hc t ht.le))
      (Set.mem_Ioi.mpr (hc' t ht.le)) (hu (c t) (hc t ht.le))
    have hE0 := (Real.exp_pos (-ρ * t)).le
    have hfle : f t ≤ μ t * (c' t - c t) := by
      simp only [f]
      rw [hfoc t ht.le, ← mul_sub, mul_assoc]
      exact mul_le_mul_of_nonneg_left hs hE0
    have hGt := mul_le_mul_of_nonneg_left (hG t ht.le) (hμ0 t ht.le)
    nlinarith
  have hanti : AntitoneOn Φ (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · have hprim := intervalIntegral.continuousOn_primitive_interval' (hint T hT)
        (Set.left_mem_uIcc (a := (0 : ℝ)) (b := T))
      rw [Set.uIcc_of_le hT] at hprim
      refine hprim.add fun t ht => ?_
      exact (((hμ t ht.1).mul ((hx' t ht.1).sub (hx t ht.1))).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hD t ht.1).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hD t ht.1).deriv]
      exact hneg t ht.1
  have hle := hanti (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  simp only [Φ, intervalIntegral.integral_same, zero_add, h0, sub_self, mul_zero] at hle
  have hsplit : ∫ s in (0 : ℝ)..T, f s = (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) -
      ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t) :=
    intervalIntegral.integral_sub ((huc'.mono (hsub T hT)).intervalIntegrable)
      ((huc.mono (hsub T hT)).intervalIntegrable)
  rw [hsplit] at hle
  linarith

/-- **Mangasarian–Arrow sufficiency, infinite horizon**: under the hypotheses of `mangasarian`,
if the terminal term `μ(T)(x(T) − x'(T))` is eventually at most any `δ > 0`, the candidate is
catching-up optimal against the competitor, and if both welfare integrals converge, the
competitor's welfare is at most the candidate's. -/
theorem mangasarian_catching_up {ρ : ℝ} {u u' : ℝ → ℝ} {G Gx : ℝ → ℝ → ℝ}
    {x c μ x' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (G t (x t) - c t) t)
    (hμ : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * Gx t (x t))) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t)) (hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t)
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (hx' : ∀ t, 0 ≤ t → HasDerivAt x' (G t (x' t) - c' t) t) (h0 : x' 0 = x 0)
    (hG : ∀ t, 0 ≤ t → G t (x' t) ≤ G t (x t) + Gx t (x t) * (x' t - x t))
    (hterm : ∀ δ > 0, ∀ᶠ T in atTop, μ T * (x T - x' T) ≤ δ) :
    (∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ) ∧
    ∀ J J' : ℝ, Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) atTop (𝓝 J) →
      Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) atTop (𝓝 J') →
      J' ≤ J := by
  have hcu : ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ := by
    intro δ hδ
    filter_upwards [hterm δ hδ, eventually_ge_atTop (0 : ℝ)] with T h1 h2
    linarith [mangasarian hconc hu hc hcc hx hμ hfoc hμ0 hc' hcc' hx' h0 hG h2]
  refine ⟨hcu, fun J J' hJ hJ' => ?_⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  exact le_of_tendsto_of_tendsto hJ' (hJ.add_const δ) (hcu δ hδ)

/-- **Sufficiency for the consumption–saving problem** (AKMM, (9.16)–(9.17), (9.24)–(9.25),
pp. 246–249). If `u` is concave with `u' ≥ 0`, and the candidate satisfies `ȧ = w + ra − c`,
(9.24) `μ = e^{−ρt}u'(c)`, (9.25) `rμ + μ̇ = 0`, and the TVC `lim e^{−ρT}u'(c(T))a(T) = 0`,
then it is catching-up optimal against every path from `a(0)` with positive continuous
consumption that satisfies the nPg (9.17), stated as `liminf e^{−rT}a'(T) ≥ 0`. -/
theorem mangasarian_consumption_saving {ρ r w : ℝ} {u u' : ℝ → ℝ} {a c μ a' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (w + r * a t - c t) t)
    (h924 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h925 : ∀ t, 0 ≤ t → HasDerivAt μ (-r * μ t) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * a T) atTop (𝓝 0))
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (w + r * a' t - c' t) t) (h0 : a' 0 = a 0)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-r * T) * a' T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + δ := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [h924 t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  have hμexp : ∀ T, 0 ≤ T → μ T = Real.exp (-r * T) * μ 0 := fun T hT =>
    SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt rfl h925 hT
  refine (mangasarian_catching_up (G := fun _ y => r * y + w) (Gx := fun _ _ => r) hconc hu hc
    hcc (fun t ht => by convert ha t ht using 1; ring) (fun t ht => by
      convert h925 t ht using 1; ring) h924 hμ0 hc' hcc'
    (fun t ht => by convert ha' t ht using 1; ring) h0 (fun t _ => by ring_nf; rfl) ?_).1
  intro δ hδ
  set K := μ 0
  have hK : 0 ≤ K := hμ0 0 le_rfl
  set η := δ / (2 * (K + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  have htvc' : Tendsto (fun T => μ T * a T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [h924 T hT]
  filter_upwards [hnpg η hη, htvc'.eventually (gt_mem_nhds (half_pos hδ)),
    eventually_ge_atTop (0 : ℝ)] with T h1 h2 hT
  have e : μ T * a' T = K * (Real.exp (-r * T) * a' T) := by rw [hμexp T hT]; ring
  have h3 : -(K * η) ≤ μ T * a' T := by
    rw [e]; nlinarith
  have hKη : K * η ≤ δ / 2 := by
    have e2 : K * η = δ / 2 * (K / (K + 1)) := by
      simp only [η]; field_simp
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  nlinarith

/-- AKMM, §9.2, an instance of `mangasarian_consumption_saving`: with `r = ρ > 0`, keeping the
asset constant, `a(t) = a_0`, `c(t) = w + ra_0 > 0`, satisfies (9.24), (9.25) and the TVC, so it
is catching-up optimal against every path from `a_0` satisfying the nPg. -/
theorem mangasarian_consumption_saving_constant {ρ w a₀ : ℝ} {u u' : ℝ → ℝ} (hρ : 0 < ρ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y) (hc0 : 0 < w + ρ * a₀) {a' c' : ℝ → ℝ}
    (hc' : ∀ t, 0 ≤ t → 0 < c' t) (hcc' : ContinuousOn c' (Set.Ici 0))
    (ha' : ∀ t, 0 ≤ t → HasDerivAt a' (w + ρ * a' t - c' t) t) (h0 : a' 0 = a₀)
    (hnpg : ∀ η > 0, ∀ᶠ T in atTop, -η ≤ Real.exp (-ρ * T) * a' T) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (w + ρ * a₀)) + δ := by
  have hd : ∀ t, HasDerivAt (fun s => Real.exp (-ρ * s) * u' (w + ρ * a₀))
      (-ρ * (Real.exp (-ρ * t) * u' (w + ρ * a₀))) t := fun t =>
    SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-ρ) _ t
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (w + ρ * a₀) * a₀) atTop (𝓝 0) := by
    have := ((mangasarian_exp_neg_tendsto hρ).mul_const (u' (w + ρ * a₀))).mul_const a₀
    simpa using this
  exact mangasarian_consumption_saving (a := fun _ => a₀) (c := fun _ => w + ρ * a₀)
    (μ := fun s => Real.exp (-ρ * s) * u' (w + ρ * a₀)) hconc hu hu'0 (fun _ _ => hc0)
    continuousOn_const (fun t _ => by simpa using hasDerivAt_const t a₀)
    (fun _ _ => rfl) (fun t _ => hd t) htvc hc' hcc' ha' h0 hnpg

/-- **Sufficiency for the planner's problem** (AKMM, (9.33)–(9.34), pp. 253–254, and (9.A.1)–
(9.A.2), p. 846). Let `f` be concave on `[0, ∞)` with derivative `f'` along the candidate, `u`
concave with `u' ≥ 0`. If the candidate has positive capital and consumption,
`k̇ = f(k) − δk − c`, `μ = e^{−ρt}u'(c)` (9.A.1), `μ̇ = −μ(f'(k) − δ)` (9.A.2), and the TVC
(9.34) `lim e^{−ρT}u'(c(T))k(T) = 0`, then it is catching-up optimal against every path from
`k(0)` with `k' ≥ 0` and positive continuous consumption; disinvestment is allowed. -/
theorem mangasarian_planner {ρ δ : ℝ} {f f' u u' : ℝ → ℝ} {k c μ k' c' : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y) (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hk : ∀ t, 0 ≤ t → 0 < k t) (hfd : ∀ t, 0 ≤ t → HasDerivAt f (f' (k t)) (k t))
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (f' (k t) - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0))
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) (h0 : k' 0 = k 0) :
    (∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε) ∧
    ∀ J J' : ℝ, Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) atTop (𝓝 J) →
      Tendsto (fun T => ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t)) atTop (𝓝 J') →
      J' ≤ J := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [h9A1 t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  have hG : ∀ t, 0 ≤ t → f (k' t) - δ * k' t ≤
      f (k t) - δ * k t + (f' (k t) - δ) * (k' t - k t) := fun t ht => by
    have hs := RamseyCassKoopmans.concave_support hf (Set.mem_Ici.mpr (hk t ht).le)
      (Set.mem_Ici.mpr (hk' t ht)) (hfd t ht)
    nlinarith
  refine mangasarian_catching_up (G := fun _ y => f y - δ * y) (Gx := fun t _ => f' (k t) - δ)
    hconc hu hc hcc hkd h9A2 h9A1 hμ0 hc' hcc' hkd' h0 hG ?_
  intro ε hε
  have htvc' : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [h9A1 T hT]
  filter_upwards [htvc'.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, §9.3.2, p. 255 and fn. 3, an instance of `mangasarian_planner`: at the modified golden
rule `f'(k**) = δ + ρ` with `ρ > 0` and `c** = f(k**) − δk** > 0`, the steady state satisfies
(9.33), (9.A.1), (9.A.2) and the TVC (9.34), so it is optimal from `k(0) = k**` against every
path with `k ≥ 0`. -/
theorem mangasarian_planner_steady_state {ρ δ kss : ℝ} {f u u' : ℝ → ℝ} (hρ : 0 < ρ)
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y) (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hkss : 0 < kss) (hfd : HasDerivAt f (δ + ρ) kss) (hcss : 0 < f kss - δ * kss)
    {k' c' : ℝ → ℝ} (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) (h0 : k' 0 = kss) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (f kss - δ * kss)) + ε := by
  set css := f kss - δ * kss
  have hd : ∀ t, HasDerivAt (fun s => Real.exp (-ρ * s) * u' css)
      (-(Real.exp (-ρ * t) * u' css * (δ + ρ - δ))) t := fun t => by
    convert SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-ρ) (u' css) t using 1
    ring
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' css * kss) atTop (𝓝 0) := by
    have := ((mangasarian_exp_neg_tendsto hρ).mul_const (u' css)).mul_const kss
    simpa using this
  exact (mangasarian_planner (f' := fun _ => δ + ρ) (k := fun _ => kss) (c := fun _ => css)
    (μ := fun s => Real.exp (-ρ * s) * u' css) hf hconc hu hu'0 (fun _ _ => hkss)
    (fun _ _ => hfd) (fun _ _ => hcss) continuousOn_const
    (fun t _ => by simpa [css] using hasDerivAt_const t kss) (fun _ _ => rfl)
    (fun t _ => hd t) htvc hk' hc' hcc' hkd' h0).1

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Solow model in continuous time

AKMM, §9.3.1 (pp. 251–253): (9.27)–(9.32), Figure 9.1 and the balanced growth path.

* (9.31): the growth rate of `k̃ = K/(AL)` is `K̇/K − Ȧ/A − L̇/L` (`eq_9_31`).
* With constant returns, (9.27)–(9.30) give `k̃̇/k̃ = (sF − δK)/K − γ − n`, `F(K, AL)/(AL) = f(k̃)`
  and (9.32) `k̃̇ = sf(k̃) − (δ + γ + n)k̃` (`solowContinuous_intensive`, `eq_9_32`), the latter
  by EconomicGrowth's `hasDerivAt_capitalPerEffectiveWorker`.
* Figure 9.1: a unique positive steady state `k̃̄`, `k̃̇ > 0` below it and `k̃̇ < 0` above it, and
  global monotone convergence from every `k̃(0) > 0`, for the economy's actual `k̃(t)`
  (`solowContinuous_phase_line`, `solowContinuous_convergence`), from EconomicGrowth's
  `general_solow` and `effective_labour_convergence` with `m = δ + γ + n`.
* The balanced growth path: `Y/L = f(k̃)A`; on the steady state `Y/L` grows at exactly `γ`, and
  along every path its growth rate tends to `γ` (`solowContinuous_income_per_capita_growth`).
-/

namespace AKMM.ContinuousTime

open Filter Topology Solow1956.Neoclassical

/-- AKMM, (9.31), p. 251: for positive differentiable `K, A, L`, the growth rate of
`k̃ = K/(AL)` is `K̇/K − Ȧ/A − L̇/L`. -/
theorem eq_9_31 {K A L : ℝ → ℝ} {K' A' L' t : ℝ} (hK : HasDerivAt K K' t)
    (hA : HasDerivAt A A' t) (hL : HasDerivAt L L' t) (hK0 : 0 < K t) (hA0 : 0 < A t)
    (hL0 : 0 < L t) :
    HasDerivAt (fun s => K s / (A s * L s))
      (K t / (A t * L t) * (K' / K t - A' / A t - L' / L t)) t := by
  have hAL : A t * L t ≠ 0 := (mul_pos hA0 hL0).ne'
  convert hK.div (hA.mul hL) hAL using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- AKMM, p. 252: with constant returns `F(λK, λN) = λF(K, N)` and `f(k) = F(k, 1)`,
`F(K, AL)/(AL) = f(K/(AL))`; and from (9.27)–(9.30), (9.31) reads
`k̃̇/k̃ = (sF(K, AL) − δK)/K − γ − n = sf(k̃)/k̃ − (δ + γ + n)`. -/
theorem solowContinuous_intensive {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K E s δ γ n : ℝ}
    (hK : 0 < K) (hE : 0 < E) :
    F K E / E = F (K / E) 1 ∧
      (s * F K E - δ * K) / K - γ - n = s * F (K / E) 1 / (K / E) - (δ + γ + n) := by
  have h1 : F K E = E * F (K / E) 1 := by
    have := hcrs E hE (K / E) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
    exact this
  refine ⟨by rw [h1]; field_simp, ?_⟩
  rw [h1]
  field_simp
  ring

/-- AKMM, (9.27)–(9.32), pp. 251–252: if `L̇ = nL`, `Ȧ = γA`, `K̇ = sF(K, AL) − δK` with
constant returns, then `k̃ = K/(AL)` satisfies (9.32): `k̃̇ = sf(k̃) − (δ + γ + n)k̃`. -/
theorem eq_9_32 {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K A L : ℝ → ℝ}
    {s δ γ n t : ℝ} (hA0 : 0 < A t) (hL0 : 0 < L t)
    (h927 : HasDerivAt L (n * L t) t) (h928 : HasDerivAt A (γ * A t) t)
    (h929 : HasDerivAt K (s * F (K t) (A t * L t) - δ * K t) t) :
    HasDerivAt (fun u => K u / (A u * L u))
      (s * F (K t / (A t * L t)) 1 - (δ + γ + n) * (K t / (A t * L t))) t := by
  have hE : 0 < A t * L t := mul_pos hA0 hL0
  have hEd : HasDerivAt (fun u => A u * L u) ((n + γ) * (A t * L t)) t := by
    convert h928.mul h927 using 1
    ring
  have hY : F (K t) (A t * L t) = A t * L t * F (K t / (A t * L t)) 1 := by
    have := hcrs (A t * L t) hE (K t / (A t * L t)) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
    exact this
  have h := Solow1956.SolowSwan.hasDerivAt_capitalPerEffectiveWorker (f := fun k => F k 1)
    (E := fun u => A u * L u) hE h929 hEd hY
  convert h using 1
  ring

/-- AKMM, Figure 9.1, pp. 252–253: for a neoclassical intensive technology, `s > 0` and
`δ + γ + n > 0`, (9.32) has a unique positive steady state `k̃̄`; the right side of (9.32) is
positive below it and negative above it; and from every `k̃(0) > 0` the solution exists, is
unique, stays positive and converges monotonically to `k̃̄`. -/
theorem solowContinuous_phase_line {f : ℝ → ℝ} (h : Technology f) {s δ γ n k₀ : ℝ}
    (hs : 0 < s) (hm : 0 < δ + γ + n) (hk₀ : 0 < k₀) :
    ∃ kbar : ℝ, 0 < kbar ∧ s * f kbar - (δ + γ + n) * kbar = 0 ∧
      (∀ k, 0 < k → s * f k - (δ + γ + n) * k = 0 → k = kbar) ∧
      (∀ k, 0 < k → k < kbar → 0 < s * f k - (δ + γ + n) * k) ∧
      (∀ k, kbar < k → s * f k - (δ + γ + n) * k < 0) ∧
      ∃ k : ℝ → ℝ, k 0 = k₀ ∧
        (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (s * f (k t) - (δ + γ + n) * k t) t) ∧
        (k₀ < kbar → StrictMonoOn k (Set.Ici 0)) ∧ (kbar < k₀ → StrictAntiOn k (Set.Ici 0)) ∧
        Tendsto k atTop (𝓝 kbar) ∧
        (∀ l : ℝ → ℝ, l 0 = k₀ → (∀ t, 0 ≤ t → 0 ≤ l t) →
          (∀ t, 0 ≤ t → HasDerivAt l (s * f (l t) - (δ + γ + n) * l t) t) →
            Set.EqOn l k (Set.Ici 0)) := by
  obtain ⟨ks, hks, he, hu, k, h0, hk, hlow, hhigh, _, _, hlim, huniq⟩ :=
    general_solow h hs hm hk₀
  refine ⟨ks, hks, he, hu, fun x hx hlt => rate_pos_below h hs hx hlt he,
    fun x hlt => rate_neg_above h hs hks hlt he, k, h0, hk, fun hlt => (hlow hlt).1,
    fun hlt => (hhigh hlt).1, hlim, huniq⟩

/-- AKMM, pp. 252–253: convergence of the economy itself. If the aggregates satisfy
(9.27)–(9.30) with constant returns, `K(0) > 0`, `K ≥ 0`, and the intensive form `f(k) = F(k, 1)`
is neoclassical, then capital per effective worker `K/(AL)` converges to the steady state of
(9.32), whatever its initial value. -/
theorem solowContinuous_convergence {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (h : Technology fun k => F k 1) {K A L : ℝ → ℝ} {s δ γ n : ℝ} (hs : 0 < s)
    (hm : 0 < n + γ + δ) (hK0 : 0 < K 0) (hK : ∀ t, 0 ≤ t → 0 ≤ K t)
    (hA0 : ∀ t, 0 ≤ t → 0 < A t) (hL0 : ∀ t, 0 ≤ t → 0 < L t)
    (h927 : ∀ t, 0 ≤ t → HasDerivAt L (n * L t) t) (h928 : ∀ t, 0 ≤ t → HasDerivAt A (γ * A t) t)
    (h929 : ∀ t, 0 ≤ t → HasDerivAt K (s * F (K t) (A t * L t) - δ * K t) t) :
    Tendsto (fun t => K t / (A t * L t)) atTop (𝓝 (steadyCapital h s (n + γ + δ))) := by
  refine effective_labour_convergence h (E := fun t => A t * L t)
    (Y := fun t => F (K t) (A t * L t)) hs hm hK0 hK (fun t ht => mul_pos (hA0 t ht) (hL0 t ht))
    h929 (fun t ht => by convert (h928 t ht).mul (h927 t ht) using 1; ring) (fun t ht => ?_)
  have hE := mul_pos (hA0 t ht) (hL0 t ht)
  have := hcrs (A t * L t) hE (K t / (A t * L t)) 1
  rw [mul_div_cancel₀ _ hE.ne', mul_one] at this
  exact this

/-- AKMM, p. 253: income per capita is `Y/L = F(K, AL)/L = f(k̃)A`. On the steady state
(`k̃` constant) it grows at exactly the rate `γ` of technology; along every path converging to
the steady state `k̃̄ > 0` with `k̃̇ = sf(k̃) − (δ + γ + n)k̃`, its growth rate
`γ + f'(k̃)k̃̇/f(k̃)` tends to `γ`. -/
theorem solowContinuous_income_per_capita_growth {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (h : Technology fun k => F k 1) {K A L k : ℝ → ℝ} {s δ γ n kbar : ℝ}
    (hA0 : ∀ t, 0 < A t) (hL0 : ∀ t, 0 < L t) (hk : ∀ t, 0 < k t) (hkbar : 0 < kbar)
    (hss : s * F kbar 1 - (δ + γ + n) * kbar = 0)
    (hA : ∀ t, HasDerivAt A (γ * A t) t)
    (hkd : ∀ t, HasDerivAt k (s * F (k t) 1 - (δ + γ + n) * k t) t)
    (hlim : Tendsto k atTop (𝓝 kbar)) :
    (∀ t, 0 < K t → K t / (A t * L t) = k t → F (K t) (A t * L t) / L t = F (k t) 1 * A t) ∧
      (∀ t, HasDerivAt (fun u => Real.log (F (k u) 1 * A u))
        (deriv (fun x => F x 1) (k t) * (s * F (k t) 1 - (δ + γ + n) * k t) / F (k t) 1 + γ) t) ∧
      (∀ t, HasDerivAt (fun u => Real.log (F kbar 1 * A u)) γ t) ∧
      Tendsto (fun t => deriv (fun x => F x 1) (k t) * (s * F (k t) 1 - (δ + γ + n) * k t) /
        F (k t) 1 + γ) atTop (𝓝 γ) := by
  refine ⟨fun t hK hkt => ?_, fun t => ?_, fun t => ?_, ?_⟩
  · have hE := mul_pos (hA0 t) (hL0 t)
    have h1 := hcrs (A t * L t) hE (K t / (A t * L t)) 1
    rw [mul_div_cancel₀ _ hE.ne', mul_one] at h1
    rw [h1, ← hkt]
    field_simp [(hL0 t).ne']
  · have hfk := ((h.differentiable (k t) (hk t)).hasDerivAt).comp t (hkd t)
    have hy := (hfk.mul (hA t)).log (mul_pos (h.output_pos (hk t)) (hA0 t)).ne'
    convert hy using 1
    · rfl
    · have := (h.output_pos (hk t)).ne'
      have := (hA0 t).ne'
      simp only [Function.comp, Pi.mul_apply]
      field_simp
  · have hy := ((hA t).const_mul (F kbar 1)).log (mul_pos (h.output_pos hkbar) (hA0 t)).ne'
    convert hy using 1
    have := (h.output_pos hkbar).ne'
    have := (hA0 t).ne'
    field_simp
  · have hev : ∀ᶠ t in atTop, k t ∈ Set.Ioi 0 := Eventually.of_forall fun t => hk t
    have hk' : Tendsto k atTop (𝓝[Set.Ioi 0] kbar) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, hev⟩
    have hd := ((h.derivative_continuous kbar hkbar).tendsto).comp hk'
    have hf := ((h.differentiable kbar hkbar).continuousAt.tendsto).comp hlim
    have hr : Tendsto (fun t => s * F (k t) 1 - (δ + γ + n) * k t) atTop
        (𝓝 (s * F kbar 1 - (δ + γ + n) * kbar)) :=
      (hf.const_mul s).sub (hlim.const_mul _)
    rw [hss] at hr
    have := ((hd.mul hr).div hf (h.output_pos hkbar).ne').add_const γ
    simpa using this

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The neoclassical growth model in continuous time: the planner

AKMM, §9.3.2 (pp. 253–255) and Appendix 9.A.4 (pp. 846–848).

* (9.35): with CRRA utility the first-order conditions give `ċ/c = (f'(k) − (δ + ρ))/σ`
  (`eq_9_35`, from `eq_9_26` with `r = f'(k) − δ`).
* Figure 9.2: `k̇ > 0` iff `c < f(k) − δk`, and `ċ > 0` iff `k < k**`
  (`ramseyPlanner_phase_signs`); the modified golden rule `f'(k**) = δ + ρ` has a unique
  positive solution, below the golden rule `f'(k_gold) = δ`, which maximizes steady-state
  consumption (footnote 3; `ramseyPlanner_modified_golden_rule`, from EconomicGrowth's
  `existsUnique_stationary_capital_of_inada`, `stationary_capital_lt_golden_rule_of_strictConcave`
  and `golden_rule_strictly_maximizes_consumption`).
* A path converging to the steady state satisfies the TVC (9.34)
  (`ramseyPlanner_tvc_of_convergent`); a path reaching `k = 0` with positive consumption becomes
  infeasible immediately (`ramseyPlanner_zero_capital_infeasible`).
* Appendix 9.A.4: from (9.A.1)–(9.A.2), (9.A.3)–(9.A.4)
  `u'(c(T)) = u'(c(0))exp(−∫_0^T (f'(k) − (δ + ρ)))` and (9.A.5) ⇔ (9.A.6)
  (`appendix_9A4_marginal_utility`, `appendix_9A4_tvc_iff`); on the saddle path
  `∫_0^T (f'(k) − δ) → ∞` and (9.A.6) holds (`appendix_9A4_saddle_tvc`); a path that enters
  the region `f'(k) < δ` for good while `k` stays away from zero violates it
  (`appendix_9A4_below_saddle_violates_tvc`, instance `appendix_9A4_below_saddle_instance`).
  That a path starting below the saddle path does enter that region is read off the phase
  diagram in the book and is not formalised (figure claim).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.35), p. 254: with CRRA utility (`u'(c) = c^{−σ}`), the first-order conditions
`μ = e^{−ρt}c^{−σ}` and `μ̇ + μ(f'(k) − δ) = 0` give the Euler equation
`ċ/c = (f'(k) − (δ + ρ))/σ`. -/
theorem eq_9_35 {ρ σ δ t cdot μdot fk : ℝ} {c μ : ℝ → ℝ} (hσ : σ ≠ 0) (hc0 : 0 < c t)
    (hc : HasDerivAt c cdot t) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * c s ^ (-σ))
    (hμd : HasDerivAt μ μdot t) (hfoc : (fk - δ) * μ t + μdot = 0) :
    cdot / c t = (fk - (δ + ρ)) / σ := by
  have hu' : HasDerivAt (fun x : ℝ => x ^ (-σ)) (-σ * c t ^ (-σ - 1)) (c t) :=
    Real.hasDerivAt_rpow_const (Or.inl hc0.ne')
  have h := (eq_9_26 (u' := fun x => x ^ (-σ)) hc hu' hμ hμd hfoc
    (Real.rpow_pos_of_pos hc0 _).ne' hc0.ne').2.2.2
  rw [continuousHamiltonian_crra_relative_risk_aversion hc0] at h
  rw [eq_div_iff hσ]
  linarith

/-- AKMM, p. 254, Figure 9.2: the phase-diagram signs. `k̇ = f(k) − δk − c > 0` iff
`c < f(k) − δk`; and with `f'` strictly decreasing, `σ > 0`, `c > 0` and `f'(k**) = δ + ρ`, the
consumption drift `c(f'(k) − (δ + ρ))/σ` is positive iff `k < k**` and zero iff `k = k**`. -/
theorem ramseyPlanner_phase_signs {f fp : ℝ → ℝ} {δ ρ σ kss k c : ℝ}
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hσ : 0 < σ) (hc : 0 < c) (hk : 0 < k)
    (hkss : 0 < kss) (hss : fp kss = δ + ρ) :
    (0 < f k - δ * k - c ↔ c < f k - δ * k) ∧
      (0 < c * (fp k - (δ + ρ)) / σ ↔ k < kss) ∧ (c * (fp k - (δ + ρ)) / σ = 0 ↔ k = kss) := by
  refine ⟨by constructor <;> intro h <;> linarith, ?_, ?_⟩
  · rw [div_pos_iff_of_pos_right hσ, mul_pos_iff_of_pos_left hc, sub_pos, ← hss]
    exact hanti.lt_iff_gt hkss hk
  · rw [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, ← hss]
    simp only [hc.ne', hσ.ne', false_or, or_false]
    exact hanti.injOn.eq_iff hk hkss

/-- AKMM, p. 255 and footnote 3: for a strictly concave neoclassical `f` and `δ, ρ > 0`, the
modified golden rule `f'(k**) = δ + ρ` has a unique positive solution; it lies strictly below
any golden-rule stock `f'(k_gold) = δ`; and the golden rule strictly maximizes steady-state
consumption `f(k) − δk` over `k ≥ 0`. -/
theorem ramseyPlanner_modified_golden_rule {f : ℝ → ℝ} {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hcont : ContinuousOn (deriv f) (Set.Ioi 0))
    (h0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop) (htop : Tendsto (deriv f) atTop (𝓝 0)) :
    (∃! kss : ℝ, 0 < kss ∧ deriv f kss = ρ + δ) ∧
      (∀ kss kgold : ℝ, 0 < kss → 0 < kgold → deriv f kss = ρ + δ → deriv f kgold = δ →
        kss < kgold ∧ ∀ k, 0 ≤ k → k ≠ kgold → f k - δ * k < f kgold - δ * kgold) := by
  refine ⟨RamseyCassKoopmans.existsUnique_stationary_capital_of_inada f ρ δ (by linarith) hconc
    hdiff hcont h0 htop, fun kss kgold hkss hkg hss hg => ⟨?_, fun k hk hne => ?_⟩⟩
  · exact RamseyCassKoopmans.stationary_capital_lt_golden_rule_of_strictConcave f kss kgold ρ δ
      hconc hdiff hkss hkg hρ hss hg
  · exact RamseyCassKoopmans.golden_rule_strictly_maximizes_consumption f kgold k δ hconc hkg hk
      hne (hdiff kgold hkg) hg

/-- AKMM, p. 255: "this dynamic also satisfies the TVC (9.34), because `k(t)` and `c(t)` become
constant in the long run": if `k → k̄`, `c → c̄ > 0`, `u'` is continuous at `c̄` and `ρ > 0`, then
`e^{−ρT}u'(c(T))k(T) → 0`. -/
theorem ramseyPlanner_tvc_of_convergent {ρ kbar cbar : ℝ} {u' k c : ℝ → ℝ} (hρ : 0 < ρ)
    (hk : Tendsto k atTop (𝓝 kbar)) (hc : Tendsto c atTop (𝓝 cbar))
    (hu' : ContinuousAt u' cbar) :
    Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0) := by
  have h := ((mangasarian_exp_neg_tendsto hρ).mul (hu'.tendsto.comp hc)).mul hk
  simpa using h

/-- AKMM, p. 255: a path along which capital reaches `k(T) = 0` while consumption `c(T) > 0`
(with `f(0) = 0`) has `k̇(T) = −c(T) < 0`, so capital is negative immediately after `T`: such a
path, with `c` following the Euler equation, is not feasible. -/
theorem ramseyPlanner_zero_capital_infeasible {f : ℝ → ℝ} {δ T : ℝ} {k c : ℝ → ℝ}
    (hf0 : f 0 = 0) (hkT : k T = 0) (hcT : 0 < c T)
    (hk : HasDerivAt k (f (k T) - δ * k T - c T) T) :
    ∀ᶠ t in 𝓝[>] T, k t < 0 := by
  rw [hkT, hf0, mul_zero, sub_zero, zero_sub] at hk
  have hs := (hasDerivAt_iff_tendsto_slope.mp hk).mono_left
    (nhdsWithin_mono T fun x (hx : T < x) => ne_of_gt hx)
  have hneg : ∀ᶠ t in 𝓝[>] T, (t - T)⁻¹ • (k t - k T) < 0 := by
    have := hs.eventually (gt_mem_nhds (neg_lt_zero.mpr hcT))
    filter_upwards [this] with t ht
    rwa [slope_def_module] at ht
  filter_upwards [hneg, self_mem_nhdsWithin] with t h1 h2
  have h2' : 0 < t - T := sub_pos.mpr h2
  rw [smul_eq_mul, hkT, sub_zero] at h1
  have := (mul_neg_iff.mp h1).resolve_right (fun h => (not_lt.mpr (inv_pos.mpr h2').le) h.1)
  exact this.2

/-- AKMM, (9.A.1)–(9.A.4), pp. 846–847: if `μ = e^{−ρt}u'(c)` (9.A.1) and
`μ̇ = −μ r(t)` with `r(t) = f'(k(t)) − δ` (9.A.2), `r` continuous, then
`μ(T) = μ(0)exp(−∫_0^T r)` and, with `A = u'(c(0))`,
(9.A.4) `u'(c(T)) = A exp(−∫_0^T (r − ρ))`; taking logs, (9.A.3)
`log u'(c(T)) − log u'(c(0)) = −∫_0^T (r − ρ)` when `u'(c) > 0`. -/
theorem appendix_9A4_marginal_utility {ρ : ℝ} {r μ u' c : ℝ → ℝ} (hr : Continuous r)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * r t)) t) {T : ℝ} (hT : 0 ≤ T) :
    μ T = μ 0 * Real.exp (-∫ s in (0 : ℝ)..T, r s) ∧
      u' (c T) = u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, (r s - ρ)) ∧
      (0 < u' (c 0) → Real.log (u' (c T)) - Real.log (u' (c 0)) =
        -∫ s in (0 : ℝ)..T, (r s - ρ)) := by
  have hR : ∀ t, HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, r s) (r t) t := fun t =>
    (hr.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℝ := fun t => μ t * Real.exp (∫ s in (0 : ℝ)..t, r s)
  have hg : ∀ t, 0 ≤ t → HasDerivAt g 0 t := fun t ht => by
    have := (h9A2 t ht).mul (hR t).exp
    convert this using 1
    ring
  have hcont : ContinuousOn g (Set.Icc 0 T) := fun t ht =>
    (hg t ht.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun t ht => (hg t ht.1).hasDerivWithinAt
  have h := hconst T ⟨hT, le_rfl⟩
  simp only [g, intervalIntegral.integral_same, Real.exp_zero, mul_one] at h
  have h1 : μ T = μ 0 * Real.exp (-∫ s in (0 : ℝ)..T, r s) := by
    rw [← h, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hsub : ∫ s in (0 : ℝ)..T, (r s - ρ) = (∫ s in (0 : ℝ)..T, r s) - ρ * T := by
    rw [intervalIntegral.integral_sub (hr.intervalIntegrable 0 T)
      (intervalIntegrable_const (μ := MeasureTheory.volume))]
    simp [mul_comm]
  have h2 : u' (c T) = u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, (r s - ρ)) := by
    have e1 := h9A1 T hT
    have e0 := h9A1 0 le_rfl
    simp only [mul_zero, Real.exp_zero, one_mul] at e0
    rw [h1, e0] at e1
    rw [hsub]
    have hE := Real.exp_pos (-ρ * T)
    have : u' (c T) = Real.exp (ρ * T) * (u' (c 0) * Real.exp (-∫ s in (0 : ℝ)..T, r s)) := by
      rw [e1, ← mul_assoc, ← Real.exp_add]
      simp
    rw [this, show -((∫ s in (0 : ℝ)..T, r s) - ρ * T) = ρ * T + -∫ s in (0 : ℝ)..T, r s by ring,
      Real.exp_add]
    ring
  refine ⟨h1, h2, fun hpos => ?_⟩
  rw [h2, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- AKMM, (9.A.5)–(9.A.6), p. 847: under (9.A.1)–(9.A.2) and `u'(c(0)) > 0`, the TVC (9.A.5)
`lim e^{−ρT}u'(c(T))k(T) = 0` is equivalent to (9.A.6) `lim exp(−∫_0^T (f'(k) − δ))k(T) = 0`. -/
theorem appendix_9A4_tvc_iff {ρ : ℝ} {r μ u' c k : ℝ → ℝ} (hr : Continuous r)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * r t)) t) (hA : 0 < u' (c 0)) :
    Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0) ↔
      Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  have e : ∀ T, 0 ≤ T → Real.exp (-ρ * T) * u' (c T) * k T =
      u' (c 0) * (Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) := fun T hT => by
    rw [← h9A1 T hT, (appendix_9A4_marginal_utility hr h9A1 h9A2 hT).1, h9A1 0 le_rfl]
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  have hev : ∀ᶠ T in atTop, Real.exp (-ρ * T) * u' (c T) * k T =
      u' (c 0) * (Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) :=
    (eventually_ge_atTop 0).mono e
  rw [tendsto_congr' hev]
  constructor
  · intro h
    have := h.const_mul (u' (c 0))⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hA.ne'] using this
  · intro h
    simpa using h.const_mul (u' (c 0))

/-- AKMM, Appendix 9.A.4, p. 847, on the saddle path: if `r(t) = f'(k(t)) − δ → ρ > 0` (because
`k → k̄` with `f'(k̄) = δ + ρ`) and `k(T) → k̄`, then `∫_0^T r → ∞` and (9.A.6) holds. -/
theorem appendix_9A4_saddle_tvc {ρ kbar : ℝ} {r k : ℝ → ℝ} (hρ : 0 < ρ) (hr : Continuous r)
    (hrlim : Tendsto r atTop (𝓝 ρ)) (hk : Tendsto k atTop (𝓝 kbar)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, r s) atTop atTop ∧
      Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  obtain ⟨that, hthat⟩ := eventually_atTop.mp (hrlim.eventually (lt_mem_nhds (half_lt_self hρ)))
  have hlow : ∀ T, max that 0 ≤ T → (∫ s in (0 : ℝ)..max that 0, r s) + ρ / 2 * (T - max that 0)
      ≤ ∫ s in (0 : ℝ)..T, r s := by
    intro T hT
    rw [← intervalIntegral.integral_add_adjacent_intervals (hr.intervalIntegrable 0 (max that 0))
      (hr.intervalIntegrable (max that 0) T)]
    have hm : ρ / 2 * (T - max that 0) ≤ ∫ s in max that 0..T, r s := by
      have := intervalIntegral.integral_mono_on hT
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := ρ / 2))
        (hr.intervalIntegrable _ _) fun s hs => (hthat s ((le_max_left _ _).trans hs.1)).le
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    linarith
  have htop : Tendsto (fun T => ∫ s in (0 : ℝ)..T, r s) atTop atTop := by
    refine tendsto_atTop_mono' atTop ((eventually_ge_atTop (max that 0)).mono hlow) ?_
    have h1 : Tendsto (fun T : ℝ => ρ / 2 * (T - max that 0)) atTop atTop :=
      ((tendsto_atTop_add_const_right atTop (-max that 0) tendsto_id).const_mul_atTop
        (half_pos hρ)).congr fun T => by simp [sub_eq_add_neg]
    exact tendsto_atTop_add_const_left atTop _ h1
  refine ⟨htop, ?_⟩
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).mul hk
  simpa using this

/-- AKMM, Appendix 9.A.4, pp. 847–848, below the saddle path: if after some `t̄` the path stays
in the region `r(t) = f'(k(t)) − δ ≤ 0` (capital above the golden rule) and capital stays
above some `κ > 0`, then `exp(−∫_0^T r)k(T) ≥ exp(−∫_0^{t̄} r)κ > 0` for `T ≥ t̄`, so (9.A.6), and
hence the TVC, fails. -/
theorem appendix_9A4_below_saddle_violates_tvc {tbar κ : ℝ} {r k : ℝ → ℝ} (hr : Continuous r)
    (hneg : ∀ t, tbar ≤ t → r t ≤ 0) (hκ : 0 < κ) (hk : ∀ t, tbar ≤ t → κ ≤ k t) :
    (∀ T, tbar ≤ T → Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ ≤
      Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) ∧
      ¬ Tendsto (fun T => Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T) atTop (𝓝 0) := by
  have hbound : ∀ T, tbar ≤ T → Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ ≤
      Real.exp (-∫ s in (0 : ℝ)..T, r s) * k T := by
    intro T hT
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hr.intervalIntegrable (μ := MeasureTheory.volume) 0 tbar)
      (hr.intervalIntegrable (μ := MeasureTheory.volume) tbar T)
    have hle : ∫ s in tbar..T, r s ≤ 0 := by
      have := intervalIntegral.integral_mono_on hT (hr.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (0 : ℝ)))
        fun s hs => hneg s hs.1
      simpa using this
    have hexp : Real.exp (-∫ s in (0 : ℝ)..tbar, r s) ≤ Real.exp (-∫ s in (0 : ℝ)..T, r s) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul hexp (hk T hT) hκ.le (Real.exp_pos _).le
  refine ⟨hbound, fun hlim => ?_⟩
  have hpos : 0 < Real.exp (-∫ s in (0 : ℝ)..tbar, r s) * κ := mul_pos (Real.exp_pos _) hκ
  obtain ⟨T, hT⟩ := ((hlim.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop tbar)).exists
  linarith [hbound T hT.2]

/-- AKMM, Appendix 9.A.4: the hypotheses of `appendix_9A4_below_saddle_violates_tvc` are
satisfiable: `r ≡ −1` (a capital stock above the golden rule) and `k ≡ 1`. -/
theorem appendix_9A4_below_saddle_instance :
    ¬ Tendsto (fun T => Real.exp (-∫ _ in (0 : ℝ)..T, (-1 : ℝ)) * (1 : ℝ)) atTop (𝓝 0) :=
  (appendix_9A4_below_saddle_violates_tvc (tbar := 0) (k := fun _ => 1) continuous_const
    (fun _ _ => by norm_num) one_pos fun _ _ => le_rfl).2

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The saddle path of the planner's problem

AKMM, §9.3.2 (p. 255): "Starting from `k(0)`, the social planner has to choose the value of
initial consumption `c(0)` that is on the saddle path … On the saddle path, `(k(t), c(t))`
gradually approaches the steady state … This dynamic also satisfies the TVC (9.34)".

EconomicGrowth's `RamseyCassKoopmans` library constructs, for every `k(0) > 0`, the unique
optimum of Cass's problem, in which gross investment is irreversible (`f(k) − c ≥ 0`), with a
price certificate. The book's planner may disinvest. `ramseySaddle_path` shows that whenever
the Cass optimum invests strictly throughout (in particular for every `0 < k(0) ≤ k**`), it is
the book's saddle path: it converges to `(k**, f(k**) − δk**)`, satisfies the first-order
conditions (9.A.1)–(9.A.2) with `μ = e^{−ρt}u'(c)`, the Euler equation in the form
`ċ = −(u'/u'')(c)(f'(k) − (δ + ρ))` (which is (9.35) for CRRA), and the TVC (9.34), and by
`mangasarian_planner` it is catching-up optimal against every feasible path of the book's
problem, including paths that disinvest.

`ramseySaddle_primitives` proves that the book's model, Cobb–Douglas `f(k) = k^α` with CRRA
utility, satisfies the library's assumptions (`CassPrimitives`), and
`ramseySaddle_crra_cobbDouglas` states the result for it, with (9.35) itself.
-/

namespace AKMM.ContinuousTime

open Filter Topology RamseyCassKoopmans

/-- The derivative of the power function `A y^p + B` at `y > 0`. -/
theorem ramseySaddle_power_hasDerivAt (A B p : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => A * x ^ p + B) (A * p * y ^ (p - 1)) y := by
  have h := ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hy.ne')).const_mul A).add_const B
  convert h using 1
  ring

/-- The first and second derivatives of `A y^p + B` on `(0, ∞)`, as functions near `x > 0`. -/
theorem ramseySaddle_power_derivs (A B p : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => A * y ^ p + B) =ᶠ[𝓝 x] (fun y => A * p * y ^ (p - 1)) ∧
      HasDerivAt (deriv fun y : ℝ => A * y ^ p + B) (A * p * (p - 1) * x ^ (p - 1 - 1)) x ∧
      deriv (deriv fun y : ℝ => A * y ^ p + B) x = A * p * (p - 1) * x ^ (p - 1 - 1) := by
  have hev : deriv (fun y : ℝ => A * y ^ p + B) =ᶠ[𝓝 x] (fun y => A * p * y ^ (p - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (ramseySaddle_power_hasDerivAt A B p hy).deriv
  have hd : HasDerivAt (fun y : ℝ => A * p * y ^ (p - 1))
      (A * p * (p - 1) * x ^ (p - 1 - 1)) x := by
    have h := ramseySaddle_power_hasDerivAt (A * p) 0 (p - 1) hx
    simp only [add_zero] at h
    convert h using 1
  have hd' := hd.congr_of_eventuallyEq hev
  exact ⟨hev, hd', hd'.deriv⟩

/-- Analytic properties of `G(y) = A y^p + B` with `Ap > 0` and `p < 1` on `(0, ∞)`: positive
decreasing marginal value with continuous first and second derivatives, Inada limits, strict
concavity. -/
theorem ramseySaddle_power_props (A B p : ℝ) (hAp : 0 < A * p) (hp : p < 1) :
    (∀ y, 0 < y → DifferentiableAt ℝ (fun x : ℝ => A * x ^ p + B) y) ∧
      ContinuousOn (deriv fun x : ℝ => A * x ^ p + B) (Set.Ioi 0) ∧
      (∀ y, 0 < y → 0 < deriv (fun x : ℝ => A * x ^ p + B) y) ∧
      (∀ y, 0 < y → DifferentiableAt ℝ (deriv fun x : ℝ => A * x ^ p + B) y) ∧
      ContinuousOn (deriv (deriv fun x : ℝ => A * x ^ p + B)) (Set.Ioi 0) ∧
      (∀ y, 0 < y → deriv (deriv fun x : ℝ => A * x ^ p + B) y < 0) ∧
      Tendsto (deriv fun x : ℝ => A * x ^ p + B) (𝓝[>] (0 : ℝ)) atTop ∧
      Tendsto (deriv fun x : ℝ => A * x ^ p + B) atTop (𝓝 0) ∧
      StrictConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => A * x ^ p + B) := by
  set G : ℝ → ℝ := fun x => A * x ^ p + B
  have hD : ∀ y, 0 < y → deriv G y = A * p * y ^ (p - 1) := fun y hy =>
    (ramseySaddle_power_hasDerivAt A B p hy).deriv
  have hD2 : ∀ y, 0 < y → deriv (deriv G) y = A * p * (p - 1) * y ^ (p - 1 - 1) := fun y hy =>
    (ramseySaddle_power_derivs A B p hy).2.2
  have hneg2 : ∀ y, 0 < y → deriv (deriv G) y < 0 := fun y hy => by
    rw [hD2 y hy]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hAp (by linarith))
      (Real.rpow_pos_of_pos hy _)
  have hp1 : p - 1 < 0 := by linarith
  refine ⟨fun y hy => (ramseySaddle_power_hasDerivAt A B p hy).differentiableAt,
    fun y hy => ((ramseySaddle_power_derivs A B p hy).2.1).continuousAt.continuousWithinAt,
    fun y hy => by rw [hD y hy]; exact mul_pos hAp (Real.rpow_pos_of_pos hy _),
    fun y hy => ((ramseySaddle_power_derivs A B p hy).2.1).differentiableAt, ?_, hneg2, ?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun y : ℝ => A * p * (p - 1) * y ^ (p - 1 - 1)) (Set.Ioi 0) :=
      fun y hy => ((ramseySaddle_power_hasDerivAt (A * p * (p - 1)) 0 (p - 1 - 1) hy).congr_deriv
        rfl |>.continuousAt.congr (by filter_upwards with z; simp)).continuousWithinAt
    exact hc.congr fun y hy => hD2 y hy
  · have h := (tendsto_rpow_neg_nhdsGT_zero hp1).const_mul_atTop hAp
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hD y hy).symm
  · have h := (tendsto_rpow_neg_atTop (y := 1 - p) (by linarith)).const_mul (A * p)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [hD y hy, neg_sub]
  · refine strictConcaveOn_of_deriv2_neg (convex_Ioi 0) (fun y hy =>
      (ramseySaddle_power_hasDerivAt A B p hy).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Ioi] at hy
    simpa [Function.iterate_succ] using hneg2 y hy

/-- AKMM, p. 254: the book's model, Cobb–Douglas `f(k) = k^α` (`0 < α < 1`) with CRRA utility
`u(c) = (c^{1−σ} − 1)/(1 − σ)` (`σ > 0`, `σ ≠ 1`), `ρ, δ > 0`, satisfies the assumptions of
EconomicGrowth's Ramsey–Cass–Koopmans library. -/
theorem ramseySaddle_primitives {α σ ρ δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hσ : 0 < σ)
    (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) :
    CassPrimitives (fun k : ℝ => k ^ α) (crraUtility σ) ρ δ := by
  have hf : (fun k : ℝ => k ^ α) = fun x : ℝ => 1 * x ^ α + 0 := by funext x; ring
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : crraUtility σ = fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [crraUtility]; ring
  obtain ⟨fd, fpc, fpp, fs, fsc, -, fi0, fit, -⟩ :=
    ramseySaddle_power_props 1 0 α (by linarith) hα1
  obtain ⟨ud, -, upp, us, usc, usn, ui0, -, uconc⟩ :=
    ramseySaddle_power_props (1 / (1 - σ)) (-(1 / (1 - σ))) (1 - σ)
      (by rw [one_div, inv_mul_cancel₀ h1σ]; exact one_pos) (by linarith)
  rw [← hf] at fd fpc fpp fs fsc fi0 fit
  rw [← hu] at ud upp us usc usn ui0 uconc
  exact ⟨hρ, hδ, Real.strictConcaveOn_rpow hα0 hα1, Real.zero_rpow hα0.ne', fd, fpc, fpp, fs,
    fsc, fi0, fit, uconc, ud, upp, us, usc, usn, ui0⟩

/-- AKMM, §9.3.2, p. 255 and Appendix 9.A.4: **the saddle path**. Under EconomicGrowth's
assumptions `P` (gross output `f`, utility `u`, discount `ρ`, depreciation `δ`), if the certified
Cass optimum from `k(0) > 0` invests strictly throughout (which holds for `k(0) ≤ k**`, see
`ramseySaddle_path`), then it converges to `(k**, f(k**) − δk**)` with `f'(k**) = ρ + δ`,
satisfies (9.A.1) `μ = e^{−ρt}u'(c)`, (9.A.2) `μ̇ = −μ(f'(k) − δ)` and the TVC (9.34), and is
catching-up optimal in the book's problem (9.33): against every path from `k(0)` with `k ≥ 0`
and positive continuous consumption, disinvestment allowed. -/
theorem ramseySaddle_of_interior {f U : ℝ → ℝ} {ρ δ : ℝ} (P : CassPrimitives f U ρ δ)
    {a : FeasiblePath f δ} {q : ℝ → ℝ} (hc : CassCertificate f U ρ δ a q)
    (hint : ∀ t, 0 ≤ t → 0 < a.investment t) :
    deriv f (cassSteady P) = ρ + δ ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P)) ∧
      Tendsto a.consumption atTop (𝓝 (f (cassSteady P) - δ * cassSteady P)) ∧
      (∀ t, 0 ≤ t → discount ρ t * q t = Real.exp (-ρ * t) * deriv U (a.consumption t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun s => discount ρ s * q s)
        (-(discount ρ t * q t * (deriv f (a.capital t) - δ))) t) ∧
      Tendsto (fun T => Real.exp (-ρ * T) * deriv U (a.consumption T) * a.capital T) atTop
        (𝓝 0) ∧
      ∀ k' c' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ k' t) → (∀ t, 0 ≤ t → 0 < c' t) →
        ContinuousOn c' (Set.Ici 0) →
        (∀ t, 0 ≤ t → HasDerivAt k' (f (k' t) - δ * k' t - c' t) t) → k' 0 = a.capital 0 →
        ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (c' t) ≤
          (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * U (a.consumption t)) + ε := by
  obtain ⟨hk, hcon, -, -, -⟩ := hc.dynamics P
  have hqU : ∀ t, 0 ≤ t → q t = deriv U (a.consumption t) := fun t ht => by
    rcases mul_eq_zero.mp (hc.slack t ht) with h | h
    · linarith
    · exact absurd h (hint t ht).ne'
  have h9A1 : ∀ t, 0 ≤ t → discount ρ t * q t = Real.exp (-ρ * t) * deriv U (a.consumption t) :=
    fun t ht => by rw [hqU t ht]; rfl
  have h9A2 : ∀ t, 0 ≤ t → HasDerivAt (fun s => discount ρ s * q s)
      (-(discount ρ t * q t * (deriv f (a.capital t) - δ))) t := fun t ht => by
    have h := hasDerivAt_discounted_costate (d := ρ) (m := δ) (mu := deriv U (a.consumption t))
      (mp := deriv f (a.capital t)) (hc.costate t ht)
    convert h using 1
    rw [← hqU t ht]
    ring
  have htvc : Tendsto (fun T => Real.exp (-ρ * T) * deriv U (a.consumption T) * a.capital T)
      atTop (𝓝 0) := by
    have h := hc.transversality.mul hk
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [← h9A1 T hT]
  refine ⟨(cassSteady_spec P).2, hk, hcon, h9A1, h9A2, htvc, ?_⟩
  intro k' c' hk' hc' hcc' hkd' h0
  exact (mangasarian_planner (f' := deriv f) (μ := fun s => discount ρ s * q s)
    P.f_conc.concaveOn P.U_conc.concaveOn (fun y hy => (P.U_diff y hy).hasDerivAt)
    (fun y hy => (P.U_prime_pos y hy).le) hc.capital_pos
    (fun t ht => (P.f_diff _ (hc.capital_pos t ht)).hasDerivAt) a.consumption_pos
    a.consumption_continuous (fun t ht => a.hasDerivAt_capital' ht) h9A1 h9A2 htvc hk' hc'
    hcc' hkd' h0).1

/-- AKMM, §9.3.2, p. 255: **the saddle path from `k(0) ≤ k**`**. For every `0 < k(0) ≤ k**`
the certified Cass optimum invests strictly, so it is the book's saddle path: it converges to
the steady state, satisfies (9.A.1), (9.A.2), (9.34), the Euler equation
`ċ = −(u'/u'')(c)(f'(k) − (ρ + δ))` (for `k(0) < k**`, `t > 0`), and is catching-up optimal in
the book's problem (`ramseySaddle_of_interior`). -/
theorem ramseySaddle_path {f U : ℝ → ℝ} {ρ δ k₀ : ℝ} (P : CassPrimitives f U ρ δ)
    (hk₀ : 0 < k₀) (hle : k₀ ≤ cassSteady P) :
    ∃ a : FeasiblePath f δ, ∃ q : ℝ → ℝ, a.capital 0 = k₀ ∧ CassCertificate f U ρ δ a q ∧
      (∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k₀ < cassSteady P → ∀ t, 0 < t → HasDerivAt a.consumption
        (-(deriv U (a.consumption t)) / deriv (deriv U) (a.consumption t) *
          (deriv f (a.capital t) - (ρ + δ))) t) := by
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk₀
  set a := optimalPath P hk₀
  have hint : ∀ t, 0 ≤ t → 0 < a.investment t := by
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨ks, hks, hstat, b, Jb, hb0, -, -, -, -, -, -, -, hbinv, -, -, -, hbuniq⟩ :=
        cass_general_dynamic f U ρ δ k₀ P.d_pos P.m_pos hk₀ P.f_conc P.f_zero P.f_diff
          P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont P.f_inada0 P.f_inadaTop
          P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont P.U_second_neg P.U_inada0
      have hks' : cassSteady P = ks := cassSteady_eq P hks hstat
      obtain ⟨J, hJ⟩ := hc.welfare
      have huniq := (hbuniq a J (hc.isCassOptimal P hJ) h0).2
      intro t ht
      rw [(huniq t ht).2.2]
      exact hbinv (hks' ▸ hlt) t ht
    · intro t ht
      have hconst := (hc.dynamics P).2.2.2.2 (h0.trans heq) t ht
      have hr := a.resource t ht
      rw [hconst.1, hconst.2] at hr
      have : a.investment t = δ * cassSteady P := by linarith
      rw [this]
      exact mul_pos P.m_pos (cassSteady_spec P).1
  refine ⟨a, q, h0, hc, hint, fun hlt t ht => ?_⟩
  have h := hc.hasDerivAt_consumption P (by rw [h0]; exact hlt.ne) le_rfl
    (fun s hs => hint s hs) ht
  exact h

/-- AKMM, (9.35) and p. 255, **for the book's model**: Cobb–Douglas `f(k) = k^α` and CRRA
utility. For `0 < k(0) ≤ k**` there is a path that converges to the steady state, invests
strictly, satisfies the CRRA Euler equation (9.35) `ċ/c = (f'(k) − (δ + ρ))/σ` (when
`k(0) < k**`, `t > 0`), and is optimal in the book's problem with the properties of
`ramseySaddle_of_interior`. -/
theorem ramseySaddle_crra_cobbDouglas {α σ ρ δ k₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hk₀ : 0 < k₀)
    (hle : k₀ ≤ cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ)) :
    ∃ a : FeasiblePath (fun k : ℝ => k ^ α) δ, ∃ q : ℝ → ℝ, a.capital 0 = k₀ ∧
      CassCertificate (fun k : ℝ => k ^ α) (crraUtility σ) ρ δ a q ∧
      (∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k₀ < cassSteady (ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ) → ∀ t, 0 < t →
        ∃ cdot, HasDerivAt a.consumption cdot t ∧
          cdot / a.consumption t = (α * a.capital t ^ (α - 1) - (δ + ρ)) / σ) := by
  set P := ramseySaddle_primitives hα0 hα1 hσ hσ1 hρ hδ
  obtain ⟨a, q, h0, hc, hint, heul⟩ := ramseySaddle_path P hk₀ hle
  refine ⟨a, q, h0, hc, hint, fun hlt t ht => ⟨_, heul hlt t ht, ?_⟩⟩
  have hct := a.consumption_pos t ht.le
  have hkt := hc.capital_pos t ht.le
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  have hu : crraUtility σ = fun x : ℝ => 1 / (1 - σ) * x ^ (1 - σ) + -(1 / (1 - σ)) := by
    funext x; simp only [crraUtility]; ring
  have hU1 : deriv (crraUtility σ) (a.consumption t) = a.consumption t ^ (-σ) := by
    rw [hu, (ramseySaddle_power_hasDerivAt _ _ _ hct).deriv]
    field_simp
    ring_nf
  have hU2 : deriv (deriv (crraUtility σ)) (a.consumption t) =
      -σ * a.consumption t ^ (-σ - 1) := by
    rw [hu, (ramseySaddle_power_derivs _ _ _ hct).2.2]
    field_simp
    ring_nf
  have hF1 : deriv (fun k : ℝ => k ^ α) (a.capital t) = α * a.capital t ^ (α - 1) := by
    exact (Real.hasDerivAt_rpow_const (Or.inl hkt.ne')).deriv
  rw [hU1, hU2, hF1]
  have hsplit : a.consumption t ^ (-σ - 1) * a.consumption t = a.consumption t ^ (-σ) := by
    rw [Real.rpow_sub_one hct.ne']
    field_simp
  have hpos := Real.rpow_pos_of_pos hct (-σ)
  have hpos1 := Real.rpow_pos_of_pos hct (-σ - 1)
  rw [div_eq_div_iff hct.ne' hσ.ne']
  rw [← hsplit]
  field_simp
  ring

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The market equilibrium in continuous time

AKMM, §9.3.2, "The market equilibrium in continuous time" (pp. 256–257): (9.36)–(9.39).

* The household problem (9.36) and its Euler equation (9.37)
  `ċ_i/c_i = (r(t) − (δ + ρ))/σ` (`eq_9_37`), and sufficiency of the household's conditions
  with the no-borrowing constraint `k_i ≥ 0` and the TVC (`market_household_optimal`).
* The firm: with constant returns, `F₁(K, L) = f'(k̃)` and `F₂(K, L) = f(k̃) − k̃f'(k̃)`,
  `k̃ = K/L` (`market_firm_marginal_products`); at these prices profit is zero and maximal
  (`market_firm_optimal`).
* Market clearing and (9.38)–(9.39): `r = f'(k)`, `w = f(k) − kf'(k)`; substituting into (9.36)
  and (9.37) under symmetry gives exactly (9.33) and (9.35) (`market_equilibrium_planner_system`).
* The planner's solution with these prices is a market equilibrium: the household budget
  holds, the household's first-order conditions and TVC hold, so households optimize; firms
  maximize profit and markets clear (`market_planner_is_equilibrium`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.37), p. 256: the household's first-order conditions for (9.36),
`μ = e^{−ρt}c_i^{−σ}` and `μ̇ + μ(r(t) − δ) = 0`, give the Euler equation
`ċ_i/c_i = (r(t) − (δ + ρ))/σ`. -/
theorem eq_9_37 {ρ σ δ t cdot μdot rt : ℝ} {c μ : ℝ → ℝ} (hσ : σ ≠ 0) (hc0 : 0 < c t)
    (hc : HasDerivAt c cdot t) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * c s ^ (-σ))
    (hμd : HasDerivAt μ μdot t) (hfoc : (rt - δ) * μ t + μdot = 0) :
    cdot / c t = (rt - (δ + ρ)) / σ :=
  eq_9_35 hσ hc0 hc hμ hμd hfoc

/-- AKMM, (9.36)–(9.37), p. 256: **sufficiency for the household**. If `u` is concave with
`u' ≥ 0`, and the household's plan satisfies (9.36) `k̇ = r(t)k + w(t) − δk − c`, the conditions
`μ = e^{−ρt}u'(c)`, `μ̇ = −μ(r(t) − δ)` and the TVC `lim e^{−ρT}u'(c(T))k(T) = 0`, then it is
catching-up optimal against every plan from the same `k_i(0)` with `k_i ≥ 0` and positive
continuous consumption. -/
theorem market_household_optimal {ρ δ : ℝ} {u u' r w : ℝ → ℝ} {k c μ k' c' : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (r t * k t + w t - δ * k t - c t) t)
    (hfoc : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (hcost : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (r t - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0))
    (hk' : ∀ t, 0 ≤ t → 0 ≤ k' t) (hc' : ∀ t, 0 ≤ t → 0 < c' t)
    (hcc' : ContinuousOn c' (Set.Ici 0))
    (hkd' : ∀ t, 0 ≤ t → HasDerivAt k' (r t * k' t + w t - δ * k' t - c' t) t)
    (h0 : k' 0 = k 0) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε := by
  have hμ0 : ∀ t, 0 ≤ t → 0 ≤ μ t := fun t ht => by
    rw [hfoc t ht]; exact mul_nonneg (Real.exp_pos _).le (hu'0 _ (hc t ht))
  refine (mangasarian_catching_up (G := fun t y => (r t - δ) * y + w t)
    (Gx := fun t _ => r t - δ) hconc hu hc hcc (fun t ht => by convert hkd t ht using 1; ring)
    hcost hfoc hμ0 hc' hcc' (fun t ht => by convert hkd' t ht using 1; ring) h0
    (fun t _ => by ring_nf; rfl) ?_).1
  intro ε hε
  have htvc' : Tendsto (fun T => μ T * k T) atTop (𝓝 0) := by
    refine htvc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [hfoc T hT]
  filter_upwards [htvc'.eventually (gt_mem_nhds hε), eventually_ge_atTop (0 : ℝ)] with T h1 hT
  nlinarith [mul_nonneg (hμ0 T hT) (hk' T hT)]

/-- AKMM, p. 256 (Section 3.3): with constant returns, `F(K, L) = Lf(K/L)` for `L > 0`, and the
marginal products are `F₁(K, L) = f'(k̃)` and `F₂(K, L) = f(k̃) − k̃f'(k̃)`, `k̃ = K/L`,
`f(k) = F(k, 1)`. -/
theorem market_firm_marginal_products {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N) {K L f' : ℝ}
    (hL : 0 < L) (hf : HasDerivAt (fun k => F k 1) f' (K / L)) :
    F K L = L * F (K / L) 1 ∧ HasDerivAt (fun x => F x L) f' K ∧
      HasDerivAt (fun x => F K x) (F (K / L) 1 - K / L * f') L := by
  have hform : ∀ x y, 0 < y → F x y = y * F (x / y) 1 := fun x y hy => by
    have := hcrs y hy (x / y) 1
    rw [mul_div_cancel₀ _ hy.ne', mul_one] at this
    exact this
  refine ⟨hform K L hL, ?_, ?_⟩
  · have hin : HasDerivAt (fun x : ℝ => x / L) (1 / L) K := by
      simpa using (hasDerivAt_id K).div_const L
    have h := (hf.comp K hin).const_mul L
    have hev : (fun x => F x L) =ᶠ[𝓝 K] fun x => L * F (x / L) 1 :=
      Eventually.of_forall fun x => hform x L hL
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
  · have hin : HasDerivAt (fun y : ℝ => K / y) (-K / L ^ 2) L := by
      have := (hasDerivAt_inv hL.ne').const_mul K
      convert this using 1
      · funext y; simp [div_eq_mul_inv]
      · field_simp
    have h := (hasDerivAt_id L).mul (hf.comp L hin)
    have hev : (fun y => F K y) =ᶠ[𝓝 L] fun y => id y * (fun k => F k 1) (K / y) := by
      filter_upwards [Ioi_mem_nhds hL] with y hy
      exact hform K y hy
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [id, one_mul, Function.comp]
    field_simp
    ring

/-- AKMM, p. 256: the firm's problem `max F(K, L) − rK − wL`. At `r = f'(k̃)` and
`w = f(k̃) − k̃f'(k̃)` with `f` concave, the choice `(K, L)` with `K/L = k̃` earns zero profit
(Euler's theorem), and every `(K', L')` with `L' > 0`, `K' ≥ 0` earns at most zero. -/
theorem market_firm_optimal {F : ℝ → ℝ → ℝ}
    (hcrs : ∀ lam > 0, ∀ K N, F (lam * K) (lam * N) = lam * F K N)
    (hconc : ConcaveOn ℝ (Set.Ici 0) fun k => F k 1) {K L f' : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hf : HasDerivAt (fun k => F k 1) f' (K / L)) :
    F K L - f' * K - (F (K / L) 1 - K / L * f') * L = 0 ∧
      ∀ K' L', 0 ≤ K' → 0 < L' → F K' L' - f' * K' - (F (K / L) 1 - K / L * f') * L' ≤ 0 := by
  have hform : ∀ x y, 0 < y → F x y = y * F (x / y) 1 := fun x y hy => by
    have := hcrs y hy (x / y) 1
    rw [mul_div_cancel₀ _ hy.ne', mul_one] at this
    exact this
  refine ⟨?_, fun K' L' hK' hL' => ?_⟩
  · rw [hform K L hL]
    field_simp
    ring
  · rw [hform K' L' hL']
    have hs := RamseyCassKoopmans.concave_support hconc (Set.mem_Ici.mpr (div_nonneg hK hL.le))
      (Set.mem_Ici.mpr (div_nonneg hK' hL'.le)) hf
    have e : L' * (F (K' / L') 1 - F (K / L) 1 - f' * (K' / L' - K / L)) =
        L' * F (K' / L') 1 - f' * K' - (F (K / L) 1 - K / L * f') * L' := by
      field_simp
      ring
    have := mul_nonpos_of_nonneg_of_nonpos hL'.le (by linarith : F (K' / L') 1 - F (K / L) 1 -
      f' * (K' / L' - K / L) ≤ 0)
    linarith

/-- AKMM, (9.38)–(9.39), pp. 256–257: with market clearing `∫k_i = K`, `L = 1`, symmetry
`k_i = k`, `c_i = c`, and the prices `r = f'(k)`, `w = f(k) − kf'(k)`, the household budget
(9.36) is the resource constraint (9.33) and the Euler equation (9.37) is (9.35). -/
theorem market_equilibrium_planner_system (f : ℝ → ℝ) (fp δ ρ σ k c : ℝ) :
    fp * k + (f k - k * fp) - δ * k - c = f k - δ * k - c ∧
      (fp - (δ + ρ)) / σ = (fp - (δ + ρ)) / σ := ⟨by ring, rfl⟩

/-- AKMM, pp. 256–257: **the planner's solution is a market equilibrium**. If `(k, c)` solves the
planner's conditions — (9.33), `μ = e^{−ρt}u'(c)`, `μ̇ = −μ(f'(k) − δ)` and the TVC (9.34) —
then with the prices (9.38)–(9.39), `r(t) = f'(k(t))`, `w(t) = f(k(t)) − k(t)f'(k(t))`: the
household budget (9.36) holds along `(k, c)`, and every household plan from `k(0)` with
`k_i ≥ 0` is (catching-up) no better, so `(k, c)` is the household's optimum; markets clear with
`K = k`, `L = 1`. -/
theorem market_planner_is_equilibrium {ρ δ : ℝ} {f f' u u' : ℝ → ℝ} {k c μ : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y)
    (hu'0 : ∀ y, 0 < y → 0 ≤ u' y)
    (hc : ∀ t, 0 ≤ t → 0 < c t) (hcc : ContinuousOn c (Set.Ici 0))
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (f (k t) - δ * k t - c t) t)
    (h9A1 : ∀ t, 0 ≤ t → μ t = Real.exp (-ρ * t) * u' (c t))
    (h9A2 : ∀ t, 0 ≤ t → HasDerivAt μ (-(μ t * (f' (k t) - δ))) t)
    (htvc : Tendsto (fun T => Real.exp (-ρ * T) * u' (c T) * k T) atTop (𝓝 0)) :
    (∀ t, 0 ≤ t → HasDerivAt k ((fun s => f' (k s)) t * k t +
        (fun s => f (k s) - k s * f' (k s)) t - δ * k t - c t) t) ∧
      ∀ k' c' : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ k' t) → (∀ t, 0 ≤ t → 0 < c' t) →
        ContinuousOn c' (Set.Ici 0) →
        (∀ t, 0 ≤ t → HasDerivAt k' (f' (k t) * k' t + (f (k t) - k t * f' (k t)) -
          δ * k' t - c' t) t) → k' 0 = k 0 →
        ∀ ε > 0, ∀ᶠ T in atTop, ∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c' t) ≤
          (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) + ε := by
  have hbud : ∀ t, 0 ≤ t → HasDerivAt k ((fun s => f' (k s)) t * k t +
      (fun s => f (k s) - k s * f' (k s)) t - δ * k t - c t) t := fun t ht => by
    convert hkd t ht using 1
    simp only
    ring
  refine ⟨hbud, fun k' c' hk' hc' hcc' hkd' h0 => ?_⟩
  exact market_household_optimal (r := fun s => f' (k s)) (w := fun s => f (k s) - k s * f' (k s))
    hconc hu hu'0 hc hcc hbud h9A1 h9A2 htvc hk' hc' hcc' hkd' h0

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Uncertainty: the Poisson distribution and exponential waiting times

AKMM, §9.4 (pp. 257–259): (9.40)–(9.43), the Poisson distribution, survival probabilities and
the expected duration of a job.

Mathlib has no Poisson *process* (independent increments, counting paths). What follows from
the binomial approximation, the exponential distribution and memorylessness is proved:

* (9.40)–(9.42): the binomial probabilities `b(k, n)` of `k` successes in `n` trials with
  success probability `λ/n`; they sum to `1`, the expected number of successes is `λ`, and
  (9.41)–(9.42) hold (`poisson_binomial_sum`, `poisson_expected_successes`, `eq_9_41`,
  `eq_9_42`).
* (9.43): `b(0, n) → e^{−λ}`; the ratio `b(k, n)/b(k − 1, n) → λ/k`; hence the law of small
  numbers `b(k, n) → e^{−λ}λ^k/k!` (`eq_9_43`, `poisson_ratio_limit`, `poisson_limit`).
* The Poisson probabilities sum to `1` with mean `λ` (`poisson_sum_mean`); with rate `λ` on an
  interval of length `T` they are those of parameter `λT` (`poisson_limit_interval`).
* The probability of no success in `(t, t + T]` is `e^{−λT}`, memoryless; and a decreasing
  survival function with values in `(0, 1)` that is memoryless is exponential
  (`poisson_survival_memoryless`, `poisson_memoryless_iff_exponential`, from Sargent–Stachurski's
  Lemma 10.1.1). With a time-varying rate the survival probability `S`, defined by
  `Ṡ = −λ(s)S`, `S(t) = 1`, is `e^{−∫_t^{t+T} λ}` (`poisson_survival_time_varying`).
* The expected remaining job duration `∫_0^∞ tσe^{−σt}dt = 1/σ`, and the density integrates to
  `1` (`poisson_expected_duration`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.40), p. 258: the binomial probability of `k` successes in `n` trials with success
probability `λ/n` each. -/
noncomputable def binomialProb (lam : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (lam / n) ^ k * (1 - lam / n) ^ (n - k)

/-- AKMM, p. 258: the binomial probabilities `b(0, n), …, b(n, n)` sum to `1`. -/
theorem poisson_binomial_sum (lam : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binomialProb lam n k = 1 := by
  have h := (add_pow (lam / n) (1 - lam / n) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [binomialProb]
  ring

/-- AKMM, p. 258: with `n` trials of success probability `λ/n`, the expected number of successes
is `λ/n + ⋯ + λ/n = λ` (`n` times). -/
theorem poisson_expected_successes (lam : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ _i ∈ Finset.range n, lam / n = lam := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- AKMM, (9.41), p. 258: `b(0, n) = (1 − λ/n)^n`. -/
theorem eq_9_41 (lam : ℝ) (n : ℕ) : binomialProb lam n 0 = (1 - lam / n) ^ n := by
  simp [binomialProb]

/-- AKMM, (9.42), p. 258: for `1 ≤ k ≤ n` and `λ ≠ n`,
`b(k, n) = b(k − 1, n) · ((n − (k − 1))/k) · ((λ/n)/(1 − λ/n))`, and
`((n − (k − 1))/k)((λ/n)/(1 − λ/n)) = (λ − (k − 1)λ/n)/(k − λk/n)`. -/
theorem eq_9_42 (lam : ℝ) {n k : ℕ} (hk : k + 1 ≤ n) (hn : (n : ℝ) ≠ lam) :
    binomialProb lam n (k + 1) =
        binomialProb lam n k * (((n : ℝ) - k) / (k + 1) * ((lam / n) / (1 - lam / n))) ∧
      ((n : ℝ) - k) / (k + 1) * ((lam / n) / (1 - lam / n)) =
        (lam - k * lam / n) / ((k + 1) - lam * (k + 1) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have h1 : 1 - lam / n ≠ 0 := by
    intro h
    have h' : lam / n = 1 := by linarith
    rw [div_eq_one_iff_eq hn0] at h'
    exact hn h'.symm
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hchoose : ((n.choose (k + 1) : ℕ) : ℝ) * (k + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
    have := Nat.choose_succ_right_eq n k
    rw [show ((n : ℝ) - k) = ((n - k : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]]
    exact_mod_cast this
  have hpow : (1 - lam / n) ^ (n - k) = (1 - lam / n) ^ (n - (k + 1)) * (1 - lam / n) := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · simp only [binomialProb]
    rw [hpow]
    have hc : ((n.choose (k + 1) : ℕ) : ℝ) = (n.choose k : ℝ) * ((n : ℝ) - k) / (k + 1) := by
      rw [eq_div_iff hk1, hchoose]
    rw [hc]
    set p := lam / (n : ℝ)
    field_simp
    ring
  · field_simp

/-- AKMM, (9.43), p. 258: `p(0) = lim_{n→∞} b(0, n) = e^{−λ}`. -/
theorem eq_9_43 (lam : ℝ) :
    Tendsto (fun n : ℕ => binomialProb lam n 0) atTop (𝓝 (Real.exp (-lam))) := by
  simp only [eq_9_41]
  have h := Real.tendsto_one_add_div_pow_exp (-lam)
  simpa [neg_div, sub_eq_add_neg] using h

/-- AKMM, p. 258: `lim_{n→∞} b(k + 1, n)/b(k, n) = λ/(k + 1)`, in the form of the limit of the
ratio `(λ − kλ/n)/((k + 1) − λ(k + 1)/n)` of (9.42). -/
theorem poisson_ratio_limit (lam : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (lam - k * lam / n) / ((k + 1) - lam * (k + 1) / n)) atTop
      (𝓝 (lam / (k + 1))) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n : ℕ => lam - k * lam / n) atTop (𝓝 (lam - k * lam * 0)) := by
    refine tendsto_const_nhds.sub ((h0.const_mul (k * lam)).congr fun n => ?_)
    ring
  have hden : Tendsto (fun n : ℕ => ((k : ℝ) + 1) - lam * (k + 1) / n) atTop
      (𝓝 ((k + 1) - lam * (k + 1) * 0)) := by
    refine tendsto_const_nhds.sub ((h0.const_mul (lam * (k + 1))).congr fun n => ?_)
    ring
  simp only [mul_zero, sub_zero] at hnum hden
  exact hnum.div hden (by positivity)

/-- AKMM, p. 259: **the Poisson limit** (law of small numbers). For every `k`,
`b(k, n) → p(k) = e^{−λ}λ^k/k!` as `n → ∞`, by applying the ratio limit for `k = 1, 2, …`. -/
theorem poisson_limit (lam : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => binomialProb lam n k) atTop
      (𝓝 (Real.exp (-lam) * lam ^ k / k.factorial)) := by
  induction k with
  | zero => simpa using eq_9_43 lam
  | succ k ih =>
    have hprod := ih.mul (poisson_ratio_limit lam k)
    have hlim : Real.exp (-lam) * lam ^ k / k.factorial * (lam / (k + 1)) =
        Real.exp (-lam) * lam ^ (k + 1) / (k + 1).factorial := by
      push_cast [Nat.factorial_succ]
      field_simp
      ring
    rw [hlim] at hprod
    refine hprod.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_gt |lam|
    filter_upwards [eventually_ge_atTop (k + 1), eventually_gt_atTop N] with n hn hnN
    have hne : (n : ℝ) ≠ lam := by
      intro h
      have : (N : ℝ) < n := by exact_mod_cast hnN
      have := le_abs_self lam
      linarith
    have e := eq_9_42 lam hn hne
    rw [e.1, e.2]

/-- AKMM, p. 259: the Poisson probabilities `p(k) = e^{−λ}λ^k/k!` sum to `1` and have mean `λ`. -/
theorem poisson_sum_mean (lam : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / k.factorial) 1 ∧
      HasSum (fun k : ℕ => (k : ℝ) * (Real.exp (-lam) * lam ^ k / k.factorial)) lam := by
  have hexp : HasSum (fun n : ℕ => lam ^ n / (n.factorial : ℝ)) (Real.exp lam) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) lam
    rwa [← Real.exp_eq_exp_ℝ] at this
  have h1 : HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / k.factorial) 1 := by
    have := hexp.mul_left (Real.exp (-lam))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    refine this.congr_fun fun k => ?_
    ring
  refine ⟨h1, ?_⟩
  have h2 := (h1.mul_left lam)
  rw [mul_one] at h2
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  refine h2.congr_fun fun k => ?_
  push_cast [Nat.factorial_succ, pow_succ]
  field_simp

/-- AKMM, p. 259: on an interval of length `T` with trials of length `Δ = T/n` and success
probability `λΔ = λT/n`, the number of successes converges in distribution to the Poisson
distribution with parameter `λT`, whose mean is `λT`. -/
theorem poisson_limit_interval (lam T : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => binomialProb (lam * T) n k) atTop
      (𝓝 (Real.exp (-(lam * T)) * (lam * T) ^ k / k.factorial)) ∧
      HasSum (fun k : ℕ => (k : ℝ) * (Real.exp (-(lam * T)) * (lam * T) ^ k / k.factorial))
        (lam * T) :=
  ⟨poisson_limit (lam * T) k, (poisson_sum_mean (lam * T)).2⟩

/-- AKMM, p. 259: the probability of no success during `(t, t + T]` is `p(0) = e^{−λT}`, and it
is memoryless: `e^{−λ(s + T)}/e^{−λs} = e^{−λT}` (Sargent–Stachurski, Exercise 10.1.1). -/
theorem poisson_survival_memoryless (lam s T : ℝ) :
    Real.exp (-(lam * T)) * (lam * T) ^ 0 / (Nat.factorial 0) = Real.exp (-lam * T) ∧
      Real.exp (-lam * (s + T)) / Real.exp (-lam * s) = Real.exp (-lam * T) := by
  refine ⟨by simp [neg_mul], (SargentStachurski.ContinuousTime.exp_memoryless lam s T).2⟩

/-- AKMM, p. 259, "the Poisson process is a memoryless process": a decreasing survival function
`G` with `0 < G < 1` on `(0, ∞)` is memoryless, `G(s + t) = G(s)G(t)`, if and only if it is
exponential, `G(t) = e^{−λt}` with `λ > 0` (Sargent–Stachurski, Lemma 10.1.1, imported). -/
theorem poisson_memoryless_iff_exponential {G : ℝ → ℝ} (hanti : AntitoneOn G (Set.Ioi 0))
    (hG : ∀ t > 0, 0 < G t ∧ G t < 1) :
    (∀ s > 0, ∀ t > 0, G (s + t) = G s * G t) ↔ ∃ lam > 0, ∀ t > 0, G t = Real.exp (-lam * t) := by
  refine ⟨SargentStachurski.ContinuousTime.eq_exp_of_memoryless hanti hG, ?_⟩
  rintro ⟨lam, -, hlam⟩ s hs t ht
  rw [hlam s hs, hlam t ht, hlam (s + t) (by linarith)]
  exact (SargentStachurski.ContinuousTime.exp_memoryless lam s t).1

/-- AKMM, p. 259: with a time-varying rate `λ(s)` (continuous), the survival probability `S`
from `t` — defined by the hazard equation `Ṡ(s) = −λ(s)S(s)`, `S(t) = 1` — is
`S(t + T) = e^{−∫_t^{t+T} λ(s)ds}`. -/
theorem poisson_survival_time_varying {lam S : ℝ → ℝ} (hlam : Continuous lam) {t T : ℝ}
    (hT : 0 ≤ T) (hS : ∀ s, t ≤ s → HasDerivAt S (-lam s * S s) s) (hS0 : S t = 1) :
    S (t + T) = Real.exp (-∫ s in t..t + T, lam s) := by
  set a : ℝ → ℝ := fun x => S (t + x)
  have ha : ∀ x, 0 ≤ x → HasDerivAt a (0 + (fun y => -lam (t + y)) x * a x - 0) x := by
    intro x hx
    have h := (hS (t + x) (by linarith)).comp x ((hasDerivAt_id x).const_add t)
    simp only [mul_one] at h
    convert h using 1
    · rfl
    · simp only [a]
      ring
  have hcont : Continuous fun y => -lam (t + y) :=
    (hlam.comp (continuous_const.add continuous_id)).neg
  have h := appendix_9A3_continuous_budget hcont continuous_const continuous_const ha hT
  simp only [sub_self, mul_zero, intervalIntegral.integral_zero, add_zero, a, add_zero,
    hS0] at h
  have hsub : ∫ y in (0 : ℝ)..T, -lam (t + y) = -∫ s in t..t + T, lam s := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_add_left (fun s => lam s) t]
    simp
  rw [hsub, neg_neg] at h
  have hE := Real.exp_pos (∫ s in t..t + T, lam s)
  calc S (t + T) = Real.exp (-∫ s in t..t + T, lam s) *
        (Real.exp (∫ s in t..t + T, lam s) * S (t + T)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-∫ s in t..t + T, lam s) := by rw [h, mul_one]

/-- AKMM, p. 259: the expected remaining duration of a job with separation rate `σ > 0` is
`∫_0^∞ tσe^{−σt}dt = 1/σ`, and the density `σe^{−σt}` integrates to `1`. -/
theorem poisson_expected_duration {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-σ * t) * σ = 1 / σ ∧
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-σ * t) * σ = 1 := by
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := σ) two_pos hσ
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := σ) one_pos hσ
  have hG2 : Real.Gamma 2 = 1 := Real.Gamma_two
  have hG1 : Real.Gamma 1 = 1 := Real.Gamma_one
  constructor
  · have e : ∀ t : ℝ, t * Real.exp (-σ * t) * σ = σ * (t ^ ((2 : ℝ) - 1) * Real.exp (-(σ * t))) :=
      fun t => by norm_num; ring_nf
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul, h2, hG2, Real.rpow_two]
    field_simp
  · have e : ∀ t : ℝ, Real.exp (-σ * t) * σ = σ * (t ^ ((1 : ℝ) - 1) * Real.exp (-(σ * t))) :=
      fun t => by norm_num; ring_nf
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul, h1, hG1, Real.rpow_one]
    field_simp

end AKMM.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Unemployment flows

AKMM, §9.4 (pp. 259–260): (9.44) `u̇ = (N − u)σ − uλ` with separation rate `σ > 0`, job-finding
rate `λ > 0` and population `N`.

* The steady state `ū = σN/(σ + λ)` is the unique rest point (`unemployment_steady_state`).
* Every solution is `u(t) = ū + (u(0) − ū)e^{−(σ+λ)t}` (existence and uniqueness, the latter
  by Sargent–Stachurski's Example 10.1.1); so unemployment converges to `ū` from every initial
  value, monotonically in distance (`unemployment_solution`, `unemployment_unique`,
  `unemployment_converges`).
* The steady-state unemployment rate `ū/N = σ/(σ + λ)` is strictly increasing in `σ` and
  strictly decreasing in `λ` (`unemployment_rate_comparative_statics`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, p. 260: the steady state of (9.44): `(N − u)σ − uλ = 0` iff `u = ū = σN/(σ + λ)`; and
the rate is `ū/N = σ/(σ + λ)`. -/
theorem unemployment_steady_state {N σ lam u : ℝ} (hσ : 0 < σ) (hlam : 0 < lam) (hN : N ≠ 0) :
    ((N - u) * σ - u * lam = 0 ↔ u = σ * N / (σ + lam)) ∧
      σ * N / (σ + lam) / N = σ / (σ + lam) := by
  have hs : σ + lam ≠ 0 := by positivity
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [eq_div_iff hs]; linarith
  · rw [h]; field_simp; ring
  · field_simp

/-- AKMM, (9.44), p. 260: `u(t) = ū + (u₀ − ū)e^{−(σ+λ)t}` solves `u̇ = (N − u)σ − uλ` with
`u(0) = u₀`. -/
theorem unemployment_solution (N σ lam u₀ t : ℝ) (hs : σ + lam ≠ 0) :
    HasDerivAt (fun s => σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) *
        Real.exp (-(σ + lam) * s))
      ((N - (σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t))) * σ -
        (σ * N / (σ + lam) + (u₀ - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t)) * lam) t := by
  have h := (SargentStachurski.ContinuousTime.hasDerivAt_exp_mul (-(σ + lam))
    (u₀ - σ * N / (σ + lam)) t).const_add (σ * N / (σ + lam))
  convert h using 1
  · funext s; ring
  · field_simp
    ring

/-- AKMM, (9.44), p. 260: every solution of `u̇ = (N − u)σ − uλ` on `[0, ∞)` is
`u(t) = ū + (u(0) − ū)e^{−(σ+λ)t}`. -/
theorem unemployment_unique {N σ lam : ℝ} {u : ℝ → ℝ} (hs : σ + lam ≠ 0)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u ((N - u t) * σ - u t * lam) t) {t : ℝ} (ht : 0 ≤ t) :
    u t = σ * N / (σ + lam) + (u 0 - σ * N / (σ + lam)) * Real.exp (-(σ + lam) * t) := by
  set ub := σ * N / (σ + lam)
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun x => u x - ub) (-(σ + lam) * (u s - ub)) s := by
    intro s hs'
    convert (hu s hs').sub_const ub using 1
    simp only [ub]
    field_simp
    ring
  have h := SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt rfl hd ht
  linarith

/-- AKMM, p. 260: "unemployment converges to the steady-state value, regardless of the initial
unemployment": for `σ, λ > 0` every solution of (9.44) tends to `ū`, and its distance from `ū`
is nonincreasing. -/
theorem unemployment_converges {N σ lam : ℝ} {u : ℝ → ℝ} (hσ : 0 < σ) (hlam : 0 < lam)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u ((N - u t) * σ - u t * lam) t) :
    Tendsto u atTop (𝓝 (σ * N / (σ + lam))) ∧
      AntitoneOn (fun t => |u t - σ * N / (σ + lam)|) (Set.Ici 0) := by
  have hs : 0 < σ + lam := by linarith
  have hform := fun t (ht : 0 ≤ t) => unemployment_unique hs.ne' hu ht
  refine ⟨?_, fun s hs' t ht hst => ?_⟩
  · have h := ((mangasarian_exp_neg_tendsto hs).const_mul (u 0 - σ * N / (σ + lam))).const_add
      (σ * N / (σ + lam))
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hform t ht]
  · simp only
    rw [hform s hs', hform t ht, add_sub_cancel_left, add_sub_cancel_left, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)

/-- AKMM, p. 260: the steady-state unemployment rate `σ/(σ + λ)` is strictly increasing in the
separation rate `σ` and strictly decreasing in the job-finding rate `λ`. -/
theorem unemployment_rate_comparative_statics {lam σ : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    StrictMonoOn (fun x => x / (x + lam)) (Set.Ioi 0) ∧
      StrictAntiOn (fun y => σ / (σ + y)) (Set.Ioi 0) := by
  refine ⟨fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
  · simp only [Set.mem_Ioi] at hx hy
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · simp only [Set.mem_Ioi] at hx hy
    exact div_lt_div_of_pos_left hσ (by linarith) (by linarith)

end AKMM.ContinuousTime

set_option linter.style.longLine false
#print axioms AKMM.ContinuousTime.eq_9_2
#print axioms AKMM.ContinuousTime.growthRates_discrete_unique
#print axioms AKMM.ContinuousTime.eq_9_4
#print axioms AKMM.ContinuousTime.eq_9_4_unique
#print axioms AKMM.ContinuousTime.eq_9_3_unique
#print axioms AKMM.ContinuousTime.eq_9_5
#print axioms AKMM.ContinuousTime.growthRates_log_exponential
#print axioms AKMM.ContinuousTime.growthRates_growth_accounting
#print axioms AKMM.ContinuousTime.growthRates_growth_accounting_rate
#print axioms AKMM.ContinuousTime.growthRates_log_difference
#print axioms AKMM.ContinuousTime.growthRates_log_one_add_approx
#print axioms AKMM.ContinuousTime.appendix_9A1
#print axioms AKMM.ContinuousTime.appendix_9A2_exp
#print axioms AKMM.ContinuousTime.appendix_9A2_log
#print axioms AKMM.ContinuousTime.discreteDiscount
#print axioms AKMM.ContinuousTime.discreteBudget_discount_pos
#print axioms AKMM.ContinuousTime.discreteBudget_const_discount
#print axioms AKMM.ContinuousTime.appendix_9A3_discrete_budget
#print axioms AKMM.ContinuousTime.appendix_9A3_discrete_lbc
#print axioms AKMM.ContinuousTime.appendix_9A3_discrete_limit
#print axioms AKMM.ContinuousTime.appendix_9A3_discrete_lbc_infinite
#print axioms AKMM.ContinuousTime.appendix_9A3_discrete_npg_iff_lbc
#print axioms AKMM.ContinuousTime.discreteBudget_finite_npg_iff
#print axioms AKMM.ContinuousTime.discreteBudget_npg_printed_example
#print axioms AKMM.ContinuousTime.discreteBudget_npg_counterexample
#print axioms AKMM.ContinuousTime.discreteHamiltonian
#print axioms AKMM.ContinuousTime.discreteLagrangian
#print axioms AKMM.ContinuousTime.discreteHamiltonian_lagrangian
#print axioms AKMM.ContinuousTime.eq_9_8
#print axioms AKMM.ContinuousTime.eq_9_9
#print axioms AKMM.ContinuousTime.eq_9_10
#print axioms AKMM.ContinuousTime.eq_9_13
#print axioms AKMM.ContinuousTime.eq_9_14
#print axioms AKMM.ContinuousTime.discreteHamiltonian_marginal
#print axioms AKMM.ContinuousTime.discreteHamiltonian_tvc_iff
#print axioms AKMM.ContinuousTime.discreteHamiltonian_finite_sufficient
#print axioms AKMM.ContinuousTime.discreteOptimality_pc
#print axioms AKMM.ContinuousTime.discreteOptimality_pa
#print axioms AKMM.ContinuousTime.discreteOptimality_perturb_budget
#print axioms AKMM.ContinuousTime.discreteOptimality_perturb_sum
#print axioms AKMM.ContinuousTime.discreteOptimality_euler_of_localMax
#print axioms AKMM.ContinuousTime.discreteOptimality_perturb_pos
#print axioms AKMM.ContinuousTime.discreteHamiltonian_euler_necessary
#print axioms AKMM.ContinuousTime.discreteHamiltonian_tvc_necessary
#print axioms AKMM.ContinuousTime.discreteHamiltonian_tvc_infinite_iff
#print axioms AKMM.ContinuousTime.discreteHamiltonian_infinite_sufficient
#print axioms AKMM.ContinuousTime.discreteHamiltonian_constant_path_optimal
#print axioms AKMM.ContinuousTime.discreteHamiltonian_euler_necessary_infinite
#print axioms AKMM.ContinuousTime.eq_9_18
#print axioms AKMM.ContinuousTime.continuousBudget_discount_limit
#print axioms AKMM.ContinuousTime.continuousBudget_npg_discount_limit
#print axioms AKMM.ContinuousTime.continuousBudget_hasDerivAt_cumulative
#print axioms AKMM.ContinuousTime.appendix_9A3_integrating_factor
#print axioms AKMM.ContinuousTime.appendix_9A3_continuous_budget
#print axioms AKMM.ContinuousTime.appendix_9A3_continuous_budget_forward
#print axioms AKMM.ContinuousTime.appendix_9A3_printed_budget_false
#print axioms AKMM.ContinuousTime.appendix_9A3_continuous_npg_iff_lbc
#print axioms AKMM.ContinuousTime.eq_9_17_budget
#print axioms AKMM.ContinuousTime.productLimits_riemann
#print axioms AKMM.ContinuousTime.productLimits_product
#print axioms AKMM.ContinuousTime.appendix_9A3_product_limit
#print axioms AKMM.ContinuousTime.productLimits_survival
#print axioms AKMM.ContinuousTime.ctHamiltonian
#print axioms AKMM.ContinuousTime.ctCurrentHamiltonian
#print axioms AKMM.ContinuousTime.eq_9_20
#print axioms AKMM.ContinuousTime.eq_9_21
#print axioms AKMM.ContinuousTime.continuousHamiltonian_integration_by_parts
#print axioms AKMM.ContinuousTime.continuousHamiltonian_present_current
#print axioms AKMM.ContinuousTime.eq_9_22
#print axioms AKMM.ContinuousTime.eq_9_23
#print axioms AKMM.ContinuousTime.eq_9_26
#print axioms AKMM.ContinuousTime.continuousHamiltonian_crra_coefficient_pos
#print axioms AKMM.ContinuousTime.crraUtility
#print axioms AKMM.ContinuousTime.continuousHamiltonian_crra_derivs
#print axioms AKMM.ContinuousTime.continuousHamiltonian_crra_relative_risk_aversion
#print axioms AKMM.ContinuousTime.continuousHamiltonian_discrete_euler_linearized
#print axioms AKMM.ContinuousTime.continuousHamiltonian_discrete_euler_remainder
#print axioms AKMM.ContinuousTime.mangasarian_exp_neg_tendsto
#print axioms AKMM.ContinuousTime.mangasarian
#print axioms AKMM.ContinuousTime.mangasarian_catching_up
#print axioms AKMM.ContinuousTime.mangasarian_consumption_saving
#print axioms AKMM.ContinuousTime.mangasarian_consumption_saving_constant
#print axioms AKMM.ContinuousTime.mangasarian_planner
#print axioms AKMM.ContinuousTime.mangasarian_planner_steady_state
#print axioms AKMM.ContinuousTime.eq_9_31
#print axioms AKMM.ContinuousTime.solowContinuous_intensive
#print axioms AKMM.ContinuousTime.eq_9_32
#print axioms AKMM.ContinuousTime.solowContinuous_phase_line
#print axioms AKMM.ContinuousTime.solowContinuous_convergence
#print axioms AKMM.ContinuousTime.solowContinuous_income_per_capita_growth
#print axioms AKMM.ContinuousTime.eq_9_35
#print axioms AKMM.ContinuousTime.ramseyPlanner_phase_signs
#print axioms AKMM.ContinuousTime.ramseyPlanner_modified_golden_rule
#print axioms AKMM.ContinuousTime.ramseyPlanner_tvc_of_convergent
#print axioms AKMM.ContinuousTime.ramseyPlanner_zero_capital_infeasible
#print axioms AKMM.ContinuousTime.appendix_9A4_marginal_utility
#print axioms AKMM.ContinuousTime.appendix_9A4_tvc_iff
#print axioms AKMM.ContinuousTime.appendix_9A4_saddle_tvc
#print axioms AKMM.ContinuousTime.appendix_9A4_below_saddle_violates_tvc
#print axioms AKMM.ContinuousTime.appendix_9A4_below_saddle_instance
#print axioms AKMM.ContinuousTime.ramseySaddle_power_hasDerivAt
#print axioms AKMM.ContinuousTime.ramseySaddle_power_derivs
#print axioms AKMM.ContinuousTime.ramseySaddle_power_props
#print axioms AKMM.ContinuousTime.ramseySaddle_primitives
#print axioms AKMM.ContinuousTime.ramseySaddle_of_interior
#print axioms AKMM.ContinuousTime.ramseySaddle_path
#print axioms AKMM.ContinuousTime.ramseySaddle_crra_cobbDouglas
#print axioms AKMM.ContinuousTime.eq_9_37
#print axioms AKMM.ContinuousTime.market_household_optimal
#print axioms AKMM.ContinuousTime.market_firm_marginal_products
#print axioms AKMM.ContinuousTime.market_firm_optimal
#print axioms AKMM.ContinuousTime.market_equilibrium_planner_system
#print axioms AKMM.ContinuousTime.market_planner_is_equilibrium
#print axioms AKMM.ContinuousTime.binomialProb
#print axioms AKMM.ContinuousTime.poisson_binomial_sum
#print axioms AKMM.ContinuousTime.poisson_expected_successes
#print axioms AKMM.ContinuousTime.eq_9_41
#print axioms AKMM.ContinuousTime.eq_9_42
#print axioms AKMM.ContinuousTime.eq_9_43
#print axioms AKMM.ContinuousTime.poisson_ratio_limit
#print axioms AKMM.ContinuousTime.poisson_limit
#print axioms AKMM.ContinuousTime.poisson_sum_mean
#print axioms AKMM.ContinuousTime.poisson_limit_interval
#print axioms AKMM.ContinuousTime.poisson_survival_memoryless
#print axioms AKMM.ContinuousTime.poisson_memoryless_iff_exponential
#print axioms AKMM.ContinuousTime.poisson_survival_time_varying
#print axioms AKMM.ContinuousTime.poisson_expected_duration
#print axioms AKMM.ContinuousTime.unemployment_steady_state
#print axioms AKMM.ContinuousTime.unemployment_solution
#print axioms AKMM.ContinuousTime.unemployment_unique
#print axioms AKMM.ContinuousTime.unemployment_converges
#print axioms AKMM.ContinuousTime.unemployment_rate_comparative_statics
