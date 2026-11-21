/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ContinuousTime.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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
