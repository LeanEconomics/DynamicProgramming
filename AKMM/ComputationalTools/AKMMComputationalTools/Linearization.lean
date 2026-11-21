/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

/-!
# The log-linearised stochastic growth model with labour

AKMM, §10.5.2, (10.12), p. 275, and §10.6, (10.13)–(10.17), (10.27), pp. 277–281.

* (10.12): the first-order condition of the static labour choice has at most one root in `H`
  (its left side is strictly decreasing), so `H(z, K, K′)` is well defined (`labour_foc_unique`).
* Log-linearisation (variables `x_t = log(X_t/X̄)`): output
  `e^zK^αH^{1−α} = K̄^αH̄^{1−α}e^{z+αk+(1−α)h}`
  (`rbc_output_exp`); the first-order expansions of (10.9), of the labour supply condition (10.14)
  and of the Euler equation (10.13) at the steady state (`loglin_resource`, `loglin_labour`,
  `loglin_euler`, the last using `β(1 − δ + αK̄^{α−1}H̄^{1−α}) = 1` and, as in fn. 7, certainty
  equivalence).
* (10.15): `h_t = θ(z_t + αk_t − c_t)` with `θ = (1 − H̄)/(H̄(1 − α) + α)` (`eq_10_15`).
* (10.16) (`eq_10_16`) and (10.17), corrected: the coefficient of `z_t` is
  `βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ` (`eq_10_17`); the printed coefficient lacks the factor `α`
  (`eq_10_17_printed_counterexample`), and so does the second entry of `E` in (10.27)
  (`eq_10_27`).
-/

namespace AKMM.ComputationalTools

open Real

/-! ### (10.12): the static labour choice -/

/-- AKMM, (10.12), p. 275: the derivative in `H` of
`(1 − φ)log(AH^{1−α} + R) + φlog(1 − H)`, with `A = e^zK^α` and `R = (1 − δ)K − K′`. -/
noncomputable def labourFoc (φ α A R H : ℝ) : ℝ :=
  (1 - φ) * ((1 - α) * A * H ^ (-α)) / (A * H ^ (1 - α) + R) - φ / (1 - H)

/-- AKMM, (10.12), p. 275: "the solution to this problem can be written as `H(z, K, K′)`": on the
set of `H ∈ (0, 1)` with positive consumption, the first-order condition is strictly decreasing
in `H`, so it has at most one root. -/
theorem labour_foc_unique {φ α A R : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) {H₁ H₂ : ℝ} (h1 : H₁ ∈ Set.Ioo 0 1) (h2 : H₂ ∈ Set.Ioo 0 1)
    (hc1 : 0 < A * H₁ ^ (1 - α) + R) (hlt : H₁ < H₂) :
    labourFoc φ α A R H₂ < labourFoc φ α A R H₁ := by
  have hc2 : A * H₁ ^ (1 - α) + R < A * H₂ ^ (1 - α) + R := by
    have := Real.rpow_lt_rpow h1.1.le hlt (by linarith : 0 < 1 - α)
    nlinarith
  have hp : H₂ ^ (-α) < H₁ ^ (-α) := Real.rpow_lt_rpow_of_neg h1.1 hlt (by linarith)
  have hp0 : 0 < H₂ ^ (-α) := Real.rpow_pos_of_pos h2.1 _
  have hfirst : (1 - φ) * ((1 - α) * A * H₂ ^ (-α)) / (A * H₂ ^ (1 - α) + R) <
      (1 - φ) * ((1 - α) * A * H₁ ^ (-α)) / (A * H₁ ^ (1 - α) + R) := by
    have hk : 0 < (1 - φ) * ((1 - α) * A) := by
      have : 0 < 1 - φ := by linarith
      have : 0 < 1 - α := by linarith
      positivity
    rw [show (1 - φ) * ((1 - α) * A * H₂ ^ (-α)) = (1 - φ) * ((1 - α) * A) * H₂ ^ (-α) by ring,
      show (1 - φ) * ((1 - α) * A * H₁ ^ (-α)) = (1 - φ) * ((1 - α) * A) * H₁ ^ (-α) by ring]
    rw [div_lt_div_iff₀ (hc1.trans hc2) hc1]
    have := mul_lt_mul_of_pos_left hp hk
    nlinarith [mul_pos hk hp0]
  have hsecond : φ / (1 - H₁) < φ / (1 - H₂) := by
    apply div_lt_div_of_pos_left hφ0 (by linarith [h2.2]) (by linarith)
  unfold labourFoc
  linarith

/-! ### Log-linearisation -/

/-- AKMM, p. 277: output in log deviations,
`e^z(K̄e^k)^α(H̄e^h)^{1−α} = K̄^αH̄^{1−α}e^{z+αk+(1−α)h}`. -/
theorem rbc_output_exp {α Kbar Hbar : ℝ} (hK : 0 < Kbar) (hH : 0 < Hbar) (z k h : ℝ) :
    exp z * (Kbar * exp k) ^ α * (Hbar * exp h) ^ (1 - α) =
      Kbar ^ α * Hbar ^ (1 - α) * exp (z + α * k + (1 - α) * h) := by
  rw [Real.mul_rpow hK.le (exp_pos k).le, Real.mul_rpow hH.le (exp_pos h).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  ring_nf

/-- Derivative at `0` of `ε ↦ c·e^{εx}`. -/
theorem loglin_exp_deriv (c x : ℝ) : HasDerivAt (fun ε => c * exp (ε * x)) (c * x) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const x).exp.const_mul c
  simpa using h

/-- AKMM, p. 277, the first log-linearised equation: along any direction
`(k′, c, z, k, h)` of log deviations, the resource constraint (10.9),
`K̄e^{k′} + C̄e^c − K̄^αH̄^{1−α}e^{z+αk+(1−α)h} − (1 − δ)K̄e^k`, has derivative
`K̄k′ + C̄c − K̄^αH̄^{1−α}(z + αk + (1 − α)h) − (1 − δ)K̄k` at the steady state. -/
theorem loglin_resource (α δ Kbar Hbar Cbar k' c z k h : ℝ) :
    HasDerivAt (fun ε => Kbar * exp (ε * k') + Cbar * exp (ε * c) -
        Kbar ^ α * Hbar ^ (1 - α) * exp (ε * (z + α * k + (1 - α) * h)) -
        (1 - δ) * Kbar * exp (ε * k))
      (Kbar * k' + Cbar * c - Kbar ^ α * Hbar ^ (1 - α) * (z + α * k + (1 - α) * h) -
        (1 - δ) * Kbar * k) 0 :=
  (((loglin_exp_deriv Kbar k').add (loglin_exp_deriv Cbar c)).sub
    (loglin_exp_deriv _ _)).sub (loglin_exp_deriv _ _)

/-- AKMM, p. 277, the labour supply condition (10.14) in logs: the term `−log(1 − H̄e^{εh})` has
derivative `H̄h/(1 − H̄)` at `ε = 0` (the other terms of the log of (10.14) are linear in the log
deviations). -/
theorem loglin_labour {Hbar : ℝ} (hH1 : Hbar < 1) (h : ℝ) :
    HasDerivAt (fun ε => -Real.log (1 - Hbar * exp (ε * h))) (Hbar * h / (1 - Hbar)) 0 := by
  have hd := (loglin_exp_deriv Hbar h).const_sub 1
  have hpos : (1 - Hbar * exp (0 * h)) ≠ 0 := by simp; linarith
  have := (hd.log hpos).neg
  convert this using 1
  simp
  ring

/-- AKMM, p. 277, the Euler equation (10.13) in logs (certainty equivalence, fn. 7): the term
`log(1 − δ + R̄e^{εx})`, with `R̄ = αK̄^{α−1}H̄^{1−α}` and `x = z′ + (α − 1)k′ + (1 − α)h′`, has
derivative `βR̄x` at the steady state `β(1 − δ + R̄) = 1`. -/
theorem loglin_euler {β δ Rbar : ℝ} (hss : β * (1 - δ + Rbar) = 1) (x : ℝ) :
    HasDerivAt (fun ε => Real.log (1 - δ + Rbar * exp (ε * x))) (β * Rbar * x) 0 := by
  have hd := (loglin_exp_deriv Rbar x).const_add (1 - δ)
  have hne : 1 - δ + Rbar ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hss; exact zero_ne_one hss
  have hpos : (1 - δ + Rbar * exp (0 * x)) ≠ 0 := by simpa using hne
  have := hd.log hpos
  convert this using 1
  simp only [zero_mul, exp_zero, mul_one]
  have hβ : β = (1 - δ + Rbar)⁻¹ := eq_inv_of_mul_eq_one_left hss
  rw [hβ]
  field_simp

/-- AKMM, p. 277: `θ ≡ (1 − H̄)/(H̄(1 − α) + α)`. -/
noncomputable def theta (α Hbar : ℝ) : ℝ := (1 - Hbar) / (Hbar * (1 - α) + α)

/-- AKMM, (10.15), p. 277: the log-linearised labour supply condition
`−c + z + αk − αh = (H̄/(1 − H̄))h` is equivalent to `h = θ(z + αk − c)`. -/
theorem eq_10_15 {α Hbar : ℝ} (hα0 : 0 < α) (hH0 : 0 < Hbar) (hH1 : Hbar < 1)
    (z k c h : ℝ) :
    -c + z + α * k - α * h = Hbar / (1 - Hbar) * h ↔ h = theta α Hbar * (z + α * k - c) := by
  have h1 : 0 < 1 - Hbar := by linarith
  have h2 : 0 < Hbar * (1 - α) + α := by nlinarith
  unfold theta
  rw [div_mul_eq_mul_div, eq_div_iff h1.ne', div_mul_eq_mul_div, eq_comm, eq_div_iff h2.ne']
  constructor <;> intro h <;> linarith

/-- AKMM, (10.16), p. 277: substituting (10.15) into the log-linearised resource constraint. -/
theorem eq_10_16 {α δ Kbar Hbar Cbar θ k' c z k h : ℝ}
    (hres : Kbar * k' + Cbar * c =
      Kbar ^ α * Hbar ^ (1 - α) * (z + α * k + (1 - α) * h) + (1 - δ) * Kbar * k)
    (hh : h = θ * (z + α * k - c)) :
    Kbar * k' = Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)) * z +
      (Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar) * k -
      (Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar) * c := by
  subst hh
  linear_combination hres

/-- AKMM, (10.17), p. 278, corrected: substituting `h′ = θ(z′ + αk′ − c′)` into the log-linearised
Euler equation `−c = βαK̄^{α−1}H̄^{1−α}(z′ + (α − 1)k′ + (1 − α)h′) − c′`, with expectations
`E_t c′` and `E_t z′ = ρz` (the equation is linear, so it holds for the expectations), gives
`βαK̄^{α−1}H̄^{1−α}(1 − α)(1 − θα)k′ + (βαθ(1 − α)K̄^{α−1}H̄^{1−α} + 1)E_t c′
 = βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρz + c`. -/
theorem eq_10_17 {α β ρ Kbar Hbar θ k' Ec' Eh' z c : ℝ}
    (heul : -c = β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) *
      (ρ * z + (α - 1) * k' + (1 - α) * Eh') - Ec')
    (hh : Eh' = θ * (ρ * z + α * k' - Ec')) :
    β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α) * k' +
        (β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1) * Ec' =
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ * z + c := by
  subst hh
  linear_combination heul

/-- AKMM, (10.17), p. 278, as printed: the coefficient of `z_t` is printed
`β(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`; it differs from the derived `βα(1 + θ(1 − α))K̄^{α−1}H̄^{1−α}ρ`
(`eq_10_17`) whenever `α ≠ 1` and the other factors are nonzero (in particular for
`α ∈ (0, 1)`, `β, ρ, K̄, H̄ > 0`, `θ ≥ 0`). -/
theorem eq_10_17_printed_counterexample {α β ρ Kbar Hbar θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hρ : 0 < ρ) (hK : 0 < Kbar) (hH : 0 < Hbar) (hθ : 0 ≤ θ) :
    β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ ≠
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ := by
  have h1 : 0 < 1 + θ * (1 - α) := by nlinarith
  have hK' : 0 < Kbar ^ (α - 1) := Real.rpow_pos_of_pos hK _
  have hH' : 0 < Hbar ^ (1 - α) := Real.rpow_pos_of_pos hH _
  have hpos : 0 < β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ := by positivity
  intro h
  have : β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ =
      α * (β * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ) := by ring
  rw [this] at h
  nlinarith

/-- AKMM, (10.27), pp. 280–281: the matrices `B`, `A` and (corrected) `E` of the log-linearised
growth model, with `Y = K̄^αH̄^{1−α}` and `Q = βαK̄^{α−1}H̄^{1−α}`. -/
noncomputable def rbcB (α β Kbar Hbar θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kbar, 0;
    β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α),
      β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1]

/-- The matrix `A` of (10.27). -/
noncomputable def rbcA (α δ Kbar Hbar Cbar θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar,
      -(Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar);
    0, 1]

/-- The vector `E` of (10.27), with the factor `α` restored in its second entry. -/
noncomputable def rbcE (α β ρ Kbar Hbar θ : ℝ) : Fin 2 → ℝ :=
  ![Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)),
    β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ]

/-- AKMM, (10.27), p. 281: "In matrix form, (10.16) and (10.17) can be expressed as
`B[k_{t+1}; E_t c_{t+1}] = A[k_t; c_t] + Ez_t`" (with `E` corrected). -/
theorem eq_10_27 (α β δ ρ Kbar Hbar Cbar θ k' Ec' k c z : ℝ) :
    (rbcB α β Kbar Hbar θ).mulVec ![k', Ec'] =
        (rbcA α δ Kbar Hbar Cbar θ).mulVec ![k, c] + z • rbcE α β ρ Kbar Hbar θ ↔
      (Kbar * k' = Kbar ^ α * Hbar ^ (1 - α) * (1 + θ * (1 - α)) * z +
        (Kbar ^ α * Hbar ^ (1 - α) * α * (1 + θ * (1 - α)) + (1 - δ) * Kbar) * k -
        (Kbar ^ α * Hbar ^ (1 - α) * θ * (1 - α) + Cbar) * c) ∧
      (β * α * Kbar ^ (α - 1) * Hbar ^ (1 - α) * (1 - α) * (1 - θ * α) * k' +
        (β * α * θ * (1 - α) * Kbar ^ (α - 1) * Hbar ^ (1 - α) + 1) * Ec' =
      β * α * (1 + θ * (1 - α)) * Kbar ^ (α - 1) * Hbar ^ (1 - α) * ρ * z + c) := by
  rw [funext_iff, Fin.forall_fin_two]
  simp only [rbcB, rbcA, rbcE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end AKMM.ComputationalTools
