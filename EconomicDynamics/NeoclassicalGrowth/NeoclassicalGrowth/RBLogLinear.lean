/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBModel
import NeoclassicalGrowth.Basics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module

/-!
# The log-linearised basic RBC model

Miao, §14.2, pp. 474–480, "Log-linearized System". `X̂` is the log deviation of `X_t` from its
steady-state value `X` (z̄ = 1). "Taking logarithms and total differentiation" is made precise as
the derivative at `s = 0` along the curve `X(s) = Xe^{sX̂}` (whose log deviation is `sX̂`); the
log-linearised equation is the vanishing of that derivative.

* (14.27) in logs: the derivative is `Ĉ + ζN̂ − (ẑ + αK̂ − αN̂)`, `ζ = N/(1 − N)`
  (`eq_14_27_loglin`), solved as (14.31) (`eq_14_31`).
* The resource constraint (14.23)–(14.24): the derivative is
  `CĈ + KK̂' − (1 − δ)KK̂ − Y(ẑ + αK̂ + (1 − α)N̂)` (`rb_resource_loglin`), solved for `K̂'`
  with the steady-state Euler equation `1 = β(αY/K + 1 − δ)` (`rb_resource_solved`), and with
  (14.31) substituted, (14.32) (`eq_14_32`).
* The Euler equation (14.26): the derivative of the integrand (`rb_euler_loglin`), the
  linearised equation `−Ĉ_t = −Ĉ_{t+1} + βα(Y/K)[ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}]`
  (`rb_euler_loglin_eq`), and with (14.31) substituted, (14.33), deterministically
  (`eq_14_33_det`) and with a conditional expectation operator `E_t` (`eq_14_33`).
* The labour market: log-linearised supply (14.36) `ζN̂ = −Ĉ + ŵ` (`eq_14_36_loglin`) and demand
  (14.37) `ŵ = ẑ + αK̂ − αN̂` (`eq_14_37`); their intersection (`rb_labour_market`); the supply
  curve slopes up and the demand curve down (`rb_labour_slopes`).
* Output `Ŷ = αK̂ + (1 − α)N̂ + ẑ` (`rb_output_loglin`), the rental rate `R̂_k = Ŷ − K̂`
  (`rb_rental_loglin`), investment from the resource constraint and from (14.24)
  (`rb_investment_loglin`).
* The stock return (p. 479): with `R^s = R_k + 1 − δ`, the log deviation is
  `R̂^s = (R_k/R^s)R̂_k = (1 − β(1 − δ))R̂_k` (`rb_stock_return_loglin`); the printed
  `R̂^s = R̂_k` is false for `δ < 1` (`rb_stock_return_printed_false`).
* The risk-free rate (p. 480): `r̂^f_{t+1} = E_tĈ_{t+1} − Ĉ_t` (`rb_riskfree_loglin`,
  `rb_riskfree_eq`, and with `E_t`, `rb_riskfree_E`).

The coefficients of (14.32)–(14.33) are `rb_p`, `rb_g`, `rb_q`, `rb_a`, `rb_b`, `rb_c`, written in
terms of `α`, `β`, `ζ` and the steady-state ratios `Y/K`, `C/K`.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-- `ζ = N/(1 − N)` (Miao, p. 475). -/
noncomputable def rb_zeta (N : ℝ) : ℝ := N / (1 - N)

/-- The coefficient of `K̂_t` in (14.32): `1/β + (1 − α)/(α + ζ)·αY/K`. -/
noncomputable def rb_p (α β ζ yk : ℝ) : ℝ := 1 / β + (1 - α) / (α + ζ) * α * yk

/-- The coefficient of `ẑ_t` in (14.32): `(Y/K)(1 + ζ)/(ζ + α)`. -/
noncomputable def rb_g (α ζ yk : ℝ) : ℝ := yk * (1 + ζ) / (ζ + α)

/-- Minus the coefficient of `Ĉ_t` in (14.32): `C/K + (1 − α)/(α + ζ)·Y/K`. -/
noncomputable def rb_q (α ζ yk ck : ℝ) : ℝ := ck + (1 - α) / (α + ζ) * yk

/-- `(1 − α)βα(Y/K)/(α + ζ)`, (14.33). -/
noncomputable def rb_a (α β ζ yk : ℝ) : ℝ := (1 - α) * β * α * yk / (α + ζ)

/-- `βα(Y/K)(1 + ζ)/(α + ζ)`, (14.33). -/
noncomputable def rb_b (α β ζ yk : ℝ) : ℝ := β * α * yk * (1 + ζ) / (α + ζ)

/-- `βα(1 − α)(Y/K)ζ/(α + ζ)`, (14.33). -/
noncomputable def rb_c (α β ζ yk : ℝ) : ℝ := β * α * (1 - α) * yk * ζ / (α + ζ)

/-! ### Exponential curves -/

theorem rb_hasDerivAt_exp_mul (x : ℝ) : HasDerivAt (fun s => Real.exp (s * x)) x 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).exp

theorem rb_Y_exp (α : ℝ) {z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_Y α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_Y α z K N * Real.exp (a + α * b + (1 - α) * c) := by
  unfold rb_Y
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  have := hz
  ring_nf

theorem rb_MPK_exp (α : ℝ) {z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_MPK α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_MPK α z K N * Real.exp (a + (α - 1) * b + (1 - α) * c) := by
  unfold rb_MPK
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  have := hz
  ring_nf

theorem rb_MPL_exp (α : ℝ) {z K N : ℝ} (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_MPL α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_MPL α z K N * Real.exp (a + α * b - α * c) := by
  unfold rb_MPL
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, show a + α * b - α * c = a + b * α + c * -α by ring,
    Real.exp_add, Real.exp_add]
  ring

theorem rb_hasDerivAt_log_one_sub {N n : ℝ} (hN : N < 1) :
    HasDerivAt (fun s => Real.log (1 - N * Real.exp (s * n))) (-(N * n) / (1 - N)) 0 := by
  have h := (((rb_hasDerivAt_exp_mul n).const_mul N).const_sub 1).log (by simp; linarith)
  simpa using h

/-! ### (14.27) and (14.31) -/

/-- Miao, p. 475: "taking logarithms and total differentiation" of (14.27): the derivative at
`s = 0` of `ln(χC_t) − ln(1 − N_t) − ln((1 − α)z_tK_t^αN_t^{−α})` along `X(s) = Xe^{sX̂}` is
`Ĉ + ζN̂ − (ẑ + αK̂ − αN̂)`, `ζ = N/(1 − N)`. -/
theorem eq_14_27_loglin {α χ C K N : ℝ} (hα1 : α < 1) (hχ : 0 < χ) (hC : 0 < C) (hK : 0 < K)
    (hN0 : 0 < N) (hN1 : N < 1) (c z k n : ℝ) :
    HasDerivAt (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) -
        Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))))
      (c + rb_zeta N * n - (z + α * k - α * n)) 0 := by
  have hM := rb_MPL_pos hα1 one_pos hK hN0 (α := α)
  have hf : (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) -
        Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n)))) =
      fun s => Real.log (χ * C) + s * c - Real.log (1 - N * Real.exp (s * n)) -
        (Real.log (rb_MPL α 1 K N) + s * (z + α * k - α * n)) := by
    funext s
    have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
    rw [e, rb_MPL_exp α hK hN0, ← mul_assoc, Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_mul hM.ne' (by positivity), Real.log_exp]
    ring_nf
  rw [hf]
  have h1 := (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (Real.log (χ * C))).sub
    (rb_hasDerivAt_log_one_sub (n := n) hN1)
  have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const (z + α * k - α * n)).const_add
    (Real.log (rb_MPL α 1 K N))
  convert h1.sub h2 using 1
  · funext s
    simp only [Pi.sub_apply, id]
  · rw [rb_zeta]
    ring

/-- Miao, (14.31), p. 475: `Ĉ + ζN̂ = ẑ + αK̂ − αN̂` iff
`N̂ = ẑ/(α + ζ) + αK̂/(α + ζ) − Ĉ/(α + ζ)`. -/
theorem eq_14_31 {α ζ : ℝ} (h : α + ζ ≠ 0) (c z k n : ℝ) :
    c + ζ * n = z + α * k - α * n ↔
      n = 1 / (α + ζ) * z + α / (α + ζ) * k - 1 / (α + ζ) * c := by
  constructor
  · intro h1
    field_simp
    linarith
  · intro h1
    rw [h1]
    field_simp
    ring

/-! ### The resource constraint and (14.32) -/

/-- Miao, p. 475: total differentiation of the resource constraint
`C_t + K_{t+1} − (1 − δ)K_t = z_tK_t^αN_t^{1−α}` along `X(s) = Xe^{sX̂}`: the derivative is
`CĈ + KK̂' − (1 − δ)KK̂ − Y(ẑ + αK̂ + (1 − α)N̂)` with `Y = K^αN^{1−α}`. -/
theorem rb_resource_loglin (α δ : ℝ) {C K N : ℝ} (hK : 0 < K) (hN : 0 < N) (c k' z k n : ℝ) :
    HasDerivAt (fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n)))
      (C * c + K * k' - (1 - δ) * K * k -
        rb_Y α 1 K N * (z + α * k + (1 - α) * n)) 0 := by
  have hf : (fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α 1 K N * Real.exp (s * (z + α * k + (1 - α) * n)) := by
    funext s
    have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
    rw [e, rb_Y_exp α one_pos hK hN]
    ring_nf
  rw [hf]
  have := (((rb_hasDerivAt_exp_mul c).const_mul C).add ((rb_hasDerivAt_exp_mul k').const_mul K)).sub
    (((rb_hasDerivAt_exp_mul k).const_mul K).const_mul (1 - δ)) |>.sub
    ((rb_hasDerivAt_exp_mul (z + α * k + (1 - α) * n)).const_mul (rb_Y α 1 K N))
  convert this using 1
  ring

/-- Miao, p. 475: solving the linearised resource constraint for `K̂_{t+1}`:
`K̂' = (Y/K)[ẑ + αK̂ + (1 − α)N̂] − (C/K)Ĉ + (1 − δ)K̂ = K̂/β + (Y/K)[ẑ + (1 − α)N̂] − (C/K)Ĉ`,
using the steady-state Euler equation `1 = β(αY/K + 1 − δ)`. -/
theorem rb_resource_solved {α β δ C K Y : ℝ} (hK : 0 < K) (hss : α * (Y / K) + 1 - δ = 1 / β)
    {c k' z k n : ℝ} (h : C * c + K * k' - (1 - δ) * K * k - Y * (z + α * k + (1 - α) * n) = 0) :
    k' = Y / K * (z + α * k + (1 - α) * n) - C / K * c + (1 - δ) * k ∧
      k' = 1 / β * k + Y / K * (z + (1 - α) * n) - C / K * c := by
  have h1 : k' = Y / K * (z + α * k + (1 - α) * n) - C / K * c + (1 - δ) * k := by
    field_simp
    linarith
  refine ⟨h1, ?_⟩
  rw [h1, ← hss]
  ring

/-- Miao, (14.32), p. 475: substituting (14.31) for `N̂_t` into the solved resource constraint
gives `K̂_{t+1} = (1/β + (1 − α)/(α + ζ)·αY/K)K̂_t + (Y/K)(1 + ζ)/(ζ + α)·ẑ_t
− (C/K + (1 − α)/(α + ζ)·Y/K)Ĉ_t`. -/
theorem eq_14_32 {α β ζ yk ck : ℝ} (hαζ : α + ζ ≠ 0) {c k' z k n : ℝ}
    (hk : k' = 1 / β * k + yk * (z + (1 - α) * n) - ck * c)
    (hn : n = 1 / (α + ζ) * z + α / (α + ζ) * k - 1 / (α + ζ) * c) :
    k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c := by
  have h' : ζ + α ≠ 0 := by rwa [add_comm]
  rw [hk, hn, rb_p, rb_g, rb_q]
  field_simp
  ring

/-! ### The Euler equation and (14.33) -/

/-- Miao, p. 476: total differentiation of the Euler equation (14.26): the derivative at `s = 0`
of the integrand `1/C_t − β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}` along
`X(s) = Xe^{sX̂}` is
`(−Ĉ_t + β(R_k + 1 − δ)Ĉ_{t+1} − βR_k(ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}))/C`. -/
theorem rb_euler_loglin (α β δ : ℝ) {C K N : ℝ} (hC : 0 < C) (hK : 0 < K) (hN : 0 < N)
    (c c' z' k' n' : ℝ) :
    HasDerivAt (fun s => 1 / (C * Real.exp (s * c)) -
        β * (rb_MPK α (Real.exp (s * z')) (K * Real.exp (s * k')) (N * Real.exp (s * n')) +
          1 - δ) / (C * Real.exp (s * c')))
      ((-c + β * (rb_MPK α 1 K N + 1 - δ) * c' -
        β * rb_MPK α 1 K N * (z' + (α - 1) * k' + (1 - α) * n')) / C) 0 := by
  set e := z' + (α - 1) * k' + (1 - α) * n'
  have hf : (fun s => 1 / (C * Real.exp (s * c)) -
        β * (rb_MPK α (Real.exp (s * z')) (K * Real.exp (s * k')) (N * Real.exp (s * n')) +
          1 - δ) / (C * Real.exp (s * c'))) =
      fun s => 1 / C * Real.exp (s * (-c)) -
        β / C * (rb_MPK α 1 K N * Real.exp (s * (e - c')) + (1 - δ) * Real.exp (s * (-c'))) := by
    funext s
    have ez : Real.exp (s * z') = 1 * Real.exp (s * z') := (one_mul _).symm
    rw [ez, rb_MPK_exp α one_pos hK hN]
    have h1 : Real.exp (s * (-c)) = 1 / Real.exp (s * c) := by
      rw [mul_neg, Real.exp_neg, one_div]
    have h2 : Real.exp (s * (-c')) = 1 / Real.exp (s * c') := by
      rw [mul_neg, Real.exp_neg, one_div]
    have h3 : Real.exp (s * (e - c')) = Real.exp (s * e) / Real.exp (s * c') := by
      rw [mul_sub, Real.exp_sub]
    rw [h1, h2, h3]
    simp only [e]
    field_simp
    ring_nf
  rw [hf]
  have := ((rb_hasDerivAt_exp_mul (-c)).const_mul (1 / C)).sub
    ((((rb_hasDerivAt_exp_mul (e - c')).const_mul (rb_MPK α 1 K N)).add
      ((rb_hasDerivAt_exp_mul (-c')).const_mul (1 - δ))).const_mul (β / C))
  convert this using 1
  field_simp
  ring

/-- Miao, p. 476: with the steady-state Euler equation `β(αY/K + 1 − δ) = 1` and
`R_k = αY/K`, the linearised Euler equation (the derivative of `rb_euler_loglin` set to zero) is
`−Ĉ_t = −Ĉ_{t+1} + βα(Y/K)[ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}]`. -/
theorem rb_euler_loglin_eq {α β δ C yk Rk : ℝ} (hC : 0 < C) (hRk : Rk = α * yk)
    (hss : β * (Rk + 1 - δ) = 1) (c c' z' k' n' : ℝ) :
    (-c + β * (Rk + 1 - δ) * c' - β * Rk * (z' + (α - 1) * k' + (1 - α) * n')) / C = 0 ↔
      -c = -c' + β * α * yk * (z' + (α - 1) * k' + (1 - α) * n') := by
  rw [div_eq_zero_iff, hss, hRk]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hC.ne'
  · intro h
    left
    linarith

/-- Miao, (14.33), p. 476, deterministic form: substituting (14.31) at `t + 1` into the
linearised Euler equation gives
`−Ĉ_t = −(1 + (1 − α)βα(Y/K)/(α + ζ))Ĉ_{t+1} + βα(Y/K)(1 + ζ)/(α + ζ)·ẑ_{t+1}
− βα(1 − α)(Y/K)ζ/(α + ζ)·K̂_{t+1}`. -/
theorem eq_14_33_det {α β ζ yk : ℝ} (hαζ : α + ζ ≠ 0) {c c' z' k' n' : ℝ}
    (he : -c = -c' + β * α * yk * (z' + (α - 1) * k' + (1 - α) * n'))
    (hn : n' = 1 / (α + ζ) * z' + α / (α + ζ) * k' - 1 / (α + ζ) * c') :
    -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k' := by
  rw [he, hn, rb_a, rb_b, rb_c]
  field_simp
  ring

/-- Miao, (14.33), p. 476, with the conditional expectation: let `E_t` be a conditional
expectation operator (a continuous linear map, as in Chapter 2). If
`−Ĉ_t = E_t[−Ĉ_{t+1} + βα(Y/K)(ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1})]` and (14.31) holds at
`t + 1`, then `−Ĉ_t = −(1 + a)E_tĈ_{t+1} + bE_tẑ_{t+1} − cE_tK̂_{t+1}`. -/
theorem eq_14_33 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (E : CondExpSystem ℝ V)
    {α β ζ yk : ℝ} (hαζ : α + ζ ≠ 0) {C Z Kh Nh : ℕ → V} (t : ℕ)
    (he : -C t = E.E t (-C (t + 1) + (β * α * yk) • (Z (t + 1) + (α - 1) • Kh (t + 1) +
      (1 - α) • Nh (t + 1))))
    (hn : Nh (t + 1) = (1 / (α + ζ)) • Z (t + 1) + (α / (α + ζ)) • Kh (t + 1) -
      (1 / (α + ζ)) • C (t + 1)) :
    -C t = -(1 + rb_a α β ζ yk) • E.E t (C (t + 1)) + rb_b α β ζ yk • E.E t (Z (t + 1)) -
      rb_c α β ζ yk • E.E t (Kh (t + 1)) := by
  rw [he, hn]
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [rb_a, rb_b, rb_c]
  match_scalars <;> field_simp <;> ring

/-! ### The labour market (14.36)–(14.37), output, rental rate, investment -/

/-- Miao, p. 478: the log-linearised labour supply (14.36) `χC_t/(1 − N_t) = w_t`: the derivative
of `ln(χC) − ln(1 − N) − ln w` along `X(s) = Xe^{sX̂}` is `Ĉ + ζN̂ − ŵ`, so the linearised supply
curve is `ζN̂ = −Ĉ + ŵ`. -/
theorem eq_14_36_loglin {χ C N w : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hN1 : N < 1) (hw : 0 < w)
    (c n wh : ℝ) :
    HasDerivAt (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) - Real.log (w * Real.exp (s * wh)))
      (c + rb_zeta N * n - wh) 0 := by
  have hf : (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) - Real.log (w * Real.exp (s * wh))) =
      fun s => Real.log (χ * C) + s * c - Real.log (1 - N * Real.exp (s * n)) -
        (Real.log w + s * wh) := by
    funext s
    rw [← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul hw.ne' (by positivity), Real.log_exp]
  rw [hf]
  have h1 := (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (Real.log (χ * C))).sub
    (rb_hasDerivAt_log_one_sub (n := n) hN1)
  have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const wh).const_add (Real.log w)
  convert h1.sub h2 using 1
  · funext s
    simp only [Pi.sub_apply, id]
  · rw [rb_zeta]
    ring

/-- Miao, (14.37), p. 478: the log-linearised labour demand `w = (1 − α)zK^αN^{−α}`: the log of
the wage along `X(s) = Xe^{sX̂}` is `ln w + s(ẑ + αK̂ − αN̂)`, so `ŵ = ẑ + αK̂ − αN̂`. -/
theorem eq_14_37 {α K N : ℝ} (hα1 : α < 1) (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_MPL α 1 K N) + s * (z + α * k - α * n) := by
  have hM := rb_MPL_pos hα1 one_pos hK hN (α := α)
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_MPL_exp α hK hN, Real.log_mul hM.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 478 (Figure 14.2): the log-linearised labour supply `ζN̂ = −Ĉ + ŵ` and demand
`ŵ = ẑ + αK̂ − αN̂` intersect at `N̂ = (ẑ + αK̂ − Ĉ)/(α + ζ)` (this is (14.31)) and
`ŵ = (ζ(ẑ + αK̂) + αĈ)/(α + ζ)`. -/
theorem rb_labour_market {α ζ : ℝ} (hαζ : α + ζ ≠ 0) {c z k n wh : ℝ} :
    (ζ * n = -c + wh ∧ wh = z + α * k - α * n) ↔
      (n = (z + α * k - c) / (α + ζ) ∧ wh = (ζ * (z + α * k) + α * c) / (α + ζ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hn : n = (z + α * k - c) / (α + ζ) := by
      field_simp
      linarith
    refine ⟨hn, ?_⟩
    rw [h2, hn]
    field_simp
    ring
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    constructor <;> field_simp <;> ring

/-- Miao, p. 478: the labour supply curve `ŵ = ζN̂ + Ĉ` is upward sloping in `N̂` (`ζ > 0`) and
shifts up with `Ĉ` (the wealth effect); the demand curve `ŵ = ẑ + αK̂ − αN̂` is downward sloping and
shifts up with `ẑ`. In equilibrium `∂N̂/∂Ĉ = −1/(α + ζ) < 0`, `∂ŵ/∂Ĉ = α/(α + ζ) > 0`,
`∂N̂/∂ẑ = 1/(α + ζ) > 0` and `∂ŵ/∂ẑ = ζ/(α + ζ) > 0`. -/
theorem rb_labour_slopes {α ζ : ℝ} (hα : 0 < α) (hζ : 0 < ζ) :
    StrictMono (fun n : ℝ => ζ * n) ∧ StrictAnti (fun n : ℝ => -(α * n)) ∧
      -1 / (α + ζ) < 0 ∧ 0 < α / (α + ζ) ∧ 0 < 1 / (α + ζ) ∧ 0 < ζ / (α + ζ) := by
  have h : 0 < α + ζ := by linarith
  refine ⟨fun a b hab => by simp only; nlinarith, fun a b hab => by simp only; nlinarith,
    by rw [neg_div]; exact neg_neg_of_pos (by positivity), by positivity, by positivity,
    by positivity⟩

/-- Miao, p. 478: the log-linearised production function. Along `X(s) = Xe^{sX̂}`,
`ln Y = ln Y + s(ẑ + αK̂ + (1 − α)N̂)`, so `Ŷ = αK̂ + (1 − α)N̂ + ẑ`. -/
theorem rb_output_loglin {α K N : ℝ} (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_Y α 1 K N) + s * (α * k + (1 - α) * n + z) := by
  have hY := rb_Y_pos (α := α) one_pos hK hN
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_Y_exp α one_pos hK hN, Real.log_mul hY.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 478: the rental rate `R_k = αY/K`; along `X(s) = Xe^{sX̂}`,
`ln R_k = ln R_k + s(Ŷ − K̂)`, so `R̂_k = Ŷ − K̂`. -/
theorem rb_rental_loglin {α K N : ℝ} (hα : 0 < α) (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_MPK α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_MPK α 1 K N) + s * ((α * k + (1 - α) * n + z) - k) := by
  have hR := rb_MPK_pos hα one_pos hK hN
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_MPK_exp α one_pos hK hN, Real.log_mul hR.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 480 ("we can derive investment simply from the resource constraint"): the
linearised resource constraint `CĈ + IÎ = YŶ` gives `Î = (YŶ − CĈ)/I`, and the linearised
(14.24) `KK̂' = (1 − δ)KK̂ + IÎ` with `I = δK` gives `Î = (K̂' − (1 − δ)K̂)/δ`. -/
theorem rb_investment_loglin {δ C I Y K : ℝ} (hI : 0 < I) (hδ : 0 < δ) (hIK : I = δ * K)
    {c i y k k' : ℝ} :
    (C * c + I * i = Y * y → i = (Y * y - C * c) / I) ∧
      (K * k' = (1 - δ) * K * k + I * i → i = (k' - (1 - δ) * k) / δ) := by
  have hK : K ≠ 0 := by rintro rfl; simp at hIK; linarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · field_simp
    linarith
  · rw [hIK] at h
    rw [eq_div_iff hδ.ne']
    apply mul_left_cancel₀ hK
    linarith

/-! ### Returns -/

/-- Miao, p. 479, corrected: with `R^s = R_k + 1 − δ`, along `R_k(s) = R_ke^{sR̂_k}` the log
deviation of `R^s` is `(R_k/R^s)R̂_k`: `d/ds ln(R_ke^{sR̂_k} + 1 − δ)|₀ = R_kR̂_k/(R_k + 1 − δ)`;
at the steady state `R^s = 1/β`, so `R̂^s = (1 − β(1 − δ))R̂_k`. -/
theorem rb_stock_return_loglin {β δ Rk : ℝ} (hRs : β * (Rk + 1 - δ) = 1) (hβ : 0 < β)
    (r : ℝ) :
    HasDerivAt (fun s => Real.log (Rk * Real.exp (s * r) + 1 - δ)) ((1 - β * (1 - δ)) * r) 0 := by
  have hpos : Rk + 1 - δ ≠ 0 := by
    intro h; rw [h, mul_zero] at hRs; exact zero_ne_one hRs
  have h := (((rb_hasDerivAt_exp_mul r).const_mul Rk).add_const (1 - δ)).log
    (by simpa [add_sub_assoc] using hpos)
  convert h using 1
  · funext s; ring_nf
  · simp only [zero_mul, Real.exp_zero, mul_one]
    have hR : Rk = 1 / β - (1 - δ) := by field_simp; linarith
    rw [show Rk + (1 - δ) = Rk + 1 - δ by ring]
    field_simp
    rw [hR]
    field_simp
    ring

/-- Correction to Miao, p. 479: the printed `R̂^s_t = R̂_kt` fails whenever `δ < 1` and
`R̂_k ≠ 0` (here `β = 1/2`, `δ = 0`, `R_k = 1`, `R̂_k = 1`: the log deviation of `R^s` is `1/2`). -/
theorem rb_stock_return_printed_false :
    ¬ HasDerivAt (fun s => Real.log (1 * Real.exp (s * 1) + 1 - 0)) 1 0 := by
  intro h
  have h2 := rb_stock_return_loglin (β := 1 / 2) (δ := 0) (Rk := 1) (by norm_num) (by norm_num) 1
  have := h.unique h2
  norm_num at this

/-- Miao, p. 480: total differentiation of the risk-free Euler equation
`1/C_t = βE_t[(1 + r^f_{t+1})/C_{t+1}]`: the derivative at `s = 0` of the integrand
`1/C_t − βR^f_{t+1}/C_{t+1}` along `X(s) = Xe^{sX̂}` (with `R̂^f = dR^f/R^f`) is
`(−Ĉ_t − βR^f(R̂^f − Ĉ_{t+1}))/C`. -/
theorem rb_riskfree_loglin (β : ℝ) {C Rf : ℝ} (hC : 0 < C) (c c' r : ℝ) :
    HasDerivAt (fun s => 1 / (C * Real.exp (s * c)) -
        β * (Rf * Real.exp (s * r)) / (C * Real.exp (s * c')))
      ((-c - β * Rf * (r - c')) / C) 0 := by
  have hf : (fun s => 1 / (C * Real.exp (s * c)) -
        β * (Rf * Real.exp (s * r)) / (C * Real.exp (s * c'))) =
      fun s => 1 / C * Real.exp (s * (-c)) - β * Rf / C * Real.exp (s * (r - c')) := by
    funext s
    rw [mul_neg, Real.exp_neg, mul_sub, Real.exp_sub]
    field_simp
  rw [hf]
  have := ((rb_hasDerivAt_exp_mul (-c)).const_mul (1 / C)).sub
    ((rb_hasDerivAt_exp_mul (r - c')).const_mul (β * Rf / C))
  convert this using 1
  field_simp

/-- Miao, p. 480: with `βR^f = 1` at the steady state, the linearised risk-free Euler equation
is `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t`. -/
theorem rb_riskfree_eq {β C Rf : ℝ} (hC : 0 < C) (hss : β * Rf = 1) (c c' r : ℝ) :
    (-c - β * Rf * (r - c')) / C = 0 ↔ r = c' - c := by
  rw [div_eq_zero_iff, hss]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hC.ne'
  · intro h
    left
    linarith

/-- Miao, p. 480: since `r^f_{t+1}` is known at date `t` (`E_tr̂^f_{t+1} = r̂^f_{t+1}`), applying
`E_t` to the linearised equation gives `r̂^f_{t+1} = E_tĈ_{t+1} − Ĉ_t` (`Ĉ_t` adapted). -/
theorem rb_riskfree_E {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : CondExpSystem ℝ V) {C R : ℕ → V} (t : ℕ) (hC : E.E t (C t) = C t)
    (hR : E.E t (R (t + 1)) = R (t + 1)) (h : E.E t (R (t + 1) - (C (t + 1) - C t)) = 0) :
    R (t + 1) = E.E t (C (t + 1)) - C t := by
  rw [map_sub, map_sub, hC, hR, sub_eq_zero] at h
  exact h

end Miao.NeoclassicalGrowth
