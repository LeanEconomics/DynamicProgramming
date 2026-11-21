/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.NKEquilibrium
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The basic DNK model: log-linearising the equilibrium conditions (Miao §19.1.7)

Miao, §19.1.7, pp. 624–627. A log-linearisation is made precise as a first-order perturbation:
every variable is a positive differentiable path `s ↦ X(s)` through its zero-inflation
steady-state value `X(0)`, the nonlinear equation holds for every `s`, and the hat variable is
the log-derivative `X̂ = d ln X(s)/ds` at `s = 0`. Differentiating the equation at `s = 0` gives
the log-linear equation exactly. Tools: `nk_path_deriv`, `nk_rpow_path`.

* (19.19) from (19.13): `P̂_t = θP̂_{t−1} + (1 − θ)P̂*_t`, so `q_t = θπ_t/(1 − θ)` (`eq_19_19`).
* The terms of (19.11) (`nk_loglin_reset_terms`); the "simplifying" step to (19.20) is
  `eq_19_20` in `NKPhillips`.
* (19.21) from (19.12), with `b` of (19.22) (`eq_19_21`, `nk_b`).
* The log-linear (19.2) (`nk_loglin_19_2`), (19.9) (`nk_loglin_MC`), (19.16)
  (`nk_loglin_19_16`), (19.17) (`nk_loglin_19_17`) and (19.18) (`nk_loglin_19_18`).
  With (19.19), the dispersion obeys `Δ̂_t = θΔ̂_{t−1}` (`nk_loglin_dispersion`), so from the
  steady state (`Δ̂_{−1} = 0`) `Δ̂_t = 0` for all `t` and `Ŷ_t = Â_t + (1 − α)N̂_t`
  (`nk_dispersion_zero`, `nk_loglin_output`): "the price dispersion term does not matter up to
  first order". The book's total differential of (19.16) treats the dispersion of the previous
  period as fixed; the recursion makes this explicit.
* (19.26) and the natural rate (19.27) from the Euler equations, for `E_t` an expectation over
  finitely many successor states with probabilities `q_j` (`nk_loglin_euler`, `eq_19_26`,
  `nk_loglin_natural_rate`); in them `i_t` and `r^n_t` stand for `ln(1 + i_t)`,
  `ln(1 + r^n_t)`, and `ı̂_t = ln(1 + i_t) − ln(1 + i) = ln(1 + i_t) + ln β` exactly. The book's
  `ı̂_t = i_t + ln β` uses `ln(1 + i_t) ≈ i_t` in addition.
* (19.29) from (19.14): exact, with `i_t := ln(1 + i_t)`, `π_t = ln Π_t`, `x_t = ln(Y_t/Y^f_t)`
  (`eq_19_29`).

**Departure.** The conditional expectation in (19.26)–(19.27) is over finitely many successor
states; the infinite sum in (19.11) is log-linearised term by term (`nk_loglin_reset_terms`).
-/

namespace Miao.NewKeynesian

/-- A positive path with log-derivative `x̂` at `0` has derivative `X(0)x̂` at `0`. -/
theorem nk_path_deriv {X : ℝ → ℝ} {xh : ℝ} (hX : ∀ s, 0 < X s)
    (h : HasDerivAt (fun s => Real.log (X s)) xh 0) : HasDerivAt X (X 0 * xh) 0 := by
  have hd := (Real.hasDerivAt_exp (Real.log (X 0))).comp 0 h
  rw [Real.exp_log (hX 0)] at hd
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (Real.exp_log (hX s)).symm)

/-- The derivative of `X(s)^a` along a positive path: `aX(0)^a x̂`. -/
theorem nk_rpow_path {X : ℝ → ℝ} {xh : ℝ} (a : ℝ) (hX : ∀ s, 0 < X s)
    (h : HasDerivAt (fun s => Real.log (X s)) xh 0) :
    HasDerivAt (fun s => X s ^ a) (a * X 0 ^ a * xh) 0 := by
  have e : (fun s => X s ^ a) = fun s => Real.exp (a * Real.log (X s)) :=
    funext fun s => by rw [Real.rpow_def_of_pos (hX s), mul_comm]
  have hd := (Real.hasDerivAt_exp _).comp 0 (h.const_mul a)
  rw [e]
  refine hd.congr_deriv ?_
  rw [← mul_comm (Real.log (X 0)), ← Real.rpow_def_of_pos (hX 0)]
  ring

/-- **(19.19)** (Miao, p. 624): log-linearising (19.13). If `P_t(s), P_{t−1}(s), P*_t(s) > 0`
satisfy (19.13) for every `s`, all equal `P̄` at `s = 0` (zero inflation), and have
log-derivatives `p̂, p̂₋, p̂*`, then `p̂ = θp̂₋ + (1 − θ)p̂*`, and for `θ ≠ 1`,
`q = p̂* − p̂ = θπ/(1 − θ)` with `π = p̂ − p̂₋`. -/
theorem eq_19_19 {θ ε : ℝ} {P Pm Ps : ℝ → ℝ} {ph pmh psh : ℝ} (hε : ε ≠ 1) (hθ : θ ≠ 1)
    (hP : ∀ s, 0 < P s) (hPm : ∀ s, 0 < Pm s) (hPs : ∀ s, 0 < Ps s)
    (h0m : Pm 0 = P 0) (h0s : Ps 0 = P 0)
    (dP : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (dPm : HasDerivAt (fun s => Real.log (Pm s)) pmh 0)
    (dPs : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (h13 : ∀ s, P s ^ (1 - ε) = θ * Pm s ^ (1 - ε) + (1 - θ) * Ps s ^ (1 - ε)) :
    ph = θ * pmh + (1 - θ) * psh ∧ psh - ph = θ / (1 - θ) * (ph - pmh) := by
  have d1 := nk_rpow_path (1 - ε) hP dP
  have d2 := ((nk_rpow_path (1 - ε) hPm dPm).const_mul θ).add
    ((nk_rpow_path (1 - ε) hPs dPs).const_mul (1 - θ))
  have e : (fun s => P s ^ (1 - ε)) =
      (fun s => θ * Pm s ^ (1 - ε)) + fun s => (1 - θ) * Ps s ^ (1 - ε) := funext h13
  rw [e] at d1
  have hu := d1.unique d2
  rw [h0m, h0s] at hu
  have hc : (1 - ε) * P 0 ^ (1 - ε) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (Ne.symm hε)) (Real.rpow_pos_of_pos (hP 0) _).ne'
  have h1 : ph = θ * pmh + (1 - θ) * psh := by
    apply mul_left_cancel₀ hc
    linear_combination hu
  refine ⟨h1, ?_⟩
  have h2 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  field_simp
  linear_combination (-1) * h1

/-- **(19.22)** (Miao, p. 624): `b = εα/(1 − α)`. -/
noncomputable def nk_b (ε α : ℝ) : ℝ := ε * α / (1 - α)

/-- **(19.21)** (Miao, p. 624): log-linearising (19.12). If
`MC_{k|t}(s) = MC_k(s)(P*(s)/P_k(s))^{εα/(α−1)}` for every `s` (positive paths), then
`m̂_{k|t} = m̂_k − b(p̂* − p̂_k)`, `b = εα/(1 − α)`. -/
theorem eq_19_21 {ε α : ℝ} {MCkt MCk Ps Pk : ℝ → ℝ} {mkt mk psh pkh : ℝ} (hα : α ≠ 1)
    (h2 : ∀ s, 0 < MCk s) (h3 : ∀ s, 0 < Ps s) (h4 : ∀ s, 0 < Pk s)
    (d1 : HasDerivAt (fun s => Real.log (MCkt s)) mkt 0)
    (d2 : HasDerivAt (fun s => Real.log (MCk s)) mk 0)
    (d3 : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (d4 : HasDerivAt (fun s => Real.log (Pk s)) pkh 0)
    (h12 : ∀ s, MCkt s = MCk s * (Ps s / Pk s) ^ (ε * α / (α - 1))) :
    mkt = mk - nk_b ε α * (psh - pkh) := by
  have e : (fun s => Real.log (MCkt s)) = fun s => Real.log (MCk s) +
      ε * α / (α - 1) * (Real.log (Ps s) - Real.log (Pk s)) := funext fun s => by
    rw [h12, Real.log_mul (h2 s).ne' (Real.rpow_pos_of_pos (div_pos (h3 s) (h4 s)) _).ne',
      Real.log_rpow (div_pos (h3 s) (h4 s)), Real.log_div (h3 s).ne' (h4 s).ne']
  rw [e] at d1
  have hu := d1.unique (d2.add ((d3.sub d4).const_mul _))
  rw [hu, nk_b]
  have : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have : α - 1 ≠ 0 := sub_ne_zero.2 hα
  field_simp
  ring

/-- Miao, p. 624: log-linearising the terms of (19.11) in the form
`P*_t Y_{t+k}^{1−γ}P_{t+k}^{ε−1} = μY_{t+k}^{1−γ}P_{t+k}^εMC_{t+k|t}` (term by term). Along
positive paths through a steady state with `P*(0) = P_k(0) = P̄` and `μMC_{k|t}(0) = 1`, the
derivatives of the two sides are `c(p̂* + (1 − γ)ŷ_k + (ε − 1)p̂_k)` and
`c((1 − γ)ŷ_k + εp̂_k + m̂_{k|t})` with the same `c = P̄Y_k(0)^{1−γ}P̄^{ε−1} > 0`. -/
theorem nk_loglin_reset_terms {γ ε mu : ℝ} {Ps Yk Pk MC : ℝ → ℝ} {psh yh pkh mh : ℝ}
    (h1 : ∀ s, 0 < Ps s) (h2 : ∀ s, 0 < Yk s) (h3 : ∀ s, 0 < Pk s) (h4 : ∀ s, 0 < MC s)
    (hss : Ps 0 = Pk 0) (hmc : mu * MC 0 = 1)
    (d1 : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (d2 : HasDerivAt (fun s => Real.log (Yk s)) yh 0)
    (d3 : HasDerivAt (fun s => Real.log (Pk s)) pkh 0)
    (d4 : HasDerivAt (fun s => Real.log (MC s)) mh 0) :
    HasDerivAt (fun s => Ps s * Yk s ^ (1 - γ) * Pk s ^ (ε - 1))
      (Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) * (psh + (1 - γ) * yh + (ε - 1) * pkh)) 0 ∧
    HasDerivAt (fun s => mu * Yk s ^ (1 - γ) * Pk s ^ ε * MC s)
      (Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) * ((1 - γ) * yh + ε * pkh + mh)) 0 ∧
    0 < Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) := by
  have a1 := nk_path_deriv h1 d1
  have a2 := nk_rpow_path (1 - γ) h2 d2
  have a3 := nk_rpow_path (ε - 1) h3 d3
  have a3' := nk_rpow_path ε h3 d3
  have a4 := nk_path_deriv h4 d4
  have hp := h3 0
  have hy := Real.rpow_pos_of_pos (h2 0) (1 - γ)
  have hpe : Pk 0 ^ ε = Pk 0 * Pk 0 ^ (ε - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  refine ⟨?_, ?_, by have := Real.rpow_pos_of_pos hp (ε - 1); positivity⟩
  · refine ((a1.mul a2).mul a3).congr_deriv ?_
    simp only [Pi.mul_apply, hss]
    ring
  · refine ((((hasDerivAt_const (0 : ℝ) mu).mul a2).mul a3').mul a4).congr_deriv ?_
    have hm : MC 0 = 1 / mu := by
      have : mu ≠ 0 := by
        rintro rfl
        simp at hmc
      field_simp
      linarith
    simp only [Pi.mul_apply]
    rw [hm, hpe]
    have : mu ≠ 0 := by
      rintro rfl
      simp at hmc
    field_simp
    ring

/-- Miao, p. 625: log-linearising (19.2). If `χN(s)^ν/C(s)^{−γ} = W(s)/P(s)` for every `s`
(positive paths), then `ŵ − p̂ = νn̂ + γĉ`. -/
theorem nk_loglin_19_2 {χ ν γ : ℝ} {N C W P : ℝ → ℝ} {nh ch wh ph : ℝ} (hχ : 0 < χ)
    (h1 : ∀ s, 0 < N s) (h2 : ∀ s, 0 < C s) (h3 : ∀ s, 0 < W s) (h4 : ∀ s, 0 < P s)
    (d1 : HasDerivAt (fun s => Real.log (N s)) nh 0)
    (d2 : HasDerivAt (fun s => Real.log (C s)) ch 0)
    (d3 : HasDerivAt (fun s => Real.log (W s)) wh 0)
    (d4 : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (h : ∀ s, χ * N s ^ ν / C s ^ (-γ) = W s / P s) : wh - ph = ν * nh + γ * ch := by
  have e : (fun s => Real.log (W s) - Real.log (P s)) =
      fun s => Real.log χ + ν * Real.log (N s) + γ * Real.log (C s) := funext fun s => by
    rw [← Real.log_div (h3 s).ne' (h4 s).ne', ← h s,
      Real.log_div (mul_pos hχ (Real.rpow_pos_of_pos (h1 s) _)).ne'
        (Real.rpow_pos_of_pos (h2 s) _).ne',
      Real.log_mul hχ.ne' (Real.rpow_pos_of_pos (h1 s) _).ne', Real.log_rpow (h1 s),
      Real.log_rpow (h2 s)]
    ring
  have hd : HasDerivAt (fun s => Real.log (W s) - Real.log (P s)) (wh - ph) 0 := d3.sub d4
  rw [e] at hd
  have hu := hd.unique (((hasDerivAt_const (0 : ℝ) (Real.log χ)).add (d1.const_mul ν)).add
    (d2.const_mul γ))
  linarith

/-- Miao, p. 625: log-linearising (19.9). If
`MC(s) = (W(s)/P(s))/(A(s)(1 − α)(Y(s)/A(s))^{−α/(1−α)})`
for every `s` (positive paths, `α < 1`), then `m̂ = ŵ − p̂ + α/(1 − α)ŷ − 1/(1 − α)â`. -/
theorem nk_loglin_MC {α : ℝ} {MC W P A Y : ℝ → ℝ} {mh wh ph ah yh : ℝ} (hα : α < 1)
    (h2 : ∀ s, 0 < W s) (h3 : ∀ s, 0 < P s) (h4 : ∀ s, 0 < A s)
    (h5 : ∀ s, 0 < Y s)
    (d1 : HasDerivAt (fun s => Real.log (MC s)) mh 0)
    (d2 : HasDerivAt (fun s => Real.log (W s)) wh 0)
    (d3 : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (d4 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (d5 : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (h : ∀ s, MC s = nk_MCavg (W s / P s) (A s) α (Y s)) :
    mh = wh - ph + α / (1 - α) * yh - 1 / (1 - α) * ah := by
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have e : (fun s => Real.log (MC s)) = fun s => Real.log (W s) - Real.log (P s) -
      Real.log (A s) - Real.log (1 - α) + α / (1 - α) * (Real.log (Y s) - Real.log (A s)) :=
    funext fun s => by
      have hq := div_pos (h5 s) (h4 s)
      have hr := Real.rpow_pos_of_pos hq (-α / (1 - α))
      have hm : 0 < A s * (1 - α) := mul_pos (h4 s) h1p
      rw [h s, nk_MCavg, Real.log_div (div_pos (h2 s) (h3 s)).ne' (mul_pos hm hr).ne',
        Real.log_div (h2 s).ne' (h3 s).ne', Real.log_mul hm.ne' hr.ne',
        Real.log_mul (h4 s).ne' h1p.ne', Real.log_rpow hq, Real.log_div (h5 s).ne' (h4 s).ne']
      ring
  rw [e] at d1
  have hu := d1.unique (((((d2.sub d3).sub d4).sub (hasDerivAt_const (0 : ℝ) _)).add
    ((d5.sub d4).const_mul (α / (1 - α)))))
  rw [hu]
  field_simp
  ring

/-- Miao, p. 625: log-linearising (19.16). If `Y(s) = A(s)N(s)^{1−α}Δ(s)^{α−1}` for every `s`
(positive paths), then `ŷ = â + (1 − α)n̂ + (α − 1)Δ̂`. -/
theorem nk_loglin_19_16 {α : ℝ} {Y A N Δ : ℝ → ℝ} {yh ah nh dh : ℝ}
    (h2 : ∀ s, 0 < A s) (h3 : ∀ s, 0 < N s) (h4 : ∀ s, 0 < Δ s)
    (d1 : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (d2 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (d3 : HasDerivAt (fun s => Real.log (N s)) nh 0)
    (d4 : HasDerivAt (fun s => Real.log (Δ s)) dh 0)
    (h : ∀ s, Y s = A s * N s ^ (1 - α) * Δ s ^ (α - 1)) :
    yh = ah + (1 - α) * nh + (α - 1) * dh := by
  have e : (fun s => Real.log (Y s)) = fun s => Real.log (A s) + (1 - α) * Real.log (N s) +
      (α - 1) * Real.log (Δ s) := funext fun s => by
    rw [h s, Real.log_mul (mul_pos (h2 s) (Real.rpow_pos_of_pos (h3 s) _)).ne'
      (Real.rpow_pos_of_pos (h4 s) _).ne', Real.log_mul (h2 s).ne'
      (Real.rpow_pos_of_pos (h3 s) _).ne', Real.log_rpow (h3 s), Real.log_rpow (h4 s)]
  rw [e] at d1
  exact d1.unique ((d2.add (d3.const_mul _)).add (d4.const_mul _))

/-- Miao, pp. 622, 625: log-linearising (19.17) around `Δ = Π = P*/P = 1`. If
`Δ(s) = θΠ(s)^{ε/(1−α)}Δ₋(s) + (1 − θ)Q(s)^{−ε/(1−α)}` for every `s` (positive paths, all `1` at
`s = 0`), then `Δ̂ = θΔ̂₋ + (ε/(1 − α))(θπ − (1 − θ)q)`. -/
theorem nk_loglin_19_17 {θ ε α : ℝ} {Δ Δm Infl Q : ℝ → ℝ} {dh dmh pih qh : ℝ}
    (h1 : ∀ s, 0 < Δ s) (h2 : ∀ s, 0 < Δm s) (h3 : ∀ s, 0 < Infl s) (h4 : ∀ s, 0 < Q s)
    (e1 : Δ 0 = 1) (e2 : Δm 0 = 1) (e3 : Infl 0 = 1) (e4 : Q 0 = 1)
    (d1 : HasDerivAt (fun s => Real.log (Δ s)) dh 0)
    (d2 : HasDerivAt (fun s => Real.log (Δm s)) dmh 0)
    (d3 : HasDerivAt (fun s => Real.log (Infl s)) pih 0)
    (d4 : HasDerivAt (fun s => Real.log (Q s)) qh 0)
    (h : ∀ s, Δ s = θ * Infl s ^ (ε / (1 - α)) * Δm s + (1 - θ) * Q s ^ (-ε / (1 - α))) :
    dh = θ * dmh + ε / (1 - α) * (θ * pih - (1 - θ) * qh) := by
  have a1 := nk_path_deriv h1 d1
  have a2 := nk_path_deriv h2 d2
  have a3 := nk_rpow_path (ε / (1 - α)) h3 d3
  have a4 := nk_rpow_path (-ε / (1 - α)) h4 d4
  have a5 := (((hasDerivAt_const (0 : ℝ) θ).mul a3).mul a2).add
    ((hasDerivAt_const (0 : ℝ) (1 - θ)).mul a4)
  have a6 : HasDerivAt Δ _ 0 := a5.congr_of_eventuallyEq (Filter.Eventually.of_forall h)
  have hu := a1.unique a6
  simp only [Pi.mul_apply, e1, e2, e3, e4, Real.one_rpow] at hu
  linear_combination hu

/-- Miao, p. 625: with (19.19) (`q = θπ/(1 − θ)`, `θ ≠ 1`), the log-linear (19.17) is
`Δ̂ = θΔ̂₋`. -/
theorem nk_loglin_dispersion {θ ε α dh dmh pih qh : ℝ} (hθ : θ ≠ 1)
    (h17 : dh = θ * dmh + ε / (1 - α) * (θ * pih - (1 - θ) * qh))
    (h19 : qh = θ / (1 - θ) * pih) : dh = θ * dmh := by
  have : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [h17, h19]
  field_simp
  ring

/-- Miao, p. 626: starting from the steady state (`Δ̂_{−1} = 0`), `Δ̂_t = θΔ̂_{t−1}` gives
`Δ̂_t = 0` for every `t`; from any `Δ̂_{−1}`, `Δ̂_t = θ^{t+1}Δ̂_{−1}`. -/
theorem nk_dispersion_zero {θ : ℝ} {dh : ℕ → ℝ} (h : ∀ t, dh (t + 1) = θ * dh t) :
    (∀ t, dh t = θ ^ t * dh 0) ∧ (dh 0 = 0 → ∀ t, dh t = 0) := by
  have h1 : ∀ t, dh t = θ ^ t * dh 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [h n, ih, pow_succ]; ring
  exact ⟨h1, fun h0 t => by rw [h1 t, h0, mul_zero]⟩

/-- Miao, pp. 625–626: with `Δ̂ = 0`, the log-linear (19.16) is `Ŷ = Â + (1 − α)N̂`. -/
theorem nk_loglin_output {α yh ah nh dh : ℝ} (h16 : yh = ah + (1 - α) * nh + (α - 1) * dh)
    (hd : dh = 0) : yh = ah + (1 - α) * nh := by
  rw [h16, hd, mul_zero, add_zero]

/-- Miao, p. 626: log-linearising (19.18). If
`Y^f(s) = ((1 − α)/(μχ))^{(1−α)/D}A(s)^{(1+ν)/D}` for every `s`, `D = γ(1 − α) + α + ν`, then
`Ŷ^f = ((1 + ν)/D)Â`. -/
theorem nk_loglin_19_18 {γ ν α χ mu : ℝ} {Yf A : ℝ → ℝ} {yfh ah : ℝ} (hk : 0 < (1 - α) / (mu * χ))
    (h2 : ∀ s, 0 < A s)
    (d1 : HasDerivAt (fun s => Real.log (Yf s)) yfh 0)
    (d2 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (h : ∀ s, Yf s = ((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
      A s ^ ((1 + ν) / (γ * (1 - α) + α + ν))) :
    yfh = (1 + ν) / (γ * (1 - α) + α + ν) * ah := by
  have e : (fun s => Real.log (Yf s)) = fun s =>
      Real.log (((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν))) +
        (1 + ν) / (γ * (1 - α) + α + ν) * Real.log (A s) := funext fun s => by
    rw [h s, Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos (h2 s) _).ne',
      Real.log_rpow (h2 s)]
  rw [e] at d1
  have hu := d1.unique ((hasDerivAt_const (0 : ℝ) _).add (d2.const_mul _))
  linarith

/-- The Euler-equation perturbation (Miao, pp. 626–627). Let `E_t` be the expectation over
finitely many successor states `j` with probabilities `q_j` (`∑q_j = 1`). If
`1 = βR(s)∑_j q_j exp(L_j(s))` for every `s` with `R(s) > 0`, `βR(0) = 1`, `L_j(0) = 0`, `ln R`
having derivative `r̂` and `L_j` derivative `ℓ_j` at `0`, then `r̂ + ∑_j q_jℓ_j = 0`. -/
theorem nk_loglin_euler {n : ℕ} {β : ℝ} {q : Fin n → ℝ} {R : ℝ → ℝ} {L : Fin n → ℝ → ℝ}
    {rh : ℝ} {lh : Fin n → ℝ} (hq : ∑ j, q j = 1) (hR : ∀ s, 0 < R s) (hR0 : β * R 0 = 1)
    (hL0 : ∀ j, L j 0 = 0) (dR : HasDerivAt (fun s => Real.log (R s)) rh 0)
    (dL : ∀ j, HasDerivAt (L j) (lh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * Real.exp (L j s)) :
    rh + ∑ j, q j * lh j = 0 := by
  have aR := nk_path_deriv hR dR
  have aS : HasDerivAt (fun s => ∑ j, q j * Real.exp (L j s))
      (∑ j, q j * (Real.exp (L j 0) * lh j)) 0 :=
    HasDerivAt.fun_sum fun j _ => ((dL j).exp).const_mul (q j)
  have hd := (aR.const_mul β).mul aS
  have e : (fun s => β * R s * ∑ j, q j * Real.exp (L j s)) = fun _ => 1 := funext fun s =>
    (h s).symm
  have hd' : HasDerivAt (fun s => β * R s * ∑ j, q j * Real.exp (L j s)) 0 0 := by
    rw [e]
    exact hasDerivAt_const _ _
  have hu := hd.unique hd'
  simp only [hL0, Real.exp_zero, one_mul, mul_one, hq] at hu
  have : β * (R 0 * rh) + β * R 0 * ∑ j, q j * lh j = rh + ∑ j, q j * lh j := by
    rw [show β * (R 0 * rh) = (β * R 0) * rh by ring, hR0, one_mul, one_mul]
  linarith

/-- **(19.26)** (Miao, p. 626): log-linearising the Euler equation (19.3) with `C = Y`. With
finitely many successor states `j` (probabilities `q_j`), positive paths `Y(s), Y_j(s), P(s),
P_j(s), R(s) = 1 + i(s)` with `Y_j(0) = Y(0)`, `P_j(0) = P(0)`, `βR(0) = 1`, and
`1 = βR(s)∑_j q_j(Y_j(s)/Y(s))^{−γ}P(s)/P_j(s)` for every `s` (`γ ≠ 0`):
`ŷ = ∑_j q_jŷ_j − γ⁻¹(ı̂ − ∑_j q_jπ_j)`, `π_j = p̂_j − p̂`, `ı̂ = d ln(1 + i)`. -/
theorem eq_19_26 {n : ℕ} {β γ : ℝ} (hγ : γ ≠ 0) {q : Fin n → ℝ} {R Y P : ℝ → ℝ}
    {Yj Pj : Fin n → ℝ → ℝ} {ih yh ph : ℝ} {yjh pjh : Fin n → ℝ} (hq : ∑ j, q j = 1)
    (hR : ∀ s, 0 < R s) (hY : ∀ s, 0 < Y s) (hP : ∀ s, 0 < P s) (hYj : ∀ j s, 0 < Yj j s)
    (hPj : ∀ j s, 0 < Pj j s) (hR0 : β * R 0 = 1) (hY0 : ∀ j, Yj j 0 = Y 0)
    (hP0 : ∀ j, Pj j 0 = P 0)
    (dR : HasDerivAt (fun s => Real.log (R s)) ih 0)
    (dY : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (dP : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (dYj : ∀ j, HasDerivAt (fun s => Real.log (Yj j s)) (yjh j) 0)
    (dPj : ∀ j, HasDerivAt (fun s => Real.log (Pj j s)) (pjh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * ((Yj j s / Y s) ^ (-γ) * (P s / Pj j s))) :
    yh = ∑ j, q j * yjh j - γ⁻¹ * (ih - ∑ j, q j * (pjh j - ph)) := by
  set L : Fin n → ℝ → ℝ := fun j s =>
    -γ * (Real.log (Yj j s) - Real.log (Y s)) + (Real.log (P s) - Real.log (Pj j s))
  have hexp : ∀ j s, (Yj j s / Y s) ^ (-γ) * (P s / Pj j s) = Real.exp (L j s) := fun j s => by
    simp only [L]
    rw [Real.exp_add, Real.rpow_def_of_pos (div_pos (hYj j s) (hY s)),
      Real.log_div (hYj j s).ne' (hY s).ne', ← Real.log_div (hP s).ne' (hPj j s).ne',
      Real.exp_log (div_pos (hP s) (hPj j s)), mul_comm (-γ)]
  have hu := nk_loglin_euler (L := L) (lh := fun j => -γ * (yjh j - yh) + (ph - pjh j)) hq hR
    hR0 (fun j => by simp [L, hY0, hP0]) dR
    (fun j => ((((dYj j).sub dY).const_mul (-γ)).add (dP.sub (dPj j))))
    (fun s => by rw [h s]; simp only [hexp])
  have e1 : ∑ j, q j * (-γ * (yjh j - yh) + (ph - pjh j)) =
      -γ * (∑ j, q j * yjh j) + γ * yh - ∑ j, q j * (pjh j - ph) := by
    have : ∑ j, q j * (-γ * (yjh j - yh) + (ph - pjh j)) =
        ∑ j, (-γ * (q j * yjh j) + γ * yh * q j - q j * (pjh j - ph)) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hq]
    ring
  rw [e1] at hu
  field_simp
  linear_combination hu

/-- Miao, p. 627: the natural rate of interest. With finitely many successor states, if
`1 = βR^n(s)∑_j q_j(Y^f_j(s)/Y^f(s))^{−γ}` for every `s` (`R^n = 1 + r^n`, positive paths,
`Y^f_j(0) = Y^f(0)`, `βR^n(0) = 1`), then `r̂^n = γ(∑_j q_jŷ^f_j − ŷ^f)`, i.e.
`ln(1 + r^n) = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` to first order, which is (19.27):
`ŷ^f = ∑_j q_jŷ^f_j − γ⁻¹r̂^n`. -/
theorem nk_loglin_natural_rate {n : ℕ} {β γ : ℝ} (hγ : γ ≠ 0) {q : Fin n → ℝ} {R Y : ℝ → ℝ}
    {Yj : Fin n → ℝ → ℝ} {rh yh : ℝ} {yjh : Fin n → ℝ} (hq : ∑ j, q j = 1)
    (hR : ∀ s, 0 < R s) (hY : ∀ s, 0 < Y s) (hYj : ∀ j s, 0 < Yj j s) (hR0 : β * R 0 = 1)
    (hY0 : ∀ j, Yj j 0 = Y 0)
    (dR : HasDerivAt (fun s => Real.log (R s)) rh 0)
    (dY : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (dYj : ∀ j, HasDerivAt (fun s => Real.log (Yj j s)) (yjh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * (Yj j s / Y s) ^ (-γ)) :
    rh = γ * (∑ j, q j * yjh j - yh) ∧ yh = ∑ j, q j * yjh j - γ⁻¹ * rh := by
  have h' := eq_19_26 (P := fun _ => 1) (Pj := fun _ _ => 1) (ph := 0) (pjh := fun _ => 0)
    hγ hq hR hY (fun _ => one_pos) hYj (fun _ _ => one_pos) hR0 hY0 (fun _ => rfl) dR dY
    (by simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)) dYj
    (fun _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (fun s => by simpa using h s)
  simp only [sub_zero, mul_zero, Finset.sum_const_zero] at h'
  refine ⟨?_, h'⟩
  rw [h']
  field_simp
  ring

/-- **(19.29)** (Miao, p. 627): the Taylor rule (19.14) in logs is exactly
`ln(1 + i_t) = −ln β + φ_π ln Π_t + φ_y ln(Y_t/Y^f_t) + v_t` (`β > 0`, `1 + i_t > 0`). -/
theorem eq_19_29 {φπ φy β i Pt Ptm1 Y Yf v : ℝ} (hβ : 0 < β) (hi : 0 < 1 + i) :
    nk_taylorRule φπ φy β i Pt Ptm1 Y Yf v ↔
      Real.log (1 + i) = -Real.log β + φπ * Real.log (Pt / Ptm1) + φy * Real.log (Y / Yf) + v := by
  rw [nk_taylorRule, show (1 : ℝ) + (1 / β - 1) = 1 / β by ring,
    Real.log_div hi.ne' (by positivity), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

end Miao.NewKeynesian
