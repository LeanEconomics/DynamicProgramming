/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.PPP
import StickyPriceModels.ReduxLogLinear

/-!
# The log-linear system as exact derivatives

AKMM, §23.3.3–§23.3.4, (23.21)–(23.27), pp. 714–718.

"Log-linearised" statements are made precise as exact derivatives at the symmetric
non-stochastic steady state `p_H = p_F = 1`, `P = P* = 1`, `Q = T = 1`, `C = C* = Ȳ`. We perturb
every variable along a ray: `p_H = e^{t·ph}`, `p_F = e^{t·pf}` (so the log terms of trade move by
`T̂ = pf − ph`), `C = Ȳe^{tĉ}`, `C* = Ȳe^{tĉ*}`, `Y_H = Ȳe^{tŷ}`, `Y_F = Ȳe^{tŷ*}`, and prove that
the derivative at `t = 0` of the log of each nonlinear object is the book's linear expression:

* the CPI (23.4): `P̂ = aph + (1−a)pf` (from Obstfeld–Rogoff's `hasDerivAt_log_bloc`);
* (23.21): `Q̂ = (a_H − a*_H)T̂`, i.e. `(2a_H − 1)T̂` when `a*_H = 1 − a_H` (`eq_23_21`);
* (23.22) is exact in logs: `log W = σ(log C − log C*) − log Q` (`eq_23_22`);
* the world demands for each good, `D̂_H = aĉ + (1−a)ĉ* + 2a(1−a)φT̂` and
  `D̂_F = (1−a)ĉ + aĉ* − 2a(1−a)φT̂` (`loglin_DH`, `loglin_DF`), hence (23.23) and world
  consumption `Ĉ + Ĉ* = D̂_H + D̂_F` (`eq_23_23`, `loglin_world`);
* (23.25): the autarky wealth gap (`eq_23_25`);
* (23.27): the bond-economy wealth gap (`eq_23_27`), with the bond position measured as in the
  correction recorded in `docs/corrections.md`.

The algebraic consequences (23.24) and (23.26) follow (`eq_23_24`, `eq_23_26`), with fn 28.
Throughout `0 < a < 1`, `φ > 0`, `φ ≠ 1` for the nonlinear objects.
-/

namespace AKMM.InternationalMacro

open Real
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos)
open ObstfeldRogoff.StickyPriceModels.ReduxLogLinear (hasDerivAt_log_bloc log_demand_exact)

/-- The CPI along the ray `p_H = e^{t·ph}`, `p_F = e^{t·pf}`. -/
noncomputable def loglinP (a φ ph pf t : ℝ) : ℝ := blocPriceIndex φ a (exp (t * ph)) (exp (t * pf))

/-- The CPI along the ray is positive. -/
theorem loglinP_pos {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) : 0 < loglinP a φ ph pf t :=
  blocPriceIndex_pos ha0 ha1 (exp_pos _) (exp_pos _)

/-- At the steady state `t = 0` the CPI is one. -/
theorem loglinP_zero (a φ ph pf : ℝ) : loglinP a φ ph pf 0 = 1 := by
  simp [loglinP, blocPriceIndex]

/-- AKMM, (23.4) log-linearised (used for (23.21)–(23.27)): `P̂ = a p̂_H + (1−a) p̂_F`. -/
theorem loglinP_hasDerivAt {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP a φ ph pf t)) (a * ph + (1 - a) * pf) 0 := by
  have h := hasDerivAt_log_bloc (θ := φ) (A := 1) (α := ph) (β := pf) hφ ha0 ha1 one_pos
  simpa [loglinP] using h

/-- A positive function whose log has derivative `d` at `0` has derivative `f 0 · d`. -/
theorem loglin_hasDerivAt_of_log {f : ℝ → ℝ} {d : ℝ} (hf : ∀ t, 0 < f t)
    (h : HasDerivAt (fun t => log (f t)) d 0) : HasDerivAt f (f 0 * d) 0 := by
  have h2 := h.exp
  rw [exp_log (hf 0)] at h2
  convert h2 using 1
  funext t
  rw [exp_log (hf t)]

/-- The log of a weighted sum of two positive functions that agree at `0` moves by the weighted
sum of their log-derivatives. -/
theorem loglin_log_weighted {f g : ℝ → ℝ} {n K df dg : ℝ} (hf : ∀ t, 0 < f t)
    (hg : ∀ t, 0 < g t) (hf0 : f 0 = K) (hg0 : g 0 = K) (hK : 0 < K)
    (hdf : HasDerivAt (fun t => log (f t)) df 0) (hdg : HasDerivAt (fun t => log (g t)) dg 0) :
    HasDerivAt (fun t => log (n * f t + (1 - n) * g t)) (n * df + (1 - n) * dg) 0 := by
  have h1 := loglin_hasDerivAt_of_log hf hdf
  have h2 := loglin_hasDerivAt_of_log hg hdg
  have hs : HasDerivAt (fun t => n * f t + (1 - n) * g t)
      (n * (f 0 * df) + (1 - n) * (g 0 * dg)) 0 := (h1.const_mul n).add (h2.const_mul (1 - n))
  have hv : n * f 0 + (1 - n) * g 0 = K := by rw [hf0, hg0]; ring
  have hl := hs.log (by rw [hv]; exact hK.ne')
  convert hl using 1
  rw [hv, hf0, hg0]
  field_simp

/-- **(23.21)** (general weights), AKMM p. 714: the log real exchange rate `log(P*/P)` moves by
`(a_H − a*_H)T̂`, `T̂ = pf − ph`. -/
theorem loglin_rer {a as φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as) (has1 : as < 1)
    (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP as φ ph pf t / loglinP a φ ph pf t))
      ((a - as) * (pf - ph)) 0 := by
  have h := (loglinP_hasDerivAt (ph := ph) (pf := pf) has0 has1 hφ).sub
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)
  have e : (fun t => log (loglinP as φ ph pf t / loglinP a φ ph pf t))
      = fun t => log (loglinP as φ ph pf t) - log (loglinP a φ ph pf t) := by
    funext t
    rw [log_div (loglinP_pos has0 has1 t).ne' (loglinP_pos ha0 ha1 t).ne']
  rw [e]
  convert h using 1
  ring

/-- **(23.21)**, AKMM p. 714: with symmetric home bias `a*_H = 1 − a_H`,
`Q̂_t = (2a_H − 1)T̂_t`. -/
theorem eq_23_21 {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t))
      ((2 * a - 1) * (pf - ph)) 0 := by
  have h := loglin_rer (ph := ph) (pf := pf) ha0 ha1 (by linarith : (0 : ℝ) < 1 - a)
    (by linarith : 1 - a < 1) hφ
  convert h using 1
  ring

/-- **(23.22)**, AKMM p. 714, exact in logs: with `W = (C/C*)^σ/Q` (23.16),
`log W = σ(log C − log C*) − log Q`. -/
theorem eq_23_22 {σ C Cs Q : ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hQ : 0 < Q) :
    log ((C / Cs) ^ σ / Q) = σ * (log C - log Cs) - log Q := by
  rw [log_div (rpow_pos_of_pos (div_pos hC hCs) σ).ne' hQ.ne', log_rpow (div_pos hC hCs),
    log_div hC.ne' hCs.ne']

/-- The log of a CES demand `(p/P)^{−φ}C` along the ray moves by `−φ(p̂ − P̂) + Ĉ`. -/
theorem loglin_demand {φ dp dP dC : ℝ} {p P C : ℝ → ℝ} (hp : ∀ t, 0 < p t) (hP : ∀ t, 0 < P t)
    (hC : ∀ t, 0 < C t) (hdp : HasDerivAt (fun t => log (p t)) dp 0)
    (hdP : HasDerivAt (fun t => log (P t)) dP 0) (hdC : HasDerivAt (fun t => log (C t)) dC 0) :
    HasDerivAt (fun t => log (cesDemand φ (p t) (P t) (C t))) (-φ * (dp - dP) + dC) 0 := by
  have e : (fun t => log (cesDemand φ (p t) (P t) (C t)))
      = fun t => -φ * (log (p t) - log (P t)) + log (C t) := by
    funext t
    exact log_demand_exact (hp t) (hP t) (hC t)
  rw [e]
  exact ((hdp.sub hdP).const_mul (-φ)).add hdC

/-- `log(K e^{tc})` has derivative `c` at `0`. -/
theorem loglin_exp_ray (K c : ℝ) (hK : 0 < K) :
    HasDerivAt (fun t => log (K * exp (t * c))) c 0 := by
  have e : (fun t => log (K * exp (t * c))) = fun t => log K + t * c := by
    funext t; rw [log_mul hK.ne' (exp_pos _).ne', log_exp]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (log K)

/-- The world demand `D_H = c_H + c*_H` for the home good along the ray (AKMM p. 715): home
demand (23.3) with weight `a` at the home CPI and foreign demand with weight `1 − a` at the foreign
CPI. -/
noncomputable def loglinDH (a φ ph pf c cs Ybar t : ℝ) : ℝ :=
  a * cesDemand φ (exp (t * ph)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
    + (1 - a) * cesDemand φ (exp (t * ph)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs))

/-- The world demand `D*_F = c_F + c*_F` for the foreign good along the ray (AKMM p. 715). -/
noncomputable def loglinDF (a φ ph pf c cs Ybar t : ℝ) : ℝ :=
  (1 - a) * cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
    + a * cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs))

/-- AKMM, p. 715: the world demand for the home good `D_H = c_H + c*_H` (with (23.3) at home and
abroad, weights `a` and `1 − a`) log-linearises to `D̂_H = aĈ + (1−a)Ĉ* + 2a(1−a)φT̂`. -/
theorem loglin_DH {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t))
      (a * c + (1 - a) * cs + 2 * a * (1 - a) * φ * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ γ : ℝ, HasDerivAt (fun t => log (exp (t * γ))) γ 0 := by
    intro γ; simpa using loglin_exp_ray 1 γ one_pos
  have hf := loglin_demand (φ := φ) (p := fun t => exp (t * ph)) (fun t => exp_pos _)
    (loglinP_pos ha0 ha1) (fun t => mul_pos hY (exp_pos (t * c))) (hexp ph)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ) (loglin_exp_ray Ybar c hY)
  have hg := loglin_demand (φ := φ) (p := fun t => exp (t * ph)) (fun t => exp_pos _)
    (loglinP_pos h1a (by linarith)) (fun t => mul_pos hY (exp_pos (t * cs))) (hexp ph)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ) (loglin_exp_ray Ybar cs hY)
  have h0 : ∀ n : ℝ,
      cesDemand φ (exp (0 * ph)) (loglinP n φ ph pf 0) (Ybar * exp (0 * c)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have h0s : ∀ n : ℝ,
      cesDemand φ (exp (0 * ph)) (loglinP n φ ph pf 0) (Ybar * exp (0 * cs)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have hw := loglin_log_weighted (n := a)
    (f := fun t => cesDemand φ (exp (t * ph)) (loglinP a φ ph pf t) (Ybar * exp (t * c)))
    (g := fun t => cesDemand φ (exp (t * ph)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos ha0 ha1 t) (mul_pos hY (exp_pos _)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos h1a (by linarith) t) (mul_pos hY (exp_pos _))) (h0 a) (h0s (1 - a)) hY hf hg
  refine hw.congr_deriv ?_
  ring

/-- AKMM, p. 715: the world demand for the foreign good `D*_F = c_F + c*_F` log-linearises to
`D̂*_F = (1−a)Ĉ + aĈ* − 2a(1−a)φT̂`. -/
theorem loglin_DF {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDF a φ ph pf c cs Ybar t))
      ((1 - a) * c + a * cs - 2 * a * (1 - a) * φ * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ γ : ℝ, HasDerivAt (fun t => log (exp (t * γ))) γ 0 := by
    intro γ; simpa using loglin_exp_ray 1 γ one_pos
  have hf := loglin_demand (φ := φ) (p := fun t => exp (t * pf)) (fun t => exp_pos _)
    (loglinP_pos ha0 ha1) (fun t => mul_pos hY (exp_pos (t * c))) (hexp pf)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ) (loglin_exp_ray Ybar c hY)
  have hg := loglin_demand (φ := φ) (p := fun t => exp (t * pf)) (fun t => exp_pos _)
    (loglinP_pos h1a (by linarith)) (fun t => mul_pos hY (exp_pos (t * cs))) (hexp pf)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ) (loglin_exp_ray Ybar cs hY)
  have h0 : ∀ n : ℝ,
      cesDemand φ (exp (0 * pf)) (loglinP n φ ph pf 0) (Ybar * exp (0 * c)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have h0s : ∀ n : ℝ,
      cesDemand φ (exp (0 * pf)) (loglinP n φ ph pf 0) (Ybar * exp (0 * cs)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have hw := loglin_log_weighted (n := 1 - a)
    (f := fun t => cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c)))
    (g := fun t => cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos ha0 ha1 t) (mul_pos hY (exp_pos _)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos h1a (by linarith) t) (mul_pos hY (exp_pos _))) (h0 a) (h0s (1 - a)) hY hf hg
  have e : (fun t => log (loglinDF a φ ph pf c cs Ybar t)) = fun t =>
      log ((1 - a) * cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
        + (1 - (1 - a)) * cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t)
          (Ybar * exp (t * cs))) := by
    funext t; unfold loglinDF; ring_nf
  rw [e]
  refine hw.congr_deriv ?_
  ring

/-- **(23.23)**, AKMM p. 715: the relative world demand log-linearises to
`D̂_H − D̂*_F = (2a_H − 1)(Ĉ − Ĉ*) + 4a_H(1 − a_H)φT̂`. -/
theorem eq_23_23 {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t)
        - log (loglinDF a φ ph pf c cs Ybar t))
      ((2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * (pf - ph)) 0 := by
  refine ((loglin_DH ha0 ha1 hφ hY).sub (loglin_DF ha0 ha1 hφ hY)).congr_deriv ?_
  ring

/-- AKMM, p. 715: world demand equals world consumption to first order,
`D̂_H + D̂*_F = Ĉ + Ĉ*`; with goods-market clearing `D = Y` this is `Ŷ_H + Ŷ*_F = Ĉ + Ĉ*`,
"independently of the structure of financial markets". -/
theorem loglin_world {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t)
        + log (loglinDF a φ ph pf c cs Ybar t)) (c + cs) 0 := by
  refine ((loglin_DH ha0 ha1 hφ hY).add (loglin_DF ha0 ha1 hφ hY)).congr_deriv ?_
  ring

/-- **(23.24)**, AKMM p. 716: substituting the wealth gap (23.22) `Ŵ = σ(Ĉ − Ĉ*) − Q̂` and
(23.21) `Q̂ = (2a − 1)T̂` into (23.23) gives
`D̂_H − D̂*_F = σ⁻¹(2a − 1)Ŵ + σ⁻¹[4a(1 − a)(σφ − 1) + 1]T̂`. -/
theorem eq_23_24 {a φ σ c cs q τ W : ℝ} (hσ : σ ≠ 0) (h21 : q = (2 * a - 1) * τ)
    (h22 : W = σ * (c - cs) - q) :
    (2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * τ
      = σ⁻¹ * (2 * a - 1) * W + σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ := by
  rw [h22, h21]
  field_simp
  ring

/-- The coefficient of `T̂` in (23.24) equals `4a(1 − a)φ + (2a − 1)²/σ`. -/
theorem loglin_coef_eq {a φ σ : ℝ} (hσ : σ ≠ 0) :
    σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) = 4 * a * (1 - a) * φ + (2 * a - 1) ^ 2 / σ := by
  field_simp
  ring

/-- **Footnote 28**, AKMM p. 716: the coefficient on `T̂` in (23.24) is positive and strictly
increasing in the trade elasticity `φ` (for `0 < a < 1`, `σ, φ > 0`). -/
theorem fn_28 {a σ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) :
    (∀ φ : ℝ, 0 < φ → 0 < σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1)) ∧
    StrictMono (fun φ : ℝ => σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1)) := by
  have h1a : 0 < 1 - a := by linarith
  constructor
  · intro φ hφ
    rw [loglin_coef_eq hσ.ne']
    have : 0 ≤ (2 * a - 1) ^ 2 / σ := div_nonneg (sq_nonneg _) hσ.le
    have : 0 < 4 * a * (1 - a) * φ := by positivity
    linarith
  · intro φ₁ φ₂ h
    simp only
    rw [loglin_coef_eq hσ.ne', loglin_coef_eq hσ.ne']
    have : 0 < 4 * a * (1 - a) := by positivity
    nlinarith

/-- The log of the autarky consumption `C = p_H Y_H/P` (23.15) along the ray. -/
theorem loglin_autarky_cons {a φ ph pf y Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t))
      (y - (1 - a) * (pf - ph)) 0 := by
  have e : (fun t => log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t))
      = fun t => log (exp (t * ph)) + log (Ybar * exp (t * y)) - log (loglinP a φ ph pf t) := by
    funext t
    rw [log_div (by positivity) (loglinP_pos ha0 ha1 t).ne',
      log_mul (exp_pos _).ne' (by positivity)]
  rw [e]
  have h1 : HasDerivAt (fun t => log (exp (t * ph))) ph 0 := by
    simpa using loglin_exp_ray 1 ph one_pos
  refine ((h1.add (loglin_exp_ray Ybar y hY)).sub
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)).congr_deriv ?_
  ring

/-- **(23.25)**, AKMM p. 716: under financial autarky (`C = p_H Y_H/P`, `C* = p_F Y*_F/P*`) the
log wealth gap `log W = σ(log C − log C*) − log Q` (23.22) moves by
`Ŵ^{FA} = σ[Ŷ_H − Ŷ*_F − 2(1 − a_H)T̂] − (2a_H − 1)T̂`. -/
theorem eq_23_25 {a φ σ ph pf y ys Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t =>
        log (((exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          / (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t)) ^ σ
          / (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t)))
      (σ * (y - ys - 2 * (1 - a) * (pf - ph)) - (2 * a - 1) * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have e : (fun t =>
        log (((exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          / (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t)) ^ σ
          / (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t)))
      = fun t => σ * (log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          - log (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t))
          - log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t) := by
    funext t
    have hP := loglinP_pos (φ := φ) (ph := ph) (pf := pf) ha0 ha1 t
    have hPs := loglinP_pos (φ := φ) (ph := ph) (pf := pf) h1a (by linarith) t
    exact eq_23_22 (by positivity) (by positivity) (div_pos hPs hP)
  rw [e]
  have hC := loglin_autarky_cons (ph := ph) (pf := pf) (y := y) ha0 ha1 hφ hY
  have hCs : HasDerivAt (fun t => log (exp (t * pf) * (Ybar * exp (t * ys))
      / loglinP (1 - a) φ ph pf t)) (ys + (1 - a) * (pf - ph)) 0 := by
    have e2 : (fun t => log (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t))
        = fun t => log (exp (t * pf)) + log (Ybar * exp (t * ys))
          - log (loglinP (1 - a) φ ph pf t) := by
      funext t
      rw [log_div (by positivity) (loglinP_pos h1a (by linarith) t).ne',
        log_mul (exp_pos _).ne' (by positivity)]
    rw [e2]
    have h1 : HasDerivAt (fun t => log (exp (t * pf))) pf 0 := by
      simpa using loglin_exp_ray 1 pf one_pos
    refine ((h1.add (loglin_exp_ray Ybar ys hY)).sub
      (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ)).congr_deriv ?_
    ring
  have hQ := eq_23_21 (ph := ph) (pf := pf) ha0 ha1 hφ
  refine (((hC.sub hCs).const_mul σ).sub hQ).congr_deriv ?_
  ring

/-- **(23.26)**, AKMM p. 716: under financial autarky, with the consumption gap
`Ĉ − Ĉ* = Ŷ_H − Ŷ*_F − 2(1 − a)T̂` (from (23.15), `loglin_autarky_cons`), the relative demand
(23.23) and market clearing `D̂_H − D̂*_F = Ŷ_H − Ŷ*_F` give
`D̂_H − D̂*_F = [1 − 2a_H(1 − φ)]T̂` (for `a_H < 1`). -/
theorem eq_23_26 {a φ c cs y ys τ D : ℝ} (ha1 : a < 1)
    (h23 : D = (2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * τ)
    (hFA : c - cs = y - ys - 2 * (1 - a) * τ) (hclear : D = y - ys) :
    D = (1 - 2 * a * (1 - φ)) * τ := by
  have h1a : (1 - a) ≠ 0 := by linarith
  have key : 2 * (1 - a) * D = 2 * (1 - a) * ((1 - 2 * a * (1 - φ)) * τ) := by
    rw [hFA] at h23
    nlinarith
  exact mul_left_cancel₀ (by positivity) key

/-- AKMM, p. 716: (23.26) equivalently from (23.24) and (23.25): substituting the autarky wealth
gap (23.25) into (23.24) and imposing `D̂ = Ŷ` gives the same schedule. -/
theorem eq_23_26_of_24_25 {a φ σ y ys τ W D : ℝ} (hσ : 0 < σ) (ha1 : a < 1)
    (h24 : D = σ⁻¹ * (2 * a - 1) * W + σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ)
    (h25 : W = σ * (y - ys - 2 * (1 - a) * τ) - (2 * a - 1) * τ) (hclear : D = y - ys) :
    D = (1 - 2 * a * (1 - φ)) * τ := by
  have h1a : 0 < 1 - a := by linarith
  have h' : D = (2 * a - 1) * (y - ys - 2 * (1 - a) * τ) + 4 * a * (1 - a) * φ * τ := by
    rw [h24, h25]
    field_simp
    ring
  exact eq_23_26 ha1 h' rfl hclear

/-- Bond-economy consumption along the ray (AKMM p. 713): `C = (p Y − Q_b B + B_{−1})/P`, with
income price `p = e^{t·pinc}`, output `Y = Ȳe^{ty}`, bond price `Q_b = β₀e^{t·qb}` and nominal bond
positions `B = tȲ·bb`, `B_{−1} = tȲ·bbm` (zero at the steady state, `P_{−1} = 1`), so that
`bb`, `bbm` are the first-order real bond positions `b/Ȳ`. -/
noncomputable def loglinBondCons (n φ ph pf pinc y bb bbm qb β₀ Ybar t : ℝ) : ℝ :=
  (exp (t * pinc) * (Ybar * exp (t * y)) - β₀ * exp (t * qb) * (t * Ybar * bb) + t * Ybar * bbm)
    / loglinP n φ ph pf t

/-- The log of bond-economy consumption moves by `p̂ + Ŷ − β₀ bb + bbm − P̂` (the linearised
budget constraint of AKMM p. 713). -/
theorem loglin_bond_cons {n φ ph pf pinc y bb bbm qb β₀ Ybar : ℝ} (hn0 : 0 < n) (hn1 : n < 1)
    (hφ : φ ≠ 1) (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinBondCons n φ ph pf pinc y bb bbm qb β₀ Ybar t))
      (pinc + y - β₀ * bb + bbm - (n * ph + (1 - n) * pf)) 0 := by
  have he : ∀ k : ℝ, HasDerivAt (fun t => exp (t * k)) k 0 := by
    intro k
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).exp
  have hlin : ∀ k : ℝ, HasDerivAt (fun t => t * k) k 0 := by
    intro k; simpa using (hasDerivAt_id (0 : ℝ)).mul_const k
  have h1 : HasDerivAt (fun t => exp (t * pinc) * (Ybar * exp (t * y))) (Ybar * (pinc + y)) 0 := by
    convert (he pinc).mul ((he y).const_mul Ybar) using 1
    simp; ring
  have h2 : HasDerivAt (fun t => β₀ * exp (t * qb) * (t * Ybar * bb)) (β₀ * Ybar * bb) 0 := by
    convert ((he qb).const_mul β₀).mul (hlin (Ybar * bb)) using 1
    · funext t; simp only [Pi.mul_apply]; ring
    · simp; ring
  have h3 : HasDerivAt (fun t => t * Ybar * bbm) (Ybar * bbm) 0 := by
    convert hlin (Ybar * bbm) using 1
    funext t; ring
  set N : ℝ → ℝ := fun t => exp (t * pinc) * (Ybar * exp (t * y))
      - β₀ * exp (t * qb) * (t * Ybar * bb) + t * Ybar * bbm with hNdef
  have hN : HasDerivAt N (Ybar * (pinc + y) - β₀ * Ybar * bb + Ybar * bbm) 0 := (h1.sub h2).add h3
  have hN0 : N 0 = Ybar := by simp [hNdef]
  have hP := loglin_hasDerivAt_of_log (loglinP_pos (φ := φ) (ph := ph) (pf := pf) hn0 hn1)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) hn0 hn1 hφ)
  rw [loglinP_zero, one_mul] at hP
  have hP0 : loglinP n φ ph pf 0 ≠ 0 := by rw [loglinP_zero]; exact one_ne_zero
  have hq : HasDerivAt (fun t => N t / loglinP n φ ph pf t)
      (((Ybar * (pinc + y) - β₀ * Ybar * bb + Ybar * bbm) * loglinP n φ ph pf 0
        - N 0 * (n * ph + (1 - n) * pf)) / loglinP n φ ph pf 0 ^ 2) 0 := hN.div hP hP0
  have hv : N 0 / loglinP n φ ph pf 0 = Ybar := by rw [loglinP_zero, hN0, div_one]
  have hl := hq.log (by rw [hv]; exact hY.ne')
  unfold loglinBondCons
  refine hl.congr_deriv ?_
  rw [hv, loglinP_zero, hN0]
  field_simp

/-- **(23.27)**, AKMM p. 718: in the bond economy (bonds in zero net supply, so the foreign
position is the negative of the home one) the log wealth gap
`σ(log C − log C*) − log Q` (23.22) moves by
`σ[Ŷ_H − Ŷ*_F − 2(1 − a)T̂] − (2a − 1)T̂ + 2σ(bbm − β bb)`, where `bb`, `bbm` are the real bond
positions `b_t/Ȳ`, `b_{t−1}/Ȳ`. With `b̃ = β b/Ȳ` (the steady-state value of the position,
the convention of (23.30)) the last term is the printed `2σβ⁻¹[b̃_{t−1} − βb̃_t]`
(`loglin_bond_printed`). -/
theorem eq_23_27 {a φ σ ph pf y ys bb bbm qb β₀ Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : φ ≠ 1) (hY : 0 < Ybar) :
    HasDerivAt (fun t => σ * (log (loglinBondCons a φ ph pf ph y bb bbm qb β₀ Ybar t)
        - log (loglinBondCons (1 - a) φ ph pf pf ys (-bb) (-bbm) qb β₀ Ybar t))
        - log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t))
      (σ * (y - ys - 2 * (1 - a) * (pf - ph)) - (2 * a - 1) * (pf - ph)
        + 2 * σ * (bbm - β₀ * bb)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hC := loglin_bond_cons (pinc := ph) (y := y) (bb := bb) (bbm := bbm) (qb := qb)
    (β₀ := β₀) (ph := ph) (pf := pf) ha0 ha1 hφ hY
  have hCs := loglin_bond_cons (pinc := pf) (y := ys) (bb := -bb) (bbm := -bbm) (qb := qb)
    (β₀ := β₀) (ph := ph) (pf := pf) h1a (by linarith) hφ hY
  have hQ := eq_23_21 (ph := ph) (pf := pf) ha0 ha1 hφ
  refine (((hC.sub hCs).const_mul σ).sub hQ).congr_deriv ?_
  ring

/-- AKMM, (23.27), p. 718: the bond term `2σ(bbm − β bb)` equals the printed
`2σβ⁻¹[b̃_{t−1} − βb̃_t]` when the positions are measured at steady-state value,
`b̃ = β·bb`. -/
theorem loglin_bond_printed {σ β₀ bb bbm : ℝ} (hβ : β₀ ≠ 0) :
    2 * σ * (bbm - β₀ * bb) = 2 * σ * β₀⁻¹ * (β₀ * bbm - β₀ * (β₀ * bb)) := by
  field_simp

end AKMM.InternationalMacro
