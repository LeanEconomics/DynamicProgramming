/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Complete markets: Euler equations, UIP and full risk sharing

AKMM, §23.3.2, (23.9)–(23.13) and (23.16), pp. 708–712.

Uncertainty is Miao's event tree `BPTree S` (histories are lists over a finite shock set, most
recent shock first, with strictly positive probabilities), so `Pr(s_{t+1}|sᵗ)` is
`T.pr (s :: h)/T.pr h` and `Eₜ` is `bp_condExp T 1`. A home Arrow–Debreu security bought at
history `h` pays one unit of currency in state `s` and costs `q h s`; with `𝓔 = 1` the foreign
securities pay the same currency and, by no arbitrage, cost the same (fn 19). With marginal
utility `μ = u′` (any function), we prove from the Euler equations (23.9) of the two countries:

* the riskless gross returns (23.10): `1/R = βEₜ[u′(C_{t+1})]/u′(C_t)` and its foreign analogue
  (`eq_23_10`), and the real UIP condition (23.11)
  `1/R* = βEₜ[u′(C_{t+1})Q_{t+1}/Q_t]/u′(C_t)` (`eq_23_11`);
* `R > 0` (`rs_return_pos`), but **not** the book's `R_t ≥ 1`: a deterministic economy with
  falling consumption has `R = 1/2` (`rs_return_lt_one`);
* state-by-state risk sharing (23.12) (`eq_23_12`), hence `u′(C_t)Q_t/u′(C*_t) = κ₀` at every
  history (`rs_kappa_const`), and under CRRA `Q_t = κ₀(C_t/C*_t)^σ` (23.13) (`eq_23_13`);
* the wealth gap (23.16) `W = χ*/χ = (C/C*)^σ/Q` (`eq_23_16`), constant and equal to `1/κ₀`
  under complete markets (`rs_wealth_const`).

The Euler equations are taken as hypotheses (first-order conditions of the household problem,
as in the book).
-/

namespace AKMM.InternationalMacro

open Real Finset
open Miao.CompleteMarkets (BPTree bp_condExp bp_condExp_succ bp_condExp_zero bp_detTree)

variable {S : Type*} [Fintype S]

/-- The conditional expectation `Eₜ[x_{t+1}]` at history `h` written out on the tree. -/
theorem rs_condExp_one (T : BPTree S) (x : List S → ℝ) (h : List S) :
    bp_condExp T 1 x h = ∑ s, T.pr (s :: h) / T.pr h * x (s :: h) := by
  rw [bp_condExp_succ]
  rfl

/-- **(23.10)**, AKMM p. 709: from the home Euler equations (23.9), the cost
`(1/P_t) Σ_s q_t(s) P_{t+1}(s)` of one sure unit of the home basket, `1/R_t`, equals
`βEₜ[u′(C_{t+1})]/u′(C_t)`; likewise abroad with the foreign Euler equations. -/
theorem eq_23_10 (T : BPTree S) {mu : ℝ → ℝ} {C P : List S → ℝ} {q : List S → S → ℝ} {β : ℝ}
    (h : List S) (hmu : mu (C h) ≠ 0) (hP : ∀ h, P h ≠ 0)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    (∑ s, q h s * P (s :: h)) / P h = β * bp_condExp T 1 (fun h' => mu (C h')) h / mu (C h) := by
  rw [rs_condExp_one, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e := heuler s
  have hPs := hP (s :: h)
  have hPh := hP h
  field_simp at e ⊢
  linear_combination e

/-- **(23.11)**, real UIP, AKMM p. 710: investing in foreign securities, which by no arbitrage
cost the same `q` (`𝓔 = 1`), the cost `(1/P*_t)Σ_s q_t(s)P*_{t+1}(s)` of a sure unit of the
foreign basket, `1/R*_t`, equals `βEₜ[u′(C_{t+1})Q_{t+1}/Q_t]/u′(C_t)` with `Q = P*/P`, using the
home Euler equations alone. -/
theorem eq_23_11 (T : BPTree S) {mu : ℝ → ℝ} {C P Ps : List S → ℝ} {q : List S → S → ℝ}
    {β : ℝ} (h : List S) (hmu : mu (C h) ≠ 0) (hP : ∀ h, P h ≠ 0) (hPs : ∀ h, Ps h ≠ 0)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    (∑ s, q h s * Ps (s :: h)) / Ps h
      = β * bp_condExp T 1 (fun h' => mu (C h') * (Ps h' / P h')) h
        / (mu (C h) * (Ps h / P h)) := by
  rw [rs_condExp_one, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e := heuler s
  have h1 := hP (s :: h)
  have h2 := hP h
  have h3 := hPs (s :: h)
  have h4 := hPs h
  field_simp at e ⊢
  linear_combination e

/-- AKMM, p. 709: with positive prices, probabilities and marginal utilities, the riskless cost
`1/R` is positive, so the gross real return `R` is positive. -/
theorem rs_return_pos (T : BPTree S) [Nonempty S] {mu : ℝ → ℝ} {C P : List S → ℝ}
    {q : List S → S → ℝ} {β : ℝ} (h : List S) (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h))
    (hP : ∀ h, 0 < P h)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    0 < (∑ s, q h s * P (s :: h)) / P h := by
  rw [eq_23_10 T h (hmu h).ne' (fun h => (hP h).ne') heuler, rs_condExp_one]
  have hsum : 0 < ∑ s, T.pr (s :: h) / T.pr h * mu (C (s :: h)) :=
    Finset.sum_pos (fun s _ => mul_pos (div_pos (T.pr_pos _) (T.pr_pos _)) (hmu _))
      Finset.univ_nonempty
  exact div_pos (mul_pos hβ hsum) (hmu h)

/-- AKMM, p. 709 (corrected): "the gross real return `R_t ≥ 1`" does not follow. In the
deterministic tree with log utility (`u′(C) = 1/C`), `β = 1/2`, `P ≡ 1` and consumption falling
by a factor four each period, `C_t = 4^{−t}`, the Euler equation (23.9) holds with `q = 2`, so the
riskless cost is `1/R = 2` and `R = 1/2 < 1`. -/
theorem rs_return_lt_one :
    let C : List Unit → ℝ := fun h => (1 / 4) ^ h.length
    let q : List Unit → Unit → ℝ := fun _ _ => 2
    (∀ h s, (C h)⁻¹ * q h s / 1
        = bp_detTree.pr (s :: h) / bp_detTree.pr h * (1 / 2) * (C (s :: h))⁻¹ / 1) ∧
      ∀ h, (∑ s, q h s * 1) / 1 = (2 : ℝ) := by
  intro C q
  refine ⟨fun h s => ?_, fun h => ?_⟩
  · simp only [C, q, bp_detTree, List.length_cons, div_one, one_div, inv_pow, inv_inv, pow_succ]
    ring
  · simp [q]

/-- **(23.12)**, AKMM p. 710: if both countries' Euler equations (23.9) hold with the same
Arrow–Debreu prices (no arbitrage, `𝓔 = 1`), then
`u′(C_t)P*_t/(u′(C*_t)P_t) = u′(C_{t+1})P*_{t+1}/(u′(C*_{t+1})P_{t+1})` in every state. -/
theorem eq_23_12 (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ}
    {β : ℝ} (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h)) (hmus : ∀ h, 0 < mu (Cs h))
    (hP : ∀ h, 0 < P h) (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h))
    (heulers : ∀ h s, mu (Cs h) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * mu (Cs (s :: h)) / Ps (s :: h)) (h : List S) (s : S) :
    mu (C h) * Ps h / (mu (Cs h) * P h)
      = mu (C (s :: h)) * Ps (s :: h) / (mu (Cs (s :: h)) * P (s :: h)) := by
  have e1 := heuler h s
  have e2 := heulers h s
  have hpr : 0 < T.pr (s :: h) / T.pr h := div_pos (T.pr_pos _) (T.pr_pos _)
  have hq : 0 < q h s := by
    have : 0 < mu (C h) * q h s / P h := by
      rw [e1]; have := hmu (s :: h); have := hP (s :: h); positivity
    have h' : 0 < mu (C h) * q h s := by
      have := hP h
      exact (div_pos_iff_of_pos_right this).mp ‹_›
    exact pos_of_mul_pos_right h' (hmu h).le
  have := hmu h; have := hmus h; have := hP h; have := hPs h
  have := hmu (s :: h); have := hmus (s :: h); have := hP (s :: h); have := hPs (s :: h)
  field_simp at e1 e2 ⊢
  apply mul_left_cancel₀ hq.ne'
  linear_combination (Ps h * mu (Cs (s :: h))) * e1 - (P h * mu (C (s :: h))) * e2

/-- AKMM, p. 710: under complete markets the marginal-utility-weighted real exchange rate is
constant on the whole tree: `u′(C_t)Q_t/u′(C*_t) = κ₀ = u′(C₀)Q₀/u′(C*₀)` at every history,
with `Q = P*/P`. -/
theorem rs_kappa_const (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ}
    {q : List S → S → ℝ} {β : ℝ} (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h))
    (hmus : ∀ h, 0 < mu (Cs h)) (hP : ∀ h, 0 < P h) (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h))
    (heulers : ∀ h s, mu (Cs h) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * mu (Cs (s :: h)) / Ps (s :: h)) (h : List S) :
    mu (C h) * Ps h / (mu (Cs h) * P h) = mu (C []) * Ps [] / (mu (Cs []) * P []) := by
  induction h with
  | nil => rfl
  | cons s h ih =>
    rw [← ih]
    exact (eq_23_12 T hβ hmu hmus hP hPs heuler heulers h s).symm

/-- **(23.13)**, AKMM p. 710: with CRRA utility, `u′(C) = C^{−σ}`, full risk sharing reads
`Q_t = κ₀(C_t/C*_t)^σ` at every history, `κ₀ = C₀^{−σ}Q₀/C*₀^{−σ}`. -/
theorem eq_23_13 (T : BPTree S) {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ} {β σ : ℝ}
    (hβ : 0 < β) (hC : ∀ h, 0 < C h) (hCs : ∀ h, 0 < Cs h) (hP : ∀ h, 0 < P h)
    (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, C h ^ (-σ) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * C (s :: h) ^ (-σ) / P (s :: h))
    (heulers : ∀ h s, Cs h ^ (-σ) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * Cs (s :: h) ^ (-σ) / Ps (s :: h)) (h : List S) :
    Ps h / P h = C [] ^ (-σ) * Ps [] / (Cs [] ^ (-σ) * P []) * (C h / Cs h) ^ σ := by
  have hk := rs_kappa_const T (mu := fun c => c ^ (-σ)) hβ (fun h => rpow_pos_of_pos (hC h) _)
    (fun h => rpow_pos_of_pos (hCs h) _) hP hPs heuler heulers h
  rw [← hk, div_rpow (hC h).le (hCs h).le]
  have h1 := rpow_pos_of_pos (hC h) σ
  have h2 := rpow_pos_of_pos (hCs h) σ
  rw [rpow_neg (hC h).le, rpow_neg (hCs h).le]
  have := (hP h).ne'
  field_simp

/-- **(23.16)**, AKMM p. 712: with CRRA utility the ratio of the Lagrange multipliers
`χ = u′(C)/P` is `W = χ*/χ = (C/C*)^σ/Q`, `Q = P*/P`. -/
theorem eq_23_16 {σ C Cs P Ps : ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hP : 0 < P) (hPs : 0 < Ps) :
    (Cs ^ (-σ) / Ps) / (C ^ (-σ) / P) = (C / Cs) ^ σ / (Ps / P) := by
  rw [rpow_neg hC.le, rpow_neg hCs.le, div_rpow hC.le hCs.le]
  have := (rpow_pos_of_pos hC σ).ne'
  have := (rpow_pos_of_pos hCs σ).ne'
  field_simp

/-- AKMM, p. 712: "`W_t` is constant over time in the complete-markets model": with CRRA utility
and complete markets, `W = χ*/χ = 1/κ₀` at every history. -/
theorem rs_wealth_const (T : BPTree S) {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ} {β σ : ℝ}
    (hβ : 0 < β) (hC : ∀ h, 0 < C h) (hCs : ∀ h, 0 < Cs h) (hP : ∀ h, 0 < P h)
    (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, C h ^ (-σ) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * C (s :: h) ^ (-σ) / P (s :: h))
    (heulers : ∀ h s, Cs h ^ (-σ) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * Cs (s :: h) ^ (-σ) / Ps (s :: h)) (h : List S) :
    (Cs h ^ (-σ) / Ps h) / (C h ^ (-σ) / P h)
      = (C [] ^ (-σ) * Ps [] / (Cs [] ^ (-σ) * P []))⁻¹ := by
  have hk := rs_kappa_const T (mu := fun c => c ^ (-σ)) hβ (fun h => rpow_pos_of_pos (hC h) _)
    (fun h => rpow_pos_of_pos (hCs h) _) hP hPs heuler heulers h
  rw [← hk]
  have := (rpow_pos_of_pos (hC h) (-σ)).ne'
  have := (rpow_pos_of_pos (hCs h) (-σ)).ne'
  have := (hP h).ne'
  have := (hPs h).ne'
  field_simp

end AKMM.InternationalMacro
