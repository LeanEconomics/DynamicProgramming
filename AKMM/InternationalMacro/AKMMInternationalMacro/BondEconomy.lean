/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.RiskSharing
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The bond economy: UIP, the covariance form and the zero-mean wealth wedge

AKMM, §23.3.2 "Riskless bonds only" and §23.3.3, (23.17)–(23.20), pp. 713–714.

On Miao's event tree, with the Euler equation (23.17) `Q_t = βEₜ[u′(C_{t+1})P_t/(u′(C_t)P_{t+1})]`
at home and abroad and one bond price (no arbitrage, `𝓔 = 1`), we prove:

* the real UIP condition (23.18) (`eq_23_18`);
* its covariance form (23.19) with the real rate `R⁻¹ = βEₜ[m]`, `m = u′(C_{t+1})/u′(C_t)`,
  `π = P_t/P_{t+1}`: `R⁻¹Eₜ[π] + β covₜ(m, π) = R*⁻¹Eₜ[π*] + β covₜ(m*, π*)` (`eq_23_19`). The
  book prints the covariances without the factor `β`; that version is false
  (`eq_23_19_printed_counterexample`);
* the wedge (23.20) `ε = χ_{t+1}/χ_t − χ*_{t+1}/χ*_t` has zero conditional mean (`eq_23_20`,
  `bond_wedge_mean_zero`);
* linearised, with `χ_{t+1}/χ_t = e^{a}` and `χ*_{t+1}/χ*_t = e^{b}`: if the UIP condition
  `Eₜ[e^{ta} − e^{tb}] = 0` holds along a path of equilibria, then the first-order wedge
  `ε̂ = a − b` has `Eₜ[ε̂] = 0`, and the log wealth gap `log W = log χ* − log χ` moves by exactly
  `b − a = −ε̂`, so `Eₜ[Ŵ_{t+1} − Ŵ_t] = 0` (`bond_wealth_loglin`).
-/

namespace AKMM.InternationalMacro

open Real Finset Filter
open Miao.CompleteMarkets (BPTree bp_condExp bp_condExp_sub_fun bp_markovTree)

variable {S : Type*} [Fintype S]

/-- **(23.18)**, AKMM p. 713: if the home and foreign Euler equations (23.17) hold with the same
bond price `Q_t` (no arbitrage under `𝓔 = 1`), then
`Eₜ[u′(C_{t+1})P_t/(u′(C_t)P_{t+1})] = Eₜ[u′(C*_{t+1})P*_t/(u′(C*_t)P*_{t+1})]`. -/
theorem eq_23_18 (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ} {β Qb : ℝ} (h : List S)
    (hβ : β ≠ 0)
    (he : Qb = β * bp_condExp T 1 (fun h' => mu (C h') / mu (C h) * (P h / P h')) h)
    (hes : Qb = β * bp_condExp T 1 (fun h' => mu (Cs h') / mu (Cs h) * (Ps h / Ps h')) h) :
    bp_condExp T 1 (fun h' => mu (C h') / mu (C h) * (P h / P h')) h
      = bp_condExp T 1 (fun h' => mu (Cs h') / mu (Cs h) * (Ps h / Ps h')) h := by
  rw [he] at hes
  exact mul_left_cancel₀ hβ hes

/-- The conditional covariance `covₜ(x_{t+1}, y_{t+1})` at history `h`. -/
noncomputable def bondCov (T : BPTree S) (x y : List S → ℝ) (h : List S) : ℝ :=
  bp_condExp T 1 (fun h' => x h' * y h') h - bp_condExp T 1 x h * bp_condExp T 1 y h

/-- **(23.19)** (corrected), AKMM p. 713: with `R⁻¹ = βEₜ[m]` (the definition on p. 713),
`βEₜ[mπ] = R⁻¹Eₜ[π] + β covₜ(m, π)`; hence the UIP condition (23.18) `Eₜ[mπ] = Eₜ[m*π*]` is
equivalent to `R⁻¹Eₜ[π] + β covₜ(m, π) = R*⁻¹Eₜ[π*] + β covₜ(m*, π*)`. -/
theorem eq_23_19 (T : BPTree S) {β : ℝ} (hβ : β ≠ 0) (m pi ms pis : List S → ℝ) (h : List S) :
    bp_condExp T 1 (fun h' => m h' * pi h') h = bp_condExp T 1 (fun h' => ms h' * pis h') h ↔
      β * bp_condExp T 1 m h * bp_condExp T 1 pi h + β * bondCov T m pi h
        = β * bp_condExp T 1 ms h * bp_condExp T 1 pis h + β * bondCov T ms pis h := by
  unfold bondCov
  constructor
  · intro e; rw [← sub_eq_zero]; ring_nf; rw [e]; ring
  · intro e
    have : β * (bp_condExp T 1 (fun h' => m h' * pi h') h
        - bp_condExp T 1 (fun h' => ms h' * pis h') h) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hβ
    · linarith

/-- The two-state event tree with probability `1/2` for each shock (Miao's Markov tree). -/
noncomputable def bondCoinTree : BPTree Bool :=
  bp_markovTree (fun _ _ => 1 / 2) true (fun _ _ => by norm_num)
    (fun _ => by simp)

/-- `E₀[x₁] = x(H)/2 + x(T)/2` on the coin tree. -/
theorem bondCoinTree_condExp (x : List Bool → ℝ) :
    bp_condExp bondCoinTree 1 x [] = x [true] / 2 + x [false] / 2 := by
  rw [rs_condExp_one, Fintype.sum_bool]
  simp [bondCoinTree, bp_markovTree, Miao.CompleteMarkets.bp_markovPr]
  ring

/-- AKMM, (23.19), p. 713 (printed version refuted): the printed
`R⁻¹Eₜ[π] + covₜ(m, π) = R*⁻¹Eₜ[π*] + covₜ(m*, π*)` (covariances without `β`) does not follow from
(23.17)–(23.18). Two equally likely states, log utility `u′(C) = 1/C`, `β = 1/2`; home:
`C ≡ 1`, `P ≡ 1`; foreign: `C*₀ = 1`, `C*₁ ∈ {2, 2/3}`, `P*₀ = 1`, `P*₁ ∈ {2/5, 2}`. Then
`m ≡ π ≡ 1`, `m* ∈ {1/2, 3/2}`, `π* ∈ {5/2, 1/2}`, both Euler equations hold with `Q = 1/2`
(so (23.18) holds), but the printed left side is `1/2` and its right side `1/4`. -/
theorem eq_23_19_printed_counterexample :
    let Cs : List Bool → ℝ := fun h => if h = [true] then 2 else if h = [false] then 2 / 3 else 1
    let Ps : List Bool → ℝ := fun h => if h = [true] then 2 / 5 else if h = [false] then 2 else 1
    let m : List Bool → ℝ := fun _ => (1 / 1 : ℝ) / (1 / 1)
    let pi : List Bool → ℝ := fun _ => (1 : ℝ) / 1
    let ms : List Bool → ℝ := fun h' => (1 / Cs h') / (1 / Cs [])
    let pis : List Bool → ℝ := fun h' => Ps [] / Ps h'
    (1 / 2 : ℝ) = 1 / 2 * bp_condExp bondCoinTree 1 (fun h' => m h' * pi h') [] ∧
      (1 / 2 : ℝ) = 1 / 2 * bp_condExp bondCoinTree 1 (fun h' => ms h' * pis h') [] ∧
      1 / 2 * bp_condExp bondCoinTree 1 m [] * bp_condExp bondCoinTree 1 pi []
          + bondCov bondCoinTree m pi [] = 1 / 2 ∧
      1 / 2 * bp_condExp bondCoinTree 1 ms [] * bp_condExp bondCoinTree 1 pis []
          + bondCov bondCoinTree ms pis [] = 1 / 4 := by
  intro Cs Ps m pi ms pis
  unfold bondCov
  simp only [bondCoinTree_condExp, m, pi, ms, pis, Cs, Ps]
  norm_num

/-- **(23.20)**, AKMM p. 714: the wedge `u′(C_{t+1})P_t/(u′(C_t)P_{t+1}) − (foreign)` is
`χ_{t+1}/χ_t − χ*_{t+1}/χ*_t` with `χ = u′(C)/P`. -/
theorem eq_23_20 {u0 u1 us0 us1 P0 P1 Ps0 Ps1 : ℝ} (hu0 : u0 ≠ 0) (hus0 : us0 ≠ 0)
    (hP1 : P1 ≠ 0) (hPs1 : Ps1 ≠ 0) :
    u1 / u0 * (P0 / P1) - us1 / us0 * (Ps0 / Ps1)
      = (u1 / P1) / (u0 / P0) - (us1 / Ps1) / (us0 / Ps0) := by
  field_simp

/-- AKMM, p. 714: "this wedge must equal zero in expectation": under (23.18),
`Eₜ[ε_{t+1}] = 0`. -/
theorem bond_wedge_mean_zero (T : BPTree S) (m ms : List S → ℝ) (h : List S)
    (h18 : bp_condExp T 1 m h = bp_condExp T 1 ms h) :
    bp_condExp T 1 (fun h' => m h' - ms h') h = 0 := by
  rw [bp_condExp_sub_fun, h18, sub_self]

/-- AKMM, p. 714, linearised: write `χ_{t+1}/χ_t = e^{a}` and `χ*_{t+1}/χ*_t = e^{b}` state by
state. If the UIP condition holds along a path of equilibria indexed by `t` (scaling the shocks,
`Eₜ[e^{ta} − e^{tb}] = 0` for all `t`), then its first-order term vanishes, `Eₜ[a − b] = 0`, i.e.
`Eₜ[ε̂] = 0`; and the log wealth gap `log W = log χ* − log χ` changes by exactly `b − a = −ε̂`,
so `Eₜ[Ŵ_{t+1} − Ŵ_t] = 0`. -/
theorem bond_wealth_loglin (T : BPTree S) (a b : List S → ℝ) (h : List S)
    (h18 : ∀ t : ℝ, bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h = 0)
    {chi chis : ℝ} (hchi : 0 < chi) (hchis : 0 < chis) :
    bp_condExp T 1 (fun h' => a h' - b h') h = 0 ∧
      bp_condExp T 1 (fun h' => log ((chis * exp (b h')) / (chi * exp (a h')))
        - log (chis / chi)) h = 0 := by
  have hfun : (fun t : ℝ => bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h)
      = fun t => ∑ s, T.pr (s :: h) / T.pr h * (exp (t * a (s :: h)) - exp (t * b (s :: h))) := by
    funext t; rw [rs_condExp_one]
  have hd : HasDerivAt (fun t => ∑ s, T.pr (s :: h) / T.pr h
      * (exp (t * a (s :: h)) - exp (t * b (s :: h))))
      (∑ s, T.pr (s :: h) / T.pr h * (a (s :: h) - b (s :: h))) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ =>
      ((((hasDerivAt_id (0 : ℝ)).mul_const (a (s :: h))).exp.sub
        ((hasDerivAt_id (0 : ℝ)).mul_const (b (s :: h))).exp).const_mul (T.pr (s :: h) / T.pr h)))
    simpa using this
  have hzero : HasDerivAt (fun t => ∑ s, T.pr (s :: h) / T.pr h
      * (exp (t * a (s :: h)) - exp (t * b (s :: h)))) 0 0 := by
    rw [← hfun]
    have : (fun t : ℝ => bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h)
        = fun _ => 0 := funext h18
    rw [this]
    exact hasDerivAt_const _ _
  have h1 : bp_condExp T 1 (fun h' => a h' - b h') h = 0 := by
    rw [rs_condExp_one]
    exact hd.unique hzero
  refine ⟨h1, ?_⟩
  have e : (fun h' => log ((chis * exp (b h')) / (chi * exp (a h'))) - log (chis / chi))
      = fun h' => -(a h' - b h') := by
    funext h'
    rw [log_div (by positivity) (by positivity), log_mul hchis.ne' (exp_pos _).ne',
      log_mul hchi.ne' (exp_pos _).ne', log_div hchis.ne' hchi.ne', log_exp, log_exp]
    ring
  rw [e, rs_condExp_one]
  rw [rs_condExp_one] at h1
  simp only [mul_neg, Finset.sum_neg_distrib, h1, neg_zero]

end AKMM.InternationalMacro
