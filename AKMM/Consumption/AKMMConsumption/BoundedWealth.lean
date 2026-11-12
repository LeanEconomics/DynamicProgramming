/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.SIBounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bounds on wealth accumulation

AKMM, §11.3.5, (11.42)–(11.46), fn. 23–25, pp. 312–314.

The book's informal proof (after Schechtman and Escudero 1977) is formalised in two layers.

* **The book's argument, given (11.44).** From the Euler equation (11.42) and the identity
  (11.43), if `E u′(c(x′))/u′(c(x̄′)) → 1` as `x → ∞` and `βR < 1`, then `x̄′(x) < x` for all large
  `x`: the highest next-period cash in hand is below today's (`eq_11_43`,
  `bw_bounded_of_ratio`); and `x̄′ − x′ = ȳ − y′` (`bw_cash_gap`, the step of (11.45)).
* **The theorem.** The Taylor step from (11.46) to (11.44) is replaced by Miao's proof of
  Schechtman–Escudero (`Miao.IncompleteMarkets.SIModel.Solution.lemma_8_3_3_all`, reused): with
  `βR < 1` and relative risk aversion eventually below some `γ`, there is `x*` with `x′ < x` for
  every income realisation once `x > x*` (`bw_bounded_wealth`); CRRA qualifies
  (`bw_crra_rra`, `bw_bounded_wealth_crra`), and CRRA has `α(c) = σ/c → 0`, (11.46)
  (`bw_crra_ara_tendsto`).
* **Correction** (p. 314: "(11.46) requires … that `u` belongs to the DARA class … under DARA
  the condition `βR < 1` is sufficient"). DARA does not give (11.46): `u′(c) = e^{−c}/c` has
  strictly decreasing absolute risk aversion `α(c) = 1 + 1/c`, which tends to `1`
  (`bw_dara_not_ara_zero`). The sufficient condition the proof uses is `α → 0`, delivered for
  instance by bounded relative risk aversion.
-/

namespace AKMM.Consumption

open Filter Topology

/-- **AKMM, (11.42)–(11.43), p. 313.** If `u′(c(x)) = βRD(x)` with `D(x) = E u′(c(x′))` and
`u′(c(x̄′)) ≠ 0`, then `u′(c(x)) = βR(D(x)/u′(c(x̄′)))u′(c(x̄′))`. -/
theorem eq_11_43 {mx D mbar βR : ℝ} (h : mx = βR * D) (hm : mbar ≠ 0) :
    mx = βR * (D / mbar) * mbar := by
  rw [h]; field_simp

/-- AKMM, p. 314, (11.45): `x′ = Ra′ + y′` and `x̄′ = Ra′ + ȳ`, so `x̄′ − x′ = ȳ − y′`. -/
theorem bw_cash_gap (R a' y' ybar : ℝ) : (R * a' + ybar) - (R * a' + y') = ybar - y' := by ring

/-- **AKMM, p. 313: the bounded-wealth argument given (11.44).** Let `u′` be strictly decreasing
on `(0, ∞)`, consumption `c` positive and strictly increasing, `βR < 1` (`βR > 0`), and let the
Euler equation (11.42) `u′(c(x)) = βRD(x)` hold with `D(x) = E u′(c(x′))`. If (11.44)
`D(x)/u′(c(x̄′(x))) → 1` as `x → ∞`, then for all large `x`, `x̄′(x) < x`: cash in hand does not
increase forever. -/
theorem bw_bounded_of_ratio {du cons xbar D : ℝ → ℝ} {βR : ℝ} (hβR0 : 0 < βR) (hβR : βR < 1)
    (hdu : StrictAntiOn du (Set.Ioi 0)) (hdupos : ∀ c, 0 < c → 0 < du c)
    (hc : StrictMono cons) (hcpos : ∀ x, 0 < cons x) (heuler : ∀ x, du (cons x) = βR * D x)
    (h44 : Tendsto (fun x => D x / du (cons (xbar x))) atTop (𝓝 1)) :
    ∀ᶠ x in atTop, xbar x < x := by
  have hlt : ∀ᶠ x in atTop, D x / du (cons (xbar x)) < 1 / βR :=
    h44.eventually (gt_mem_nhds (by rw [lt_div_iff₀ hβR0]; linarith))
  filter_upwards [hlt] with x hx
  have hm := hdupos _ (hcpos (xbar x))
  have h1 : du (cons x) < du (cons (xbar x)) := by
    rw [eq_11_43 (heuler x) hm.ne']
    have : βR * (D x / du (cons (xbar x))) < 1 := by
      rw [lt_div_iff₀ hβR0] at hx; linarith
    nlinarith
  by_contra hle
  push Not at hle
  have := hdu.antitoneOn (hcpos _) (hcpos _) (hc.monotone hle)
  linarith

/-- **AKMM, p. 313: `βR < 1` bounds wealth** (Schechtman and Escudero 1977, Clarida 1987, Huggett
1997; the proof is Miao's Lemma 8.3.3). In Miao's i.i.d. income fluctuation problem, if `βR < 1`
and relative risk aversion is eventually below some `γ > 0`, there is `x*` such that
`x′ = Râ(x) + y − rb < x` for every income `y ≤ y_max` whenever `x > x*`. -/
theorem bw_bounded_wealth {M : Miao.IncompleteMarkets.SIModel} (S : M.Solution)
    (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ} (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x :=
  S.lemma_8_3_3_all hβR hddu hγ0 hγ

/-- CRRA marginal utility `u′(c) = c^{−σ}` has constant relative risk aversion `σ`. -/
theorem bw_crra_rra {σ c : ℝ} (hc : 0 < c) :
    -c * (-σ * c ^ (-σ - 1)) / c ^ (-σ) = σ := by
  have hp : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have e : c ^ (-σ - 1) = c ^ (-σ) * c⁻¹ := by
    rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
  rw [e]
  field_simp

/-- **AKMM, p. 314 with CRRA.** In Miao's income fluctuation problem with CRRA marginal utility
`u′(c) = c^{−σ}` and `βR < 1`, wealth is bounded: there is `x*` with `x′ < x` for every income
once `x > x*`. -/
theorem bw_bounded_wealth_crra {M : Miao.IncompleteMarkets.SIModel} (S : M.Solution) {σ : ℝ}
    (hσ : 0 < σ) (hdu : ∀ c, 0 < c → M.du c = c ^ (-σ)) (hβR : M.β * M.R < 1) :
    ∃ xstar, M.xmin ≤ xstar ∧ ∀ x, xstar < x → ∀ y, y ≤ M.ymax → M.next (S.sav x) y < x := by
  have hddu : ∀ c, 0 < c → HasDerivAt M.du (-σ * c ^ (-σ - 1)) c := by
    intro c hc
    have h := Real.hasDerivAt_rpow_const (x := c) (p := -σ) (Or.inl hc.ne')
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hc] with x hx
    exact hdu x hx
  refine bw_bounded_wealth S hβR hddu (γ := σ + 1) (by linarith) ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  rw [hdu c hc, bw_crra_rra hc]
  linarith

/-- **AKMM, (11.46), p. 314, for CRRA.** Absolute risk aversion `α(c) = σ/c → 0` as `c → ∞`. -/
theorem bw_crra_ara_tendsto (σ : ℝ) : Tendsto (fun c : ℝ => σ / c) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- **Correction to AKMM, p. 314** ("Condition (11.46) requires … that `u` belongs to the DARA
class"; "under DARA the condition `βR < 1` is sufficient"). DARA does not give (11.46): the
marginal utility `u′(c) = e^{−c}/c` is positive and strictly decreasing on `(0, ∞)`, its absolute
risk aversion `α(c) = −u″(c)/u′(c) = 1 + 1/c` is strictly decreasing (DARA), and `α(c) → 1 ≠ 0`. -/
theorem bw_dara_not_ara_zero :
    (∀ c : ℝ, 0 < c → HasDerivAt (fun x => Real.exp (-x) / x)
        (-(Real.exp (-c) / c) - Real.exp (-c) / c ^ 2) c) ∧
      (∀ c : ℝ, 0 < c → 0 < Real.exp (-c) / c) ∧
      (∀ c : ℝ, 0 < c →
        -(-(Real.exp (-c) / c) - Real.exp (-c) / c ^ 2) / (Real.exp (-c) / c) = 1 + 1 / c) ∧
      StrictAntiOn (fun c : ℝ => 1 + 1 / c) (Set.Ioi 0) ∧
      Tendsto (fun c : ℝ => 1 + 1 / c) atTop (𝓝 1) := by
  refine ⟨fun c hc => ?_, fun c hc => div_pos (Real.exp_pos _) hc, fun c hc => ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-c)) c := by
      simpa using (hasDerivAt_neg c).exp
    have := h1.div (hasDerivAt_id c) hc.ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  · have := Real.exp_pos (-c)
    field_simp
    ring
  · intro x hx y hy hxy
    have : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
    simp only
    linarith
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero

end AKMM.Consumption
