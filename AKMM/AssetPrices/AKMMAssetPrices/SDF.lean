/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.TwoPeriod
import CompleteMarkets.BPAssetPricing

/-!
# The stochastic discount factor, risk premia and risk-neutral probabilities

AKMM, §16.4, pp. 480–482. The states have probabilities `π ≫ 0` summing to one; expectations and
covariances are Miao's `bp_E π` and `bp_Cov π` (`Miao.CompleteMarkets`).

* The SDF `M(ω) = q(ω)/π(ω)` (`sdfM`); `pⁿ = E[dⁿM]` (`sdf_price`) and `1 = E[RⁿM]`
  (`sdf_return`); the riskless bond `pᵇ = Σ_ω q(ω) = E[M] = 1/R_f` (`sdf_bond`).
* Risk-neutral pricing (16.16): with `M ≡ β`, `pᵇ = β` and `pⁿ = E[dⁿ]/R_f` (`eq_16_16`).
* The risk adjustment: `pⁿ = E[dⁿ]/R_f − (−Cov(dⁿ, M))` (`sdf_risk_adjustment`).
* (16.17), corrected: `1 = E[Rⁿ]E[M] + Cov(Rⁿ, M)` and `E[Rⁿ] − R_f = −Cov(Rⁿ, M)/E[M]`
  (`eq_16_17`); the printed `1 = E[RⁿM] + Cov(Rⁿ, M)` fails (`eq_16_17_printed_counterexample`).
* Risk-neutral probabilities (16.18): `π* = q/Σq` is positive and sums to one
  (`riskNeutral_pos`, `riskNeutral_sum`), `pⁿ = E*[dⁿ]/R_f` (`eq_16_18`); with complete markets
  `π*` is unique (`riskNeutral_unique_of_complete`), and when a riskless bond is traded `π*` is
  unique iff markets are complete (`riskNeutral_unique_iff`).

Departure: (16.17) is printed as `1 = E[RM] + Cov(R, M)`; and "`π*` is unique if markets are
complete, otherwise there may be many" is proved in the form above (with a bond, uniqueness of `π*`
is equivalent to completeness). See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open Matrix Miao.CompleteMarkets

variable {S N : Type} [Fintype S] [Fintype N]

/-- AKMM, p. 480: the stochastic discount factor `M(ω) = q(ω)/π(ω)`. -/
noncomputable def sdfM (q pr : S → ℝ) : S → ℝ := fun s => q s / pr s

omit [Fintype S] in
/-- `π(ω)M(ω) = q(ω)`. -/
theorem sdf_mul_M {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s) (s : S) : pr s * sdfM q pr s = q s := by
  have := (hpr s).ne'
  simp only [sdfM]
  field_simp

omit [Fintype N] in
/-- AKMM, p. 480: `pⁿ = Σ_ω dⁿ(ω)q(ω) = E[dⁿ(ω)M(ω)]`. -/
theorem sdf_price {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) (n : N) :
    p n = bp_E pr fun s => D s n * sdfM q pr s := by
  rw [hq n, bp_E]
  exact Finset.sum_congr rfl fun s _ => by rw [mul_left_comm, sdf_mul_M hpr]

omit [Fintype N] in
/-- AKMM, p. 480: the return `Rⁿ(ω) = dⁿ(ω)/pⁿ` satisfies `1 = E[Rⁿ(ω)M(ω)]`. -/
theorem sdf_return {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) {n : N} (hp : p n ≠ 0) :
    bp_E pr (fun s => D s n / p n * sdfM q pr s) = 1 := by
  have := eq_13_30 pr (sdfM q pr) (fun s => D s n) (p n) hp (by
    rw [sdf_price hpr hq n]
    exact Finset.sum_congr rfl fun s _ => by ring)
  rw [← this]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype N] in
/-- AKMM, p. 481: a riskless bond (payoff 1 in every state) costs `pᵇ = Σ_ω q(ω) = E[M]`, so
`R_f = 1/E[M]`. -/
theorem sdf_bond {p : N → ℝ} {D : Matrix S N ℝ} {q pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hq : ∀ n, p n = ∑ s, D s n * q s) {b : N} (hb : ∀ s, D s b = 1) :
    p b = ∑ s, q s ∧ p b = bp_E pr (sdfM q pr) := by
  refine ⟨by simp [hq b, hb], ?_⟩
  rw [sdf_price hpr hq b]
  simp [hb]

omit [Fintype N] in
/-- AKMM, (16.16), p. 480: if agents are risk neutral, `M(ω) = β` in every state, then the bond
price is `pᵇ = 1/R_f = E[M] = β` and every asset is priced by its expected payoff discounted at
the riskless rate, `pⁿ = E[dⁿ]/R_f` with `R_f = 1/β`. -/
theorem eq_16_16 {p : N → ℝ} {D : Matrix S N ℝ} {pr : S → ℝ} (hpr : ∀ s, 0 < pr s)
    (hpr1 : ∑ s, pr s = 1) {β : ℝ} (hβ : 0 < β) (hq : ∀ n, p n = ∑ s, D s n * (β * pr s))
    (n : N) :
    bp_E pr (sdfM (fun s => β * pr s) pr) = β ∧ p n = bp_E pr (fun s => D s n) / (1 / β) := by
  have hM : sdfM (fun s => β * pr s) pr = fun _ => β := funext fun s => by
    simp only [sdfM]
    field_simp [(hpr s).ne']
  refine ⟨by rw [hM, bp_E_const pr hpr1], ?_⟩
  rw [sdf_price hpr hq n, hM, div_div_eq_mul_div, div_one]
  simp only [bp_E, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- AKMM, p. 481: the risk adjustment. With `R_f = 1/E[M]`,
`pⁿ = E[dⁿ]E[M] + Cov(dⁿ, M) = E[dⁿ]/R_f − (−Cov(dⁿ, M))`. -/
theorem sdf_risk_adjustment {pr d M : S → ℝ} {pn : ℝ}
    (hp : pn = bp_E pr fun s => d s * M s) :
    pn = bp_E pr d * bp_E pr M + bp_Cov pr d M ∧
      pn = bp_E pr d / (1 / bp_E pr M) - -bp_Cov pr d M := by
  have h1 : pn = bp_E pr d * bp_E pr M + bp_Cov pr d M := by
    rw [hp, bp_Cov]
    ring
  refine ⟨h1, ?_⟩
  rw [h1]
  field_simp
  ring

/-- AKMM, (16.17), p. 481, corrected: from `1 = E[RM]`,
`1 = E[R]E[M] + Cov(R, M)` and, with `R_f = 1/E[M]`, `E[R] − R_f = −Cov(R, M)/E[M]`. -/
theorem eq_16_17 {pr R M : S → ℝ} (hM : bp_E pr M ≠ 0) (h : bp_E pr (fun s => R s * M s) = 1) :
    1 = bp_E pr R * bp_E pr M + bp_Cov pr R M ∧
      bp_E pr R - 1 / bp_E pr M = -bp_Cov pr R M / bp_E pr M := by
  have h1 : 1 = bp_E pr R * bp_E pr M + bp_Cov pr R M := by
    rw [bp_Cov, h]
    ring
  refine ⟨h1, ?_⟩
  field_simp
  linarith

/-- AKMM, (16.17), p. 481: the printed `1 = E[RM] + Cov(R, M)` is false. Two equally likely
states, state prices `q = (1/4, 1/2)` (`M = (1/2, 1)`), and the Arrow security for state 1 (price
`1/4`, return `R = (4, 0)`): `E[RM] = 1` but `Cov(R, M) = −1/2`. -/
theorem eq_16_17_printed_counterexample :
    bp_E (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun s => ![4, 0] s * ![1 / 2, 1] s) = 1 ∧
      bp_Cov (fun _ : Fin 2 => (1 / 2 : ℝ)) ![4, 0] ![1 / 2, 1] = -1 / 2 ∧
      bp_E (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun s => ![4, 0] s * ![1 / 2, 1] s) +
        bp_Cov (fun _ : Fin 2 => (1 / 2 : ℝ)) ![4, 0] ![1 / 2, 1] ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [bp_Cov, bp_E, Fin.sum_univ_two] <;> norm_num

/-- AKMM, p. 481: the risk-neutral probabilities `π*(ω) = q(ω)/Σ_{ω'} q(ω')`. -/
noncomputable def riskNeutral (q : S → ℝ) : S → ℝ := fun s => q s / ∑ s', q s'

/-- AKMM, p. 481: with `q ≫ 0` the risk-neutral probabilities are strictly positive. -/
theorem riskNeutral_pos [Nonempty S] {q : S → ℝ} (hq : ∀ s, 0 < q s) (s : S) :
    0 < riskNeutral q s :=
  div_pos (hq s) (Finset.sum_pos (fun s _ => hq s) Finset.univ_nonempty)

/-- AKMM, p. 481: the risk-neutral probabilities sum to one. -/
theorem riskNeutral_sum [Nonempty S] {q : S → ℝ} (hq : ∀ s, 0 < q s) :
    ∑ s, riskNeutral q s = 1 := by
  have h : 0 < ∑ s, q s := Finset.sum_pos (fun s _ => hq s) Finset.univ_nonempty
  simp only [riskNeutral, ← Finset.sum_div]
  exact div_self h.ne'

omit [Fintype N] in
/-- AKMM, (16.18), p. 481: with `1/R_f = Σ_ω q(ω)`, `pⁿ = Σ_ω dⁿ(ω)π*(ω)/R_f = E*[dⁿ]/R_f`. -/
theorem eq_16_18 [Nonempty S] {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) (n : N) :
    p n = bp_E (riskNeutral q) (fun s => D s n) / (1 / ∑ s, q s) := by
  have h : 0 < ∑ s, q s := Finset.sum_pos (fun s _ => hq.1 s) Finset.univ_nonempty
  rw [hq.2 n, bp_E, div_div_eq_mul_div, div_one, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [riskNeutral]
    field_simp

/-- AKMM, p. 482: with complete markets the risk-neutral probability is unique (it is computed
from the unique state prices). -/
theorem riskNeutral_unique_of_complete {p : N → ℝ} {D : Matrix S N ℝ} {q q' : S → ℝ}
    (hq : tpStatePrices p D q) (hq' : tpStatePrices p D q') (hD : D.rank = Fintype.card S) :
    riskNeutral q' = riskNeutral q := by
  rw [((tp_statePrices_unique_iff_rank hq).2 hD) q' hq']

/-- AKMM, p. 482: when a riskless bond is traded, the risk-neutral probability is unique iff
markets are complete. (The bond fixes `Σ_ω q(ω) = pᵇ`, so `π*` determines `q`.) -/
theorem riskNeutral_unique_iff {p : N → ℝ} {D : Matrix S N ℝ} {q : S → ℝ}
    (hq : tpStatePrices p D q) {b : N} (hb : ∀ s, D s b = 1) :
    (∀ q', tpStatePrices p D q' → riskNeutral q' = riskNeutral q) ↔
      D.rank = Fintype.card S := by
  rw [← tp_statePrices_unique_iff_rank hq]
  have hsum : ∀ q', tpStatePrices p D q' → ∑ s, q' s = p b := fun q' h => by
    simp [h.2 b, hb]
  constructor
  · intro h q' hq'
    funext s
    have hne : ∑ s, q s ≠ 0 :=
      (Finset.sum_pos (fun s _ => hq.1 s) ⟨s, Finset.mem_univ s⟩).ne'
    have e := congrFun (h q' hq') s
    simp only [riskNeutral] at e
    rw [hsum q' hq', ← hsum q hq] at e
    exact (div_left_inj' hne).1 e
  · intro h q' hq'
    rw [h q' hq']

end AKMM.AssetPrices
