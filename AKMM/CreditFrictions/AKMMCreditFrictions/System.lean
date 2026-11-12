/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCreditFrictions.Household
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The two-period system, the price of capital, slack limits and working capital

AKMM, §19.5, (19.11)–(19.16), pp. 577–579; §19.5.2, Property 19.5.2, pp. 580–581; §19.5.4,
Property 19.5.4, p. 582; §19.5.5, (19.17)–(19.18), p. 584.

* **Period 1** (p. 577): with `k₂ = b₂ = 0`, no terminal dividend cost and `p′ = 1`, the
  budgets give `C′ = (1 − δ)K′ + Y′` (`sys_terminal_C`).
* **(19.11)–(19.16)** (pp. 578–579): the general conditions (19.5), (19.6), (19.9), the binding
  limit, the budgets of firm and household and `T = B′/R̃ − B′/R`, with `u = ln(c − ℓ^ν)`
  (so `βu₁′/u₁ = β(C − L^ν)/g(z′, K′)`), `wL = (1 − α)F`, `p′ = 1`, `ϕ′(D′) = 1`, give the six
  equations (`system_19_11_to_19_16`).
* **Property 19.5.2** (pp. 580–581): the elasticity of net worth `pK − B` in `p` is
  `pK/(pK − B)`, greater than one iff `B > 0` (`sys_networth_elasticity`,
  `property_19_5_2_networth`); the rearranged budget
  `K′ = [(1 − δ)K + (αF − B − D − κ(D − φ)²)/p]/(1 − ξ)` (`sys_Kprime_eq`); holding `D` fixed,
  `∂K′/∂p = −N/(p²(1 − ξ))` with `N = αF − B − D − κ(D − φ)²`, positive iff `N < 0`
  (`sys_hasDerivAt_Kprime`, `property_19_5_2`), and its size increases with `ξ`
  (`sys_multiplier_mono`). `B > 0` does not give `N < 0` (`sys_B_pos_not_sufficient`).
* **Property 19.5.4** (p. 582): with `µ = 0` the conditions (19.11), (19.13)–(19.16) do not
  involve `ξ` and the limit stays slack for `ξ′ ≥ ξ`, so an equilibrium with a slack limit
  remains one (`property_19_5_4`). For an abstract concave problem with a linear limit, a
  strictly slack optimum is a global unconstrained optimum and stays optimal for `ξ′ ≥ ξ`
  (`sys_slack_global`, `property_19_5_4_opt`).
* **Working capital** (p. 584): the Lagrangian conditions with the limit
  `wℓ + b′/R_c ≤ ξpk′` give (19.18) `F_ℓ = (1 + µ)w` (`eq_19_18`); (19.5) is unchanged
  (`sys_wc_19_5`); with `R_c = R̃` (19.6) is unchanged (`sys_wc_19_6_tilde`), but with the
  printed `R_c = R` it becomes `E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ/(1 + τ)`
  (`sys_wc_19_6_printed`), different from `1 − µ` when `µ ≠ 0`, `τ ≠ 0`
  (`sys_wc_19_6_printed_ne`).
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, p. 577: "all resources are consumed": with `k₂ = b₂ = 0`, no dividend cost and
`p′ = 1`, the firm's period-1 budget `F′ − w′L′ = B′ + (0 − (1 − δ)K′) + D′` and the
household's `D′ + B′ + w′L′ = C′` give `C′ = (1 − δ)K′ + F′`. -/
theorem sys_terminal_C {F' w' L' B' K' δ D' C' : ℝ}
    (hfirm : F' - w' * L' = B' + 1 * (0 - (1 - δ) * K') + D')
    (hhh : D' + B' + w' * L' = C') : C' = (1 - δ) * K' + F' := by
  linarith

/-- **(19.11)–(19.16)** (AKMM, pp. 578–579). In period 0, with the firm's discount factor
`m = βu₁(C′, L′)/u₁(C, L)` for `u₁ = 1/(c − ℓ^ν)` and `C′ − L′^ν = g`, the conditions
(19.5) `m ϕ′(D)/1 · ((1 − δ)·1 + F_k′) = (1 − µξ)p` and (19.6) `m ϕ′(D)/1 · R̃ = 1 − µ`,
(19.9) `1/R = m`, the binding limit `B′/R̃ = ξpK′`, `R̃ = R/(1 + τ)`, the firm's budget, the
wage bill `wL = (1 − α)F`, the household's budget with `A = A′ = 1` and the tax
`T = B′/R̃ − B′/R` imply the six equations (19.11)–(19.16). -/
theorem system_19_11_to_19_16 {β C L ν g δ Fk μ ξ p κ φ D Rt R τ B' K' F w B K α T m : ℝ}
    (hg : g ≠ 0) (hCL : C - L ^ ν ≠ 0) (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (hm : m = β * (1 / g) / (1 / (C - L ^ ν)))
    (h195 : m * (cfPhiD κ φ D / 1) * ((1 - δ) * 1 + Fk) = (1 - μ * ξ) * p)
    (h196 : m * (cfPhiD κ φ D / 1) * Rt = 1 - μ) (h199 : 1 / R = m)
    (hbind : B' / Rt = ξ * p * K') (hRt : Rt = R / (1 + τ))
    (hfirm : F - w * L + B' / Rt = B + p * (K' - (1 - δ) * K) + cfPhi κ φ D)
    (hw : w * L = (1 - α) * F) (hhh : (D + 1) * 1 + B + w * L = C + 1 * 1 + B' / R + T)
    (hT : T = B' / Rt - B' / R) :
    (1 - μ * ξ) * p = β * ((C - L ^ ν) / g) * (1 - δ + Fk) * (1 + 2 * κ * (D - φ)) ∧
    (1 + τ) * B' / R = ξ * p * K' ∧
    α * F + (1 + τ) * B' / R = B + p * (K' - (1 - δ) * K) + D + κ * (D - φ) ^ 2 ∧
    (D + B + (1 - α) * F = C + B' / R + T ∧ T = τ * B' / R) ∧
    (1 - μ) * (1 + τ) / R = β * ((C - L ^ ν) / g) * (1 + 2 * κ * (D - φ)) ∧
    1 / R = β * ((C - L ^ ν) / g) := by
  have hmg : m = β * ((C - L ^ ν) / g) := by rw [hm]; field_simp
  have hB : B' / Rt = (1 + τ) * B' / R := by rw [hRt]; field_simp
  have hTt : T = τ * B' / R := by rw [hT, hRt, hh_tax hR]
  refine ⟨?_, ?_, ?_, ⟨?_, hTt⟩, ?_, ?_⟩
  · rw [← h195, hmg]
    unfold cfPhiD
    ring
  · rw [← hB, hbind]
  · rw [← hB]
    unfold cfPhi at hfirm
    linarith
  · linarith
  · have : (1 - μ) * (1 + τ) / R = m * cfPhiD κ φ D := by
      rw [← h196, hRt]
      field_simp
    rw [this, hmg]
    unfold cfPhiD
    ring
  · rw [h199, hmg]

/-! ### Property 19.5.2: the price of capital -/

/-- AKMM, p. 580: the elasticity of net worth `n(p) = pK − B` in `p`,
`n′(p)·p/n(p) = pK/(pK − B)`. -/
theorem sys_networth_elasticity {p K B : ℝ} :
    HasDerivAt (fun x => x * K - B) K p ∧ K * p / (p * K - B) = p * K / (p * K - B) := by
  refine ⟨?_, by ring⟩
  simpa using ((hasDerivAt_id p).mul_const K).sub_const B

/-- **Property 19.5.2, net worth** (AKMM, p. 580): "Provided that `B > 0`, a 1 percent increase in
`p` generates an increase in net worth larger than 1 percent": with positive net worth
`pK − B > 0` and `p, K > 0`, the elasticity `pK/(pK − B)` exceeds one iff `B > 0`; and for a
finite rise `p₀ < p₁`, `(p₁K − B)/(p₀K − B) > p₁/p₀` iff `B > 0`. -/
theorem property_19_5_2_networth {p K B : ℝ} (hn : 0 < p * K - B) :
    (1 < p * K / (p * K - B) ↔ 0 < B) ∧
    ∀ {p₀ p₁ : ℝ}, 0 < p₀ → p₀ < p₁ → 0 < p₀ * K - B → 0 < K →
      (p₁ / p₀ < (p₁ * K - B) / (p₀ * K - B) ↔ 0 < B) := by
  refine ⟨?_, ?_⟩
  · rw [one_lt_div hn]
    constructor <;> intro h <;> linarith
  · intro p₀ p₁ h0 h01 hn0 hK
    rw [div_lt_div_iff₀ h0 hn0]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith

/-- AKMM, p. 580: using (19.12) in (19.13), `αF + ξpK′ = B + p[K′ − (1 − δ)K] + D + κ(D − φ)²`,
the budget rearranges to `K′ = [(1 − δ)K + (αF − B − D − κ(D − φ)²)/p]/(1 − ξ)`. -/
theorem sys_Kprime_eq {α F ξ p K' B δ K D κ φ : ℝ} (hp : p ≠ 0) (hξ : ξ ≠ 1)
    (h : α * F + ξ * p * K' = B + p * (K' - (1 - δ) * K) + D + κ * (D - φ) ^ 2) :
    K' = 1 / (1 - ξ) * ((1 - δ) * K + (α * F - B - D - κ * (D - φ) ^ 2) / p) := by
  have h1 : 1 - ξ ≠ 0 := sub_ne_zero.2 (Ne.symm hξ)
  field_simp
  linear_combination -h

/-- AKMM, p. 580: holding the other terms fixed, the rearranged `K′` has derivative
`−N/(p²(1 − ξ))` in `p`, `N = αF − B − D − κ(D − φ)²`. -/
theorem sys_hasDerivAt_Kprime {ξ δ K N p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun x => 1 / (1 - ξ) * ((1 - δ) * K + N / x)) (-N / (p ^ 2 * (1 - ξ))) p := by
  have h := ((hasDerivAt_inv hp).const_mul N).const_add ((1 - δ) * K) |>.const_mul (1 / (1 - ξ))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · rw [div_eq_mul_inv (-N), mul_inv]
    ring
  · simp only [div_eq_mul_inv]

/-- **Property 19.5.2** (AKMM, pp. 580–581): with a binding limit and `ξ < 1`, holding dividends
and the period-0 terms fixed, a higher price of capital raises `K′` iff the profits net of
liabilities and dividends `N = αF − B − D − κ(D − φ)²` are negative. -/
theorem property_19_5_2 {ξ N p : ℝ} (hp : p ≠ 0) (hξ : ξ < 1) :
    0 < -N / (p ^ 2 * (1 - ξ)) ↔ N < 0 := by
  have hd : 0 < p ^ 2 * (1 - ξ) := mul_pos (by positivity) (by linarith)
  rw [div_pos_iff_of_pos_right hd]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 580: "The first term … acts as a multiplier, and depends positively on `ξ`": for
`N < 0` the response `−N/(p²(1 − ξ))` increases with `ξ < 1`. -/
theorem sys_multiplier_mono {N p ξ₁ ξ₂ : ℝ} (hN : N < 0) (hp : p ≠ 0) (h₁₂ : ξ₁ < ξ₂)
    (h₂ : ξ₂ < 1) : -N / (p ^ 2 * (1 - ξ₁)) < -N / (p ^ 2 * (1 - ξ₂)) := by
  have hp2 : 0 < p ^ 2 := by positivity
  exact div_lt_div_of_pos_left (by linarith) (mul_pos hp2 (by linarith))
    (mul_lt_mul_of_pos_left (by linarith) hp2)

/-- AKMM, p. 580 (correction): `B > 0`, the hypothesis of Property 19.5.2, does not give
`N = αF − B − D − κ(D − φ)² < 0`: with `αF = 2`, `B = 1`, `D = 0`, `κ = 0` the response of
`K′` to `p` is negative. -/
theorem sys_B_pos_not_sufficient :
    ∃ αF B D κ φ : ℝ, 0 < B ∧ 0 < αF - B - D - κ * (D - φ) ^ 2 :=
  ⟨2, 1, 0, 0, 0, by norm_num, by norm_num⟩

/-! ### Property 19.5.4: a slack constraint -/

/-- **Property 19.5.4** (AKMM, p. 582). If the limit is slack at an equilibrium for `ξ`
(`µ = 0`), then (19.11) holds at every `ξ′` (it involves `ξ` only through `µξ`), the other
conditions (19.13)–(19.16) do not involve `ξ`, and for `ξ′ ≥ ξ` (with `pK′ ≥ 0`) the limit
remains satisfied with `µ = 0` and complementary slackness: the same allocation is an
equilibrium, so an increase in `ξ` has no effect. -/
theorem property_19_5_4 {p rhs K' B' R τ ξ ξ' : ℝ} (hpK : 0 ≤ p * K')
    (h1911 : (1 - 0 * ξ) * p = rhs) (hlim : (1 + τ) * B' / R ≤ ξ * p * K') (hξ : ξ ≤ ξ') :
    (1 - 0 * ξ') * p = rhs ∧ (1 + τ) * B' / R ≤ ξ' * p * K' ∧
      (0 : ℝ) * (ξ' * p * K' - (1 + τ) * B' / R) = 0 := by
  refine ⟨by rw [← h1911]; ring, ?_, by ring⟩
  have : ξ * (p * K') ≤ ξ' * (p * K') := mul_le_mul_of_nonneg_right hξ hpK
  nlinarith

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A strictly slack optimum of a concave problem with a linear limit `b(x) ≤ ξa(x)` is a global
optimum on the convex set `X`. -/
theorem sys_slack_global {X : Set E} {J : E → ℝ} {a b : E →ₗ[ℝ] ℝ} {ξ : ℝ} {x : E}
    (hJ : ConcaveOn ℝ X J) (hx : x ∈ X) (hslack : b x < ξ * a x)
    (hopt : ∀ y ∈ X, b y ≤ ξ * a y → J y ≤ J x) : ∀ y ∈ X, J y ≤ J x := by
  intro y hy
  by_contra hc
  push Not at hc
  set s := ξ * a x - b x with hs
  set r := b y - ξ * a y with hr
  have hs0 : 0 < s := by rw [hs]; linarith
  rcases le_or_gt r 0 with hr0 | hr0
  · exact absurd (hopt y hy (by rw [hr] at hr0; linarith)) (not_le.2 hc)
  · set t := s / (s + r) with ht
    have hsr : 0 < s + r := by linarith
    have ht0 : 0 < t := div_pos hs0 hsr
    have ht1 : t < 1 := (div_lt_one hsr).2 (by linarith)
    have hz : (1 - t) • x + t • y ∈ X := hJ.1 hx hy (by linarith) ht0.le (by ring)
    have hfeas : b ((1 - t) • x + t • y) ≤ ξ * a ((1 - t) • x + t • y) := by
      simp only [map_add, map_smul, smul_eq_mul]
      have e : (1 - t) * b x + t * b y - ξ * ((1 - t) * a x + t * a y) = t * r - (1 - t) * s := by
        rw [hr, hs]; ring
      have e2 : t * r - (1 - t) * s = 0 := by
        rw [ht]; field_simp; ring
      linarith
    have h1 := hopt _ hz hfeas
    have h2 := hJ.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at h2
    nlinarith

/-- **Property 19.5.4, optimisation form** (AKMM, p. 582): "if they were not borrowing up to
the limit before … there is no reason for them to change that level of borrowing when the limit
expands". For a concave objective on a convex set with the limit `b(x) ≤ ξa(x)`, `a ≥ 0`, a
strictly slack optimum at `ξ` is feasible and optimal at every `ξ′ ≥ ξ`. -/
theorem property_19_5_4_opt {X : Set E} {J : E → ℝ} {a b : E →ₗ[ℝ] ℝ} {ξ ξ' : ℝ} {x : E}
    (hJ : ConcaveOn ℝ X J) (hx : x ∈ X) (ha : 0 ≤ a x) (hξ : ξ ≤ ξ')
    (hslack : b x < ξ * a x) (hopt : ∀ y ∈ X, b y ≤ ξ * a y → J y ≤ J x) :
    b x ≤ ξ' * a x ∧ ∀ y ∈ X, b y ≤ ξ' * a y → J y ≤ J x := by
  refine ⟨by nlinarith, fun y hy _ => sys_slack_global hJ hx hslack hopt y hy⟩

/-! ### Working capital -/

/-- **(19.18)** (AKMM, p. 584): with the working-capital limit `wℓ + b′/R_c ≤ ξpk′` (multiplier
`µλ`), the first-order condition for labour `λ(F_ℓ − w) − µλw = 0`, `λ ≠ 0`, gives
`F_ℓ = (1 + µ)w`. -/
theorem eq_19_18 {lam Fl w μ : ℝ} (hlam : lam ≠ 0) (h : lam * (Fl - w) - μ * lam * w = 0) :
    Fl = (1 + μ) * w := by
  have : lam * (Fl - (1 + μ) * w) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hlam
  · linarith

variable {S : Type*} [Fintype S]

/-- AKMM, p. 584: with working capital the first-order condition for `k′` is the same as
before, so (19.5) is unchanged. -/
theorem sys_wc_19_5 (pr m lams Ωk p' Fk q' : S → ℝ) (lam q μ ξ p δ : ℝ) (hq : 1 = lam * q)
    (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωk s) - lam * p + μ * lam * ξ * p = 0)
    (henv : ∀ s, Ωk s = lams s * ((1 - δ) * p' s + Fk s)) :
    ∑ s, pr s * (m s * (q / q' s * ((1 - δ) * p' s + Fk s))) = (1 - μ * ξ) * p :=
  eq_19_5 pr m lams Ωk p' Fk q' lam q μ ξ p δ hq hqs hfoc henv

/-- AKMM, p. 584: with the limit `wℓ + b′/R̃ ≤ ξpk′` the first-order condition for `b′` is
`E[m′Ω_b′] + λ/R̃ − µλ/R̃ = 0`, so (19.6) is unchanged. -/
theorem sys_wc_19_6_tilde (pr m lams Ωb q' : S → ℝ) (lam q μ Rt : ℝ) (hRt : Rt ≠ 0)
    (hq : 1 = lam * q) (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / Rt = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ :=
  eq_19_6 pr m lams Ωb q' lam q μ Rt hRt hq hqs hfoc henv

/-- AKMM, (19.17), p. 584, as printed (`wℓ + b′/R ≤ ξpk′`, `R = (1 + τ)R̃`): the first-order
condition for `b′` is `E[m′Ω_b′] + λ/R̃ − µλ/R = 0`, and (19.6) becomes
`E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ/(1 + τ)`. -/
theorem sys_wc_19_6_printed (pr m lams Ωb q' : S → ℝ) (lam q μ Rt τ : ℝ) (hRt : Rt ≠ 0)
    (hτ : 1 + τ ≠ 0) (hq : 1 = lam * q) (hqs : ∀ s, 1 = lams s * q' s)
    (hfoc : ∑ s, pr s * (m s * Ωb s) + lam / Rt - μ * lam / ((1 + τ) * Rt) = 0)
    (henv : ∀ s, Ωb s = -lams s) :
    (∑ s, pr s * (m s * (q / q' s))) * Rt = 1 - μ / (1 + τ) := by
  refine eq_19_6 pr m lams Ωb q' lam q (μ / (1 + τ)) Rt hRt hq hqs ?_ henv
  rw [← hfoc]
  field_simp

/-- AKMM, p. 584 (correction): under the printed (19.17), the condition of
`sys_wc_19_6_printed` is not (19.6) whenever `µ ≠ 0` and `τ ≠ 0`: `1 − µ/(1 + τ) ≠ 1 − µ`. -/
theorem sys_wc_19_6_printed_ne {μ τ : ℝ} (hμ : μ ≠ 0) (hτ : τ ≠ 0) (hτ1 : 1 + τ ≠ 0) :
    1 - μ / (1 + τ) ≠ 1 - μ := by
  intro h
  have : μ / (1 + τ) = μ := by linarith
  rw [div_eq_iff hτ1] at this
  have : μ * τ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hμ h1
  · exact hτ h1

end AKMM.CreditFrictions
