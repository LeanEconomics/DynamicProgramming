/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCreditFrictions.TwoPeriod
import AKMMCreditFrictions.System

/-!
# Comparative statics of the two-period model: Properties 19.5.1, 19.5.3 and 19.5.5

AKMM, §19.5.1, Property 19.5.1, pp. 579–580; §19.5.3, Property 19.5.3, pp. 581–582; §19.5.4,
Property 19.5.5, pp. 582–583.

The book argues these properties from (19.11)–(19.13) and (19.15) "keeping other things
unchanged". We prove them for the firm's problem at given prices: the interest rate `R` and the
discount factor `Λ = β(C − L^ν)/g(z′, K′) = 1/R` are held fixed, as in the book's argument
(they are general-equilibrium objects the book does not sign). The equations are

* (19.11) `(1 − µξ)p = Λ(1 − δ + F_k(K′))ϕ′(D)`,
* (19.15) `(1 − µ)(1 + τ)/R = Λϕ′(D)`,
* the budget with the binding limit (19.12)–(19.13), `αF + ξpK′ = B + p[K′ − (1 − δ)K] + ϕ(D)`.

From (19.11) and (19.15), `Λ(1 − δ + F_k) = p[(1 − ξ)/ϕ′(D) + ξc]`, `c = RΛ/(1 + τ)`, and
`µ = 1 − cϕ′(D)` (`cs_return`, `cs_mu`): the effective cost of capital is a weighted average of
`1/ϕ′(D)` (equity) and `c` (debt), with `c < 1/ϕ′(D)` exactly when the limit binds.

* **Property 19.5.3** (`property_19_5_3`): with a binding limit (`µ₀ > 0`), a lower `ξ` lowers
  `K′`; hence next period's output and employment fall (`property_19_5_3_output`). No sign
  condition beyond `κ ≥ 0`, `ϕ′ > 0`, `ξ ≤ 1` and `F_k` decreasing is needed. In general
  equilibrium with `κ = 0` (so `µ = τ/(1 + τ)`), the same holds when `C − L^ν = W − pK′`,
  `F_k` decreases and `g` increases in `K′` (`property_19_5_3_ge`).
* **Property 19.5.1** (`property_19_5_1`): a rise in `z′` with current profits `αF` not falling
  raises `K′` with a binding limit, and also with a slack one (`property_19_5_1_slack`). With
  the closed-form `F_k` (`ν > 1`), if dividends fall (`D₁ < D₀`, which holds automatically when
  only `z′` changes, `cs_div_falls`) the proportional response of `K′` is strictly smaller with
  the binding limit than with a slack one (`property_19_5_1_dampening`).
* **Property 19.5.5** (`property_19_5_5`): starting from a slack solution, a fall in `ξ` large
  enough that the old plan violates the limit (`ξ₁pK₀′ < B₀′/R̃`) forces the limit to bind and
  strictly lowers `K′` (`κ > 0`, `ξ₁ < 1`); next period's output and employment fall
  (`property_19_5_5_output`).
-/

namespace AKMM.CreditFrictions

open Set

/-- AKMM, (19.11) and (19.15): the return to capital equals the effective cost,
`Λ(1 − δ + F_k) = p[(1 − ξ)/ϕ′(D) + ξRΛ/(1 + τ)]`. -/
theorem cs_return {Λ R τ p δ Fk ξ μ q : ℝ} (hq : 0 < q) (hτ : 0 < 1 + τ) (hR : 0 < R)
    (h1911 : (1 - μ * ξ) * p = Λ * (1 - δ + Fk) * q) (h1915 : (1 - μ) * (1 + τ) / R = Λ * q) :
    Λ * (1 - δ + Fk) = p * ((1 - ξ) / q + ξ * (R * Λ / (1 + τ))) := by
  have h' : (1 - μ) * (1 + τ) = R * Λ * q := by
    rw [div_eq_iff hR.ne'] at h1915
    linarith
  have hc : R * Λ / (1 + τ) * q = 1 - μ := by
    rw [div_mul_eq_mul_div, div_eq_iff hτ.ne']
    linarith
  have e : Λ * (1 - δ + Fk) * q = p * ((1 - ξ) / q + ξ * (R * Λ / (1 + τ))) * q := by
    rw [← h1911, mul_assoc p, add_mul, div_mul_cancel₀ _ hq.ne', mul_assoc ξ, hc]
    ring
  exact mul_right_cancel₀ hq.ne' e

/-- AKMM, (19.15): `µ = 1 − cϕ′(D)` with `c = RΛ/(1 + τ)`. -/
theorem cs_mu {Λ R τ μ q : ℝ} (hτ : 0 < 1 + τ) (hR : 0 < R)
    (h1915 : (1 - μ) * (1 + τ) / R = Λ * q) : μ = 1 - R * Λ / (1 + τ) * q := by
  have h' : (1 - μ) * (1 + τ) = R * Λ * q := by
    rw [div_eq_iff hR.ne'] at h1915
    linarith
  have hc : R * Λ / (1 + τ) * q = 1 - μ := by
    rw [div_mul_eq_mul_div, div_eq_iff hτ.ne']
    linarith
  linarith

/-- **Property 19.5.3** (AKMM, pp. 581–582). Let `(K₀, D₀, µ₀)` solve (19.11), (19.15) and the
budget with the binding limit at `ξ₀`, with `µ₀ > 0`, and `(K₁, D₁, µ₁)` solve them at
`ξ₁ < ξ₀ ≤ 1`, with `ϕ′(D₀), ϕ′(D₁) > 0`, `κ ≥ 0`, at the same prices `R, Λ > 0` and with
`F_k` strictly decreasing. Then `K₁ < K₀`: "a negative financial shock has a negative impact on
capital accumulation". -/
theorem property_19_5_3 {Fk : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    {Λ R τ p δ α F B K κ φ ξ₀ ξ₁ K₀ K₁ D₀ D₁ μ₀ μ₁ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hξ : ξ₁ < ξ₀) (hξ1 : ξ₀ ≤ 1) (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ₀) * p = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F + ξ₀ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ₁) * p = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F + ξ₁ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁)
    (hμ₀ : 0 < μ₀) : K₁ < K₀ := by
  by_contra hc
  push Not at hc
  set c := R * Λ / (1 + τ) with hcdef
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  have hm₀ := cs_mu hτ hR h15₀
  -- the binding limit: `c < 1/ϕ′(D₀)`
  have hc0 : c < 1 / cfPhiD κ φ D₀ := by
    rw [lt_div_iff₀ hq₀]
    linarith
  -- dividends fall
  have hphi : cfPhi κ φ D₁ < cfPhi κ φ D₀ := by
    have : (1 - ξ₀) * K₀ < (1 - ξ₁) * K₁ := by nlinarith
    nlinarith
  have hD := div_lt_of_phi_lt hq₀ hq₁ hphi
  have hqq : cfPhiD κ φ D₁ ≤ cfPhiD κ φ D₀ := div_phiD_le hκ hD.le
  have hinv : 1 / cfPhiD κ φ D₀ ≤ 1 / cfPhiD κ φ D₁ := one_div_le_one_div_of_le hq₁ hqq
  -- the effective cost rises
  have hcost : (1 - ξ₀) / cfPhiD κ φ D₀ + ξ₀ * c < (1 - ξ₁) / cfPhiD κ φ D₁ + ξ₁ * c := by
    have e₀ : (1 - ξ₀) / cfPhiD κ φ D₀ = (1 - ξ₀) * (1 / cfPhiD κ φ D₀) := by ring
    have e₁ : (1 - ξ₁) / cfPhiD κ φ D₁ = (1 - ξ₁) * (1 / cfPhiD κ φ D₁) := by ring
    rw [e₀, e₁]
    nlinarith
  have hFk1 : Fk K₀ < Fk K₁ := by
    have : Λ * (1 - δ + Fk K₀) < Λ * (1 - δ + Fk K₁) := by
      rw [hr₀, hr₁]
      exact mul_lt_mul_of_pos_left hcost hp
    nlinarith
  rcases hc.lt_or_eq with h | h
  · exact absurd (hFk hK₀ hK₁ h) (not_lt.2 hFk1.le)
  · rw [h] at hFk1
    exact lt_irrefl _ hFk1

/-- **Property 19.5.3, output and employment** (AKMM, p. 582): with the closed forms of the
two-period model (`e = α + ν − 1 > 0`, `0 < α < 1`), the lower `K′` lowers next period's
employment `L′` and output `Y′`. -/
theorem property_19_5_3_output {α ν z' K₀ K₁ : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z') (he : 0 < α + ν - 1) (hK₁ : 0 < K₁) (hK : K₁ < K₀) :
    tpL α ν 1 z' K₁ < tpL α ν 1 z' K₀ ∧ tpY α ν z' K₁ < tpY α ν z' K₀ :=
  ⟨tp_L_strictMono_K hα0 hα hν one_pos hz he hK₁ (hK₁.trans hK) hK,
    tp_Y_strictMono_K hα0 hα hν hz he hK₁ (hK₁.trans hK) hK⟩

/-- **Property 19.5.3 in general equilibrium with `κ = 0`** (AKMM, pp. 581–582). With `κ = 0`,
(19.15)–(19.16) give `µ = τ/(1 + τ)`, and with the resource constraint
`C − L^ν = W − pK′` (`W = F + p(1 − δ)K − L^ν`), (19.11) reads
`(1 − µξ)p = β(W − pK′)(1 − δ + F_k(K′))/g(K′)`. If `τ > 0`, `F_k` is strictly decreasing,
`g` increasing and positive, `1 − δ + F_k > 0` and `W − pK′ > 0`, then `ξ₁ < ξ₀` gives
`K₁ < K₀`. -/
theorem property_19_5_3_ge {Fk g : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    (hg : MonotoneOn g (Ioi 0)) {β W p δ τ R ξ₀ ξ₁ K₀ K₁ μ₀ μ₁ C₀ C₁ : ℝ} (hβ : 0 < β)
    (hp : 0 < p) (hτ : 0 < τ) (hR : 0 < R) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hg₀ : 0 < g K₀) (hret₁ : 0 < 1 - δ + Fk K₁)
    (hW₀ : 0 < W - p * K₀) (hW₁ : 0 < W - p * K₁) (hξ : ξ₁ < ξ₀)
    (h11₀ : (1 - μ₀ * ξ₀) * p = β * (C₀ / g K₀) * (1 - δ + Fk K₀) * (1 + 2 * 0 * (0 : ℝ)))
    (h15₀ : (1 - μ₀) * (1 + τ) / R = β * (C₀ / g K₀) * (1 + 2 * 0 * (0 : ℝ)))
    (h16₀ : 1 / R = β * (C₀ / g K₀)) (hC₀ : C₀ = W - p * K₀)
    (h11₁ : (1 - μ₁ * ξ₁) * p = β * (C₁ / g K₁) * (1 - δ + Fk K₁) * (1 + 2 * 0 * (0 : ℝ)))
    (h15₁ : (1 - μ₁) * (1 + τ) / R = β * (C₁ / g K₁) * (1 + 2 * 0 * (0 : ℝ)))
    (h16₁ : 1 / R = β * (C₁ / g K₁)) (hC₁ : C₁ = W - p * K₁) : K₁ < K₀ := by
  -- `µ = τ/(1 + τ)` at both
  have hμ : ∀ μ : ℝ, (1 - μ) * (1 + τ) / R = 1 / R → μ = τ / (1 + τ) := by
    intro μ h
    have h1 : (1 + τ) ≠ 0 := by linarith
    field_simp at h ⊢
    linarith
  have hμ₀ := hμ μ₀ (by rw [h15₀, h16₀]; ring)
  have hμ₁ := hμ μ₁ (by rw [h15₁, h16₁]; ring)
  have hμpos : 0 < τ / (1 + τ) := div_pos hτ (by linarith)
  have hlhs : (1 - μ₀ * ξ₀) * p < (1 - μ₁ * ξ₁) * p := by
    rw [hμ₀, hμ₁]
    exact mul_lt_mul_of_pos_right (by nlinarith) hp
  by_contra hc
  push Not at hc
  have hgle : g K₀ ≤ g K₁ := hg hK₀ hK₁ hc
  have hg₁ : 0 < g K₁ := lt_of_lt_of_le hg₀ hgle
  have hFle : Fk K₁ ≤ Fk K₀ := by
    rcases hc.lt_or_eq with h | h
    · exact (hFk hK₀ hK₁ h).le
    · rw [h]
  have hH : β * (C₁ / g K₁) * (1 - δ + Fk K₁) ≤ β * (C₀ / g K₀) * (1 - δ + Fk K₀) := by
    rw [hC₀, hC₁]
    have h1 : (W - p * K₁) / g K₁ ≤ (W - p * K₀) / g K₀ :=
      div_le_div₀ hW₀.le (by nlinarith) hg₀ hgle
    have h2 : 0 ≤ (W - p * K₁) / g K₁ := (div_pos hW₁ hg₁).le
    have h3 := mul_le_mul h1 (by linarith : 1 - δ + Fk K₁ ≤ 1 - δ + Fk K₀) hret₁.le
      (div_pos hW₀ hg₀).le
    nlinarith
  simp only [mul_zero, add_zero, mul_one] at h11₀ h11₁
  linarith

/-- **Property 19.5.1, binding limit** (AKMM, p. 579): "The response of investment to the
productivity shock is positive." At given prices, let `(K₀, D₀, µ₀)` and `(K₁, D₁, µ₁)` solve
(19.11), (19.15) and the budget with the binding limit for `(z₀′, F₀)` and `(z₁′, F₁)`, with
`z₀′ < z₁′`, current profits not falling (`αF₀ ≤ αF₁`), `ξ ≤ 1`, `κ ≥ 0`, `ϕ′ > 0`, and `F_k`
strictly increasing in `z′` and strictly decreasing in `K′`. Then `K₀ < K₁`. -/
theorem property_19_5_1 {Fk : ℝ → ℝ → ℝ} (hz : ∀ K, 0 < K → StrictMonoOn (Fk · K) (Ioi 0))
    (hK : ∀ z, 0 < z → StrictAntiOn (Fk z) (Ioi 0))
    {Λ R τ p δ α F₀ F₁ B K κ φ ξ z₀ z₁ K₀ K₁ D₀ D₁ μ₀ μ₁ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hz₀ : 0 < z₀) (hz01 : z₀ < z₁) (hF : α * F₀ ≤ α * F₁) (hξ1 : ξ ≤ 1)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ) * p = Λ * (1 - δ + Fk z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F₀ + ξ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ) * p = Λ * (1 - δ + Fk z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F₁ + ξ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁) : K₀ < K₁ := by
  by_contra hc
  push Not at hc
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  -- dividends do not fall
  have hD : D₀ ≤ D₁ := by
    by_contra hD
    push Not at hD
    have e := div_phi_sub κ φ D₀ D₁
    have : (D₁ - D₀) * (cfPhiD κ φ D₀ + cfPhiD κ φ D₁) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have h0 : 0 ≤ (1 - ξ) * p * (K₀ - K₁) :=
      mul_nonneg (mul_nonneg (by linarith) hp.le) (by linarith)
    have : cfPhi κ φ D₁ - cfPhi κ φ D₀ = α * F₁ - α * F₀ + (1 - ξ) * p * (K₀ - K₁) := by
      linear_combination h13₀ - h13₁
    linarith
  have hqq : cfPhiD κ φ D₀ ≤ cfPhiD κ φ D₁ := div_phiD_le hκ hD
  have hinv : 1 / cfPhiD κ φ D₁ ≤ 1 / cfPhiD κ φ D₀ := one_div_le_one_div_of_le hq₀ hqq
  have hcost : (1 - ξ) / cfPhiD κ φ D₁ ≤ (1 - ξ) / cfPhiD κ φ D₀ := by
    have e₀ : (1 - ξ) / cfPhiD κ φ D₀ = (1 - ξ) * (1 / cfPhiD κ φ D₀) := by ring
    have e₁ : (1 - ξ) / cfPhiD κ φ D₁ = (1 - ξ) * (1 / cfPhiD κ φ D₁) := by ring
    rw [e₀, e₁]
    exact mul_le_mul_of_nonneg_left hinv (by linarith)
  have hle : Fk z₁ K₁ ≤ Fk z₀ K₀ := by
    have : Λ * (1 - δ + Fk z₁ K₁) ≤ Λ * (1 - δ + Fk z₀ K₀) := by
      rw [hr₀, hr₁]
      exact mul_le_mul_of_nonneg_left (by linarith) hp.le
    nlinarith
  have hz₁ : 0 < z₁ := hz₀.trans hz01
  have h1 : Fk z₁ K₀ ≤ Fk z₁ K₁ := by
    rcases hc.lt_or_eq with h | h
    · exact (hK z₁ hz₁ hK₁ hK₀ h).le
    · rw [h]
  have h2 : Fk z₀ K₀ < Fk z₁ K₀ := hz K₀ hK₀ hz₀ hz₁ hz01
  linarith

/-- **Property 19.5.1, slack limit** (AKMM, p. 579): with `µ = 0`, (19.15) pins `ϕ′(D)` and
(19.11) pins `F_k(z′, K′)`, so a rise in `z′` raises `K′`. -/
theorem property_19_5_1_slack {Fk : ℝ → ℝ → ℝ} (hz : ∀ K, 0 < K → StrictMonoOn (Fk · K) (Ioi 0))
    (hK : ∀ z, 0 < z → StrictAntiOn (Fk z) (Ioi 0))
    {Λ R τ p δ κ φ z₀ z₁ K₀ K₁ D₀ D₁ : ℝ} (hΛ : 0 < Λ) (hR : 0 < R) (hτ : 0 < 1 + τ)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hz₀ : 0 < z₀) (hz01 : z₀ < z₁)
    (h11₀ : (1 - 0 * 0) * p = Λ * (1 - δ + Fk z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h11₁ : (1 - 0 * 0) * p = Λ * (1 - δ + Fk z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₁) : K₀ < K₁ := by
  have hq : cfPhiD κ φ D₀ = cfPhiD κ φ D₁ := by
    have := h15₀.symm.trans h15₁
    exact mul_left_cancel₀ hΛ.ne' this
  have hqpos : 0 < cfPhiD κ φ D₀ := by
    have : 0 < (1 - 0) * (1 + τ) / R := by simp only [sub_zero, one_mul]; exact div_pos hτ hR
    rw [h15₀] at this
    exact pos_of_mul_pos_right this hΛ.le
  have heq : Fk z₀ K₀ = Fk z₁ K₁ := by
    rw [← hq] at h11₁
    have := h11₀.symm.trans h11₁
    have := mul_right_cancel₀ hqpos.ne' this
    have := mul_left_cancel₀ hΛ.ne' this
    linarith
  by_contra hc
  push Not at hc
  have hz₁ : 0 < z₁ := hz₀.trans hz01
  have h1 : Fk z₁ K₀ ≤ Fk z₁ K₁ := by
    rcases hc.lt_or_eq with h | h
    · exact (hK z₁ hz₁ hK₁ hK₀ h).le
    · rw [h]
  have h2 : Fk z₀ K₀ < Fk z₁ K₀ := hz K₀ hK₀ hz₀ hz₁ hz01
  linarith

/-- AKMM, p. 579: "in order for the firm to fund the higher investment, it has to reduce
dividends": with the binding limit, unchanged current profits and `ξ < 1`, a rise in `K′`
lowers `D` (`ϕ′ > 0`). -/
theorem cs_div_falls {p δ α F B K κ φ ξ K₀ K₁ D₀ D₁ : ℝ} (hp : 0 < p) (hξ : ξ < 1)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁) (hK : K₀ < K₁)
    (h13₀ : α * F + ξ * p * K₀ = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (h13₁ : α * F + ξ * p * K₁ = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁) : D₁ < D₀ := by
  refine div_lt_of_phi_lt hq₀ hq₁ ?_
  have : 0 < (1 - ξ) * p * (K₁ - K₀) := by
    have := mul_pos (sub_pos.2 hξ) hp
    exact mul_pos this (by linarith)
  nlinarith

/-- Comparing proportional responses: if `z₀^a K₀^b < z₁^a K₁^b` and
`z₀^a S₀^b = z₁^a S₁^b` with `b < 0` and all variables positive, then `K₁/K₀ < S₁/S₀`. -/
theorem cs_ratio_lt {a b z₀ z₁ K₀ K₁ S₀ S₁ : ℝ} (hb : b < 0) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hS₀ : 0 < S₀) (hS₁ : 0 < S₁)
    (h1 : z₀ ^ a * K₀ ^ b < z₁ ^ a * K₁ ^ b) (h2 : z₀ ^ a * S₀ ^ b = z₁ ^ a * S₁ ^ b) :
    K₁ / K₀ < S₁ / S₀ := by
  have ha₀ := Real.rpow_pos_of_pos hz₀ a
  have ha₁ := Real.rpow_pos_of_pos hz₁ a
  have hk₀ := Real.rpow_pos_of_pos hK₀ b
  have hk₁ := Real.rpow_pos_of_pos hK₁ b
  have hs₀ := Real.rpow_pos_of_pos hS₀ b
  have hs₁ := Real.rpow_pos_of_pos hS₁ b
  -- `S₁^b K₀^b < K₁^b S₀^b`
  have key : S₁ ^ b * K₀ ^ b < K₁ ^ b * S₀ ^ b := by
    have e : z₀ ^ a * K₀ ^ b * S₀ ^ b < z₁ ^ a * K₁ ^ b * S₀ ^ b :=
      mul_lt_mul_of_pos_right h1 hs₀
    have e2 : z₀ ^ a * K₀ ^ b * S₀ ^ b = z₁ ^ a * S₁ ^ b * K₀ ^ b := by
      rw [mul_right_comm, h2]
    rw [e2] at e
    have : z₁ ^ a * (S₁ ^ b * K₀ ^ b) < z₁ ^ a * (K₁ ^ b * S₀ ^ b) := by
      calc z₁ ^ a * (S₁ ^ b * K₀ ^ b) = z₁ ^ a * S₁ ^ b * K₀ ^ b := by ring
        _ < z₁ ^ a * K₁ ^ b * S₀ ^ b := e
        _ = z₁ ^ a * (K₁ ^ b * S₀ ^ b) := by ring
    exact lt_of_mul_lt_mul_left this ha₁.le
  by_contra hc
  push Not at hc
  have hlt := (Real.rpow_le_rpow_of_nonpos (div_pos hS₁ hS₀) hc hb.le)
  rw [Real.div_rpow hK₁.le hK₀.le, Real.div_rpow hS₁.le hS₀.le, div_le_div_iff₀ hk₀ hs₀] at hlt
  linarith

/-- **Property 19.5.1, dampening** (AKMM, p. 579): "the responses of investment and output will
be smaller if the borrowing constraint is binding". With the closed-form `F_k` (`0 < α < 1`,
`ν > 1`) and fixed prices, compare a rise `z₀′ < z₁′`
* with a binding limit, solutions `(K₀, D₀)`, `(K₁, D₁)` of (19.11), (19.15) (the budget enters
  only through `D₁ < D₀`, which `cs_div_falls` provides when current profits are unchanged),
  `κ > 0`, `ξ < 1`;
* with a slack limit, solutions `S₀, S₁` of (19.11), (19.15) with `µ = 0`.
Then the proportional response of `K′` is strictly smaller with the binding limit:
`K₁/K₀ < S₁/S₀`. -/
theorem property_19_5_1_dampening {α ν Λ R τ p δ κ φ ξ z₀ z₁ K₀ K₁ S₀ S₁ D₀ D₁ E₀ E₁ μ₀ μ₁ : ℝ}
    (hα0 : 0 < α) (hα : α < 1) (hν : 1 < ν) (hκ : 0 < κ) (hΛ : 0 < Λ) (hp : 0 < p)
    (hR : 0 < R) (hτ : 0 < 1 + τ) (hξ : ξ < 1) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hS₀ : 0 < S₀) (hS₁ : 0 < S₁) (hD : D₁ < D₀)
    (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - μ₀ * ξ) * p = Λ * (1 - δ + tpFk α ν z₀ K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - μ₀) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h11₁ : (1 - μ₁ * ξ) * p = Λ * (1 - δ + tpFk α ν z₁ K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (s11₀ : (1 - 0 * ξ) * p = Λ * (1 - δ + tpFk α ν z₀ S₀) * cfPhiD κ φ E₀)
    (s15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ E₀)
    (s11₁ : (1 - 0 * ξ) * p = Λ * (1 - δ + tpFk α ν z₁ S₁) * cfPhiD κ φ E₁)
    (s15₁ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ E₁) : K₁ / K₀ < S₁ / S₀ := by
  -- binding: the marginal product rises
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  have hqq : cfPhiD κ φ D₁ < cfPhiD κ φ D₀ := by
    have e := div_phiD_sub κ φ D₀ D₁
    have : 0 < κ * (D₀ - D₁) := mul_pos hκ (by linarith)
    linarith
  have hinv : 1 / cfPhiD κ φ D₀ < 1 / cfPhiD κ φ D₁ := one_div_lt_one_div_of_lt hq₁ hqq
  have hbind : tpFk α ν z₀ K₀ < tpFk α ν z₁ K₁ := by
    have : Λ * (1 - δ + tpFk α ν z₀ K₀) < Λ * (1 - δ + tpFk α ν z₁ K₁) := by
      rw [hr₀, hr₁]
      refine mul_lt_mul_of_pos_left ?_ hp
      have e₀ : (1 - ξ) / cfPhiD κ φ D₀ = (1 - ξ) * (1 / cfPhiD κ φ D₀) := by ring
      have e₁ : (1 - ξ) / cfPhiD κ φ D₁ = (1 - ξ) * (1 / cfPhiD κ φ D₁) := by ring
      rw [e₀, e₁]
      have := mul_lt_mul_of_pos_left hinv (sub_pos.2 hξ)
      linarith
    have := lt_of_mul_lt_mul_left this hΛ.le
    linarith
  -- slack: the marginal product is unchanged
  have hslack : tpFk α ν z₀ S₀ = tpFk α ν z₁ S₁ := by
    have hq : cfPhiD κ φ E₀ = cfPhiD κ φ E₁ := mul_left_cancel₀ hΛ.ne' (s15₀.symm.trans s15₁)
    have hqpos : 0 < cfPhiD κ φ E₀ := by
      have : 0 < (1 - 0) * (1 + τ) / R := by simp only [sub_zero, one_mul]; exact div_pos hτ hR
      rw [s15₀] at this
      exact pos_of_mul_pos_right this hΛ.le
    rw [← hq] at s11₁
    have := mul_right_cancel₀ hqpos.ne' (s11₀.symm.trans s11₁)
    have := mul_left_cancel₀ hΛ.ne' this
    linarith
  -- compare through the closed form
  have he : 0 < α + ν - 1 := by linarith
  set cK := α * ((1 - α) / ν) ^ ((1 - α) / (α + ν - 1)) with hcK
  have hc : 0 < cK :=
    mul_pos hα0 (Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _)
  have hb : ν * α / (α + ν - 1) - 1 < 0 := by
    rw [sub_neg, div_lt_one he]
    nlinarith
  have hform : ∀ z K, tpFk α ν z K =
      cK * (z ^ (ν / (α + ν - 1)) * K ^ (ν * α / (α + ν - 1) - 1)) := by
    intro z K
    simp only [tpFk, hcK]
    ring
  rw [hform, hform] at hbind hslack
  exact cs_ratio_lt hb hz₀ hz₁ hK₀ hK₁ hS₀ hS₁ (lt_of_mul_lt_mul_left hbind hc.le)
    (mul_left_cancel₀ hc.ne' hslack)

/-- **Property 19.5.5** (AKMM, p. 583). At fixed prices with `κ > 0`, let `(K₀, D₀, B₀)` be a
solution with a slack limit at `ξ₀` (`µ₀ = 0`: (19.11), (19.15) and the budget
`αF + B′/R̃ = B + p[K′ − (1 − δ)K] + ϕ(D)`), and let `ξ₁ < 1` fall so far that the old plan
violates the limit, `ξ₁pK₀ < B₀/R̃`. Let `(K₁, D₁, B₁, µ₁)` satisfy the Kuhn–Tucker conditions
at `ξ₁`: (19.11), (19.15), the budget, `B₁/R̃ ≤ ξ₁pK₁`, `µ₁ ≥ 0`, `µ₁(ξ₁pK₁ − B₁/R̃) = 0`. Then
the limit binds and `K₁ < K₀`: "a sufficiently large decrease in `ξ` reduces investment". -/
theorem property_19_5_5 {Fk : ℝ → ℝ} (hFk : StrictAntiOn Fk (Ioi 0))
    {Λ R τ p δ α F B K κ φ Rt ξ₀ ξ₁ K₀ K₁ D₀ D₁ B₀ B₁ μ₁ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ)
    (hp : 0 < p) (hR : 0 < R) (hτ : 0 < 1 + τ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁)
    (hξ1 : ξ₁ < 1) (hq₀ : 0 < cfPhiD κ φ D₀) (hq₁ : 0 < cfPhiD κ φ D₁)
    (h11₀ : (1 - 0 * ξ₀) * p = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀)
    (h15₀ : (1 - 0) * (1 + τ) / R = Λ * cfPhiD κ φ D₀)
    (h13₀ : α * F + B₀ / Rt = B + p * (K₀ - (1 - δ) * K) + cfPhi κ φ D₀)
    (hbig : ξ₁ * p * K₀ < B₀ / Rt)
    (h11₁ : (1 - μ₁ * ξ₁) * p = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁)
    (h15₁ : (1 - μ₁) * (1 + τ) / R = Λ * cfPhiD κ φ D₁)
    (h13₁ : α * F + B₁ / Rt = B + p * (K₁ - (1 - δ) * K) + cfPhi κ φ D₁)
    (hlim₁ : B₁ / Rt ≤ ξ₁ * p * K₁) (hμ₁ : 0 ≤ μ₁) (hcs₁ : μ₁ * (ξ₁ * p * K₁ - B₁ / Rt) = 0) :
    0 < μ₁ ∧ B₁ / Rt = ξ₁ * p * K₁ ∧ K₁ < K₀ := by
  set c := R * Λ / (1 + τ) with hcdef
  have hm₀ := cs_mu hτ hR h15₀
  have hm₁ := cs_mu hτ hR h15₁
  have hr₀ := cs_return hq₀ hτ hR h11₀ h15₀
  have hr₁ := cs_return hq₁ hτ hR h11₁ h15₁
  -- the limit binds
  have hpos : 0 < μ₁ := by
    rcases hμ₁.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hm₁
      have hq : cfPhiD κ φ D₁ = cfPhiD κ φ D₀ := by
        have hc0 : c ≠ 0 := by rw [hcdef]; exact (div_pos (mul_pos hR hΛ) hτ).ne'
        have : c * cfPhiD κ φ D₁ = c * cfPhiD κ φ D₀ := by linarith
        exact mul_left_cancel₀ hc0 this
      have hDeq : D₁ = D₀ := by
        have := div_phiD_sub κ φ D₀ D₁
        rw [hq, sub_self] at this
        have : κ * (D₁ - D₀) = 0 := by linarith
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd h1 hκ.ne'
        · linarith
      have hFeq : Fk K₁ = Fk K₀ := by
        have e1 : Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₀ = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀ :=
          calc Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₀ = Λ * (1 - δ + Fk K₁) * cfPhiD κ φ D₁ := by
                rw [hq]
            _ = (1 - μ₁ * ξ₁) * p := h11₁.symm
            _ = (1 - 0 * ξ₀) * p := by rw [← h]; ring
            _ = Λ * (1 - δ + Fk K₀) * cfPhiD κ φ D₀ := h11₀
        have := mul_left_cancel₀ hΛ.ne' (mul_right_cancel₀ hq₀.ne' e1)
        linarith
      have hKeq : K₁ = K₀ := hFk.injOn hK₁ hK₀ hFeq
      have hBeq : B₁ / Rt = B₀ / Rt := by rw [hKeq, hDeq] at h13₁; linarith
      rw [hBeq, hKeq] at hlim₁
      linarith
  have hbind : B₁ / Rt = ξ₁ * p * K₁ := by
    rcases mul_eq_zero.1 hcs₁ with h | h
    · exact absurd h hpos.ne'
    · linarith
  refine ⟨hpos, hbind, ?_⟩
  -- the effective cost rises above `c`
  have hc1 : c < 1 / cfPhiD κ φ D₁ := by
    rw [lt_div_iff₀ hq₁]
    linarith
  have hc0 : 1 / cfPhiD κ φ D₀ = c := by
    rw [div_eq_iff hq₀.ne']
    linarith
  have hFk1 : Fk K₀ < Fk K₁ := by
    have : Λ * (1 - δ + Fk K₀) < Λ * (1 - δ + Fk K₁) := by
      rw [hr₀, hr₁]
      have e₀ : (1 - ξ₀) / cfPhiD κ φ D₀ = (1 - ξ₀) * (1 / cfPhiD κ φ D₀) := by ring
      have e₁ : (1 - ξ₁) / cfPhiD κ φ D₁ = (1 - ξ₁) * (1 / cfPhiD κ φ D₁) := by ring
      rw [e₀, e₁, hc0]
      have := mul_lt_mul_of_pos_left hc1 (sub_pos.2 hξ1)
      nlinarith
    nlinarith
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with h | h
  · exact absurd (hFk hK₀ hK₁ h) (not_lt.2 hFk1.le)
  · rw [h] at hFk1
    exact lt_irrefl _ hFk1

/-- **Property 19.5.5, output and employment** (AKMM, p. 583): the lower `K′` reduces future
output and employment (closed forms, `e > 0`, `0 < α < 1`). -/
theorem property_19_5_5_output {α ν z' K₀ K₁ : ℝ} (hα0 : 0 < α) (hα : α < 1) (hν : 0 < ν)
    (hz : 0 < z') (he : 0 < α + ν - 1) (hK₁ : 0 < K₁) (hK : K₁ < K₀) :
    tpL α ν 1 z' K₁ < tpL α ν 1 z' K₀ ∧ tpY α ν z' K₁ < tpY α ν z' K₀ :=
  property_19_5_3_output hα0 hα hν hz he hK₁ hK

end AKMM.CreditFrictions
