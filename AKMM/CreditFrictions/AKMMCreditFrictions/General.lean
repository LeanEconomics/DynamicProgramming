/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMCreditFrictions.MM
import AKMMCreditFrictions.Household
import NeoclassicalGrowth.RMDecentral

/-!
# The general model and the neoclassical growth model

AKMM, §19.6, (19.19)–(19.22), Proposition 19.1 and the box "More intuition for
Modigliani–Miller principle", pp. 585–587.

* **(19.19)–(19.22)**: (19.4) and (19.8) give `F₃ = −u₂/u₁` (`eq_19_19`); (19.5) with
  `m′ = βu₁′/u₁` is (19.20) (`eq_19_20`); (19.6) with `R̃ = R/(1 + τ)` is (19.21)
  (`eq_19_21`); (19.22) is the household's (19.9) (`eq_19_22`).
* **`κ = 0`** (p. 586): (19.21) and (19.22) give `(1 − µ)(1 + τ) = 1`, so `µ = τ/(1 + τ)` and
  `µ > 0` iff `τ > 0` (`gm_kappa_zero`, `gm_binding_iff`).
* **`κ > 0`** (p. 586): `µ > 0` iff `E[m′ϕ′(D)/ϕ′(D′)] < (1 + τ)E[m′]`, so if the
  `m′`-weighted mean of `ϕ′(D)/ϕ′(D′)` is at least `1 + τ`, (19.21) cannot hold with `µ > 0`
  (`gm_mu_pos_iff`, `gm_not_binding`). Scaling `m′` (a higher level of `u₁′/u₁`) with `R`
  adjusting through (19.22) leaves `µ` unchanged (`gm_mu_scale`); without uncertainty
  `µ = 1 − ϕ′(D)/((1 + τ)ϕ′(D′))` (`gm_mu_det`).
* **Proposition 19.1** (p. 586): with `τ = κ = 0` and `p ≡ 1`, a deterministic equilibrium of the
  economy with financial frictions has `µ ≡ 0` and its allocation satisfies the household,
  firm and market-clearing conditions of the neoclassical growth model as formalised in Miao
  Ch. 14 (`Miao.NeoclassicalGrowth.RMHHFOC`, `RMFirmFOC`, `RMClear`) (`proposition_19_1`),
  hence the planner's conditions (`proposition_19_1_planner`, via `rm_ce_planner`); debt is
  indeterminate: every debt path satisfying the limit, with dividends from the firm's budget,
  gives an equilibrium with the same allocation (`proposition_19_1_debt`), and there are
  distinct ones (`proposition_19_1_indeterminate`).
* **The box on p. 587**: when `τ = κ = 0`, (19.6) is `E[m′R] = 1`, so the gain
  `∆(1 − E[m′R])` from changing the financing is zero (`gm_box`).

Departure: Proposition 19.1 is proved for the deterministic model, by comparing the first-order
and market-clearing conditions as the book's proof does; transversality conditions are not
compared.
-/

namespace AKMM.CreditFrictions

open Miao.NeoclassicalGrowth

/-- **(19.19)** (AKMM, p. 585): (19.4) `F₃ = w` and (19.8) `u₁w = −u₂` with `u₁ ≠ 0` give
`F₃(z, K, L) = −u₂(C, L)/u₁(C, L)`. -/
theorem eq_19_19 {F3 w u1 u2 : ℝ} (hu1 : u1 ≠ 0) (h194 : F3 = w) (h198 : u1 * w = -u2) :
    F3 = -u2 / u1 := by
  rw [h194, eq_div_iff hu1]
  linarith

variable {S : Type*} [Fintype S]

/-- **(19.20)** (AKMM, p. 585): (19.5) with the stochastic discount factor
`m′ₛ = βu₁(C′ₛ, L′ₛ)/u₁(C, L)`. -/
theorem eq_19_20 (pr u1' q' p' F2 : S → ℝ) {β u1 q μ ξ p δ : ℝ}
    (h195 : ∑ s, pr s * (β * u1' s / u1 * (q / q' s * ((1 - δ) * p' s + F2 s))) =
      (1 - μ * ξ) * p) :
    (1 - μ * ξ) * p = ∑ s, pr s * (β * (u1' s / u1) * (q / q' s) * ((1 - δ) * p' s + F2 s)) := by
  rw [← h195]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **(19.21)** (AKMM, p. 586): (19.6) `E[m′ϕ′(D)/ϕ′(D′)]R̃ = 1 − µ` with `R̃ = R/(1 + τ)` is
`(1 − µ)(1 + τ)/R = E[β(u₁′/u₁)ϕ′(D)/ϕ′(D′)]`. -/
theorem eq_19_21 (pr m r : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h196 : (∑ s, pr s * (m s * r s)) * (R / (1 + τ)) = 1 - μ) :
    (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s) := by
  rw [← h196]
  field_simp

/-- **(19.22)** (AKMM, p. 586): the household's bond condition, (19.9) (printed as "(19.6)"),
`1/R = E[βu₁(C′, L′)/u₁(C, L)]`. -/
theorem eq_19_22 (pr u1' : S → ℝ) {β u1 R : ℝ}
    (h199 : 1 / R = ∑ s, pr s * (β * u1' s / u1)) :
    1 / R = ∑ s, pr s * (β * (u1' s / u1)) := by
  rw [h199]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- AKMM, p. 586: "If we relax Assumption 19.4.3 by imposing `κ = 0` …, conditions (19.21) and
(19.22) imply `(1 − µ)(1 + τ) = 1`": with `ϕ′ ≡ 1`, `µ = τ/(1 + τ)`. -/
theorem gm_kappa_zero (pr m : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * 1))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    (1 - μ) * (1 + τ) = 1 ∧ μ = τ / (1 + τ) := by
  have e : ∑ s, pr s * (m s * 1) = ∑ s, pr s * m s := by simp
  rw [e, ← h1922] at h1921
  have h1 : (1 - μ) * (1 + τ) = 1 := by
    field_simp at h1921
    linarith
  refine ⟨h1, ?_⟩
  field_simp
  linarith

/-- AKMM, p. 586: "a sufficient condition to have a binding borrowing constraint (so that
`µ > 0`) is that `τ > 0`": with `κ = 0` and `1 + τ > 0`, `µ > 0` iff `τ > 0`. -/
theorem gm_binding_iff (pr m : S → ℝ) {μ R τ : ℝ} (hR : R ≠ 0) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * 1))
    (h1922 : 1 / R = ∑ s, pr s * m s) : 0 < μ ↔ 0 < τ := by
  rw [(gm_kappa_zero pr m hR hτ.ne' h1921 h1922).2, div_pos_iff_of_pos_right hτ]

/-- AKMM, p. 586: with `κ > 0`, (19.21) and (19.22) give
`(1 − µ)(1 + τ)E[m′] = E[m′ϕ′(D)/ϕ′(D′)]`, so (with `E[m′] = 1/R > 0`) `µ > 0` iff
`E[m′ϕ′(D)/ϕ′(D′)] < (1 + τ)E[m′]`. -/
theorem gm_mu_pos_iff (pr m r : S → ℝ) {μ R τ : ℝ} (hR : 0 < R) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    0 < μ ↔ ∑ s, pr s * (m s * r s) < (1 + τ) * ∑ s, pr s * m s := by
  rw [← h1921, ← h1922]
  have : (1 - μ) * (1 + τ) / R = (1 + τ) * (1 / R) - μ * ((1 + τ) / R) := by ring
  rw [this]
  have hp : 0 < (1 + τ) / R := div_pos hτ hR
  constructor
  · intro h
    have := mul_pos h hp
    linarith
  · intro h
    have : 0 < μ * ((1 + τ) / R) := by linarith
    exact pos_of_mul_pos_left this hp.le

/-- AKMM, p. 586: "if in expectation `ϕ′(D)/ϕ′(D′)` is sufficiently larger than 1, then condition
(19.21) cannot be satisfied with `µ > 0`": precisely, if
`E[m′ϕ′(D)/ϕ′(D′)] ≥ (1 + τ)E[m′]`, then `µ ≤ 0`. -/
theorem gm_not_binding (pr m r : S → ℝ) {μ R τ : ℝ} (hR : 0 < R) (hτ : 0 < 1 + τ)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s)
    (hbig : (1 + τ) * ∑ s, pr s * m s ≤ ∑ s, pr s * (m s * r s)) : μ ≤ 0 := by
  by_contra h
  push Not at h
  have := (gm_mu_pos_iff pr m r hR hτ h1921 h1922).1 h
  linarith

/-- AKMM, p. 586 (clarification): scaling the discount factor `m′` by `c > 0` (a higher level of
`u₁′/u₁`), with `R` adjusting through (19.22), leaves (19.21)–(19.22) satisfied with the same
`µ`: the level of `u₁′/u₁` alone does not decide whether the limit binds. -/
theorem gm_mu_scale (pr m r : S → ℝ) {μ R τ c : ℝ} (hc : 0 < c)
    (h1921 : (1 - μ) * (1 + τ) / R = ∑ s, pr s * (m s * r s))
    (h1922 : 1 / R = ∑ s, pr s * m s) :
    (1 - μ) * (1 + τ) / (R / c) = ∑ s, pr s * (c * m s * r s) ∧
      1 / (R / c) = ∑ s, pr s * (c * m s) := by
  have e1 : ∑ s, pr s * (c * m s * r s) = c * ∑ s, pr s * (m s * r s) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : ∑ s, pr s * (c * m s) = c * ∑ s, pr s * m s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, e2, ← h1921, ← h1922]
  constructor <;> field_simp

/-- AKMM, p. 586: without uncertainty, (19.21)–(19.22) give `µ = 1 − ϕ′(D)/((1 + τ)ϕ′(D′))`,
independent of `u₁′/u₁`. -/
theorem gm_mu_det {μ R τ m r : ℝ} (hR : R ≠ 0) (hτ : 1 + τ ≠ 0)
    (h1921 : (1 - μ) * (1 + τ) / R = m * r) (h1922 : 1 / R = m) :
    μ = 1 - r / (1 + τ) := by
  rw [← h1922] at h1921
  field_simp at h1921 ⊢
  linarith

/-- **The box on p. 587** (AKMM): when `τ = κ = 0`, the firm's (19.6),
`E[m′ϕ′(d)/ϕ′(d′)]R̃ = 1 − µ`, with `µ = 0` (from `gm_kappa_zero` at `τ = 0`) is
`E[m′R] = 1`, and the gain `∆ − E[m′∆R]` from raising `∆` by debt is zero for every `∆`. -/
theorem gm_box (pr m : S → ℝ) {μ R : ℝ} (hμ : μ = 0)
    (h196 : (∑ s, pr s * (m s * (cfPhiD 0 0 0 / cfPhiD 0 0 0))) * (R / (1 + 0)) = 1 - μ)
    (Δ : ℝ) : Δ - ∑ s, pr s * (m s * (Δ * R)) = 0 := by
  have h : ∑ s, pr s * (m s * R) = 1 := by
    have e : (∑ s, pr s * (m s * (cfPhiD 0 0 0 / cfPhiD 0 0 0))) * (R / (1 + 0)) =
        ∑ s, pr s * (m s * R) := by
      simp only [cfPhiD, mul_zero, zero_mul, add_zero, div_one, mul_one]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [← e, h196, hμ, sub_zero]
  exact (mm_box_gain_zero_iff pr m R).2 h Δ

/-! ### Proposition 19.1 -/

/-- **Proposition 19.1** (AKMM, p. 586). Consider a deterministic equilibrium of the economy with
financial frictions, `p ≡ 1`, `τ = 0`, `κ = 0`: (19.4) `F_L = w`, (19.8) `u₁w = −u₂`, (19.20),
(19.21), (19.22), the firm's budget with `R̃ = R/(1 + τ)`, the household's budget with
`A = A′ = 1` and the tax `T = B′/R̃ − B′/R`. Then the multiplier is zero, `µ ≡ 0`, and the
allocation `(C, L, K)`, with `R^k = F_K`, `w = F_L` and `I = K′ − (1 − δ)K`, satisfies the
neoclassical growth model's household conditions (14.7)–(14.8) `RMHHFOC`, the firm's
conditions (14.3) `RMFirmFOC` and market clearing (14.4) `RMClear` of Miao Ch. 14. -/
theorem proposition_19_1 {uc un F FK FN : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0)
    (huc : ∀ t, uc (C t) (L t) ≠ 0) (hR : ∀ t, R t ≠ 0)
    (h194 : ∀ t, FN (K t) (L t) = w t)
    (h198 : ∀ t, uc (C t) (L t) * w t = -un (C t) (L t))
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (h1922 : ∀ t, 1 / R t = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    (∀ t, μ t = 0) ∧
    RMHHFOC uc un β δ C L (fun t => FK (K t) (L t)) w ∧
    RMFirmFOC FK FN 1 K L (fun t => FK (K t) (L t)) w ∧
    RMClear F 1 1 δ C (fun t => K (t + 1) - (1 - δ) * K t) L K C
      (fun t => K (t + 1) - (1 - δ) * K t) L K := by
  subst hτ hκ
  have hq : ∀ d, cfPhiD 0 φ d = 1 := fun d => by simp [cfPhiD]
  have hμ : ∀ t, μ t = 0 := by
    intro t
    have h := h1921 t
    rw [hq, hq, div_one, mul_one, ← h1922 t] at h
    have hR' := hR t
    field_simp at h
    linarith
  refine ⟨hμ, fun t => ⟨?_, ?_⟩, fun t => ⟨by simp, by simp [h194 t]⟩, fun t => ?_⟩
  · have h := h1920 t
    rw [hμ, hq, hq] at h
    have hu := huc t
    field_simp at h
    linarith
  · rw [← h194 t, div_eq_iff (huc t), ← h198 t, h194 t]
    ring
  · refine ⟨by simp, by simp, by simp, by simp, by ring, ?_⟩
    have := hh_resource (hfirm t) (hhh t) (hT t)
    simp only [one_pow, one_mul]
    linarith

/-- **Proposition 19.1, planner** (AKMM, p. 586–587): if moreover `F` has constant returns
(so `F_K`, `F_L` are homogeneous of degree zero) and `K, L > 0`, the allocation satisfies the
planner's first-order conditions of the neoclassical growth model (Miao, p. 465,
`rm_ce_planner`). -/
theorem proposition_19_1_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0)
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hK : ∀ t, 0 < K t) (hL : ∀ t, 0 < L t)
    (huc : ∀ t, uc (C t) (L t) ≠ 0) (hR : ∀ t, R t ≠ 0)
    (h194 : ∀ t, FN (K t) (L t) = w t)
    (h198 : ∀ t, uc (C t) (L t) * w t = -un (C t) (L t))
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (h1922 : ∀ t, 1 / R t = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    RMPlannerFOC uc un F FK FN β 1 1 δ C (fun t => K (t + 1) - (1 - δ) * K t) L K := by
  obtain ⟨-, h1, h2, h3⟩ := proposition_19_1 hτ hκ huc hR h194 h198 h1920 h1921 h1922 hfirm hhh hT
  exact rm_ce_planner hhom hFK hFN one_pos one_pos hK hL h1 h2 h3

/-- **Proposition 19.1, debt** (AKMM, pp. 586–587): "the equilibrium debt chosen by firms is
indeterminate". With `τ = κ = 0`, take an equilibrium as in `proposition_19_1` and any other
debt path `B̂` with the same initial debt. Paying the dividends `D̂` the firm's budget then
allows, `(C, L, K, D̂, B̂, R, µ)` satisfies every equilibrium condition: (19.20) and (19.21)
do not involve dividends when `κ = 0`, the firm's budget holds by construction and the
household's budget follows from the resource constraint. -/
theorem proposition_19_1_debt {uc F FK : ℝ → ℝ → ℝ} {β δ ξ τ κ φ : ℝ}
    {C L K D B Bh R μ w T : ℕ → ℝ} (hτ : τ = 0) (hκ : κ = 0) (hR : ∀ t, R t ≠ 0)
    (h1920 : ∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))) * ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1))))
    (h1921 : ∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (D t) / cfPhiD κ φ (D (t + 1))))
    (hfirm : ∀ t, F (K t) (L t) - w t * L t + B (t + 1) / (R t / (1 + τ)) =
      B t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (D t))
    (hhh : ∀ t, (D t + 1) * 1 + B t + w t * L t = C t + 1 * 1 + B (t + 1) / R t + T t)
    (hT : ∀ t, T t = B (t + 1) / (R t / (1 + τ)) - B (t + 1) / R t) :
    let Dh : ℕ → ℝ := fun t => F (K t) (L t) - w t * L t + Bh (t + 1) / (R t / (1 + τ)) -
      Bh t - 1 * (K (t + 1) - (1 - δ) * K t)
    let Th : ℕ → ℝ := fun t => Bh (t + 1) / (R t / (1 + τ)) - Bh (t + 1) / R t
    (∀ t, (1 - μ t * ξ) * 1 = β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
      (cfPhiD κ φ (Dh t) / cfPhiD κ φ (Dh (t + 1))) *
        ((1 - δ) * 1 + FK (K (t + 1)) (L (t + 1)))) ∧
    (∀ t, (1 - μ t) * (1 + τ) / R t =
      β * (uc (C (t + 1)) (L (t + 1)) / uc (C t) (L t)) *
        (cfPhiD κ φ (Dh t) / cfPhiD κ φ (Dh (t + 1)))) ∧
    (∀ t, F (K t) (L t) - w t * L t + Bh (t + 1) / (R t / (1 + τ)) =
      Bh t + 1 * (K (t + 1) - (1 - δ) * K t) + cfPhi κ φ (Dh t)) ∧
    (∀ t, (Dh t + 1) * 1 + Bh t + w t * L t = C t + 1 * 1 + Bh (t + 1) / R t + Th t) := by
  intro Dh Th
  subst hτ hκ
  have hq : ∀ d, cfPhiD 0 φ d = 1 := fun d => by simp [cfPhiD]
  have hphi : ∀ d, cfPhi 0 φ d = d := fun d => by simp [cfPhi]
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have e : cfPhiD 0 φ (Dh t) / cfPhiD 0 φ (Dh (t + 1)) =
        cfPhiD 0 φ (D t) / cfPhiD 0 φ (D (t + 1)) := by rw [hq, hq, hq, hq]
    rw [e]
    exact h1920 t
  · have e : cfPhiD 0 φ (Dh t) / cfPhiD 0 φ (Dh (t + 1)) =
        cfPhiD 0 φ (D t) / cfPhiD 0 φ (D (t + 1)) := by rw [hq, hq, hq, hq]
    rw [e]
    exact h1921 t
  · rw [hphi]
    simp only [Dh]
    ring
  · have hres := hh_resource (hfirm t) (hhh t) (hT t)
    have hR' := hR t
    simp only [Dh, Th, add_zero, div_one]
    simp only [add_zero, zero_mul] at hres
    linarith

/-- **Proposition 19.1, indeterminacy** (AKMM, p. 586): with `τ = κ = 0`, `R > 0` and an
equilibrium debt path `B` satisfying the limit `B(t + 1)/R̃ ≤ ξK(t + 1)`, the path that lowers
debt by one unit from date 1 on also satisfies the limit, has the same initial debt, and
differs from `B`: debt is not determined by the equilibrium conditions. -/
theorem proposition_19_1_indeterminate {ξ τ : ℝ} {K B R : ℕ → ℝ} (hτ : τ = 0)
    (hR : ∀ t, 0 < R t) (hlim : ∀ t, B (t + 1) / (R t / (1 + τ)) ≤ ξ * 1 * K (t + 1)) :
    ∃ Bh : ℕ → ℝ, Bh 0 = B 0 ∧ Bh ≠ B ∧
      ∀ t, Bh (t + 1) / (R t / (1 + τ)) ≤ ξ * 1 * K (t + 1) := by
  subst hτ
  refine ⟨fun t => if t = 0 then B 0 else B t - 1, by simp, fun h => ?_, fun t => ?_⟩
  · have := congrFun h 1
    simp at this
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, add_zero, div_one]
    have := hlim t
    simp only [add_zero, div_one] at this
    have hr := hR t
    have : (B (t + 1) - 1) / R t ≤ B (t + 1) / R t :=
      div_le_div_of_nonneg_right (by linarith) hr.le
    linarith

end AKMM.CreditFrictions
