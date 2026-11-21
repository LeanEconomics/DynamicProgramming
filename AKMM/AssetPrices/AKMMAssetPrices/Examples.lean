/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.TwoPeriod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The two examples of §16.4

AKMM, §16.4, pp. 476–477 and p. 480.

* **Example 1** (complete markets, a stock and a bond): `D = [δ₁ 1; δ₂ 1]` with `δ₁ > δ₂`, rank 2
  (`ex1_complete`); the state prices `q = (Dᵀ)⁻¹p = (pˢ − δ₂pᵇ, δ₁pᵇ − pˢ)/(δ₁ − δ₂)`
  (`ex1_statePrices_eq`, `ex1_statePrices_formula`); no arbitrage iff `δ₁pᵇ > pˢ > δ₂pᵇ`
  (`ex1_noArbitrage_iff`), equivalently the returns do not dominate each other
  (`ex1_returns_iff`), and then both prices are positive (`ex1_prices_pos`); every payoff `x` is
  bought by `θ = D⁻¹x` at cost `((pˢ − pᵇδ₂)x₁ + (pᵇδ₁ − pˢ)x₂)/(δ₁ − δ₂)` (`ex1_value`), which is
  positive on nonzero nonnegative `x` (`ex1_value_pos`).
* **Example 2** (incomplete markets, one stock): `D = (δ₁, δ₂)ᵀ` (`ex2_incomplete`); with
  `δ₁ > δ₂ > 0` no arbitrage iff `pˢ > 0` (`ex2_noArbitrage_iff`); with `δ₁ = 2`, `δ₂ = 0.5`,
  `pˢ = 1` the state prices are exactly `q(1) ∈ (0, 0.5)`, `q(2) = 2 − 4q(1)`
  (`ex2_statePrices_iff`); the two agents' subjective state prices `(1/4, 1)` and `(1/3, 2/3)`
  (p. 480) both price the stock at 1 yet differ (`ex2_disagreement`).

Departure: the book writes the bond price in the value map as `p_f`; it is `pᵇ`.
-/

namespace AKMM.AssetPrices

open Matrix

/-- AKMM, p. 476: Example 1's payoff matrix, a stock paying `δ₁, δ₂` and a bond paying 1. -/
def ex1D (δ₁ δ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![δ₁, 1; δ₂, 1]

/-- AKMM, p. 476: Example 1's prices `p = (pˢ, pᵇ)`. -/
def ex1p (ps pb : ℝ) : Fin 2 → ℝ := ![ps, pb]

/-- AKMM, p. 476: `rank D = S = 2` when `δ₁ ≠ δ₂`, so markets are complete. -/
theorem ex1_complete {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) : (ex1D δ₁ δ₂).rank = 2 := by
  have hdet : (ex1D δ₁ δ₂).det = δ₁ - δ₂ := by
    simp [ex1D, det_fin_two_of]
  have hu : IsUnit (ex1D δ₁ δ₂) := by
    rw [isUnit_iff_isUnit_det, hdet]
    exact (sub_ne_zero.2 h).isUnit
  simpa using rank_of_isUnit _ hu

/-- AKMM, p. 476: the state prices of Example 1. -/
noncomputable def ex1q (δ₁ δ₂ ps pb : ℝ) : Fin 2 → ℝ :=
  ![(ps - δ₂ * pb) / (δ₁ - δ₂), (δ₁ * pb - ps) / (δ₁ - δ₂)]

/-- AKMM, p. 476: `q = (Dᵀ)⁻¹p` solves `p = Dᵀq`. -/
theorem ex1_statePrices_formula {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) (ps pb : ℝ) :
    ∀ n, ex1p ps pb n = ∑ s, ex1D δ₁ δ₂ s n * ex1q δ₁ δ₂ ps pb s := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  intro n
  fin_cases n <;> simp [ex1p, ex1D, ex1q, Fin.sum_univ_two] <;> field_simp <;> ring

/-- AKMM, p. 476: any `q` with `p = Dᵀq` is the formula `(pˢ − δ₂pᵇ, δ₁pᵇ − pˢ)/(δ₁ − δ₂)`. -/
theorem ex1_statePrices_eq {δ₁ δ₂ ps pb : ℝ} (h : δ₁ ≠ δ₂) {q : Fin 2 → ℝ}
    (hq : ∀ n, ex1p ps pb n = ∑ s, ex1D δ₁ δ₂ s n * q s) : q = ex1q δ₁ δ₂ ps pb := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  have h0 : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 0
  have h1 : pb = q 0 + q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 1
  funext s
  fin_cases s <;> simp only [ex1q, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> rw [eq_div_iff h', h0, h1] <;> ring

/-- AKMM, p. 476: with `δ₁ > δ₂`, Example 1 has no arbitrage iff `δ₁pᵇ > pˢ > δ₂pᵇ`. -/
theorem ex1_noArbitrage_iff {δ₁ δ₂ : ℝ} (h : δ₂ < δ₁) (ps pb : ℝ) :
    tpNoArbitrage (ex1p ps pb) (ex1D δ₁ δ₂) ↔ δ₂ * pb < ps ∧ ps < δ₁ * pb := by
  have hd : 0 < δ₁ - δ₂ := sub_pos.2 h
  rw [tp_ftap]
  constructor
  · rintro ⟨q, hq⟩
    rw [ex1_statePrices_eq h.ne' hq.2] at hq
    have h0 := hq.1 0
    have h1 := hq.1 1
    simp only [ex1q, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨by linarith [(div_pos_iff_of_pos_right hd).1 h0],
      by linarith [(div_pos_iff_of_pos_right hd).1 h1]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ex1q δ₁ δ₂ ps pb, fun s => ?_, ex1_statePrices_formula h.ne' ps pb⟩
    fin_cases s
    · exact div_pos (by simp; linarith) hd
    · exact div_pos (by simp; linarith) hd

/-- AKMM, p. 476: for positive prices the arbitrage restrictions are that neither return
dominates the other, `δ₁/pˢ > 1/pᵇ > δ₂/pˢ`. -/
theorem ex1_returns_iff {δ₁ δ₂ ps pb : ℝ} (hps : 0 < ps) (hpb : 0 < pb) :
    (δ₂ * pb < ps ∧ ps < δ₁ * pb) ↔ (δ₂ / ps < 1 / pb ∧ 1 / pb < δ₁ / ps) := by
  rw [div_lt_div_iff₀ hps hpb, div_lt_div_iff₀ hpb hps]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- AKMM, p. 476: under no arbitrage both asset prices in Example 1 are positive (the payoffs are
positive). -/
theorem ex1_prices_pos {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ : δ₂ < δ₁) {ps pb : ℝ}
    (h : tpNoArbitrage (ex1p ps pb) (ex1D δ₁ δ₂)) : 0 < ps ∧ 0 < pb := by
  obtain ⟨q, hq0, hq⟩ := (tp_ftap _ _).1 h
  have h0 : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 0
  have h1 : pb = q 0 + q 1 := by simpa [ex1p, ex1D, Fin.sum_univ_two] using hq 1
  have a := hq0 0
  have b := hq0 1
  constructor
  · rw [h0]; nlinarith [mul_pos (hδ₂.trans hδ) a, mul_pos hδ₂ b]
  · rw [h1]; linarith

/-- AKMM, p. 477: the portfolio `θ = D⁻¹x` generating the payoff `x`. -/
noncomputable def ex1θ (δ₁ δ₂ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(x 0 - x 1) / (δ₁ - δ₂), (δ₁ * x 1 - δ₂ * x 0) / (δ₁ - δ₂)]

/-- AKMM, p. 477: every payoff `x ∈ ℝ²` is attained, `Dθ = x`, at the cost
`pᵀθ = pᵀD⁻¹x = ((pˢ − pᵇδ₂)x₁ + (pᵇδ₁ − pˢ)x₂)/(δ₁ − δ₂)`. -/
theorem ex1_value {δ₁ δ₂ : ℝ} (h : δ₁ ≠ δ₂) (ps pb : ℝ) (x : Fin 2 → ℝ) :
    ex1D δ₁ δ₂ *ᵥ ex1θ δ₁ δ₂ x = x ∧
      ex1p ps pb ⬝ᵥ ex1θ δ₁ δ₂ x =
        ((ps - pb * δ₂) * x 0 + (pb * δ₁ - ps) * x 1) / (δ₁ - δ₂) := by
  have h' : δ₁ - δ₂ ≠ 0 := sub_ne_zero.2 h
  refine ⟨funext fun s => ?_, ?_⟩
  · fin_cases s <;> simp [ex1D, ex1θ, mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring
  · simp [ex1p, ex1θ, dotProduct, Fin.sum_univ_two]
    field_simp
    ring

/-- AKMM, p. 477: under the arbitrage conditions the value of every nonnegative nonzero payoff is
strictly positive. -/
theorem ex1_value_pos {δ₁ δ₂ ps pb : ℝ} (h : δ₂ < δ₁) (h1 : δ₂ * pb < ps) (h2 : ps < δ₁ * pb)
    {x : Fin 2 → ℝ} (hx : ∀ s, 0 ≤ x s) (hne : x ≠ 0) :
    0 < ((ps - pb * δ₂) * x 0 + (pb * δ₁ - ps) * x 1) / (δ₁ - δ₂) := by
  have hd : 0 < δ₁ - δ₂ := sub_pos.2 h
  apply div_pos _ hd
  have hx0 := hx 0
  have hx1 := hx 1
  have hor : 0 < x 0 ∨ 0 < x 1 := by
    by_contra hc
    push Not at hc
    apply hne
    funext s
    fin_cases s
    · exact le_antisymm hc.1 hx0
    · exact le_antisymm hc.2 hx1
  rcases hor with h0 | h0
  · nlinarith [mul_nonneg (by linarith : 0 ≤ pb * δ₁ - ps) hx1]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ ps - pb * δ₂) hx0]

/-- AKMM, p. 477: Example 2's payoff matrix, a single stock paying `δ₁, δ₂`. -/
def ex2D (δ₁ δ₂ : ℝ) : Matrix (Fin 2) Unit ℝ := fun s _ => ![δ₁, δ₂] s

/-- AKMM, p. 478: with one asset and two states markets are incomplete. -/
theorem ex2_incomplete (δ₁ δ₂ : ℝ) : ¬ Function.Surjective (ex2D δ₁ δ₂).mulVec :=
  ObstfeldRogoff.InternationalFinancialMarkets.Spanning.not_spans_of_card_lt (by simp)

/-- AKMM, p. 478: with `δ₁ > δ₂ > 0`, no arbitrage requires (and only requires) a positive stock
price. -/
theorem ex2_noArbitrage_iff {δ₁ δ₂ : ℝ} (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (ps : ℝ) :
    tpNoArbitrage (fun _ => ps) (ex2D δ₁ δ₂) ↔ 0 < ps := by
  rw [tp_ftap]
  constructor
  · rintro ⟨q, hq0, hq⟩
    have h : ps = δ₁ * q 0 + δ₂ * q 1 := by simpa [ex2D, Fin.sum_univ_two] using hq ()
    rw [h]
    have := hq0 0
    have := hq0 1
    positivity
  · intro hps
    refine ⟨![ps / (2 * δ₁), ps / (2 * δ₂)], fun s => ?_, fun _ => ?_⟩
    · fin_cases s
      · exact div_pos hps (by positivity)
      · exact div_pos hps (by positivity)
    · simp [ex2D, Fin.sum_univ_two]
      field_simp
      ring

/-- AKMM, p. 478: with `δ₁ = 2`, `δ₂ = 0.5` and `pˢ = 1`, `q` are state prices iff
`q(1) ∈ (0, 0.5)` and `q(2) = 2 − 4q(1)`; in particular they are not unique. -/
theorem ex2_statePrices_iff (q : Fin 2 → ℝ) :
    tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) q ↔
      (0 < q 0 ∧ q 0 < 1 / 2) ∧ q 1 = 2 - 4 * q 0 := by
  constructor
  · rintro ⟨hq0, hq⟩
    have h := hq ()
    simp [ex2D, Fin.sum_univ_two] at h
    have := hq0 1
    refine ⟨⟨hq0 0, by linarith⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, c⟩
    refine ⟨fun s => ?_, fun _ => ?_⟩
    · fin_cases s
      · exact a
      · simp only [Fin.mk_one, c]; linarith
    · simp [ex2D, Fin.sum_univ_two, c]
      ring

/-- AKMM, p. 480: in Example 2 agents `i` and `j` with subjective state prices `qᵢ = (1/4, 1)` and
`qⱼ = (1/3, 2/3)` agree on the stock price `2qᵢ(1) + 0.5qᵢ(2) = 2qⱼ(1) + 0.5qⱼ(2) = 1` but
disagree on the value of consumption in each state. -/
theorem ex2_disagreement :
    tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) ![1 / 4, 1] ∧
      tpStatePrices (fun _ => 1) (ex2D 2 (1 / 2)) ![1 / 3, 2 / 3] ∧
        (![1 / 4, 1] : Fin 2 → ℝ) ≠ ![1 / 3, 2 / 3] := by
  refine ⟨(ex2_statePrices_iff _).2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩,
    (ex2_statePrices_iff _).2 ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, fun h => ?_⟩
  have := congrFun h 0
  norm_num at this

end AKMM.AssetPrices
