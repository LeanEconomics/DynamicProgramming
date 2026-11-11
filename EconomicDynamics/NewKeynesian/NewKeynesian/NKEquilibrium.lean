/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.NKFinalGoods
import NewKeynesian.NKIntermediate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The basic DNK model: aggregation, the Taylor rule and the sticky price equilibrium
(Miao §§19.1.3–19.1.5)

Miao, pp. 621–623. Firms are indexed by a probability space `(J, μ)`; in period `t` the firms in
a measurable set `S` (the non-adjusters, `μ(S) = θ`) keep last period's price and the others
set `P*_t`.

* The law of large numbers used by the book is the hypothesis that the non-adjusters are a
  representative sample of last period's prices: `∫_S f(P^j_{t−1}) dj = θ∫ f(P^j_{t−1}) dj` for
  the relevant `f` (`nk_calvo_avg` is the averaging step). Under it:
  (19.13) `P_t^{1−ε} = θP_{t−1}^{1−ε} + (1 − θ)(P*_t)^{1−ε}` (`eq_19_13`), and
  (19.17) `Δ_t = θΠ_t^{ε/(1−α)}Δ_{t−1} + (1 − θ)(P*_t/P_t)^{−ε/(1−α)}` (`eq_19_17`).
* (19.14), the Taylor rule (`nk_taylorRule`).
* (19.15) `N_t = (Y_t/A_t)^{1/(1−α)}Δ_t` and (19.16) `Y_t = A_tN_t^{1−α}Δ_t^{α−1}`
  (`eq_19_15`, `eq_19_16`), with the price dispersion `Δ_t` (`nk_dispersion`).
* The zero-inflation deterministic steady state used in §19.1.7: with constant `P = P*`,
  `Π = 1`, `Δ = 1`, `1 + i = 1/β`, `MC = 1/μ` and `Y = Y^f`, the Euler equation (19.3), (19.11),
  (19.13), (19.14) and (19.17) hold (`nk_steady_state`, with the steady-state (19.11) computed
  in `nk_reset_constant`: constant inputs and weights `(θβ)^kΛ` give `P* = μMC·P`).
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- The Calvo averaging step (Miao, pp. 621–622): if `g = f` on the set `S` of non-adjusters,
`g = c` off it, `μ(S) = θ` and `∫_S f = θ∫ f` (the law of large numbers), then
`∫ g = θ∫ f + (1 − θ)c`. -/
theorem nk_calvo_avg {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ c : ℝ} (hθ : μ.real S = θ) {f g : J → ℝ}
    (hf : Integrable f μ) (hgS : ∀ j ∈ S, g j = f j) (hgc : ∀ j ∉ S, g j = c)
    (hLLN : ∫ j in S, f j ∂μ = θ * ∫ j, f j ∂μ) :
    ∫ j, g j ∂μ = θ * ∫ j, f j ∂μ + (1 - θ) * c := by
  have h1 : ∫ j in S, g j ∂μ = ∫ j in S, f j ∂μ := setIntegral_congr_fun hS fun j hj => hgS j hj
  have h2 : ∫ j in Sᶜ, g j ∂μ = ∫ _ in Sᶜ, c ∂μ :=
    setIntegral_congr_fun hS.compl fun j hj => hgc j hj
  have hgi : Integrable g μ := by
    have hon1 : IntegrableOn g S μ :=
      (hf.integrableOn).congr_fun (fun j hj => (hgS j hj).symm) hS
    have hon2 : IntegrableOn g Sᶜ μ :=
      (integrableOn_const (C := c)).congr_fun (fun j hj => (hgc j hj).symm) hS.compl
    rw [← integrableOn_univ, ← Set.union_compl_self S]
    exact hon1.union hon2
  rw [← integral_add_compl hS hgi, h1, h2, setIntegral_const, probReal_compl_eq_one_sub hS, hθ,
    hLLN, smul_eq_mul]

/-- **(19.13)** (Miao, p. 621): Calvo price-index dynamics. Prices at `t` are `p₁ = p₀` on the
non-adjusters `S` (`μ(S) = θ`) and `P* > 0` elsewhere; under the law of large numbers
`∫_S p₀^{1−ε} = θ∫ p₀^{1−ε}`, `P_t^{1−ε} = θP_{t−1}^{1−ε} + (1 − θ)(P*)^{1−ε}`. -/
theorem eq_19_13 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε Pstar : ℝ} (hε : 1 < ε) (hθ : μ.real S = θ)
    {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j) (hPs : 0 < Pstar)
    (hI : Integrable (fun j => p₀ j ^ (1 - ε)) μ) (hS1 : ∀ j ∈ S, p₁ j = p₀ j)
    (hSc : ∀ j ∉ S, p₁ j = Pstar)
    (hLLN : ∫ j in S, p₀ j ^ (1 - ε) ∂μ = θ * ∫ j, p₀ j ^ (1 - ε) ∂μ) :
    nk_priceIndex μ ε p₁ ^ (1 - ε) =
      θ * nk_priceIndex μ ε p₀ ^ (1 - ε) + (1 - θ) * Pstar ^ (1 - ε) := by
  have hint := nk_calvo_avg (g := fun j => p₁ j ^ (1 - ε)) (c := Pstar ^ (1 - ε)) hS hθ hI
    (fun j hj => by simp only [hS1 j hj]) (fun j hj => by simp only [hSc j hj]) hLLN
  have hI0 := (nk_integral_rpow_pos hp₀ hI).le
  have hθ0 : 0 ≤ θ := hθ ▸ measureReal_nonneg
  have hθ1 : θ ≤ 1 := hθ ▸ measureReal_le_one
  have hI1 : 0 ≤ ∫ j, p₁ j ^ (1 - ε) ∂μ := by
    rw [hint]
    have := mul_nonneg (sub_nonneg.2 hθ1) (Real.rpow_pos_of_pos hPs (1 - ε)).le
    have := mul_nonneg hθ0 hI0
    linarith
  rw [nk_priceIndex_rpow (by linarith) hI1, nk_priceIndex_rpow (by linarith) hI0, hint]

/-- Miao, p. 622: the price dispersion `Δ_t = ∫ (P^j_t/P_t)^{−ε/(1−α)} dj`. -/
noncomputable def nk_dispersion {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε α : ℝ)
    (p : J → ℝ) (P : ℝ) : ℝ :=
  ∫ j, (p j / P) ^ (-ε / (1 - α)) ∂μ

/-- **(19.15)** (Miao, p. 622): with each firm on its demand curve (19.6) and using the labour
`N^j = (Y^j/A)^{1/(1−α)}` that (19.8) requires, aggregate labour is
`N = ∫ N^j dj = (Y/A)^{1/(1−α)}Δ`. -/
theorem eq_19_15 {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε α A Y P : ℝ}
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) {p : J → ℝ} (hp : ∀ j, 0 < p j) :
    ∫ j, ((p j / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) ∂μ =
      (Y / A) ^ (1 / (1 - α)) * nk_dispersion μ ε α p P := by
  have hpt : ∀ j, ((p j / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) =
      (p j / P) ^ (-ε / (1 - α)) * (Y / A) ^ (1 / (1 - α)) := fun j => by
    have hq := div_pos (hp j) hP
    rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hq.le _) (div_pos hY hA).le,
      ← Real.rpow_mul hq.le]
    congr 2
    ring
  simp only [hpt]
  rw [integral_mul_const, nk_dispersion, mul_comm]

/-- **(19.16)** (Miao, p. 622): from (19.15), `Y = AN^{1−α}Δ^{α−1}` (`A, Y, Δ > 0`, `α < 1`). -/
theorem eq_19_16 {α A Y N Δ : ℝ} (hA : 0 < A) (hY : 0 < Y) (hΔ : 0 < Δ) (hα : α < 1)
    (h15 : N = (Y / A) ^ (1 / (1 - α)) * Δ) : Y = A * N ^ (1 - α) * Δ ^ (α - 1) := by
  have hq := div_pos hY hA
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  rw [h15, Real.mul_rpow (Real.rpow_nonneg hq.le _) hΔ.le, ← Real.rpow_mul hq.le,
    show 1 / (1 - α) * (1 - α) = 1 by field_simp, Real.rpow_one]
  have e : Δ ^ (1 - α) * Δ ^ (α - 1) = 1 := by
    rw [← Real.rpow_add hΔ]
    norm_num
  calc Y = A * (Y / A) * (Δ ^ (1 - α) * Δ ^ (α - 1)) := by rw [e]; field_simp
    _ = A * (Y / A * Δ ^ (1 - α)) * Δ ^ (α - 1) := by ring

/-- **(19.17)** (Miao, p. 622): price-dispersion dynamics. Prices at `t` are `p₁ = p₀` on the
non-adjusters `S` (`μ(S) = θ`) and `P*` elsewhere; under the law of large numbers
`∫_S (p₀/P₀)^{−ε/(1−α)} = θΔ_{t−1}`,
`Δ_t = θΠ_t^{ε/(1−α)}Δ_{t−1} + (1 − θ)(P*/P₁)^{−ε/(1−α)}` with `Π_t = P₁/P₀`. -/
theorem eq_19_17 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε α Pstar P₀ P₁ : ℝ} (hθ : μ.real S = θ)
    (hP₀ : 0 < P₀) (hP₁ : 0 < P₁) {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j)
    (hI : Integrable (fun j => (p₀ j / P₀) ^ (-ε / (1 - α))) μ)
    (hS1 : ∀ j ∈ S, p₁ j = p₀ j) (hSc : ∀ j ∉ S, p₁ j = Pstar)
    (hLLN : ∫ j in S, (p₀ j / P₀) ^ (-ε / (1 - α)) ∂μ = θ * nk_dispersion μ ε α p₀ P₀) :
    nk_dispersion μ ε α p₁ P₁ = θ * (P₁ / P₀) ^ (ε / (1 - α)) * nk_dispersion μ ε α p₀ P₀ +
      (1 - θ) * (Pstar / P₁) ^ (-ε / (1 - α)) := by
  set a := -ε / (1 - α)
  set k := (P₀ / P₁) ^ a
  have hk : k = (P₁ / P₀) ^ (ε / (1 - α)) := by
    simp only [k, a]
    rw [show P₀ / P₁ = (P₁ / P₀)⁻¹ by rw [inv_div], Real.inv_rpow (div_pos hP₁ hP₀).le,
      ← Real.rpow_neg (div_pos hP₁ hP₀).le]
    congr 2
    ring
  have hf : ∀ j, (p₀ j / P₁) ^ a = k * (p₀ j / P₀) ^ a := fun j => by
    simp only [k]
    rw [← Real.mul_rpow (div_pos hP₀ hP₁).le (div_pos (hp₀ j) hP₀).le]
    congr 1
    field_simp
  have hfI : Integrable (fun j => (p₀ j / P₁) ^ a) μ := by
    simp only [hf]
    exact hI.const_mul k
  have hLLN' : ∫ j in S, (p₀ j / P₁) ^ a ∂μ = θ * ∫ j, (p₀ j / P₁) ^ a ∂μ := by
    simp only [hf]
    rw [integral_const_mul, integral_const_mul, hLLN, nk_dispersion]
    ring
  have h := nk_calvo_avg (g := fun j => (p₁ j / P₁) ^ a) (c := (Pstar / P₁) ^ a) hS hθ hfI
    (fun j hj => by simp only [hS1 j hj]) (fun j hj => by simp only [hSc j hj]) hLLN'
  rw [nk_dispersion, h]
  simp only [hf]
  rw [integral_const_mul, ← hk]
  simp only [nk_dispersion, a]
  ring

/-- **(19.14)** (Miao, p. 621), the Taylor rule
`ln((1 + i_t)/(1 + i)) = φ_π ln(P_t/P_{t−1}) + φ_y ln(Y_t/Y^f_t) + v_t`, `i = 1/β − 1`. -/
def nk_taylorRule (φπ φy β i Pt Ptm1 Y Yf v : ℝ) : Prop :=
  Real.log ((1 + i) / (1 + (1 / β - 1))) = φπ * Real.log (Pt / Ptm1) + φy * Real.log (Y / Yf) + v

/-- Miao, p. 624: (19.11) at constant inputs. With weights `w_k = (θβ)^kΛ` (`0 ≤ θβ < 1`,
`Λ, P, Y > 0`, `MC ≠ 0`) and constant `P_k = P`, `Y_k = Y`, `MC_k = MC`, the right side of
(19.11) is `μMC·P`, `μ = ε/(ε − 1)`. -/
theorem nk_reset_constant {θ β Λ ε P Y MC : ℝ} (h0 : 0 ≤ θ * β) (h1 : θ * β < 1) (hΛ : 0 < Λ)
    (hP : 0 < P) (hY : 0 < Y) :
    ε / (ε - 1) * (∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC) /
        ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y = ε / (ε - 1) * MC * P := by
  have hg := tsum_geometric_of_lt_one h0 h1
  have e1 : ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC =
      (∑' k : ℕ, (θ * β) ^ k) * (Λ * P ^ ε * Y * MC) := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by ring
  have e2 : ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y =
      (∑' k : ℕ, (θ * β) ^ k) * (Λ * P ^ (ε - 1) * Y) := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by ring
  have hs : 0 < ∑' k : ℕ, (θ * β) ^ k := by
    rw [hg]
    exact inv_pos.2 (by linarith)
  rw [e1, e2, Real.rpow_sub hP, Real.rpow_one]
  have := Real.rpow_pos_of_pos hP ε
  field_simp

/-- The zero-inflation deterministic steady state (Miao, pp. 621–624). At constant
`C = Y > 0`, `P = P* > 0`, `Π = 1`, `Δ = 1`, `MC`, `1 + i = 1/β` and `Y = Y^f`, `v = 0`:
the Euler equation (19.3) holds, (19.11) holds (with weights `(θβ)^kΛ`) iff `MC = 1/μ`,
(19.13) and (19.17) hold, and the Taylor rule (19.14) holds. -/
theorem nk_steady_state {θ β γ ε α φπ φy Λ P Y MC : ℝ} (hβ : 0 < β) (hθ0 : 0 ≤ θ)
    (hθβ : θ * β < 1) (hε : 1 < ε) (hΛ : 0 < Λ) (hP : 0 < P) (hY : 0 < Y) :
    (1 = β * (1 + (1 / β - 1)) * ((Y / Y) ^ (-γ) * (P / P))) ∧
    (P = ε / (ε - 1) * (∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC) /
        ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y ↔ MC = (ε - 1) / ε) ∧
    (P ^ (1 - ε) = θ * P ^ (1 - ε) + (1 - θ) * P ^ (1 - ε)) ∧
    ((1 : ℝ) = θ * (P / P) ^ (ε / (1 - α)) * 1 + (1 - θ) * (P / P) ^ (-ε / (1 - α))) ∧
    nk_taylorRule φπ φy β (1 / β - 1) P P Y Y 0 := by
  have hPP : P / P = 1 := div_self hP.ne'
  have hYY : Y / Y = 1 := div_self hY.ne'
  refine ⟨?_, ?_, by ring, ?_, ?_⟩
  · rw [hPP, hYY, Real.one_rpow]
    field_simp
    ring
  · rw [nk_reset_constant (mul_nonneg hθ0 hβ.le) hθβ hΛ hP hY]
    have hε0 : ε ≠ 0 := by linarith
    have hε1 : ε - 1 ≠ 0 := by linarith
    constructor
    · intro h
      have h2 : ε / (ε - 1) * MC * P = 1 * P := by rw [one_mul]; exact h.symm
      have h3 := mul_right_cancel₀ hP.ne' h2
      field_simp at h3 ⊢
      linarith
    · intro h
      rw [h]
      field_simp
  · rw [hPP, Real.one_rpow, Real.one_rpow]
    ring
  · have hb : (1 : ℝ) + (1 / β - 1) ≠ 0 := by
      rw [show (1 : ℝ) + (1 / β - 1) = 1 / β by ring]
      positivity
    simp only [nk_taylorRule, hPP, hYY, Real.log_one, mul_zero, add_zero, div_self hb]

end Miao.NewKeynesian
