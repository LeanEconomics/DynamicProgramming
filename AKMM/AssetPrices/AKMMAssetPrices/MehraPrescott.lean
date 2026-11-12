/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.AssetPricing
import StochasticDiscounting.PerronFrobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The equity premium in the Mehra–Prescott economy

AKMM, §16.6, pp. 485–488 (with fns. 4–5). Endowment growth `G ∈ {G_L, G_H}` follows the
symmetric two-state chain `Π = [φ 1−φ; 1−φ φ]`; the stock is a claim to the endowment and the
stochastic discount factor is `M = βG^{−γ}`.

* The symmetric chain has the stationary distribution `(1/2, 1/2)`, the only one when `φ ≠ 1`
  (`mp_stationary_iff`).
* (16.24) in ratio form: `p = vy` turns `pₜ = Eₜ[Mₜ₊₁(yₜ₊₁ + pₜ₊₁)]` into
  `vₜ = Eₜ[βG^{1−γ}ₜ₊₁(1 + vₜ₊₁)]` (`mp_pd_step`).
* With `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}`, when `ρ(βA) < 1`, `v = (I − βA)⁻¹βA𝟙` is the unique solution of
  `v = βA(1 + v)` (`mp_pd_unique`, from Sargent–Stachurski's Exercise 6.3.6, `isPDRatio_iff`) and
  equals the series of fn. 4, `Σ_{t≥1}(βA)ᵗ𝟙` (`mp_pd_series`); `ρ(βA) < 1` holds when every row
  sum of `βA` is below one (`mp_specRad_lt_one`).
* (16.25): `rˢᵢⱼ = Gⱼ(1 + vⱼ)/vᵢ − 1` (`eq_16_25`); (16.26)–(16.27): conditional and
  unconditional expected returns, the bond price `pᶠᵢ = Σⱼ ΠᵢⱼβGⱼ^{−γ}` and the riskless rate
  (`mpCondMean`, `mpUncondMean`, `mp_bond_price`, `mpRf`), and the equity premium
  (`mpEquityPremium`).
* Fn. 5: with `G_L = 1 + μ − δ`, `G_H = 1 + μ + δ` and `π = (1/2, 1/2)`, `E[G] − 1 = μ`,
  `σ²(G) = δ²` and the autocorrelation is `2φ − 1` (`fn5_mean`, `fn5_var`, `fn5_autocorr`).

Departure: (16.25) writes `gⱼ` for the gross growth rate `Gⱼ`. The claim of Figure 16.4 is in
`FigureClaims`.
-/

namespace AKMM.AssetPrices

open Matrix SargentStachurski.StochasticDiscounting

/-- AKMM, p. 486: the symmetric transition matrix `Π = [φ 1−φ; 1−φ φ]`. -/
def mpPi (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![φ, 1 - φ; 1 - φ, φ]

/-- AKMM, p. 486: the stationary distribution `π = Πᵀπ` of the symmetric chain is `(1/2, 1/2)`,
and it is the only one when `φ ≠ 1`. -/
theorem mp_stationary_iff {φ : ℝ} (hφ : φ ≠ 1) (pr : Fin 2 → ℝ) :
    ((mpPi φ)ᵀ *ᵥ pr = pr ∧ pr 0 + pr 1 = 1) ↔ pr = ![1 / 2, 1 / 2] := by
  have h1 : (1 : ℝ) - φ ≠ 0 := sub_ne_zero.2 (Ne.symm hφ)
  constructor
  · rintro ⟨hs, hsum⟩
    have e0 : φ * pr 0 + (1 - φ) * pr 1 = pr 0 := by
      simpa [mpPi, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hs 0
    have hd : (1 - φ) * (pr 1 - pr 0) = 0 := by linarith
    have heq : pr 1 = pr 0 := by
      have := (mul_eq_zero.1 hd).resolve_left h1
      linarith
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨funext fun i => ?_, by norm_num⟩
    fin_cases i <;> simp [mpPi, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- AKMM, (16.24), p. 486: with `pₜ = vₜyₜ`, `yₜ₊₁ = Gₜ₊₁yₜ` and `Mₜ₊₁ = βG^{−γ}ₜ₊₁`,
`Mₜ₊₁(yₜ₊₁ + pₜ₊₁)/yₜ = βG^{1−γ}ₜ₊₁(1 + vₜ₊₁)`. -/
theorem mp_pd_step {β γ G y v' : ℝ} (hG : 0 < G) (hy : 0 < y) :
    β * G ^ (-γ) * (G * y + v' * (G * y)) / y = β * G ^ (1 - γ) * (1 + v') := by
  have e : G ^ (1 - γ) = G ^ (-γ) * G := by
    rw [sub_eq_neg_add, Real.rpow_add hG, Real.rpow_one]
  rw [e]
  field_simp

/-- AKMM, p. 486: the matrix `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}`. -/
noncomputable def mpA (φ γ : ℝ) (G : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => mpPi φ i j * G j ^ (1 - γ)

/-- AKMM, p. 486: when `ρ(βA) < 1`, `v = (I − βA)⁻¹βA𝟙` is the unique solution of
`v = βA(1 + v)` (in finite states every solution is bounded). -/
theorem mp_pd_unique {φ γ β : ℝ} {G : Fin 2 → ℝ} (hρ : specRad (β • mpA φ γ G) < 1)
    (v : Fin 2 → ℝ) :
    v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) ↔
      v = (1 - β • mpA φ γ G)⁻¹ *ᵥ ((β • mpA φ γ G) *ᵥ fun _ => 1) := by
  rw [← isPDRatio_iff hρ, IsPDRatio]
  have : (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) =
      (β • mpA φ γ G) *ᵥ (fun _ => 1) + (β • mpA φ γ G) *ᵥ v := by
    rw [← mulVec_add]
    rfl
  rw [this]

/-- AKMM, fn. 4, p. 486: recursive substitution, `v = Σ_{t≥1}(βA)ᵗ𝟙`. -/
theorem mp_pd_series {φ γ β : ℝ} {G : Fin 2 → ℝ} (hρ : specRad (β • mpA φ γ G) < 1) :
    (1 - β • mpA φ γ G)⁻¹ *ᵥ ((β • mpA φ γ G) *ᵥ fun _ => 1) =
      ∑' t : ℕ, (β • mpA φ γ G) ^ (t + 1) *ᵥ fun _ => (1 : ℝ) :=
  pdRatio_eq_tsum hρ

/-- A sufficient condition for `ρ(βA) < 1`: every row sum `β Σⱼ ΠᵢⱼGⱼ^{1−γ}` is below one. -/
theorem mp_specRad_lt_one {φ γ β : ℝ} {G : Fin 2 → ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hβ : 0 ≤ β) (hG : ∀ j, 0 < G j) {C : ℝ} (hC : C < 1)
    (hrow : ∀ i, ∑ j, β * (mpPi φ i j * G j ^ (1 - γ)) ≤ C) :
    specRad (β • mpA φ γ G) < 1 := by
  refine lt_of_le_of_lt (specRad_le_of_rowsum_le _ (fun i j => ?_) fun i => ?_) hC
  · have hP : 0 ≤ mpPi φ i j := by
      fin_cases i <;> fin_cases j <;> simp [mpPi] <;> linarith
    simp only [Matrix.smul_apply, mpA, Matrix.of_apply, smul_eq_mul]
    exact mul_nonneg hβ (mul_nonneg hP (Real.rpow_pos_of_pos (hG j) _).le)
  · simpa [mpA] using hrow i

/-- AKMM, (16.25), p. 486: with `pᵢ = vᵢy` and `pⱼ' = vⱼGⱼy`, the stock return
`(yₜ₊₁ + pₜ₊₁ − pₜ)/pₜ` from state `i` to state `j` is `Gⱼ(1 + vⱼ)/vᵢ − 1`. -/
theorem eq_16_25 {y Gj vi vj : ℝ} (hy : 0 < y) (hvi : vi ≠ 0) :
    (Gj * y + vj * (Gj * y) - vi * y) / (vi * y) = Gj * (1 + vj) / vi - 1 := by
  field_simp

/-- AKMM, (16.26), p. 487: the conditional expected return `Eᵢ[rˢ] = Σⱼ Πᵢⱼrˢᵢⱼ`. -/
def mpCondMean (P : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ j, P i j * r i j

/-- AKMM, (16.26), p. 487: the unconditional expected return `E[rˢ] = Σᵢ πᵢEᵢ[rˢ]`. -/
def mpUncondMean (pr : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i, pr i * mpCondMean P r i

/-- AKMM, p. 487: the price of the one-period riskless bond, `pᶠᵢ = Eᵢ[M] = Σⱼ ΠᵢⱼβGⱼ^{−γ}`. -/
noncomputable def mpBond (φ β γ : ℝ) (G : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ j, mpPi φ i j * (β * G j ^ (-γ))

/-- AKMM, (16.27), p. 487: the riskless rate `rᶠᵢ = 1/pᶠᵢ − 1`. -/
noncomputable def mpRf (φ β γ : ℝ) (G : Fin 2 → ℝ) (i : Fin 2) : ℝ := 1 / mpBond φ β γ G i - 1

/-- AKMM, p. 487: the unconditional equity premium `E[rˢ] − E[rᶠ]`. -/
noncomputable def mpEquityPremium (φ β γ : ℝ) (G : Fin 2 → ℝ) (r : Fin 2 → Fin 2 → ℝ) : ℝ :=
  mpUncondMean ![1 / 2, 1 / 2] (mpPi φ) r - ∑ i, ![1 / 2, 1 / 2] i * mpRf φ β γ G i

/-- AKMM, p. 487: the bond price in closed form, `pᶠ₁ = β(φG_L^{−γ} + (1 − φ)G_H^{−γ})`,
`pᶠ₂ = β((1 − φ)G_L^{−γ} + φG_H^{−γ})`, and the bond is priced at `E[M]` and its gross return is
`1/pᶠᵢ`. -/
theorem mp_bond_price (φ β γ : ℝ) (G : Fin 2 → ℝ) :
    mpBond φ β γ G 0 = β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ)) ∧
      mpBond φ β γ G 1 = β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)) := by
  constructor <;> simp [mpBond, mpPi, Fin.sum_univ_two] <;> ring

/-- AKMM, fn. 5, p. 487: `E[Gₜ] = π₁G_L + π₂G_H`. -/
def fn5Mean (pr G : Fin 2 → ℝ) : ℝ := ∑ i, pr i * G i

/-- AKMM, fn. 5: `E[Gₜ²]`. -/
def fn5Second (pr G : Fin 2 → ℝ) : ℝ := ∑ i, pr i * G i ^ 2

/-- AKMM, fn. 5: `E[GₜGₜ₋₁] = Σᵢⱼ πᵢΠᵢⱼGᵢGⱼ`. -/
def fn5Cross (pr G : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i, ∑ j, pr i * P i j * G i * G j

/-- The growth states `G_L = 1 + μ − δ`, `G_H = 1 + μ + δ`. -/
def fn5G (μ δ : ℝ) : Fin 2 → ℝ := ![1 + μ - δ, 1 + μ + δ]

/-- AKMM, p. 487 and fn. 5: with the stationary `π = (1/2, 1/2)`, the mean net growth rate is
`E[Gₜ] − 1 = μ`. -/
theorem fn5_mean (μ δ : ℝ) : fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) - 1 = μ := by
  simp [fn5Mean, fn5G, Fin.sum_univ_two]
  ring

/-- AKMM, fn. 5: the variance `σ²(Gₜ − 1) = σ²(Gₜ) = E[Gₜ²] − E[Gₜ]² = δ²`. -/
theorem fn5_var (μ δ : ℝ) :
    fn5Second ![1 / 2, 1 / 2] (fn5G μ δ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2 = δ ^ 2 := by
  simp [fn5Second, fn5Mean, fn5G, Fin.sum_univ_two]
  ring

/-- AKMM, p. 487 and fn. 5: the autocorrelation
`(E[GₜGₜ₋₁] − E[Gₜ]²)/σ²(Gₜ)` of the symmetric chain is `2φ − 1` (so `φ` governs persistence). -/
theorem fn5_autocorr (μ δ φ : ℝ) (hδ : δ ≠ 0) :
    (fn5Cross ![1 / 2, 1 / 2] (fn5G μ δ) (mpPi φ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2) /
      (fn5Second ![1 / 2, 1 / 2] (fn5G μ δ) - fn5Mean ![1 / 2, 1 / 2] (fn5G μ δ) ^ 2) =
      2 * φ - 1 := by
  rw [fn5_var, div_eq_iff (pow_ne_zero 2 hδ)]
  simp [fn5Cross, fn5Mean, fn5G, mpPi, Fin.sum_univ_two]
  ring

end AKMM.AssetPrices
