/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.ScalarRE
import DifferenceEquations.Nonsingular

/-!
# The Blanchard–Kahn condition

AKMM, §10.6.1, pp. 278–283.

* One jump variable, (10.18)–(10.20): `y_{t+1} = λy_t` with `λ = 1/φ`; `y_{t+T} = λᵀy_t`; for
  `λ > 1` the only path that does not blow up is `y ≡ 0`, for `0 < λ ≤ 1` every path stays
  bounded (`eq_10_19`, `eq_10_20`, `bk_scalar_indeterminate`).
* With a shock, (10.21)–(10.23), with conditional expectations `E_t` (Miao's `CondExpSystem`):
  `E_t[y_{t+T}] = λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` (`bk_forecast`, fn. 8, and the book's form
  `bk_forecast_book`); for `λ > 1` the forecasts stay bounded iff `y_t = −z_t/(λ − ρ)`
  (`eq_10_23`); for `0 < λ ≤ 1` they stay bounded for every `y_t` (`bk_fn8`), and there are
  many bounded solutions (`bk_indeterminate`). The bounded adapted solution is unique
  (`eq_10_23_unique`, from Miao's (2.3)).
* Guess and verify, (10.24)–(10.25): `A = −1/(λ − ρ)` (`eq_10_25`).
* The general case, (10.26)–(10.31): the transformed system (`eq_10_30`), the solution
  `ỹ_t = ΛΓ₂a_t` of the unstable block (`bk_tilde_solution`), the policy
  `y_t = −H̃₂₂⁻¹H̃₂₁x_t + H̃₂₂⁻¹ΛΓ₂a_t` (`bk_y_solution`) and the law of motion of `x`
  (`bk_x_solution`); and the Blanchard–Kahn condition `h = m` (number of unstable eigenvalues =
  number of jump variables, with `H̃₂₂` invertible) giving a unique non-explosive solution
  (`bk_condition`, Miao's Theorem 1.4.2 for `[x_{t+1}; y_{t+1}] = F[x_t; y_t] + Ga_t`).
-/

namespace AKMM.ComputationalTools

open Finset Miao.RationalExpectations
open scoped Matrix

/-! ### One non-predetermined variable -/

/-- AKMM, (10.18)–(10.19), p. 278: `y_t = φy_{t+1}` with `φ > 0` is `y_{t+1} = λy_t`,
`λ = 1/φ`. -/
theorem eq_10_19 {φ : ℝ} (hφ : 0 < φ) (y y' : ℝ) : y = φ * y' ↔ y' = φ⁻¹ * y := by
  constructor
  · rintro rfl; field_simp
  · rintro rfl; field_simp

/-- AKMM, p. 278: "Applying (10.19) repeatedly, `y_{t+T} = λᵀy_t`". -/
theorem bk_scalar_iterate {lam : ℝ} {y : ℕ → ℝ} (h : ∀ t, y (t + 1) = lam * y t) (t T : ℕ) :
    y (t + T) = lam ^ T * y t := by
  induction T with
  | zero => simp
  | succ T ih => rw [← add_assoc, h, ih, pow_succ]; ring

/-- AKMM, (10.20), p. 278: for `λ > 1` the only path of `y_{t+1} = λy_t` along which `y_{t+T}`
remains bounded is `y_t = 0` for all `t`. -/
theorem eq_10_20 {lam : ℝ} (hl : 1 < lam) {y : ℕ → ℝ} (h : ∀ t, y (t + 1) = lam * y t) :
    (∃ M, ∀ t, |y t| ≤ M) ↔ ∀ t, y t = 0 := by
  constructor
  · rintro ⟨M, hM⟩ t
    by_contra hne
    have hpos : 0 < |y t| := abs_pos.2 hne
    obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt (M / |y t|) hl
    have h1 := hM (t + T)
    rw [bk_scalar_iterate h, abs_mul, abs_of_pos (by positivity : 0 < lam ^ T)] at h1
    rw [div_lt_iff₀ hpos] at hT
    linarith
  · intro h0
    exact ⟨0, fun t => by rw [h0 t, abs_zero]⟩

/-- AKMM, p. 278: "When `λ ≤ 1`, any value of `y_t` is consistent with `lim y_{t+T}` being
finite" (indeterminacy): for `0 < λ ≤ 1` every path is bounded by `|y₀|`. -/
theorem bk_scalar_indeterminate {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1) {y : ℕ → ℝ}
    (h : ∀ t, y (t + 1) = lam * y t) (t : ℕ) : |y t| ≤ |y 0| := by
  have := bk_scalar_iterate h 0 t
  rw [zero_add] at this
  rw [this, abs_mul, abs_of_pos (pow_pos hl0 t)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hl0.le hl1)

/-! ### A jump variable driven by an AR(1) shock -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- AKMM, p. 279 and fn. 8: from (10.21) `E_t[y_{t+1}] = λy_t + z_t` and (10.22)
`E_t[z_{t+1}] = ρz_t`, the law of iterated expectations gives
`E_t[y_{t+T}] = λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` (`λ ≠ ρ`). -/
theorem bk_forecast (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hne : lam ≠ ρ) {y z : ℕ → V}
    (hy : sre_IsAdapted E y) (hz : sre_IsAdapted E z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t T : ℕ) :
    E.E t (y (t + T)) = lam ^ T • y t + ((lam ^ T - ρ ^ T) / (lam - ρ)) • z t := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  induction T with
  | zero => simp [hy t]
  | succ T ih =>
    rw [← add_assoc, ← E.tower_le_apply (Nat.le_add_right t T), h21, map_add, map_smul, ih,
      sre_iter E hz h22 T t, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    congr 1
    · rw [pow_succ, mul_comm]
    · congr 1
      field_simp
      ring

/-- AKMM, p. 279: the printed form `E_t[y_{t+T}] = λᵀ[y_t + (1/λ)(1 + ρ/λ + ⋯ + (ρ/λ)^{T−1})z_t]
= λᵀy_t + (1 − (ρ/λ)ᵀ)/(λ − ρ)·λᵀz_t` agrees with `bk_forecast` (`λ ≠ 0`). -/
theorem bk_forecast_book {lam ρ : ℝ} (hl : lam ≠ 0) (hne : lam ≠ ρ) (T : ℕ) :
    (lam ^ T - ρ ^ T) / (lam - ρ) = lam ^ T * ((1 - (ρ / lam) ^ T) / (lam - ρ)) ∧
      lam ^ T * (1 / lam * ∑ j ∈ range T, (ρ / lam) ^ j) =
        lam ^ T * ((1 - (ρ / lam) ^ T) / (lam - ρ)) := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  have hq : ρ / lam ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hl] at h; exact hne h.symm
  refine ⟨by rw [div_pow]; field_simp, ?_⟩
  rw [geom_sum_eq hq]
  congr 1
  have h1 : ρ / lam - 1 ≠ 0 := sub_ne_zero.2 hq
  field_simp
  ring

/-- AKMM, (10.23), p. 279: for `λ > 1` and `0 ≤ ρ < 1`, the forecasts `E_t[y_{t+T}]` remain
bounded as `T → ∞` exactly when `y_t = −z_t/(λ − ρ)`. -/
theorem eq_10_23 (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hl : 1 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {y z : ℕ → V} (hy : sre_IsAdapted E y) (hz : sre_IsAdapted E z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    (∃ M, ∀ T, ‖E.E t (y (t + T))‖ ≤ M) ↔ y t = -(lam - ρ)⁻¹ • z t := by
  have hd : 0 < lam - ρ := by linarith
  have hform : ∀ T, E.E t (y (t + T)) =
      lam ^ T • (y t + (lam - ρ)⁻¹ • z t) - (ρ ^ T / (lam - ρ)) • z t := by
    intro T
    rw [bk_forecast E (by linarith) hy hz h21 h22, smul_add, smul_smul, sub_div, sub_smul,
      div_eq_mul_inv]
    abel
  have hρT : ∀ T : ℕ, ‖(ρ ^ T / (lam - ρ)) • z t‖ ≤ ‖z t‖ / (lam - ρ) := by
    intro T
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonneg (pow_nonneg hρ0 T)]
    rw [div_mul_eq_mul_div]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le)
  constructor
  · rintro ⟨M, hM⟩
    set w := y t + (lam - ρ)⁻¹ • z t
    have hw : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ := norm_pos_iff.2 hne
      obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((M + ‖z t‖ / (lam - ρ)) / ‖w‖) hl
      have h1 : lam ^ T * ‖w‖ ≤ M + ‖z t‖ / (lam - ρ) := by
        have := hM T
        rw [hform T] at this
        have h2 := norm_sub_norm_le (lam ^ T • w) ((ρ ^ T / (lam - ρ)) • z t)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < lam ^ T)] at h2
        linarith [hρT T]
      rw [div_lt_iff₀ hpos] at hT
      linarith
    have : y t = w - (lam - ρ)⁻¹ • z t := by simp only [w]; abel
    rw [this, hw, zero_sub, neg_smul]
  · intro hyt
    refine ⟨‖z t‖ / (lam - ρ), fun T => ?_⟩
    have hw : y t + (lam - ρ)⁻¹ • z t = 0 := by rw [hyt, neg_smul, neg_add_cancel]
    rw [hform T, hw, smul_zero, zero_sub, norm_neg]
    exact hρT T

/-- AKMM, p. 279, fn. 8: for `0 < λ ≤ 1` (and `0 ≤ ρ < 1`, `λ ≠ ρ`) the forecasts
`λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)·z_t` stay bounded for every value of `y_t` ("indeterminacy"). -/
theorem bk_fn8 (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hne : lam ≠ ρ) {y z : ℕ → V} (hy : sre_IsAdapted E y)
    (hz : sre_IsAdapted E z) (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    ∃ M, ∀ T, ‖E.E t (y (t + T))‖ ≤ M := by
  have hd : 0 < |lam - ρ| := abs_pos.2 (sub_ne_zero.2 hne)
  refine ⟨‖y t‖ + 2 / |lam - ρ| * ‖z t‖, fun T => ?_⟩
  rw [bk_forecast E hne hy hz h21 h22]
  have hl : lam ^ T ≤ 1 := pow_le_one₀ hl0.le hl1
  have hr : ρ ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1.le
  have hlp : 0 ≤ lam ^ T := pow_nonneg hl0.le T
  have hrp : 0 ≤ ρ ^ T := pow_nonneg hρ0 T
  calc ‖lam ^ T • y t + ((lam ^ T - ρ ^ T) / (lam - ρ)) • z t‖
      ≤ ‖lam ^ T • y t‖ + ‖((lam ^ T - ρ ^ T) / (lam - ρ)) • z t‖ := norm_add_le _ _
    _ ≤ ‖y t‖ + 2 / |lam - ρ| * ‖z t‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlp,
          abs_div]
        gcongr
        · exact mul_le_of_le_one_left (norm_nonneg _) hl
        · rw [abs_le]; constructor <;> linarith

/-- AKMM, p. 279: "When `λ ≤ 1`, indeterminacy exists, because many values of `y_t` can keep
`lim E_t[y_{t+T}]` finite": for `|λ| ≤ 1`, adding to any solution `y` of (10.21) the bubble
`λᵗX` (with `X` known at date `0`) gives another solution, bounded if `y` is. -/
theorem bk_indeterminate (E : CondExpSystem ℝ V) {lam : ℝ} (hl : |lam| ≤ 1) {y z : ℕ → V}
    (hy : sre_IsAdapted E y) (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t) {X : V}
    (hX : E.E 0 X = X) :
    sre_IsAdapted E (fun t => y t + lam ^ t • X) ∧
      (∀ t, E.E t (y (t + 1) + lam ^ (t + 1) • X) = lam • (y t + lam ^ t • X) + z t) ∧
      (sre_IsBounded y → sre_IsBounded (fun t => y t + lam ^ t • X)) := by
  have hXt : ∀ t, E.E t X = X := fun t => by
    rw [← hX, E.tower_ge_apply (Nat.zero_le t)]
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · simp only [map_add, map_smul, hy t, hXt t]
  · rw [map_add, map_smul, h21, hXt, smul_add, smul_smul, pow_succ, mul_comm (lam ^ t)]
    abel
  · rintro ⟨M, hM⟩
    refine ⟨M + ‖X‖, fun t => ?_⟩
    refine (norm_add_le _ _).trans (add_le_add (hM t) ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hl)

/-- AKMM, (10.23), p. 279, uniqueness among bounded solutions: for `|λ| > 1`, `|ρ| < |λ|` and a
bounded adapted shock with `E_t[z_{t+1}] = ρz_t`, every bounded adapted solution of (10.21) is
`y_t = −z_t/(λ − ρ)` (Miao's (2.3) and its uniqueness, `eq_2_3_unique`, `sre_fwd_ar1`). -/
theorem eq_10_23_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {lam ρ : ℝ}
    (hl : 1 < |lam|) (hρ : |ρ| < |lam|) {y z : ℕ → V} (hy : sre_IsAdapted E y)
    (hyb : sre_IsBounded y) (hz : sre_IsAdapted E z) (hzb : sre_IsBounded z)
    (h21 : ∀ t, E.E t (y (t + 1)) = lam • y t + z t)
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    y t = -(lam - ρ)⁻¹ • z t := by
  rw [eq_2_3_unique E hl hz hzb hy hyb h21, sre_fwd_ar1 E hρ hz h22 t, neg_inv, neg_sub]

/-- AKMM, (10.24)–(10.25), p. 280 (guess and verify): `y_t = Az_t` solves (10.21) for every
`z_t` iff `Aρ = λA + 1`, i.e. `A = −1/(λ − ρ)`; and then `E_t[Az_{t+1}] = λAz_t + z_t`. -/
theorem eq_10_25 {lam ρ A : ℝ} (hne : lam ≠ ρ) :
    A * ρ = lam * A + 1 ↔ A = -1 / (lam - ρ) := by
  have hd : lam - ρ ≠ 0 := sub_ne_zero.2 hne
  rw [eq_div_iff hd]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 280 ("verify"): with `A = −1/(λ − ρ)`, `y_t = Az_t` satisfies (10.21). -/
theorem eq_10_24_verify (E : CondExpSystem ℝ V) {lam ρ : ℝ} (hne : lam ≠ ρ) {z : ℕ → V}
    (h22 : ∀ t, E.E t (z (t + 1)) = ρ • z t) (t : ℕ) :
    E.E t ((-1 / (lam - ρ)) • z (t + 1)) = lam • ((-1 / (lam - ρ)) • z t) + z t := by
  have hA := (eq_10_25 (A := -1 / (lam - ρ)) hne).2 rfl
  rw [map_smul, h22, smul_smul, smul_smul, hA, add_smul, one_smul]

/-! ### `m` non-predetermined and `n + k` predetermined variables -/

/-- AKMM, (10.28)–(10.30), p. 281: if `F = HJH⁻¹`, multiplying
`[x_{t+1}; E_t y_{t+1}] = F[x_t; y_t] + Ga_t` by `H⁻¹` gives
`H⁻¹[x_{t+1}; E_t y_{t+1}] = JH⁻¹[x_t; y_t] + H⁻¹Ga_t`. -/
theorem eq_10_30 {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι]
    {F H Hinv J : Matrix ι ι ℝ} (G : Matrix ι σ ℝ) (hH : Hinv * H = 1)
    (hF : F = H * J * Hinv) {w w' : ι → ℝ} {a : σ → ℝ} (h : w' = F *ᵥ w + G *ᵥ a) :
    Hinv *ᵥ w' = J *ᵥ (Hinv *ᵥ w) + (Hinv * G) *ᵥ a := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, Matrix.one_mul]

/-- AKMM, p. 282: the unstable block `E_t[ỹ_{t+1}] = J₂ỹ_t + Γ₂a_t`, with `J₂ = diag(λᵢ)` and
`E_t a_{t+1} = ρa_t`, is solved by `ỹ_t = ΛΓ₂a_t` with `Λ = diag(−1/(λᵢ − ρ))`: for every
value `g = Γ₂a_t`, `Λ(ρg) = J₂(Λg) + g`, componentwise (10.23). -/
theorem bk_tilde_solution {κ : Type*} [Fintype κ] [DecidableEq κ] {lamv : κ → ℝ} {ρ : ℝ}
    (hne : ∀ i, lamv i ≠ ρ) (g : κ → ℝ) :
    Matrix.diagonal (fun i => -1 / (lamv i - ρ)) *ᵥ (ρ • g) =
      Matrix.diagonal lamv *ᵥ (Matrix.diagonal (fun i => -1 / (lamv i - ρ)) *ᵥ g) + g := by
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  have hd : lamv i - ρ ≠ 0 := sub_ne_zero.2 (hne i)
  field_simp
  ring

/-- AKMM, p. 283: from `ΛΓ₂a_t = H̃₂₁x_t + H̃₂₂y_t` (10.31) and `H̃₂₂` invertible (left inverse
`Q`), "the solution for `y_t` is `y_t = −H̃₂₂⁻¹H̃₂₁x_t + H̃₂₂⁻¹ΛΓ₂a_t`". -/
theorem bk_y_solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {H21 : Matrix κ ι ℝ}
    {H22 Q : Matrix κ κ ℝ} (hQ : Q * H22 = 1) {x : ι → ℝ} {y r : κ → ℝ}
    (h : r = H21 *ᵥ x + H22 *ᵥ y) : y = -((Q * H21) *ᵥ x) + Q *ᵥ r := by
  rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  abel

/-- AKMM, p. 283: "From (10.28), `x_{t+1} = F₁₁x_t + F₁₂y_t + G₁a_t =
(F₁₁ − F₁₂H̃₂₂⁻¹H̃₂₁)x_t + (G₁ + F₁₂H̃₂₂⁻¹ΛΓ₂)a_t`". -/
theorem bk_x_solution {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    {F11 : Matrix ι ι ℝ} {F12 : Matrix ι κ ℝ} {G1 : Matrix ι σ ℝ} {H21 : Matrix κ ι ℝ}
    {Q : Matrix κ κ ℝ} {LG : Matrix κ σ ℝ} {x x' : ι → ℝ} {y : κ → ℝ} {a : σ → ℝ}
    (hx : x' = F11 *ᵥ x + F12 *ᵥ y + G1 *ᵥ a) (hy : y = -((Q * H21) *ᵥ x) + (Q * LG) *ᵥ a) :
    x' = (F11 - F12 * Q * H21) *ᵥ x + (G1 + F12 * Q * LG) *ᵥ a := by
  rw [hx, hy, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

/-- AKMM, p. 281 (Blanchard and Kahn 1980): "the equilibrium (i.e. the solutions for `x_t` and
`y_t` that don't blow up in the future) is unique if `h = m`". For
`[x_{t+1}; y_{t+1}] = F[x_t; y_t] + Ga_t` (the certainty-equivalent form of (10.28)) with a real
block split of `F` into `n` stable and `h` unstable directions (`P = H⁻¹` with the stable rows
first), `h = m` and `H̃₂₂ = P_{uy}` invertible, there is exactly one bounded solution for every
initial `x₀` and every bounded `a` (Miao's Theorem 1.4.2 with `A = I`). -/
theorem bk_condition {κ υ σ τ m : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ]
    [DecidableEq υ] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Fintype m]
    (F : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (G : Matrix (κ ⊕ υ) m ℝ)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : Miao.DifferenceEquations.IsRealBlockSplit F P R Js Ju)
    (hhm : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (x₀ : κ → ℝ) (a : ℕ → m → ℝ)
    (ha : Miao.DifferenceEquations.IsStableSeq a) :
    ∃! w : ℕ → κ ⊕ υ → ℝ, (∀ t, w (t + 1) = F *ᵥ w t + G *ᵥ a t) ∧ w 0 ∘ Sum.inl = x₀ ∧
      Miao.DifferenceEquations.IsStableSeq w := by
  have hS' : Miao.DifferenceEquations.IsRealBlockSplit ((1 : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ)⁻¹ * F)
      P R Js Ju := by rwa [inv_one, Matrix.one_mul]
  have h := Miao.DifferenceEquations.theorem_1_4_2 1 F G (by simp) hS' hhm Q hQ x₀ a ha
  simpa [Miao.DifferenceEquations.IsSolution, Matrix.one_mulVec] using h

end AKMM.ComputationalTools
