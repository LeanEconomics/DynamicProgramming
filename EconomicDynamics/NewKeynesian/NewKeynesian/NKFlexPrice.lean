/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.NKIntermediate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The basic DNK model: the flexible price equilibrium (Miao §19.1.6)

Miao, §19.1.6, p. 623, with `μ = ε/(ε − 1)` the desired markup.

* At `θ = 0` the weights `θ^kβ^kΛ_{t+k}` of (19.11) vanish for `k ≥ 1`, and (19.11) becomes
  `P*_t/P_t = μMC^j_t` (`nk_flex_reset`). The book writes "`θ → 0`"; the formula is the value
  at `θ = 0` (the limit is not formalised).
* With symmetric prices `P* = P`: `MC^j = 1/μ`, `Y^j = Y` (`nk_flex_symmetric`), and by (19.9)
  with `Y = AN^{1−α}`, `W/P = (1/μ)(1 − α)AN^{−α}` (`nk_flex_wage`).
* **(19.18)**: with (19.2) and `C = Y = AN^{1−α}`, the labour market clears iff
  `ln N = (ln((1 − α)/(μχ)) + (1 − γ)ln A)/(γ(1 − α) + α + ν)`, and then
  `Y^f = ((1 − α)/(μχ))^{(1−α)/(γ(1−α)+α+ν)}A^{(1+ν)/(γ(1−α)+α+ν)}` (`eq_19_18`): a unique
  flexible-price equilibrium, with output determined by productivity alone.
-/

namespace Miao.NewKeynesian

/-- Miao, p. 623: (19.11) at `θ = 0`. With weights `w_k = 0^k c_k` (`c₀ ≠ 0`), the right side
of (19.11) is `μMC₀P₀`; so the reset price satisfies `P*/P₀ = μMC₀`, a markup over marginal
cost. -/
theorem nk_flex_reset {ε x : ℝ} {c Pk Yk MC : ℕ → ℝ} (hc : c 0 ≠ 0) (hP : 0 < Pk 0)
    (hY : 0 < Yk 0)
    (h11 : x = ε / (ε - 1) * (∑' k, (0 : ℝ) ^ k * c k * Pk k ^ ε * Yk k * MC k) /
      ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ (ε - 1) * Yk k) :
    x / Pk 0 = ε / (ε - 1) * MC 0 := by
  have e1 : ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ ε * Yk k * MC k = c 0 * Pk 0 ^ ε * Yk 0 * MC 0 := by
    rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
    simp
  have e2 : ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ (ε - 1) * Yk k = c 0 * Pk 0 ^ (ε - 1) * Yk 0 := by
    rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
    simp
  rw [h11, e1, e2, Real.rpow_sub hP, Real.rpow_one]
  have := Real.rpow_pos_of_pos hP ε
  field_simp

/-- Miao, p. 623: with flexible prices all firms are symmetric. If `P* = P` and
`P*/P = μMC^j` (`ε > 1`) then `MC^j = 1/μ`, and the demand (19.6) gives `Y^j = Y`. -/
theorem nk_flex_symmetric {ε P MCj Y : ℝ} (hε : 1 < ε) (hP : 0 < P)
    (h : P / P = ε / (ε - 1) * MCj) : MCj = (ε - 1) / ε ∧ (P / P) ^ (-ε) * Y = Y := by
  rw [div_self hP.ne'] at h
  refine ⟨?_, by rw [div_self hP.ne', Real.one_rpow, one_mul]⟩
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp at h ⊢
  linarith

/-- Miao, p. 623: with `MC = 1/μ` and `Y = AN^{1−α}`, (19.9) gives
`W/P = (1/μ)(1 − α)AN^{−α}`. -/
theorem nk_flex_wage {w A α N mu : ℝ} (hA : 0 < A) (hN : 0 < N) (hα : α < 1)
    (h : nk_MCavg w A α (A * N ^ (1 - α)) = 1 / mu) :
    w = 1 / mu * (1 - α) * A * N ^ (-α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have e : (A * N ^ (1 - α) / A) ^ (-α / (1 - α)) = N ^ (-α) := by
    rw [mul_div_cancel_left₀ _ hA.ne', ← Real.rpow_mul hN.le]
    congr 1
    field_simp
  rw [nk_MCavg, e] at h
  have hpos : 0 < A * (1 - α) * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  rw [div_eq_iff hpos.ne'] at h
  rw [h]
  ring

/-- **(19.18)** (Miao, p. 623), the flexible-price (natural) output. With
`D = γ(1 − α) + α + ν > 0`, `α < 1`, `μ, χ, A, N > 0`: the labour-market condition
`χN^ν/C^{−γ} = (1/μ)(1 − α)AN^{−α}` with `C = AN^{1−α}` holds iff
`ln N = (ln((1 − α)/(μχ)) + (1 − γ)ln A)/D`, and then
`AN^{1−α} = ((1 − α)/(μχ))^{(1−α)/D}A^{(1+ν)/D}`. -/
theorem eq_19_18 {γ ν α χ mu A N : ℝ} (hα1 : α < 1) (hχ : 0 < χ)
    (hmu : 0 < mu) (hA : 0 < A) (hN : 0 < N) (hD : 0 < γ * (1 - α) + α + ν) :
    (χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) = 1 / mu * (1 - α) * A * N ^ (-α) ↔
      Real.log N = (Real.log ((1 - α) / (mu * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν)) ∧
    (Real.log N = (Real.log ((1 - α) / (mu * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν) →
      A * N ^ (1 - α) = ((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
        A ^ ((1 + ν) / (γ * (1 - α) + α + ν))) := by
  set D := γ * (1 - α) + α + ν
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have hk : 0 < (1 - α) / (mu * χ) := by positivity
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have hL : 0 < χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) :=
    div_pos (mul_pos hχ (Real.rpow_pos_of_pos hN _)) (Real.rpow_pos_of_pos hY _)
  have hR : 0 < 1 / mu * (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  have logL : Real.log (χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ)) =
      Real.log χ + ν * Real.log N + γ * (Real.log A + (1 - α) * Real.log N) := by
    rw [Real.log_div (mul_pos hχ (Real.rpow_pos_of_pos hN _)).ne'
      (Real.rpow_pos_of_pos hY _).ne', Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hN, Real.log_rpow hY, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hN]
    ring
  have logR : Real.log (1 / mu * (1 - α) * A * N ^ (-α)) =
      -Real.log mu + Real.log (1 - α) + Real.log A - α * Real.log N := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne',
      Real.log_mul (by positivity) hA.ne', Real.log_mul (by positivity) h1p.ne',
      one_div, Real.log_inv, Real.log_rpow hN]
    ring
  have logk : Real.log ((1 - α) / (mu * χ)) = Real.log (1 - α) - Real.log mu - Real.log χ := by
    rw [Real.log_div h1p.ne' (by positivity), Real.log_mul hmu.ne' hχ.ne']
    ring
  refine ⟨?_, ?_⟩
  · rw [← Real.log_injOn_pos.eq_iff hL hR, logL, logR, logk, eq_div_iff hD.ne']
    constructor <;> intro h <;> linarith
  · intro h
    apply Real.log_injOn_pos hY (mul_pos (Real.rpow_pos_of_pos hk _) (Real.rpow_pos_of_pos hA _))
    rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
      Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_rpow hk, Real.log_rpow hA, h]
    field_simp
    ring

end Miao.NewKeynesian
