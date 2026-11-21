/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RBModel

/-!
# The nonstochastic steady state of the basic RBC model

Miao, §14.2, pp. 473–474, "Steady State" and "Calibration". With `z_t = z̄` constant
(the book takes `z̄ = 1`; a general `z̄ > 0` is used for the permanent TFP shock, p. 484) and
`ρ_k = 1/β − (1 − δ) > 0`:

* The steady-state Euler equation `1 = β(αK^{α−1}N^{1−α} + 1 − δ)` holds iff
  `K/N = (z̄α/ρ_k)^{1/(1−α)}` (`rb_ss_euler`; the book's display with `z̄ = 1`, `rb_ss_KN`).
* Factor prices `R_k = αY/K = α(K/N)^{α−1}`, `w = (1 − α)(K/N)^α` (`rb_ss_prices`);
  `I = δK = δ(K/N)N`, `Y = (K/N)^αN` (`rb_ss_IY_levels`); the ratios `Y/K = ρ_k/α`,
  `I/Y = δα/ρ_k`, `C/Y = 1 − δα/ρ_k` (`rb_ss_ratios`).
* (14.28) `χ = (1 − α)(K/N)^α(1 − N)/C` (`eq_14_28`), in closed form
  `χ = (1 − α)(1 − N)/(N(1 − δα/ρ_k))` (`rb_ss_chi`); the map `N ↦ χ` is a strictly decreasing
  bijection of `(0, 1)` onto `(0, ∞)` with inverse `N = (1 − α)/(1 − α + χs_c)`
  (`rb_ss_N_iff`, `rb_ss_N_mem`, `rb_ss_chi_strictAnti`): "there is a one-to-one mapping between
  `χ` and `N`". For given `χ` the steady state exists and is unique (`rb_ss_exists_unique`).
* Calibration (p. 474): with `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33`, the exact value
  is `χ = 623971/350889 ≈ 1.778` (`rb_calib_chi`); the printed `χ = 1.75` is not what (14.28)
  gives for these parameters (`rb_calib_chi_ne`).
* A permanent TFP change: hours do not depend on `z̄`, and `K`, `Y`, `I`, `C`, `w` scale with
  `z̄^{1/(1−α)}` (`rb_ss_permanent`), so their log changes are `ln z̄/(1 − α)`.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-- `ρ_k = 1/β − (1 − δ)`, the steady-state rental rate. -/
noncomputable def rb_rk (β δ : ℝ) : ℝ := 1 / β - (1 - δ)

/-- The steady-state capital–labour ratio `(z̄α/ρ_k)^{1/(1−α)}` (Miao, p. 473 with `z̄ = 1`). -/
noncomputable def rb_kn (α β δ z : ℝ) : ℝ := (z * α / rb_rk β δ) ^ (1 - α)⁻¹

/-- The steady-state consumption share `s_c = C/Y = 1 − δα/ρ_k`. -/
noncomputable def rb_sc (α β δ : ℝ) : ℝ := 1 - δ * α / rb_rk β δ

theorem rb_rk_pos {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) : 0 < rb_rk β δ := by
  have : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  unfold rb_rk
  linarith

theorem rb_sc_pos {α β δ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 ≤ δ) :
    0 < rb_sc α β δ := by
  have hr := rb_rk_pos hβ0 hβ1 hδ0
  have : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  unfold rb_sc
  rw [sub_pos, div_lt_one hr]
  unfold rb_rk
  nlinarith

theorem rb_sc_lt_one {α β δ : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ) :
    rb_sc α β δ < 1 := by
  have hr := rb_rk_pos hβ0 hβ1 hδ0.le
  unfold rb_sc
  have : 0 < δ * α / rb_rk β δ := by positivity
  linarith

theorem rb_kn_pos {α β δ z : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hz : 0 < z) : 0 < rb_kn α β δ z := by
  have := rb_rk_pos hβ0 hβ1 hδ
  unfold rb_kn
  positivity

theorem rb_kn_pow {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) : rb_kn α β δ z ^ (1 - α) = z * α / rb_rk β δ := by
  have := rb_rk_pos hβ0 hβ1 hδ
  unfold rb_kn
  exact Real.rpow_inv_rpow (by positivity) (by linarith)

/-- Output and marginal products in terms of `K/N`: `MPK = αz(K/N)^{α−1}`. -/
theorem rb_MPK_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α z K N = α * z * (K / N) ^ (α - 1) := by
  rw [rb_MPK, Real.div_rpow hK.le hN.le, show 1 - α = -(α - 1) by ring,
    Real.rpow_neg hN.le]
  field_simp

theorem rb_MPL_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPL α z K N = (1 - α) * z * (K / N) ^ α := by
  rw [rb_MPL, Real.div_rpow hK.le hN.le, Real.rpow_neg hN.le]
  field_simp

theorem rb_Y_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_Y α z K N = z * (K / N) ^ α * N := by
  rw [rb_Y, Real.div_rpow hK.le hN.le, Real.rpow_sub hN, Real.rpow_one]
  have := Real.rpow_pos_of_pos hN α
  field_simp

/-- At the steady-state ratio the marginal product of capital is `ρ_k`. -/
theorem rb_MPK_kn {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    rb_MPK α z (rb_kn α β δ z * N) N = rb_rk β δ := by
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hr := rb_rk_pos hβ0 hβ1 hδ
  rw [rb_MPK_ratio α z (by positivity) hN, mul_div_cancel_right₀ _ hN.ne',
    show α - 1 = -(1 - α) by ring, Real.rpow_neg hk.le, rb_kn_pow hα0 hα1 hβ0 hβ1 hδ hz]
  field_simp

/-- **The steady-state Euler equation** (Miao, p. 473): for `K, N, z̄ > 0`,
`1 = β(αz̄K^{α−1}N^{1−α} + 1 − δ)` iff `K/N = (z̄α/(1/β − (1 − δ)))^{1/(1−α)}`. -/
theorem rb_ss_euler {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    1 = β * (rb_MPK α z K N + 1 - δ) ↔ K / N = rb_kn α β δ z := by
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have hiff : 1 = β * (rb_MPK α z K N + 1 - δ) ↔ rb_MPK α z K N = rb_rk β δ := by
    unfold rb_rk
    constructor
    · intro h
      field_simp
      linarith
    · intro h
      rw [h]
      field_simp
      ring
  rw [hiff]
  constructor
  · intro h
    rw [rb_MPK_ratio α z hK hN, show α - 1 = -(1 - α) by ring,
      Real.rpow_neg (div_pos hK hN).le] at h
    have hp : (K / N) ^ (1 - α) = z * α / rb_rk β δ := by
      have := Real.rpow_pos_of_pos (div_pos hK hN) (1 - α)
      field_simp at h ⊢
      linarith
    unfold rb_kn
    rw [← hp, Real.rpow_rpow_inv (div_pos hK hN).le (by linarith)]
  · intro h
    have hK' : K = rb_kn α β δ z * N := by
      rw [← h]
      field_simp
    rw [hK']
    exact rb_MPK_kn hα0 hα1 hβ0 hβ1 hδ hz hN

/-- Miao, p. 473 (`z̄ = 1`): `K/N = (α/(1/β − (1 − δ)))^{1/(1−α)}`. -/
theorem rb_ss_KN {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (h : 1 = β * (rb_MPK α 1 K N + 1 - δ)) :
    K / N = (α / (1 / β - (1 - δ))) ^ (1 / (1 - α)) := by
  rw [(rb_ss_euler hα0 hα1 hβ0 hβ1 hδ one_pos hK hN).1 h, rb_kn, rb_rk, one_mul]
  simp only [one_div]

/-- Miao, p. 473: the steady-state factor prices `R_k = αY/K = α(K/N)^{α−1}` and
`w = (1 − α)(K/N)^α` (with `z̄ = 1`). -/
theorem rb_ss_prices (α : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α 1 K N = α * rb_Y α 1 K N / K ∧ rb_MPK α 1 K N = α * (K / N) ^ (α - 1) ∧
      rb_MPL α 1 K N = (1 - α) * (K / N) ^ α := by
  refine ⟨rb_MPK_eq α 1 hK, ?_, ?_⟩
  · rw [rb_MPK_ratio α 1 hK hN, mul_one]
  · rw [rb_MPL_ratio α 1 hK hN, mul_one]

/-- Miao, p. 473: `I = δK = δ(K/N)N` (from (14.24)) and `Y = (K/N)^αN` (with `z̄ = 1`). -/
theorem rb_ss_IY_levels (α δ : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    K = (1 - δ) * K + δ * K ∧ δ * K = δ * (K / N) * N ∧ rb_Y α 1 K N = (K / N) ^ α * N := by
  refine ⟨by ring, by field_simp, ?_⟩
  rw [rb_Y_ratio α 1 hK hN, one_mul]

/-- Miao, pp. 473–475: the steady-state great ratios. With `K = (K/N)N` at the steady-state
ratio, `I = δK` and `C = Y − I`: `Y/K = ρ_k/α`, `I/Y = δα/ρ_k`, `C/Y = 1 − δα/ρ_k`, and
`αY/K + 1 − δ = 1/β` (used in the log-linearisation). -/
theorem rb_ss_ratios {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    let K := rb_kn α β δ z * N
    let Y := rb_Y α z K N
    Y / K = rb_rk β δ / α ∧ δ * K / Y = δ * α / rb_rk β δ ∧
      (Y - δ * K) / Y = rb_sc α β δ ∧ α * (Y / K) + 1 - δ = 1 / β := by
  intro K Y
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have hK : 0 < K := mul_pos hk hN
  have hY : 0 < Y := rb_Y_pos hz hK hN
  have hYK : Y / K = rb_rk β δ / α := by
    have h := rb_MPK_kn hα0 hα1 hβ0 hβ1 hδ hz hN
    rw [rb_MPK_eq α z hK] at h
    rw [eq_div_iff hα0.ne', ← h]
    simp only [Y, K]
    ring
  have hKY : K / Y = α / rb_rk β δ := by
    rw [← inv_div, hYK, inv_div]
  refine ⟨hYK, ?_, ?_, ?_⟩
  · rw [mul_div_assoc, hKY]
    ring
  · rw [sub_div, div_self hY.ne', mul_div_assoc, hKY, rb_sc]
    ring
  · rw [hYK, rb_rk]
    field_simp
    ring

/-- Miao, (14.28), p. 473: at the steady state (`z̄ = 1`), (14.27) `χC/(1 − N) = (1 − α)K^αN^{−α}`
is `χ = (1 − α)(K/N)^α(1 − N)/C`. -/
theorem eq_14_28 {α χ : ℝ} {K N C : ℝ} (hK : 0 < K) (hN0 : 0 < N) (hN1 : N < 1) (hC : 0 < C) :
    eq_14_27 α χ 1 K C N ↔ χ = (1 - α) * (K / N) ^ α * (1 - N) / C := by
  rw [eq_14_27, rb_MPL_ratio α 1 hK hN0, mul_one]
  have h1 : 0 < 1 - N := by linarith
  constructor
  · intro h
    field_simp
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- (14.28) in closed form: at the steady state, (14.27) holds iff
`χ = (1 − α)(1 − N)/(N(1 − δα/ρ_k))`. -/
theorem rb_ss_chi {α β δ χ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1) :
    eq_14_27 α χ z (rb_kn α β δ z * N) (rb_Y α z (rb_kn α β δ z * N) N -
        δ * (rb_kn α β δ z * N)) N ↔
      χ = (1 - α) * (1 - N) / (N * rb_sc α β δ) := by
  obtain ⟨-, -, hC, -⟩ := rb_ss_ratios hα0 hα1 hβ0 hβ1 hδ hz hN0
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hK : 0 < rb_kn α β δ z * N := mul_pos hk hN0
  have hY : 0 < rb_Y α z (rb_kn α β δ z * N) N := rb_Y_pos hz hK hN0
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  set Y := rb_Y α z (rb_kn α β δ z * N) N
  have hCe : Y - δ * (rb_kn α β δ z * N) = rb_sc α β δ * Y := by
    rw [← hC]
    field_simp
  rw [eq_14_27, hCe, rb_MPL_eq α z _ hN0]
  have h1 : 0 < 1 - N := by linarith
  rw [div_eq_div_iff h1.ne' hN0.ne', eq_div_iff (mul_pos hN0 hs).ne']
  constructor
  · intro h
    have : (χ * (N * rb_sc α β δ) - (1 - α) * (1 - N)) * Y = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact absurd h' hY.ne'
  · intro h
    linear_combination Y * h

/-- Hours as a function of `χ`: `N(χ) = (1 − α)/(1 − α + χs_c)`. -/
noncomputable def rb_ssN (α β δ χ : ℝ) : ℝ := (1 - α) / (1 - α + χ * rb_sc α β δ)

/-- "A one-to-one mapping between `χ` and `N`" (Miao, p. 473): for `N ∈ (0, 1)`,
`χ = (1 − α)(1 − N)/(Ns_c)` iff `N = (1 − α)/(1 − α + χs_c)`. -/
theorem rb_ss_N_iff {α β δ χ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hχ : 0 ≤ χ) {N : ℝ} (hN0 : 0 < N) :
    χ = (1 - α) * (1 - N) / (N * rb_sc α β δ) ↔ N = rb_ssN α β δ χ := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hd : 0 < 1 - α + χ * rb_sc α β δ := by nlinarith
  have h1α : 0 < 1 - α := by linarith
  unfold rb_ssN
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

theorem rb_ss_N_mem {α β δ χ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hχ : 0 < χ) : 0 < rb_ssN α β δ χ ∧ rb_ssN α β δ χ < 1 := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hcs := mul_pos hχ hs
  unfold rb_ssN
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- The map `N ↦ χ = (1 − α)(1 − N)/(Ns_c)` is strictly decreasing on `(0, 1)`. -/
theorem rb_ss_chi_strictAnti {α β δ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) :
    StrictAntiOn (fun N => (1 - α) * (1 - N) / (N * rb_sc α β δ)) (Set.Ioo 0 1) := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  intro a ha b hb hab
  simp only
  rw [div_lt_div_iff₀ (mul_pos hb.1 hs) (mul_pos ha.1 hs)]
  have h1 : 0 < 1 - α := by linarith
  have : (1 - b) * a < (1 - a) * b := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this (mul_pos h1 hs)]

/-- **Existence and uniqueness of the steady state** (Miao, p. 473): for every `χ > 0`
there is exactly one `(K, N)` with `K > 0`, `N ∈ (0, 1)`, satisfying the steady-state Euler
equation and (14.27) with `C = Y − δK > 0`; it is `N = (1 − α)/(1 − α + χs_c)`,
`K = (K/N)N`. -/
theorem rb_ss_exists_unique {α β δ χ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hz : 0 < z) (hχ : 0 < χ) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < 1 ∧ 0 < rb_Y α z p.1 p.2 - δ * p.1 ∧
      1 = β * (rb_MPK α z p.1 p.2 + 1 - δ) ∧
      eq_14_27 α χ z p.1 (rb_Y α z p.1 p.2 - δ * p.1) p.2 := by
  obtain ⟨hN0, hN1⟩ := rb_ss_N_mem hα1 hβ0 hβ1 hδ hχ
  set N := rb_ssN α β δ χ
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hK : 0 < rb_kn α β δ z * N := mul_pos hk hN0
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hCpos : ∀ M, 0 < M → 0 < rb_Y α z (rb_kn α β δ z * M) M - δ * (rb_kn α β δ z * M) :=
    fun M hM => by
      obtain ⟨-, -, hC, -⟩ := rb_ss_ratios hα0 hα1 hβ0 hβ1 hδ hz hM
      have hY : 0 < rb_Y α z (rb_kn α β δ z * M) M := rb_Y_pos hz (mul_pos hk hM) hM
      have : rb_Y α z (rb_kn α β δ z * M) M - δ * (rb_kn α β δ z * M) =
          rb_sc α β δ * rb_Y α z (rb_kn α β δ z * M) M := by
        rw [← hC]; field_simp
      rw [this]
      positivity
  refine ⟨(rb_kn α β δ z * N, N), ⟨hK, hN0, hN1, hCpos N hN0, ?_, ?_⟩, ?_⟩
  · exact (rb_ss_euler hα0 hα1 hβ0 hβ1 hδ hz hK hN0).2 (by field_simp)
  · exact (rb_ss_chi hα0 hα1 hβ0 hβ1 hδ hz hN0 hN1).2
      ((rb_ss_N_iff hα1 hβ0 hβ1 hδ hχ.le hN0).2 rfl)
  · rintro ⟨K', N'⟩ ⟨hK', hN0', hN1', -, he, hf⟩
    simp only at hK' hN0' hN1' he hf
    have hKN := (rb_ss_euler hα0 hα1 hβ0 hβ1 hδ hz hK' hN0').1 he
    have hK'' : K' = rb_kn α β δ z * N' := by rw [← hKN]; field_simp
    subst hK''
    have hNN := (rb_ss_N_iff hα1 hβ0 hβ1 hδ hχ.le hN0').1
      ((rb_ss_chi hα0 hα1 hβ0 hβ1 hδ hz hN0' hN1').1 hf)
    rw [hNN]

/-- **Calibration** (Miao, p. 474): with `α = 0.33`, `β = 0.99`, `δ = 0.025` and `N = 0.33`,
(14.28) gives `χ = (1 − α)(1 − N)/(Ns_c) = 623971/350889`, with `1.77 < χ < 1.78`. -/
theorem rb_calib_chi :
    (1 - 33 / 100) * (1 - 33 / 100) / (33 / 100 * rb_sc (33 / 100) (99 / 100) (1 / 40)) =
      (623971 / 350889 : ℝ) ∧ (1.77 : ℝ) < 623971 / 350889 ∧ (623971 / 350889 : ℝ) < 1.78 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [rb_sc, rb_rk]
  norm_num

/-- Correction to Miao, p. 474: the printed calibrated value `χ = 1.75` is not the value of
(14.28) at the stated parameters `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33`. -/
theorem rb_calib_chi_ne :
    (1 - 33 / 100) * (1 - 33 / 100) / (33 / 100 * rb_sc (33 / 100) (99 / 100) (1 / 40)) ≠
      (1.75 : ℝ) := by
  rw [rb_calib_chi.1]
  norm_num

/-- **A permanent TFP change** (Miao, p. 484): hours in the steady state do not depend on
`z̄` (`rb_ssN` does not involve `z̄`), and the capital–labour ratio scales as
`(K/N)(z̄) = z̄^{1/(1−α)}(K/N)(1)`; hence `K`, `Y`, `I = δK`, `C = s_cY` and `w` all scale with
`z̄^{1/(1−α)}`: their log changes are `ln z̄/(1 − α)`. -/
theorem rb_ss_permanent {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    rb_kn α β δ z = z ^ (1 - α)⁻¹ * rb_kn α β δ 1 ∧
      rb_Y α z (rb_kn α β δ z * N) N = z ^ (1 - α)⁻¹ * rb_Y α 1 (rb_kn α β δ 1 * N) N ∧
      rb_MPL α z (rb_kn α β δ z * N) N = z ^ (1 - α)⁻¹ * rb_MPL α 1 (rb_kn α β δ 1 * N) N ∧
      Real.log (rb_kn α β δ z * N) = Real.log (rb_kn α β δ 1 * N) + Real.log z / (1 - α) := by
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have h1 : 0 < 1 - α := by linarith
  have hk1 := rb_kn_pos hα0 hβ0 hβ1 hδ one_pos
  have hkz := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hkn : rb_kn α β δ z = z ^ (1 - α)⁻¹ * rb_kn α β δ 1 := by
    unfold rb_kn
    rw [one_mul, ← Real.mul_rpow hz.le (by positivity), mul_div_assoc]
  have hzp : 0 < z ^ (1 - α)⁻¹ := Real.rpow_pos_of_pos hz _
  -- `z (z^{1/(1−α)})^α = z^{1/(1−α)}`
  have hza : z * (z ^ (1 - α)⁻¹) ^ α = z ^ (1 - α)⁻¹ := by
    rw [← Real.rpow_mul hz.le]
    conv_lhs => lhs; rw [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    field_simp
    ring
  refine ⟨hkn, ?_, ?_, ?_⟩
  · rw [rb_Y_ratio α z (mul_pos hkz hN) hN, rb_Y_ratio α 1 (mul_pos hk1 hN) hN,
      mul_div_cancel_right₀ _ hN.ne', mul_div_cancel_right₀ _ hN.ne', hkn,
      Real.mul_rpow hzp.le hk1.le]
    linear_combination (rb_kn α β δ 1 ^ α * N) * hza
  · rw [rb_MPL_ratio α z (mul_pos hkz hN) hN, rb_MPL_ratio α 1 (mul_pos hk1 hN) hN,
      mul_div_cancel_right₀ _ hN.ne', mul_div_cancel_right₀ _ hN.ne', hkn,
      Real.mul_rpow hzp.le hk1.le]
    linear_combination ((1 - α) * rb_kn α β δ 1 ^ α) * hza
  · rw [hkn, mul_assoc, Real.log_mul hzp.ne' (mul_pos hk1 hN).ne', Real.log_rpow hz]
    ring

end Miao.NeoclassicalGrowth
