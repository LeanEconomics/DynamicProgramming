/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Balanced growth in the neoclassical growth model

AKMM, §4.3.3, pp. 113–114. Technology `A_t` grows at rate `γ`, population `L_t` at rate `n`;
`x̃ = X/(AL)`, `f(k) = F(k, 1)` for a constant-returns `F`; utilitarian welfare
`Σ βᵗL_tu(c_t)` with CRRA `u(c) = c^{1−σ}/(1 − σ)`.

* (4.18): `c̃_t = f(k̃_t) + (1 − δ)k̃_t − (1 + γ)(1 + n)k̃_{t+1}` (`eq_4_18`).
* (4.19)–(4.20): `βᵗL_tc_t^{1−σ}/(1 − σ) = β̃ᵗc̃_t^{1−σ}/(1 − σ)` with
  `β̃ = β(1 + n)(1 + γ)^{1−σ}` (`eq_4_19`, `adjustedDiscount`).
* The detrended problem's partial derivatives (`bgp_hasFDerivAt`) and its Euler equation
  `(1 + n)(1 + γ)c̃_t^{−σ} = β̃c̃_{t+1}^{−σ}(f'(k̃_{t+1}) + 1 − δ)` (`bgp_euler_detrended`); written
  with `β` the factor `1 + n` drops out, and it is the Euler equation of per-capita consumption
  `c_t = (1 + γ)ᵗc̃_t` (`bgp_euler_original`).
* The balanced-growth condition `(1 + n)(1 + γ) = β̃(f'(k̃) + 1 − δ)` (`bgp_condition`), which
  for `n = γ = 0` is (4.16) (`bgp_no_growth`), and its Cobb–Douglas solution (`bgp_cobbDouglas`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- **AKMM, (4.18), p. 113.** With constant returns `F(lK, lN) = lF(K, N)` (`l > 0`),
`A_{t+1} = (1 + γ)A_t`, `L_{t+1} = (1 + n)L_t` and `C_t = F(K_t, A_tL_t) + (1 − δ)K_t − K_{t+1}`,
variables per efficiency unit satisfy `c̃_t = f(k̃_t) + (1 − δ)k̃_t − (1 + γ)(1 + n)k̃_{t+1}`. -/
theorem eq_4_18 {F : ℝ → ℝ → ℝ} (hcrs : ∀ l : ℝ, 0 < l → ∀ K N, F (l * K) (l * N) = l * F K N)
    {δ γ n : ℝ} {A L K C : ℕ → ℝ} (hA : ∀ t, A (t + 1) = (1 + γ) * A t)
    (hL : ∀ t, L (t + 1) = (1 + n) * L t) (hpos : ∀ t, 0 < A t * L t)
    (hC : ∀ t, C t = F (K t) (A t * L t) + (1 - δ) * K t - K (t + 1)) (t : ℕ) :
    C t / (A t * L t) = F (K t / (A t * L t)) 1 + (1 - δ) * (K t / (A t * L t)) -
      (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) := by
  have h := hpos t
  have hA0 : A t ≠ 0 := left_ne_zero_of_mul h.ne'
  have hL0 : L t ≠ 0 := right_ne_zero_of_mul h.ne'
  have hF : F (K t) (A t * L t) = A t * L t * F (K t / (A t * L t)) 1 := by
    rw [← hcrs _ h]
    congr 1
    · field_simp
    · ring
  have hnext : (1 + γ) * (1 + n) * (K (t + 1) / (A (t + 1) * L (t + 1))) =
      K (t + 1) / (A t * L t) := by
    have h1 : 0 < A (t + 1) * L (t + 1) := hpos (t + 1)
    rw [hA, hL] at h1 ⊢
    have h2 : (1 + γ) * (1 + n) ≠ 0 := by
      intro h0
      rw [show (1 + γ) * A t * ((1 + n) * L t) = (1 + γ) * (1 + n) * (A t * L t) by ring,
        h0, zero_mul] at h1
      exact lt_irrefl 0 h1
    have hg : (1 + γ) ≠ 0 := left_ne_zero_of_mul h2
    have hn' : (1 + n) ≠ 0 := right_ne_zero_of_mul h2
    field_simp
  rw [hnext, hC, hF]
  field_simp

/-- AKMM, (4.20), p. 114: the adjusted discount factor `β̃ = β(1 + n)(1 + γ)^{1−σ}`. -/
noncomputable def adjustedDiscount (β n γ σ : ℝ) : ℝ := β * (1 + n) * (1 + γ) ^ (1 - σ)

/-- **AKMM, (4.19), p. 114.** With `L_t = (1 + n)ᵗ`, `A_t = (1 + γ)ᵗ` and per-capita consumption
`c_t = A_tc̃_t`, `βᵗL_tc_t^{1−σ}/(1 − σ) = β̃ᵗc̃_t^{1−σ}/(1 − σ)`. -/
theorem eq_4_19 {β n γ σ c : ℝ} (hγ : 0 < 1 + γ) (hc : 0 ≤ c) (t : ℕ) :
    β ^ t * (1 + n) ^ t * ((1 + γ) ^ t * c) ^ (1 - σ) / (1 - σ) =
      adjustedDiscount β n γ σ ^ t * c ^ (1 - σ) / (1 - σ) := by
  have e : ((1 + γ) ^ t) ^ (1 - σ) = ((1 + γ) ^ (1 - σ)) ^ t := by
    rw [← rpow_natCast, ← rpow_mul hγ.le, mul_comm, rpow_mul hγ.le, rpow_natCast]
  rw [mul_rpow (pow_nonneg hγ.le t) hc, e, adjustedDiscount, mul_pow, mul_pow]
  ring

/-- AKMM, p. 114: the detrended return `u(f(k̃) + (1 − δ)k̃ − (1 + γ)(1 + n)k̃')`, with
`h = f + (1 − δ)·id` and `m = (1 + γ)(1 + n)`, has partial derivatives `F̃₁ = u'(c̃)h'(k̃)` and
`F̃₂ = −mu'(c̃)`. -/
theorem bgp_hasFDerivAt {u h : ℝ → ℝ} {m k k' du dh : ℝ} (hu : HasDerivAt u du (h k - m * k'))
    (hh : HasDerivAt h dh k) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => u (h p.1 - m * p.2)) D (k, k') ∧
      D (1, 0) = du * dh ∧ D (0, 1) = -(m * du) := by
  have hin := (hh.hasFDerivAt.comp (k, k')
    (hasFDerivAt_fst (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ)))).sub
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := ((k, k') : ℝ × ℝ))).const_mul m)
  have hout := hu.hasFDerivAt.comp (k, k') hin
  refine ⟨_, hout, ?_, ?_⟩ <;> simp [mul_comm]

/-- **AKMM, p. 114: the detrended Euler equation.** In terms of the partial derivatives of the
detrended return, `F̃₂(t) + β̃F̃₁(t + 1) = 0` is
`(1 + n)(1 + γ)u'(c̃_t) = β̃u'(c̃_{t+1})(f'(k̃_{t+1}) + 1 − δ)`. -/
theorem bgp_euler_detrended {m βt du0 du1 dh1 : ℝ} :
    -(m * du0) + βt * (du1 * dh1) = 0 ↔ m * du0 = βt * du1 * dh1 := by
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 114: `1 + n` drops out.** For `c̃ > 0`, `1 + γ > 0`, `1 + n > 0`, the detrended
Euler equation `(1 + n)(1 + γ)c̃_t^{−σ} = β̃c̃_{t+1}^{−σ}R` holds iff per-capita consumption
`c_t = (1 + γ)ᵗc̃_t` satisfies the Euler equation `c_t^{−σ} = βc_{t+1}^{−σ}R` with the original
`β`. -/
theorem bgp_euler_original {β n γ σ R c0 c1 : ℝ} (hγ : 0 < 1 + γ) (hn : 0 < 1 + n)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (t : ℕ) :
    (1 + n) * (1 + γ) * c0 ^ (-σ) = adjustedDiscount β n γ σ * c1 ^ (-σ) * R ↔
      ((1 + γ) ^ t * c0) ^ (-σ) = β * ((1 + γ) ^ (t + 1) * c1) ^ (-σ) * R := by
  set x := (1 + γ) ^ (-σ)
  have hx : 0 < x := rpow_pos_of_pos hγ _
  have hpow : ∀ s : ℕ, ((1 + γ) ^ s) ^ (-σ) = x ^ s := fun s => by
    rw [← rpow_natCast, ← rpow_mul hγ.le, mul_comm, rpow_mul hγ.le, rpow_natCast]
  have hβt : adjustedDiscount β n γ σ = β * (1 + n) * (1 + γ) * x := by
    rw [adjustedDiscount, sub_eq_neg_add, rpow_add hγ, rpow_one]; ring
  rw [mul_rpow (pow_nonneg hγ.le t) hc0.le, mul_rpow (pow_nonneg hγ.le (t + 1)) hc1.le, hpow,
    hpow, hβt, pow_succ]
  have hxt : 0 < x ^ t := pow_pos hx t
  have hm : 0 < (1 + n) * (1 + γ) := mul_pos hn hγ
  constructor <;> intro h
  · have : c0 ^ (-σ) = β * x * c1 ^ (-σ) * R := by
      have := congrArg (fun y => y / ((1 + n) * (1 + γ))) h
      rw [mul_div_cancel_left₀ _ hm.ne'] at this
      rw [this]; field_simp
    rw [this]; ring
  · have : c0 ^ (-σ) = β * x * c1 ^ (-σ) * R := by
      have := congrArg (fun y => y / x ^ t) h
      rw [mul_comm, mul_div_assoc, div_self hxt.ne', mul_one] at this
      rw [this]; field_simp
    rw [this]; ring

/-- **AKMM, p. 114: the balanced-growth condition.** With constant `c̃ > 0`
(`u'(c̃_t) = u'(c̃_{t+1}) ≠ 0`), the detrended Euler equation reduces to
`(1 + n)(1 + γ) = β̃(f'(k̃) + 1 − δ)`. -/
theorem bgp_condition {m βt du dh : ℝ} (hdu : du ≠ 0) (h : m * du = βt * du * dh) :
    m = βt * dh := by
  have : du * (m - βt * dh) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hdu
  · linarith

/-- AKMM, p. 114: with `n = γ = 0`, `β̃ = β` and the balanced-growth condition is (4.16),
`1 = β(f'(k̄) + 1 − δ)`. -/
theorem bgp_no_growth {β σ d : ℝ} :
    adjustedDiscount β 0 0 σ = β ∧
      ((1 + 0) * (1 + 0) = adjustedDiscount β 0 0 σ * d ↔ 1 = β * d) := by
  have : adjustedDiscount β 0 0 σ = β := by simp [adjustedDiscount]
  rw [this]
  exact ⟨rfl, by norm_num⟩

/-- **AKMM, p. 114: Cobb–Douglas balanced growth.** With `f(k) = k^α`, `0 < α < 1`, and
`D = (1 + n)(1 + γ)/β̃ − 1 + δ > 0`, `k̃ = (α/D)^{1/(1−α)}` satisfies the balanced-growth condition
`(1 + n)(1 + γ) = β̃(αk̃^{α−1} + 1 − δ)`. -/
theorem bgp_cobbDouglas {α βt m δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβt : 0 < βt)
    (hD : 0 < m / βt - 1 + δ) :
    m = βt * (α * ((α / (m / βt - 1 + δ)) ^ (1 / (1 - α))) ^ (α - 1) + 1 - δ) := by
  set D := m / βt - 1 + δ
  have hq : 0 < α / D := div_pos hα0 hD
  have hkey : ((α / D) ^ (1 / (1 - α))) ^ (α - 1) = D / α := by
    rw [← rpow_mul hq.le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show (1 - α) ≠ 0 by linarith]; ring, rpow_neg_one, inv_div]
  rw [hkey, mul_div_cancel₀ _ hα0.ne']
  simp only [D]
  field_simp
  ring

end AKMM.DynamicOptimization
