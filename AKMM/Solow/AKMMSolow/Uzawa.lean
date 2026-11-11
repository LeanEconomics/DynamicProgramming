/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import UzawaModern.Growth.Uzawa
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uzawa's theorem in discrete time

AKMM, Appendix 3.A, pp. 825–826 (cited on p. 78): a discrete-time version of Uzawa (1961)
following Schlicht (2006). EconomicGrowth's `UzawaModern` formalises the continuous-time
Jones–Scrimgeour/Schlicht argument with exponential paths; the book's statements are in discrete
time and are proved here, reusing `UzawaModern.Uzawa.rate_eq_of_weighted_moments` (the
weighted-moment identity that identifies growth factors) for the variant with nonnegative
consumption.

* **Theorem .1** (Part I): if every balanced path of the reference technology `F̃₀` is consistent
  with `F̃_t`, then `F̃_t(K, L) = F̃₀(K, A_t L)` with `A_t = ((1 + γ)/(1 + n))^t` (`theorem_3A_1`).
  `A_t` grows at `(1 + γ)/(1 + n) − 1` (`uzawa_technology_growth`), and the labour-augmenting
  factor is unique when `F̃₀` is increasing in labour (`uzawa_technology_unique`).
* **Theorem .2** (Part II): with `K_{t+1} − K_t = I_t − δK_t` (3.A.2), `Y_t = C_t + I_t` (3.A.3),
  constant growth rates and `I_t > 0`, `γ_Y = γ_K` (`theorem_3A_2`). The proof's steps:
  `γ_K = I_t/K_t − δ` (`uzawa_capital_growth`), `γ_I = γ_K` (`uzawa_investment_growth`), and
  (3.A.4) (`eq_3A_4`). Variants: nonnegative consumption, via `UzawaModern`
  (`uzawa_part2_nonneg_consumption`); the constant-saving Solow case (`uzawa_part2_solow`).

**Departures.** (i) Theorem .1 says `A_t` grows at `(1 + γ)(1 + n) − 1`; its own proof gives
`A_t = ((1 + γ)/(1 + n))^t`, a rate of `(1 + γ)/(1 + n) − 1`. The printed rate is false
(`uzawa_printed_rate_counterexample`, with `γ = 0`, `n = 1`). (ii) The proof of Theorem .2 writes
`1 + γ_K = I_t/K_t − δ`; the correct identity is `γ_K = I_t/K_t − δ`
(`uzawa_capital_growth`). (iii) Theorem .2 needs output to be nonzero (so that `γ_Y` is defined
as a ratio); we assume `Y₀ ≠ 0`, and with `Y ≡ 0` the conclusion fails
(`uzawa_part2_zero_output_counterexample`).
-/

namespace AKMM.Solow

/-- **Theorem .1** (Uzawa Theorem, Part I; AKMM, Appendix 3.A, p. 825). Let `F̃₀` have constant
returns on the positive orthant and suppose that for all `Y, K, L > 0` with `Y = F̃₀(K, L)` the
balanced path `Y(1 + γ)^t = F̃_t(K(1 + γ)^t, L(1 + n)^t)` is consistent with `F̃_t` at every `t`.
Then `F̃_t(K_t, L_t) = F̃₀(K_t, A_t L_t)` for all `K_t, L_t > 0`, with `A_t = ((1 + γ)/(1 + n))^t`:
technical progress is labour-augmenting and `F = F̃₀`. -/
theorem theorem_3A_1 {Ft : ℕ → ℝ → ℝ → ℝ} {γ n : ℝ} (hγ : 0 < 1 + γ) (hn : 0 < 1 + n)
    (hcrs : ∀ c K L, 0 < c → 0 < K → 0 < L → Ft 0 (c * K) (c * L) = c * Ft 0 K L)
    (hbg : ∀ Y K L, 0 < K → 0 < L → Y = Ft 0 K L →
      ∀ t : ℕ, Y * (1 + γ) ^ t = Ft t (K * (1 + γ) ^ t) (L * (1 + n) ^ t))
    (t : ℕ) {Kt Lt : ℝ} (hK : 0 < Kt) (hL : 0 < Lt) :
    Ft t Kt Lt = Ft 0 Kt (((1 + γ) / (1 + n)) ^ t * Lt) := by
  have hg : 0 < (1 + γ) ^ t := pow_pos hγ t
  have hnt : 0 < (1 + n) ^ t := pow_pos hn t
  have h := hbg (Ft 0 (Kt / (1 + γ) ^ t) (Lt / (1 + n) ^ t)) (Kt / (1 + γ) ^ t)
    (Lt / (1 + n) ^ t) (div_pos hK hg) (div_pos hL hnt) rfl t
  rw [div_mul_cancel₀ Kt (ne_of_gt hg), div_mul_cancel₀ Lt (ne_of_gt hnt)] at h
  rw [← h, mul_comm, ← hcrs _ _ _ hg (div_pos hK hg) (div_pos hL hnt),
    mul_div_cancel₀ Kt (ne_of_gt hg), div_pow]
  congr 1
  field_simp

/-- AKMM, Appendix 3.A, p. 826, corrected: the labour-augmenting factor of Theorem .1,
`A_t = ((1 + γ)/(1 + n))^t`, has `A₀ = 1` and grows at the constant rate `(1 + γ)/(1 + n) − 1`. -/
theorem uzawa_technology_growth {γ n : ℝ} (t : ℕ) :
    ((1 + γ) / (1 + n)) ^ 0 = 1 ∧
      ((1 + γ) / (1 + n)) ^ (t + 1) = (1 + ((1 + γ) / (1 + n) - 1)) * ((1 + γ) / (1 + n)) ^ t :=
  ⟨pow_zero _, by rw [pow_succ]; ring⟩

/-- AKMM, Appendix 3.A, p. 826 ("`F(K_t, A_t L_t)` completely characterizes `F̃_t`"): if `F̃₀` is
strictly increasing in labour, the labour-augmenting factor in a representation
`F̃_t(K, L) = F̃₀(K, B L)` is unique. -/
theorem uzawa_technology_unique {F0 : ℝ → ℝ → ℝ} {K L A B : ℝ}
    (hmono : StrictMonoOn (F0 K) (Set.Ioi 0)) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (h : F0 K (A * L) = F0 K (B * L)) : A = B := by
  have := hmono.injOn (Set.mem_Ioi.mpr (mul_pos hA hL)) (Set.mem_Ioi.mpr (mul_pos hB hL)) h
  exact mul_right_cancel₀ (ne_of_gt hL) this

/-- AKMM, Appendix 3.A, Theorem .1 as printed ("`A_t` grows at a constant rate
`(1 + γ)(1 + n) − 1`") is false. With `γ = 0`, `n = 1` and `F̃_t(K, L) = K + (1/2)^t L`, the
hypotheses of Theorem .1 hold (`F̃₀ = K + L` has constant returns), but `F̃₁(K, L) ≠ F̃₀(K, 2L)`:
the factor at `t = 1` is `1/2 = (1 + γ)/(1 + n)`, not `2 = (1 + γ)(1 + n)`. -/
theorem uzawa_printed_rate_counterexample :
    ∃ Ft : ℕ → ℝ → ℝ → ℝ,
      (∀ c K L, 0 < c → 0 < K → 0 < L → Ft 0 (c * K) (c * L) = c * Ft 0 K L) ∧
      (∀ Y K L, 0 < K → 0 < L → Y = Ft 0 K L →
        ∀ t : ℕ, Y * (1 + 0) ^ t = Ft t (K * (1 + 0) ^ t) (L * (1 + 1) ^ t)) ∧
      ¬ (∀ K L, 0 < K → 0 < L → Ft 1 K L = Ft 0 K (((1 + 0) * (1 + 1)) ^ 1 * L)) := by
  refine ⟨fun t K L => K + (1 / 2 : ℝ) ^ t * L, fun c K L _ _ _ => by ring,
    fun Y K L _ _ hY t => ?_, fun h => ?_⟩
  · rw [hY]
    have : (1 / 2 : ℝ) ^ t * (L * (1 + 1) ^ t) = L * ((1 / 2) * 2) ^ t := by rw [mul_pow]; ring
    simp only
    rw [this]
    norm_num
  · have := h 1 1 one_pos one_pos
    norm_num at this

/-- AKMM, Appendix 3.A, proof of Theorem .2, corrected: from (3.A.2) and constant capital
growth `K_{t+1} = (1 + γ_K)K_t` with `I_t > 0`, capital is never zero and
`γ_K = I_t/K_t − δ` (printed as `1 + γ_K = I_t/K_t − δ`). -/
theorem uzawa_capital_growth {K I : ℕ → ℝ} {δ γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (t : ℕ) : K t ≠ 0 ∧ γK = I t / K t - δ := by
  have hK : K t ≠ 0 := by
    intro h0
    have := hacc t
    rw [hgK, h0] at this
    linarith [hI t]
  refine ⟨hK, ?_⟩
  have := hacc t
  rw [hgK] at this
  field_simp
  linarith

/-- AKMM, Appendix 3.A, proof of Theorem .2: `I_t/K_t` is constant, so `γ_I = γ_K`. -/
theorem uzawa_investment_growth {K I : ℕ → ℝ} {δ γK γI : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hI : ∀ t, 0 < I t) : γI = γK := by
  have hlev : ∀ t, I t = (γK + δ) * K t := fun t => by
    have := hacc t; rw [hgK] at this; linarith
  have h1 : I 1 = (1 + γK) * I 0 := by rw [hlev 1, hlev 0, hgK 0]; ring
  rw [hgI 0] at h1
  have := mul_right_cancel₀ (ne_of_gt (hI 0)) h1
  linarith

/-- AKMM, (3.A.4), p. 826: subtracting (3.A.3) at `t` from `t + 1` with constant growth rates
gives `γ_C C_t + γ_I I_t = γ_Y Y_t` and `(γ_C − γ_Y)C_t = (γ_Y − γ_I)I_t`. -/
theorem eq_3A_4 {Y C I : ℕ → ℝ} {γY γC γI : ℝ} (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (t : ℕ) :
    γC * C t + γI * I t = γY * Y t ∧ (γC - γY) * C t = (γY - γI) * I t := by
  have h1 := hres (t + 1)
  rw [hgY, hgC, hgI, hres t] at h1
  have h2 : γC * C t + γI * I t = γY * Y t := by rw [hres t]; linarith
  refine ⟨h2, ?_⟩
  rw [hres t] at h2
  linarith

/-- **Theorem .2** (Uzawa Theorem, Part II; AKMM, Appendix 3.A, p. 826). Under (3.A.2) and
(3.A.3), on a path with `I_t > 0` along which `Y_t, C_t, I_t, K_t` grow at constant rates
`γ_Y, γ_C, γ_I, γ_K`, output and capital grow at the same rate: `γ_Y = γ_K` (and `γ_I = γ_K`).
Output is assumed nonzero (`Y₀ ≠ 0`), as the definition of `γ_Y` as a ratio requires. -/
theorem theorem_3A_2 {Y C I K : ℕ → ℝ} {δ γY γC γI γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (hY : Y 0 ≠ 0) : γY = γK ∧ γI = γK := by
  have hIK := uzawa_investment_growth hacc hgK hgI hI
  refine ⟨?_, hIK⟩
  rw [← hIK]
  by_contra hne
  have E0 := (eq_3A_4 hres hgY hgC hgI 0).2
  have E1 := (eq_3A_4 hres hgY hgC hgI 1).2
  rw [hgC 0, hgI 0] at E1
  -- `(γ_Y − γ_I) I₀ ≠ 0`, so `(γ_C − γ_Y) C₀ ≠ 0`
  have hR : (γY - γI) * I 0 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) (ne_of_gt (hI 0))
  have hL : (γC - γY) * C 0 ≠ 0 := E0 ▸ hR
  -- comparing `t = 0` and `t = 1`: `γ_C = γ_I`, i.e. `I_t/C_t` constant
  have hCI : γC = γI := by
    have : (γC - γY) * C 0 * (1 + γC) = (γC - γY) * C 0 * (1 + γI) := by
      calc (γC - γY) * C 0 * (1 + γC) = (γY - γI) * ((1 + γI) * I 0) := by rw [← E1]; ring
        _ = (γY - γI) * I 0 * (1 + γI) := by ring
        _ = (γC - γY) * C 0 * (1 + γI) := by rw [E0]
    have := mul_left_cancel₀ hL this
    linarith
  -- then `(γ_I − γ_Y) Y₀ = 0`, contradicting `Y₀ ≠ 0`
  rw [hCI] at E0
  have : (γI - γY) * Y 0 = 0 := by rw [hres 0]; linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hne (by linarith)
  · exact hY h

/-- AKMM, Appendix 3.A, Theorem .2 with nonnegative consumption (the Jones–Scrimgeour setting):
then no assumption on output is needed, and `γ_Y = γ_I` follows from `UzawaModern`'s
weighted-moment identity `rate_eq_of_weighted_moments` applied to the growth factors. -/
theorem uzawa_part2_nonneg_consumption {Y C I K : ℕ → ℝ} {δ γY γC γI γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hres : ∀ t, Y t = C t + I t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgC : ∀ t, C (t + 1) = (1 + γC) * C t)
    (hgI : ∀ t, I (t + 1) = (1 + γI) * I t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) (hC : 0 ≤ C 0) : γY = γK := by
  have hIK := uzawa_investment_growth hacc hgK hgI hI
  have h1 := hres 1
  rw [hgY, hgC, hgI] at h1
  have h2 := hres 2
  rw [hgY, hgY, hgC, hgC, hgI, hgI] at h2
  have := UzawaModern.Uzawa.rate_eq_of_weighted_moments hC (hI 0) (hres 0)
    (by rw [mul_comm]; linarith : Y 0 * (1 + γY) = C 0 * (1 + γC) + I 0 * (1 + γI))
    (by nlinarith : Y 0 * (1 + γY) ^ 2 = C 0 * (1 + γC) ^ 2 + I 0 * (1 + γI) ^ 2)
  linarith

/-- AKMM, Appendix 3.A, closing remark: in the Solow model `I_t = sY_t`, so
`γ_I = γ_Y` directly and `γ_Y = γ_K`. -/
theorem uzawa_part2_solow {Y I K : ℕ → ℝ} {s δ γY γK : ℝ}
    (hacc : ∀ t, K (t + 1) - K t = I t - δ * K t) (hsave : ∀ t, I t = s * Y t)
    (hgY : ∀ t, Y (t + 1) = (1 + γY) * Y t) (hgK : ∀ t, K (t + 1) = (1 + γK) * K t)
    (hI : ∀ t, 0 < I t) : γY = γK :=
  uzawa_investment_growth hacc hgK (fun t => by rw [hsave, hsave, hgY]; ring) hI

/-- AKMM, Appendix 3.A, Theorem .2 needs `Y ≠ 0`: with `Y_t = 0`, `C_t = −(3/2)2^t`,
`I_t = (3/2)2^t`, `K_t = 2^t` and `δ = 1/2`, (3.A.2), (3.A.3) and the constant-growth conditions
hold with `γ_Y = 0`, `γ_C = γ_I = γ_K = 1` and `I_t > 0`, yet `γ_Y ≠ γ_K`. -/
theorem uzawa_part2_zero_output_counterexample :
    ∃ (Y C I K : ℕ → ℝ) (δ γY γC γI γK : ℝ),
      (∀ t, K (t + 1) - K t = I t - δ * K t) ∧ (∀ t, Y t = C t + I t) ∧
      (∀ t, Y (t + 1) = (1 + γY) * Y t) ∧ (∀ t, C (t + 1) = (1 + γC) * C t) ∧
      (∀ t, I (t + 1) = (1 + γI) * I t) ∧ (∀ t, K (t + 1) = (1 + γK) * K t) ∧
      (∀ t, 0 < I t) ∧ Y 0 = 0 ∧ γY ≠ γK := by
  refine ⟨fun _ => 0, fun t => -(3 / 2 * 2 ^ t), fun t => 3 / 2 * 2 ^ t, fun t => 2 ^ t,
    1 / 2, 0, 1, 1, 1, fun t => ?_, fun t => by ring, fun t => by ring, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t => by positivity, rfl, by norm_num⟩ <;>
  · simp only
    rw [pow_succ]
    ring

end AKMM.Solow
