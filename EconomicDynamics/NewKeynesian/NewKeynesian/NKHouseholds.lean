/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The basic DNK model: households (Miao §19.1.1)

Miao, §19.1.1, pp. 616–618. The household has the separable money-in-the-utility period utility
(19.1) `u(C, N, m) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν) + m^{1−ϕ}/(1 − ϕ)`.

* The partial derivatives of (19.1) and the sign conditions `u₁ > 0`, `u₂ < 0`, `u₃ > 0`,
  `u₁₁ < 0`, `u₂₂ < 0`, `u₃₃ < 0` (`nk_u_C`, `nk_u_N`, `nk_u_m`, `nk_u_CC`, `nk_u_NN`, `nk_u_mm`,
  `nk_u_signs`), for `γ, ϕ ≠ 1` (the printed formula is undefined at `γ = 1` or `ϕ = 1`) and
  `χ > 0` (needed for `u₂ < 0`, not stated in the book).
* The satiation assumption "`u₃(·, ·, m) ≤ 0` for `m > m*`" quoted on p. 617 fails for (19.1):
  `u₃ = m^{−ϕ} > 0` everywhere (`nk_u_no_satiation`).
* (19.2) from the first-order conditions for `C_t` and `N_t` (`eq_19_2`).
* (19.3), the consumption Euler equation, from the bond first-order condition; `E_t` is
  Mathlib's conditional expectation `μ[·|ℱ_t]` and the `F_t`-measurable factor `C_t^γP_t` is
  pulled out of it (`eq_19_3`).
* (19.4), the money demand equation, from the money and bond first-order conditions
  (`eq_19_4`); solving it for the money supply (p. 622) needs `i_t > 0`, and then
  `M_{t+1} = P_t(C_t^{−γ}i_t/(1 + i_t))^{−1/ϕ}` (`nk_money_supply`, `nk_money_demand_pos_rate`).

The first-order conditions themselves are listed, not derived, in the book; they are the
hypotheses here (with `Λ_t = C_t^{−γ}` for the `C_t` condition). The transversality conditions
are stated in the book and play no role in the derivations.
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- The period utility (19.1) (Miao, p. 617):
`u(C, N, m) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν) + m^{1−ϕ}/(1 − ϕ)`. -/
noncomputable def nk_u (γ ν ϕ χ C N m : ℝ) : ℝ :=
  C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν) + m ^ (1 - ϕ) / (1 - ϕ)

/-- `d/dx [x^{1−a}/(1 − a)] = x^{−a}` for `x > 0`, `a ≠ 1`. -/
theorem nk_hasDerivAt_pow_div {a x : ℝ} (ha : a ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ (1 - a) / (1 - a)) (x ^ (-a)) x := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h := (Real.hasDerivAt_rpow_const (p := 1 - a) (Or.inl hx.ne')).div_const (1 - a)
  convert h using 1
  rw [show (1 : ℝ) - a - 1 = -a by ring]
  field_simp

/-- (19.1), Miao, p. 617: `u₁ = C^{−γ}`. -/
theorem nk_u_C {γ ν ϕ χ C N m : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun c => nk_u γ ν ϕ χ c N m) (C ^ (-γ)) C := by
  have h := ((nk_hasDerivAt_pow_div hγ hC).sub_const (χ * N ^ (1 + ν) / (1 + ν))).add_const
    (m ^ (1 - ϕ) / (1 - ϕ))
  exact h

/-- (19.1), Miao, p. 617: `u₂ = −χN^ν`. -/
theorem nk_u_N {γ ν ϕ χ C N m : ℝ} (hν : 0 < ν) (hN : 0 < N) :
    HasDerivAt (fun n => nk_u γ ν ϕ χ C n m) (-(χ * N ^ ν)) N := by
  have h1 : (1 : ℝ) + ν ≠ 0 := by linarith
  have hd := ((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)
  have h := (hd.const_sub (C ^ (1 - γ) / (1 - γ))).add_const (m ^ (1 - ϕ) / (1 - ϕ))
  convert h using 1
  · funext n
    simp only [nk_u]
  · rw [show (1 : ℝ) + ν - 1 = ν by ring]
    field_simp

/-- (19.1), Miao, p. 617: `u₃ = m^{−ϕ}`. -/
theorem nk_u_m {γ ν ϕ χ C N m : ℝ} (hϕ : ϕ ≠ 1) (hm : 0 < m) :
    HasDerivAt (fun x => nk_u γ ν ϕ χ C N x) (m ^ (-ϕ)) m := by
  have h := (nk_hasDerivAt_pow_div hϕ hm).const_add
    (C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν))
  exact h

/-- (19.1), Miao, p. 617: `u₁₁ = −γC^{−γ−1}`. -/
theorem nk_u_CC {γ C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun c : ℝ => c ^ (-γ)) (-γ * C ^ (-γ - 1)) C :=
  Real.hasDerivAt_rpow_const (Or.inl hC.ne')

/-- (19.1), Miao, p. 617: `u₂₂ = −χνN^{ν−1}`. -/
theorem nk_u_NN {ν χ N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n : ℝ => -(χ * n ^ ν)) (-(χ * (ν * N ^ (ν - 1)))) N :=
  ((Real.hasDerivAt_rpow_const (Or.inl hN.ne')).const_mul χ).neg

/-- (19.1), Miao, p. 617: `u₃₃ = −ϕm^{−ϕ−1}`. -/
theorem nk_u_mm {ϕ m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x : ℝ => x ^ (-ϕ)) (-ϕ * m ^ (-ϕ - 1)) m :=
  Real.hasDerivAt_rpow_const (Or.inl hm.ne')

/-- Miao, p. 617: the sign conditions `u₁ > 0`, `u₂ < 0`, `u₃ > 0`, `u₁₁ < 0`, `u₂₂ < 0`,
`u₃₃ < 0` hold for (19.1) with `γ, ν, ϕ, χ > 0` at `C, N, m > 0`. -/
theorem nk_u_signs {γ ν ϕ χ C N m : ℝ} (hγ : 0 < γ) (hν : 0 < ν) (hϕ : 0 < ϕ) (hχ : 0 < χ)
    (hC : 0 < C) (hN : 0 < N) (hm : 0 < m) :
    0 < C ^ (-γ) ∧ -(χ * N ^ ν) < 0 ∧ 0 < m ^ (-ϕ) ∧ -γ * C ^ (-γ - 1) < 0 ∧
      -(χ * (ν * N ^ (ν - 1))) < 0 ∧ -ϕ * m ^ (-ϕ - 1) < 0 := by
  have h1 := Real.rpow_pos_of_pos hC (-γ)
  have h2 := Real.rpow_pos_of_pos hN ν
  have h3 := Real.rpow_pos_of_pos hm (-ϕ)
  have h4 := Real.rpow_pos_of_pos hC (-γ - 1)
  have h5 := Real.rpow_pos_of_pos hN (ν - 1)
  have h6 := Real.rpow_pos_of_pos hm (-ϕ - 1)
  refine ⟨h1, ?_, h3, ?_, ?_, ?_⟩
  · have := mul_pos hχ h2
    linarith
  · have := mul_pos hγ h4
    linarith
  · have := mul_pos hχ (mul_pos hν h5)
    linarith
  · have := mul_pos hϕ h6
    linarith

/-- Miao, p. 617: the satiation assumption "there is a finite `m* > 0` with `u₃(·, ·, m) ≤ 0`
for all `m > m*`" fails for the specification (19.1): `u₃ = m^{−ϕ} > 0` for every `m > 0`. -/
theorem nk_u_no_satiation (ϕ : ℝ) : ¬ ∃ mstar : ℝ, 0 < mstar ∧ ∀ m, mstar < m → m ^ (-ϕ) ≤ 0 := by
  rintro ⟨mstar, hms, h⟩
  have := h (mstar + 1) (by linarith)
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < mstar + 1) (-ϕ)
  linarith

/-- **(19.2)** (Miao, p. 618): the first-order conditions `C_t^{−γ} = Λ_t` and
`χN_t^ν = Λ_tW_t/P_t` give `χN_t^ν/C_t^{−γ} = W_t/P_t`. -/
theorem eq_19_2 {γ χ C N W P Λ ν : ℝ} (hC : 0 < C) (hΛ : C ^ (-γ) = Λ)
    (hN : χ * N ^ ν = Λ * (W / P)) : χ * N ^ ν / C ^ (-γ) = W / P := by
  have h := Real.rpow_pos_of_pos hC (-γ)
  rw [hN, ← hΛ]
  field_simp

/-- **(19.3)** (Miao, p. 618), the consumption Euler equation. With `Λ_s = C_s^{−γ}` and the
bond first-order condition `Λ_t/(P_t(1 + i_t)) = E_t[βΛ_{t+1}/P_{t+1}]` (`E_t = μ[·|ℱ_t]`),
`1 = β(1 + i_t)E_t[(C_{t+1}/C_t)^{−γ}P_t/P_{t+1}]` almost surely. The `F_t`-measurability of
`C_t^γP_t` and the integrability of the two integrands are used to pull `C_t^γP_t` out of
`E_t`. -/
theorem eq_19_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {ℱ : MeasurableSpace Ω}
    {β γ : ℝ} {C P i Λ : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ s ω, 0 < C s ω) (hP : ∀ s ω, 0 < P s ω)
    (hi : ∀ ω, 0 < 1 + i t ω) (hΛ : ∀ s ω, Λ s ω = C s ω ^ (-γ))
    (hB : (fun ω => Λ t ω / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ])
    (hmeas : StronglyMeasurable[ℱ] (fun ω => C t ω ^ γ * P t ω))
    (hint1 : Integrable (fun ω => C (t + 1) ω ^ (-γ) / P (t + 1) ω) μ)
    (hint2 : Integrable (fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω)) μ) :
    (fun _ => (1 : ℝ)) =ᵐ[μ] fun ω => β * (1 + i t ω) *
      μ[fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω) | ℱ] ω := by
  set k : Ω → ℝ := fun ω => C t ω ^ γ * P t ω
  set g : Ω → ℝ := fun ω => C (t + 1) ω ^ (-γ) / P (t + 1) ω
  have hkg : (fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω)) = k * g := by
    funext ω
    have h0 := hC t ω
    have h1 := hC (t + 1) ω
    have h2 := hP t ω
    have h3 := hP (t + 1) ω
    simp only [k, g, Pi.mul_apply]
    rw [Real.div_rpow h1.le h0.le, Real.rpow_neg h0.le γ]
    have := Real.rpow_pos_of_pos h0 γ
    field_simp
  have hβg : (fun ω => β * Λ (t + 1) ω / P (t + 1) ω) = β • g := by
    funext ω
    simp only [g, hΛ, Pi.smul_apply, smul_eq_mul]
    ring
  have hpull : μ[k * g | ℱ] =ᵐ[μ] k * μ[g | ℱ] :=
    condExp_mul_of_stronglyMeasurable_left hmeas (by rw [← hkg]; exact hint2) hint1
  have hsm : μ[β • g | ℱ] =ᵐ[μ] β • μ[g | ℱ] := condExp_smul β g ℱ
  rw [hβg] at hB
  rw [hkg]
  filter_upwards [hpull, hsm, hB] with ω h1 h2 h3
  rw [h1]
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2 h3 ⊢
  have e : β * μ[g | ℱ] ω = Λ t ω / (P t ω * (1 + i t ω)) := by rw [h3, h2]
  have hc := hC t ω
  have hp := hP t ω
  have hii := hi ω
  have ec : C t ω ^ γ * C t ω ^ (-γ) = 1 := by
    rw [← Real.rpow_add hc]
    simp
  calc (1 : ℝ) = (1 + i t ω) * (C t ω ^ γ * P t ω) * (Λ t ω / (P t ω * (1 + i t ω))) := by
        rw [hΛ]
        field_simp
        linear_combination -ec
    _ = β * (1 + i t ω) * (k ω * μ[g | ℱ] ω) := by
        rw [← e]
        simp only [k]
        ring

/-- **(19.4)** (Miao, p. 618), the money demand equation. From the money first-order condition
`(M_{t+1}/P_t)^{−ϕ}/P_t − Λ_t/P_t + E_t[βΛ_{t+1}/P_{t+1}] = 0`, the bond first-order condition
and `Λ_t = C_t^{−γ}`: `(M_{t+1}/P_t)^{−ϕ}/C_t^{−γ} = i_t/(1 + i_t)` almost surely. -/
theorem eq_19_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {ℱ : MeasurableSpace Ω}
    {β γ ϕ : ℝ} {C P i Λ M : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω)
    (hi : ∀ ω, 0 < 1 + i t ω) (hΛ : ∀ ω, Λ t ω = C t ω ^ (-γ))
    (hB : (fun ω => Λ t ω / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ])
    (hM : (fun ω => (M (t + 1) ω / P t ω) ^ (-ϕ) / P t ω - Λ t ω / P t ω +
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ] ω) =ᵐ[μ] fun _ => 0) :
    (fun ω => (M (t + 1) ω / P t ω) ^ (-ϕ) / C t ω ^ (-γ)) =ᵐ[μ]
      fun ω => i t ω / (1 + i t ω) := by
  filter_upwards [hB, hM] with ω h1 h2
  rw [← h1] at h2
  have hc := Real.rpow_pos_of_pos (hC ω) (-γ)
  have hp := hP ω
  have hii := hi ω
  rw [hΛ] at h2
  rw [div_eq_div_iff hc.ne' hii.ne']
  have e2 : (M (t + 1) ω / P t ω) ^ (-ϕ) - C t ω ^ (-γ) + C t ω ^ (-γ) / (1 + i t ω) = 0 := by
    have := congrArg (· * P t ω) h2
    simp only [zero_mul] at this
    rw [← this]
    field_simp
  field_simp at e2
  linear_combination e2

/-- Miao, p. 622: (19.4) determines the money supply. For `C_t, P_t, M_{t+1} > 0`, `ϕ > 0` and
`i_t > 0`, (19.4) holds iff `M_{t+1} = P_t(C_t^{−γ}i_t/(1 + i_t))^{−1/ϕ}`. -/
theorem nk_money_supply {γ ϕ C P M i : ℝ} (hϕ : 0 < ϕ) (hC : 0 < C) (hP : 0 < P) (hM : 0 < M)
    (hi : 0 < i) :
    (M / P) ^ (-ϕ) / C ^ (-γ) = i / (1 + i) ↔
      M = P * (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
  have hc := Real.rpow_pos_of_pos hC (-γ)
  have hq : 0 < C ^ (-γ) * (i / (1 + i)) := by positivity
  have hmp : 0 < M / P := div_pos hM hP
  rw [div_eq_iff hc.ne']
  constructor
  · intro h
    have h' : (M / P) ^ (-ϕ) = C ^ (-γ) * (i / (1 + i)) := by rw [h]; ring
    have e : M / P = (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
      rw [← h', ← Real.rpow_mul hmp.le]
      rw [show -ϕ * (-1 / ϕ) = 1 by field_simp, Real.rpow_one]
    rw [← e]
    field_simp
  · intro h
    have e : M / P = (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
      rw [h]
      field_simp
    rw [e, ← Real.rpow_mul hq.le, show -1 / ϕ * -ϕ = 1 by field_simp, Real.rpow_one]
    ring

/-- Miao, pp. 618, 622: a monetary equilibrium needs a positive nominal interest rate. If
`1 + i_t > 0` and `i_t ≤ 0`, (19.4) has no solution `M_{t+1}/P_t > 0`. -/
theorem nk_money_demand_pos_rate {γ ϕ C mreal i : ℝ} (hC : 0 < C) (hm : 0 < mreal)
    (hi1 : 0 < 1 + i) (hi : i ≤ 0) : mreal ^ (-ϕ) / C ^ (-γ) ≠ i / (1 + i) := by
  have h1 : 0 < mreal ^ (-ϕ) / C ^ (-γ) :=
    div_pos (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos hC _)
  have h2 : i / (1 + i) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hi hi1.le
  intro h
  linarith

end Miao.NewKeynesian
