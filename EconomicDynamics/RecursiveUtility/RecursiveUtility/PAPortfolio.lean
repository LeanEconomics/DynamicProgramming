/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PAEpsteinZin
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Portfolio choice with Epstein–Zin utility: optimality and equilibrium

Miao, *Economic Dynamics in Discrete Time*, §20.4 and §20.4.1 (pp. 711–714).

One node of the event tree (`PAEpsteinZin`): next-period states `s : S` with probabilities `p`.
Wealth `X`, consumption `C = a X`, portfolio return `R_w(s)`, next-period consumption `C'(s)`
and wealth `X'(s) = R_w(s)(X − C)` (20.21).

* (20.21) and the wealth return: `pa_wealthReturn`, `pa_wealthReturn_eq` (with a riskless
  asset, `R_w = R_f + ∑ ψ_i (R_i − R_f)`).
* The Bellman equation under the conjecture `J_{t+1}(X) = A_{t+1} X`: the objective is
  homogeneous of degree one in wealth (`pa_bellman_conjecture`) and so is its supremum
  (`pa_value_homogeneous`), which is the conjecture `J_t(X) = A_t X_t`.
* (20.22): the first-order condition for the consumption–wealth ratio `a`
  (`pa_bellman_hasDerivAt`, `eq_20_22`).
* (20.23)–(20.26): `eq_20_23`, `eq_20_24`, `eq_20_25`, `eq_20_26`.
* The portfolio first-order condition and (20.27)–(20.30): `pa_portfolio_foc`,
  `pa_portfolio_foc_X`, `eq_20_27`, `pa_sum_portfolio_foc`, `eq_20_28`, `eq_20_29`, with the
  kernel `M̄` of (20.30) (`pa_Mbar`).
* (20.31) and `M = M̄` (`eq_20_31`, `pa_M_eq_Mbar`).
* The riskfree rate `R_f = 1/E_t M` and the conditional equity premium
  `E_t R_e − R_f = −Cov_t(R_e, M)/E_t M` (`pa_riskfree_rate`, `pa_equity_premium`).

Departures: none in substance. The first-order conditions are proved as necessary conditions
at a local maximum (the text derives them without discussing sufficiency).
-/

namespace Miao.RecursiveUtility

open Real

/-- Miao, (20.21), p. 711: the portfolio (wealth, market) return `R_w = ∑_i ψ_i R_i`. -/
def pa_wealthReturn {S ι : Type*} [Fintype ι] (ψ : ι → ℝ) (R : ι → S → ℝ) (s : S) : ℝ :=
  ∑ i, ψ i * R i s

/-- Miao, p. 711: with `∑_i ψ_i = 1` and a riskless asset `i₀` (`R_{i₀} ≡ R_f`), the wealth
return is `R_w = R_f + ∑_{i} ψ_i (R_i − R_f)`. -/
theorem pa_wealthReturn_eq {S ι : Type*} [Fintype ι] {ψ : ι → ℝ} (hψ : ∑ i, ψ i = 1)
    (R : ι → S → ℝ) (Rf : ℝ) (s : S) :
    pa_wealthReturn ψ R s = Rf + ∑ i, ψ i * (R i s - Rf) := by
  simp only [pa_wealthReturn, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hψ, one_mul]
  ring

/-- Miao, (20.21), p. 711: the budget constraint `X_{t+1} = R_{w,t+1}(X_t − C_t)`. -/
def pa_nextWealth {S : Type*} (Rw : S → ℝ) (X C : ℝ) (s : S) : ℝ := Rw s * (X - C)

/-- The objective of the Bellman equation of §20.4.1 after substituting the conjecture,
`(1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β Q^{1−ρ}` with `Q = M_t(A_{t+1} R_{w,t+1})`. -/
noncomputable def pa_bellmanInner (β ρ Q a : ℝ) : ℝ :=
  (1 - β) * a ^ (1 - ρ) + (1 - a) ^ (1 - ρ) * (β * Q ^ (1 - ρ))

theorem pa_bellmanInner_pos {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q) (ha0 : 0 < a)
    (ha1 : a < 1) : 0 < pa_bellmanInner β ρ Q a :=
  add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos ha0 _))
    (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (mul_pos hβ0 (Real.rpow_pos_of_pos hQ _)))

/-- Miao, §20.4.1, p. 711: substituting the budget constraint (20.21), `C = a X` and the
conjecture `J_{t+1}(X') = A_{t+1} X'` into the Bellman equation, the objective equals
`X ((1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β (M_t(A_{t+1} R_{w,t+1}))^{1−ρ})^{1/(1−ρ)}`. -/
theorem pa_bellman_conjecture {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {A' Rw : S → ℝ}
    (hA : ∀ s, 0 < A' s) (hR : ∀ s, 0 < Rw s) {X a : ℝ} (hX : 0 < X) (ha0 : 0 < a)
    (ha1 : a < 1) :
    pa_W β ρ (a * X) (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)
      = X * pa_bellmanInner β ρ (pa_CE γ p fun s => A' s * Rw s) a ^ (1 / (1 - ρ)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hQ : 0 ≤ pa_CE γ p fun s => A' s * Rw s :=
    Real.rpow_nonneg (Finset.sum_nonneg fun s _ => mul_nonneg (hp s)
      (Real.rpow_nonneg (mul_pos (hA s) (hR s)).le _)) _
  have hCE : (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)
      = X * ((1 - a) * pa_CE γ p fun s => A' s * Rw s) := by
    rw [← mul_assoc, ← pa_CE_homog hγ hp (by nlinarith) fun s => (mul_pos (hA s) (hR s)).le]
    congr 1
    funext s
    simp only [pa_nextWealth]
    ring
  rw [hCE, mul_comm a X, pa_W_homog hβ0.le hβ1.le hρ hX ha0.le (mul_nonneg (by linarith) hQ)]
  congr 1
  simp only [pa_W, pa_bellmanInner]
  rw [Real.mul_rpow (by linarith) hQ]
  ring_nf

/-- Miao, §20.4.1, p. 711: if `J_{t+1}(X') = A_{t+1} X'`, the value
`J_t(X) = sup_{a, R_w} W(a X, M_t(A_{t+1} R_w (X − a X)))` is linear in wealth,
`J_t(X) = A_t X` with `A_t = J_t(1)`: the conjecture `J_t(X_t) = A_t X_t`. Here `Rset` is
the set of attainable portfolio returns. -/
theorem pa_value_homogeneous {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {A' : S → ℝ}
    (hA : ∀ s, 0 < A' s) (Rset : Set (S → ℝ)) (hR : ∀ Rw ∈ Rset, ∀ s, 0 < Rw s) {X : ℝ}
    (hX : 0 < X) :
    sSup {v | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ Rw ∈ Rset,
        v = pa_W β ρ (a * X) (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)}
      = X * sSup {v | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ Rw ∈ Rset,
        v = pa_W β ρ (a * 1) (pa_CE γ p fun s => A' s * pa_nextWealth Rw 1 (a * 1) s)} := by
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hX.le]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨a, ha, Rw, hRw, rfl⟩
    refine ⟨_, ⟨a, ha, Rw, hRw, rfl⟩, ?_⟩
    rw [pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) hX ha.1 ha.2,
      pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) one_pos ha.1 ha.2, one_mul]
  · rintro ⟨w, ⟨a, ha, Rw, hRw, rfl⟩, rfl⟩
    refine ⟨a, ha, Rw, hRw, ?_⟩
    rw [pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) hX ha.1 ha.2,
      pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) one_pos ha.1 ha.2, one_mul]

/-- Miao, §20.4.1, p. 712: the derivative of the inner objective with respect to `a`,
`(1 − ρ)((1 − β) a^{−ρ} − β Q^{1−ρ} (1 − a)^{−ρ})`. -/
theorem pa_bellmanInner_hasDerivAt {β ρ Q a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (pa_bellmanInner β ρ Q)
      ((1 - ρ) * ((1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ))) a := by
  have e : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have h1 : HasDerivAt (fun a : ℝ => a ^ (1 - ρ)) ((1 - ρ) * a ^ (-ρ)) a := by
    have := Real.hasDerivAt_rpow_const (x := a) (p := 1 - ρ) (Or.inl ha0.ne')
    rwa [e] at this
  have h2 : HasDerivAt (fun a : ℝ => (1 - a) ^ (1 - ρ)) (-1 * (1 - ρ) * (1 - a) ^ (-ρ)) a := by
    have := ((hasDerivAt_id a).const_sub 1).rpow_const (p := 1 - ρ)
      (Or.inl (by simp only [id]; linarith))
    simp only [id] at this
    rwa [e] at this
  have := (h1.const_mul (1 - β)).add (h2.mul_const (β * Q ^ (1 - ρ)))
  convert this using 1
  · funext y
    simp only [pa_bellmanInner, Pi.add_apply]
  · ring

/-- Miao, §20.4.1, p. 712: the derivative of the Bellman objective
`a ↦ ((1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β Q^{1−ρ})^{1/(1−ρ)}`. -/
theorem pa_bellman_hasDerivAt {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun a => pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ)))
      ((1 - ρ) * ((1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ)) * (1 / (1 - ρ))
        * pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ) - 1)) a :=
  (pa_bellmanInner_hasDerivAt ha0 ha1).rpow_const
    (Or.inl (pa_bellmanInner_pos hβ0 hβ1 hQ ha0 ha1).ne')

/-- Miao, (20.22), p. 712: the first-order condition for the consumption–wealth ratio,
`(a/(1 − a))^{−ρ} = β/(1 − β) (M_t(A_{t+1} R_{w,t+1}))^{1−ρ}`, at any interior local maximum
`a ∈ (0, 1)` of the Bellman objective. -/
theorem eq_20_22 {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hQ : 0 < Q)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hmax : IsLocalMax (fun a => pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ))) a) :
    (a / (1 - a)) ^ (-ρ) = β / (1 - β) * Q ^ (1 - ρ) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hd := hmax.hasDerivAt_eq_zero (pa_bellman_hasDerivAt hβ0 hβ1 hQ ha0 ha1)
  have hpos := Real.rpow_pos_of_pos (pa_bellmanInner_pos (ρ := ρ) hβ0 hβ1 hQ ha0 ha1)
    (1 / (1 - ρ) - 1)
  have hk : (1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ) = 0 := by
    rcases mul_eq_zero.1 hd with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h h1
        · exact h
      · simp only [one_div, inv_eq_zero] at h
        exact absurd h h1
    · exact absurd h hpos.ne'
  have hb : (0 : ℝ) < 1 - a := by linarith
  rw [Real.div_rpow ha0.le hb.le]
  have hpa := Real.rpow_pos_of_pos hb (-ρ)
  have hβ' : (1 : ℝ) - β ≠ 0 := by linarith
  rw [div_eq_iff hpa.ne', div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hβ']
  linear_combination hk

/-- Miao, (20.23), p. 712: eliminating the expectation between the Bellman equation and
(20.22), `A_t = (1 − β)^{1/(1−ρ)} a_t^{−ρ/(1−ρ)} = (1 − β)^{1/(1−ρ)} (C_t/X_t)^{−ρ/(1−ρ)}`. -/
theorem eq_20_23 {β ρ Q a : ℝ} (hβ1 : β < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (h22 : (a / (1 - a)) ^ (-ρ) = β / (1 - β) * Q ^ (1 - ρ)) :
    pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ)) = (1 - β) ^ (1 / (1 - ρ)) * a ^ (-ρ / (1 - ρ)) := by
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hQ' : β * Q ^ (1 - ρ) = (1 - β) * (a ^ (-ρ) / (1 - a) ^ (-ρ)) := by
    rw [← Real.div_rpow ha0.le hb.le, h22]
    field_simp
  have hin : pa_bellmanInner β ρ Q a = (1 - β) * a ^ (-ρ) := by
    simp only [pa_bellmanInner]
    rw [hQ', show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add ha0, Real.rpow_add hb,
      Real.rpow_one, Real.rpow_one]
    have := (Real.rpow_pos_of_pos hb (-ρ)).ne'
    field_simp
    ring
  rw [hin, Real.mul_rpow hβ'.le (Real.rpow_nonneg ha0.le _), ← Real.rpow_mul ha0.le]
  ring_nf

/-- Miao, (20.25), p. 712: with `X_t = C_t/a_t`, `X_{t+1} = (X_t − C_t)R_{w,t+1}
= R_{w,t+1} C_t (1 − a_t)/a_t`. -/
theorem eq_20_25 {S : Type*} (Rw : S → ℝ) {X C : ℝ} (hX : 0 < X) (hC : 0 < C) (s : S) :
    pa_nextWealth Rw X C s = Rw s * C * ((1 - C / X) / (C / X)) := by
  simp only [pa_nextWealth]
  field_simp

/-- Miao, (20.23) one period ahead: `A_{t+1} = (1 − β)^{1/(1−ρ)} (C_{t+1}/X_{t+1})^{−ρ/(1−ρ)}`. -/
noncomputable def pa_Anext {S : Type*} (β ρ : ℝ) (C' X' : S → ℝ) (s : S) : ℝ :=
  (1 - β) ^ (1 / (1 - ρ)) * (C' s / X' s) ^ (-ρ / (1 - ρ))

/-- Miao, (20.24), p. 712: substituting (20.23) at `t + 1` into (20.22),
`(a_t/(1 − a_t))^{−ρ}
= β (E_t[(C_{t+1}/X_{t+1})^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{1−γ}])^{(1−ρ)/(1−γ)}`. -/
theorem eq_20_24 {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) {β ρ γ a : ℝ}
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {C' X' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hX' : ∀ s, 0 < X' s) (hR : ∀ s, 0 < Rw s)
    (h22 : (a / (1 - a)) ^ (-ρ)
      = β / (1 - β) * (pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s) ^ (1 - ρ)) :
    (a / (1 - a)) ^ (-ρ) = β * (pa_E p fun s =>
      (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) ^ ((1 - ρ) / (1 - γ)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hterm : ∀ s, (pa_Anext β ρ C' X' s * Rw s) ^ (1 - γ) = (1 - β) ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) := by
    intro s
    have hc := hC' s
    have hx := hX' s
    have hr := hR s
    simp only [pa_Anext]
    rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hβ'.le, ← Real.rpow_mul (by positivity),
      show 1 / (1 - ρ) * (1 - γ) = (1 - γ) / (1 - ρ) by ring,
      show -ρ / (1 - ρ) * (1 - γ) = -ρ * (1 - γ) / (1 - ρ) by ring]
    ring
  have hG : 0 ≤ pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (mul_nonneg
      (Real.rpow_nonneg (div_pos (hC' s) (hX' s)).le _) (Real.rpow_nonneg (hR s).le _))
  rw [h22]
  simp only [pa_CE]
  rw [pa_E_congr p hterm, pa_E_const_mul, ← Real.rpow_mul (mul_nonneg
    (Real.rpow_nonneg hβ'.le _) hG), Real.mul_rpow (Real.rpow_nonneg hβ'.le _) hG,
    ← Real.rpow_mul hβ'.le, show (1 - γ) / (1 - ρ) * (1 / (1 - γ) * (1 - ρ)) = 1 by field_simp,
    Real.rpow_one, show 1 / (1 - γ) * (1 - ρ) = (1 - ρ) / (1 - γ) by ring]
  field_simp

/-- Miao, (20.26), p. 712: substituting (20.25) into (20.24),
`β^{(1−γ)/(1−ρ)} E_t[(C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ)}] = 1`. -/
theorem eq_20_26 {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {β ρ γ a C : ℝ} (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (h24 : (a / (1 - a)) ^ (-ρ) = β * (pa_E p fun s =>
      (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) ^ ((1 - ρ) / (1 - γ))) :
    β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ ((1 - γ) / (1 - ρ))) = 1 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hb : (0 : ℝ) < 1 - a := by linarith
  set b := a / (1 - a) with hb_def
  have hbpos : 0 < b := div_pos ha0 hb
  set k := -ρ * (1 - γ) / (1 - ρ) with hk
  have hterm : ∀ s, (C' s / X' s) ^ k * Rw s ^ (1 - γ)
      = b ^ k * ((C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ))) := by
    intro s
    have hc := hC' s
    have hr := hR s
    rw [h25 s]
    apply pa_eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, hb_def]
    rw [hk]
    field_simp
    ring
  have hE' : 0 < pa_E p fun s => (C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ)) :=
    pa_E_pos hp hp1 fun s => mul_pos (Real.rpow_pos_of_pos (div_pos (hC' s) hC) _)
      (Real.rpow_pos_of_pos (hR s) _)
  set E' := pa_E p fun s => (C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ)) with hE'_def
  rw [pa_E_congr p hterm, pa_E_const_mul, Real.mul_rpow (Real.rpow_nonneg hbpos.le _) hE'.le,
    ← Real.rpow_mul hbpos.le, show k * ((1 - ρ) / (1 - γ)) = -ρ by rw [hk]; field_simp] at h24
  have hβE : β * E' ^ ((1 - ρ) / (1 - γ)) = 1 := by
    have hbρ := Real.rpow_pos_of_pos hbpos (-ρ)
    field_simp at h24
    nlinarith [h24]
  have := congrArg (fun x : ℝ => x ^ ((1 - γ) / (1 - ρ))) hβE
  simp only [Real.one_rpow] at this
  rw [Real.mul_rpow hβ0.le (Real.rpow_nonneg hE'.le _), ← Real.rpow_mul hE'.le,
    show (1 - ρ) / (1 - γ) * ((1 - γ) / (1 - ρ)) = 1 by field_simp, Real.rpow_one] at this
  exact this

/-- The wealth return in excess-return form, `R_w = R_f + ∑_i ψ_i (R_i − R_f)`, where `ψ` are
the weights on the risky assets (the riskless asset has weight `1 − ∑ ψ_i`). -/
def pa_Rw {S ι : Type*} [Fintype ι] (Rf : ℝ) (ψ : ι → ℝ) (R : ι → S → ℝ) (s : S) : ℝ :=
  Rf + ∑ i, ψ i * (R i s - Rf)

/-- Raising the weight on risky asset `i` by `t` (financed by the riskless asset) moves the
wealth return by `t (R_i − R_f)`. -/
theorem pa_Rw_update {S ι : Type*} [Fintype ι] [DecidableEq ι] (Rf : ℝ) (ψ : ι → ℝ)
    (R : ι → S → ℝ) (i : ι) (t : ℝ) (s : S) :
    pa_Rw Rf (ψ + t • Pi.single i 1) R s = pa_Rw Rf ψ R s + t * (R i s - Rf) := by
  simp only [pa_Rw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  ring

/-- Miao, §20.4.1, p. 712: the portfolio first-order condition. If the weight `t = 0` on the
direction `d` (for asset `i`, `d = R_i − R_f`) locally maximises the certainty equivalent
`M_t(A_{t+1}(R_w + t d))`, then `E_t[A_{t+1}^{1−γ} R_w^{−γ} d] = 0`. -/
theorem pa_portfolio_foc {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {γ : ℝ} (hγ : γ ≠ 1) {A' Rw d : S → ℝ} (hA : ∀ s, 0 < A' s)
    (hR : ∀ s, 0 < Rw s)
    (hmax : IsLocalMax (fun t : ℝ => pa_CE γ p fun s => A' s * (Rw s + t * d s)) 0) :
    (pa_E p fun s => A' s ^ (1 - γ) * Rw s ^ (-γ) * d s) = 0 := by
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hterm : ∀ s, HasDerivAt (fun t : ℝ => p s * (A' s * (Rw s + t * d s)) ^ (1 - γ))
      (p s * ((1 - γ) * (A' s ^ (1 - γ) * Rw s ^ (-γ) * d s))) 0 := by
    intro s
    have hin : HasDerivAt (fun t : ℝ => A' s * (Rw s + t * d s)) (A' s * (1 * d s)) 0 :=
      (((hasDerivAt_id (0 : ℝ)).mul_const (d s)).const_add (Rw s)).const_mul (A' s)
    have hpos : 0 < A' s * (Rw s + 0 * d s) := by
      rw [zero_mul, add_zero]; exact mul_pos (hA s) (hR s)
    have := (hin.rpow_const (p := 1 - γ) (Or.inl hpos.ne')).const_mul (p s)
    convert this using 2
    rw [zero_mul, add_zero, Real.mul_rpow (hA s).le (hR s).le,
      show (1 : ℝ) - γ - 1 = -γ by ring, Real.rpow_sub (hA s), Real.rpow_one]
    have := (hA s).ne'
    simp only [Real.rpow_neg (hA s).le]
    field_simp
  have hg := HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hterm s
  have hg0 : 0 < ∑ s, p s * (A' s * (Rw s + 0 * d s)) ^ (1 - γ) := by
    simp only [zero_mul, add_zero]
    exact pa_E_pos hp hp1 fun s => Real.rpow_pos_of_pos (mul_pos (hA s) (hR s)) _
  have hce := hg.rpow_const (p := 1 / (1 - γ)) (Or.inl hg0.ne')
  have hd := hmax.hasDerivAt_eq_zero hce
  have hpos := Real.rpow_pos_of_pos hg0 (1 / (1 - γ) - 1)
  rcases mul_eq_zero.1 hd with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have hsum : ∑ s, p s * ((1 - γ) * (A' s ^ (1 - γ) * Rw s ^ (-γ) * d s))
          = (1 - γ) * pa_E p fun s => A' s ^ (1 - γ) * Rw s ^ (-γ) * d s := by
        simp only [pa_E, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hsum] at h
      exact (mul_eq_zero.1 h).resolve_left h2
    · simp only [one_div, inv_eq_zero] at h
      exact absurd h h2
  · exact absurd h hpos.ne'

/-- Miao, p. 712: substituting (20.23) at `t + 1` into the portfolio first-order condition,
`E_t[(C_{t+1}/X_{t+1})^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{−γ} (R_{i,t+1} − R_{f,t+1})] = 0`. -/
theorem pa_portfolio_foc_X {S : Type*} [Fintype S] {p : S → ℝ} {β ρ γ : ℝ} (hβ1 : β < 1)
    {C' X' Rw d : S → ℝ} (hC' : ∀ s, 0 < C' s) (hX' : ∀ s, 0 < X' s)
    (hfoc : (pa_E p fun s => pa_Anext β ρ C' X' s ^ (1 - γ) * Rw s ^ (-γ) * d s) = 0) :
    (pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) = 0 := by
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hterm : ∀ s, pa_Anext β ρ C' X' s ^ (1 - γ) * Rw s ^ (-γ) * d s
      = (1 - β) ^ ((1 - γ) / (1 - ρ)) *
        ((C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) := by
    intro s
    have hc := hC' s
    have hx := hX' s
    simp only [pa_Anext]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hβ'.le,
      ← Real.rpow_mul (by positivity), show 1 / (1 - ρ) * (1 - γ) = (1 - γ) / (1 - ρ) by ring,
      show -ρ / (1 - ρ) * (1 - γ) = -ρ * (1 - γ) / (1 - ρ) by ring]
    ring
  rw [pa_E_congr p hterm, pa_E_const_mul] at hfoc
  exact (mul_eq_zero.1 hfoc).resolve_left (Real.rpow_pos_of_pos hβ' _).ne'

/-- Miao, (20.27), p. 712: substituting (20.25),
`E_t[(C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ) − 1} (R_{i,t+1} − R_{f,t+1})] = 0`. -/
theorem eq_20_27 {S : Type*} [Fintype S] {p : S → ℝ} {ρ γ a C : ℝ} (hρ : ρ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw d : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (hfoc : (pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) = 0) :
    (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      Rw s ^ ((1 - γ) / (1 - ρ) - 1) * d s) = 0 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hbpos : 0 < a / (1 - a) := div_pos ha0 hb
  have hterm : ∀ s, (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s
      = (a / (1 - a)) ^ (-ρ * (1 - γ) / (1 - ρ)) * ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
        Rw s ^ ((1 - γ) / (1 - ρ) - 1) * d s) := by
    intro s
    have hc := hC' s
    have hr := hR s
    have key : (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ)
        = (a / (1 - a)) ^ (-ρ * (1 - γ) / (1 - ρ)) * ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
          Rw s ^ ((1 - γ) / (1 - ρ) - 1)) := by
      rw [h25 s]
      apply pa_eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
      field_simp
      ring
    rw [key]
    ring
  rw [pa_E_congr p hterm, pa_E_const_mul] at hfoc
  exact (mul_eq_zero.1 hfoc).resolve_left (Real.rpow_pos_of_pos hbpos _).ne'

/-- Miao, p. 713: multiplying (20.27) by `ψ_{i,t+1}` and summing over the risky assets,
`E_t[K R_w^{(1−γ)/(1−ρ)−1} R_f] = E_t[K R_w^{(1−γ)/(1−ρ)}]`, `K = (C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)}`. -/
theorem pa_sum_portfolio_foc {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {ρ γ C Rf : ℝ}
    {C' : S → ℝ} {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) :
    (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf)
      = pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
        pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ)) := by
  set K := fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
    pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) with hK
  have hsum : ∑ i, ψ i * (pa_E p fun s => K s * (R i s - Rf)) = 0 := by
    simp only [hK, h27, mul_zero, Finset.sum_const_zero]
  have hpt : ∀ s, (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))
      = K s * Rf + K s * ∑ i, ψ i * (R i s - Rf) := by
    intro s
    rw [← mul_add, show Rf + ∑ i, ψ i * (R i s - Rf) = pa_Rw Rf ψ R s from rfl, hK]
    simp only
    rw [mul_assoc, ← Real.rpow_add_one (hR s).ne', sub_add_cancel]
  have hswap : (pa_E p fun s => K s * ∑ i, ψ i * (R i s - Rf))
      = ∑ i, ψ i * (pa_E p fun s => K s * (R i s - Rf)) := by
    simp only [pa_E, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  rw [pa_E_congr p hpt, pa_E_add, hswap, hsum, add_zero]

/-- Miao, (20.30), p. 713: the kernel
`M̄_{t+1} = (β (C_{t+1}/C_t)^{−ρ})^{(1−γ)/(1−ρ)} R_{w,t+1}^{(ρ−γ)/(1−ρ)}`. -/
noncomputable def pa_Mbar {S : Type*} (β ρ γ C : ℝ) (C' Rw : S → ℝ) (s : S) : ℝ :=
  (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) * Rw s ^ ((ρ - γ) / (1 - ρ))

theorem pa_Mbar_eq {S : Type*} {β ρ γ C : ℝ} (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C)
    {C' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s) (s : S) :
    pa_Mbar β ρ γ C C' Rw s = β ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ ((1 - γ) / (1 - ρ) - 1)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hc := hC' s
  simp only [pa_Mbar]
  rw [Real.mul_rpow hβ0.le (by positivity), ← Real.rpow_mul (by positivity),
    show -ρ * ((1 - γ) / (1 - ρ)) = -ρ * (1 - γ) / (1 - ρ) by ring,
    show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by field_simp; ring]
  ring

/-- Miao, (20.28), p. 713: using (20.26) in `pa_sum_portfolio_foc`,
`E_t[(β (C_{t+1}/C_t)^{−ρ})^{(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ) − 1} R_{f,t+1}] = 1`. -/
theorem eq_20_28 {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {β ρ γ C Rf : ℝ}
    (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C) {C' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h26 : β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))) = 1)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) :
    (pa_E p fun s => (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf) = 1 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hpt : ∀ s, (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf = β ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf) := by
    intro s
    have h := pa_Mbar_eq (γ := γ) (Rw := pa_Rw Rf ψ R) hβ0 hρ hC hC' s
    simp only [pa_Mbar] at h
    rw [show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by field_simp; ring] at h
    rw [h]
    ring
  rw [pa_E_congr p hpt, pa_E_const_mul, pa_sum_portfolio_foc hR h27, h26]

/-- Miao, (20.29)–(20.30), p. 713: the Euler equation `E_t[M̄_{t+1} R_{i,t+1}] = 1` for every
asset `i`, where `M̄` is the kernel (20.30). -/
theorem eq_20_29 {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {β ρ γ C Rf : ℝ}
    (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C) {C' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h26 : β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))) = 1)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) (i : ι) :
    (pa_E p fun s => pa_Mbar β ρ γ C C' (pa_Rw Rf ψ R) s * R i s) = 1 := by
  have h28 := eq_20_28 hβ0 hρ hC hC' hR h26 h27
  set K := fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
    pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) with hK
  have hMK : ∀ s, pa_Mbar β ρ γ C C' (pa_Rw Rf ψ R) s * R i s
      = β ^ ((1 - γ) / (1 - ρ)) * (K s * Rf) + β ^ ((1 - γ) / (1 - ρ)) * (K s * (R i s - Rf)) := by
    intro s
    rw [pa_Mbar_eq hβ0 hρ hC hC' s]
    ring
  have h28' : (pa_E p fun s => β ^ ((1 - γ) / (1 - ρ)) * (K s * Rf)) = 1 := by
    refine Eq.trans (pa_E_congr p fun s => ?_) h28
    have h := pa_Mbar_eq (γ := γ) (Rw := pa_Rw Rf ψ R) hβ0 hρ hC hC' s
    simp only [pa_Mbar] at h
    rw [show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by
      have : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
      field_simp; ring] at h
    rw [h, hK]
    ring
  rw [pa_E_congr p hMK, pa_E_add, h28', pa_E_const_mul, h27 i, mul_zero, add_zero]

/-- Miao, (20.31), p. 713: substituting (20.23) into `U_t = J_t(X_t) = A_t X_t`,
`X_t/C_t = (1/(1 − β)) (U_t/C_t)^{1−ρ}`. -/
theorem eq_20_31 {β ρ X C U : ℝ} (hβ1 : β < 1) (hρ : ρ ≠ 1) (hX : 0 < X) (hC : 0 < C)
    (hU : U = (1 - β) ^ (1 / (1 - ρ)) * (C / X) ^ (-ρ / (1 - ρ)) * X) :
    X / C = 1 / (1 - β) * (U / C) ^ (1 - ρ) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  subst hU
  apply pa_eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
  field_simp
  ring

/-- Miao, pp. 713–714: the pricing kernel (20.20) equals the kernel (20.30), `M_{t+1} = M̄_{t+1}`.
Here `U_{t+1} = A_{t+1} X_{t+1}` is the utility value, `A_{t+1}` is given by (20.23),
`X_{t+1}` by (20.25), and the consumption–wealth ratio `a_t` satisfies (20.22). -/
theorem pa_M_eq_Mbar {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {β ρ γ a C : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw U' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (hU : ∀ s, U' s = pa_Anext β ρ C' X' s * X' s)
    (h22 : (a / (1 - a)) ^ (-ρ)
      = β / (1 - β) * (pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s) ^ (1 - ρ)) (s : S) :
    pa_M β ρ γ p C C' U' s = pa_Mbar β ρ γ C C' Rw s := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hX' : ∀ s, 0 < X' s := fun s => by
    rw [h25 s]; exact mul_pos (mul_pos (hR s) hC) (div_pos hb ha0)
  have hA : ∀ s, 0 < pa_Anext β ρ C' X' s := fun s =>
    mul_pos (Real.rpow_pos_of_pos hβ' _) (Real.rpow_pos_of_pos (div_pos (hC' s) (hX' s)) _)
  set Q := pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s with hQ_def
  have hQ : 0 < Q := pa_CE_pos hp hp1 γ fun s => mul_pos (hA s) (hR s)
  have hCE : pa_CE γ p U' = C * ((1 - a) / a) * Q := by
    rw [hQ_def, ← pa_CE_homog hγ hp (mul_pos hC (div_pos hb ha0))
      fun s => (mul_pos (hA s) (hR s)).le]
    congr 1
    funext s
    rw [hU s, h25 s]
    ring
  have hlQ : Real.log Q = (-ρ * Real.log (a / (1 - a)) - Real.log (β / (1 - β))) / (1 - ρ) := by
    have := congrArg Real.log h22
    rw [Real.log_rpow (div_pos ha0 hb), Real.log_mul (div_pos hβ0 hβ').ne'
      (Real.rpow_pos_of_pos hQ _).ne', Real.log_rpow hQ] at this
    field_simp
    linarith
  have hc := hC' s
  have hr := hR s
  have hx := hX' s
  have hu : U' s = pa_Anext β ρ C' X' s * X' s := hU s
  simp only [pa_M, pa_Mbar]
  rw [hCE, hu]
  have ha' := hA s
  have hab : 0 < (1 - a) / a := div_pos hb ha0
  apply pa_eq_of_log_eq (by positivity) (by positivity)
  simp only [pa_Anext]
  rw [h25 s]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  rw [hlQ]
  simp (disch := positivity) only [Real.log_div]
  field_simp
  ring

/-- Miao, p. 714: the Euler equation (20.29) for the riskless asset gives
`R_{f,t+1} = 1/E_t[M_{t+1}]`. -/
theorem pa_riskfree_rate {S : Type*} [Fintype S] {p M : S → ℝ} {Rf : ℝ}
    (h : (pa_E p fun s => M s * Rf) = 1) : Rf = 1 / pa_E p M := by
  rw [pa_E_mul_const] at h
  have hM : pa_E p M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  field_simp
  linarith

/-- The conditional covariance `Cov_t(f, g) = E_t[f g] − E_t f E_t g`. -/
def pa_Cov {S : Type*} [Fintype S] (p f g : S → ℝ) : ℝ :=
  pa_E p (fun s => f s * g s) - pa_E p f * pa_E p g

/-- Miao, p. 714: the conditional equity premium
`E_t[R_{e,t+1}] − R_{f,t+1} = −Cov_t(R_{e,t+1}, M_{t+1})/E_t[M_{t+1}]`, from the Euler
equations for equity and the riskless asset. -/
theorem pa_equity_premium {S : Type*} [Fintype S] {p M Re : S → ℝ} {Rf : ℝ}
    (he : (pa_E p fun s => M s * Re s) = 1) (hf : (pa_E p fun s => M s * Rf) = 1) :
    pa_E p Re - Rf = -pa_Cov p Re M / pa_E p M := by
  have hRf := pa_riskfree_rate hf
  rw [pa_E_mul_const] at hf
  have hM : pa_E p M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hf
    exact zero_ne_one hf
  have he' : (pa_E p fun s => Re s * M s) = 1 := by
    rw [← he]; exact pa_E_congr p fun s => mul_comm _ _
  simp only [pa_Cov, he']
  rw [hRf]
  field_simp
  ring

end Miao.RecursiveUtility
