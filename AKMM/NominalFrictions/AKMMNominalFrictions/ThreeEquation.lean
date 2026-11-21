/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMNominalFrictions.NaturalOutput
import BasicNewKeynesianModel.Expectations

/-!
# The three-equation model: the IS curve and the New Keynesian Phillips curve

AKMM, §18.3, pp. 543–544, and Appendix 18.A.1, pp. 871–872.

**The IS curve (18.15).** Under perfect foresight the log of the Euler equation (18.5) is exact,
and with `C = Y` and natural output (18.13) it gives
`x_t = x_{t+1} − σ⁻¹(î_t − π̂_{t+1} − r^n_t)` with
`r^n_t = −log β + σ(1+ψ)/(σ+ψ)(log A_{t+1} − log A_t)` (`eq_18_15_exact`). The book prints
`(Â_t − E_tÂ_{t+1})`: that sign is wrong (`rn_printed_iff`: the printed equation holds only when
productivity is expected constant). Under uncertainty, from the log-linear Euler equation
`σ ŷ_t = σ E_t ŷ_{t+1} − (î_t − E_t π_{t+1} + log β)` (logs taken inside `E_t`, footnote 9), the
same algebra gives (18.15) with `r^n_t = −log β + σ(1+ψ)/(σ+ψ)(E_t a_{t+1} − a_t)` for any
expectation system (`eq_18_15`).

**The rule (18.17).** With `î = log(1 + i)` as in (18.15), (18.17) has no intercept, so it is not
consistent with the zero-inflation steady state unless `β = 1` (`rule_18_17_no_steady_state`);
the rule needs the intercept `−log β` (the book's `ī`), as in the rule on p. 543.

**The Phillips curve (18.16).** (18.A.1) in present-value form gives (18.A.2)
(`eq_18_A_2_pv`, `eq_18_A_2`); (18.A.3) is the derivative of (18.10) at zero inflation
(`eq_18_A_3`); combined they give (18.A.4) (`eq_18_A_4`); dispersion drops out to first order
(`eq_18_A_dispersion`, `nk_dispersion_hat_zero`); (18.A.5)–(18.A.6) hold exactly in logs, with
the dispersion term `ψ log D` (`eq_18_A_5_exact`), so `ŵ − Â = (σ+ψ) x` when `D = 1`; and (18.16)
follows (`eq_18_16`), with `κ > 0` decreasing in `θ` (`nk_kappa_pos`, `nk_kappa_antitone`).
-/

namespace AKMM.NominalFrictions

open Filter Topology Finset Gali.BasicNewKeynesianModel

/-- AKMM, (18.16), p. 544: the slope `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`. -/
noncomputable def nfKappa (β θ σ ψ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) * (σ + ψ) / θ

/-- **AKMM, (18.15), p. 543 (corrected), perfect foresight, exact**: with `C = Y`, the Euler
equation (18.5) and natural output (18.13) at `t` and `t + 1`, the output gap satisfies
`x_t = x_{t+1} − σ⁻¹(log(1+i_t) − log(1+π_{t+1}) − r^n_t)`,
`r^n_t = −log β + σ(1+ψ)/(σ+ψ)(log A_{t+1} − log A_t)`. -/
theorem eq_18_15_exact {β σ ψ mu i π' Y₀ Y₁ A₀ A₁ : ℝ} (hσ : σ ≠ 0) (hβ : 0 < β)
    (hmu : 0 < mu) (hY₀ : 0 < Y₀) (hY₁ : 0 < Y₁) (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hi : 0 < 1 + i) (hπ : 0 < 1 + π')
    (heuler : Y₀ ^ (-σ) = β * ((1 + i) / (1 + π') * Y₁ ^ (-σ))) :
    nfGap Y₀ (mu ^ (-1 / (σ + ψ)) * A₀ ^ ((1 + ψ) / (σ + ψ))) =
      nfGap Y₁ (mu ^ (-1 / (σ + ψ)) * A₁ ^ ((1 + ψ) / (σ + ψ))) -
        σ⁻¹ * (Real.log (1 + i) - Real.log (1 + π') -
          (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (Real.log A₁ - Real.log A₀))) := by
  have hl := congrArg Real.log heuler
  rw [Real.log_rpow hY₀, Real.log_mul hβ.ne' (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_div hi.ne' hπ.ne', Real.log_rpow hY₁] at hl
  rw [nat_gap_loglinear hmu hA₀, nat_gap_loglinear hmu hA₁]
  have hσi : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  have e : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) = (1 + ψ) / (σ + ψ) := by
    rw [← mul_div_assoc, ← mul_assoc, hσi, one_mul]
  linear_combination (-σ⁻¹) * hl - (Real.log Y₀ - Real.log Y₁) * hσi -
    (Real.log A₁ - Real.log A₀) * e

/-- **AKMM, p. 543 (the printed natural rate)**: given the exact relation of `eq_18_15_exact`,
the IS equation with the printed `r^n = −log β + σ(1+ψ)/(σ+ψ)(log A_t − log A_{t+1})` also
holds iff `log A_{t+1} = log A_t` (for `σ, 1 + ψ ≠ 0`, `σ + ψ ≠ 0`). -/
theorem rn_printed_iff {β σ ψ x₀ x₁ ii pp a₀ a₁ : ℝ} (hσ : σ ≠ 0) (hψ : 1 + ψ ≠ 0)
    (hs : σ + ψ ≠ 0)
    (hcorr : x₀ = x₁ - σ⁻¹ * (ii - pp - (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (a₁ - a₀)))) :
    x₀ = x₁ - σ⁻¹ * (ii - pp - (-Real.log β + σ * (1 + ψ) / (σ + ψ) * (a₀ - a₁))) ↔ a₁ = a₀ := by
  constructor
  · intro h
    have h2 : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) * (2 * (a₁ - a₀)) = 0 := by
      linear_combination h - hcorr
    have hc : σ⁻¹ * (σ * (1 + ψ) / (σ + ψ)) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hσ) (div_ne_zero (mul_ne_zero hσ hψ) hs)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc
    · linarith
  · intro h; rw [h] at hcorr ⊢; exact hcorr

/-- **AKMM, (18.15), p. 543 (corrected), under uncertainty**: if
`σ y_t = σ E_t y_{t+1} − (î_t − E_t π_{t+1} + log β)` (the log-linear Euler equation, footnote 9)
and natural output is `y^n = c + ψ_a a` with `ψ_a = (1+ψ)/(σ+ψ)` (18.13), then
`x_t = E_t x_{t+1} − σ⁻¹(î_t − E_t π_{t+1} − r^n_t)` with
`r^n_t = −log β + σψ_a(E_t a_{t+1} − a_t)`. -/
theorem eq_18_15 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β σ ψ c : ℝ} (hσ : σ ≠ 0)
    {y yn a ii pinf : ℕ → Ω → ℝ} (t : ℕ)
    (heuler : σ • y t = σ • 𝔼.E t (y (t + 1)) - (ii t - 𝔼.E t (pinf (t + 1)) +
      fun _ => Real.log β))
    (hyn : ∀ s, yn s = (fun _ => c) + ((1 + ψ) / (σ + ψ)) • a s) :
    y t - yn t = 𝔼.E t (y (t + 1) - yn (t + 1)) - σ⁻¹ • (ii t - 𝔼.E t (pinf (t + 1)) -
      ((fun _ => -Real.log β) + (σ * ((1 + ψ) / (σ + ψ))) • (𝔼.E t (a (t + 1)) - a t))) := by
  rw [hyn t, hyn (t + 1), map_sub, map_add, 𝔼.const, map_smul]
  funext ω
  have h := congrFun heuler ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  field_simp
  linear_combination h

/-- **AKMM, (18.17), p. 544**: with `î = log(1 + i)` as in (18.15) and `r^n = −log β` (constant
productivity), a zero-inflation, zero-gap steady state with `ω = 0` satisfies (18.15) only if
`î = −log β`, while the printed rule (18.17) gives `î = 0`; both hold only if `β = 1`. -/
theorem rule_18_17_no_steady_state {β σ ii : ℝ} (hβ : 0 < β) (hσ : σ ≠ 0)
    (his : (0 : ℝ) = 0 - σ⁻¹ * (ii - 0 - -Real.log β)) (hrule : ii = 0) : β = 1 := by
  rw [hrule] at his
  have : Real.log β = 0 := by
    have h := his
    field_simp at h
    linarith
  rcases Real.log_eq_zero.1 this with h | h | h <;> [linarith; exact h; linarith]

/-- **AKMM, (18.A.2), p. 871 (from the present value)**: if the reset price satisfies
`p̂^R_t = (1 − βθ) ∑_k (βθ)^k (m_{t+k} + P̂_{t+k} − P̂_t)` (the log-linearised (18.A.1) with
`p̂^R_{t,τ} = p̂^R_t − (P̂_τ − P̂_t)` and `∑ (βθ)^k = 1/(1 − βθ)`) and the series converges, then
`p̂^R_t = (1 − βθ) m_t + βθ (p̂^R_{t+1} + P̂_{t+1} − P̂_t)` (perfect foresight). -/
theorem eq_18_A_2 {β θ : ℝ} {m P pR : ℕ → ℝ} (t : ℕ)
    (hs : ∀ s, Summable fun k => (β * θ) ^ k * (m (s + k) + P (s + k) - P s))
    (hpv : ∀ s, pR s = (1 - β * θ) * ∑' k, (β * θ) ^ k * (m (s + k) + P (s + k) - P s))
    (hs1 : Summable fun k : ℕ => (β * θ) ^ k) :
    pR t = (1 - β * θ) * m t + β * θ * (pR (t + 1) + P (t + 1) - P t) := by
  rw [hpv t, hpv (t + 1), (hs t).tsum_eq_zero_add]
  have e : ∀ k, (β * θ) ^ (k + 1) * (m (t + (k + 1)) + P (t + (k + 1)) - P t) =
      β * θ * ((β * θ) ^ k * (m (t + 1 + k) + P (t + 1 + k) - P (t + 1)) +
        (β * θ) ^ k * (P (t + 1) - P t)) := by
    intro k
    rw [show t + (k + 1) = t + 1 + k by ring, pow_succ]; ring
  simp_rw [e]
  rw [tsum_mul_left, (hs (t + 1)).tsum_add (hs1.mul_right _), tsum_mul_right]
  have hb : ‖β * θ‖ < 1 := summable_geometric_iff_norm_lt_one.1 hs1
  have hb1 : β * θ < 1 := lt_of_abs_lt (by rwa [Real.norm_eq_abs] at hb)
  have h0 : (1 : ℝ) - β * θ ≠ 0 := by linarith
  rw [tsum_geometric_of_norm_lt_one hb]
  simp only [pow_zero, one_mul, add_zero]
  field_simp
  ring

/-- **AKMM, (18.A.2), p. 871, under uncertainty**: the recursive form
`p̂^R_t = (1 − βθ) m_t + βθ E_t(p̂^R_{t+1} + π_{t+1})` as a definition of the reset-price
dynamics for any expectation system (used by `eq_18_A_4`). -/
def ResetRecursion {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β θ : ℝ)
    (m pR infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pR t = (1 - β * θ) • m t + (β * θ) • 𝔼.E t (pR (t + 1) + infl (t + 1))

/-- **AKMM, (18.A.2)–(18.A.3), p. 872 (a concrete instance)**: under perfect foresight, the
geometric paths `p̂^R_t = cρᵗ`, `π_t = (1 − θ)/θ · cρᵗ`, marginal cost
`m_t = cρᵗ(1 − βρ)/(1 − βθ)` and output gap `x_t = m_t/(σ + ψ)` satisfy the reset-price
recursion `ResetRecursion`, the inflation relation (18.A.3) and `m = (σ + ψ)x`: all the
hypotheses of `eq_18_A_4`, `eq_18_16` and `eq_18_23` (`βθ ≠ 1`, `θ ≠ 0`, `σ + ψ ≠ 0`). For
`c ≠ 0` the paths are nonzero. -/
theorem reset_recursion_instance {β θ σ ψ c ρ : ℝ} (hβθ : β * θ ≠ 1) (hθ : θ ≠ 0)
    (hs : σ + ψ ≠ 0) :
    ResetRecursion perfectForesight β θ
        (fun t _ => c * ρ ^ t * (1 - β * ρ) / (1 - β * θ)) (fun t _ => c * ρ ^ t)
        (fun t _ => (1 - θ) / θ * (c * ρ ^ t)) ∧
      (∀ s, (fun _ => (1 - θ) / θ * (c * ρ ^ s) : Unit → ℝ) =
        ((1 - θ) / θ) • (fun _ => c * ρ ^ s : Unit → ℝ)) ∧
      (∀ s, (fun _ => c * ρ ^ s * (1 - β * ρ) / (1 - β * θ) : Unit → ℝ) =
        (σ + ψ) • (fun _ => c * ρ ^ s * (1 - β * ρ) / (1 - β * θ) / (σ + ψ) : Unit → ℝ)) ∧
      (c ≠ 0 → (fun _ => c * ρ ^ 0 : Unit → ℝ) ≠ 0) := by
  have h1 : (1 : ℝ) - β * θ ≠ 0 := sub_ne_zero.2 (Ne.symm hβθ)
  refine ⟨fun t => ?_, fun s => ?_, fun s => ?_, fun hc h => ?_⟩
  · funext ω
    change c * ρ ^ t = (1 - β * θ) * (c * ρ ^ t * (1 - β * ρ) / (1 - β * θ)) +
      β * θ * (c * ρ ^ (t + 1) + (1 - θ) / θ * (c * ρ ^ (t + 1)))
    field_simp
    ring
  · funext ω; simp only [Pi.smul_apply, smul_eq_mul]
  · funext ω; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  · have := congrFun h ()
    simp only [pow_zero, mul_one, Pi.zero_apply] at this
    exact hc this

/-- **AKMM, (18.A.3), p. 872**: the log-linearisation of (18.10). As a function of
`z = log p^R`, `log(1 + π) = (1/(ε − 1)) log((1 − (1 − θ) e^{(1−ε)z})/θ)` has derivative
`(1 − θ)/θ` at the zero-inflation steady state `z = 0`. -/
theorem eq_18_A_3 {θ ε : ℝ} (hθ : 0 < θ) (hε : ε ≠ 1) :
    HasDerivAt (fun z => 1 / (ε - 1) * Real.log ((1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ))
      ((1 - θ) / θ) 0 := by
  have hε1 : ε - 1 ≠ 0 := sub_ne_zero.2 hε
  have hg : HasDerivAt (fun z => (1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ)
      (-(1 - θ) * (1 - ε) / θ) 0 := by
    have h1 : HasDerivAt (fun z : ℝ => (1 - ε) * z) (1 - ε) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - ε)
    have h2 := ((h1.exp.const_mul (1 - θ)).const_sub 1).div_const θ
    convert h2 using 1
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  have hg0 : (1 - (1 - θ) * Real.exp ((1 - ε) * 0)) / θ = 1 := by
    simp [div_self hθ.ne']
  have hl := (hg.log (by rw [hg0]; norm_num)).const_mul (1 / (ε - 1))
  rw [hg0] at hl
  convert hl using 1
  field_simp
  ring

/-- **AKMM, (18.A.3) and (18.10), p. 872**: (18.A.3) is the derivative of the exact relation
(18.10): for `p^R = e^z`, `log` of the right side of (18.10) is the function of `eq_18_A_3`. -/
theorem eq_18_A_3_exact {θ ε z : ℝ}
    (hpos : 0 < (1 - (1 - θ) * Real.exp z ^ (1 - ε)) / θ) :
    Real.log (((1 - (1 - θ) * Real.exp z ^ (1 - ε)) / θ) ^ (1 / (ε - 1))) =
      1 / (ε - 1) * Real.log ((1 - (1 - θ) * Real.exp ((1 - ε) * z)) / θ) := by
  rw [Real.log_rpow hpos, ← Real.exp_mul, mul_comm z]

/-- **AKMM, (18.A.4), p. 872**: if the reset price follows (18.A.2) and inflation is
`π = (1 − θ)/θ · p̂^R` (18.A.3) at every date, then
`π_t = (1 − θ)(1 − βθ)/θ · m_t + β E_t π_{t+1}` (`θ ∈ (0, 1)`). -/
theorem eq_18_A_4 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β θ : ℝ} (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1)
    {m pR infl : ℕ → Ω → ℝ} (hrec : ResetRecursion 𝔼 β θ m pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (t : ℕ) :
    infl t = ((1 - θ) * (1 - β * θ) / θ) • m t + β • 𝔼.E t (infl (t + 1)) := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ1)
  have hp : ∀ s, pR s = (θ / (1 - θ)) • infl s := by
    intro s; rw [h3 s, smul_smul, div_mul_div_cancel₀ h1θ, div_self hθ0, one_smul]
  have hsum : pR (t + 1) + infl (t + 1) = (1 / (1 - θ)) • infl (t + 1) := by
    rw [hp (t + 1)]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [h3 t, hrec t, hsum, map_smul]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **AKMM, p. 872 (dispersion to first order)**: the log of the dispersion recursion (18.12),
`log[(1 − θ)(e^{s a})^{−ε} + θ(e^{s b})^ε e^{s c}]`, has derivative
`−ε(1 − θ) a + θ ε b + θ c` at the steady state `s = 0` (`D̄ = p̄^R = 1 + π̄ = 1`). -/
theorem eq_18_A_dispersion (θ ε a b c : ℝ) :
    HasDerivAt (fun s => Real.log ((1 - θ) * (Real.exp (s * a)) ^ (-ε) +
        θ * (Real.exp (s * b)) ^ ε * Real.exp (s * c)))
      (-ε * (1 - θ) * a + θ * ε * b + θ * c) 0 := by
  have e : ∀ s, (1 - θ) * (Real.exp (s * a)) ^ (-ε) + θ * (Real.exp (s * b)) ^ ε *
      Real.exp (s * c) = (1 - θ) * Real.exp (-ε * a * s) + θ * Real.exp ((ε * b + c) * s) := by
    intro s
    rw [← Real.exp_mul, ← Real.exp_mul, mul_assoc θ, ← Real.exp_add]
    congr 3 <;> ring
  simp_rw [e]
  have h1 : HasDerivAt (fun s => (1 - θ) * Real.exp (-ε * a * s) + θ * Real.exp ((ε * b + c) * s))
      ((1 - θ) * (Real.exp (-ε * a * 0) * (-ε * a)) +
        θ * (Real.exp ((ε * b + c) * 0) * (ε * b + c))) 0 := by
    have ha : HasDerivAt (fun s : ℝ => -ε * a * s) (-ε * a) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-ε * a)
    have hb : HasDerivAt (fun s : ℝ => (ε * b + c) * s) (ε * b + c) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (ε * b + c)
    exact (ha.exp.const_mul _).add (hb.exp.const_mul _)
  have h0 : (1 - θ) * Real.exp (-ε * a * 0) + θ * Real.exp ((ε * b + c) * 0) = 1 := by simp
  have hl := h1.log (by rw [h0]; norm_num)
  rw [h0] at hl
  convert hl using 1
  simp
  ring

/-- **AKMM, p. 872**: with (18.A.3), `b = (1 − θ)/θ · a`, the first-order dispersion
recursion is `D̂_t = θ D̂_{t−1}`. -/
theorem nk_dispersion_hat_rec {θ ε a c : ℝ} (hθ : θ ≠ 0) :
    -ε * (1 - θ) * a + θ * ε * ((1 - θ) / θ * a) + θ * c = θ * c := by
  field_simp; ring

/-- **AKMM, p. 872**: `D̂_t = θ D̂_{t−1}` with no initial dispersion gives `D̂_t = 0` for all
`t`: price dispersion does not affect the first-order dynamics. -/
theorem nk_dispersion_hat_zero {θ : ℝ} {D : ℕ → ℝ} (h0 : D 0 = 0)
    (hrec : ∀ t, D (t + 1) = θ * D t) (t : ℕ) : D t = 0 := by
  induction t with
  | zero => exact h0
  | succ t ih => rw [hrec t, ih, mul_zero]

/-- **AKMM, (18.A.5)–(18.A.6), p. 872, exact in logs**: with `C = Y`, (18.6) `C^{−σ} w = L^ψ`,
(18.11) `Y = A L/D` and natural output (18.13),
`log(w/A) + log µ = (σ + ψ)(log Y − log Y^n) + ψ log D`. Around the steady state
`w̄/Ā = 1/µ`, `D̄ = 1`, this is `ŵ − Â = (σ + ψ) x + ψ D̂`, and with `D̂ = 0` to first order
(`nk_dispersion_hat_zero`), `ŵ − Â = (σ + ψ)(Ŷ − Ŷ^n)`. -/
theorem eq_18_A_5_exact {σ ψ mu w A D Y L : ℝ} (hs : σ + ψ ≠ 0) (hmu : 0 < mu) (hw : 0 < w)
    (hA : 0 < A) (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Real.log (w / A) + Real.log mu =
      (σ + ψ) * nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) + ψ * Real.log D := by
  have hLe : L = D * Y / A := by rw [hprod]; field_simp
  have hlog := congrArg Real.log hlab
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' hw.ne', Real.log_rpow hY,
    Real.log_rpow hL, hLe, Real.log_div (by positivity) hA.ne',
    Real.log_mul hD.ne' hY.ne'] at hlog
  rw [nat_gap_loglinear hmu hA, Real.log_rpow hmu, Real.log_div hw.ne' hA.ne']
  have e1 : (σ + ψ) * (-1 / (σ + ψ) * Real.log mu) = -Real.log mu := by field_simp
  have e2 : (σ + ψ) * ((1 + ψ) / (σ + ψ) * Real.log A) = (1 + ψ) * Real.log A := by field_simp
  linear_combination hlog + e1 + e2

/-- **AKMM, (18.16), p. 544**: from (18.A.4) and `m_t = ŵ_t − Â_t = (σ + ψ) x_t`,
`π_t = κ x_t + β E_t π_{t+1}`, `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`. -/
theorem eq_18_16 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β θ σ ψ : ℝ} (hθ0 : θ ≠ 0)
    (hθ1 : θ ≠ 1) {m x pR infl : ℕ → Ω → ℝ} (hrec : ResetRecursion 𝔼 β θ m pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (hm : ∀ s, m s = (σ + ψ) • x s) (t : ℕ) :
    infl t = nfKappa β θ σ ψ • x t + β • 𝔼.E t (infl (t + 1)) := by
  rw [eq_18_A_4 𝔼 hθ0 hθ1 hrec h3 t, hm t, smul_smul, nfKappa]
  congr 2
  ring

/-- AKMM, p. 544: `κ > 0` for `θ ∈ (0, 1)`, `βθ < 1`, `σ + ψ > 0`. -/
theorem nk_kappa_pos {β θ σ ψ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hs : 0 < σ + ψ) : 0 < nfKappa β θ σ ψ := by
  unfold nfKappa
  have : 0 < 1 - β * θ := by linarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- **AKMM, p. 544**: "the slope of the Phillips curve is larger if prices are more flexible
(lower `θ`)": for `0 ≤ β ≤ 1` and `σ + ψ > 0`, `κ` is strictly decreasing in `θ` on `(0, 1)`. -/
theorem nk_kappa_antitone {β σ ψ θ₁ θ₂ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hs : 0 < σ + ψ)
    (h0 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ < 1) : nfKappa β θ₂ σ ψ < nfKappa β θ₁ σ ψ := by
  unfold nfKappa
  have hθ2 : 0 < θ₂ := by linarith
  have a1 : (1 - θ₂) / θ₂ < (1 - θ₁) / θ₁ := by
    rw [div_lt_div_iff₀ hθ2 h0]; nlinarith
  have a2 : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
  have b2 : 0 < 1 - β * θ₂ := by nlinarith
  have c1 : 0 ≤ (1 - θ₂) / θ₂ := div_nonneg (by linarith) hθ2.le
  have e : ∀ θ : ℝ, (1 - θ) * (1 - β * θ) * (σ + ψ) / θ =
      (1 - θ) / θ * (1 - β * θ) * (σ + ψ) := fun θ => by ring
  rw [e, e]
  have := mul_lt_mul_of_pos_of_nonneg' a1 a2 b2 (by
    have : 0 < (1 - θ₁) / θ₁ := div_pos (by linarith) h0
    linarith)
  nlinarith [mul_lt_mul_of_pos_right this hs]

/-- AKMM, p. 544: `κ` is increasing in the elasticity `σ + ψ` of marginal cost to output. -/
theorem nk_kappa_mono_sens {β θ σ ψ σ' ψ' : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (h : σ + ψ < σ' + ψ') : nfKappa β θ σ ψ < nfKappa β θ σ' ψ' := by
  unfold nfKappa
  have : 0 < (1 - θ) * (1 - β * θ) := mul_pos (by linarith) (by linarith)
  rw [div_lt_div_iff_of_pos_right hθ0]
  nlinarith

end AKMM.NominalFrictions
