/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMMoney.OLGEquilibrium

/-!
# Money growth in the overlapping-generations endowment economy

AKMM, §17.2.3, p. 501, and the remark on p. 514. The money stock grows at the gross rate
`1 + μ`, `μ ≥ 0`, `M_t = M₀(1 + μ)ᵗ`; the new money `μM_t` is handed to the old of date `t + 1` as
a lump-sum transfer, so cohort `t` has old-age income `ω_o + p_{m,t+1}μM_t` besides its money.

* `mgIsEquilibrium`; `mg_step_iff`: with `p_{m,t} > 0` the young hold the stock iff
  `p_{m,t+1} > 0` and `m_{t+1}(ω_y − (2 + μ)m_t) = (1 + μ)ω_o m_t`, `m_t = p_{m,t}M_t`.
* `mg_stationary_iff`: a stationary monetary equilibrium (constant real balances `m̄`) exists iff
  `ω_y > (1 + μ)ω_o`, and then `m̄ = (ω_y − (1 + μ)ω_o)/(2 + μ)`.
* `mg_return`: in it the real return on money is `1/(1 + μ)` (below one for `μ > 0`) and the
  price level `P = 1/p_m` grows at the money growth rate, `P_{t+1}/P_t = 1 + μ`.
* `mg_value_strictAntiOn`: the total real value of money `m̄` is strictly decreasing in `μ`, so
  it is lower than without money growth.

**Departure.** On p. 514 the book says the stationary equilibrium has "the rate of inflation
equal[ling] the inverse of the money growth rate". Inflation equals the money growth rate
(`mg_return`); it is the price of money that changes at the inverse rate.
-/

namespace AKMM.Money

/-- AKMM, p. 501: the money stock `M_t = M₀(1 + μ)ᵗ`. -/
noncomputable def mgStock (M0 μ : ℝ) (t : ℕ) : ℝ := M0 * (1 + μ) ^ t

/-- AKMM, p. 501: an equilibrium with money growth: at every date the young optimally buy the
whole stock `M_t`, given the transfer `p_{m,t+1}μM_t` they receive when old. -/
def mgIsEquilibrium (ωy ωo μ M0 : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ ∀ t, olgMoneyOptimal ωy (ωo + p (t + 1) * μ * mgStock M0 μ t) (p t) (p (t + 1))
    (mgStock M0 μ t)

/-- The money stock is positive. -/
theorem mgStock_pos {M0 μ : ℝ} (hM : 0 < M0) (hμ : 0 ≤ μ) (t : ℕ) : 0 < mgStock M0 μ t := by
  unfold mgStock; positivity

/-- AKMM, p. 501: `M_{t+1} = (1 + μ)M_t`. -/
theorem mgStock_succ (M0 μ : ℝ) (t : ℕ) : mgStock M0 μ (t + 1) = (1 + μ) * mgStock M0 μ t := by
  unfold mgStock; ring

/-- AKMM, p. 501: one step of an equilibrium with money growth. With `p_{m,t} > 0` the young buy
the stock iff `p_{m,t+1} > 0` and, in real balances `m_t = p_{m,t}M_t`,
`m_{t+1}(ω_y − (2 + μ)m_t) = (1 + μ)ω_o m_t`. -/
theorem mg_step_iff {ωy ωo μ M0 : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hμ : 0 ≤ μ) (hM : 0 < M0)
    {p : ℕ → ℝ} (t : ℕ) (hpt : 0 < p t) (hpt1 : 0 ≤ p (t + 1)) :
    olgMoneyOptimal ωy (ωo + p (t + 1) * μ * mgStock M0 μ t) (p t) (p (t + 1)) (mgStock M0 μ t)
      ↔ 0 < p (t + 1) ∧ p (t + 1) * mgStock M0 μ (t + 1) *
        (ωy - (2 + μ) * (p t * mgStock M0 μ t)) = (1 + μ) * ωo * (p t * mgStock M0 μ t) := by
  have hMt := mgStock_pos hM hμ t
  have hb : 0 < ωo + p (t + 1) * μ * mgStock M0 μ t := by positivity
  rw [olg_moneyOptimal_iff_pos hωy hb hpt hpt1, mgStock_succ]
  set Mt := mgStock M0 μ t
  constructor
  · rintro ⟨-, hd⟩
    have hdpos : 0 < olgDemand ωy (ωo + p (t + 1) * μ * Mt) (p (t + 1) / p t) := by
      rw [← hd]; positivity
    unfold olgDemand at hd hdpos
    split_ifs at hd hdpos with hc
    · exact absurd hdpos (lt_irrefl 0)
    · have h1 : 0 < p (t + 1) := by
        rcases hpt1.lt_or_eq with h' | h'
        · exact h'
        · rw [← h', zero_div, zero_mul] at hc
          exact absurd (by rw [zero_mul, zero_mul, add_zero]; exact hωo.le) hc
      refine ⟨h1, ?_⟩
      field_simp at hd
      linear_combination (-(1 + μ) * Mt) * hd
  · rintro ⟨h1, he⟩
    refine ⟨hMt.le, ?_⟩
    have hcore : p (t + 1) * ωy - (2 + μ) * (p t * p (t + 1) * Mt) - ωo * p t = 0 := by
      have h0 : ((1 + μ) * Mt) * (p (t + 1) * ωy - (2 + μ) * (p t * p (t + 1) * Mt) -
          ωo * p t) = 0 := by linear_combination he
      rcases mul_eq_zero.1 h0 with h' | h'
      · exact absurd h' (by positivity)
      · exact h'
    unfold olgDemand
    have hlt : (ωo + p (t + 1) * μ * Mt) * p t < p (t + 1) * ωy := by
      nlinarith [mul_pos (mul_pos h1 hMt) hpt, mul_pos hpt hMt]
    have hc : ¬ (p (t + 1) / p t * ωy ≤ ωo + p (t + 1) * μ * Mt) := by
      rw [not_le, div_mul_eq_mul_div, lt_div_iff₀ hpt]; linarith
    simp only [hc, ↓reduceIte]
    field_simp
    linear_combination -hcore

/-- **AKMM, p. 501: the stationary monetary equilibrium with money growth.** Prices with constant
real balances `p_{m,t}M_t = m̄ > 0` form an equilibrium iff `ω_y > (1 + μ)ω_o` and
`m̄ = (ω_y − (1 + μ)ω_o)/(2 + μ)`. -/
theorem mg_stationary_iff {ωy ωo μ M0 mb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hμ : 0 ≤ μ)
    (hM : 0 < M0) (hmb : 0 < mb) :
    mgIsEquilibrium ωy ωo μ M0 (fun t => mb / mgStock M0 μ t) ↔
      (1 + μ) * ωo < ωy ∧ mb = (ωy - (1 + μ) * ωo) / (2 + μ) := by
  have hpos : ∀ t, 0 < mb / mgStock M0 μ t := fun t => div_pos hmb (mgStock_pos hM hμ t)
  have hreal : ∀ t, mb / mgStock M0 μ t * mgStock M0 μ t = mb := fun t =>
    div_mul_cancel₀ _ (mgStock_pos hM hμ t).ne'
  have key : ∀ t, olgMoneyOptimal ωy (ωo + mb / mgStock M0 μ (t + 1) * μ * mgStock M0 μ t)
      (mb / mgStock M0 μ t) (mb / mgStock M0 μ (t + 1)) (mgStock M0 μ t) ↔
      mb * (ωy - (2 + μ) * mb) = (1 + μ) * ωo * mb := fun t => by
    rw [mg_step_iff (p := fun t => mb / mgStock M0 μ t) hωy hωo hμ hM t (hpos t) (hpos _).le]
    simp only [hreal]
    exact ⟨fun h => h.2, fun h => ⟨hpos _, h⟩⟩
  have h2 : (0 : ℝ) < 2 + μ := by linarith
  unfold mgIsEquilibrium
  simp only [key]
  constructor
  · rintro ⟨-, h⟩
    have e := h 0
    have e' : ωy - (2 + μ) * mb = (1 + μ) * ωo := by
      apply mul_left_cancel₀ hmb.ne'; linear_combination e
    refine ⟨?_, ?_⟩
    · nlinarith
    · rw [eq_div_iff h2.ne']; linarith
  · rintro ⟨-, h⟩
    refine ⟨fun t => (hpos t).le, fun _ => ?_⟩
    rw [h]; field_simp; ring

/-- AKMM, p. 501 and p. 522: along a stationary equilibrium with money growth the gross real
return on money is `1/(1 + μ)` and the price level `P_t = 1/p_{m,t}` grows at the money growth
rate: `P_{t+1}/P_t = 1 + μ` (inflation equals money growth, not its inverse as printed on
p. 514). -/
theorem mg_return {μ M0 mb : ℝ} (hμ : 0 ≤ μ) (hM : 0 < M0) (hmb : 0 < mb) (t : ℕ) :
    (mb / mgStock M0 μ (t + 1)) / (mb / mgStock M0 μ t) = 1 / (1 + μ) ∧
      (mb / mgStock M0 μ (t + 1))⁻¹ / (mb / mgStock M0 μ t)⁻¹ = 1 + μ ∧
      (0 < μ → 1 / (1 + μ) < 1) := by
  have hMt := mgStock_pos hM hμ t
  rw [mgStock_succ]
  refine ⟨?_, ?_, fun h => by rw [div_lt_one (by linarith)]; linarith⟩
  · field_simp
  · field_simp

/-- AKMM, p. 501: the real value of the money stock in the stationary equilibrium,
`m̄(μ) = (ω_y − (1 + μ)ω_o)/(2 + μ)`, is strictly decreasing in `μ ≥ 0`; in particular it is
lower than without money growth. -/
theorem mg_value_strictAntiOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictAntiOn (fun μ : ℝ => (ωy - (1 + μ) * ωo) / (2 + μ)) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end AKMM.Money
