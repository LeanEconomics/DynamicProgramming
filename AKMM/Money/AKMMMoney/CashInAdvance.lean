/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cash-in-advance model and the Friedman rule

AKMM, §17.3.2, pp. 504–505, and "The Friedman rule", p. 512. The household maximises
`∑ βᵗu(c_t, l_t)` subject to the cash-in-advance constraint `c_t ≤ m_t` (17.18) and the budget
(17.19); `βᵗλ_t` and `βᵗµ_t` are the multipliers on the budget and the CIA constraint, and the
first-order conditions are (17.20)–(17.23). In a stationary equilibrium `w = z`, `a = 0`,
`c = z(1 − l)`, and the multipliers are constant.

* `eq_17_19`: (17.17) in real balances is (17.19).
* `cia_stationary_growth`: with the money stock growing at the gross rate `γ` and a binding CIA,
  `p_{m,t}/p_{m,t+1} = γ`, `µ = λ(γ − β)/β`, an equilibrium needs `γ ≥ β`, and
  `u₂/u₁ = βz/γ`.
* `eq_17_24`: with a constant stock (`γ = 1`): `p_m = c/M`, `q = β`, `µ = λ(1 − β)/β > 0`,
  `q(1 + i) = 1`, and `u₂/u₁ = βz` (17.24).
* `cia_must_bind`: if the CIA never binds (`µ = 0`) the price of money grows at `1/β` and the
  transversality condition `βᵗλm_t → 0` fails.
* `cia_mrs_lt_mrt`: `βz < z`; with `u = log c + θ log l` CIA consumption `βz/(θ + β)` is below the
  frictionless `z/(θ + 1)` and leisure is higher (`cia_log_consumption`, `cia_log_compare`).
* `cia_friedman_rule`: with `γ = β` (money withdrawn at the rate of discount, taxes
  `τ_t = (1 − β)p_{m,t}M_t`), `µ = 0`, the frictionless condition `u₂/u₁ = z` holds, the nominal
  rate is zero, the transversality condition holds and the nominal stock vanishes.

The first-order conditions are taken as given, as in the book.
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.19)**, p. 504: with `m = p_{m,t}M`, `m′ = p_{m,t+1}M′`, the budget (17.17)
`q_ta_{t+1} + p_{m,t}M_{t+1} = a_t + p_{m,t}M_t − c_t + w_t(1 − l_t) − τ_t` is (17.19). -/
theorem eq_17_19 {c q a a' pt pt1 M M' w l τ : ℝ} (hpt1 : pt1 ≠ 0) :
    q * a' + pt * M' = a + pt * M - c + w * (1 - l) - τ ↔
      c + q * a' + pt / pt1 * (pt1 * M') = a + pt * M + w * (1 - l) - τ := by
  have : pt / pt1 * (pt1 * M') = pt * M' := by field_simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- AKMM, pp. 505 and 512: a stationary CIA equilibrium with money growing at the gross rate `γ`
(`M_t = M₀γᵗ`), constant consumption `c > 0`, constant multipliers `λ > 0`, `µ ≥ 0` and a binding
constraint `c = p_{m,t}M_t`. Then `p_{m,t}/p_{m,t+1} = γ`, `µ = λ(γ − β)/β`, so `γ ≥ β`, and
(17.20)–(17.21) give `u₂/u₁ = βz/γ`. -/
theorem cia_stationary_growth {β γ z c M0 lam mu U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) (hc : 0 < c) (hM0 : 0 < M0) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu))
    (hbind : ∀ t, c = pm t * (M0 * γ ^ t)) :
    (∀ t, pm t / pm (t + 1) = γ) ∧ mu = lam * (γ - β) / β ∧ β ≤ γ ∧ U2 / U1 = β * z / γ := by
  have hpm : ∀ t, pm t = c / (M0 * γ ^ t) := fun t => by
    rw [hbind t]; field_simp
  have hret : ∀ t, pm t / pm (t + 1) = γ := fun t => by
    rw [hpm, hpm, pow_succ]; field_simp
  have hmu' : mu = lam * (γ - β) / β := by
    have := h23 0; rw [hret] at this
    field_simp; linarith
  refine ⟨hret, hmu', ?_, ?_⟩
  · have : 0 ≤ lam * (γ - β) / β := hmu'.symm ▸ hmu
    have := (div_nonneg_iff.1 this)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · nlinarith [(mul_nonneg_iff_of_pos_left hlam).1 h1]
    · linarith
  · rw [h20, h21, hmu']
    have : lam + lam * (γ - β) / β = lam * γ / β := by field_simp; ring
    rw [this]
    field_simp

/-- **AKMM, (17.24)**, p. 505: in the stationary equilibrium with a constant money stock `M`, a
constant consumption `c > 0` and a binding CIA: `p_m = c/M` is constant, `q = β` (from (17.22)),
the nominal rate satisfies `q(1 + i) = 1`, the CIA multiplier is `µ = λ(1 − β)/β > 0`, and
`u₂(c, 1 − c/z)/u₁(c, 1 − c/z) = zλ/(λ + µ) = βz`. -/
theorem eq_17_24 {β z c M lam mu q i U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hc : 0 < c) (hM : 0 < M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z) (h22 : lam * q = β * lam)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu)) (hbind : ∀ t, c = pm t * M)
    (hfisher : q * (1 + i) = pm 0 / pm 1) :
    (∀ t, pm t = c / M) ∧ q = β ∧ q * (1 + i) = 1 ∧ mu = lam * (1 - β) / β ∧ 0 < mu ∧
      U2 / U1 = z * (lam / (lam + mu)) ∧ U2 / U1 = β * z := by
  have hb : ∀ t, c = pm t * (M * 1 ^ t) := fun t => by rw [one_pow, mul_one]; exact hbind t
  obtain ⟨hret, hmu', -, hmrs⟩ :=
    cia_stationary_growth hβ one_pos hc hM hlam hmu h20 h21 h23 hb
  have hq : q = β := by
    have := mul_left_cancel₀ hlam.ne' (h22.trans (mul_comm β lam))
    exact this
  refine ⟨fun t => by rw [hbind t]; field_simp, hq, by rw [hfisher, hret], hmu', ?_, ?_, ?_⟩
  · rw [hmu']; exact div_pos (mul_pos hlam (by linarith)) hβ
  · rw [h20, h21]; field_simp
  · rw [hmrs]; ring

/-- AKMM, p. 505: the CIA must bind in a stationary equilibrium. If it never binds (`µ_t = 0`)
with a constant `λ > 0`, (17.23) makes the price of money grow at `1/β`,
`p_{m,t} = p_{m,0}β^{−t}`, and with a constant stock `M > 0` the transversality condition
`βᵗλ_t m_t → 0` fails. -/
theorem cia_must_bind {β lam M : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hM : 0 < M)
    (hpm : ∀ t, 0 < pm t) (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + 0)) :
    (∀ t, pm t = pm 0 / β ^ t) ∧
      ¬ Tendsto (fun t : ℕ => β ^ t * lam * (pm t * M)) atTop (𝓝 0) := by
  have hstep : ∀ t, pm (t + 1) = pm t / β := fun t => by
    have := h23 t
    rw [add_zero] at this
    have h1 : pm t / pm (t + 1) = β := mul_left_cancel₀ hlam.ne' (this.trans (mul_comm β lam))
    have := (hpm (t + 1)).ne'
    field_simp at h1 ⊢
    linarith
  have hform : ∀ t, pm t = pm 0 / β ^ t := fun t => by
    induction t with
    | zero => simp
    | succ n ih => rw [hstep, ih, pow_succ]; field_simp
  refine ⟨hform, fun h => ?_⟩
  have hc : (fun t : ℕ => β ^ t * lam * (pm t * M)) = fun _ => lam * (pm 0 * M) := by
    funext t; rw [hform]; field_simp
  rw [hc] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  have : 0 < lam * (pm 0 * M) := by have := hpm 0; positivity
  linarith

/-- AKMM, p. 505: in the CIA economy the marginal rate of substitution between leisure and
consumption, `βz`, is below the marginal rate of transformation `z`. -/
theorem cia_mrs_lt_mrt {β z : ℝ} (hβ1 : β < 1) (hz : 0 < z) : β * z < z := by nlinarith

/-- AKMM, p. 505 (an instance): with `u(c, l) = log c + θ log l` and `l = 1 − c/z`, the condition
`u₂/u₁ = θc/l = κz` holds at `c ∈ (0, z)` iff `c = κz/(θ + κ)`. -/
theorem cia_log_consumption {θ κ z c : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hz : 0 < z) (hcz : c < z) :
    θ * c / (1 - c / z) = κ * z ↔ c = κ * z / (θ + κ) := by
  have hl : 0 < 1 - c / z := by rw [sub_pos, div_lt_one hz]; exact hcz
  rw [div_eq_iff hl.ne', eq_div_iff (by linarith)]
  constructor <;> intro h <;> field_simp at h ⊢ <;> linarith

/-- AKMM, p. 505: "in the CIA economy leisure is higher and consumption is lower": with
`u = log c + θ log l`, CIA consumption `βz/(θ + β)` is below the frictionless `z/(θ + 1)`. -/
theorem cia_log_compare {θ β z : ℝ} (hθ : 0 < θ) (hβ : 0 < β) (hβ1 : β < 1) (hz : 0 < z) :
    β * z / (θ + β) < 1 * z / (θ + 1) ∧ 1 - (1 * z / (θ + 1)) / z < 1 - (β * z / (θ + β)) / z := by
  have h1 : β * z / (θ + β) < 1 * z / (θ + 1) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_pos hθ hz]
  refine ⟨h1, ?_⟩
  have := div_lt_div_of_pos_right h1 hz
  linarith

/-- **AKMM, p. 505: the Friedman rule.** Withdraw money at the rate of discount, `M_t = M₀βᵗ`,
through the lump-sum tax `τ_t = (1 − β)p_{m,t}M_t`. In the stationary CIA equilibrium with
constant consumption the CIA multiplier is zero, the frictionless condition `u₂/u₁ = z` holds,
the return on money equals the real interest rate (`q = β`, nominal rate `i = 0`), the tax equals
`(1 − β)c`, the transversality condition `βᵗλm_t → 0` holds and the nominal stock vanishes. -/
theorem cia_friedman_rule {β z c M0 lam mu q i U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hc : 0 < c) (hM0 : 0 < M0) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z) (h22 : lam * q = β * lam)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu))
    (hbind : ∀ t, c = pm t * (M0 * β ^ t)) (hfisher : q * (1 + i) = pm 0 / pm 1) :
    mu = 0 ∧ U2 / U1 = z ∧ i = 0 ∧
      (∀ t, (1 - β) * (pm t * (M0 * β ^ t)) = (1 - β) * c) ∧
      Tendsto (fun t : ℕ => β ^ t * lam * (pm t * (M0 * β ^ t))) atTop (𝓝 0) ∧
      Tendsto (fun t : ℕ => M0 * β ^ t) atTop (𝓝 0) := by
  obtain ⟨hret, hmu', -, hmrs⟩ :=
    cia_stationary_growth hβ hβ hc hM0 hlam hmu h20 h21 h23 hbind
  have hq : q = β := mul_left_cancel₀ hlam.ne' (h22.trans (mul_comm β lam))
  have hpow : Tendsto (fun t : ℕ => β ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  refine ⟨by rw [hmu', sub_self, mul_zero, zero_div], by rw [hmrs]; field_simp, ?_,
    fun t => by rw [← hbind t], ?_, by simpa using hpow.const_mul M0⟩
  · rw [hret, hq] at hfisher
    have : β * i = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ.ne'
    · exact h
  · have : (fun t : ℕ => β ^ t * lam * (pm t * (M0 * β ^ t))) = fun t => β ^ t * (lam * c) := by
      funext t; rw [← hbind t]; ring
    rw [this]
    simpa using hpow.mul_const (lam * c)

end AKMM.Money
