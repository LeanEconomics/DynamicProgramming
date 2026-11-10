/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWHousehold

/-!
# §17.2.2–17.2.3: fiat money, interest on currency, Propositions 17.2.2 and 17.2.3 (i)

Miao, §17.2.2–17.2.3, pp. 572–577.

* Fiat money (§17.2.2): `bw_fiat_budget` (the mapping `m′/p = a′`, `w = 1`, `b = 0`, `r = 0`),
  `bw_fiat_quantity_theory` (`Ea(0) = M/p` determines `p = M/Ea(0)`, proportional to `M`),
  `bw_fiat_borrowing_raises_price` (with borrowing `b > 0`, `Ea(0; b) = Ea(0; 0) − b` and the
  price level rises), `bw_fiat_driven_out` (`b > Ea(0; 0)` gives `Ea(0; b) < 0`: no positive price
  level values fiat money).
* Explicit interest (§17.2.3): `eq_17_9`, `eq_17_10` (`τ = r̃M/p`), `bw_bewley_budget`,
  `bw_bewley_mapping` (`m′/p = â′`, `φ = M/p`, `r = r̃` maps the problem into (17.2));
  `BWBewleyEqm`: the stationary equilibrium with interest on currency financed by lump-sum taxes
  ((17.10), (17.11)); `eq_17_11` (market clearing `E m′/p = M/p` iff `Ea(r̃) = 0`).
* **Proposition 17.2.2** (`proposition_17_2_2`, `BWBewleyEqm.toHuggett`): a Bewley equilibrium
  has the allocation and interest rate of a Huggett equilibrium with `φ = M/p`.
* The back-solving method (`bw_backSolve`, `bw_backsolving`): from a Huggett equilibrium with
  limit `φ > 0` and any `M > 0`, `p = M/φ` and `τ = r̃M/p` give a Bewley equilibrium.
* `bw_bewley_real_balances_le`: real balances satisfy `r̃M/p ≤ e(s)` for every `s` (the largest
  supportable `M/p` is the natural limit `wl_min/r̃`).
* **Proposition 17.2.3**, first part (`proposition_17_2_3_rates`): the rates supportable by
  paying interest on currency are exactly the Huggett equilibrium rates for debt limits
  `0 < φ ≤ e_min/r̃`. The second part (the rate is below `1/β − 1`) is in `BWRate`.
* Implicit interest (`bw_implicit_*`): `1 + r = 1/(1 + g)`, `τ = (M_t/p_{t−1})r`, the budget is the
  Huggett budget with `φ = M_t/p_{t−1}`, money is retired at the rate `r/(1 + r)`.

**Departures.** (1) "The highest interest rate … equals that associated with the Huggett model
with the natural borrowing limit" relies on the `Ea(r)` curves shifting left as the limit rises
(Figure 17.3), a numerical finding; it is not proved. What is proved is the characterisation of
the supportable rates and the bound `φ ≤ e_min/r̃` (corrections).
-/

namespace Miao.IncompleteMarkets

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-! ### §17.2.2 Fiat money -/

/-- Miao, p. 572: with `m_{t+1}/p = a_{t+1}`, `w = 1`, `b = 0` and `r = 0`, the budget
`m′/p + c = m/p + l` with `m′ ≥ 0` is (17.2), `c + a′ = (1 + r)a + wl`, `a′ ≥ −b`. -/
theorem bw_fiat_budget (m m' p c l : ℝ) :
    (m' / p + c = m / p + l ∧ 0 ≤ m' / p) ↔
      (c + m' / p = (1 + 0) * (m / p) + 1 * l ∧ -0 ≤ m' / p) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by linarith, by simpa using h2⟩

/-- Miao, p. 573 (the quantity theory of money): with `M > 0` and `Ea(0) > 0`, the market-clearing
condition `Ea(0) = M/p` determines the price level `p = M/Ea(0)`, proportional to `M`. -/
theorem bw_fiat_quantity_theory {M m p : ℝ} (hM : 0 < M) (hm : 0 < m) :
    (0 < p ∧ m = M / p) ↔ p = M / m := by
  constructor
  · rintro ⟨hp, rfl⟩; field_simp
  · rintro rfl; exact ⟨div_pos hM hm, by field_simp⟩

/-- Miao, p. 573: doubling (scaling) the money stock scales the price level `p = M/Ea(0)`. -/
theorem bw_fiat_neutral (M m k : ℝ) : (k * M) / m = k * (M / m) := by ring

/-- Miao, p. 573: permitting borrowing `b > 0` lowers `Ea(0)` by `b` (Proposition 17.2.1) and,
when fiat money is still valued, raises the price level `p = M/Ea(0; b)`. -/
theorem bw_fiat_borrowing_raises_price (H : BWEconomy E) {M m0 b : ℝ}
    (hm0 : m0 ∈ H.EaSet 0 0 H.e) (hM : 0 < M) (hb : 0 < b) (hpos : 0 < m0 - b) :
    m0 - b ∈ H.EaSet 0 b H.e ∧ M / m0 < M / (m0 - b) := by
  refine ⟨?_, div_lt_div_of_pos_left hM hpos (by linarith)⟩
  rw [proposition_17_2_1]
  exact ⟨m0, hm0, rfl⟩

/-- Miao, p. 573: if `b > Ea(0; 0)` then `Ea(0; b) < 0` (Proposition 17.2.1), so no positive price
level clears the money market: inside money drives fiat money out. -/
theorem bw_fiat_driven_out (H : BWEconomy E) {M m0 b : ℝ} (hm0 : m0 ∈ H.EaSet 0 0 H.e)
    (hM : 0 < M) (hb : m0 < b) :
    m0 - b ∈ H.EaSet 0 b H.e ∧ m0 - b < 0 ∧ ∀ p, 0 < p → M / p ≠ m0 - b := by
  refine ⟨?_, by linarith, fun p hp h => ?_⟩
  · rw [proposition_17_2_1]; exact ⟨m0, hm0, rfl⟩
  · have := div_pos hM hp; linarith

/-! ### §17.2.3 Interest on currency: explicit interest -/

/-- Miao, (17.9), p. 573: the government budget constraint `τp_t + M_{t+1} = M_t + r̃M_t`. -/
def eq_17_9 (τ p M M' rt : ℝ) : Prop := τ * p + M' = M + rt * M

/-- Miao, (17.10), p. 574: with a constant money stock `M_t = M_{t+1} = M` and price level `p > 0`,
(17.9) is equivalent to `τ = r̃M/p`. -/
theorem eq_17_10 {τ p M rt : ℝ} (hp : 0 < p) : eq_17_9 τ p M M rt ↔ τ = rt * M / p := by
  unfold eq_17_9
  constructor
  · intro h; field_simp; linarith
  · rintro rfl; field_simp; ring

/-- Miao, p. 574: substituting `τ = r̃M/p` into the household budget
`m′/p + c ≤ (1 + r̃)m/p + wl − τ`. -/
theorem bw_bewley_budget {m m' p c w l rt M τ : ℝ} (hτ : τ = rt * M / p) :
    (m' / p + c ≤ (1 + rt) * m / p + w * l - τ) ↔
      (m' / p + c ≤ (1 + rt) * m / p + w * l - rt * M / p) := by
  rw [hτ]

/-- Miao, pp. 574–575: with `â = m/p`, `â′ = m′/p ≥ 0`, `φ = M/p` and `r = r̃`, the Bewley budget
`c + â′ = (1 + r̃)â + wl − r̃φ` is the Huggett budget (17.2) `c + a′ = (1 + r)a + wl` in
`a = â − φ`, and `â′ ≥ 0` is `a′ ≥ −φ`. -/
theorem bw_bewley_mapping (q q' c w l rt φ : ℝ) :
    (c + q' = (1 + rt) * q + w * l - rt * φ ↔
      c + (q' - φ) = (1 + rt) * (q - φ) + w * l) ∧ (0 ≤ q' ↔ -φ ≤ q' - φ) := by
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- The **Bewley economy with interest on currency** (Miao, §17.2.3, pp. 573–575): a stationary
equilibrium with a constant money stock `M > 0`, a constant price level `p > 0`, nominal interest
`r̃` on currency financed by the lump-sum tax `τ = r̃M/p` (17.10), real balances `q = m/p ≥ 0`
with the policy `h(q, s) = m′/p`, the household's Bellman equation for
`c + q′ = (1 + r̃)q + e(s) − τ`, `q′ ≥ 0`, market clearing (17.11) `∫ h dλ = M/p` and a stationary
distribution `λ` on `[0, ∞) × E`. -/
structure BWBewleyEqm (H : BWEconomy E) where
  M : ℝ
  p : ℝ
  τ : ℝ
  rt : ℝ
  V : ℝ → E → ℝ
  h : ℝ → E → ℝ
  lam : Measure (ℝ × E)
  M_pos : 0 < M
  p_pos : 0 < p
  gov : τ = rt * M / p
  isProb : IsProbabilityMeasure lam
  supp : lam {q | q.1 < -0} = 0
  bellman : H.Bellman rt 0 (fun s => H.e s - τ) V h
  integrable : Integrable (fun q => h q.1 q.2) lam
  clear : ∫ q, h q.1 q.2 ∂lam = M / p
  stationary : H.Stationary h lam

/-- Miao, (17.11), p. 574 and p. 575: for a stationary `λ` on real balances, market clearing
`E m′/p = M/p` is equivalent to `Ea(r̃) = 0` for the Huggett distribution `λ` shifted by `−φ`,
`φ = M/p`. -/
theorem eq_17_11 {lam : Measure (ℝ × E)} [IsProbabilityMeasure lam] {h : ℝ → E → ℝ}
    (hI : Integrable (fun q => h q.1 q.2) lam) (φ : ℝ) :
    ∫ q, h q.1 q.2 ∂lam = φ ↔
      ∫ p, (h (p.1 - -φ) p.2 + -φ) ∂(lam.map (bw_shift (-φ))) = 0 := by
  rw [bw_integral_shift hI]
  constructor <;> intro hh <;> linarith

/-- Real balances in a Bewley equilibrium: `φ = M/p > 0`. -/
theorem BWBewleyEqm.phi_pos {H : BWEconomy E} (B : BWBewleyEqm H) : 0 < B.M / B.p :=
  div_pos B.M_pos B.p_pos

/-- The tax in a Bewley equilibrium is `τ = r̃φ` with `φ = M/p`. -/
theorem BWBewleyEqm.tau_eq {H : BWEconomy E} (B : BWBewleyEqm H) : B.τ = B.rt * (B.M / B.p) := by
  rw [B.gov]; ring

/-- The Huggett equilibrium of **Proposition 17.2.2**: debt limit `φ = M/p`, rate `r̃`,
`V_H(a) = V(a + φ)`, `g(a) = h(a + φ) − φ`, distribution `λ` shifted by `−φ`. -/
noncomputable def BWBewleyEqm.toHuggett {H : BWEconomy E} (B : BWBewleyEqm H) :
    BWHuggettEqm H (B.M / B.p) where
  V := fun x s => B.V (x - -(B.M / B.p)) s
  g := fun x s => B.h (x - -(B.M / B.p)) s + -(B.M / B.p)
  r := B.rt
  lam := B.lam.map (bw_shift (-(B.M / B.p)))
  isProb := @bw_isProb_shift E _ _ B.isProb _
  supp := by
    have := @bw_supp_shift E _ B.lam 0 B.supp (-(B.M / B.p))
    simpa using this
  bellman := bw_bellman_shift B.bellman (by ring) (fun s => by rw [B.tau_eq]; ring)
  integrable := @bw_integrable_shift E _ B.lam B.isProb _ B.integrable _
  clear := by
    have := @bw_integral_shift E _ B.lam B.isProb _ B.integrable (-(B.M / B.p))
    rw [this, B.clear]; ring
  stationary := bw_stationary_shift B.stationary _

/-- **Proposition 17.2.2** (Miao, p. 575). A stationary equilibrium of the Bewley model with
interest on currency financed by lump-sum taxes has the same allocation and interest rate as an
equilibrium of Huggett's model with debt limit `φ = M/p`, the equilibrium real balances: the
rate is `r̃`, the asset policy is `g(q − φ) = h(q) − φ`, consumption agrees at corresponding
states, `c_H(q − φ, s) = c_B(q, s)`, and the distribution is that of real balances shifted
by `−φ`. -/
theorem proposition_17_2_2 {H : BWEconomy E} (B : BWBewleyEqm H) :
    B.toHuggett.r = B.rt ∧
    (∀ q s, B.toHuggett.g (q - B.M / B.p) s = B.h q s - B.M / B.p) ∧
    (∀ q s, (1 + B.toHuggett.r) * (q - B.M / B.p) + H.e s - B.toHuggett.g (q - B.M / B.p) s =
      (1 + B.rt) * q + (H.e s - B.τ) - B.h q s) ∧
    B.toHuggett.lam = B.lam.map (bw_shift (-(B.M / B.p))) := by
  refine ⟨rfl, fun q s => ?_, fun q s => ?_, rfl⟩
  · simp only [BWBewleyEqm.toHuggett, sub_neg_eq_add, sub_add_cancel]; ring
  · simp only [BWBewleyEqm.toHuggett, sub_neg_eq_add, sub_add_cancel]
    rw [B.tau_eq]; ring

/-- **The back-solving method** (Miao, p. 575, Steps 1–3): given a Huggett equilibrium with debt
limit `φ > 0` (Step 1 chooses `φ`; Step 2 is the Huggett equilibrium rate `r̃`, `Ea(r̃) = 0`) and a
money stock `M > 0`, set `p = M/φ` and `τ = r̃M/p` (Step 3). -/
noncomputable def bw_backSolve {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (hφ : 0 < φ)
    (M : ℝ) (hM : 0 < M) : BWBewleyEqm H where
  M := M
  p := M / φ
  τ := Q.r * M / (M / φ)
  rt := Q.r
  V := fun x s => Q.V (x - φ) s
  h := fun x s => Q.g (x - φ) s + φ
  lam := Q.lam.map (bw_shift φ)
  M_pos := hM
  p_pos := div_pos hM hφ
  gov := rfl
  isProb := @bw_isProb_shift E _ _ Q.isProb _
  supp := by
    have := @bw_supp_shift E _ Q.lam φ Q.supp φ
    simpa using this
  bellman := bw_bellman_shift Q.bellman (by ring) (fun s => by field_simp)
  integrable := @bw_integrable_shift E _ Q.lam Q.isProb _ Q.integrable _
  clear := by
    have := @bw_integral_shift E _ Q.lam Q.isProb _ Q.integrable φ
    rw [this, Q.clear, zero_add]; field_simp
  stationary := bw_stationary_shift Q.stationary _

/-- Miao, p. 575: the back-solved Bewley equilibrium has `p = M/φ`, `τ = r̃M/p = r̃φ`, the Huggett
rate `r̃`, and real balances `M/p = φ`. -/
theorem bw_backsolving {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (hφ : 0 < φ) (M : ℝ)
    (hM : 0 < M) :
    (bw_backSolve Q hφ M hM).p = M / φ ∧ (bw_backSolve Q hφ M hM).rt = Q.r ∧
      (bw_backSolve Q hφ M hM).τ = Q.r * φ ∧
      (bw_backSolve Q hφ M hM).M / (bw_backSolve Q hφ M hM).p = φ := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Q.r * M / (M / φ) = Q.r * φ; field_simp
  · change M / (M / φ) = φ; field_simp

/-- Miao, p. 575, Step 1: in a Bewley equilibrium the tax is payable in every state,
`τ = r̃M/p ≤ e(s)`; so real balances cannot exceed `e_min/r̃` when `r̃ > 0` ("the largest level of
real balances … is `wl_min/r̃`, the natural borrowing limit"). -/
theorem bw_bewley_real_balances_le {H : BWEconomy E} (B : BWBewleyEqm H) (s : E) :
    B.rt * (B.M / B.p) ≤ H.e s := by
  have := bw_natural_limit B.bellman s
  rw [B.tau_eq] at this
  linarith

/-- **Proposition 17.2.3**, first part (Miao, p. 576), in the precise form the argument gives: a
rate `r̃` is supported by paying interest on currency iff it is the equilibrium rate of the
Huggett economy for some debt limit `φ > 0`; any such `φ` satisfies `r̃φ ≤ e(s)` for all `s`
(it is at most the natural limit). -/
theorem proposition_17_2_3_rates (H : BWEconomy E) (r : ℝ) :
    (∃ B : BWBewleyEqm H, B.rt = r) ↔ ∃ φ, 0 < φ ∧ ∃ Q : BWHuggettEqm H φ, Q.r = r := by
  constructor
  · rintro ⟨B, rfl⟩; exact ⟨_, B.phi_pos, B.toHuggett, rfl⟩
  · rintro ⟨φ, hφ, Q, rfl⟩; exact ⟨bw_backSolve Q hφ 1 one_pos, rfl⟩

/-- Proposition 17.2.3 (support): a Huggett equilibrium with debt limit `φ > 0` has
`rφ ≤ e(s)` in every state. -/
theorem bw_huggett_limit_le_natural {H : BWEconomy E} {φ : ℝ} (Q : BWHuggettEqm H φ) (s : E) :
    Q.r * φ ≤ H.e s :=
  bw_natural_limit Q.bellman s

/-! ### §17.2.3 Interest on currency: implicit interest -/

/-- Miao, p. 576: `M_{t+1} = M_t(1 + g)` is equivalent to
`M_{t+1}/p_t = (M_t/p_{t−1})(p_{t−1}/p_t)(1 + g)`. -/
theorem bw_implicit_money {M M' p p₀ g : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) :
    M' = M * (1 + g) ↔ M' / p = M / p₀ * (p₀ / p) * (1 + g) := by
  constructor
  · rintro rfl; field_simp
  · intro h; field_simp at h; linarith

/-- Miao, p. 576: in a steady state with constant real balances `M_{t+1}/p_t = M_t/p_{t−1} > 0`
and `p_t/p_{t−1} = 1/(1 + r)`, `M_{t+1} = M_t(1 + g)` forces `1 + r = 1/(1 + g)`. -/
theorem bw_implicit_rate {M M' p p₀ g r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hM : 0 < M)
    (hg : M' = M * (1 + g)) (hreal : M' / p = M / p₀) (hinfl : p / p₀ = 1 / (1 + r)) :
    1 + r = 1 / (1 + g) := by
  have h1 : p₀ / p = 1 + r := by
    rw [← one_div_one_div (1 + r), ← hinfl]; field_simp
  have h2 := (bw_implicit_money hp hp₀).1 hg
  rw [hreal, h1] at h2
  have hM₀ : M / p₀ ≠ 0 := (div_pos hM hp₀).ne'
  have h3 : M / p₀ * ((1 + r) * (1 + g) - 1) = 0 := by linear_combination -h2
  have h4 : (1 + r) * (1 + g) = 1 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hM₀
    · linarith
  exact eq_one_div_of_mul_eq_one_left h4

/-- Miao, p. 576: by (17.9) with `r̃ = 0`, the lump-sum tax is `τ = −gM_t/p_t`, and with
`p_{t−1}/p_t = 1 + r`, `1 + g = 1/(1 + r)` it equals `(M_t/p_{t−1}) r`. -/
theorem bw_implicit_tax {τ M M' p p₀ g r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hr : 0 < 1 + r)
    (hgov : eq_17_9 τ p M M' 0) (hg : M' = M * (1 + g)) (hg' : 1 + g = 1 / (1 + r))
    (hinfl : p₀ / p = 1 + r) : τ = -(g * M / p) ∧ τ = M / p₀ * r := by
  unfold eq_17_9 at hgov
  have h1 : τ = -(g * M / p) := by
    rw [hg] at hgov; field_simp; linarith
  refine ⟨h1, ?_⟩
  have hg2 : g = -r / (1 + r) := by field_simp at hg' ⊢; linarith
  have hp' : p = p₀ / (1 + r) := by field_simp at hinfl ⊢; linarith
  rw [h1, hg2, hp']
  field_simp

/-- Miao, p. 576: with these taxes, the budget `m_{t+1}/p_t + c ≤ m_t/p_t + wl − (M_t/p_{t−1})r`
in the real balances `q_t = m_t/p_{t−1}` (so `m_t/p_t = (1 + r)q_t`) is the Bewley/Huggett budget
`c + q_{t+1} ≤ (1 + r)q_t + wl − rφ` with `φ = M_t/p_{t−1}`. -/
theorem bw_implicit_budget {m m' p p₀ c w l M r : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀)
    (hinfl : p₀ / p = 1 + r) :
    (m' / p + c ≤ m / p + w * l - M / p₀ * r) ↔
      (c + m' / p ≤ (1 + r) * (m / p₀) + w * l - r * (M / p₀)) := by
  have this : m / p = (1 + r) * (m / p₀) := by
    rw [← hinfl]; field_simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- Miao, p. 577: for `r > 0` the government retires money at the rate `r/(1 + r)`,
`M_{t+1} − M_t = −(r/(1 + r))M_t`, and prices fall, `p_t/p_{t−1} = 1/(1 + r) < 1`. -/
theorem bw_implicit_deflation {M M' g r : ℝ} (hr : 0 < r) (hg : M' = M * (1 + g))
    (hg' : 1 + g = 1 / (1 + r)) : M' - M = -(r / (1 + r)) * M ∧ 1 / (1 + r) < 1 := by
  have hr1 : (0 : ℝ) < 1 + r := by linarith
  refine ⟨?_, by rw [div_lt_one hr1]; linarith⟩
  have hg2 : g = 1 / (1 + r) - 1 := by linarith
  rw [hg, hg2]; field_simp; ring

end Miao.IncompleteMarkets
