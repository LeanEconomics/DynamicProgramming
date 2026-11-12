/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.Deterministic
import LifeCycleFiscalPolicy.RicardianEquivalence

/-!
# §21.2.3: deterministic dynastic models

AKMM, §21.2.3, pp. 644–649. Consumer `i` maximises `Σ βᵗu(cᵢ,ₜ)` subject to
`cᵢ,ₜ + aᵢ,ₜ₊₁ = (1 + r − δ)aᵢ,ₜ + εᵢw` and the no-Ponzi condition (fn 21). With
`R = 1 + r − δ` and `Aₜ = Raₜ` this is the deterministic problem (11.12) of AKMM Chapter 11
(`AKMM.Consumption.cd_Optimal`), with income `y = εᵢw`; `dy_Optimal` records the translation and
`dy_plan_iff` checks it. Optimality is from Chapter 11: the Euler equation (11.13) is necessary
(`eq_11_13`) and, with concave `u`, sufficient (`cd_optimal_of_euler`).

* **Steady-state indeterminacy** (p. 645): `dy_constant_optimal`: if `β(1 + r − δ) = 1`, holding
  any initial wealth forever is optimal; `dy_indeterminacy`: every wealth distribution summing to
  `k` with positive consumption is a steady state; `dy_indeterminacy_example`: two different ones;
  `dy_mpc`: the marginal propensity to consume out of wealth is `r − δ`.
* **OLG with altruism** (pp. 646–647): `ol_budget_iff`, `ol_IsIndirect`,
  `ol_isIndirect_prod` (instance), `ol_bellman_reduction`: the altruistic Bellman problem in
  `(c_y, c_o, a′)` has the same maximal values as the dynastic problem in `(R_y, a′)`;
  `ol_dynastic_utility` (Obstfeld–Rogoff's `utility_eq_tsum_iff`); `ol_indeterminacy`,
  `ol_example`: the steady-state wealth distribution is again indeterminate.
* **Discount-factor heterogeneity** (p. 647): `hd_constant_beta`, `hd_unique_beta`: constant
  positive consumption forces `βR = 1`, so agents with different `β` cannot both be at a steady
  state; `hd_strictAnti`, `hd_tendsto_zero`, `hd_assets_limit`: when `βᵢR < 1` consumption falls
  strictly to zero and wealth converges to `−εᵢw/(r − δ)`; `hd_strictMono`: `βR > 1` makes
  consumption rise forever, so `R = 1/max βᵢ`.
* **Return heterogeneity** (p. 649): `rh_lower_return_iff`: with common `β` and
  `βR_max = 1`, every agent with a lower return has `βRᵢ < 1`, and the results above apply.
-/

namespace AKMM.Inequality

open Filter Topology AKMM.Consumption

/-- AKMM, p. 645: consumer `i`'s problem `max Σ βᵗu(cₜ)` s.t. `cₜ + aₜ₊₁ = Raₜ + y`, `a₀` given,
no Ponzi games, `c > 0`, in Chapter 11's form with `Aₜ = Raₜ` (`R = 1 + r − δ`, `y = εᵢw`). -/
def dy_Optimal (β R a₀ y : ℝ) (u : ℝ → ℝ) (c a : ℕ → ℝ) : Prop :=
  cd_Optimal β R (R * a₀) u (fun _ => y) c (fun t => R * a t)

/-- AKMM, p. 645: the translation is exact: Chapter 11's plan with `Aₜ = Raₜ` is the Chapter 21
budget `cₜ + aₜ₊₁ = Raₜ + y` with `a₀` given, `c > 0` and `aₜ/Rᵗ → 0`. -/
theorem dy_plan_iff {R a₀ y : ℝ} (hR : 0 < R) {c a : ℕ → ℝ} :
    cd_Plan R (R * a₀) (fun _ => y) c (fun t => R * a t) ↔
      a 0 = a₀ ∧ (∀ t, c t + a (t + 1) = R * a t + y) ∧ (∀ t, 0 < c t) ∧
        Tendsto (fun t => a t / R ^ t) atTop (𝓝 0) := by
  have hfun : (fun t => R * a t / R ^ t) = fun t => R * (a t / R ^ t) := by
    funext t; ring
  constructor
  · rintro ⟨h0, hb, hc, ht⟩
    refine ⟨mul_left_cancel₀ hR.ne' h0, fun t => ?_, hc, ?_⟩
    · have := hb t
      have h2 : a (t + 1) = y + R * a t - c t := mul_left_cancel₀ hR.ne' this
      linarith
    · rw [hfun] at ht
      have := ht.const_mul R⁻¹
      simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul] at this
      exact this
  · rintro ⟨h0, hb, hc, ht⟩
    refine ⟨by simp only [h0], fun t => ?_, hc, ?_⟩
    · have := hb t
      simp only
      rw [show a (t + 1) = R * a t + y - c t by linarith]
      ring
    · rw [hfun]
      simpa using ht.const_mul R

/-- **AKMM, p. 645: holding wealth constant is optimal when `β(1 + r − δ) = 1`.** For
`0 < β < 1`, `βR = 1` and concave `u` (tangent inequalities with derivative `du`), the plan
`aₜ = a₀`, `cₜ = (R − 1)a₀ + y > 0` solves the consumer's problem. -/
theorem dy_constant_optimal {β R a₀ y : ℝ} {u du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hβR : β * R = 1) (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z))
    (hc : 0 < (R - 1) * a₀ + y) :
    dy_Optimal β R a₀ y u (fun _ => (R - 1) * a₀ + y) (fun _ => a₀) := by
  have hRb : R = β⁻¹ := eq_inv_of_mul_eq_one_right hβR
  have hR : 0 < R := by rw [hRb]; exact inv_pos.2 hβ
  have hRi : R⁻¹ = β := by rw [hRb, inv_inv]
  apply cd_optimal_of_euler hβ hR htan
  · refine ⟨rfl, fun t => by ring, fun _ => hc, ?_⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul (R * a₀)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    rw [div_eq_mul_inv, ← inv_pow, hRi]
  · intro t; rw [hβR, one_mul]
  · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  · rw [hRi]; exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _

/-- **AKMM, p. 645: steady-state indeterminacy of the wealth distribution.** Let
`β(1 + r − δ) = 1`, `Σᵢ εᵢ = 1`. For every wealth distribution `(aᵢ)` with `Σᵢ aᵢ = k` and
`cᵢ = (r − δ)aᵢ + εᵢw > 0`, holding `aᵢ` forever is optimal for every consumer, and aggregate
consumption is `(r − δ)k + w`. -/
theorem dy_indeterminacy {ι : Type*} [Fintype ι] {β r δ w k : ℝ} {u du : ℝ → ℝ}
    (ε a : ι → ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hss : β * (1 + r - δ) = 1)
    (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) (hk : ∑ i, a i = k)
    (hε : ∑ i, ε i = 1) (hc : ∀ i, 0 < (r - δ) * a i + ε i * w) :
    (∀ i, dy_Optimal β (1 + r - δ) (a i) (ε i * w) u (fun _ => (r - δ) * a i + ε i * w)
      (fun _ => a i)) ∧ ∑ i, ((r - δ) * a i + ε i * w) = (r - δ) * k + w := by
  refine ⟨fun i => ?_, ?_⟩
  · have h := dy_constant_optimal (a₀ := a i) (y := ε i * w) hβ hβ1 hss htan
      (by rw [show 1 + r - δ - 1 = r - δ by ring]; exact hc i)
    rwa [show 1 + r - δ - 1 = r - δ by ring] at h
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hk, hε, one_mul]

/-- AKMM, p. 645: the tangent inequality of `log`. -/
theorem dy_log_tangent (x z : ℝ) (hx : 0 < x) (hz : 0 < z) :
    Real.log x ≤ Real.log z + z⁻¹ * (x - z) := by
  have := Real.log_le_sub_one_of_pos (div_pos hx hz)
  rw [Real.log_div hx.ne' hz.ne'] at this
  have e : z⁻¹ * (x - z) = x / z - 1 := by field_simp
  linarith

/-- **AKMM, p. 645: "any combination is possible".** With log utility, `β = 1/2`, `r − δ = 1`,
`w = 1`, two consumers with `ε = 1/2` each and `k = 1`, both `(1/2, 1/2)` and `(0, 1)` are
steady-state wealth distributions. -/
theorem dy_indeterminacy_example :
    ∃ a b : Fin 2 → ℝ, a ≠ b ∧ ∑ i, a i = 1 ∧ ∑ i, b i = 1 ∧
      (∀ i, dy_Optimal (1 / 2) 2 (a i) (1 / 2) Real.log (fun _ => a i + 1 / 2) (fun _ => a i)) ∧
      ∀ i, dy_Optimal (1 / 2) 2 (b i) (1 / 2) Real.log (fun _ => b i + 1 / 2) (fun _ => b i) := by
  refine ⟨fun _ => 1 / 2, ![0, 1], fun h => ?_, by simp, by simp, fun i => ?_,
    fun i => ?_⟩
  · have := congrFun h 0
    norm_num at this
  · have h := dy_constant_optimal (β := 1 / 2) (R := 2) (a₀ := 1 / 2)
      (y := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) dy_log_tangent (by norm_num)
    convert h using 2
    ring
  · have hb : 0 ≤ ![(0 : ℝ), 1] i := by fin_cases i <;> simp
    have h := dy_constant_optimal (β := 1 / 2) (R := 2) (a₀ := ![(0 : ℝ), 1] i)
      (y := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num) dy_log_tangent (by linarith)
    convert h using 2
    ring

/-- **AKMM, p. 645: "a marginal propensity `r − δ`".** Steady-state consumption
`c = (r − δ)a + εw` has derivative `r − δ` in wealth. -/
theorem dy_mpc (r δ ε w a : ℝ) : HasDerivAt (fun x => (r - δ) * x + ε * w) (r - δ) a := by
  simpa using ((hasDerivAt_id a).const_mul (r - δ)).add_const (ε * w)

/-! ### Overlapping generations with altruism -/

/-- **AKMM, p. 646: the generation's budget.** `c_y + c_o/R + a′ = aR + w(ε_y + ε_o/R)` is
`R_y + a′ = aR + wε̂` with `R_y = c_y + c_o/R` and `ε̂ = ε_y + ε_o/R`. -/
theorem ol_budget_iff (cy co a' a R w εy εo : ℝ) :
    cy + co / R + a' = a * R + w * (εy + εo / R) ↔
      (cy + co / R) + a' = a * R + w * (εy + εo / R) := Iff.rfl

/-- AKMM, p. 646: `u(R) = max U(c_y, c_o)` s.t. `c_y + c_o/R̃ = R` (`R̃ = 1 + r − δ`): for every
`R` the maximum exists and equals `u(R)`. -/
def ol_IsIndirect (U : ℝ → ℝ → ℝ) (Rt : ℝ) (uR : ℝ → ℝ) : Prop :=
  ∀ R, IsGreatest {x | ∃ cy co, cy + co / Rt = R ∧ x = U cy co} (uR R)

/-- An instance: for `U(c_y, c_o) = c_y c_o` and `R̃ > 0`, `u(R) = R̃R²/4`. -/
theorem ol_isIndirect_prod {Rt : ℝ} (hRt : 0 < Rt) :
    ol_IsIndirect (fun cy co => cy * co) Rt (fun R => Rt * R ^ 2 / 4) := by
  intro R
  refine ⟨⟨R / 2, Rt * R / 2, by field_simp; ring, by ring⟩, ?_⟩
  rintro x ⟨cy, co, hb, rfl⟩
  have hco : co = Rt * (R - cy) := by field_simp at hb; linarith
  rw [hco]
  nlinarith [sq_nonneg (R - 2 * cy), hRt]

/-- **AKMM, p. 646: the altruistic problem is a dynastic problem.** For any continuation value
`V`, the two Bellman right-hand sides
`max_{c_y, c_o, a′} U(c_y, c_o) + βV(a′)` s.t. `c_y + c_o/R̃ + a′ = aR̃ + w(ε_y + ε_o/R̃)` and
`max_{R_y, a′} u(R_y) + βV(a′)` s.t. `R_y + a′ = aR̃ + wε̂` have the same maximum. -/
theorem ol_bellman_reduction {U : ℝ → ℝ → ℝ} {Rt : ℝ} {uR : ℝ → ℝ} (hU : ol_IsIndirect U Rt uR)
    (V : ℝ → ℝ) (β a w εy εo v : ℝ) :
    IsGreatest {x | ∃ cy co a', cy + co / Rt + a' = a * Rt + w * (εy + εo / Rt) ∧
        x = U cy co + β * V a'} v ↔
      IsGreatest {x | ∃ R a', R + a' = a * Rt + w * (εy + εo / Rt) ∧ x = uR R + β * V a'} v := by
  constructor
  · rintro ⟨⟨cy, co, a', hb, rfl⟩, hub⟩
    obtain ⟨⟨cy', co', hb', he'⟩, hle⟩ := hU (cy + co / Rt)
    have h1 : U cy co ≤ uR (cy + co / Rt) := hle ⟨cy, co, rfl, rfl⟩
    have h2 : U cy' co' + β * V a' ≤ U cy co + β * V a' :=
      hub ⟨cy', co', a', by rw [hb', hb], rfl⟩
    refine ⟨⟨cy + co / Rt, a', hb, by linarith⟩, ?_⟩
    rintro x ⟨R, b, hR, rfl⟩
    obtain ⟨⟨cy'', co'', hb'', he''⟩, -⟩ := hU R
    rw [he'']
    exact hub ⟨cy'', co'', b, by rw [hb'', hR], rfl⟩
  · rintro ⟨⟨R, a', hb, rfl⟩, hub⟩
    obtain ⟨⟨cy, co, hb', he⟩, -⟩ := hU R
    refine ⟨⟨cy, co, a', by rw [hb', hb], by rw [he]⟩, ?_⟩
    rintro x ⟨cy', co', b, hR, rfl⟩
    have h1 : U cy' co' ≤ uR (cy' + co' / Rt) := (hU _).2 ⟨cy', co', rfl, rfl⟩
    have h2 := hub ⟨cy' + co' / Rt, b, hR, rfl⟩
    linarith

/-- AKMM, p. 646, with Obstfeld–Rogoff (3.56)–(3.60): the altruistic recursion
`Wₜ = u(R_{y,t}) + βWₜ₊₁` gives the dynastic utility `W₀ = Σ βᵗu(R_{y,t})` iff `βⁿWₙ → 0`. -/
theorem ol_dynastic_utility {β : ℝ} {u : ℝ → ℝ} {Ry W : ℕ → ℝ}
    (hW : ∀ t, W t = u (Ry t) + β * W (t + 1)) (hsum : Summable fun t => β ^ t * u (Ry t)) :
    W 0 = ∑' t, β ^ t * u (Ry t) ↔ Tendsto (fun n => β ^ n * W n) atTop (𝓝 0) := by
  have h := ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.utility_eq_tsum_iff hW 0
    (by simpa using hsum)
  simpa using h

/-- **AKMM, p. 646: "the steady-state wealth distribution is indeterminate"** in the altruistic
OLG economy: with `β(1 + r − δ) = 1` and a concave indirect utility `u`, holding any bequest `a₀`
forever (`R_y = (r − δ)a₀ + wε̂ > 0`) solves the dynastic problem. -/
theorem ol_indeterminacy {β r δ w εy εo a₀ : ℝ} {uR du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hss : β * (1 + r - δ) = 1) (htan : ∀ x z, 0 < x → 0 < z → uR x ≤ uR z + du z * (x - z))
    (hc : 0 < (r - δ) * a₀ + w * (εy + εo / (1 + r - δ))) :
    dy_Optimal β (1 + r - δ) a₀ (w * (εy + εo / (1 + r - δ))) uR
      (fun _ => (r - δ) * a₀ + w * (εy + εo / (1 + r - δ))) (fun _ => a₀) := by
  have h := dy_constant_optimal (a₀ := a₀) (y := w * (εy + εo / (1 + r - δ))) hβ hβ1 hss htan
    (by rw [show 1 + r - δ - 1 = r - δ by ring]; exact hc)
  rwa [show 1 + r - δ - 1 = r - δ by ring] at h

/-- AKMM, p. 646: a concrete altruistic economy: `U(c_y, c_o) = log(c_y + c_o/R̃)` has indirect
utility `u = log`, which is concave, so `ol_indeterminacy` applies. -/
theorem ol_example {Rt : ℝ} :
    ol_IsIndirect (fun cy co => Real.log (cy + co / Rt)) Rt Real.log ∧
      ∀ x z : ℝ, 0 < x → 0 < z → Real.log x ≤ Real.log z + z⁻¹ * (x - z) := by
  refine ⟨fun R => ⟨⟨R, 0, by simp, by simp⟩, ?_⟩, dy_log_tangent⟩
  rintro x ⟨cy, co, hb, rfl⟩
  simp only [hb, le_refl]

/-! ### Discount-factor heterogeneity -/

/-- **AKMM, p. 647.** An optimal plan with constant positive consumption and `u′(c) ≠ 0` has
`βR = 1`. -/
theorem hd_constant_beta {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hu : ∀ x, 0 < x → HasDerivAt u (du x) x) (hopt : dy_Optimal β R a₀ y u c a)
    (hconst : ∀ t, c t = c 0) (hdu : du (c 0) ≠ 0) : β * R = 1 := by
  have h := eq_11_13 hβ hR hu hopt 0
  rw [hconst 1] at h
  have : (β * R - 1) * du (c 0) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · exact absurd h0 hdu

/-- **AKMM, p. 647: "the long-run wealth distribution is determinate".** Two consumers facing
the same `R` with `βᵢ ≠ βⱼ` cannot both have constant positive consumption (`u′ ≠ 0`). -/
theorem hd_unique_beta {βi βj R ai aj yi yj : ℝ} {u du : ℝ → ℝ} {ci cj ai' aj' : ℕ → ℝ}
    (hβi : 0 < βi) (hβj : 0 < βj) (hR : 0 < R) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hi : dy_Optimal βi R ai yi u ci ai') (hj : dy_Optimal βj R aj yj u cj aj')
    (hci : ∀ t, ci t = ci 0) (hcj : ∀ t, cj t = cj 0) (hdi : du (ci 0) ≠ 0)
    (hdj : du (cj 0) ≠ 0) : βi = βj := by
  have h1 := hd_constant_beta hβi hR hu hi hci hdi
  have h2 := hd_constant_beta hβj hR hu hj hcj hdj
  have : (βi - βj) * R = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- **AKMM, p. 647.** If `βR < 1` and `u′` is positive and strictly decreasing, optimal
consumption is strictly decreasing. -/
theorem hd_strictAnti {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : StrictAnti c := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  apply strictAnti_nat_of_succ_lt
  intro t
  have he := eq_11_13 hβ hR hu hopt t
  have hlt : du (c t) < du (c (t + 1)) := by
    have := hdu _ (hc (t + 1))
    have : β * R * du (c (t + 1)) < 1 * du (c (t + 1)) := mul_lt_mul_of_pos_right hβR this
    linarith
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at hlt; exact lt_irrefl _ hlt
  · have := hanti (hc t) (hc (t + 1)) h
    linarith

/-- **AKMM, p. 647: "all other consumers' consumption levels are converging to zero".** If
`βR < 1` (here `R = 1/β_max` and `β < β_max`) and `u′` is positive and strictly decreasing,
optimal consumption converges to `0`. -/
theorem hd_tendsto_zero {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : Tendsto c atTop (𝓝 0) := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  have hq : 1 < (β * R)⁻¹ := one_lt_inv_iff₀.2 ⟨mul_pos hβ hR, hβR⟩
  have hpow : ∀ t, du (c t) = (β * R)⁻¹ ^ t * du (c 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have he := eq_11_13 hβ hR hu hopt t
      have hne : β * R ≠ 0 := (mul_pos hβ hR).ne'
      rw [pow_succ, mul_comm ((β * R)⁻¹ ^ t), mul_assoc, ← ih, he]
      field_simp
  have hdiv : Tendsto (fun t => du (c t)) atTop atTop := by
    exact ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const (hdu _ (hc 0))).congr
      fun t => (hpow t).symm
  rw [tendsto_order]
  refine ⟨fun e he => Eventually.of_forall fun t => he.trans (hc t), fun e he => ?_⟩
  filter_upwards [hdiv.eventually_gt_atTop (du e)] with t ht
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at ht; exact lt_irrefl _ ht
  · have := hanti he (hc t) h
    linarith

/-- **AKMM, p. 647: "`0 = (r − δ)aᵢ + εᵢw`".** With `R = 1 + r − δ > 1` and `βR < 1`, the
wealth of the impatient consumer converges to `−y/(R − 1) = −εᵢw/(r − δ)` (the natural debt
limit), where consumption is zero. -/
theorem hd_assets_limit {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR1 : 1 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : Tendsto a atTop (𝓝 (-y / (R - 1))) := by
  have hR : 0 < R := one_pos.trans hR1
  have hopt1 : cd_Plan R (R * a₀) (fun _ => y) c (fun t => R * a t) := hopt.1
  obtain ⟨-, hb, hcpos, htvc⟩ := hopt1
  have hc0 := hd_tendsto_zero hβ hR hβR hu hdu hanti hopt
  have hdec := hd_strictAnti hβ hR hβR hu hdu hanti hopt
  have hq0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hq1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR1
  have hy : ∀ t : ℕ, Summable fun j : ℕ => R⁻¹ ^ j * y := fun _ =>
    (summable_geometric_of_lt_one hq0 hq1).mul_right y
  have hpv : ∀ t, Summable fun j => R⁻¹ ^ j * c (t + j) := fun t =>
    cd_summable_pv_cons (y := fun _ => y) (a := fun t => R * a t) hR hb (fun s => (hcpos s).le) t
      (cd_tvc_shift hR htvc t) (hy t)
  have hib : ∀ t, ∑' j, R⁻¹ ^ j * c (t + j) = R * a t + y * (1 - R⁻¹)⁻¹ := by
    intro t
    have := cd_intertemporal_budget (y := fun _ => y) (a := fun t => R * a t) hR hb t
      (cd_tvc_shift hR htvc t) (hy t) (hpv t)
    rw [this, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    ring
  have hbound : ∀ t, ∑' j, R⁻¹ ^ j * c (t + j) ≤ c t * (1 - R⁻¹)⁻¹ := by
    intro t
    rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hpv t)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    rw [mul_comm (c t)]
    exact mul_le_mul_of_nonneg_left (hdec.antitone (Nat.le_add_right t j)) (pow_nonneg hq0 j)
  have hnn : ∀ t, 0 ≤ ∑' j, R⁻¹ ^ j * c (t + j) := fun t =>
    tsum_nonneg fun j => mul_nonneg (pow_nonneg hq0 j) (hcpos _).le
  have hS : Tendsto (fun t => ∑' j, R⁻¹ ^ j * c (t + j)) atTop (𝓝 0) := by
    have hup : Tendsto (fun t => c t * (1 - R⁻¹)⁻¹) atTop (𝓝 0) := by
      simpa using hc0.mul_const (1 - R⁻¹)⁻¹
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hnn hbound
  have ha : ∀ t, a t = R⁻¹ * (∑' j, R⁻¹ ^ j * c (t + j) - y * (1 - R⁻¹)⁻¹) := by
    intro t
    rw [hib t]
    field_simp
    ring
  have hlim : -y / (R - 1) = R⁻¹ * (0 - y * (1 - R⁻¹)⁻¹) := by
    have h1 : R - 1 ≠ 0 := by linarith
    have h2 : R ≠ 0 := hR.ne'
    field_simp
    ring
  rw [hlim]
  exact ((hS.sub_const _).const_mul _).congr fun t => (ha t).symm

/-- **AKMM, p. 647.** If `βR > 1` (a consumer more patient than `1/R`), optimal consumption is
strictly increasing, so it is never constant: the steady-state `R` is `1/max βᵢ`. -/
theorem hd_strictMono {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : StrictMono c := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  apply strictMono_nat_of_lt_succ
  intro t
  have he := eq_11_13 hβ hR hu hopt t
  have hlt : du (c (t + 1)) < du (c t) := by
    have := hdu _ (hc (t + 1))
    have : 1 * du (c (t + 1)) < β * R * du (c (t + 1)) := mul_lt_mul_of_pos_right hβR this
    linarith
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at hlt; exact lt_irrefl _ hlt
  · have := hanti (hc (t + 1)) (hc t) h
    linarith

/-- **AKMM, p. 649: return heterogeneity.** With a common `β` and `βR_max = 1` for the highest
return, every consumer with `Rᵢ < R_max` has `βRᵢ < 1`, so by `hd_tendsto_zero` and
`hd_assets_limit` their consumption vanishes and their wealth tends to `−εᵢw/(Rᵢ − 1)`. -/
theorem rh_lower_return_iff {β Rmax Ri : ℝ} (hβ : 0 < β) (hmax : β * Rmax = 1) :
    β * Ri < 1 ↔ Ri < Rmax := by
  rw [← hmax]
  exact mul_lt_mul_iff_of_pos_left hβ

end AKMM.Inequality
