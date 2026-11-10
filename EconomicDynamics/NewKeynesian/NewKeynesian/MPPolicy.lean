/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.CPNKDiscretion
import NewKeynesian.MPQuadratic

/-!
# Monetary policy design: commitment versus discretion (Miao §19.2.3)

Miao, §19.2.3, pp. 635–640. The policy problem is the one of Miao, Examples 9.4.2 and 9.5.1:
the Phillips curve with cost-push shock (19.32) `π_t = κx_t + βE_tπ_{t+1} + u_t` is (9.23) with
`z_t = u_t`, and the loss `½∑βᵗ[π_t² + λ(x_t − x*)²]` is the one of Chapter 9. We reuse the
Chapter 9 modules `CPNKCommitment` and `CPNKDiscretion` (`ex942a` is the stable root `a` of
(9.29), `ex942Rule` the multiplier rule, `ex951θ = λ/(κ² + λ)`, `ex951pi` the discretionary
rule). As in Chapter 9 the expectations are replaced by the expected paths
`E_tu_{t+j} = ρ_u^ju_t` where a forward solution is involved; the laws of motion derived from
the multiplier rule are identities along every path of `u`.

**Strict inflation targeting** (p. 635). `mp_strict_targeting`: without cost-push shocks and
with `x* = 0`, the path `π = x = 0` satisfies (19.24) and has zero loss, every path has
nonnegative loss, and a path of zero loss has `π = x = 0`; `mp_strict_targeting_pi_zero`:
`π ≡ 0` forces `x ≡ 0` (`κ ≠ 0`); `mp_strict_targeting_rate`: then the IS curve (19.28) holds
iff `i_t = r^n_t`. `mp_cost_push_tradeoff` (p. 636): with (19.32), `π_t = 0` forces
`x_t = −u_t/κ ≠ 0` when `u_t ≠ 0`.

**Commitment** (pp. 636–637). `eq_19_33`, `eq_19_34`: the first-order conditions are the
derivatives of the Lagrangian of Chapter 9 (`ex942Lagr`, with the multiplier `β^{t+1}μ_{x,t+1}`
on (19.32)); for `π_0` the condition is (19.33) with `μ_{x0} = 0`. `mp_commit_rule`: every bounded
solution has `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + u_t/(1 − βaρ_u))` ("as in Chapter
9.4"). `mp_commit_x_law`, `mp_commit_pi_law`, `mp_commit_initial`: the laws
`x_t = ax_{t−1} − (aκ/λ)u_t/(1 − βaρ_u)`, `π_t = aπ_{t−1} + a(u_t − u_{t−1})/(1 − βaρ_u)` and the
initial values `x_0`, `π_0` exactly as printed. `mp_price_level`, `mp_price_level_stationary`:
the price level is `p_t = p_{−1} − βμ_{x,t+1}`, bounded, and
`p_t = ap_{t−1} + au_t/(1 − βaρ_u) + (1 − a)p_{−1} + aκx*/(1 − βa)`; the printed law
`p_t = ap_{t−1} + au_t/(1 − βaρ_u)` needs `(1 − a)p_{−1} + aκx*/(1 − βa) = 0` (with `p_{−1} = 0`:
`x* = 0`), `mp_price_level_printed_false`.

**Timeless perspective** (pp. 637–638). `eq_19_35`; `mp_timeless_euler`
(`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t`); `mp_timeless_coeff` (the coefficient
`κ/(λ(1 + β(1 − ρ − a)) + κ²)` equals `aκ/(λ(1 − βaρ))`, so the law is the commitment law);
`mp_timeless_solves`, `mp_timeless_unique`; `mp_timeless_pi`; `mp_commit_pi0`
(`π_0 = −(λ/κ)(x_0 − x*)` under precommitment); `mp_timeless_vs_commitment` (if `x_{−1} = x*`
the timeless path is the commitment path, and it is only then, for `a ≠ 0`).

**Discretion** (pp. 638–639). `mp_discretion_inflation`: the forward solution gives
`π_t = λκx*/(κ² + λ − βλ) + λu_t/(κ² + λ − βλρ_u)`; the book prints the shock coefficient as
`λκ/(κ² + λ − βλρ_u)`, which is false unless `κ = 1` (`mp_discretion_printed_false`).
`mp_inflation_bias`: the long-run inflation `λκx*/(κ² + (1 − β)λ)` is positive for
`κ, x* > 0`. `mp_a_lt_theta`, `mp_discretion_above_commitment`: `a < λ/(κ² + λ)`, and without
shocks discretionary inflation exceeds commitment inflation at every date;
`mp_discretion_gap_impact`: at the date of a cost-push shock the gap is
`(θ/(1 − βθ) − a/(1 − βa))κx* + (θ − a)u_0/((1 − βθρ)(1 − βaρ))`, increasing in `u_0`.

**Figure 19.3** (the qualitative facts stated, for all parameters with `κ, λ > 0`,
`0 < β < 1`, `x* = 0`, `ρ_u = 0`, one shock `u_0 = σ > 0`): `mp_fig_19_3_commitment` (inflation
rises on impact and is negative afterwards, the output gap is negative at every date and
serially correlated, `x_{t+1} = ax_t`) and `mp_fig_19_3_discretion` (inflation rises and the
output gap falls on impact, both are zero from the next period on). The plotted numbers are
computational and not formalised.
-/

namespace Miao.NewKeynesian

open Filter Topology MeasureTheory

/-! ### Strict inflation targeting -/

/-- **Strict inflation targeting is optimal** (Miao, p. 635). Without cost-push shocks and with
`x* = 0` (efficient steady state), let the loss be `∑βᵗ(π_t² + λx_t²)` (`β > 0`, `λ > 0`). The
path `π = x = 0` satisfies (19.24) `π_t = κx_t + βπ_{t+1}` and has loss `0`; every summable path
has loss `≥ 0`; a summable path with loss `0` is `π = x = 0`. -/
theorem mp_strict_targeting {β κ lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    (∀ t : ℕ, (fun _ : ℕ => (0 : ℝ)) t =
      κ * (fun _ : ℕ => (0 : ℝ)) t + β * (fun _ : ℕ => (0 : ℝ)) (t + 1)) ∧
      ∑' t : ℕ, β ^ t * ((0 : ℝ) ^ 2 + lam * (0 : ℝ) ^ 2) = 0 ∧
      (∀ pin x : ℕ → ℝ, 0 ≤ ∑' t, β ^ t * (pin t ^ 2 + lam * x t ^ 2)) ∧
      (∀ pin x : ℕ → ℝ, Summable (fun t => β ^ t * (pin t ^ 2 + lam * x t ^ 2)) →
        ∑' t, β ^ t * (pin t ^ 2 + lam * x t ^ 2) = 0 → ∀ t, pin t = 0 ∧ x t = 0) := by
  have hnn : ∀ (pin x : ℕ → ℝ) t, 0 ≤ β ^ t * (pin t ^ 2 + lam * x t ^ 2) := fun pin x t =>
    mul_nonneg (pow_nonneg hβ.le t) (by positivity)
  refine ⟨fun _ => by simp, by simp, fun pin x => tsum_nonneg (hnn pin x),
    fun pin x hs h0 t => ?_⟩
  have hle : β ^ t * (pin t ^ 2 + lam * x t ^ 2) ≤ 0 := by
    rw [← h0]
    exact hs.le_tsum t fun j _ => hnn pin x j
  have hz : pin t ^ 2 + lam * x t ^ 2 = 0 := by
    have := hnn pin x t
    have hb := pow_pos hβ t
    have h2 : β ^ t * (pin t ^ 2 + lam * x t ^ 2) = 0 := le_antisymm hle this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hb.ne'
    · exact h
  have h1 : pin t ^ 2 = 0 := by nlinarith [sq_nonneg (pin t), sq_nonneg (x t)]
  have h2 : x t ^ 2 = 0 := by nlinarith [sq_nonneg (pin t), sq_nonneg (x t)]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2⟩

/-- Miao, p. 635: with (19.24) and no cost-push shock, `π_t = 0` for all `t` implies `x_t = 0`
for all `t` (`κ ≠ 0`). -/
theorem mp_strict_targeting_pi_zero {β κ : ℝ} (hκ : κ ≠ 0) (pin x : ℕ → ℝ)
    (h24 : ∀ t, pin t = κ * x t + β * pin (t + 1)) (hpi : ∀ t, pin t = 0) : ∀ t, x t = 0 := by
  intro t
  have := h24 t
  rw [hpi t, hpi (t + 1), mul_zero, add_zero] at this
  rcases mul_eq_zero.1 this.symm with h | h
  · exact absurd h hκ
  · exact h

/-- Miao, p. 635 ("Hence, `i_t = r^n_t`"): at `π = x = 0` the IS curve (19.28)
`x_t = x_{t+1} − γ⁻¹(i_t − π_{t+1} − r^n_t)` holds iff `i_t = r^n_t` (`γ ≠ 0`). -/
theorem mp_strict_targeting_rate {γ i rn : ℝ} (hγ : γ ≠ 0) :
    ((0 : ℝ) = 0 - γ⁻¹ * (i - 0 - rn)) ↔ i = rn := by
  constructor
  · intro h
    have : γ⁻¹ * (i - rn) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (inv_ne_zero hγ)
    · linarith
  · intro h
    rw [h]
    ring

/-- **The short-run trade-off** (Miao, p. 636): with the cost-push shock in (19.32),
`π_t = π_{t+1} = 0` forces `x_t = −u_t/κ`, which is nonzero when `u_t ≠ 0` (`κ ≠ 0`). -/
theorem mp_cost_push_tradeoff {β κ x u : ℝ} (hκ : κ ≠ 0) (h32 : (0 : ℝ) = κ * x + β * 0 + u) :
    x = -u / κ ∧ (u ≠ 0 → x ≠ 0) := by
  have hx : x = -u / κ := by
    rw [eq_div_iff hκ]
    linarith
  refine ⟨hx, fun hu h => hu ?_⟩
  rw [h] at h32
  linarith

/-! ### Commitment: first-order conditions and the multiplier -/

/-- **(19.33)** (Miao, p. 636). For the Lagrangian of the commitment problem (`ex942Lagr` with
no shock-law multiplier, `u_t` the cost-push shock in place of `z_t`, multiplier
`β^{t+1}μ_{x,t+1}` on (19.32)) the derivative in `π_s` (`s < T`) is
`βˢ(π_s + βμ_{x,s+1} − βμ_{xs})`, where `μ_{x0} = 0`: at `s = 0` (the first-order condition for
`π_0`) this is `π_0 + βμ_{x1}`, i.e. (19.33) holds at `t = 0` with `μ_{x0} = 0`. -/
theorem eq_19_33 (β κ lam xs : ℝ) (μ u : ℕ → ℝ) (hμ0 : μ 0 = 0) {T s : ℕ} (hs : s < T)
    (pin x : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) T
      (cpPert pin s a) x u) (β ^ s * (pin s + β * μ (s + 1) - β * μ s)) 0 :=
  eq_9_25 β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) hμ0 hs pin x u

/-- **(19.34)** (Miao, p. 636): the derivative of the commitment Lagrangian in `x_s` (`s < T`) is
`βˢ(λ(x_s − x*) − βκμ_{x,s+1})`. -/
theorem eq_19_34 (β κ lam xs : ℝ) (μ u : ℕ → ℝ) {T s : ℕ} (hs : s < T) (pin x : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) T pin
      (cpPert x s a) u) (β ^ s * (lam * (x s - xs) - β * κ * μ (s + 1))) 0 :=
  eq_9_26 β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) hs pin x u

/-- **The commitment multiplier** (Miao, p. 636, "as in Chapter 9.4"). Let `0 < β < 1`,
`λ > 0`, `κ ≠ 0`, `|ρ_u| ≤ 1`, `a = ex942a` the smaller root of (9.29), and let the expected
shock path be `u_{t+1} = ρ_uu_t`. If bounded `π, x, μ` with `μ_{x0} = 0` satisfy (19.33),
(19.34) and (19.32) at every date, then
`μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + u_t/(1 − βaρ_u))` for every `t`. -/
theorem mp_commit_rule {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : κ ≠ 0) (hρ : |ρ| ≤ 1) (pin x u μ : ℕ → ℝ) (hu : ∀ t, u (t + 1) = ρ * u t)
    (h33 : ∀ t, pin t + β * μ (t + 1) - β * μ t = 0)
    (h34 : ∀ t, lam * (x t - xs) - β * κ * μ (t + 1) = 0)
    (h32 : ∀ t, pin t = κ * x t + β * pin (t + 1) + u t) (hμb : ∃ M, ∀ t, |μ t| ≤ M) :
    ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) (u t) := by
  obtain ⟨ha0, ha1, -, hroot, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have h28 : ∀ t, β * μ (t + 2) - ex942b β κ lam * μ (t + 1) + μ t = κ * xs / β + u t / β :=
    fun t => eq_9_28 hβ0.ne' hlam.ne' pin x u μ t (h33 t) (h33 (t + 1)) (h34 t) (h32 t)
  exact ex942_unique_bounded hβ0.ne' (mul_pos hβ0 ha0) (by nlinarith) hρ hroot u μ hu h28 hμb

/-- The multiplier rule in terms of `βμ`: `βμ_{x,t+1} = a(βμ_{xt}) − a(κx*/(1 − βa) +
u_t/(1 − βaρ_u))` (`β ≠ 0`). -/
theorem mp_beta_rule {β κ ρ xs a μ z : ℝ} (hβ : β ≠ 0) :
    β * ex942Rule β κ ρ xs a μ z =
      a * (β * μ) - a * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ)) := by
  simp only [ex942Rule]
  field_simp

/-- For a root `a` of (9.29) with `1 − βa ≠ 0`: `1 − a − aκ²/(λ(1 − βa)) = 0`. -/
theorem mp_root_identity {β κ lam a : ℝ} (hd1 : 1 - β * a ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    1 - a - a * κ ^ 2 * lam⁻¹ * (1 - β * a)⁻¹ = 0 := by
  have h : (1 - a - a * κ ^ 2 * lam⁻¹ * (1 - β * a)⁻¹) * (1 - β * a) =
      β * a ^ 2 - ex942b β κ lam * a + 1 := by
    have hinv : (1 - β * a)⁻¹ * (1 - β * a) = 1 := inv_mul_cancel₀ hd1
    simp only [ex942b, div_eq_mul_inv]
    linear_combination (-a * κ ^ 2 * lam⁻¹) * hinv
  rw [hroot] at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact h1
  · exact absurd h1 hd1

/-- **The commitment law for the output gap** (Miao, p. 637). Let `a` be a root of (9.29),
`β ≠ 0`, `1 − βa ≠ 0`, `μ` follow the multiplier rule along any path `u`,
and `x_t = x* + (βκ/λ)μ_{x,t+1}` ((19.34)). Then `x_{t+1} = ax_t − (aκ/λ)u_{t+1}/(1 − βaρ_u)`. -/
theorem mp_commit_x_law {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (u μ : ℕ → ℝ)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) (t : ℕ) :
    xs + β * κ / lam * μ (t + 2) =
      a * (xs + β * κ / lam * μ (t + 1)) - a * κ / lam * (u (t + 1) / (1 - β * a * ρ)) := by
  have hid := mp_root_identity hd1 hroot
  have hb := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ (t + 1)) (z := u (t + 1))
    hβ
  rw [← hμ (t + 1)] at hb
  have e : β * κ / lam * μ (t + 2) = κ * lam⁻¹ * (β * μ (t + 1 + 1)) := by ring
  rw [e, hb]
  simp only [div_eq_mul_inv]
  linear_combination xs * hid

/-- **The commitment law for inflation** (Miao, p. 637). With `π_t = β(μ_{xt} − μ_{x,t+1})`
((19.33)) and the multiplier rule along any path `u` (`β ≠ 0`):
`π_{t+1} = aπ_t + a(u_{t+1} − u_t)/(1 − βaρ_u)`. -/
theorem mp_commit_pi_law {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (u μ : ℕ → ℝ)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) (t : ℕ) :
    β * (μ (t + 1) - μ (t + 2)) =
      a * (β * (μ t - μ (t + 1))) + a * (u (t + 1) - u t) / (1 - β * a * ρ) := by
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ t) (z := u t) hβ
  have h2 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ (t + 1))
    (z := u (t + 1)) hβ
  rw [← hμ t] at h1
  rw [← hμ (t + 1)] at h2
  have h2' : β * μ (t + 2) = a * (β * μ (t + 1)) -
      a * (κ * xs / (1 - β * a) + u (t + 1) / (1 - β * a * ρ)) := h2
  linear_combination h1 - h2'

/-- **The commitment initial values** (Miao, p. 637). With `μ_{x0} = 0`:
`x_0 = x* + (βκ/λ)μ_{x1} = x* − (aκ/λ)(κx*/(1 − βa) + u_0/(1 − βaρ_u))` and
`π_0 = −βμ_{x1} = a(κx*/(1 − βa) + u_0/(1 − βaρ_u))`. -/
theorem mp_commit_initial {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (u μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) :
    xs + β * κ / lam * μ 1 =
        xs - a * κ / lam * (κ * xs / (1 - β * a) + u 0 / (1 - β * a * ρ)) ∧
      β * (μ 0 - μ 1) = a * (κ * xs / (1 - β * a) + u 0 / (1 - β * a * ρ)) := by
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ 0) (z := u 0) hβ
  rw [← hμ 0, hμ0, mul_zero, mul_zero, zero_sub] at h1
  constructor
  · have e : β * κ / lam * μ 1 = κ / lam * (β * μ 1) := by ring
    rw [e, h1]
    ring
  · rw [hμ0]
    simp only [zero_add] at h1
    linarith

/-- **The price level under commitment** (Miao, p. 637). Let `P_t = p_{t−1}` (so `P_0 = p_{−1}`)
with `p_t − p_{t−1} = π_t = β(μ_{xt} − μ_{x,t+1})`, `μ_{x0} = 0` and the multiplier rule. Then
`p_t = p_{−1} − βμ_{x,t+1}` and
`p_t = ap_{t−1} + au_t/(1 − βaρ_u) + (1 − a)p_{−1} + aκx*/(1 − βa)`. -/
theorem mp_price_level {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (u μ P : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hP : ∀ t, P (t + 1) - P t = β * (μ t - μ (t + 1))) :
    (∀ t, P (t + 1) = P 0 - β * μ (t + 1)) ∧
      ∀ t, P (t + 1) = a * P t + a * u t / (1 - β * a * ρ) + (1 - a) * P 0 +
        a * (κ * xs / (1 - β * a)) := by
  have hlev : ∀ t, P (t + 1) = P 0 - β * μ (t + 1) := by
    intro t
    induction t with
    | zero =>
      have h := hP 0
      rw [hμ0] at h
      linarith
    | succ n ih => linarith [hP (n + 1)]
  refine ⟨hlev, fun t => ?_⟩
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ t) (z := u t) hβ
  rw [← hμ t] at h1
  have hPt : P t = P 0 - β * μ t := by
    cases t with
    | zero => rw [hμ0]; ring
    | succ n => exact hlev n
  rw [hlev t, h1, hPt]
  ring

/-- **The printed price-level law fails for `x* ≠ 0`** (Miao, p. 637). With the normalisation
`p_{−1} = 0`, `0 < a`, `1 − βa ≠ 0` and `κx* ≠ 0`, `p_0 ≠ ap_{−1} + au_0/(1 − βaρ_u)`. -/
theorem mp_price_level_printed_false {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hκx : κ * xs ≠ 0) (u μ P : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hP : ∀ t, P (t + 1) - P t = β * (μ t - μ (t + 1))) (hP0 : P 0 = 0) :
    P 1 ≠ a * P 0 + a * u 0 / (1 - β * a * ρ) := by
  have h := (mp_price_level hβ u μ P hμ0 hμ hP).2 0
  rw [hP0] at h ⊢
  intro h'
  rw [h'] at h
  have : a * (κ * xs / (1 - β * a)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ha h1
  · exact hκx (by rw [div_eq_zero_iff] at h1; tauto)

/-- **The price level is stationary** (Miao, p. 637). If `0 ≤ a < 1`, `|u_t| ≤ U` and
`1 − βaρ_u ≠ 0`, the commitment multiplier satisfies
`|βμ_{xt}| ≤ a(|κx*/(1 − βa)| + U/|1 − βaρ_u|)/(1 − a)`, so `p_t = p_{−1} − βμ_{x,t+1}` is
bounded. -/
theorem mp_price_level_stationary {β κ ρ xs a U : ℝ} (hβ : β ≠ 0) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u μ : ℕ → ℝ) (hU : ∀ t, |u t| ≤ U) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) :
    ∀ t, |β * μ t| ≤ a * (|κ * xs / (1 - β * a)| + U / |1 - β * a * ρ|) / (1 - a) := by
  set B := a * (|κ * xs / (1 - β * a)| + U / |1 - β * a * ρ|)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hB : 0 ≤ B := mul_nonneg ha0 (by positivity)
  intro t
  rw [le_div_iff₀ (by linarith)]
  induction t with
  | zero => rw [hμ0]; simp only [mul_zero, abs_zero, zero_mul]; exact hB
  | succ n ih =>
    have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ n) (z := u n) hβ
    rw [← hμ n] at h1
    rw [h1]
    have hk : |κ * xs / (1 - β * a) + u n / (1 - β * a * ρ)| ≤
        |κ * xs / (1 - β * a)| + U / |1 - β * a * ρ| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div]
      exact div_le_div_of_nonneg_right (hU n) (abs_nonneg _)
    have h2 : |a * (β * μ n) - a * (κ * xs / (1 - β * a) + u n / (1 - β * a * ρ))| ≤
        a * |β * μ n| + B := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul a, abs_mul a, abs_of_nonneg ha0]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk ha0)
    have h3 : a * |β * μ n| ≤ a * (B / (1 - a)) := by
      apply mul_le_mul_of_nonneg_left _ ha0
      rw [le_div_iff₀ (by linarith)]
      exact ih
    have h4 : a * (B / (1 - a)) + B = B / (1 - a) := by
      have : (1 : ℝ) - a ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
    have h5 : |a * (β * μ n) - a * (κ * xs / (1 - β * a) + u n / (1 - β * a * ρ))| ≤
        B / (1 - a) := by linarith
    rwa [le_div_iff₀ (by linarith)] at h5

/-! ### The timeless perspective -/

/-- **(19.35)** (Miao, p. 637). If (19.33) holds at `t` and (19.34) at `t` and `t − 1`
(`κ ≠ 0`), then `π_t = −(λ/κ)(x_t − x_{t−1})`. -/
theorem eq_19_35 {β κ lam xs pin x xm μ μ' : ℝ} (hκ : κ ≠ 0)
    (h33 : pin + β * μ' - β * μ = 0) (h34 : lam * (x - xs) - β * κ * μ' = 0)
    (h34m : lam * (xm - xs) - β * κ * μ = 0) : pin = -(lam / κ) * (x - xm) := by
  field_simp
  linear_combination κ * h33 + h34 - h34m

/-- Miao, p. 637: substituting (19.35) at `t` and `t + 1` into (19.32) gives
`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t` (`κ, λ ≠ 0`). -/
theorem mp_timeless_euler {β κ lam pin pin' x x' xm u : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (h35 : pin = -(lam / κ) * (x - xm)) (h35' : pin' = -(lam / κ) * (x' - x))
    (h32 : pin = κ * x + β * pin' + u) :
    (1 + β + κ ^ 2 / lam) * x = β * x' + xm - κ / lam * u := by
  rw [h35, h35'] at h32
  field_simp at h32 ⊢
  linear_combination (-1) * h32

/-- Miao, pp. 637–638: for a root `a` of (9.29) with `a ≠ 0`, the timeless coefficient
`κ/(λ(1 + β(1 − ρ − a)) + κ²)` equals `aκ/(λ(1 − βaρ))` (`λ ≠ 0`, `1 − βaρ ≠ 0`), so the law
`x_t = ax_{t−1} − κu_t/(λ(1 + β(1 − ρ − a)) + κ²)` is the commitment law of p. 637
("the same as that under optimal commitment"). -/
theorem mp_timeless_coeff {β κ lam ρ a : ℝ} (ha : a ≠ 0) (hlam : lam ≠ 0)
    (hd2 : 1 - β * a * ρ ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    lam * (1 + β * (1 - ρ - a)) + κ ^ 2 = lam * (1 - β * a * ρ) / a ∧
      κ / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) = a * κ / (lam * (1 - β * a * ρ)) := by
  have hb := ex942_b_eq ha hroot
  simp only [ex942b] at hb
  have e : lam * (1 + β * (1 - ρ - a)) + κ ^ 2 = lam * (1 - β * a * ρ) / a := by
    have : κ ^ 2 = lam * (β * a + a⁻¹ - 1 - β) := by
      field_simp at hb ⊢
      linear_combination hb
    rw [this]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e]
  field_simp

/-- Miao, p. 637 ("Solving yields"): if `a` is a root of (9.29), `a ≠ 0`, `λ ≠ 0`,
`1 − βaρ ≠ 0`, `x_t = ax_{t−1} + cu_t` with `c = −aκ/(λ(1 − βaρ))`, and
`E_tx_{t+1} = ax_t + cρu_t` (`E_tu_{t+1} = ρu_t`), then
`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t`. -/
theorem mp_timeless_solves {β κ lam ρ a xm u : ℝ} (ha : a ≠ 0) (hlam : lam ≠ 0)
    (hd2 : 1 - β * a * ρ ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    let c := -(a * κ / (lam * (1 - β * a * ρ)))
    let x := a * xm + c * u
    ex942b β κ lam * x = β * (a * x + c * ρ * u) + xm - κ / lam * u := by
  intro c x
  rw [ex942_b_eq ha hroot]
  simp only [x, c]
  field_simp
  ring

/-- **Uniqueness of the timeless solution** (Miao, p. 637). Let `0 < β`, `0 < βa < 1`,
`|ρ| ≤ 1`, `a` a root of (9.29), `u_{t+1} = ρu_t` (expected path) and `X_s = x_{s−1}` bounded with
`βX_{s+2} − (1 + β + κ²/λ)X_{s+1} + X_s = (κ/λ)u_s` (the timeless equation at date `s`). Then
`x_s = ax_{s−1} − aκu_s/(λ(1 − βaρ))`. -/
theorem mp_timeless_unique {β κ lam ρ a : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a) (ha1 : β * a < 1)
    (hρ : |ρ| ≤ 1) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (u X : ℕ → ℝ)
    (hu : ∀ t, u (t + 1) = ρ * u t)
    (heq : ∀ s, β * X (s + 2) - ex942b β κ lam * X (s + 1) + X s = κ / lam * u s)
    (hXb : ∃ M, ∀ t, |X t| ≤ M) :
    ∀ s, X (s + 1) = a * X s - a * κ / lam * (u s / (1 - β * a * ρ)) := by
  have h := ex942_unique_bounded (xs := 0) hβ ha0 ha1 hρ hroot (fun s => β * (κ / lam) * u s) X
    (fun t => by simp only [hu t]; ring) (fun s => by rw [heq s]; field_simp; ring) hXb
  intro s
  rw [h s, ex942Rule]
  field_simp
  ring

/-- Miao, p. 638: substituting the timeless law `x_t = ax_{t−1} + cu_t`,
`c = −κ/(λ(1 + β(1 − ρ − a)) + κ²)`, into (19.35) gives
`π_t = (λ/κ)(1 − a)x_{t−1} + λu_t/(λ(1 + β(1 − ρ − a)) + κ²)` (`κ ≠ 0`). -/
theorem mp_timeless_pi {β κ lam ρ a xm u : ℝ} (hκ : κ ≠ 0) :
    -(lam / κ) * ((a * xm - κ / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) * u) - xm) =
      lam / κ * (1 - a) * xm + lam / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) * u := by
  field_simp
  ring

/-- Miao, p. 638: under optimal precommitment `μ_{x0} = 0`, so (19.33) and (19.34) at `t = 0`
give `π_0 = −(λ/κ)(x_0 − x*)` (`κ ≠ 0`), which differs from (19.35) at `t = 0` unless
`x_{−1} = x*`. -/
theorem mp_commit_pi0 {β κ lam xs pin x μ' : ℝ} (hκ : κ ≠ 0) (h33 : pin + β * μ' - β * 0 = 0)
    (h34 : lam * (x - xs) - β * κ * μ' = 0) : pin = -(lam / κ) * (x - xs) := by
  field_simp
  linear_combination κ * h33 + h34

/-- **Timeless perspective versus commitment** (Miao, p. 638). Let `a` be a root of (9.29) with
`a ≠ 0`, `β ≠ 0`, `1 − βa ≠ 0`, `μ` the commitment multiplier (`μ_{x0} = 0`, the rule along
`u`), `x^c_t = x* + (βκ/λ)μ_{x,t+1}` the commitment output gap, and `x^{tl}` the timeless path
`x^{tl}_t = ax^{tl}_{t−1} − (aκ/λ)u_t/(1 − βaρ)` from `x^{tl}_{−1} = X_0`
(`X_{t+1} = x^{tl}_t`). Then `x^{tl} = x^c` at every date iff `X_0 = x*`. -/
theorem mp_timeless_vs_commitment {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0)
    (u μ X : ℕ → ℝ) (hμ0 : μ 0 = 0) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hX : ∀ t, X (t + 1) = a * X t - a * κ / lam * (u t / (1 - β * a * ρ))) :
    (∀ t, X (t + 1) = xs + β * κ / lam * μ (t + 1)) ↔ X 0 = xs := by
  have hx0 : xs + β * κ / lam * μ 1 = a * xs - a * κ / lam * (u 0 / (1 - β * a * ρ)) := by
    rw [(mp_commit_initial (lam := lam) hβ u μ hμ0 hμ).1]
    have hid := mp_root_identity hd1 hroot
    simp only [div_eq_mul_inv]
    linear_combination xs * hid
  constructor
  · intro h
    have h0 := h 0
    rw [hX 0, hx0] at h0
    have : a * (X 0 - xs) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 ha
    · linarith
  · intro h0 t
    induction t with
    | zero => rw [hX 0, hx0, h0]
    | succ n ih =>
      rw [hX (n + 1), ih, mp_commit_x_law hβ hd1 hroot u μ hμ n]

/-! ### Discretion -/

/-- The discretionary rule in the book's closed form:
`θ(κx*/(1 − βθ) + u/(1 − βθρ)) = λκx*/(κ² + λ − βλ) + λu/(κ² + λ − βλρ)`. -/
theorem mp_ex951pi_closed {β κ lam ρ xs u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) :
    ex951pi β κ lam ρ xs u =
      lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam / (κ ^ 2 + lam - β * lam * ρ) * u := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  have hk : κ ^ 2 + lam ≠ 0 := by positivity
  have e1 : κ ^ 2 + lam - β * lam = (κ ^ 2 + lam) * (1 - β * ex951θ κ lam) := by
    simp only [ex951θ]
    field_simp
  have e2 : κ ^ 2 + lam - β * lam * ρ = (κ ^ 2 + lam) * (1 - β * ex951θ κ lam * ρ) := by
    simp only [ex951θ]
    field_simp
  rw [e1, e2, ex951pi]
  simp only [ex951θ] at hd1 hd2 ⊢
  field_simp

/-- **Discretionary inflation** (Miao, p. 638). For `0 < β < 1`, `λ > 0`, `|ρ_u| ≤ 1`, let
`p_j = E_tπ_{t+j}` be bounded with `p_j = θ(κx* + βp_{j+1} + ρ_u^ju_t)`, `θ = λ/(κ² + λ)` (the
discretionary condition (9.43)). Then
`π_t = θ∑ⱼβʲθʲ(κx* + E_tu_{t+j}) = λκx*/(κ² + λ − βλ) + λu_t/(κ² + λ − βλρ_u)`. -/
theorem mp_discretion_inflation {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (u : ℝ) (p : ℕ → ℝ)
    (hp : ∀ j, p j = ex951θ κ lam * (κ * xs + β * p (j + 1) + ρ ^ j * u))
    (hb : ∃ M, ∀ j, |p j| ≤ M) :
    p 0 = ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * u) ∧
      p 0 = lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam / (κ ^ 2 + lam - β * lam * ρ) * u := by
  have h1 := ex951_forward hβ0 hβ1 hlam hρ u p hp hb
  refine ⟨h1, ?_⟩
  rw [h1, ex951_series hβ0 hβ1 hlam hρ u, mp_ex951pi_closed hβ0 hβ1 hlam hρ]

/-- **The printed discretionary coefficient is wrong** (Miao, p. 638). The book's closed form
`λκx*/(κ² + λ − βλ) + λκu_t/(κ² + λ − βλρ_u)` differs from the discretionary inflation rate
whenever `κ ≠ 1` and `u_t ≠ 0` (`0 < β < 1`, `λ > 0`, `|ρ_u| ≤ 1`). -/
theorem mp_discretion_printed_false {β κ lam ρ xs u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) (hκ : κ ≠ 1) (hu : u ≠ 0) :
    ex951pi β κ lam ρ xs u ≠
      lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam * κ / (κ ^ 2 + lam - β * lam * ρ) * u := by
  rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ]
  intro h
  have hden : 0 < κ ^ 2 + lam - β * lam * ρ := by
    have h1 : β * ρ ≤ |β * ρ| := le_abs_self _
    rw [abs_mul, abs_of_pos hβ0] at h1
    have h2 : |ρ| * β ≤ β := mul_le_of_le_one_left hβ0.le hρ
    nlinarith [sq_nonneg κ]
  have : lam / (κ ^ 2 + lam - β * lam * ρ) * u * (1 - κ) = 0 := by
    have e : lam * κ / (κ ^ 2 + lam - β * lam * ρ) * u =
        κ * (lam / (κ ^ 2 + lam - β * lam * ρ) * u) := by ring
    rw [e] at h
    linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (div_pos hlam hden).ne'
    · exact hu h2
  · exact hκ (by linarith)

/-- **Inflation bias** (Miao, p. 638): without shocks, discretionary inflation is
`λκx*/(κ² + (1 − β)λ)`, positive for `κ, x*, λ > 0`, `0 < β < 1`. -/
theorem mp_inflation_bias {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (hκ : 0 < κ) (hxs : 0 < xs) :
    ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) ∧
      0 < ex951pi β κ lam ρ xs 0 := by
  have e : ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) := by
    rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ, mul_zero, add_zero]
    congr 1
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 < (1 - β) * lam := mul_pos (by linarith) hlam
  positivity

/-- Miao, p. 638: the commitment root is below the discretionary coefficient,
`a < θ = λ/(κ² + λ)` (`0 < β < 1`, `λ > 0`, `κ ≠ 0`). -/
theorem mp_a_lt_theta {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) (hκ : κ ≠ 0) :
    ex942a β κ lam < ex951θ κ lam := by
  obtain ⟨ha0, ha1, -, hroot, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  set θ := ex951θ κ lam
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hk2 : 0 < κ ^ 2 := by positivity
  have hPθ : β * θ ^ 2 - ex942b β κ lam * θ + 1 = -(β * κ ^ 2 * lam / (κ ^ 2 + lam) ^ 2) := by
    simp only [θ, ex951θ, ex942b]
    field_simp
    ring
  have hneg : β * θ ^ 2 - ex942b β κ lam * θ + 1 < 0 := by
    rw [hPθ, neg_lt_zero]
    positivity
  have hb := ex942_b_eq ha0.ne' hroot
  have hfac : β * θ ^ 2 - ex942b β κ lam * θ + 1 = (θ - a) * (β * θ - a⁻¹) := by
    rw [hb]
    have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    linear_combination (-1) * hia
  have hai : 1 < a⁻¹ := one_lt_inv_iff₀.2 ⟨ha0, ha1⟩
  by_contra hle
  push Not at hle
  have h1 : β * θ - a⁻¹ < 0 := by nlinarith
  have h2 : 0 ≤ (θ - a) * (β * θ - a⁻¹) := mul_nonneg_of_nonpos_of_nonpos (by linarith) h1.le
  linarith

/-- **Discretion has higher inflation at all times** (Miao, pp. 638–639). Without cost-push
shocks, with `κx* > 0`, `0 < β < 1`, `λ > 0`, commitment inflation `π_t = β(μ_{xt} − μ_{x,t+1})`
(`μ_{x0} = 0`, the rule with `a = ex942a`) is below the discretionary rate at every date. -/
theorem mp_discretion_above_commitment {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκx : 0 < κ * xs) (μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) 0) :
    ∀ t, β * (μ t - μ (t + 1)) < ex951pi β κ lam ρ xs 0 := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at hκx
  obtain ⟨hc, -, -, -⟩ := cp_commitment_vs_discretion hβ0 hβ1 hlam hκ ρ μ hμ0 hμ
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have hat := mp_a_lt_theta hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  set θ := ex951θ κ lam
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hd1 : 0 < 1 - β * a := by nlinarith
  have hd2 : 0 < 1 - β * θ := by nlinarith
  have hpd : ex951pi β κ lam ρ xs 0 = θ * (κ * xs / (1 - β * θ)) := by
    simp only [ex951pi, zero_div, add_zero]
    rfl
  intro t
  rw [hc t, hpd]
  have hpow : a ^ (t + 1) ≤ a := by
    rw [pow_succ]
    exact mul_le_of_le_one_left ha0.le (pow_le_one₀ ha0.le ha1.le)
  have hK : 0 < κ * xs / (1 - β * a) := div_pos hκx hd1
  have hcmp : a * (κ * xs / (1 - β * a)) < θ * (κ * xs / (1 - β * θ)) := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hd1 hd2]
    nlinarith
  calc a ^ (t + 1) * (κ * xs / (1 - β * a)) ≤ a * (κ * xs / (1 - β * a)) :=
        mul_le_mul_of_nonneg_right hpow hK.le
    _ < θ * (κ * xs / (1 - β * θ)) := hcmp

/-- The algebra of the impact gap:
`θ(K/(1 − βθ) + u/(1 − βθρ)) − a(K/(1 − βa) + u/(1 − βaρ)) =
(θ/(1 − βθ) − a/(1 − βa))K + (θ − a)u/((1 − βθρ)(1 − βaρ))`. -/
theorem mp_gap_algebra {β ρ a θ K u : ℝ} (h3 : 1 - β * θ * ρ ≠ 0) (h4 : 1 - β * a * ρ ≠ 0) :
    θ * (K / (1 - β * θ) + u / (1 - β * θ * ρ)) - a * (K / (1 - β * a) + u / (1 - β * a * ρ)) =
      (θ / (1 - β * θ) - a / (1 - β * a)) * K + (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) * u
    := by
  have e : θ / (1 - β * θ * ρ) - a / (1 - β * a * ρ) =
      (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) := by
    rw [div_sub_div _ _ h3 h4, show θ * (1 - β * a * ρ) - (1 - β * θ * ρ) * a = θ - a by ring]
  rw [← e]
  ring

/-- **The gap at the date of a cost-push shock** (Miao, p. 639). With `0 < β < 1`, `λ > 0`,
`κ ≠ 0`, `|ρ_u| ≤ 1`, the date-0 discretionary inflation minus the date-0 commitment inflation
`a(κx*/(1 − βa) + u_0/(1 − βaρ_u))` is
`(θ/(1 − βθ) − a/(1 − βa))κx* + (θ − a)u_0/((1 − βθρ_u)(1 − βaρ_u))`, and both coefficients are
positive: the gap rises with the shock. -/
theorem mp_discretion_gap_impact {β κ lam ρ xs u0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκ : κ ≠ 0) (hρ : |ρ| ≤ 1) :
    let a := ex942a β κ lam
    let θ := ex951θ κ lam
    ex951pi β κ lam ρ xs u0 - a * (κ * xs / (1 - β * a) + u0 / (1 - β * a * ρ)) =
        (θ / (1 - β * θ) - a / (1 - β * a)) * (κ * xs) +
          (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) * u0 ∧
      0 < θ / (1 - β * θ) - a / (1 - β * a) ∧
      0 < (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) := by
  intro a θ
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have hat : a < θ := mp_a_lt_theta hβ0 hβ1 hlam hκ
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hθ0 : 0 < θ := ex951θ_pos hlam
  have hβρ : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    nlinarith [abs_nonneg ρ]
  have hr := abs_lt.1 hβρ
  have hd1 : 0 < 1 - β * a := by nlinarith
  have hd2 : 0 < 1 - β * θ := by nlinarith
  have hd3 : 0 < 1 - β * θ * ρ := by nlinarith
  have hd4 : 0 < 1 - β * a * ρ := by nlinarith
  refine ⟨?_, ?_, div_pos (by linarith) (mul_pos hd3 hd4)⟩
  · simp only [ex951pi]
    exact mp_gap_algebra hd3.ne' hd4.ne'
  · rw [sub_pos, div_lt_div_iff₀ hd1 hd2]
    nlinarith

/-! ### Figure 19.3: the qualitative facts -/

/-- **Figure 19.3, commitment** (Miao, pp. 639–640). Let `0 < β < 1`, `λ > 0`, `κ > 0`,
`x* = 0`, `ρ_u = 0`, a single cost-push shock `u_0 = σ > 0` (`u_t = 0` for `t ≥ 1`), `μ_{x0} = 0`
and the commitment rule. Then `βμ_{x,t+1} = −a^{t+1}σ`; the output gap
`x_t = (βκ/λ)μ_{x,t+1} = −(κ/λ)a^{t+1}σ` is negative at every date and serially correlated
(`x_{t+1} = ax_t`); inflation rises on impact (`π_0 = aσ > 0`) and is negative afterwards
(`π_{t+1} = −a^{t+1}(1 − a)σ < 0`). -/
theorem mp_fig_19_3_commitment {β κ lam σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hσ : 0 < σ) (u μ : ℕ → ℝ) (hu0 : u 0 = σ) (hu : ∀ t, u (t + 1) = 0)
    (hμ0 : μ 0 = 0) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ 0 0 (ex942a β κ lam) (μ t) (u t)) :
    let a := ex942a β κ lam
    (∀ t, β * μ (t + 1) = -(a ^ (t + 1) * σ)) ∧
      (∀ t, β * κ / lam * μ (t + 1) < 0) ∧
      (∀ t, β * κ / lam * μ (t + 2) = a * (β * κ / lam * μ (t + 1))) ∧
      0 < β * (μ 0 - μ 1) ∧ (∀ t, β * (μ (t + 1) - μ (t + 2)) < 0) := by
  intro a
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ.ne'
  have hrule : ∀ t, β * μ (t + 1) = a * (β * μ t) - a * u t := fun t => by
    rw [hμ t, mp_beta_rule hβ0.ne']
    simp only [mul_zero, zero_div, zero_add, sub_zero, div_one]
    rfl
  have hclosed : ∀ t, β * μ (t + 1) = -(a ^ (t + 1) * σ) := by
    intro t
    induction t with
    | zero => rw [hrule 0, hμ0, hu0]; ring
    | succ n ih => rw [hrule (n + 1), ih, hu n]; ring
  have hx : ∀ t, β * κ / lam * μ (t + 1) = κ / lam * -(a ^ (t + 1) * σ) := fun t => by
    rw [← hclosed t]
    ring
  refine ⟨hclosed, fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · rw [hx t]
    have : 0 < a ^ (t + 1) * σ := mul_pos (pow_pos ha0 _) hσ
    have : 0 < κ / lam := div_pos hκ hlam
    nlinarith
  · rw [hx, hx]
    ring
  · have h1 := hclosed 0
    have : β * (μ 0 - μ 1) = a * σ := by
      rw [mul_sub, hμ0, mul_zero, zero_sub, h1]
      ring
    rw [this]
    exact mul_pos ha0 hσ
  · have e : β * (μ (t + 1) - μ (t + 2)) = -(a ^ (t + 1) * σ) + a ^ (t + 2) * σ := by
      rw [mul_sub, hclosed t, hclosed (t + 1)]
      ring
    rw [e]
    have : a ^ (t + 2) < a ^ (t + 1) := pow_lt_pow_right_of_lt_one₀ ha0 ha1 (by omega)
    nlinarith

/-- **Figure 19.3, discretion** (Miao, pp. 639–640). With `x* = 0`, `ρ_u = 0`, `λ > 0`, `κ > 0`,
`0 < β < 1` and a single shock `u_0 = σ > 0`, the discretionary policy
`π_t = ex951pi(u_t)`, `x_t = (λx* − κ(βE_tπ_{t+1} + u_t))/(κ² + λ)` ((9.43) with
`E_tπ_{t+1} = ex951pi(ρ_uu_t)`) has inflation rising and the output gap falling on impact, and
both are `0` from the next period on. -/
theorem mp_fig_19_3_discretion {β κ lam σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hσ : 0 < σ) (u : ℕ → ℝ) (hu0 : u 0 = σ) (hu : ∀ t, u (t + 1) = 0) :
    let pin : ℕ → ℝ := fun t => ex951pi β κ lam 0 0 (u t)
    let x : ℕ → ℝ := fun t =>
      (lam * 0 - κ * (β * ex951pi β κ lam 0 0 (0 * u t) + u t)) / (κ ^ 2 + lam)
    0 < pin 0 ∧ x 0 < 0 ∧ ∀ t, pin (t + 1) = 0 ∧ x (t + 1) = 0 := by
  intro pin x
  have hρ : |(0 : ℝ)| ≤ 1 := by simp
  have hcl : ∀ v, ex951pi β κ lam 0 0 v = lam / (κ ^ 2 + lam) * v := fun v => by
    rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ]
    ring_nf
  have hk : 0 < κ ^ 2 + lam := by positivity
  refine ⟨?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · simp only [pin, hcl, hu0]
    positivity
  · simp only [x, hcl, hu0, zero_mul, mul_zero, zero_sub, zero_add]
    rw [div_neg_iff]
    right
    exact ⟨by nlinarith [mul_pos hκ hσ], hk⟩
  · simp only [pin, hcl, hu t, mul_zero]
  · simp only [x, hcl, hu t, mul_zero, zero_add, sub_zero, zero_div]

end Miao.NewKeynesian
