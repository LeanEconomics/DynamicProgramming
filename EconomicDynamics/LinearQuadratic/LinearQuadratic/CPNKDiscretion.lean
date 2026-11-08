/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.CPNKCommitment

/-!
# The New Keynesian model under discretion: Example 9.5.1, and commitment versus discretion

Miao, §9.5, p. 315 (Example 9.5.1), with the comparison to Example 9.4.2 (pp. 308–311).
Throughout `θ = λ/(κ² + λ)`.

* `eq_9_43`: for `λ > 0`, the static problem `min ½π² + (λ/2)(x − x*)²` subject to
  `π = κx + βπᵉ + z` has the unique solution with `π = θ(κx* + βπᵉ + z)` (9.43).
* `IsMPE951`, `example_9_5_1`: a Markov perfect equilibrium is a pair `π(z)`, `πᵉ(z)` with
  `π(z) = θ(κx* + βπᵉ(z) + z)` and `πᵉ(z) = E π(ρz + ε)`; for `0 < β < 1`, `|ρ| ≤ 1` and any
  integrable mean-zero shock, `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))` is one, and it is the
  only one with `π` affine in `z` (`example_9_5_1_unique`).
* `ex951_forward`: every bounded solution of the forward recursion
  `E_tπ_{t+j} = θ(κx* + βE_tπ_{t+j+1} + E_t z_{t+j})` (`E_t z_{t+j} = ρʲz_t`) has
  `π_t = θ∑ⱼ βʲθʲ(κx* + E_t z_{t+j})`, the book's formula; `ex951_series` sums it to the
  closed form above.
* `cp_commitment_vs_discretion` (the comparison of §§9.4–9.5): without cost-push shocks,
  inflation under commitment is `π_t = a^{t+1}κx*/(1 − βa) → 0`, while under discretion it is
  the constant inflation bias `θκx*/(1 − βθ) = λκx*/(κ² + (1 − β)λ)`, nonzero when `κx* ≠ 0`.
-/

namespace Miao.LinearQuadratic

open Filter Topology MeasureTheory

/-- `θ = λ/(κ² + λ)`. -/
noncomputable def ex951θ (κ lam : ℝ) : ℝ := lam / (κ ^ 2 + lam)

theorem ex951θ_pos {κ lam : ℝ} (hlam : 0 < lam) : 0 < ex951θ κ lam :=
  div_pos hlam (by positivity)

theorem ex951θ_le_one {κ lam : ℝ} (hlam : 0 < lam) : ex951θ κ lam ≤ 1 := by
  rw [ex951θ, div_le_one (by positivity)]
  nlinarith [sq_nonneg κ]

/-- Miao, (9.43), p. 315. For `λ > 0`, the problem `min ½π² + (λ/2)(x − x*)²` subject to
`π = κx + βπᵉ + z` (with `πᵉ` taken as given) is solved by
`x̂ = (λx* − κ(βπᵉ + z))/(κ² + λ)`, `π̂ = κx̂ + βπᵉ + z = θ(κx* + βπᵉ + z)`, and by no other
feasible pair. -/
theorem eq_9_43 {κ lam xs β πe z : ℝ} (hlam : 0 < lam) :
    let xh := (lam * xs - κ * (β * πe + z)) / (κ ^ 2 + lam)
    let ph := κ * xh + β * πe + z
    ph = ex951θ κ lam * (κ * xs + β * πe + z) ∧
    ∀ p x, p = κ * x + β * πe + z →
      (1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2 ≤ (1 / 2) * p ^ 2 + lam / 2 * (x - xs) ^ 2 ∧
      ((1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2 = (1 / 2) * p ^ 2 + lam / 2 * (x - xs) ^ 2 →
        x = xh ∧ p = ph) := by
  intro xh ph
  have hd : κ ^ 2 + lam ≠ 0 := by positivity
  have hsq : ∀ x, (1 / 2) * (κ * x + β * πe + z) ^ 2 + lam / 2 * (x - xs) ^ 2 =
      ((1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2) + (κ ^ 2 + lam) / 2 * (x - xh) ^ 2 := by
    intro x
    simp only [ph, xh]
    field_simp
    ring
  refine ⟨?_, fun p x hp => ?_⟩
  · simp only [ph, xh, ex951θ]
    field_simp
    ring
  · rw [hp, hsq x]
    refine ⟨by nlinarith [sq_nonneg (x - xh)], fun h => ?_⟩
    have h2 : (κ ^ 2 + lam) / 2 * (x - xh) ^ 2 = 0 := by linarith
    have h3 : (x - xh) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · exact absurd h4 (by positivity)
      · exact h4
    have hx : x = xh := by nlinarith [sq_nonneg (x - xh)]
    exact ⟨hx, by rw [hx]⟩

/-- **Markov perfect equilibrium of Example 9.5.1** (Miao, p. 315): `π(z) = θ(κx* + βπᵉ(z) + z)`
(9.43 at `πᵉ = πᵉ(z)`) and `πᵉ(z) = E_t π(z_{t+1})` with `z_{t+1} = ρz + ε`, `ε ∼ ν`. -/
def IsMPE951 (β κ lam ρ xs : ℝ) (ν : Measure ℝ) (pf pe : ℝ → ℝ) : Prop :=
  (∀ z, pf z = ex951θ κ lam * (κ * xs + β * pe z + z)) ∧ ∀ z, pe z = ∫ e, pf (ρ * z + e) ∂ν

/-- The discretionary inflation rule `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))`. -/
noncomputable def ex951pi (β κ lam ρ xs z : ℝ) : ℝ :=
  ex951θ κ lam * (κ * xs / (1 - β * ex951θ κ lam) + z / (1 - β * ex951θ κ lam * ρ))

theorem ex951_denoms {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) : 1 - β * ex951θ κ lam ≠ 0 ∧ 1 - β * ex951θ κ lam * ρ ≠ 0 ∧
      |β * ex951θ κ lam| < 1 ∧ |β * ex951θ κ lam * ρ| < 1 := by
  have h0 := ex951θ_pos (κ := κ) hlam
  have h1 := ex951θ_le_one (κ := κ) hlam
  have hb : β * ex951θ κ lam < 1 := by nlinarith
  have hb0 : 0 < β * ex951θ κ lam := mul_pos hβ0 h0
  have hc : |β * ex951θ κ lam * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hb0]
    nlinarith [abs_nonneg ρ]
  refine ⟨by linarith, ?_, by rw [abs_of_pos hb0]; exact hb, hc⟩
  have := (abs_lt.1 hc).2
  linarith

/-- **Example 9.5.1** (Miao, p. 315). For `0 < β < 1`, `λ > 0`, `|ρ| ≤ 1` and an integrable
mean-zero shock, `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))` with
`πᵉ(z) = θ(κx*/(1 − βθ) + ρz/(1 − βθρ))` is a Markov perfect equilibrium. -/
theorem example_9_5_1 {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable (fun e => e) ν)
    (hmean : ∫ e, e ∂ν = 0) :
    IsMPE951 β κ lam ρ xs ν (ex951pi β κ lam ρ xs) (fun z => ex951pi β κ lam ρ xs (ρ * z)) := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  refine ⟨fun z => ?_, fun z => ?_⟩
  · have hA := inv_mul_cancel₀ hd1
    have hB := inv_mul_cancel₀ hd2
    simp only [ex951pi]
    linear_combination ex951θ κ lam * κ * xs * hA + ex951θ κ lam * z * hB
  · have h : ∀ e, ex951pi β κ lam ρ xs (ρ * z + e) =
        ex951pi β κ lam ρ xs (ρ * z) + (ex951θ κ lam / (1 - β * ex951θ κ lam * ρ)) * e :=
      fun e => by
        simp only [ex951pi]
        ring
    simp only [h]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
      hmean]
    simp

/-- **Uniqueness among affine rules** (Example 9.5.1). If `π(z) = c₀ + c₁z` is part of a
Markov perfect equilibrium, then `π` is the rule of `example_9_5_1`. -/
theorem example_9_5_1_unique {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable (fun e => e) ν)
    (hmean : ∫ e, e ∂ν = 0) (c0 c1 : ℝ) (pe : ℝ → ℝ)
    (h : IsMPE951 β κ lam ρ xs ν (fun z => c0 + c1 * z) pe) :
    ∀ z, c0 + c1 * z = ex951pi β κ lam ρ xs z := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  obtain ⟨h1, h2⟩ := h
  have hpe : ∀ z, pe z = c0 + c1 * (ρ * z) := fun z => by
    rw [h2 z]
    have : ∀ e, c0 + c1 * (ρ * z + e) = (c0 + c1 * (ρ * z)) + c1 * e := fun e => by ring
    simp only [this]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const,
      integral_const_mul, hmean]
    simp
  set θ := ex951θ κ lam
  have e0 := h1 0
  have e1 := h1 1
  rw [hpe] at e0 e1
  have hc0 : c0 = θ * (κ * xs) / (1 - β * θ) := by
    rw [eq_div_iff hd1]
    linarith
  have hc1 : c1 = θ / (1 - β * θ * ρ) := by
    rw [eq_div_iff hd2]
    linarith
  intro z
  rw [hc0, hc1, ex951pi]
  field_simp
  ring

/-- Miao, p. 315: the book's series sums to the closed form,
`θ∑ⱼ βʲθʲ(κx* + ρʲz) = θ(κx*/(1 − βθ) + z/(1 − βθρ))`. -/
theorem ex951_series {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (z : ℝ) :
    ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) =
      ex951pi β κ lam ρ xs z := by
  obtain ⟨hd1, hd2, h1, h2⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  have hterm : ∀ j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) =
      κ * xs * (β * ex951θ κ lam) ^ j + z * (β * ex951θ κ lam * ρ) ^ j := fun j => by
    rw [mul_pow, mul_pow]
    ring
  rw [tsum_congr hterm, ((summable_geometric_of_abs_lt_one h1).mul_left _).tsum_add
      ((summable_geometric_of_abs_lt_one h2).mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one h1, tsum_geometric_of_abs_lt_one h2, ex951pi]
  ring

/-- Miao, p. 315 ("we can then solve for the discretionary inflation rate"): if
`p_j = E_tπ_{t+j}` is bounded and satisfies `p_j = θ(κx* + βp_{j+1} + ρʲz)` (9.43 with
`πᵉ = E_tπ_{t+j+1}` and `E_t z_{t+j} = ρʲz`), then `p₀ = θ∑ⱼ βʲθʲ(κx* + ρʲz)`. -/
theorem ex951_forward {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (z : ℝ) (p : ℕ → ℝ) (hp : ∀ j, p j =
      ex951θ κ lam * (κ * xs + β * p (j + 1) + ρ ^ j * z)) (hb : ∃ M, ∀ j, |p j| ≤ M) :
    p 0 = ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) := by
  obtain ⟨-, -, h1, h2⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  set θ := ex951θ κ lam
  set f : ℕ → ℝ := fun j => β ^ j * θ ^ j * (κ * xs + ρ ^ j * z) with hf
  have hsum : Summable f := by
    have : f = fun j => κ * xs * (β * θ) ^ j + z * (β * θ * ρ) ^ j := by
      funext j
      simp only [hf, mul_pow]
      ring
    rw [this]
    exact ((summable_geometric_of_abs_lt_one h1).mul_left _).add
      ((summable_geometric_of_abs_lt_one h2).mul_left _)
  have hiter : ∀ n, p 0 = θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, Finset.sum_range_succ, hp n]
      simp only [hf]
      ring
  obtain ⟨M, hM⟩ := hb
  have hrem : Tendsto (fun n => (β * θ) ^ n * p n) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => |β * θ| ^ n * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h1).mul_const M
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM n) (pow_nonneg (abs_nonneg _) _)
  have hlim : Tendsto (fun n => θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n) atTop
      (𝓝 (θ * ∑' j, f j + 0)) :=
    (hsum.hasSum.tendsto_sum_nat.const_mul θ).add hrem
  have hconst : Tendsto (fun n => θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n) atTop
      (𝓝 (p 0)) := by
    simp only [← hiter]
    exact tendsto_const_nhds
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

/-- **Commitment versus discretion** (Miao, §§9.4–9.5). Let `κ ≠ 0`, `λ > 0`, `0 < β < 1`,
`a = ex942a` the stable root of (9.29), and no cost-push shocks (`z ≡ 0`). Under commitment
(`μ_{x0} = 0`, the rule of Example 9.4.2, `π_t = β(μ_{xt} − μ_{x,t+1})`) inflation is
`π_t = a^{t+1}κx*/(1 − βa)`, which tends to `0`; under discretion it is the constant
`θκx*/(1 − βθ) = λκx*/(κ² + (1 − β)λ)` at every date, nonzero whenever `κx* ≠ 0`. -/
theorem cp_commitment_vs_discretion {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκ : κ ≠ 0) (ρ : ℝ) (μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) 0) :
    (∀ t, β * (μ t - μ (t + 1)) =
        ex942a β κ lam ^ (t + 1) * (κ * xs / (1 - β * ex942a β κ lam))) ∧
      Tendsto (fun t => β * (μ t - μ (t + 1))) atTop (𝓝 0) ∧
      ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) ∧
      (κ * xs ≠ 0 → ex951pi β κ lam ρ xs 0 ≠ 0) := by
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  have hd : 1 - β * a ≠ 0 := by nlinarith
  have h1a : 1 - a ≠ 0 := by linarith
  set K := κ * xs / (1 - β * a)
  set mbar := -(a / β) * K / (1 - a)
  have hclosed : ∀ t, μ t = mbar * (1 - a ^ t) := by
    intro t
    induction t with
    | zero => simp [hμ0]
    | succ n ih =>
      rw [hμ n, ih, ex942Rule]
      simp only [mbar, K]
      field_simp
      ring
  have hpi : ∀ t, β * (μ t - μ (t + 1)) = a ^ (t + 1) * K := by
    intro t
    rw [hclosed, hclosed]
    simp only [mbar]
    field_simp
    ring
  refine ⟨hpi, ?_, ?_, fun hk => ?_⟩
  · simp only [hpi]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const K
  · have hθd : κ ^ 2 + lam ≠ 0 := by positivity
    have hden : κ ^ 2 + (1 - β) * lam ≠ 0 := by nlinarith [sq_nonneg κ]
    simp only [ex951pi, ex951θ]
    field_simp
    ring
  · obtain ⟨hd1, -, -, -⟩ := ex951_denoms (κ := κ) (ρ := 0) hβ0 hβ1 hlam (by simp)
    simp only [ex951pi, zero_div, add_zero]
    exact mul_ne_zero (ex951θ_pos hlam).ne' (div_ne_zero hk hd1)

end Miao.LinearQuadratic
