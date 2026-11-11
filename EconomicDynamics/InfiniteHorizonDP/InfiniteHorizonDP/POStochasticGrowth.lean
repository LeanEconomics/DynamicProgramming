/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.POMotivating
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Exercise 6.2: the §6.1 planner with a Markov productivity shock

Copied from `EconomicDynamics/FiniteHorizonDP` (module `POStochasticGrowth`), namespace renamed.

**Exercise 6.2** (Miao, p. 189): `max E ∑_{t=0}^T βᵗ ln C_t` subject to
`C_t + K_{t+1} = z_t K_t^α`, where the productivity `z_t = ζ(x_t) > 0` is a function of a Markov
process `(x_t)` on a measurable space `X` with transition function `Q`. Integrability: `ln ζ` is
measurable and **bounded** (so every expectation below exists); `Q` is a Markov kernel.

With `n = T − t` periods to go, `θ_n` and the coefficient `coef_n` of §6.1 (`po61_theta`,
`po61_coef`) and `b_n` of (6.6) (`po61_b`):

* the value function is `V_t(K, x) = coef_{T−t} ln K + E_{T−t}(x)`, where
  `E_0(x) = ln ζ(x)` and
  `E_{n+1}(x) = (1 + β coef_n) ln ζ(x) + b_{n+1} + β ∫ E_n(x′) Q(x, dx′)` (`po62_E`, `po62_V`);
* the policies are `K_{t+1} = θ_{T−t} z_t K_t^α` (investment) and
  `C_t = (1 − θ_{T−t}) z_t K_t^α = z_t K_t^α/(1 + β coef_{T−t−1})` (consumption): the saving rate
  is the deterministic one of (6.3) and does not depend on the shock (`ex_6_2_policies`).

`ex_6_2` proves the stochastic Bellman equation
`V_t(K, x) = max_{0 < K′ < ζ(x)K^α} ln(ζ(x)K^α − K′) + β ∫ V_{t+1}(K′, x′) Q(x, dx′)` as a
maximisation, with the unique maximiser `K′ = θ_{T−t}ζ(x)K^α`, and `V_T(K, x) = ln(ζ(x)K^α)`.
`po62_E_bounded` gives the integrability used.

That the policy plan is optimal for the sequence problem (among the plans with integrable
rewards; Assumption 5.1.3 fails for this model) is `ex_6_2_optimal` in `POStochasticGrowthMDP`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The shock part of the value function, by periods to go. -/
noncomputable def po62_E (Q : Kernel X X) (ζ : X → ℝ) (α β : ℝ) : ℕ → X → ℝ
  | 0 => fun x => Real.log (ζ x)
  | n + 1 => fun x => (1 + β * po61_coef α β n) * Real.log (ζ x) + po61_b α β (n + 1) +
      β * ∫ x', po62_E Q ζ α β n x' ∂Q x

/-- The value function `V_t(K, x) = coef_{T−t} ln K + E_{T−t}(x)`. -/
noncomputable def po62_V (Q : Kernel X X) (ζ : X → ℝ) (α β : ℝ) (T t : ℕ) (K : ℝ) (x : X) : ℝ :=
  po61_coef α β (T - t) * Real.log K + po62_E Q ζ α β (T - t) x

/-- `E_n` is measurable and bounded when `ln ζ` is. -/
theorem po62_E_bounded {Q : Kernel X X} [IsMarkovKernel Q] {ζ : X → ℝ}
    (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ} (hB : ∀ x, |Real.log (ζ x)| ≤ B)
    (α β : ℝ) : ∀ n, Measurable (po62_E Q ζ α β n) ∧ ∃ D, ∀ x, |po62_E Q ζ α β n x| ≤ D := by
  intro n
  induction n with
  | zero => exact ⟨hζm, B, hB⟩
  | succ n ih =>
    obtain ⟨hm, D, hD⟩ := ih
    refine ⟨?_, ?_⟩
    · exact ((measurable_const.mul hζm).add measurable_const).add (measurable_const.mul
        (hm.stronglyMeasurable.integral_kernel (κ := Q)).measurable)
    · refine ⟨|1 + β * po61_coef α β n| * B + |po61_b α β (n + 1)| + |β| * D, fun x => ?_⟩
      have h1 : |∫ x', po62_E Q ζ α β n x' ∂Q x| ≤ D := by
        have := norm_integral_le_of_norm_le_const (μ := Q x) (f := po62_E Q ζ α β n) (C := D)
          (Filter.Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hD x')
        simpa [Real.norm_eq_abs] using this
      simp only [po62_E]
      calc |(1 + β * po61_coef α β n) * Real.log (ζ x) + po61_b α β (n + 1) +
            β * ∫ x', po62_E Q ζ α β n x' ∂Q x|
          ≤ |(1 + β * po61_coef α β n) * Real.log (ζ x)| + |po61_b α β (n + 1)| +
              |β * ∫ x', po62_E Q ζ α β n x' ∂Q x| := abs_add_three _ _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hB x

theorem po62_integrable_E {Q : Kernel X X} [IsMarkovKernel Q] {ζ : X → ℝ}
    (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ} (hB : ∀ x, |Real.log (ζ x)| ≤ B)
    (α β : ℝ) (n : ℕ) (x : X) : Integrable (po62_E Q ζ α β n) (Q x) := by
  obtain ⟨hm, D, hD⟩ := po62_E_bounded (Q := Q) hζm hB α β n
  exact Integrable.of_bound hm.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun x' => by rw [Real.norm_eq_abs]; exact hD x')

/-- **Exercise 6.2** (Miao, p. 189): the Bellman equation of the stochastic growth model, solved.
For `t < T`, `K > 0` and every state `x` of the shock (with `z = ζ(x) > 0`):
`ln(zK^α − K′) + β ∫ V_{t+1}(K′, x′) Q(x, dx′) ≤ V_t(K, x)` for every `K′ ∈ (0, zK^α)`, with
equality at `K′ = θ_{T−t} zK^α` and strict inequality elsewhere; and `V_T(K, x) = ln(zK^α)`. -/
theorem ex_6_2 {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} [IsMarkovKernel Q]
    {ζ : X → ℝ} (hζ : ∀ x, 0 < ζ x) (hζm : Measurable fun x => Real.log (ζ x)) {B : ℝ}
    (hB : ∀ x, |Real.log (ζ x)| ≤ B) {T t : ℕ} (ht : t < T) {K : ℝ} (hK : 0 < K) (x : X) :
    (∀ K' : ℝ, 0 < K' → K' < ζ x * K ^ α →
      Real.log (ζ x * K ^ α - K') + β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x ≤
        po62_V Q ζ α β T t K x) ∧
    (0 < po61_theta α β (T - t) * (ζ x * K ^ α) ∧
      po61_theta α β (T - t) * (ζ x * K ^ α) < ζ x * K ^ α ∧
      Real.log (ζ x * K ^ α - po61_theta α β (T - t) * (ζ x * K ^ α)) +
        β * ∫ x', po62_V Q ζ α β T (t + 1) (po61_theta α β (T - t) * (ζ x * K ^ α)) x' ∂Q x =
          po62_V Q ζ α β T t K x) ∧
    (∀ K' : ℝ, 0 < K' → K' < ζ x * K ^ α → K' ≠ po61_theta α β (T - t) * (ζ x * K ^ α) →
      Real.log (ζ x * K ^ α - K') + β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x <
        po62_V Q ζ α β T t K x) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  have hy : 0 < ζ x * K ^ α := mul_pos (hζ x) (Real.rpow_pos_of_pos hK α)
  have hc := mul_pos h.β_pos (po61_coef_pos h n)
  set c := β * po61_coef α β n with hcdef
  have hint := po62_integrable_E (Q := Q) hζm hB α β n x
  have hlogy : Real.log (ζ x * K ^ α) = Real.log (ζ x) + α * Real.log K := by
    rw [Real.log_mul (hζ x).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK α]
  have hVt : po62_V Q ζ α β T t K x = (1 + c) * Real.log (ζ x * K ^ α) -
      (1 + c) * Real.log (1 + c) + c * Real.log c + β * ∫ x', po62_E Q ζ α β n x' ∂Q x := by
    unfold po62_V
    rw [hn, po61_coef_succ h n, ← hcdef]
    simp only [po62_E]
    rw [po61_b_succ h n, ← hcdef, hlogy]
    ring
  have hrhs : ∀ K', β * ∫ x', po62_V Q ζ α β T (t + 1) K' x' ∂Q x =
      c * Real.log K' + β * ∫ x', po62_E Q ζ α β n x' ∂Q x := by
    intro K'
    unfold po62_V
    rw [hn', integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
      hcdef]
    ring
  have hθ : po61_theta α β (T - t) * (ζ x * K ^ α) = c * (ζ x * K ^ α) / (1 + c) := by
    rw [hn, (po61_theta_succ h n).1, ← hcdef]
    ring
  have hθlt : po61_theta α β (T - t) * (ζ x * K ^ α) < ζ x * K ^ α := by
    rw [hθ, div_lt_iff₀ (by linarith)]
    nlinarith
  have hθpos : 0 < po61_theta α β (T - t) * (ζ x * K ^ α) := by
    rw [hθ]
    positivity
  refine ⟨fun K' hK' hK'y => ?_, ⟨hθpos, hθlt, ?_⟩, fun K' hK' hK'y hne => ?_⟩
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).1
    linarith
  · rw [hrhs, hVt, hθ]
    have h1 : ζ x * K ^ α - c * (ζ x * K ^ α) / (1 + c) = ζ x * K ^ α / (1 + c) := by
      field_simp
      ring
    have h2 : c * (ζ x * K ^ α) / (1 + c) = c * (ζ x * K ^ α / (1 + c)) := by ring
    rw [h1, h2, Real.log_mul hc.ne' (by positivity), Real.log_div hy.ne' (by linarith)]
    ring
  · rw [hrhs, hVt]
    have := (po61_max hy hc hK' hK'y).2 (by rw [← hθ]; exact hne)
    linarith

/-- Exercise 6.2, the terminal date: `V_T(K, x) = ln(ζ(x)K^α)`. -/
theorem ex_6_2_terminal {α β : ℝ} (h : po61_Params α β) {Q : Kernel X X} {ζ : X → ℝ}
    (hζ : ∀ x, 0 < ζ x) (T : ℕ) {K : ℝ} (hK : 0 < K) (x : X) :
    po62_V Q ζ α β T T K x = Real.log (ζ x * K ^ α) := by
  have hp1 : (1 : ℝ) - α * β ≠ 0 := by linarith [h.p_lt]
  rw [Real.log_mul (hζ x).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK α]
  simp only [po62_V, Nat.sub_self, po62_E, po61_coef, zero_add, pow_one]
  field_simp
  ring

/-- **Exercise 6.2: the optimal policies** (Miao, p. 189). For `t < T`: investment
`K_{t+1} = θ_{T−t} z_t K_t^α` and consumption `C_t = z_t K_t^α − K_{t+1} = (1 − θ_{T−t}) z_t K_t^α
= z_t K_t^α/(1 + β coef_{T−t−1})`, with the deterministic saving rate `θ_{T−t}` of (6.3). -/
theorem ex_6_2_policies {α β : ℝ} (h : po61_Params α β) {T t : ℕ} (ht : t < T) (y : ℝ) :
    y - po61_theta α β (T - t) * y = (1 - po61_theta α β (T - t)) * y ∧
      (1 - po61_theta α β (T - t)) * y = y / (1 + β * po61_coef α β (T - t - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  refine ⟨by ring, ?_⟩
  rw [hn, (po61_theta_succ h n).2, show n + 1 - 1 = n by omega]
  ring

end Miao.InfiniteHorizonDP
