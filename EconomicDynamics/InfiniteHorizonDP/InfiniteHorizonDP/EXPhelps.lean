/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUPhelps
import InfiniteHorizonDP.POMotivating
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exercises 7.6 and 7.8: the value-function approach to Example 7.5.1 (Phelps 1962)

Miao, §7.6, Exercises 6 and 8, pp. 229–230. The model of Example 7.5.1: cash on hand `x > 0`,
consumption `c = x − s`, saving `s ∈ (0, x)`, `x′ = R′ s` with `R′ > 0` iid with law `ν`
(a probability measure on the positive reals `po61_Pos`), CRRA utility `u = cs_crra γ`.

* `ex7_step_max`, `ex7_step_sol`, `ex7_step_value`, `ex7_step_value_log`: the one-step problem
  `max_{s ∈ (0, x)} u(x − s) + K u(s)`, `K > 0`: with `ρ = K^{1/γ}` the maximiser is
  `s* = ρx/(1 + ρ)` (first-order condition `(x − s*)^{−γ} = K s*^{−γ}`, sufficiency by the tangent
  inequality `cs_crra_tangent`), with value `(1 + ρ)^γ u(x)` for `γ ≠ 1`.
* `ex7_integral_crra`, `ex7_integral_log`: `∫ u(R s) ν(dR) = m u(s)` with `m = E[R^{1−γ}]`
  (`γ ≠ 1`), and `= ln s + E ln R` for `γ = 1`.
* **Exercise 7.6** (`ex_7_6_bellman`, `ex_7_6_bellman_log`): the guess `V(x) = B u(x)`,
  `B = A^{−γ}`, `A = 1 − (βm)^{1/γ}` (`γ ≠ 1`), resp. `V(x) = b ln x + a`, `b = 1/(1 − β)`,
  `a = (ln(1 − β) + βb ln β + βb E ln R)/(1 − β)` (`γ = 1`), solves the Bellman equation: the
  right side is at most `V(x)` for every `s ∈ (0, x)` and equals `V(x)` at the saving
  `s = (1 − A)x`, i.e. consumption `c = Ax`. The constants are determined by matching
  (`ex_7_6_constants`: `B = A^{−γ}` is forced by the envelope condition `V′(x) = u′(Ax)`).
* **Exercise 7.8** (`ex_7_8_finite`, `ex_7_8_limit`): the finite-horizon problem
  `v_0 = u`, `v_{n+1}(x) = sup_{s ∈ (0, x)} u(x − s) + β ∫ v_n(R s) ν(dR)` (`ex7_phV`) has
  `v_n = b_n^γ u` with `b_0 = 1`, `b_{n+1} = 1 + ρ b_n`, `ρ = (βm)^{1/γ}` (`ex7_phb`,
  `b_n = Σ_{k ≤ n} ρᵏ`), and the optimal consumption with `n + 1` periods to go is
  `c_{n+1}(x) = x / b_{n+1}`. As `n → ∞`, `1/b_n → 1 − ρ = A` and `b_n^γ → A^{−γ} = B` when
  `βm < 1`: the limit policy is the policy of Example 7.5.1, optimal by `example_7_5_1` and
  `ex_7_6` (module `EXPhelpsMDP`).

**Corrections.** Exercise 7.8 refers to "the model in Exercise 6 of Chapter 6" (Markov labour
income); the Phelps model is Exercise 7 of Chapter 6 (iid returns, constant labour income `y`,
no borrowing). With `y > 0` the policy is not linear and has no closed form; the closed form, and
the model of Example 7.5.1, need `y = 0`, which we impose. `u(c) = c^{1−γ}/(1−γ)` presumes
`γ ≠ 1` (`γ = 1` is the logarithm, treated in Exercise 7.6).
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory Filter Topology

/-! ### The one-step problem -/

/-- **The one-step problem, sufficiency**: if `0 < s₀ < x` satisfies the first-order condition
`(x − s₀)^{−γ} = K s₀^{−γ}`, then `s₀` maximises `u(x − s) + K u(s)` over `s ∈ (0, x)`. -/
theorem ex7_step_max {γ K x s₀ : ℝ} (hγ : 0 < γ) (hK : 0 < K) (hs₀ : 0 < s₀) (hs₀x : s₀ < x)
    (hfoc : (x - s₀) ^ (-γ) = K * s₀ ^ (-γ)) {s : ℝ} (hs : 0 < s) (hsx : s < x) :
    cs_crra γ (x - s) + K * cs_crra γ s ≤ cs_crra γ (x - s₀) + K * cs_crra γ s₀ := by
  have h1 := cs_crra_tangent hγ (sub_pos.2 hs₀x) (sub_pos.2 hsx)
  have h2 := cs_crra_tangent hγ hs₀ hs
  have h3 := mul_le_mul_of_nonneg_left h2 hK.le
  have e : (x - s₀) ^ (-γ) * (x - s - (x - s₀)) + K * (s₀ ^ (-γ) * (s - s₀)) = 0 := by
    rw [hfoc]; ring
  nlinarith

/-- **The one-step problem, the maximiser**: with `ρ = K^{1/γ}`, `s* = ρx/(1 + ρ)` lies in
`(0, x)` and satisfies the first-order condition; consumption is `x − s* = x/(1 + ρ)`. -/
theorem ex7_step_sol {γ K x : ℝ} (hγ : 0 < γ) (hK : 0 < K) (hx : 0 < x) :
    0 < K ^ (1 / γ) * x / (1 + K ^ (1 / γ)) ∧ K ^ (1 / γ) * x / (1 + K ^ (1 / γ)) < x ∧
      x - K ^ (1 / γ) * x / (1 + K ^ (1 / γ)) = x / (1 + K ^ (1 / γ)) ∧
      (x - K ^ (1 / γ) * x / (1 + K ^ (1 / γ))) ^ (-γ) =
        K * (K ^ (1 / γ) * x / (1 + K ^ (1 / γ))) ^ (-γ) := by
  set ρ := K ^ (1 / γ)
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hK _
  have hc : x - ρ * x / (1 + ρ) = x / (1 + ρ) := by field_simp; ring
  refine ⟨by positivity, ?_, hc, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [hc, show ρ * x / (1 + ρ) = ρ * (x / (1 + ρ)) by ring,
      Real.mul_rpow hρ.le (by positivity)]
    have : ρ ^ (-γ) = K⁻¹ := by
      rw [← Real.rpow_mul hK.le, show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one]
    rw [this]
    field_simp

/-- **The one-step problem, the value** (`γ ≠ 1`): with `ρ = K^{1/γ}`,
`u(x/(1 + ρ)) + K u(ρx/(1 + ρ)) = (1 + ρ)^γ u(x)`. -/
theorem ex7_step_value {γ K x : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hK : 0 < K) (hx : 0 < x) :
    cs_crra γ (x / (1 + K ^ (1 / γ))) + K * cs_crra γ (K ^ (1 / γ) * x / (1 + K ^ (1 / γ))) =
      (1 + K ^ (1 / γ)) ^ γ * cs_crra γ x := by
  set ρ := K ^ (1 / γ)
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hK _
  have h1ρ : 0 < 1 + ρ := by linarith
  have hp : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  simp only [cs_crra, hγ1, ↓reduceIte]
  have hKρ : K * ρ ^ (1 - γ) = ρ := by
    rw [← Real.rpow_mul hK.le, show K * K ^ (1 / γ * (1 - γ)) = K ^ (1 + 1 / γ * (1 - γ)) by
      rw [Real.rpow_add hK, Real.rpow_one]]
    congr 1; field_simp; ring
  rw [show ρ * x / (1 + ρ) = ρ * (x / (1 + ρ)) by ring, Real.mul_rpow hρ.le (by positivity),
    Real.div_rpow hx.le h1ρ.le]
  have e : (1 + ρ) ^ γ = (1 + ρ) * ((1 + ρ) ^ (1 - γ))⁻¹ := by
    rw [Real.rpow_sub h1ρ, Real.rpow_one]; field_simp
  rw [e]
  have : (1 + ρ) ^ (1 - γ) ≠ 0 := (Real.rpow_pos_of_pos h1ρ _).ne'
  field_simp
  linear_combination hKρ

/-- **The one-step problem, the value** (`γ = 1`): `ln(x/(1 + K)) + K ln(Kx/(1 + K)) =
(1 + K) ln x − ln(1 + K) + K ln(K/(1 + K))`. -/
theorem ex7_step_value_log {K x : ℝ} (hK : 0 < K) (hx : 0 < x) :
    cs_crra 1 (x / (1 + K ^ (1 / (1 : ℝ)))) +
        K * cs_crra 1 (K ^ (1 / (1 : ℝ)) * x / (1 + K ^ (1 / (1 : ℝ)))) =
      (1 + K) * Real.log x - Real.log (1 + K) + K * Real.log (K / (1 + K)) := by
  simp only [cs_crra, ↓reduceIte, div_one, Real.rpow_one]
  have h1 : 0 < 1 + K := by linarith
  rw [Real.log_div hx.ne' h1.ne', show K * x / (1 + K) = K / (1 + K) * x by ring,
    Real.log_mul (div_pos hK h1).ne' hx.ne']
  ring

/-! ### Expectations of the CRRA utility -/

/-- `E[u(R s)] = m u(s)` with `m = E[R^{1−γ}]` (`γ ≠ 1`, `s > 0`), and `u(R s)` is integrable. -/
theorem ex7_integral_crra {ν : Measure po61_Pos} {γ s : ℝ} (hγ1 : γ ≠ 1) (hs : 0 < s)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν) :
    Integrable (fun r : po61_Pos => cs_crra γ (r.1 * s)) ν ∧
      ∫ r, cs_crra γ (r.1 * s) ∂ν = (∫ r, r.1 ^ (1 - γ) ∂ν) * cs_crra γ s := by
  have e : (fun r : po61_Pos => cs_crra γ (r.1 * s)) =
      fun r => r.1 ^ (1 - γ) * (s ^ (1 - γ) / (1 - γ)) := by
    funext r
    simp only [cs_crra, hγ1, ↓reduceIte]
    rw [Real.mul_rpow r.2.le hs.le]; ring
  rw [e]
  refine ⟨hm.mul_const _, ?_⟩
  rw [integral_mul_const]
  simp only [cs_crra, hγ1, ↓reduceIte]

/-- `E[ln(R s)] = ln s + E ln R` (`s > 0`), and `ln(R s)` is integrable. -/
theorem ex7_integral_log {ν : Measure po61_Pos} [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s)
    (hl : Integrable (fun r : po61_Pos => Real.log r.1) ν) :
    Integrable (fun r : po61_Pos => cs_crra 1 (r.1 * s)) ν ∧
      ∫ r, cs_crra 1 (r.1 * s) ∂ν = Real.log s + ∫ r, Real.log r.1 ∂ν := by
  have e : (fun r : po61_Pos => cs_crra 1 (r.1 * s)) = fun r => Real.log r.1 + Real.log s := by
    funext r
    simp only [cs_crra, ↓reduceIte]
    rw [Real.log_mul r.2.ne' hs.ne']
  rw [e]
  refine ⟨hl.add (integrable_const _), ?_⟩
  rw [integral_add hl (integrable_const _), integral_const, probReal_univ, one_smul]
  ring

/-! ### Exercise 7.6: the Bellman equation of Example 7.5.1 -/

/-- The consumption share of Example 7.5.1, `A = 1 − (βm)^{1/γ}` ((7.39)). -/
noncomputable def ex7_phA (β m γ : ℝ) : ℝ := 1 - (β * m) ^ (1 / γ)

/-- **Exercise 7.6, the constants** (Miao, p. 229): `ρ = (βmA^{−γ})^{1/γ}` equals `(1 − A)/A`,
so the maximiser `ρx/(1 + ρ)` of the Bellman equation is the saving `(1 − A)x`, the consumption
`x/(1 + ρ)` is `Ax`, and the value coefficient `(1 + ρ)^γ` is `A^{−γ} = B`. Conversely
`B = A^{−γ}` is the envelope condition `V′(x) = B x^{−γ} = u′(Ax)`. -/
theorem ex_7_6_constants {β m γ : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) :
    let A := ex7_phA β m γ
    0 < A ∧ A < 1 ∧ (β * m * A ^ (-γ)) ^ (1 / γ) = (1 - A) / A ∧
      1 + (β * m * A ^ (-γ)) ^ (1 / γ) = A⁻¹ ∧ (1 + (β * m * A ^ (-γ)) ^ (1 / γ)) ^ γ = A ^ (-γ)
        ∧ ∀ x, 0 < x → A ^ (-γ) * x ^ (-γ) = (A * x) ^ (-γ) := by
  intro A
  have hA := (example_7_5_1_A_mem hγ hbm.le).2 ⟨hbm, hbm1⟩
  have hA0 : 0 < A := hA.1
  have h1A : 1 - A = (β * m) ^ (1 / γ) := by simp [A, ex7_phA]
  have hρ : (β * m * A ^ (-γ)) ^ (1 / γ) = (1 - A) / A := by
    rw [Real.mul_rpow hbm.le (Real.rpow_pos_of_pos hA0 _).le, ← Real.rpow_mul hA0.le,
      show -γ * (1 / γ) = -1 by field_simp, Real.rpow_neg_one, h1A]
    ring
  have hinv : 1 + (β * m * A ^ (-γ)) ^ (1 / γ) = A⁻¹ := by
    rw [hρ]; field_simp; ring
  refine ⟨hA0, hA.2, hρ, hinv, ?_, fun x hx => (Real.mul_rpow hA0.le hx.le).symm⟩
  rw [hinv, Real.inv_rpow hA0.le, ← Real.rpow_neg_one, ← Real.rpow_mul hA0.le]
  ring_nf

/-- **Exercise 7.6** (Miao, p. 229), `γ ≠ 1`: the value-function approach to Example 7.5.1. With
`m = E[R^{1−γ}]`, `0 < βm < 1`, `A = 1 − (βm)^{1/γ}`, `B = A^{−γ}` and `V(x) = B u(x)`, for every
`x > 0` the Bellman right-hand side `u(x − s) + β E V(R s)` is at most `V(x)` for every saving
`s ∈ (0, x)`, with equality at `s = (1 − A)x` (consumption `c = Ax`). -/
theorem ex_7_6_bellman {ν : Measure po61_Pos} {β γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ∫ r, r.1 ^ (1 - γ) ∂ν) (hbm1 : β * ∫ r, r.1 ^ (1 - γ) ∂ν < 1) {x : ℝ}
    (hx : 0 < x) :
    let m := ∫ r, r.1 ^ (1 - γ) ∂ν
    let A := ex7_phA β m γ
    (∀ s, 0 < s → s < x → cs_crra γ (x - s) + β * ∫ r, A ^ (-γ) * cs_crra γ (r.1 * s) ∂ν ≤
      A ^ (-γ) * cs_crra γ x) ∧
    0 < (1 - A) * x ∧ (1 - A) * x < x ∧
    cs_crra γ (x - (1 - A) * x) + β * ∫ r, A ^ (-γ) * cs_crra γ (r.1 * ((1 - A) * x)) ∂ν =
      A ^ (-γ) * cs_crra γ x := by
  intro m A
  obtain ⟨hA0, hA1, hρ, hinv, hB, -⟩ := ex_7_6_constants hγ hbm hbm1
  set K := β * m * A ^ (-γ)
  have hK : 0 < K := mul_pos hbm (Real.rpow_pos_of_pos hA0 _)
  obtain ⟨hs0, hsx, hc, hfoc⟩ := ex7_step_sol hγ hK hx
  have hsol : K ^ (1 / γ) * x / (1 + K ^ (1 / γ)) = (1 - A) * x := by
    rw [hρ]; field_simp; ring
  have hobj : ∀ s, 0 < s → cs_crra γ (x - s) + β * ∫ r, A ^ (-γ) * cs_crra γ (r.1 * s) ∂ν =
      cs_crra γ (x - s) + K * cs_crra γ s := fun s hs => by
    rw [integral_const_mul, (ex7_integral_crra hγ1 hs hm).2]; ring
  have hval : cs_crra γ (x - (1 - A) * x) + K * cs_crra γ ((1 - A) * x) =
      A ^ (-γ) * cs_crra γ x := by
    rw [← hsol, hc, ex7_step_value hγ hγ1 hK hx, hB]
  rw [hsol] at hs0 hsx hfoc
  refine ⟨fun s hs hsx' => ?_, hs0, hsx, by rw [hobj _ hs0, hval]⟩
  rw [hobj s hs, ← hval]
  exact ex7_step_max hγ hK hs0 hsx hfoc hs hsx'

/-- The constant of the log value function, `a = (ln(1 − β) + βb ln β + βb E ln R)/(1 − β)`,
`b = 1/(1 − β)`. -/
noncomputable def ex7_pha (β mℓ : ℝ) : ℝ :=
  (Real.log (1 - β) + β / (1 - β) * Real.log β + β / (1 - β) * mℓ) / (1 - β)

/-- **Exercise 7.6** (Miao, p. 229), `γ = 1`: with `V(x) = b ln x + a`, `b = 1/(1 − β)`,
`a = ex7_pha β (E ln R)`, the Bellman right-hand side `ln(x − s) + β E V(R s)` is at most `V(x)`
for every `s ∈ (0, x)`, with equality at `s = βx` (consumption `c = (1 − β)x`). -/
theorem ex_7_6_bellman_log {ν : Measure po61_Pos} [IsProbabilityMeasure ν] {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hl : Integrable (fun r : po61_Pos => Real.log r.1) ν) {x : ℝ}
    (hx : 0 < x) :
    let a := ex7_pha β (∫ r, Real.log r.1 ∂ν)
    (∀ s, 0 < s → s < x → cs_crra 1 (x - s) +
        β * ∫ r, (1 / (1 - β) * cs_crra 1 (r.1 * s) + a) ∂ν ≤ 1 / (1 - β) * cs_crra 1 x + a) ∧
    0 < β * x ∧ β * x < x ∧
    cs_crra 1 (x - β * x) + β * ∫ r, (1 / (1 - β) * cs_crra 1 (r.1 * (β * x)) + a) ∂ν =
      1 / (1 - β) * cs_crra 1 x + a := by
  intro a
  set mℓ := ∫ r, Real.log r.1 ∂ν with hmℓ
  set K := β / (1 - β)
  have h1β : 0 < 1 - β := by linarith
  have hK : 0 < K := div_pos hβ h1β
  obtain ⟨hs0, hsx, hc, hfoc⟩ := ex7_step_sol (γ := 1) one_pos hK hx
  have hsol : K ^ (1 / (1 : ℝ)) * x / (1 + K ^ (1 / (1 : ℝ))) = β * x := by
    simp only [div_one, Real.rpow_one, K]; field_simp; ring
  have hobj : ∀ s, 0 < s → cs_crra 1 (x - s) +
      β * ∫ r, (1 / (1 - β) * cs_crra 1 (r.1 * s) + a) ∂ν =
      cs_crra 1 (x - s) + K * cs_crra 1 s + (K * mℓ + β * a) := fun s hs => by
    have hi := ex7_integral_log hs hl
    rw [integral_add (hi.1.const_mul _) (integrable_const _), integral_const_mul, hi.2,
      integral_const, probReal_univ, one_smul]
    simp only [cs_crra, ↓reduceIte, K]
    ring
  have hval : cs_crra 1 (x - β * x) + K * cs_crra 1 (β * x) + (K * mℓ + β * a) =
      1 / (1 - β) * cs_crra 1 x + a := by
    rw [← hsol, hc, ex7_step_value_log hK hx]
    simp only [cs_crra, ↓reduceIte, a, ex7_pha, K]
    rw [← hmℓ]
    have e1 : 1 + β / (1 - β) = 1 / (1 - β) := by field_simp; ring
    have e2 : β / (1 - β) / (1 / (1 - β)) = β := by field_simp
    rw [e1, e2, Real.log_div one_ne_zero h1β.ne', Real.log_one]
    field_simp
    ring
  rw [hsol] at hs0 hsx hfoc
  refine ⟨fun s hs hsx' => ?_, hs0, hsx, by rw [hobj _ hs0, hval]⟩
  rw [hobj s hs, ← hval]
  have := ex7_step_max (γ := 1) one_pos hK hs0 hsx hfoc hs hsx'
  linarith

/-! ### Exercise 7.8: the finite-horizon problem and its limit -/

/-- The finite-horizon value functions of the Phelps model with `y = 0`: `v_0 = u`,
`v_{n+1}(x) = sup_{s ∈ (0, x)} u(x − s) + β ∫ v_n(R s) ν(dR)`. -/
noncomputable def ex7_phV (γ β : ℝ) (ν : Measure po61_Pos) : ℕ → ℝ → ℝ
  | 0 => fun x => cs_crra γ x
  | n + 1 => fun x => sSup ((fun s => cs_crra γ (x - s) +
      β * ∫ r, ex7_phV γ β ν n (r.1 * s) ∂ν) '' Set.Ioo 0 x)

/-- `b_0 = 1`, `b_{n+1} = 1 + ρ b_n`. -/
noncomputable def ex7_phb (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => 1 + ρ * ex7_phb ρ n

/-- `b_n = Σ_{k ≤ n} ρᵏ`, positive for `ρ ≥ 0`. -/
theorem ex7_phb_eq (ρ : ℝ) (n : ℕ) : ex7_phb ρ n = ∑ k ∈ Finset.range (n + 1), ρ ^ k := by
  induction n with
  | zero => simp [ex7_phb]
  | succ n ih =>
    rw [ex7_phb, ih, Finset.sum_range_succ' (fun k => ρ ^ k) (n + 1), Finset.mul_sum, pow_zero,
      add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ex7_phb_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 < ex7_phb ρ n := by
  induction n with
  | zero => simp [ex7_phb]
  | succ n ih => simp only [ex7_phb]; positivity

/-- **Exercise 7.8, the finite horizon** (Miao, p. 230), `y = 0`, `γ ≠ 1`: with
`m = E[R^{1−γ}] > 0`, `β > 0`, `ρ = (βm)^{1/γ}`, for every `n` and `x > 0`,
`v_n(x) = b_n^γ u(x)`, and with `n + 1` periods to go the saving `s = ρ b_n x / b_{n+1}`
(consumption `c_{n+1}(x) = x / b_{n+1}`) attains the supremum defining `v_{n+1}(x)`. -/
theorem ex_7_8_finite {ν : Measure po61_Pos} {β γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1)
    (hm : Integrable (fun r : po61_Pos => r.1 ^ (1 - γ)) ν)
    (hbm : 0 < β * ∫ r, r.1 ^ (1 - γ) ∂ν) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    let ρ := (β * ∫ r, r.1 ^ (1 - γ) ∂ν) ^ (1 / γ)
    ex7_phV γ β ν n x = ex7_phb ρ n ^ γ * cs_crra γ x ∧
      0 < ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) ∧
      ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) < x ∧
      x - ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) = x / ex7_phb ρ (n + 1) ∧
      (∀ s, 0 < s → s < x → cs_crra γ (x - s) + β * ∫ r, ex7_phV γ β ν n (r.1 * s) ∂ν ≤
        ex7_phV γ β ν (n + 1) x) ∧
      ex7_phV γ β ν (n + 1) x = cs_crra γ (x - ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1)) +
        β * ∫ r, ex7_phV γ β ν n (r.1 * (ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1))) ∂ν := by
  intro ρ
  set m := ∫ r, r.1 ^ (1 - γ) ∂ν
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hbm _
  -- the step, given the closed form at `n`
  have step : ∀ n, (∀ x, 0 < x → ex7_phV γ β ν n x = ex7_phb ρ n ^ γ * cs_crra γ x) →
      ∀ x, 0 < x →
      0 < ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) ∧
      ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) < x ∧
      x - ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) = x / ex7_phb ρ (n + 1) ∧
      (∀ s, 0 < s → s < x → cs_crra γ (x - s) + β * ∫ r, ex7_phV γ β ν n (r.1 * s) ∂ν ≤
        cs_crra γ (x - ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1)) +
        β * ∫ r, ex7_phV γ β ν n (r.1 * (ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1))) ∂ν) ∧
      cs_crra γ (x - ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1)) +
        β * ∫ r, ex7_phV γ β ν n (r.1 * (ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1))) ∂ν =
        ex7_phb ρ (n + 1) ^ γ * cs_crra γ x := by
    intro n hv x hx
    have hb := ex7_phb_pos hρ.le n
    set K := β * m * ex7_phb ρ n ^ γ
    have hK : 0 < K := mul_pos hbm (Real.rpow_pos_of_pos hb _)
    have hKρ : K ^ (1 / γ) = ρ * ex7_phb ρ n := by
      rw [Real.mul_rpow hbm.le (Real.rpow_pos_of_pos hb _).le, ← Real.rpow_mul hb.le,
        show γ * (1 / γ) = 1 by field_simp, Real.rpow_one]
    have hb1 : 1 + K ^ (1 / γ) = ex7_phb ρ (n + 1) := by rw [hKρ]; rfl
    have hsol : K ^ (1 / γ) * x / (1 + K ^ (1 / γ)) = ρ * ex7_phb ρ n * x / ex7_phb ρ (n + 1) :=
      by rw [← hb1, hKρ]
    obtain ⟨hs0, hsx, hc, hfoc⟩ := ex7_step_sol hγ hK hx
    have hobj : ∀ s, 0 < s → cs_crra γ (x - s) + β * ∫ r, ex7_phV γ β ν n (r.1 * s) ∂ν =
        cs_crra γ (x - s) + K * cs_crra γ s := fun s hs => by
      have e : (fun r : po61_Pos => ex7_phV γ β ν n (r.1 * s)) =
          fun r => ex7_phb ρ n ^ γ * cs_crra γ (r.1 * s) :=
        funext fun r => hv _ (mul_pos r.2 hs)
      rw [e, integral_const_mul, (ex7_integral_crra hγ1 hs hm).2]
      ring
    have hval := ex7_step_value hγ hγ1 hK hx
    rw [hsol] at hs0 hsx hfoc hc hval
    rw [hb1] at hc hval
    refine ⟨hs0, hsx, hc, fun s hs hsx' => ?_, ?_⟩
    · rw [hobj s hs, hobj _ hs0]
      exact ex7_step_max hγ hK hs0 hsx hfoc hs hsx'
    · rw [hobj _ hs0, hc, hval]
  have closed : ∀ n, ∀ x, 0 < x → ex7_phV γ β ν n x = ex7_phb ρ n ^ γ * cs_crra γ x := by
    intro n
    induction n with
    | zero => intro x _; simp [ex7_phV, ex7_phb]
    | succ n ih =>
      intro x hx
      obtain ⟨hs0, hsx, -, hle, heq⟩ := step n ih x hx
      change sSup _ = _
      rw [← heq]
      refine IsGreatest.csSup_eq ⟨⟨_, ⟨hs0, hsx⟩, rfl⟩, ?_⟩
      rintro _ ⟨s, ⟨hs, hsx'⟩, rfl⟩
      exact hle s hs hsx'
  obtain ⟨hs0, hsx, hc, hle, heq⟩ := step n (closed n) x hx
  refine ⟨closed n x hx, hs0, hsx, hc, fun s hs hsx' => ?_, ?_⟩
  · rw [closed (n + 1) x hx, ← heq]; exact hle s hs hsx'
  · rw [closed (n + 1) x hx, heq]

/-- **Exercise 7.8, the limit** (Miao, p. 230): for `0 < ρ = (βm)^{1/γ} < 1` (i.e. `0 < βm < 1`),
the consumption share `1/b_n` of the finite-horizon policy tends to `1 − ρ = A`, the share of
Example 7.5.1 ((7.39)), and the value coefficient `b_n^γ` tends to `A^{−γ} = B` of
Exercise 7.6. -/
theorem ex_7_8_limit {β m γ : ℝ} (hγ : 0 < γ) (hbm : 0 < β * m) (hbm1 : β * m < 1) :
    Tendsto (fun n => (ex7_phb ((β * m) ^ (1 / γ)) n)⁻¹) atTop (𝓝 (ex7_phA β m γ)) ∧
      Tendsto (fun n => ex7_phb ((β * m) ^ (1 / γ)) n ^ γ) atTop
        (𝓝 (ex7_phA β m γ ^ (-γ))) := by
  set ρ := (β * m) ^ (1 / γ)
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hbm _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hbm.le hbm1 (by positivity)
  have hA : ex7_phA β m γ = 1 - ρ := rfl
  have hgeo : Tendsto (fun n => ex7_phb ρ n) atTop (𝓝 (1 - ρ)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hρ0.le hρ1).tendsto_sum_nat
    have h2 := this.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun n => ?_
    simp [ex7_phb_eq]
  have hpos : 0 < 1 - ρ := by linarith
  refine ⟨?_, ?_⟩
  · rw [hA]
    simpa using hgeo.inv₀ (inv_ne_zero hpos.ne')
  · rw [hA, Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
    exact hgeo.rpow_const (Or.inl (inv_ne_zero hpos.ne'))

end Miao.InfiniteHorizonDP
