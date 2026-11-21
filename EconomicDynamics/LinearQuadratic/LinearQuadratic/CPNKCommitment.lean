/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.CPRamsey
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The New Keynesian model under commitment: Examples 9.4.1 and 9.4.2

Miao, §9.4, pp. 305–311.

**Example 9.4.1** (p. 305). The basic New Keynesian model (9.20)–(9.21) with predetermined
variables `(1, z_t, Ŷ^f_t, r^n_t)` (`Fin 4`), forward-looking variables `(π_t, x_t)` (`Fin 2`)
and instrument `i_t` (`Fin 1`).
* `example_9_4_1`: the model is the state-space form (9.18) with the explicit `D`, `A`, `B`, `C`
  (`ex941D`, …); the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` becomes the
  predetermined law `r^n_{t+1} = −(1 − ρ_y)ln β + ρ_y r^n_t + γ(ρ_y − 1)ε_{y,t+1}`, which is
  consistent with the definition at every date (`example_9_4_1_rn`).
* `example_9_4_1_loss`: with unity in the state, `½(π_t − π*)² + ½λx_t²` is the loss (9.19)
  for an explicit symmetric `Q` and `R = 0`, `S = 0`.

**Example 9.4.2** (pp. 308–311). Commitment in the model (9.23) with `z_{t+1} = ρz_t + ε_{t+1}`.
* `eq_9_25`, `eq_9_26`, `eq_9_27`: the derivatives of the (horizon-`T`, perfect-foresight)
  Lagrangian `ex942Lagr` in `π_s`, `x_s`, `z_s` are `βˢ` times the left sides of (9.25)–(9.27)
  (with `μ_{x0} = 0`); `cp_stationary_iff` turns this into the first-order conditions.
* `example_9_4_2_system` (p. 310): (9.25)–(9.27), (9.23) and the shock law are the printed
  `5 × 5` system (with the fourth row of the left matrix corrected, see below).
* `eq_9_28`: (9.25), (9.26) and (9.23) give the second-order equation (9.28).
* `eq_9_29`: for `κ ≠ 0`, `λ > 0`, `0 < β < 1`, the characteristic equation (9.29) has exactly
  the two real roots `0 < a₁ < 1 < a₂` (`ex942a`), with `a₁a₂ = 1/β`.
* `ex942_lag_sum`: the lag-operator expression
  `−(1/(β²a₂))∑ⱼ a₂⁻ʲ(κx* + E_t z_{t+j})` equals `−(a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))`.
* `ex942_rule_solves`, `ex942_rule_expected`: the rule
  `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))` solves (9.28) in expectation, for
  any mean-zero shock; `ex942_unique_bounded`: every bounded solution of (9.28) along the
  expected path `E_0 z_t = ρᵗz₀` follows the rule (the forward inversion of `L⁻¹ − a₂`).
* `ex942_solution`: with `μ_{x0} = 0`, the rule and `π_t = β(μ_{xt} − μ_{x,t+1})`,
  `x_t = x* + (βκ/λ)μ_{x,t+1}` solve (9.23), (9.25), (9.26); `ex942_muz`: the forward sum
  `μ_{zt} = −β∑ⱼ(βρ)ʲμ_{x,t+1+j}` solves (9.27) — `μ_z` plays no role in the other variables
  (footnote 4).
* `ex942_time_inconsistent`: reoptimising at date 1 (restarting from `μ_{x1} = 0`) changes
  inflation at date 1 by `−β(1 − a)μ_{x1} ≠ 0` whenever `κx*/(1 − βa) + z₀/(1 − βaρ) ≠ 0`.

**Corrections.** (9.29) has roots `0 < a₁ < 1 < a₂` only if `κ ≠ 0`; for `κ = 0` the roots are
`1` and `1/β` (`eq_9_29_kappa_zero`). In our text extraction the fourth row of the left matrix
on p. 310 reads `(0, β, 0, 0, 0)`; the row that gives (9.23) is `(0, 0, 0, β, 0)`, and with the
extracted row the system does not imply (9.23) (`example_9_4_2_printed_row_false`). The book's
expectations `E_t` are replaced by the expected (perfect-foresight) paths, except in
`ex942_rule_expected`.
-/

namespace Miao.LinearQuadratic

open scoped Matrix
open Filter Topology MeasureTheory

/-! ### Example 9.4.1 -/

/-- `D` of Example 9.4.1: `[I 0; 0 D₂₂]` with `D₂₂ = [β 0; 1/γ 1]`. -/
noncomputable def ex941D (β γ : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 1 0 0 !![β, 0; 1 / γ, 1]

/-- `A` of Example 9.4.1. -/
noncomputable def ex941A (β γ κ ρz ρy : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1, 0, 0, 0; 0, ρz, 0, 0; 0, 0, ρy, 0; -(1 - ρy) * Real.log β, 0, 0, ρy] 0
    !![0, -1, 0, 0; 0, 0, 0, -(1 / γ)] !![1, -κ; 0, 1]

/-- `B` of Example 9.4.1. -/
noncomputable def ex941B (γ : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 1) ℝ :=
  Matrix.fromRows 0 !![0; 1 / γ]

/-- `C` of Example 9.4.1 (shocks `(ε_z, ε_y)`). -/
def ex941C (γ ρy : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![0, 0; 1, 0; 0, 1; 0, γ * (ρy - 1)]

/-- **Example 9.4.1** (Miao, p. 305). With `z = (1, z, Ŷ^f, r^n)`, `y = (π, x)`, `u = i`, the
state-space form (9.18) `D[z'; E y'] = A[z; y] + Bu + [Cε'; 0]` holds iff unity stays unity,
`z' = ρ_z z + ε_z'`, `Ŷ' = ρ_yŶ + ε_y'`,
`r^n' = −(1 − ρ_y)ln β + ρ_y r^n + γ(ρ_y − 1)ε_y'`, and (9.20)–(9.21) hold:
`π = κx + βE π' + z` and `x = E x' − (1/γ)(i − E π' − r^n)`. -/
theorem example_9_4_1 (β γ κ ρz ρy : ℝ) (z z' : Fin 4 → ℝ) (y Ey : Fin 2 → ℝ) (i : Fin 1 → ℝ)
    (e : Fin 2 → ℝ) :
    ex941D β γ *ᵥ Sum.elim z' Ey =
        ex941A β γ κ ρz ρy *ᵥ Sum.elim z y + ex941B γ *ᵥ i + Sum.elim (ex941C γ ρy *ᵥ e) 0 ↔
      (z' 0 = z 0 ∧ z' 1 = ρz * z 1 + e 0 ∧ z' 2 = ρy * z 2 + e 1 ∧
        z' 3 = -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1) ∧
      y 0 = κ * y 1 + β * Ey 0 + z 1 ∧ y 1 = Ey 1 - 1 / γ * (i 0 - Ey 0 - z 3) := by
  have hD : ex941D β γ *ᵥ Sum.elim z' Ey =
      Sum.elim z' ![β * Ey 0, 1 / γ * Ey 0 + Ey 1] := by
    ext (j | j) <;> fin_cases j <;>
      simp [ex941D, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply,
        Fin.succ_zero_eq_one]
  have hA : ex941A β γ κ ρz ρy *ᵥ Sum.elim z y + ex941B γ *ᵥ i + Sum.elim (ex941C γ ρy *ᵥ e) 0 =
      Sum.elim ![z 0, ρz * z 1 + e 0, ρy * z 2 + e 1,
          -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1]
        ![-z 1 + y 0 - κ * y 1, -(1 / γ) * z 3 + y 1 + 1 / γ * i 0] := by
    ext (j | j) <;> fin_cases j <;>
      simp [ex941A, ex941B, ex941C, Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec,
        dotProduct, Fin.sum_univ_succ]
    ring
  rw [hD, hA, Sum.elim_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have a0 : z' 0 = z 0 := congrFun h1 0
    have a1 : z' 1 = ρz * z 1 + e 0 := congrFun h1 1
    have a2 : z' 2 = ρy * z 2 + e 1 := congrFun h1 2
    have a3 : z' 3 = -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1 :=
      congrFun h1 3
    have b0 : β * Ey 0 = -z 1 + y 0 - κ * y 1 := congrFun h2 0
    have b1 : 1 / γ * Ey 0 + Ey 1 = -(1 / γ) * z 3 + y 1 + 1 / γ * i 0 := congrFun h2 1
    refine ⟨⟨a0, a1, a2, a3⟩, by linarith, by linarith⟩
  · rintro ⟨⟨a0, a1, a2, a3⟩, b0, b1⟩
    refine ⟨funext fun j => ?_, funext fun j => ?_⟩
    · fin_cases j
      · exact a0
      · exact a1
      · exact a2
      · exact a3
    · fin_cases j
      · change β * Ey 0 = -z 1 + y 0 - κ * y 1
        linarith
      · change 1 / γ * Ey 0 + Ey 1 = -(1 / γ) * z 3 + y 1 + 1 / γ * i 0
        linarith

/-- Miao, p. 305: the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)`, with
`E_tŶ^f_{t+1} = ρ_yŶ^f_t`, is reproduced at `t + 1` by the predetermined law of
`example_9_4_1`. -/
theorem example_9_4_1_rn (β γ ρy Yf r Yf' r' ey : ℝ)
    (hr : r = -Real.log β + γ * (ρy * Yf - Yf)) (hY : Yf' = ρy * Yf + ey)
    (hr' : r' = -(1 - ρy) * Real.log β * 1 + ρy * r + γ * (ρy - 1) * ey) :
    r' = -Real.log β + γ * (ρy * Yf' - Yf') := by
  rw [hr', hr, hY]
  ring

/-- `Q` of Example 9.4.1: the loss `½(π − π*)² + ½λx²` with unity in the state. -/
def ex941Q (πs lam : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![πs ^ 2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![-πs, 0; 0, 0; 0, 0; 0, 0] !![-πs, 0, 0, 0; 0, 0, 0, 0] !![1, 0; 0, lam]

/-- **Example 9.4.1, the loss** (Miao, p. 305): with `z₀ = 1` (unity), `½(π_t − π*)² + ½λx_t²`
is the loss (9.19) with the symmetric `Q = ex941Q`, `R = 0`, `S = 0`. -/
theorem example_9_4_1_loss (πs lam : ℝ) (z : Fin 4 → ℝ) (hz : z 0 = 1) (y : Fin 2 → ℝ)
    (i : Fin 1 → ℝ) :
    (1 / 2) * (y 0 - πs) ^ 2 + (1 / 2) * lam * y 1 ^ 2 =
      cpLoss (ex941Q πs lam) (0 : Matrix (Fin 4 ⊕ Fin 2) (Fin 1) ℝ) 0 (Sum.elim z y) i ∧
    (ex941Q πs lam)ᵀ = ex941Q πs lam := by
  refine ⟨?_, ?_⟩
  · simp [cpLoss, ex941Q, Matrix.fromBlocks_mulVec, dotProduct, Fin.sum_univ_succ,
      Fintype.sum_sum_type, hz]
    ring
  · rw [ex941Q, Matrix.fromBlocks_transpose]
    congr 1 <;> ext a b <;> fin_cases a <;> fin_cases b <;> rfl

/-! ### Example 9.4.2: the Lagrangian and the first-order conditions -/

/-- The perturbation `f_s ↦ f_s + a` of one date. -/
def cpPert (f : ℕ → ℝ) (s : ℕ) (a : ℝ) : ℕ → ℝ := fun t => f t + if t = s then a else 0

theorem cp_pert_zero (f : ℕ → ℝ) (s : ℕ) : cpPert f s 0 = f := by
  funext t
  simp [cpPert]

theorem cp_sum_delta {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t = s then a else 0) * g t = a * g s := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]

theorem cp_sum_delta_sq {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t = s then a else 0) ^ 2 * g t = a ^ 2 * g s := by
  simp only [ite_pow, ite_mul, zero_pow two_ne_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, hs, ↓reduceIte]

theorem cp_sum_delta_succ {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t + 1 = s then a else 0) * g t =
      if s = 0 then 0 else a * g (s - 1) := by
  by_cases h0 : s = 0
  · simp only [h0, Nat.add_one_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  · have hr : s - 1 < T := by omega
    have hiff : ∀ t, (t + 1 = s) ↔ (t = s - 1) := fun t => by omega
    simp only [hiff, ite_mul, zero_mul, h0, Finset.sum_ite_eq', Finset.mem_range, hr,
      ↓reduceIte]

/-- A function that is exactly `c + ab + a²d` has derivative `b` at `0`. -/
theorem cp_hasDerivAt_quad {f : ℝ → ℝ} {b c d : ℝ} (hf : ∀ a, f a = c + a * b + a ^ 2 * d) :
    HasDerivAt f b 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add c).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const d)
  have hf' : f = (fun a => c + id a * b) + fun a => a ^ 2 * d := by
    funext a
    rw [hf a, Pi.add_apply, id]
  rw [hf']
  convert this using 1
  simp

/-- Stationarity: if the derivative is `βˢg` with `β ≠ 0`, it vanishes iff `g = 0`. -/
theorem cp_stationary_iff {f : ℝ → ℝ} {β g : ℝ} (s : ℕ) (hβ : β ≠ 0)
    (hf : HasDerivAt f (β ^ s * g) 0) : HasDerivAt f 0 0 ↔ g = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.1 (hf.unique h) with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hβ)
    · exact h1
  · intro h
    rwa [h, mul_zero] at hf

/-- The Lagrangian of Example 9.4.2 (Miao, p. 309), truncated at `T`, along given paths:
`∑_{t<T} βᵗ[½π_t² + ½λ(x_t − x*)² − βμ_{z,t+1}(z_{t+1} − ρz_t − ε_{t+1})
− βμ_{x,t+1}(κx_t + βπ_{t+1} + z_t − π_t)] − μ_{z0}(z₀ − z̄₀)`. -/
noncomputable def ex942Lagr (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) (T : ℕ)
    (pin x z : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) -
    μz 0 * (z 0 - zbar)

/-- Miao, (9.25), p. 309: with `μ_{x0} = 0`, the derivative of the Lagrangian in `π_s`
(`s < T`) is `βˢ(π_s + βμ_{x,s+1} − βμ_{xs})`. -/
theorem eq_9_25 (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) (hμ0 : μx 0 = 0) {T s : ℕ}
    (hs : s < T) (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T (cpPert pin s a) x z)
      (β ^ s * (pin s + β * μx (s + 1) - β * μx s)) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := β ^ s * (1 / 2)) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * cpPert pin s a t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * cpPert pin s a (t + 1) + z t - cpPert pin s a t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (pin t + β * μx (t + 1))) +
      (if t + 1 = s then a else 0) * (-(β ^ (t + 1) * β * μx (t + 1))) +
      (if t = s then a else 0) ^ 2 * (β ^ t * (1 / 2)) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, cp_sum_delta hs, cp_sum_delta_succ hs, cp_sum_delta_sq hs]
  by_cases h0 : s = 0
  · subst h0
    simp only [↓reduceIte, hμ0]
    ring
  · simp only [h0, ↓reduceIte, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    ring

/-- Miao, (9.26), p. 309: the derivative of the Lagrangian in `x_s` (`s < T`) is
`βˢ(λ(x_s − x*) − βκμ_{x,s+1})`. -/
theorem eq_9_26 (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) {T s : ℕ} (hs : s < T)
    (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T pin (cpPert x s a) z)
      (β ^ s * (lam * (x s - xs) - β * κ * μx (s + 1))) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := β ^ s * (lam / 2)) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * pin t ^ 2 +
      (1 / 2) * lam * (cpPert x s a t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * cpPert x s a t + β * pin (t + 1) + z t - pin t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (lam * (x t - xs) - β * κ * μx (t + 1))) +
      (if t = s then a else 0) ^ 2 * (β ^ t * (lam / 2)) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    cp_sum_delta hs, cp_sum_delta_sq hs]
  ring

/-- Miao, (9.27), p. 309: the derivative of the Lagrangian in `z_s` (`s < T`) is
`βˢ(−βμ_{x,s+1} + βρμ_{z,s+1} − μ_{zs})`. -/
theorem eq_9_27 (β κ lam ρ xs zbar : ℝ) (hβ : β ≠ 0) (eps μx μz : ℕ → ℝ) {T s : ℕ}
    (hs : s < T) (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x (cpPert z s a))
      (β ^ s * (-(β * μx (s + 1)) + β * ρ * μz (s + 1) - μz s)) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := 0) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (cpPert z s a (t + 1) - ρ * cpPert z s a t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * pin (t + 1) + cpPert z s a t - pin t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (β * ρ * μz (t + 1) - β * μx (t + 1))) +
      (if t + 1 = s then a else 0) * (-(β ^ (t + 1) * μz (t + 1))) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    cp_sum_delta hs, cp_sum_delta_succ hs]
  by_cases h0 : s = 0
  · subst h0
    simp only [cpPert, ↓reduceIte]
    ring
  · have h0' : ¬ (0 = s) := fun h => h0 h.symm
    have hp : β ^ s = β ^ (s - 1 + 1) := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    simp only [cpPert, h0, h0', ↓reduceIte, add_zero]
    rw [hp, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    have := hβ
    ring

/-! ### Example 9.4.2: the system and its solution -/

/-- The left matrix of the system on p. 310 (fourth row corrected), in the variables
`(z, μ_x, x, π, μ_z)`. -/
def ex942L (β κ ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, β, 0, 0, 0; 0, β * κ, 0, 0, 0; 0, 0, 0, β, 0; 0, -β, 0, 0, β * ρ]

/-- The right matrix of the system on p. 310. -/
def ex942R (β κ lam ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ρ, 0, 0, 0, 0; 0, β, 0, -1, 0; 0, 0, lam, 0, 0; -1, 0, -κ, 1, 0; 0, 0, 0, 0, 1]

/-- **Example 9.4.2, the system** (Miao, p. 310). For `v = (z_t, μ_{xt}, x_t, π_t, μ_{zt})` and
`v' = E_t v_{t+1}`, `Lv' = Rv − (0, 0, λx*, 0, 0)` iff `E_t z_{t+1} = ρz_t`, (9.25), (9.26),
(9.23) and (9.27) hold. -/
theorem example_9_4_2_system (β κ lam ρ xs : ℝ) (v v' : Fin 5 → ℝ) :
    ex942L β κ ρ *ᵥ v' = ex942R β κ lam ρ *ᵥ v - ![0, 0, lam * xs, 0, 0] ↔
      v' 0 = ρ * v 0 ∧ v 3 + β * v' 1 - β * v 1 = 0 ∧ lam * (v 2 - xs) - β * κ * v' 1 = 0 ∧
      v 3 = κ * v 2 + β * v' 3 + v 0 ∧ -(β * v' 1) + β * ρ * v' 4 - v 4 = 0 := by
  have hL : ex942L β κ ρ *ᵥ v' = ![v' 0, β * v' 1, β * κ * v' 1, β * v' 3,
      -β * v' 1 + β * ρ * v' 4] := by
    ext j
    fin_cases j <;> simp [ex942L, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hR : ex942R β κ lam ρ *ᵥ v - ![0, 0, lam * xs, 0, 0] = ![ρ * v 0, β * v 1 - v 3,
      lam * v 2 - lam * xs, -v 0 - κ * v 2 + v 3, v 4] := by
    ext j
    fin_cases j <;> simp [ex942R, dotProduct, Fin.sum_univ_succ] <;> ring
  rw [hL, hR]
  constructor
  · intro h
    have a0 : v' 0 = ρ * v 0 := congrFun h 0
    have a1 : β * v' 1 = β * v 1 - v 3 := congrFun h 1
    have a2 : β * κ * v' 1 = lam * v 2 - lam * xs := congrFun h 2
    have a3 : β * v' 3 = -v 0 - κ * v 2 + v 3 := congrFun h 3
    have a4 : -β * v' 1 + β * ρ * v' 4 = v 4 := congrFun h 4
    refine ⟨a0, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a0, a1, a2, a3, a4⟩
    funext j
    fin_cases j
    · exact a0
    · change β * v' 1 = β * v 1 - v 3
      linarith
    · change β * κ * v' 1 = lam * v 2 - lam * xs
      linarith
    · change β * v' 3 = -v 0 - κ * v 2 + v 3
      linarith
    · change -β * v' 1 + β * ρ * v' 4 = v 4
      linarith

/-- The left matrix as it appears in our extraction of p. 310 (fourth row `(0, β, 0, 0, 0)`). -/
def ex942Lprinted (β κ ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, β, 0, 0, 0; 0, β * κ, 0, 0, 0; 0, β, 0, 0, 0; 0, -β, 0, 0, β * ρ]

/-- Correction (Miao, p. 310): with the fourth row `(0, β, 0, 0, 0)`, the system does not
imply (9.23): for `β = 1/2`, `κ = λ = 1`, `ρ = x* = 0` the point `v = 0`, `v' = (0,0,0,1,0)`
solves it but `π_t ≠ κx_t + βE_tπ_{t+1} + z_t`. -/
theorem example_9_4_2_printed_row_false :
    ex942Lprinted (1 / 2) 1 0 *ᵥ ![0, 0, 0, 1, 0] = ex942R (1 / 2) 1 1 0 *ᵥ ![0, 0, 0, 0, 0] -
      ![0, 0, 1 * 0, 0, 0] ∧
    ¬ ((![0, 0, 0, 0, 0] : Fin 5 → ℝ) 3 = 1 * (![0, 0, 0, 0, 0] : Fin 5 → ℝ) 2 +
      (1 / 2) * (![0, 0, 0, 1, 0] : Fin 5 → ℝ) 3 + (![0, 0, 0, 0, 0] : Fin 5 → ℝ) 0) := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;> simp [ex942Lprinted, ex942R, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num

/-- Miao, (9.28), p. 310: (9.25) at `t` and `t + 1`, (9.26) at `t` and (9.23) at `t` (in
expected values) give `βμ_{t+2} − (1 + β + κ²/λ)μ_{t+1} + μ_t = κx*/β + z_t/β`. -/
theorem eq_9_28 {β κ lam xs : ℝ} (hβ : β ≠ 0) (hlam : lam ≠ 0) (pin x z μ : ℕ → ℝ) (t : ℕ)
    (h25 : pin t + β * μ (t + 1) - β * μ t = 0)
    (h25' : pin (t + 1) + β * μ (t + 2) - β * μ (t + 1) = 0)
    (h26 : lam * (x t - xs) - β * κ * μ (t + 1) = 0)
    (h23 : pin t = κ * x t + β * pin (t + 1) + z t) :
    β * μ (t + 2) - (1 + β + κ ^ 2 / lam) * μ (t + 1) + μ t = κ * xs / β + z t / β := by
  have hx : x t = xs + β * κ / lam * μ (t + 1) := by
    field_simp
    linarith
  have hp : pin t = β * (μ t - μ (t + 1)) := by linarith
  have hp' : pin (t + 1) = β * (μ (t + 1) - μ (t + 2)) := by linarith
  rw [hx, hp, hp'] at h23
  have key : β * (β * μ (t + 2) - (1 + β + κ ^ 2 / lam) * μ (t + 1) + μ t) = κ * xs + z t := by
    linear_combination h23
  rw [← add_div, eq_div_iff hβ]
  linear_combination key

/-- The coefficient `1 + β + κ²/λ` of (9.28). -/
noncomputable def ex942b (β κ lam : ℝ) : ℝ := 1 + β + κ ^ 2 / lam

/-- The stable root `a₁` of (9.29). -/
noncomputable def ex942a (β κ lam : ℝ) : ℝ :=
  (ex942b β κ lam - Real.sqrt (ex942b β κ lam ^ 2 - 4 * β)) / (2 * β)

/-- A root `a ≠ 0` of (9.29) gives `1 + β + κ²/λ = βa + 1/a`. -/
theorem ex942_b_eq {β κ lam a : ℝ} (ha : a ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) : ex942b β κ lam = β * a + a⁻¹ := by
  have h1 : ex942b β κ lam * a = β * a ^ 2 + 1 := by linear_combination (-1) * hroot
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  linear_combination a⁻¹ * h1 - (ex942b β κ lam - β * a) * hia

/-- **The characteristic equation (9.29)** (Miao, p. 310). For `0 < β < 1`, `λ > 0`, `κ ≠ 0`,
`βa² − (1 + β + κ²/λ)a + 1 = 0` has the two real roots `a₁ = ex942a` and `a₂ = 1/(βa₁)`, with
`0 < a₁ < 1 < a₂`, and no others. -/
theorem eq_9_29 {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) (hκ : κ ≠ 0) :
    let a := ex942a β κ lam
    0 < a ∧ a < 1 ∧ 1 < 1 / (β * a) ∧
      β * a ^ 2 - ex942b β κ lam * a + 1 = 0 ∧
      β * (1 / (β * a)) ^ 2 - ex942b β κ lam * (1 / (β * a)) + 1 = 0 ∧
      ∀ r, β * r ^ 2 - ex942b β κ lam * r + 1 = 0 ↔ r = a ∨ r = 1 / (β * a) := by
  intro a
  set b := ex942b β κ lam with hb
  have hk2 : 0 < κ ^ 2 / lam := div_pos (by positivity) hlam
  have hb1 : 1 + β < b := by rw [hb, ex942b]; linarith
  have hD : 0 ≤ b ^ 2 - 4 * β := by nlinarith
  set q := Real.sqrt (b ^ 2 - 4 * β) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = b ^ 2 - 4 * β := Real.sq_sqrt hD
  have hqb : q < b := by nlinarith
  have hqb2 : b - 2 * β < q := by nlinarith
  have ha : a = (b - q) / (2 * β) := rfl
  have hapos : 0 < a := by rw [ha]; apply div_pos <;> linarith
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; linarith
  have hroot : β * a ^ 2 - b * a + 1 = 0 := by
    rw [ha]
    field_simp
    nlinarith
  have hβa : 0 < β * a := mul_pos hβ0 hapos
  have hβa1 : β * a < 1 := by nlinarith
  have ha2 : 1 < 1 / (β * a) := by rw [lt_div_iff₀ hβa]; linarith
  have hb' : b = β * a + a⁻¹ := ex942_b_eq hapos.ne' hroot
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hapos.ne'
  have hib : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ0.ne'
  have hfac : ∀ r, β * r ^ 2 - b * r + 1 = β * (r - a) * (r - 1 / (β * a)) := by
    intro r
    rw [hb']
    linear_combination (a⁻¹ * r - 1) * hib - β * β⁻¹ * hia
  have hroot2 : β * (1 / (β * a)) ^ 2 - b * (1 / (β * a)) + 1 = 0 := by
    rw [hfac]
    ring
  refine ⟨hapos, ha1, ha2, hroot, hroot2, fun r => ?_⟩
  rw [hfac r]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hβ0.ne'
      · exact Or.inl (sub_eq_zero.1 h2)
    · exact Or.inr (sub_eq_zero.1 h1)
  · rintro (h | h) <;> rw [h] <;> ring

/-- Correction to (9.29) (Miao, p. 310): for `κ = 0` the roots are `1` and `1/β`, so
`0 < a₁ < 1 < a₂` fails. -/
theorem eq_9_29_kappa_zero {β lam : ℝ} (hβ : β ≠ 0) :
    β * 1 ^ 2 - ex942b β 0 lam * 1 + 1 = 0 ∧
      β * (1 / β) ^ 2 - ex942b β 0 lam * (1 / β) + 1 = 0 := by
  simp only [ex942b]
  constructor
  · ring
  · field_simp
    ring

/-- Miao, p. 311: with `a₂ = 1/(βa)`, `0 < βa < 1` and `|ρ| ≤ 1`, the forward (lag-operator)
sum `−(1/(β²a₂))∑ⱼ a₂⁻ʲ(κx* + ρʲz)` equals `−(a/β)(κx*/(1 − βa) + z/(1 − βaρ))`
(`E_t z_{t+j} = ρʲz_t`). -/
theorem ex942_lag_sum {β a ρ κ xs z : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a) (ha1 : β * a < 1)
    (hρ : |ρ| ≤ 1) :
    -(1 / (β ^ 2 * (1 / (β * a)))) * ∑' j : ℕ, ((1 / (β * a)) ^ j)⁻¹ * (κ * xs + ρ ^ j * z) =
      -(a / β) * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ)) := by
  have h1 : |β * a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have h2 : |β * a * ρ| < 1 := by
    rw [abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg ρ]
  have hs1 := summable_geometric_of_abs_lt_one h1
  have hs2 := summable_geometric_of_abs_lt_one h2
  have hterm : ∀ j : ℕ, ((1 / (β * a)) ^ j)⁻¹ * (κ * xs + ρ ^ j * z) =
      κ * xs * (β * a) ^ j + z * (β * a * ρ) ^ j := fun j => by
    rw [one_div, inv_pow, inv_inv, mul_pow]
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ha0
  have hd1 : 1 - β * a ≠ 0 := by linarith
  have hd2 : 1 - β * a * ρ ≠ 0 := by
    have := (abs_lt.1 h2).2
    linarith
  rw [tsum_congr hterm, (hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one h1, tsum_geometric_of_abs_lt_one h2]
  field_simp

/-- The commitment rule for the multiplier (Miao, p. 311):
`μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))`. -/
noncomputable def ex942Rule (β κ ρ xs a μ z : ℝ) : ℝ :=
  a * μ - a / β * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ))

/-- Miao, p. 311: if `a` is a root of (9.29), the rule solves (9.28) in expectation:
with `μ_{t+1}` given by the rule and `E_tμ_{t+2} = rule(μ_{t+1}, E_t z_{t+1})`,
`E_t z_{t+1} = ρz_t`, (9.28) holds. -/
theorem ex942_rule_solves {β κ lam ρ xs a : ℝ} (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hd2 : 1 - β * a * ρ ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (μ z : ℝ) :
    β * ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a μ z) (ρ * z) -
        ex942b β κ lam * ex942Rule β κ ρ xs a μ z + μ = κ * xs / β + z / β := by
  have hia : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have hK : κ * xs / (1 - β * a) * (1 - β * a) = κ * xs := div_mul_cancel₀ _ hd1
  have hc : (1 - β * a * ρ)⁻¹ * (1 - β * a * ρ) = 1 := inv_mul_cancel₀ hd2
  rw [ex942_b_eq ha hroot, ex942Rule, ex942Rule]
  linear_combination (-μ + β⁻¹ * (κ * xs / (1 - β * a)) + β⁻¹ * (1 - β * a * ρ)⁻¹ * z) * hia +
    β⁻¹ * hK + β⁻¹ * z * hc

/-- Miao, p. 311 (the conditional expectation): for a mean-zero integrable shock `ε` with
`z_{t+1} = ρz_t + ε`, `E_t μ_{x,t+2} = E[rule(μ_{x,t+1}, ρz_t + ε)] = rule(μ_{x,t+1}, ρz_t)`. -/
theorem ex942_rule_expected {β κ ρ xs a : ℝ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun e => e) ν) (hmean : ∫ e, e ∂ν = 0) (μ z : ℝ) :
    ∫ e, ex942Rule β κ ρ xs a μ (ρ * z + e) ∂ν = ex942Rule β κ ρ xs a μ (ρ * z) := by
  have h : ∀ e, ex942Rule β κ ρ xs a μ (ρ * z + e) =
      ex942Rule β κ ρ xs a μ (ρ * z) + (-(a / β) / (1 - β * a * ρ)) * e := fun e => by
    simp only [ex942Rule]
    ring
  simp only [h]
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
    hmean]
  simp

/-- **Uniqueness of the bounded solution** (Miao, p. 311: inverting `L⁻¹ − a₂` forward). Let
`a` be a root of (9.29) with `0 < βa < 1`, `|ρ| ≤ 1`, and let `z_{t+1} = ρz_t` (the expected
path). Every bounded solution of (9.28) follows the rule `μ_{t+1} = rule(μ_t, z_t)`. -/
theorem ex942_unique_bounded {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a)
    (ha1 : β * a < 1) (hρ : |ρ| ≤ 1) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0)
    (z μ : ℕ → ℝ) (hz : ∀ t, z (t + 1) = ρ * z t)
    (h28 : ∀ t, β * μ (t + 2) - ex942b β κ lam * μ (t + 1) + μ t = κ * xs / β + z t / β)
    (hμb : ∃ M, ∀ t, |μ t| ≤ M) :
    ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (z t) := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ha0
  have hd1 : 1 - β * a ≠ 0 := by linarith
  have h2 : |β * a * ρ| < 1 := by
    rw [abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg ρ]
  have hd2 : 1 - β * a * ρ ≠ 0 := by
    have := (abs_lt.1 h2).2
    linarith
  have hb : ex942b β κ lam = β * a + a⁻¹ := ex942_b_eq ha hroot
  have hib : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  set e : ℕ → ℝ := fun t => μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t) with he
  have hrec : ∀ t, e (t + 1) = 1 / (β * a) * e t := by
    intro t
    have h := h28 t
    have hs := ex942_rule_solves (κ := κ) (lam := lam) (xs := xs) ha hd1 hd2 hroot (μ t) (z t)
    rw [hb] at h hs
    have hlin : ex942Rule β κ ρ xs a (μ (t + 1)) (ρ * z t) =
        ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a (μ t) (z t)) (ρ * z t) +
          a * (μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t)) := by
      simp only [ex942Rule]
      ring
    simp only [he, hz t, hlin]
    linear_combination β⁻¹ * h - β⁻¹ * hs -
      ((μ (t + 1 + 1) - ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a (μ t) (z t)) (ρ * z t)) -
        a * (μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t))) * hib
  have hpow : ∀ t, e t = (1 / (β * a)) ^ t * e 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hzb : ∀ t, |z t| ≤ |z 0| := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hz, abs_mul]
      nlinarith [abs_nonneg (z n)]
  obtain ⟨M, hM⟩ := hμb
  have heb : ∀ t, |e t| ≤ M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| +
      |z 0| / |1 - β * a * ρ|) := by
    intro t
    simp only [he, ex942Rule]
    have h1 := hM (t + 1)
    have h2 := hM t
    have h3 : |z t / (1 - β * a * ρ)| ≤ |z 0| / |1 - β * a * ρ| := by
      rw [abs_div]
      exact div_le_div_of_nonneg_right (hzb t) (abs_nonneg _)
    calc |μ (t + 1) - (a * μ t - a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)))|
        ≤ |μ (t + 1)| + |a * μ t| + |a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ))| :=
          by
            have := abs_sub (μ (t + 1)) (a * μ t - a / β * (κ * xs / (1 - β * a) +
              z t / (1 - β * a * ρ)))
            have := abs_sub (a * μ t) (a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)))
            linarith
      _ ≤ M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ|) := by
          rw [abs_mul, abs_mul]
          have := abs_add_le (κ * xs / (1 - β * a)) (z t / (1 - β * a * ρ))
          have h4 : |κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)| ≤
              |κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ| := by linarith
          have h5 := mul_le_mul_of_nonneg_left h4 (abs_nonneg (a / β))
          have h6 := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
          linarith
  have he0 : e 0 = 0 := by
    by_contra hne
    have hgt : 1 < 1 / (β * a) := by rw [lt_div_iff₀ ha0]; linarith
    have ht := tendsto_pow_atTop_atTop_of_one_lt hgt
    have ht2 := (ht.atTop_mul_const (abs_pos.2 hne)).eventually_gt_atTop
      (M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ|))
    obtain ⟨t, ht3⟩ := ht2.exists
    have := heb t
    rw [hpow t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    linarith
  intro t
  have := hpow t
  rw [he0, mul_zero] at this
  simp only [he] at this
  linarith

/-- **The commitment solution of Example 9.4.2** (Miao, p. 311). Let `a` be a root of (9.29),
`μ_{x0} = 0`, `μ_{x,t+1} = rule(μ_{xt}, z_t)`, `π_t = β(μ_{xt} − μ_{x,t+1})` and
`x_t = x* + (βκ/λ)μ_{x,t+1}`. Along `z_{t+1} = ρz_t`, (9.25), (9.26) and (9.23) hold at every
date. -/
theorem ex942_solution {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (hlam : lam ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hd2 : 1 - β * a * ρ ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (z μ : ℕ → ℝ)
    (hz : ∀ t, z (t + 1) = ρ * z t) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (z t)) :
    let pin : ℕ → ℝ := fun t => β * (μ t - μ (t + 1))
    let x : ℕ → ℝ := fun t => xs + β * κ / lam * μ (t + 1)
    ∀ t, pin t + β * μ (t + 1) - β * μ t = 0 ∧ lam * (x t - xs) - β * κ * μ (t + 1) = 0 ∧
      pin t = κ * x t + β * pin (t + 1) + z t := by
  intro pin x t
  refine ⟨by simp only [pin]; ring, by simp only [x]; field_simp; ring, ?_⟩
  have h := ex942_rule_solves (κ := κ) (lam := lam) (xs := xs) ha hd1 hd2 hroot (μ t) (z t)
  have hib : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  simp only [pin, x]
  rw [hμ (t + 1), hz t, hμ t]
  simp only [ex942b] at h
  linear_combination β * h + (κ * xs + z t) * hib

/-- Miao, p. 311 ("(9.25)–(9.27) then determine … `μ_{zt}`"): for bounded `μ_x` and
`|βρ| < 1`, the forward sum `μ_{zt} = −β∑ⱼ(βρ)ʲμ_{x,t+1+j}` solves (9.27). -/
theorem ex942_muz {β ρ : ℝ} (hβρ : |β * ρ| < 1) (μx : ℕ → ℝ) (hμ : ∃ M, ∀ t, |μx t| ≤ M)
    (t : ℕ) :
    let μz : ℕ → ℝ := fun t => -β * ∑' j : ℕ, (β * ρ) ^ j * μx (t + 1 + j)
    (-(β * μx (t + 1)) + β * ρ * μz (t + 1) - μz t) = 0 := by
  intro μz
  obtain ⟨M, hM⟩ := hμ
  have hsum : ∀ s, Summable fun j : ℕ => (β * ρ) ^ j * μx (s + 1 + j) := fun s => by
    refine Summable.of_norm_bounded (g := fun j => M * |β * ρ| ^ j)
      ((summable_geometric_of_lt_one (abs_nonneg _) hβρ).mul_left M) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (abs_nonneg _) _)
  have h := (hsum t).tsum_eq_zero_add
  simp only [μz]
  rw [h]
  have hs : ∀ j : ℕ, (β * ρ) ^ (j + 1) * μx (t + 1 + (j + 1)) =
      β * ρ * ((β * ρ) ^ j * μx (t + 1 + 1 + j)) := fun j => by
    rw [pow_succ, show t + 1 + (j + 1) = t + 1 + 1 + j by ring]
    ring
  rw [tsum_congr hs, tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  ring

/-- **Time inconsistency in Example 9.4.2** (Miao, p. 308 and p. 311). Commitment from date `0`
gives `μ_{x1} = rule(0, z₀)`, `μ_{x2} = rule(μ_{x1}, z₁)`, `π₁ = β(μ_{x1} − μ_{x2})`.
Reoptimising at date `1` restarts the rule from `μ_{x1} = 0`: `π̂₁ = β(0 − rule(0, z₁))`. Then
`π₁ − π̂₁ = β(1 − a)μ_{x1}`, which is nonzero when `a ≠ 1`, `β ≠ 0` and
`κx*/(1 − βa) + z₀/(1 − βaρ) ≠ 0`. -/
theorem ex942_time_inconsistent {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (z0 z1 : ℝ) (hK : κ * xs / (1 - β * a) + z0 / (1 - β * a * ρ) ≠ 0) :
    let μ1 := ex942Rule β κ ρ xs a 0 z0
    let pin1 := β * (μ1 - ex942Rule β κ ρ xs a μ1 z1)
    let pinhat1 := β * (0 - ex942Rule β κ ρ xs a 0 z1)
    pin1 - pinhat1 = β * (1 - a) * μ1 ∧ pin1 ≠ pinhat1 := by
  intro μ1 pin1 pinhat1
  have h1 : pin1 - pinhat1 = β * (1 - a) * μ1 := by
    simp only [pin1, pinhat1, ex942Rule]
    ring
  refine ⟨h1, fun h => ?_⟩
  rw [sub_eq_zero.2 h] at h1
  have hμ1 : μ1 ≠ 0 := by
    simp only [μ1, ex942Rule, mul_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero (div_ne_zero ha hβ) hK
  have : β * (1 - a) * μ1 ≠ 0 := mul_ne_zero (mul_ne_zero hβ (sub_ne_zero.2 (Ne.symm ha1))) hμ1
  exact this h1.symm

end Miao.LinearQuadratic
