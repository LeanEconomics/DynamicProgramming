/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Perturbation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The perturbation method: the systems of equations and the summary claim

Miao, §2.4, pp. 64–69, continued: the scalar model with two equations `f = (f₀, f₁)`
(`n = n_x + n_y = 2`), so each step of the perturbation method is a `2 × 2` linear system.

* `IsPertSolution`: `f`, `g`, `h` are `C²`, the shock is finite with mean zero and `F ≡ 0`
  ((2.27), (2.29), (2.30)). `pert_partials_vanish`, `pert_F_partials_zero` (p. 67).
* `eq_steady_state` (p. 67, "`ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`", correct direction) and
  `steady_state_printed_false`.
* First order: `g_sigma_system`, `pert_hom2_unique`, `theorem_g_sigma_zero` (certainty
  equivalence, p. 67); `eq_F_x_zero`, `eq_2_31`, `eq_2_32`, `eq_2_33`, `eq_2_31_of_2_33` (p. 68).
* (2.28): `eq_2_28_differential` (the total differential) and `eq_2_28` (the linearised system
  is `A E_t dX_{t+1} = B dX_t` of the form (2.11), with `A = [f_{x'} f_{y'}]`, `B = −[f_x f_y]`).
* Second order (p. 69): `g_sigma_x_system`, `theorem_g_sigma_x_zero`; `eq_F_sigma_sigma_linear`,
  `g_sigma_sigma_unique`; `eq_F_xx_linear`, `g_xx_unique`; `pertTaylor2`, `pertTaylor2_sigma`,
  `summary_uncertainty` (uncertainty enters the second-order solution only through
  `½g_σσσ²`, `½h_σσσ²`).

**Corrections.**
* "For a unique solution to exist, we must have `g_σ = h_σ = 0`" (p. 67): the homogeneous system
  always has the zero solution; it is the only one iff the determinant `A₀B₁ − B₀A₁ ≠ 0`
  (`pert_hom2_unique`), and then `g_σ = h_σ = 0` (`theorem_g_sigma_zero`). With determinant
  zero, `g_σ ≠ 0` is possible in a genuine solution (`g_sigma_not_forced`); likewise for
  `g_σx` (`g_sigma_x_not_forced`).
* The `F_σx` system is homogeneous only given `g_σ = h_σ = 0` (hypothesis of
  `g_sigma_x_system`); the summary claim needs both determinants nonzero.
* "(2.33) is equivalent to (2.28)/(2.31)": (2.31) implies (2.33) along the linearised path
  (`eq_2_33`); the converse needs `x̂₀ ≠ 0` (`eq_2_31_of_2_33`).
* "We first note `ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`" is an assumption (a choice of steady state on
  the policy), not a consequence (`steady_state_printed_false`).
-/

namespace Miao.RationalExpectations

open scoped Matrix

/-! ### The model -/

variable (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (η : ℝ) {N : ℕ}
  (p ε : Fin N → ℝ) in
/-- The scalar nonlinear model (2.27) `E_t f(y_{t+1}, y_t, x_{t+1}, x_t) = 0` with one
predetermined variable `x` and one non-predetermined `y` (so `f = (f₀, f₁) : ℝ⁴ → ℝ²`), solved by
the policy (2.29) `y = g(x, σ)`, `x' = h(x, σ) + ησε'` (Miao, pp. 66–67): `f`, `g`, `h` are `C²`,
the shock is finite with mean zero, and `F(x, σ) = 0` for all `(x, σ)` ((2.30)). The existence
and smoothness of `g` and `h` is an assumption of the method, not proved by the book. -/
structure IsPertSolution : Prop where
  f_smooth : ∀ k, ContDiff ℝ 2 (f k)
  g_smooth : ContDiff ℝ 2 g
  h_smooth : ContDiff ℝ 2 h
  shock : IsFiniteShock p ε
  solves : ∀ k q, pertF (f k) g h η p ε q = 0

/-- Miao, p. 67: "Since `F(x, σ)` is equal to zero for any values of `(x, σ)`, we must have
`F_{xⁱσʲ}(x, σ) = 0`": the partial derivatives of a function that vanishes identically
vanish identically (so all iterated ones do too). -/
theorem pert_partials_vanish {G : ℝ × ℝ → ℝ} (hG : ∀ q, G q = 0) :
    (∀ q, pertDx G q = 0) ∧ ∀ q, pertDs G q = 0 := by
  have e : G = fun _ => 0 := funext hG
  subst e
  simp [pertDx, pertDs]

/-- Miao, p. 67, `F_{xⁱσʲ}(x, σ) = 0` for `i + j ≤ 2`, for each equation of a solution. -/
theorem pert_F_partials_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) (k : Fin 2) (q : ℝ × ℝ) :
    pertDx (pertF (f k) g h η p ε) q = 0 ∧ pertDs (pertF (f k) g h η p ε) q = 0 ∧
      pertDx (pertDx (pertF (f k) g h η p ε)) q = 0 ∧
      pertDs (pertDx (pertF (f k) g h η p ε)) q = 0 ∧
      pertDs (pertDs (pertF (f k) g h η p ε)) q = 0 := by
  obtain ⟨h1, h2⟩ := pert_partials_vanish (hs.solves k)
  exact ⟨h1 q, h2 q, (pert_partials_vanish h1).1 q, (pert_partials_vanish h1).2 q,
    (pert_partials_vanish h2).2 q⟩

/-- Miao, p. 67, "`ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`", the correct direction: if `x̄` is a fixed
point of the deterministic policy `h(·, 0)` and `ȳ = g(x̄, 0)`, then `(x̄, ȳ)` is a
deterministic steady state, `f(ȳ, ȳ, x̄, x̄) = 0`. The converse is not automatic
(`steady_state_printed_false`): that the policy passes through the chosen steady state is part of
the method's assumptions. -/
theorem eq_steady_state {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb : ℝ} (hx : h (xb, 0) = xb)
    (k : Fin 2) : f k (g (xb, 0), g (xb, 0), xb, xb) = 0 := by
  have := hs.solves k (xb, 0)
  simp only [pertF, pertPhi_ss hx rfl] at this
  rwa [← Finset.sum_mul, hs.shock.sum_one, one_mul] at this

/-- **The steady state need not lie on the policy** (Miao, p. 67). With `f₀ = y − y'`,
`f₁ = (x' − x)(x' − 2x)`, `η = 0`, the policy `g = 0`, `h(x, σ) = 2x` solves (2.30), and
`(x̄, ȳ) = (1, 0)` is a deterministic steady state, yet `h(x̄, 0) = 2 ≠ x̄`. -/
theorem steady_state_printed_false :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 1 → ℝ),
      IsPertSolution f g h 0 p ε ∧ (∀ k, f k (0, 0, 1, 1) = 0) ∧ h (1, 0) ≠ 1 := by
  refine ⟨![fun v => v.2.1 - v.1, fun v => (v.2.2.1 - v.2.2.2) * (v.2.2.1 - 2 * v.2.2.2)],
    fun _ => 0, fun q => 2 * q.1, ![1], ![0], ⟨fun k => ?_, contDiff_const, by fun_prop,
      ⟨fun i => by simp, by simp, by simp⟩, fun k q => ?_⟩, fun k => ?_, by norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;> fun_prop
  · fin_cases k <;> simp [pertF, pertPhi]
  · fin_cases k <;> simp

/-! ### `g_σ` and `h_σ` -/

/-- The coefficient of `g_σ` (and of `g_σσ`) in equation `k`: `f_{y'} + f_y` at `v`. -/
noncomputable def pertCoefA (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  pertP fk 0 v + pertP fk 1 v

/-- The coefficient of `h_σ` (and of `h_σσ`, `h_σx`) in equation `k`: `f_{y'}g_x + f_{x'}`. -/
noncomputable def pertCoefB (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx : ℝ) : ℝ :=
  pertP fk 0 v * gx + pertP fk 2 v

/-- The coefficient of `g_σx` in equation `k`: `f_{y'}h_x + f_y`. -/
noncomputable def pertCoefAx (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (hx : ℝ) : ℝ :=
  pertP fk 0 v * hx + pertP fk 1 v

/-- A homogeneous `2 × 2` system `au + bv = 0`, `cu + dv = 0` has only the zero solution iff
`ad − bc ≠ 0`. -/
theorem pert_hom2_unique (a b c d : ℝ) :
    (∀ u v, a * u + b * v = 0 → c * u + d * v = 0 → u = 0 ∧ v = 0) ↔ a * d - b * c ≠ 0 := by
  constructor
  · intro H hdet
    by_cases hab : a = 0 ∧ b = 0
    · by_cases hcd : c = 0 ∧ d = 0
      · have := H 1 0 (by rw [hab.1, hab.2]; ring) (by rw [hcd.1, hcd.2]; ring)
        exact one_ne_zero this.1
      · have := H d (-c) (by linear_combination hdet) (by ring)
        exact hcd ⟨by linarith [this.2], this.1⟩
    · have := H b (-a) (by ring) (by linear_combination -hdet)
      exact hab ⟨by linarith [this.2], this.1⟩
  · intro hdet u v h1 h2
    have hu : (a * d - b * c) * u = 0 := by linear_combination d * h1 - b * h2
    have hv : (a * d - b * c) * v = 0 := by linear_combination a * h2 - c * h1
    exact ⟨(mul_eq_zero.1 hu).resolve_left hdet, (mul_eq_zero.1 hv).resolve_left hdet⟩

/-- Miao, p. 67: `F_σ(x̄, 0) = 0` is the homogeneous linear system
`(f_{y'} + f_y)g_σ + (f_{y'}g_x + f_{x'})h_σ = 0` (one equation per component of `f`), which
always has the solution `g_σ = h_σ = 0`. -/
theorem g_sigma_system {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (k : Fin 2) :
    pertCoefA (f k) (yb, yb, xb, xb) * pertDs g (xb, 0) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs h (xb, 0) = 0 := by
  have := (pert_F_partials_zero hs k (xb, 0)).2.1
  rw [eq_F_sigma (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy] at this
  rw [pertCoefA, pertCoefB]
  linear_combination this

/-- Miao, p. 67, "For a unique solution to exist, we must have `g_σ = h_σ = 0`", made precise:
the homogeneous system of `g_sigma_system` has the zero solution, and it is its unique solution
iff the determinant `A₀B₁ − B₀A₁` is nonzero (`pert_hom2_unique`); in that case
`g_σ = h_σ = 0` (certainty equivalence). -/
theorem theorem_g_sigma_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0) :
    pertDs g (xb, 0) = 0 ∧ pertDs h (xb, 0) = 0 :=
  (pert_hom2_unique _ _ _ _).2 hdet _ _ (g_sigma_system hs hx hy 0) (g_sigma_system hs hx hy 1)

/-! ### `F_x` and (2.31)–(2.33) -/

/-- Miao, p. 68: `F_x(x̄, 0) = f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x = 0` for each equation. -/
theorem eq_F_x_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (k : Fin 2) :
    pertP (f k) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx h (xb, 0) +
      pertP (f k) 1 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (f k) 2 (yb, yb, xb, xb) * pertDx h (xb, 0) + pertP (f k) 3 (yb, yb, xb, xb) = 0 := by
  rw [← eq_F_x (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy]
  exact (pert_F_partials_zero hs k (xb, 0)).1

/-- Miao, (2.31), p. 68: the two equations `f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x = 0` are
`[f_{x'} f_{y'}][1; g_x]h_x = −[f_x f_y][1; g_x]`, with `A = [f_{x'} f_{y'}]`,
`B = −[f_x f_y]` (rows = equations). -/
theorem eq_2_31 (fyp fy fxp fx : Fin 2 → ℝ) (gx hx : ℝ) :
    (∀ k, fyp k * gx * hx + fy k * gx + fxp k * hx + fx k = 0) ↔
      hx • (!![fxp 0, fyp 0; fxp 1, fyp 1] *ᵥ ![1, gx]) =
        -!![fx 0, fy 0; fx 1, fy 1] *ᵥ ![1, gx] := by
  simp only [funext_iff, Fin.forall_fin_two]
  simp only [Fin.isValue, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul,
    Matrix.mulVec_empty, add_zero, Pi.smul_apply, Pi.add_apply, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    neg_mul, Finset.sum_neg_distrib, Fin.sum_univ_two, mul_one, Matrix.cons_val_one, neg_add_rev]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by linear_combination h0, by linear_combination h1⟩

/-- Miao, (2.32), p. 68: postmultiplying (2.31) by `x̂ = x − x̄`; (2.32) for all `x̂` is
equivalent to (2.31). -/
theorem eq_2_32 (A B : Matrix (Fin 2) (Fin 2) ℝ) (gx hx : ℝ) :
    hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx] ↔
      ∀ xh : ℝ, A *ᵥ ((hx * xh) • ![1, gx]) = B *ᵥ (xh • ![1, gx]) := by
  constructor
  · intro H xh
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← H, smul_smul, mul_comm]
  · intro H
    have := H 1
    rwa [mul_one, one_smul, Matrix.mulVec_smul] at this

/-- Miao, (2.33), p. 68: if (2.31) holds, the linearised non-stochastic solution
`x̂_{t+1} = h_xx̂_t`, `ŷ_t = g_xx̂_t` satisfies `A[x̂_{t+1}; ŷ_{t+1}] = B[x̂_t; ŷ_t]`, which is
(2.28) without shocks. -/
theorem eq_2_33 (A B : Matrix (Fin 2) (Fin 2) ℝ) {gx hx : ℝ}
    (H : hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx]) {xh yh : ℕ → ℝ}
    (hxh : ∀ t, xh (t + 1) = hx * xh t) (hyh : ∀ t, yh t = gx * xh t) (t : ℕ) :
    A *ᵥ ![xh (t + 1), yh (t + 1)] = B *ᵥ ![xh t, yh t] := by
  have e1 : ![xh (t + 1), yh (t + 1)] = (hx * xh t) • ![1, gx] := by
    rw [hyh, hxh]
    ext i
    fin_cases i <;> simp [mul_comm]
  have e2 : ![xh t, yh t] = xh t • ![1, gx] := by
    rw [hyh]
    ext i
    fin_cases i <;> simp [mul_comm]
  rw [e1, e2]
  exact (eq_2_32 A B gx hx).1 H (xh t)

/-- Miao, p. 68, "this equation is equivalent to (2.31)", made precise: conversely, if the
linearised non-stochastic solution satisfies (2.33) at `t = 0` with `x̂₀ ≠ 0`, then (2.31)
holds. (With `x̂₀ = 0` (2.33) is vacuous.) -/
theorem eq_2_31_of_2_33 (A B : Matrix (Fin 2) (Fin 2) ℝ) {gx hx : ℝ} {xh yh : ℕ → ℝ}
    (hxh : ∀ t, xh (t + 1) = hx * xh t) (hyh : ∀ t, yh t = gx * xh t) (h0 : xh 0 ≠ 0)
    (H : A *ᵥ ![xh 1, yh 1] = B *ᵥ ![xh 0, yh 0]) :
    hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx] := by
  have e1 : ![xh 1, yh 1] = xh 0 • (hx • ![1, gx]) := by
    rw [hyh, hxh]
    ext i
    fin_cases i <;> simp [mul_comm, mul_assoc]
  have e2 : ![xh 0, yh 0] = xh 0 • ![1, gx] := by
    rw [hyh]
    ext i
    fin_cases i <;> simp [mul_comm]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul] at H
  exact smul_right_injective _ h0 H

/-! ### The linearised system (2.28) -/

/-- Miao, p. 65, "We totally differentiate (2.27)": for `f` differentiable at the steady state
`S`, `f(S + dv) = f(S) + f_{y'}dy' + f_ydy + f_{x'}dx' + f_xdx + o(‖dv‖)`. -/
theorem eq_2_28_differential {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {S : ℝ × ℝ × ℝ × ℝ}
    (hf : DifferentiableAt ℝ fk S) :
    HasFDerivAt fk (fderiv ℝ fk S) S ∧ ∀ dv : ℝ × ℝ × ℝ × ℝ,
      fderiv ℝ fk S dv = pertP fk 0 S * dv.1 + pertP fk 1 S * dv.2.1 +
        pertP fk 2 S * dv.2.2.1 + pertP fk 3 S * dv.2.2.2 := by
  refine ⟨hf.hasFDerivAt, fun dv => ?_⟩
  have e : dv = dv.1 • pertE4 0 + dv.2.1 • pertE4 1 + dv.2.2.1 • pertE4 2 +
      dv.2.2.2 • pertE4 3 := by
    ext <;> simp [pertE4]
  conv_lhs => rw [e]
  simp only [map_add, map_smul, smul_eq_mul, pertP]
  ring

/-- Miao, (2.28), p. 65: the linearised system
`E_t[f_{y'}dy_{t+1} + f_ydy_t + f_{x'}dx_{t+1} + f_xdx_t] = 0` (one equation per component of
`f`), for adapted `dx`, `dy`, is the system `A E_t dX_{t+1} = B dX_t` of the form (2.11) with
`dX = (dx, dy)`, `A = [f_{x'} f_{y'}]`, `B = −[f_x f_y]` (and no exogenous term). -/
theorem eq_2_28 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (E : CondExpSystem ℝ V)
    (fyp fy fxp fx : Fin 2 → ℝ) {dx dy : ℕ → V} (hdx : ∀ t, E.E t (dx t) = dx t)
    (hdy : ∀ t, E.E t (dy t) = dy t) :
    (∀ t k, E.E t (fyp k • dy (t + 1) + fy k • dy t + fxp k • dx (t + 1) + fx k • dx t) = 0) ↔
      ∀ t, matAct !![fxp 0, fyp 0; fxp 1, fyp 1] (Evec E t ![dx (t + 1), dy (t + 1)]) =
        matAct !![-fx 0, -fy 0; -fx 1, -fy 1] ![dx t, dy t] := by
  have e : ∀ t k, E.E t (fyp k • dy (t + 1) + fy k • dy t + fxp k • dx (t + 1) + fx k • dx t) =
      fyp k • E.E t (dy (t + 1)) + fy k • dy t + fxp k • E.E t (dx (t + 1)) + fx k • dx t :=
    fun t k => by simp only [map_add, map_smul, hdx, hdy]
  simp only [e, funext_iff, Fin.forall_fin_two]
  simp only [matAct, Evec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · intro H t
    exact ⟨by linear_combination (norm := module) (H t).1, by
      linear_combination (norm := module) (H t).2⟩
  · intro H t
    exact ⟨by linear_combination (norm := module) (H t).1, by
      linear_combination (norm := module) (H t).2⟩

/-! ### `g_σx`, `h_σx` -/

/-- Miao, p. 69: given `g_σ = h_σ = 0`, `F_σx(x̄, 0) = 0` is the homogeneous linear system
`(f_{y'}h_x + f_y)g_σx + (f_{y'}g_x + f_{x'})h_σx = 0` (one equation per component of `f`). -/
theorem g_sigma_x_system {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0)
    (k : Fin 2) :
    pertCoefAx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) * pertDs (pertDx g) (xb, 0) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs (pertDx h) (xb, 0) = 0 := by
  have := (pert_F_partials_zero hs k (xb, 0)).2.2.2.1
  rw [eq_F_sigma_x (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy hgs hhs] at this
  rw [pertCoefAx, pertCoefB]
  linear_combination this

/-- Miao, p. 69, "If a unique solution exists, then the solution must be equal to zero": if the
determinant of the `F_σ` system and that of the `F_σx` system are nonzero, then
`g_σ = h_σ = 0` and `g_σx = h_σx = 0`. -/
theorem theorem_g_sigma_x_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0)
    (hdetx : pertCoefAx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) :
    pertDs (pertDx g) (xb, 0) = 0 ∧ pertDs (pertDx h) (xb, 0) = 0 := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  exact (pert_hom2_unique _ _ _ _).2 hdetx _ _ (g_sigma_x_system hs hx hy hgs hhs 0)
    (g_sigma_x_system hs hx hy hgs hhs 1)

/-! ### `g_σσ`, `h_σσ` and `g_xx`, `h_xx` -/

/-- The inhomogeneous coefficient of the `F_σσ` equation (to be multiplied by `η²E[ε'²]`):
`f_{y'y'}g_x² + f_{y'x'}g_x + f_{y'}g_xx + f_{x'y'}g_x + f_{x'x'}`. -/
noncomputable def pertCoefSS (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx gxx : ℝ) : ℝ :=
  (pertP (pertP fk 0) 0 v * gx + pertP (pertP fk 0) 2 v) * gx + pertP fk 0 v * gxx +
    pertP (pertP fk 2) 0 v * gx + pertP (pertP fk 2) 2 v

/-- Miao, p. 69, "This is a system of `n` linear equations for `n` unknowns `g_σσ` and `h_σσ`",
precisely: `F_σσ(x̄, 0) = (f_{y'} + f_y)g_σσ + (f_{y'}g_x + f_{x'})h_σσ + η²E[ε'²]c` (given
`g_σ = h_σ = 0`), with the same coefficients as the `F_σ` system and `c = pertCoefSS`, which
does not involve `g_σσ`, `h_σσ`. -/
theorem eq_F_sigma_sigma_linear {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 fk) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ}
    {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF fk g h η p ε)) (xb, 0) =
      pertCoefA fk (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertCoefB fk (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs (pertDs h) (xb, 0) +
        η * η * (∑ i, p i * ε i ^ 2) *
          pertCoefSS fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) := by
  rw [eq_F_sigma_sigma hf hg hh η hp hx hy hgs hhs, pertCoefA, pertCoefB, pertCoefSS]
  ring

/-- Miao, p. 69, solving `F_σσ(x̄, 0) = 0`: if the determinant of the `F_σ` system is nonzero,
`(g_σσ, h_σσ)` is the unique solution of the linear system of `eq_F_sigma_sigma_linear`. -/
theorem g_sigma_sigma_unique {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0) (u v : ℝ)
    (huv : ∀ k, pertCoefA (f k) (yb, yb, xb, xb) * u +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * v + η * η * (∑ i, p i * ε i ^ 2) *
        pertCoefSS (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) = 0) :
    u = pertDs (pertDs g) (xb, 0) ∧ v = pertDs (pertDs h) (xb, 0) := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  have e : ∀ k, pertCoefA (f k) (yb, yb, xb, xb) * (u - pertDs (pertDs g) (xb, 0)) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * (v - pertDs (pertDs h) (xb, 0)) =
        0 := fun k => by
    have h0 := (pert_F_partials_zero hs k (xb, 0)).2.2.2.2
    rw [eq_F_sigma_sigma_linear (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy hgs
      hhs] at h0
    linear_combination huv k - h0
  obtain ⟨h1, h2⟩ := (pert_hom2_unique _ _ _ _).2 hdet _ _ (e 0) (e 1)
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- The coefficient of `g_xx` in `F_xx`: `f_{y'}h_x² + f_y`. -/
noncomputable def pertCoefAxx (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (hx : ℝ) : ℝ :=
  pertP fk 0 v * hx * hx + pertP fk 1 v

/-- The part of `F_xx` free of `g_xx`, `h_xx`. -/
noncomputable def pertCoefXX (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx hx : ℝ) : ℝ :=
  pertRow fk v 0 (gx * hx) gx hx 1 * (gx * hx) + pertRow fk v 1 (gx * hx) gx hx 1 * gx +
    pertRow fk v 2 (gx * hx) gx hx 1 * hx + pertRow fk v 3 (gx * hx) gx hx 1

/-- Miao, p. 69, "the above equation represents a system of `n × n_x × n_x` linear equations
for the same number of unknowns given by the elements of `g_xx` and `h_xx`", precisely (scalar
case, two equations): `F_xx(x̄, 0) = (f_{y'}h_x² + f_y)g_xx + (f_{y'}g_x + f_{x'})h_xx + c` with
`c` free of `g_xx`, `h_xx`. -/
theorem eq_F_xx_linear {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 fk)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF fk g h η p ε)) (xb, 0) =
      pertCoefAxx fk (yb, yb, xb, xb) (pertDx h (xb, 0)) * pertDx (pertDx g) (xb, 0) +
        pertCoefB fk (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDx (pertDx h) (xb, 0) +
        pertCoefXX fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0)) := by
  rw [eq_F_xx hf hg hh η hp hx hy, pertCoefAxx, pertCoefB, pertCoefXX]
  ring

/-- Miao, p. 69, solving `F_xx(x̄, 0) = 0`: if its determinant is nonzero, `(g_xx, h_xx)` is
the unique solution of the linear system of `eq_F_xx_linear`. -/
theorem g_xx_unique {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefAxx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAxx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) (u v : ℝ)
    (huv : ∀ k, pertCoefAxx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) * u +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * v +
        pertCoefXX (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0)) = 0) :
    u = pertDx (pertDx g) (xb, 0) ∧ v = pertDx (pertDx h) (xb, 0) := by
  have e : ∀ k, pertCoefAxx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
      (u - pertDx (pertDx g) (xb, 0)) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * (v - pertDx (pertDx h) (xb, 0)) =
        0 := fun k => by
    have h0 := (pert_F_partials_zero hs k (xb, 0)).2.2.1
    rw [eq_F_xx_linear (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy] at h0
    linear_combination huv k - h0
  obtain ⟨h1, h2⟩ := (pert_hom2_unique _ _ _ _).2 hdet _ _ (e 0) (e 1)
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-! ### The summary claim -/

/-- The second-order Taylor polynomial of `G` at `(x̄, 0)` as printed (Miao, p. 66):
`G + G_x(x − x̄) + G_σσ + ½G_xx(x − x̄)² + G_xσ(x − x̄)σ + ½G_σσσ²`, with `G_xσ` taken as the
`σ`-derivative of `G_x`. -/
noncomputable def pertTaylor2 (G : ℝ × ℝ → ℝ) (xb x σ : ℝ) : ℝ :=
  G (xb, 0) + pertDx G (xb, 0) * (x - xb) + pertDs G (xb, 0) * σ +
    1 / 2 * pertDx (pertDx G) (xb, 0) * (x - xb) ^ 2 + pertDs (pertDx G) (xb, 0) * (x - xb) * σ +
    1 / 2 * pertDs (pertDs G) (xb, 0) * σ ^ 2

/-- If `G_σ = G_σx = 0` at `(x̄, 0)`, the second-order Taylor polynomial depends on `σ` only
through `½G_σσσ²`. -/
theorem pertTaylor2_sigma {G : ℝ × ℝ → ℝ} {xb : ℝ} (hs : pertDs G (xb, 0) = 0)
    (hsx : pertDs (pertDx G) (xb, 0) = 0) (x σ : ℝ) :
    pertTaylor2 G xb x σ = pertTaylor2 G xb x 0 + 1 / 2 * pertDs (pertDs G) (xb, 0) * σ ^ 2 := by
  simp only [pertTaylor2, hs, hsx]
  ring

/-- Miao, p. 69, "uncertainty matters in the second-order approximated solution only through the
terms `½g_σσ(x̄, 0)σ²` and `½h_σσ(x̄, 0)σ²`": if the determinants of the `F_σ` and `F_σx` systems
are nonzero, the second-order Taylor polynomials of `g` and `h` at `(x̄, 0)` equal their
certainty (`σ = 0`) parts plus `½g_σσσ²`, resp. `½h_σσσ²`. -/
theorem summary_uncertainty {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0)
    (hdetx : pertCoefAx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) (x σ : ℝ) :
    pertTaylor2 g xb x σ = pertTaylor2 g xb x 0 + 1 / 2 * pertDs (pertDs g) (xb, 0) * σ ^ 2 ∧
      pertTaylor2 h xb x σ = pertTaylor2 h xb x 0 + 1 / 2 * pertDs (pertDs h) (xb, 0) * σ ^ 2 := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  obtain ⟨hgsx, hhsx⟩ := theorem_g_sigma_x_zero hs hx hy hdet hdetx
  exact ⟨pertTaylor2_sigma hgs hgsx x σ, pertTaylor2_sigma hhs hhsx x σ⟩

end Miao.RationalExpectations
