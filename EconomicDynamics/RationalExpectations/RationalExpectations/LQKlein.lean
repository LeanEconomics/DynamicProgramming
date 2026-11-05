/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.KleinMartingales
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The linear-quadratic example of the Klein method

Miao, §2.3.2, pp. 57–58: maximise `−½E∑ βᵗ[x_t', u_t'][[Q, S], [S', R]][x_t; u_t]` subject to
`x_{t+1} = Ax_t + Bu_t + Cξ_{t+1}` (2.18), with multiplier `β^{t+1}λ_{t+1}`.

* `lq_predError` (p. 57): with `x`, `u` adapted, the prediction error of `x` is
  `x_{t+1} − E_t x_{t+1} = C(ξ_{t+1} − E_tξ_{t+1})`.
* `lq_predetermined` (p. 57, "`{x_t}` is predetermined with the prediction error `{ξ_t}`"): if
  `ξ` is a martingale difference, `x` is predetermined in the sense of Definition 2.3.4 with
  prediction error `Cξ`, and `E_t x_{t+1} = Ax_t + Bu_t`.
* `lq_variation_u`, `lq_variation_x`: the first-order conditions. With the multiplier term
  written as `+β^{t+1}λ_{t+1}'(x_{t+1} − Ax_t − Bu_t − Cξ_{t+1})`, the date-`t` terms of the
  Lagrangian (divided by `βᵗ`) are `ℓ = −½q(x_t, u_t) − βλ_{t+1}'(Ax_t + Bu_t) + λ_t'x_t`. For
  symmetric `Q`, `R`, the first variations are exactly
  `ℓ(x, u + h) − ℓ(x, u) = −(S'x + Ru + βB'λ_{t+1})·h − ½h'Rh` and
  `ℓ(x + h, u) − ℓ(x, u) = −(Qx + Su − λ_t + βA'λ_{t+1})·h − ½h'Qh`, so, after conditioning on
  `F_t` (`λ_{t+1}` enters linearly), the first-order conditions are
  `S'x_t + Ru_t + βB'E_tλ_{t+1} = 0` and `Qx_t + Su_t − λ_t + βA'E_tλ_{t+1} = 0`.
* `lq_system_iff` (p. 58): these first-order conditions together with `E_t x_{t+1} = Ax_t + Bu_t`
  are equivalent to the printed system `lqLeft · E_t(x, u, λ)_{t+1} = lqRight · (x, u, λ)_t`,
  i.e. (2.11) with no forcing. Entry by entry the printed matrices are correct for this sign
  convention of the multiplier (with the opposite convention `−β^{t+1}λ_{t+1}'(…)` the signs of
  the `λ` columns flip); no misprint.

**Departures and items not formalised.**
* The book takes `{ξ_t}` to be a white noise. A white noise need not be a martingale difference
  (`E_tξ_{t+1} ≠ 0` is possible for uncorrelated `ξ`), and then the prediction error of `x` is
  `C(ξ_{t+1} − E_tξ_{t+1})`, not `Cξ_{t+1}` (`lq_predError`); the claim needs `ξ` to be a
  martingale difference (e.g. (2.2)), which `lq_predetermined` assumes.
* The conditioning step (passing from the pointwise first variation to `E_tλ_{t+1}`) needs
  products of random variables, which the abstract setting does not have; it is not formalised.
* "First-order conditions together with the transversality condition are necessary and
  sufficient for optimality" (p. 58) is not formalised: it is the linear-quadratic control
  theory of Chapter 9.
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The state is predetermined -/

/-- Miao, p. 57: with `x_{t+1} = Ax_t + Bu_t + Cξ_{t+1}` and `x`, `u` adapted, the prediction
error of `x` is `x_{t+1} − E_t x_{t+1} = C(ξ_{t+1} − E_tξ_{t+1})`. -/
theorem lq_predError {nx nu nξ : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (C : Matrix (Fin nx) (Fin nξ) 𝕜) {x : ℕ → Fin nx → V}
    {u : ℕ → Fin nu → V} {ξ : ℕ → Fin nξ → V} (hxa : IsAdaptedV E x) (hua : IsAdaptedV E u)
    (h : ∀ t, x (t + 1) = matAct A (x t) + matAct B (u t) + matAct C (ξ (t + 1))) (t : ℕ)
    (i : Fin nx) :
    x (t + 1) i - E.E t (x (t + 1) i) =
      matAct C (fun j => ξ (t + 1) j - E.E t (ξ (t + 1) j)) i := by
  rw [h t]
  simp only [matAct, Pi.add_apply, map_add, map_sum, map_smul, hxa t, hua t, smul_sub,
    Finset.sum_sub_distrib]
  abel

/-- Miao, p. 57: if `ξ` is a martingale difference (as under (2.2)), `x` and `u` are adapted and
`x₀` is `F₀`-measurable, then `x` is predetermined (Definition 2.3.4) with prediction error
`Cξ`, and `E_t x_{t+1} = Ax_t + Bu_t` (the first block row of the system on p. 58). -/
theorem lq_predetermined {nx nu nξ : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (C : Matrix (Fin nx) (Fin nξ) 𝕜) {x : ℕ → Fin nx → V}
    {u : ℕ → Fin nu → V} {ξ : ℕ → Fin nξ → V} (hxa : IsAdaptedV E x) (hua : IsAdaptedV E u)
    (hξ : IsMartingaleDiffProc E ξ)
    (h : ∀ t, x (t + 1) = matAct A (x t) + matAct B (u t) + matAct C (ξ (t + 1))) :
    IsPredeterminedKlein E (fun t => matAct C (ξ t)) x ∧
      ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) := by
  have hE : ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) := fun t => by
    funext i
    rw [h t]
    simp only [Evec, matAct, Pi.add_apply, map_add, map_sum, map_smul, hxa t, hua t, hξ t,
      smul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨⟨fun t i => ?_, fun t i => ?_, fun i => hxa 0 i⟩, hE⟩
  · rw [lq_predError E A B C hxa hua h t i]
    simp only [hξ t, sub_zero]
  · simp only [matAct, map_sum, map_smul, hξ t, smul_zero, Finset.sum_const_zero]

/-! ### The first-order conditions -/

/-- The date-`t` terms of the Lagrangian of the LQ problem divided by `βᵗ` (Miao, p. 58), with the
multiplier term `+β^{t+1}λ_{t+1}'(x_{t+1} − Ax_t − Bu_t − Cξ_{t+1})`:
`ℓ = −½(x'Qx + 2x'Su + u'Ru) − βλ_{t+1}'(Ax + Bu) + λ_t'x`. -/
noncomputable def lqPeriod {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ)
    (S : Matrix (Fin nx) (Fin nu) ℝ)
    (R : Matrix (Fin nu) (Fin nu) ℝ) (A : Matrix (Fin nx) (Fin nx) ℝ)
    (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ) (lam lamN x : Fin nx → ℝ) (u : Fin nu → ℝ) :
    ℝ :=
  -(1 / 2) * (x ⬝ᵥ Q *ᵥ x + 2 * (x ⬝ᵥ S *ᵥ u) + u ⬝ᵥ R *ᵥ u) -
    β * (lamN ⬝ᵥ (A *ᵥ x + B *ᵥ u)) + lam ⬝ᵥ x

/-- The first-order condition for `u_t` (Miao, p. 58): for symmetric `R` the first variation of
the date-`t` Lagrangian in `u` is `−(S'x + Ru + βB'λ_{t+1})·h − ½h'Rh`, so the first-order
condition is `S'x_t + Ru_t + βB'λ_{t+1} = 0` (with `E_tλ_{t+1}` after conditioning). -/
theorem lq_variation_u {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ)
    (S : Matrix (Fin nx) (Fin nu) ℝ) (R : Matrix (Fin nu) (Fin nu) ℝ) (hR : Rᵀ = R)
    (A : Matrix (Fin nx) (Fin nx) ℝ) (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ)
    (lam lamN x : Fin nx → ℝ) (u h : Fin nu → ℝ) :
    lqPeriod Q S R A B β lam lamN x (u + h) - lqPeriod Q S R A B β lam lamN x u =
      -((Sᵀ *ᵥ x + R *ᵥ u + β • (Bᵀ *ᵥ lamN)) ⬝ᵥ h) - 1 / 2 * (h ⬝ᵥ R *ᵥ h) := by
  have e1 : x ⬝ᵥ S *ᵥ h = (Sᵀ *ᵥ x) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have e2 : u ⬝ᵥ R *ᵥ h = (R *ᵥ u) ⬝ᵥ h := by
    conv_rhs => rw [← hR, Matrix.mulVec_transpose]
    rw [Matrix.dotProduct_mulVec]
  have e3 : h ⬝ᵥ R *ᵥ u = (R *ᵥ u) ⬝ᵥ h := dotProduct_comm _ _
  have e4 : lamN ⬝ᵥ B *ᵥ h = (Bᵀ *ᵥ lamN) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  simp only [lqPeriod, Matrix.mulVec_add, dotProduct_add, add_dotProduct, smul_dotProduct,
    smul_eq_mul, e1, e2, e3, e4]
  ring

/-- The first-order condition for `x_t` (Miao, p. 58): for symmetric `Q` the first variation of
the date-`t` Lagrangian in `x` is `−(Qx + Su − λ_t + βA'λ_{t+1})·h − ½h'Qh`, so the first-order
condition is `Qx_t + Su_t − λ_t + βA'λ_{t+1} = 0` (with `E_tλ_{t+1}` after conditioning). -/
theorem lq_variation_x {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ) (hQ : Qᵀ = Q)
    (S : Matrix (Fin nx) (Fin nu) ℝ) (R : Matrix (Fin nu) (Fin nu) ℝ)
    (A : Matrix (Fin nx) (Fin nx) ℝ) (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ)
    (lam lamN x h : Fin nx → ℝ) (u : Fin nu → ℝ) :
    lqPeriod Q S R A B β lam lamN (x + h) u - lqPeriod Q S R A B β lam lamN x u =
      -((Q *ᵥ x + S *ᵥ u - lam + β • (Aᵀ *ᵥ lamN)) ⬝ᵥ h) - 1 / 2 * (h ⬝ᵥ Q *ᵥ h) := by
  have e1 : x ⬝ᵥ Q *ᵥ h = (Q *ᵥ x) ⬝ᵥ h := by
    conv_rhs => rw [← hQ, Matrix.mulVec_transpose]
    rw [Matrix.dotProduct_mulVec]
  have e2 : h ⬝ᵥ Q *ᵥ x = (Q *ᵥ x) ⬝ᵥ h := dotProduct_comm _ _
  have e3 : h ⬝ᵥ S *ᵥ u = (S *ᵥ u) ⬝ᵥ h := dotProduct_comm _ _
  have e4 : lamN ⬝ᵥ A *ᵥ h = (Aᵀ *ᵥ lamN) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have e5 : lam ⬝ᵥ h = h ⬝ᵥ lam := dotProduct_comm _ _
  simp only [lqPeriod, Matrix.mulVec_add, dotProduct_add, add_dotProduct, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, e1, e2, e3, e4, e5]
  ring

/-! ### The linear system on p. 58 -/

/-- The left matrix of the system on p. 58, `[[I, 0, 0], [0, 0, −βB'], [0, 0, βA']]`, on the
index `(x, u, λ) = (Fin nx ⊕ Fin nu) ⊕ Fin nx`. -/
def lqLeft {nx nu : ℕ} (A : Matrix (Fin nx) (Fin nx) 𝕜) (B : Matrix (Fin nx) (Fin nu) 𝕜) (β : 𝕜) :
    Matrix ((Fin nx ⊕ Fin nu) ⊕ Fin nx) ((Fin nx ⊕ Fin nu) ⊕ Fin nx) 𝕜 :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 0) (Matrix.fromRows 0 (-(β • Bᵀ))) 0 (β • Aᵀ)

/-- The right matrix of the system on p. 58, `[[A, B, 0], [S', R, 0], [−Q, −S, I]]`. -/
def lqRight {nx nu : ℕ} (A : Matrix (Fin nx) (Fin nx) 𝕜) (B : Matrix (Fin nx) (Fin nu) 𝕜)
    (Q : Matrix (Fin nx) (Fin nx) 𝕜) (S : Matrix (Fin nx) (Fin nu) 𝕜)
    (R : Matrix (Fin nu) (Fin nu) 𝕜) :
    Matrix ((Fin nx ⊕ Fin nu) ⊕ Fin nx) ((Fin nx ⊕ Fin nu) ⊕ Fin nx) 𝕜 :=
  Matrix.fromBlocks (Matrix.fromBlocks A B Sᵀ R) 0 (Matrix.fromCols (-Q) (-S)) 1

theorem klL_matAct_fromBlocks {l m n o : Type*} [Fintype l] [Fintype m]
    (P : Matrix n l 𝕜) (P' : Matrix n m 𝕜) (R : Matrix o l 𝕜) (R' : Matrix o m 𝕜) (a : l → V)
    (b : m → V) :
    matAct (Matrix.fromBlocks P P' R R') (Sum.elim a b) =
      Sum.elim (matAct P a + matAct P' b) (matAct R a + matAct R' b) := by
  funext i
  cases i <;> simp [matAct, Fintype.sum_sum_type]

theorem klL_matAct_fromRows {m₁ m₂ n : Type*} [Fintype n] (P : Matrix m₁ n 𝕜)
    (R : Matrix m₂ n 𝕜) (v : n → V) :
    matAct (Matrix.fromRows P R) v = Sum.elim (matAct P v) (matAct R v) := by
  funext i
  cases i <;> simp [matAct]

theorem klL_matAct_fromCols {m n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] (P : Matrix m n₁ 𝕜)
    (R : Matrix m n₂ 𝕜) (a : n₁ → V) (b : n₂ → V) :
    matAct (Matrix.fromCols P R) (Sum.elim a b) = matAct P a + matAct R b := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

theorem klL_matAct_zero {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ 𝕜) x = 0 := by
  funext i
  simp [matAct]

theorem klL_matAct_smul {ι κ : Type*} [Fintype κ] (c : 𝕜) (M : Matrix ι κ 𝕜) (x : κ → V) :
    matAct (c • M) x = c • matAct M x := by
  funext i
  simp [matAct, Finset.smul_sum, smul_smul]

theorem klL_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ 𝕜) (x : κ → V) :
    matAct (-M) x = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem klL_Evec_elim {α β : Type*} (E : CondExpSystem 𝕜 V) (t : ℕ) (a : α → V) (b : β → V) :
    Evec E t (Sum.elim a b) = Sum.elim (Evec E t a) (Evec E t b) := by
  funext i
  cases i <;> rfl

/-- **The LQ system** (Miao, p. 58). For processes `x`, `u`, `λ`, the system
`[[I, 0, 0], [0, 0, −βB'], [0, 0, βA']] E_t(x, u, λ)_{t+1} = [[A, B, 0], [S', R, 0], [−Q, −S, I]]
(x, u, λ)_t` ((2.11) with no forcing) holds iff `E_t x_{t+1} = Ax_t + Bu_t` and the first-order
conditions `S'x_t + Ru_t + βB'E_tλ_{t+1} = 0`, `Qx_t + Su_t − λ_t + βA'E_tλ_{t+1} = 0` hold
(`lq_variation_u`, `lq_variation_x`; `'` is the transpose). -/
theorem lq_system_iff {nx nu : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (Q : Matrix (Fin nx) (Fin nx) 𝕜)
    (S : Matrix (Fin nx) (Fin nu) 𝕜) (R : Matrix (Fin nu) (Fin nu) 𝕜) (β : 𝕜)
    (x lam : ℕ → Fin nx → V) (u : ℕ → Fin nu → V) :
    IsRESolution E (lqLeft A B β) (lqRight A B Q S R) (0 : Matrix _ (Fin 0) 𝕜) (fun _ => 0)
        (fun t => Sum.elim (Sum.elim (x t) (u t)) (lam t)) ↔
      ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) ∧
        matAct Sᵀ (x t) + matAct R (u t) + β • matAct Bᵀ (Evec E t (lam (t + 1))) = 0 ∧
        matAct Q (x t) + matAct S (u t) - lam t + β • matAct Aᵀ (Evec E t (lam (t + 1))) = 0 := by
  refine forall_congr' fun t => ?_
  simp only [lqLeft, lqRight, klL_Evec_elim, klL_matAct_fromBlocks, klL_matAct_fromRows,
    klL_matAct_fromCols, klL_matAct_zero, klL_matAct_smul, klL_matAct_neg, matAct_one,
    zero_add, add_zero, ← Sum.elim_add_add, Sum.elim_eq_iff]
  have key1 : ∀ P a b : Fin nu → V, -P = a + b ↔ a + b + P = 0 := fun P a b => by
    rw [← sub_eq_zero, show -P - (a + b) = -(a + b + P) by abel, neg_eq_zero]
  have key2 : ∀ P a b c : Fin nx → V, P = -a + -b + c ↔ a + b - c + P = 0 := fun P a b c => by
    rw [← sub_eq_zero, show P - (-a + -b + c) = a + b - c + P by abel]
  rw [and_assoc]
  exact and_congr Iff.rfl (and_congr (key1 _ _ _) (key2 _ _ _ _))

end Miao.RationalExpectations
