/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.LSStability
import Mathlib.Data.Matrix.Block

/-!
# The LQ problem, the Riccati operator and completing the square

Copied from `EconomicDynamics/LinearQuadratic` (module `LSRiccati`), namespace renamed.

Miao, §9.2–§9.3, pp. 294–302. A (one-period) LQ problem `LSProblem` carries the matrices
`A, B, C, Q, R, S` of the transition `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}` (9.1) and of the loss
`r(x, u) = x'Qx + u'Ru + 2x'Su`, and the discount factor `β`. For a matrix `P` set

* `G(P) = R + βB'PB` and `N(P) = S' + βB'PA`;
* the Riccati operator (9.5)/(9.11) `T(P) = Q + βA'PA − (S + βA'PB)G(P)⁻¹(S' + βB'PA)`;
* the gain (9.8)/(9.17) `F(P) = G(P)⁻¹(S' + βB'PA)`;
* the policy map of (9.9) `T_F(P) = Q − F'S' − SF + F'RF + β(A − BF)'P(A − BF)`.

Main algebra (used by Proposition 9.2.1, §9.3 and the exercises):

* `G_posDef`: `R > 0`, `P ≥ 0`, `β ≥ 0` give `G(P) > 0` (Miao, p. 296).
* `TF_F`: `T_{F(P)}(P) = T(P)` (the rewritten Riccati equation of p. 302).
* `TF_eq_T_add`: `T_F(P) = T(P) + (F − F(P))'G(P)(F − F(P))`, hence (9.9): `T(P)` is the
  minimum of `T_F(P)` over `F` in the Loewner order, uniquely at `F(P)` (`TF_ge_T`,
  `TF_eq_T_iff`).
* `loss_add_cont`: completing the square,
  `r(x, u) + β(Ax + Bu)'P(Ax + Bu) = x'T(P)x + (u + F(P)x)'G(P)(u + F(P)x)`.
* `T_transpose`, `T_posSemidef`: `T(P)` is symmetric, and positive semidefinite when the joint
  matrix `[[Q, S], [S', R]]` is (`JointPSD`).
-/

open Matrix

open scoped MatrixOrder

namespace Miao.PartialInformation

/-- An LQ problem (Miao, §9.2–§9.3): the transition `x' = Ax + Bu + Cε` (9.1), the loss
`x'Qx + u'Ru + 2x'Su` and the discount factor `β`. -/
structure LSProblem (X U E : Type*) where
  /-- the state transition matrix -/
  A : Matrix X X ℝ
  /-- the control matrix -/
  B : Matrix X U ℝ
  /-- the shock loading -/
  C : Matrix X E ℝ
  /-- the state cost -/
  Q : Matrix X X ℝ
  /-- the control cost -/
  R : Matrix U U ℝ
  /-- the cross cost -/
  S : Matrix X U ℝ
  /-- the discount factor -/
  β : ℝ

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] (L : LSProblem X U E)

/-- The period loss `r(x, u) = x'Qx + u'Ru + 2x'Su` (the period return is `−r`). -/
def loss (x : X → ℝ) (u : U → ℝ) : ℝ :=
  x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) + 2 * (x ⬝ᵥ (L.S *ᵥ u))

/-- The joint cost matrix `[[Q, S], [S', R]]` is positive semidefinite (Proposition 9.2.1). -/
def JointPSD : Prop := (fromBlocks L.Q L.S L.Sᵀ L.R).PosSemidef

/-- `G(P) = R + βB'PB`. -/
def G (P : Matrix X X ℝ) : Matrix U U ℝ := L.R + L.β • (L.Bᵀ * P * L.B)

/-- `N(P) = S' + βB'PA`. -/
def N (P : Matrix X X ℝ) : Matrix U X ℝ := L.Sᵀ + L.β • (L.Bᵀ * P * L.A)

/-- The policy map of (9.9): `T_F(P) = Q − F'S' − SF + F'RF + β(A − BF)'P(A − BF)`. -/
def TF (P : Matrix X X ℝ) (F : Matrix U X ℝ) : Matrix X X ℝ :=
  L.Q - Fᵀ * L.Sᵀ - L.S * F + Fᵀ * L.R * F + L.β • ((L.A - L.B * F)ᵀ * P * (L.A - L.B * F))

variable [DecidableEq U]

/-- The Riccati operator (9.5), (9.11):
`T(P) = Q + βA'PA − (S + βA'PB)(R + βB'PB)⁻¹(S' + βB'PA)`. -/
noncomputable def T (P : Matrix X X ℝ) : Matrix X X ℝ :=
  L.Q + L.β • (L.Aᵀ * P * L.A) - (L.S + L.β • (L.Aᵀ * P * L.B)) * (L.G P)⁻¹ * L.N P

/-- The gain (9.8), (9.17): `F(P) = (R + βB'PB)⁻¹(S' + βB'PA)`; the control is `u = −F(P)x`. -/
noncomputable def F (P : Matrix X X ℝ) : Matrix U X ℝ := (L.G P)⁻¹ * L.N P

omit [Fintype U] [DecidableEq U] in
/-- Miao, p. 296: `R > 0`, `P ≥ 0` (and `β ≥ 0`) make `R + βB'PB` positive definite. -/
theorem G_posDef [Finite U] (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hβ : 0 ≤ L.β) :
    (L.G P).PosDef :=
  hR.add_posSemidef ((SS.LQProblem.posSemidef_transpose_mul_mul hP L.B).smul hβ)

omit [Fintype U] [DecidableEq U] in
theorem G_transpose (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) : (L.G P)ᵀ = L.G P := by
  simp only [G, transpose_add, transpose_smul, transpose_mul, transpose_transpose, hR, hP,
    Matrix.mul_assoc]

omit [Fintype U] [DecidableEq U] in
theorem N_transpose {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (L.N P)ᵀ = L.S + L.β • (L.Aᵀ * P * L.B) := by
  simp only [N, transpose_add, transpose_smul, transpose_mul, transpose_transpose, hP,
    Matrix.mul_assoc]

/-- `G(P)F(P) = N(P)`. -/
theorem G_mul_F {P : Matrix X X ℝ} (h : IsUnit (L.G P).det) : L.G P * L.F P = L.N P :=
  mul_nonsing_inv_cancel_left _ _ h

theorem T_eq_sub (P : Matrix X X ℝ) :
    L.T P = L.Q + L.β • (L.Aᵀ * P * L.A) - (L.S + L.β • (L.Aᵀ * P * L.B)) * L.F P := by
  simp only [T, F, Matrix.mul_assoc]

omit [DecidableEq U] in
/-- Expanding the policy map: `T_F(P) = Q + βA'PA − F'N(P) − (S + βA'PB)F + F'G(P)F`. -/
theorem TF_expand (P : Matrix X X ℝ) (F' : Matrix U X ℝ) :
    L.TF P F' = L.Q + L.β • (L.Aᵀ * P * L.A) - F'ᵀ * L.N P -
      (L.S + L.β • (L.Aᵀ * P * L.B)) * F' + F'ᵀ * (L.G P * F') := by
  simp only [TF, N, G, transpose_sub, transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    smul_sub]
  abel

/-- Miao, p. 302: the Riccati equation rewritten with `F = F(P)`:
`T(P) = Q + F'RF − SF − F'S' + β(A − BF)'P(A − BF)`. -/
theorem TF_F {P : Matrix X X ℝ} (h : IsUnit (L.G P).det) : L.TF P (L.F P) = L.T P := by
  rw [TF_expand, L.G_mul_F h, T_eq_sub]
  abel

/-- `T_F(P) = T(P) + (F − F(P))'G(P)(F − F(P))` for symmetric `R`, `P`. -/
theorem TF_eq_T_add (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (h : IsUnit (L.G P).det)
    (F' : Matrix U X ℝ) :
    L.TF P F' = L.T P + (F' - L.F P)ᵀ * L.G P * (F' - L.F P) := by
  have hN : L.N P = L.G P * L.F P := (L.G_mul_F h).symm
  have hNs : L.S + L.β • (L.Aᵀ * P * L.B) = (L.F P)ᵀ * L.G P := by
    rw [← L.N_transpose hP, hN, transpose_mul, L.G_transpose hR hP]
  rw [TF_expand, T_eq_sub, hN, hNs]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- (9.9) (Miao, p. 297): `T(P) ≤ T_F(P)` for every `F` in the Loewner order. -/
theorem TF_ge_T (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (hG : (L.G P).PosDef)
    (F' : Matrix U X ℝ) : L.T P ≤ L.TF P F' := by
  rw [Matrix.le_iff, L.TF_eq_T_add hR hP ((isUnit_iff_isUnit_det _).1 hG.isUnit) F',
    add_sub_cancel_left]
  exact SS.LQProblem.posSemidef_transpose_mul_mul hG.posSemidef _

/-- (9.9): the minimiser is unique, `T_F(P) = T(P)` iff `F = F(P)`. -/
theorem TF_eq_T_iff (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (hG : (L.G P).PosDef)
    (F' : Matrix U X ℝ) : L.TF P F' = L.T P ↔ F' = L.F P := by
  classical
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  refine ⟨fun h => ?_, fun h => h ▸ L.TF_F hu⟩
  rw [L.TF_eq_T_add hR hP hu, add_eq_left] at h
  have hG' := SS.LQProblem.posDef_iff_real.1 hG
  have hx : ∀ x, (F' - L.F P) *ᵥ x = 0 := by
    intro x
    by_contra hne
    have h1 := hG'.2 hne
    rw [← SS.LQProblem.dotProduct_transpose_mul_mul, h, zero_mulVec, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  rw [← sub_eq_zero]
  ext i j
  have := congrFun (hx (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- Completing the square: for symmetric invertible `G`,
`u'Gu + 2u·n = (u + G⁻¹n)'G(u + G⁻¹n) − n'G⁻¹n`. -/
theorem ls_sq_complete {G : Matrix U U ℝ} (hG : Gᵀ = G) (h : IsUnit G.det) (u n : U → ℝ) :
    u ⬝ᵥ (G *ᵥ u) + 2 * (u ⬝ᵥ n) =
      (u + G⁻¹ *ᵥ n) ⬝ᵥ (G *ᵥ (u + G⁻¹ *ᵥ n)) - n ⬝ᵥ (G⁻¹ *ᵥ n) := by
  set f := G⁻¹ *ᵥ n
  have hGf : G *ᵥ f = n := by
    simp only [f, mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]
  rw [SS.LQProblem.quad_add hG u f, SS.LQProblem.dotProduct_mulVec_comm_of_symm hG f u, hGf,
    dotProduct_comm n f]
  ring

omit [DecidableEq U] in
/-- `x'Su = u'S'x`. -/
theorem dot_S_comm (M : Matrix X U ℝ) (x : X → ℝ) (u : U → ℝ) :
    x ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (Mᵀ *ᵥ x) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- Completing the square (Miao, pp. 295–296): for symmetric `R`, `P` and invertible `G(P)`,
`r(x, u) + β(Ax + Bu)'P(Ax + Bu) = x'T(P)x + (u + F(P)x)'G(P)(u + F(P)x)`. -/
theorem loss_add_cont (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (h : IsUnit (L.G P).det) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u + L.β * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))) =
      x ⬝ᵥ (L.T P *ᵥ x) + (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) := by
  have hGs := L.G_transpose hR hP
  have e1 := SS.LQProblem.quad_add hP (L.A *ᵥ x) (L.B *ᵥ u)
  have e2 : (L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x)) = u ⬝ᵥ ((L.Bᵀ * P * L.A) *ᵥ x) := by
    rw [SS.LQProblem.mulVec_dotProduct, ← mulVec_mulVec, ← mulVec_mulVec]
  have e3 : (L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.B *ᵥ u)) = u ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ u) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul L.B P u).symm
  have e4 : (L.A *ᵥ x) ⬝ᵥ (P *ᵥ (L.A *ᵥ x)) = x ⬝ᵥ ((L.Aᵀ * P * L.A) *ᵥ x) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul L.A P x).symm
  have e5 := dot_S_comm L.S x u
  have eG : u ⬝ᵥ (L.G P *ᵥ u) = u ⬝ᵥ (L.R *ᵥ u) + L.β * (u ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ u)) := by
    rw [G, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have eN : u ⬝ᵥ (L.N P *ᵥ x) = u ⬝ᵥ (L.Sᵀ *ᵥ x) + L.β * (u ⬝ᵥ ((L.Bᵀ * P * L.A) *ᵥ x)) := by
    rw [N, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hsq := ls_sq_complete hGs h u (L.N P *ᵥ x)
  have hF : L.F P *ᵥ x = (L.G P)⁻¹ *ᵥ (L.N P *ᵥ x) := by rw [F, mulVec_mulVec]
  have eT : x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.Q *ᵥ x) + L.β * (x ⬝ᵥ ((L.Aᵀ * P * L.A) *ᵥ x)) -
      (L.N P *ᵥ x) ⬝ᵥ ((L.G P)⁻¹ *ᵥ (L.N P *ᵥ x)) := by
    rw [T, ← L.N_transpose hP, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub,
      dotProduct_add, dotProduct_smul, smul_eq_mul, SS.LQProblem.dotProduct_transpose_mul_mul L.A,
      SS.LQProblem.dotProduct_transpose_mul_mul (L.N P)]
  rw [hF, eT]
  simp only [loss]
  rw [e1, e2, e3, e4, e5]
  linear_combination hsq - eG - 2 * eN

omit [DecidableEq U] in
/-- The joint matrix's quadratic form is the loss: `[x; u]'[[Q, S], [S', R]][x; u] = r(x, u)`. -/
theorem quad_joint (x : X → ℝ) (u : U → ℝ) :
    Sum.elim x u ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ Sum.elim x u) = L.loss x u := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add, loss,
    ← dot_S_comm L.S x u]
  ring

omit [DecidableEq U] in
/-- Under `JointPSD`, the loss is nonnegative. -/
theorem loss_nonneg (hJ : L.JointPSD) (x : X → ℝ) (u : U → ℝ) : 0 ≤ L.loss x u := by
  rw [← L.quad_joint]
  exact (SS.LQProblem.posSemidef_iff_real.1 hJ).2 _

omit [Fintype X] [Fintype U] [DecidableEq U] in
/-- Under `JointPSD`, `Q` is symmetric. -/
theorem Q_transpose_of_joint [Finite X] [Finite U] (hJ : L.JointPSD) : L.Qᵀ = L.Q := by
  cases nonempty_fintype X
  cases nonempty_fintype U
  have h := (SS.LQProblem.posSemidef_iff_real.1 hJ).1
  rw [fromBlocks_transpose] at h
  exact (Matrix.fromBlocks_inj.1 h).1

omit [Fintype X] [Fintype U] [DecidableEq U] in
/-- Under `JointPSD`, `Q` is positive semidefinite. -/
theorem Q_posSemidef_of_joint [Finite X] [Finite U] (hJ : L.JointPSD) : L.Q.PosSemidef := by
  cases nonempty_fintype X
  cases nonempty_fintype U
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨L.Q_transpose_of_joint hJ, fun x => ?_⟩
  have := L.loss_nonneg hJ x 0
  simpa [loss] using this

/-- `T(P)` is symmetric for symmetric `Q`, `R`, `P` with `G(P)` invertible. -/
theorem T_transpose (hQ : L.Qᵀ = L.Q) (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (L.T P)ᵀ = L.T P := by
  have hNs := L.N_transpose hP
  rw [T, ← hNs, transpose_sub, transpose_add, transpose_mul, transpose_mul, transpose_transpose,
    transpose_smul, transpose_nonsing_inv, L.G_transpose hR hP, hQ]
  simp only [transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

/-- Miao, p. 295 (`P_t ≥ 0`): under `JointPSD`, `R > 0`, `β ≥ 0` and `P ≥ 0`, `T(P) ≥ 0`. -/
theorem T_posSemidef (hJ : L.JointPSD) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) : (L.T P).PosSemidef := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hu := (isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit
  refine SS.LQProblem.posSemidef_iff_real.2
    ⟨L.T_transpose (L.Q_transpose_of_joint hJ) hRs hPs, fun x => ?_⟩
  have h := L.loss_add_cont hRs hPs hu x (-(L.F P *ᵥ x))
  rw [neg_add_cancel, mulVec_zero, dotProduct_zero, add_zero] at h
  rw [← h]
  exact add_nonneg (L.loss_nonneg hJ _ _)
    (mul_nonneg hβ ((SS.LQProblem.posSemidef_iff_real.1 hP).2 _))

end LSProblem

end Miao.PartialInformation
