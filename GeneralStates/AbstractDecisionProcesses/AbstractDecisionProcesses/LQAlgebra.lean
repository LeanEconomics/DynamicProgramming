/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# LQ control: the Riccati map and the control gain

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.1–§2.3.5.2 and §2.3.5.6
(pp. 89–91, 94).

An LQ problem `(Q, R, A, B)` has `Q` positive semidefinite and `R` positive definite. For
positive semidefinite `P`, set `G(P) = BᵀPB + R` (positive definite), the Riccati map
`R(P) = AᵀPA − AᵀPB G(P)⁻¹ BᵀPA + Q` (2.27), the control gain `F(P) = −G(P)⁻¹BᵀPA` (2.28) and the
policy operators `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)` (2.32).

* **Exercise 2.3.13**: `R(P) = T_{F(P)}(P)`.
* **Exercise 2.3.14**: `R` maps the positive semidefinite cone `𝒫` into itself.
* **Exercise 2.3.16**: each `T_F` is an order preserving self-map of `(𝒫, ≼)` (Loewner order).
* **Lemma 2.3.3**: `F(P)x` is the unique minimizer of `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)`, by
  completing the square: the objective at `F(P)x + d` exceeds its minimum by `dᵀG(P)d`.
* **Exercise 2.3.17**: `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control matrix `G`.
-/

open Matrix

open scoped MatrixOrder

namespace SargentStachurski.AbstractDecisionProcesses

/-- An LQ control problem `(Q, R, A, B)` (§2.3.5.1). -/
structure LQProblem (K U : Type*) [Fintype K] [Fintype U] where
  /-- the state transition matrix -/
  A : Matrix K K ℝ
  /-- the control matrix -/
  B : Matrix K U ℝ
  /-- the state cost -/
  Q : Matrix K K ℝ
  /-- the control cost -/
  R : Matrix U U ℝ
  Q_psd : Q.PosSemidef
  R_pd : R.PosDef

namespace LQProblem

variable {K U : Type*} [Fintype K] [Fintype U] (L : LQProblem K U)

/-- `G(P) = BᵀPB + R`. -/
def gainDen (P : Matrix K K ℝ) : Matrix U U ℝ := L.Bᵀ * P * L.B + L.R

/-- The policy operator (2.32): `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)`. -/
def TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Q + Fᵀ * L.R * F + (L.A + L.B * F)ᵀ * P * (L.A + L.B * F)

/-- The one-period objective `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` of (2.26). -/
def cost (P : Matrix K K ℝ) (x : K → ℝ) (u : U → ℝ) : ℝ :=
  x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) +
    (L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))

/-! ### Positivity and quadratic forms -/

omit [Fintype U] in
theorem posSemidef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
theorem posDef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosDef ↔ Mᵀ = M ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
  rw [posDef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
/-- `Mᵀ P M` is positive semidefinite for positive semidefinite `P`. -/
theorem posSemidef_transpose_mul_mul {n m : Type*} [Fintype n] [Finite m]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (M : Matrix n m ℝ) : (Mᵀ * P * M).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hP.conjTranspose_mul_mul_same M

/-- `G(P) = BᵀPB + R` is positive definite for positive semidefinite `P`. -/
theorem gainDen_posDef {P : Matrix K K ℝ} (hP : P.PosSemidef) : (L.gainDen P).PosDef :=
  Matrix.PosDef.posSemidef_add (posSemidef_transpose_mul_mul hP L.B) L.R_pd

omit [Fintype U] in
/-- For symmetric `S`, `a ⬝ Sb = b ⬝ Sa`. -/
theorem dotProduct_mulVec_comm_of_symm {n : Type*} [Fintype n] {S : Matrix n n ℝ}
    (hS : Sᵀ = S) (a b : n → ℝ) : a ⬝ᵥ (S *ᵥ b) = b ⬝ᵥ (S *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

omit [Fintype U] in
/-- `(Bd) ⬝ w = d ⬝ (Bᵀw)`. -/
theorem mulVec_dotProduct {n m : Type*} [Fintype n] [Fintype m] (B : Matrix n m ℝ) (d : m → ℝ)
    (w : n → ℝ) : (B *ᵥ d) ⬝ᵥ w = d ⬝ᵥ (Bᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

omit [Fintype U] in
/-- `xᵀ(NᵀSN)x = (Nx)ᵀS(Nx)`. -/
theorem dotProduct_transpose_mul_mul {n m : Type*} [Fintype n] [Fintype m] (N : Matrix n m ℝ)
    (S : Matrix n n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((Nᵀ * S * N) *ᵥ x) = (N *ᵥ x) ⬝ᵥ (S *ᵥ (N *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_dotProduct N x]

omit [Fintype U] in
/-- `(a + b)ᵀS(a + b) = aᵀSa + 2bᵀSa + bᵀSb` for symmetric `S`. -/
theorem quad_add {n : Type*} [Fintype n] {S : Matrix n n ℝ} (hS : Sᵀ = S) (a b : n → ℝ) :
    (a + b) ⬝ᵥ (S *ᵥ (a + b)) = a ⬝ᵥ (S *ᵥ a) + 2 * (b ⬝ᵥ (S *ᵥ a)) + b ⬝ᵥ (S *ᵥ b) := by
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_mulVec_comm_of_symm hS a b]
  ring

/-- The quadratic form of `T_F(P)` is the objective at `u = Fx`. -/
theorem dotProduct_TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) (x : K → ℝ) :
    x ⬝ᵥ (L.TF F P *ᵥ x) = L.cost P x (F *ᵥ x) := by
  simp only [TF, cost, add_mulVec, dotProduct_add, dotProduct_transpose_mul_mul, mulVec_mulVec]

/-! ### Exercise 2.3.16 -/

/-- `T_F(P)` is positive semidefinite for positive semidefinite `P`. -/
theorem TF_posSemidef (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P).PosSemidef :=
  (L.Q_psd.add (posSemidef_transpose_mul_mul L.R_pd.posSemidef F)).add
    (posSemidef_transpose_mul_mul hP _)

/-- `T_F(P)` is symmetric for positive semidefinite `P`. -/
theorem TF_transpose (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P)ᵀ = L.TF F P :=
  (posSemidef_iff_real.1 (L.TF_posSemidef F hP)).1

/-- **Exercise 2.3.16** (p. 93): each `T_F` is order preserving for the Loewner order (and maps
`𝒫` into itself, `TF_posSemidef`). -/
theorem TF_mono (F : Matrix U K ℝ) {P P' : Matrix K K ℝ} (h : P ≤ P') : L.TF F P ≤ L.TF F P' := by
  rw [le_iff] at h ⊢
  have : L.TF F P' - L.TF F P = (L.A + L.B * F)ᵀ * (P' - P) * (L.A + L.B * F) := by
    simp only [TF, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [this]
  exact posSemidef_transpose_mul_mul h _

/-- Expanding `T_F(P)`. -/
theorem TF_expand (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.Q + L.Aᵀ * P * L.A + L.Aᵀ * P * (L.B * F) + Fᵀ * (L.Bᵀ * P * L.A) +
      Fᵀ * (L.gainDen P * F) := by
  simp only [TF, gainDen, transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

/-! ### The Riccati map and the control gain -/

variable [DecidableEq U]

/-- The Riccati map (2.27): `R(P) = AᵀPA − AᵀPB(BᵀPB + R)⁻¹BᵀPA + Q`. -/
noncomputable def riccati (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Aᵀ * P * L.A - L.Aᵀ * P * L.B * (L.gainDen P)⁻¹ * L.Bᵀ * P * L.A + L.Q

/-- The control gain map (2.28): `F(P) = −(BᵀPB + R)⁻¹BᵀPA`. -/
noncomputable def gain (P : Matrix K K ℝ) : Matrix U K ℝ := -((L.gainDen P)⁻¹ * L.Bᵀ * P * L.A)

/-- `G(P)F(P) = −BᵀPA`. -/
theorem gainDen_mul_gain {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.gainDen P * L.gain P = -(L.Bᵀ * P * L.A) := by
  have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit)
  simp only [gain, Matrix.mul_neg, ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- **Exercise 2.3.13** (p. 90): `R(P) = (A + BF)ᵀP(A + BF) + FᵀRF + Q` when `F = F(P)`. -/
theorem riccati_eq_TF {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.riccati P = L.TF (L.gain P) P := by
  rw [TF_expand, L.gainDen_mul_gain hP]
  simp only [riccati, gain, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- **Exercise 2.3.14** (p. 90): `R` maps `𝒫` into itself. -/
theorem riccati_posSemidef {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.riccati P).PosSemidef := by
  rw [L.riccati_eq_TF hP]
  exact L.TF_posSemidef _ hP

/-! ### Lemma 2.3.3: the control gain minimizes the one-period objective -/

/-- Completing the square: `J(F(P)x + d) = J(F(P)x) + dᵀG(P)d`. -/
theorem cost_gain_add {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) (d : U → ℝ) :
    L.cost P x (L.gain P *ᵥ x + d) = L.cost P x (L.gain P *ᵥ x) + d ⬝ᵥ (L.gainDen P *ᵥ d) := by
  have hPs : Pᵀ = P := (posSemidef_iff_real.1 hP).1
  have hRs : L.Rᵀ = L.R := (posDef_iff_real.1 L.R_pd).1
  set F := L.gain P
  set y := L.A *ᵥ x + L.B *ᵥ (F *ᵥ x)
  have hGF : L.gainDen P *ᵥ (F *ᵥ x) = -(L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) := by
    rw [mulVec_mulVec, L.gainDen_mul_gain hP, neg_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hsplit : L.A *ᵥ x + L.B *ᵥ (F *ᵥ x + d) = y + L.B *ᵥ d := by
    simp only [y, mulVec_add]
    abel
  -- the cross terms vanish: `R(Fx) + BᵀP(Ax + BFx) = (G F + BᵀPA)x = 0`
  have hcross : d ⬝ᵥ (L.R *ᵥ (F *ᵥ x)) + d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) = 0 := by
    have e : L.gainDen P *ᵥ (F *ᵥ x) =
        L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) := by
      rw [gainDen, add_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [hGF] at e
    have : L.R *ᵥ (F *ᵥ x) + L.Bᵀ *ᵥ (P *ᵥ y) = 0 := by
      simp only [y, mulVec_add]
      rw [← sub_eq_zero]
      have e' := congrArg (fun z => z + L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) e
      simp only [neg_add_cancel] at e'
      rw [sub_zero]
      calc L.R *ᵥ (F *ᵥ x) + (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) + L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))))
          = L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) +
              L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) := by abel
        _ = 0 := e'.symm
    rw [← dotProduct_add, this, dotProduct_zero]
  have h1 := quad_add hRs (F *ᵥ x) d
  have h2 := quad_add hPs y (L.B *ᵥ d)
  have h3 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ y) = d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) := mulVec_dotProduct L.B d _
  have h4 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ (L.B *ᵥ d)) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) :=
    (dotProduct_transpose_mul_mul L.B P d).symm
  have h5 : d ⬝ᵥ (L.gainDen P *ᵥ d) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) + d ⬝ᵥ (L.R *ᵥ d) := by
    rw [gainDen, add_mulVec, dotProduct_add]
  simp only [cost]
  rw [hsplit, h1, h2, h3, h4, h5]
  linear_combination (2 : ℝ) * hcross

/-- **Lemma 2.3.3** (p. 91): `F(P)x` minimizes `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` over
`u ∈ ℝᵐ`, and the minimizer is unique. -/
theorem gain_isMinimizer {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) :
    (∀ u, L.cost P x (L.gain P *ᵥ x) ≤ L.cost P x u) ∧
      ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) → u = L.gain P *ᵥ x := by
  have hG := posDef_iff_real.1 (L.gainDen_posDef hP)
  have key : ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) +
      (u - L.gain P *ᵥ x) ⬝ᵥ (L.gainDen P *ᵥ (u - L.gain P *ᵥ x)) := fun u => by
    have := L.cost_gain_add hP x (u - L.gain P *ᵥ x)
    rwa [add_sub_cancel] at this
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [key u]
    rcases eq_or_ne (u - L.gain P *ᵥ x) 0 with h | h
    · rw [h]; simp
    · linarith [hG.2 h]
  · by_contra hne
    have := hG.2 (sub_ne_zero.2 hne)
    rw [key u] at hu
    linarith

/-- **Exercise 2.3.17** (p. 94): for `P ∈ 𝒫`, `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control
matrix `G`. -/
theorem gain_iff_TF_le {P : Matrix K K ℝ} (hP : P.PosSemidef) (F : Matrix U K ℝ) :
    F = L.gain P ↔ ∀ G : Matrix U K ℝ, L.TF F P ≤ L.TF G P := by
  classical
  constructor
  · rintro rfl G
    rw [le_iff, posSemidef_iff_real]
    refine ⟨by rw [transpose_sub, L.TF_transpose _ hP, L.TF_transpose _ hP], fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg]
    exact (L.gain_isMinimizer hP x).1 _
  · intro h
    -- `xᵀT_F x ≤ xᵀT_{F(P)}x`, so `Fx` attains the minimum, hence `Fx = F(P)x`
    have hx : ∀ x, F *ᵥ x = L.gain P *ᵥ x := by
      intro x
      have h1 := (posSemidef_iff_real.1 (le_iff.1 (h (L.gain P)))).2 x
      rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg] at h1
      exact (L.gain_isMinimizer hP x).2 _ (le_antisymm h1 ((L.gain_isMinimizer hP x).1 _))
    ext i j
    have := congrFun (hx (Pi.single j 1)) i
    simpa [mulVec, dotProduct, Pi.single_apply] using this

end LQProblem

end SargentStachurski.AbstractDecisionProcesses
