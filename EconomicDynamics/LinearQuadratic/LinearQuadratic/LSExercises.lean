/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSInfiniteLimits
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Exercises 9.1 and 9.2

Miao, §9.7, p. 325.

* **Exercise 9.1** (`ex_9_1_loss`, `ex_9_1_transition`, `ex_9_1`): with
  `ũ_t = u_t + R⁻¹S'x_t` (the book prints `R⁻¹Sx_t`), `Q̃ = Q − SR⁻¹S'`, `Ã = A − BR⁻¹S'`, the
  problem becomes one with `S̃ = 0` (`normS`): the losses and transitions agree, the Riccati
  operators agree, `T̃ = T`, and the gains satisfy `F = F̃ + R⁻¹S'`. This is the normalisation
  `S = 0` used in §9.3 (p. 299).
* **Exercise 9.2** (`ex_9_2_transition`, `ex_9_2_loss`, `ex_9_2`): the uncentered problem, with
  loss the quadratic form of `[x_t − x*; u_t − u*]` in `[[Q, S], [S', R]]`, is the centered problem
  (`augment`) on the augmented state `z_t = [x_t − x*; 1]` with control `u_t − u*`; for `β < 1`
  and a positive semidefinite solution `P̃` of the augmented Riccati equation, the value function
  is `V(x) = −z'P̃z − d̃` and the optimal rule is `u = u* − F̃z`, uniquely.
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] [DecidableEq U] (L : LSProblem X U E)

/-! ### Exercise 9.1 -/

/-- The normalised problem of Exercise 9.1: `Ã = A − BR⁻¹S'`, `Q̃ = Q − SR⁻¹S'`, `S̃ = 0`. -/
noncomputable def normS : LSProblem X U E :=
  { L with A := L.A - L.B * (L.R⁻¹ * L.Sᵀ), Q := L.Q - L.S * (L.R⁻¹ * L.Sᵀ), S := 0 }

/-- **Exercise 9.1** (Miao, p. 325), the loss: `r(x, u) = x'Q̃x + ũ'Rũ` with `ũ = u + R⁻¹S'x`. -/
theorem ex_9_1_loss (hR : L.Rᵀ = L.R) (hu : IsUnit L.R.det) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u = L.normS.loss x (u + (L.R⁻¹ * L.Sᵀ) *ᵥ x) := by
  set K := L.R⁻¹ * L.Sᵀ
  have hRK : L.R *ᵥ (K *ᵥ x) = L.Sᵀ *ᵥ x := by
    rw [mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := SS.LQProblem.quad_add hR u (K *ᵥ x)
  have e2 : (K *ᵥ x) ⬝ᵥ (L.R *ᵥ u) = u ⬝ᵥ (L.Sᵀ *ᵥ x) := by
    rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hR, hRK]
  have e3 : (K *ᵥ x) ⬝ᵥ (L.R *ᵥ (K *ᵥ x)) = x ⬝ᵥ ((L.S * K) *ᵥ x) := by
    rw [hRK, ← dot_S_comm L.S x (K *ᵥ x), mulVec_mulVec]
  have e4 := dot_S_comm L.S x u
  simp only [loss, normS, sub_mulVec, dotProduct_sub, zero_mulVec, dotProduct_zero, mul_zero,
    add_zero]
  rw [e1, e2, e3, e4]
  ring

omit [DecidableEq U] in
/-- **Exercise 9.1**, the transition: `Ax + Bu = Ãx + Bũ`. -/
theorem ex_9_1_transition [DecidableEq U] (x : X → ℝ) (u : U → ℝ) :
    L.A *ᵥ x + L.B *ᵥ u = L.normS.A *ᵥ x + L.normS.B *ᵥ (u + (L.R⁻¹ * L.Sᵀ) *ᵥ x) := by
  simp only [normS, sub_mulVec, mulVec_add, mulVec_mulVec]
  abel

/-- **Exercise 9.1**: the normalisation leaves the Riccati operator unchanged, `T̃(P) = T(P)`,
and shifts the gain, `F(P) = F̃(P) + R⁻¹S'` (so `u = −Fx` iff `ũ = −F̃x`). -/
theorem ex_9_1 (hQ : L.Qᵀ = L.Q) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) :
    L.normS.T P = L.T P ∧ L.F P = L.normS.F P + L.R⁻¹ * L.Sᵀ := by
  classical
  set K := L.R⁻¹ * L.Sᵀ
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hRu : IsUnit L.R.det := (isUnit_iff_isUnit_det _).1 hR.isUnit
  have hG := L.G_posDef hR hP hβ
  have hGe : L.normS.G P = L.G P := rfl
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hq : ∀ v, 0 ≤ v ⬝ᵥ (L.G P *ᵥ v) := (SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2
  -- the two completed squares
  have key : ∀ x u, x ⬝ᵥ (L.T P *ᵥ x) + (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) =
      x ⬝ᵥ (L.normS.T P *ᵥ x) + (u + K *ᵥ x + L.normS.F P *ᵥ x) ⬝ᵥ
        (L.G P *ᵥ (u + K *ᵥ x + L.normS.F P *ᵥ x)) := by
    intro x u
    rw [← L.loss_add_cont hRs hPs hu, ← hGe, ← L.normS.loss_add_cont hRs hPs hu,
      ← L.ex_9_1_loss hRs hRu, ← L.ex_9_1_transition]
    rfl
  have hle : ∀ x, x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.normS.T P *ᵥ x) ∧
      L.F P *ᵥ x = L.normS.F P *ᵥ x + K *ᵥ x := by
    intro x
    have h1 := key x (-(L.F P *ᵥ x))
    have h2 := key x (-(L.normS.F P *ᵥ x) - K *ᵥ x)
    rw [neg_add_cancel, mulVec_zero, dotProduct_zero, add_zero] at h1
    rw [show -(L.normS.F P *ᵥ x) - K *ᵥ x + K *ᵥ x + L.normS.F P *ᵥ x = 0 by abel,
      mulVec_zero, dotProduct_zero, add_zero] at h2
    have hq1 := hq (-(L.F P *ᵥ x) + K *ᵥ x + L.normS.F P *ᵥ x)
    have hq2 := hq (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x)
    have heq : x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.normS.T P *ᵥ x) := by linarith
    refine ⟨heq, ?_⟩
    have h0 : (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x) ⬝ᵥ
        (L.G P *ᵥ (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x)) = 0 := by linarith
    by_contra hne
    have hv : -(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x ≠ 0 := by
      intro h0'
      apply hne
      rw [← sub_eq_zero, ← h0']
      abel
    have := (SS.LQProblem.posDef_iff_real.1 hG).2 hv
    linarith
  have hQs : L.normS.Qᵀ = L.normS.Q := by
    simp only [normS, transpose_sub, transpose_mul, transpose_nonsing_inv, transpose_transpose,
      hQ, hRs, Matrix.mul_assoc]
  refine ⟨SS.LQProblem.eq_of_dotProduct_mulVec_eq (L.normS.T_transpose hQs hRs hPs)
    (L.T_transpose hQ hRs hPs) fun x => ((hle x).1).symm, ?_⟩
  ext i j
  have := congrFun ((hle (Pi.single j 1)).2) i
  simpa [mulVec_single_one] using this

/-! ### Exercise 9.2 -/

/-- The augmented problem of Exercise 9.2 on the state `z = [x − x*; 1]` with control `u − u*`:
`Ã = [[A, Ax* + Bu* − x*], [0, 1]]`, `B̃ = [B; 0]`, `C̃ = [C; 0]`, `Q̃ = [[Q, 0], [0, 0]]`,
`S̃ = [S; 0]`. -/
noncomputable def augment (xs : X → ℝ) (us : U → ℝ) : LSProblem (X ⊕ Unit) U E where
  A := fromBlocks L.A (Matrix.of fun i _ => (L.A *ᵥ xs + L.B *ᵥ us - xs) i) 0 1
  B := fromRows L.B 0
  C := fromRows L.C 0
  Q := fromBlocks L.Q 0 0 0
  R := L.R
  S := fromRows L.S 0
  β := L.β

/-- The augmented state `z = [x − x*; 1]`. -/
def ls_aug (xs x : X → ℝ) : X ⊕ Unit → ℝ := Sum.elim (x - xs) fun _ => 1

omit [DecidableEq U] in
/-- **Exercise 9.2** (Miao, p. 325): (9.57) in the augmented state,
`z_{t+1} = Ãz_t + B̃(u_t − u*) + C̃ε_{t+1}`. -/
theorem ex_9_2_transition [Fintype E] (xs : X → ℝ) (us : U → ℝ) (x : X → ℝ)
    (u : U → ℝ) (e : E → ℝ) :
    ls_aug xs (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) =
      (L.augment xs us).A *ᵥ ls_aug xs x + (L.augment xs us).B *ᵥ (u - us) +
        (L.augment xs us).C *ᵥ e := by
  funext i
  rcases i with i | i
  · simp only [augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, Pi.add_apply,
      Sum.elim_inl, Pi.sub_apply, mulVec_sub, Function.comp_def]
    simp only [mulVec, dotProduct, of_apply, Fintype.univ_unit, Finset.sum_singleton,
      Sum.elim_inr, mul_one]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, mulVec, dotProduct]

omit [DecidableEq U] in
/-- **Exercise 9.2**: the uncentered loss, the quadratic form of `[x − x*; u − u*]` in
`[[Q, S], [S', R]]`, is the centered loss of the augmented problem. -/
theorem ex_9_2_loss (xs : X → ℝ) (us : U → ℝ) (x : X → ℝ) (u : U → ℝ) :
    Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ Sum.elim (x - xs) (u - us)) =
      (L.augment xs us).loss (ls_aug xs x) (u - us) := by
  rw [L.quad_joint]
  simp only [loss, augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, sumElim_dotProduct_sumElim, zero_mulVec, add_zero, dotProduct_zero]

/-- **Exercise 9.2**: for `0 ≤ β < 1`, if `P̃ ≥ 0` solves the augmented Riccati equation, then
`V(x) = −z'P̃z − d̃` (`z = [x − x*; 1]`, `d̃ = (1 − β)⁻¹β tr(P̃C̃C̃')`) solves the Bellman equation
of the uncentered problem, and the maximum is attained exactly at `u = u* − F̃z`. -/
theorem ex_9_2 [Fintype E] [DecidableEq E] {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hR : L.R.PosDef) (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) (xs : X → ℝ) (us : U → ℝ)
    {P : Matrix (X ⊕ Unit) (X ⊕ Unit) ℝ} (hP : P.PosSemidef) (hfix : (L.augment xs us).T P = P)
    (x : X → ℝ) :
    let d := (1 - L.β)⁻¹ * (L.β * trace (P * (L.augment xs us).C * (L.augment xs us).Cᵀ))
    let V := fun x' : X → ℝ => -(ls_aug xs x' ⬝ᵥ (P *ᵥ ls_aug xs x')) - d
    IsGreatest (Set.range fun u : U → ℝ =>
        -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
          Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν)
        (V x) ∧
      ∀ u, -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
          Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν =
          V x ↔ u = us - (L.augment xs us).F P *ᵥ ls_aug xs x := by
  intro d V
  set La := L.augment xs us
  have hobj : ∀ u : U → ℝ, -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
      Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν =
      La.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) (ls_aug xs x) (u - us) := by
    intro u
    rw [L.ex_9_2_loss, bellObj]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun e => ?_)
    simp only [V]
    rw [L.ex_9_2_transition xs us x u e]
  have h := La.eq_9_16_9_17 hν hR hβ0 hβ1 hP hfix (ls_aug xs x)
  simp only [hobj]
  have hsurj : Function.Surjective fun u : U → ℝ => u - us := fun v => ⟨v + us, by simp⟩
  refine ⟨?_, fun u => ?_⟩
  · have := hsurj.range_comp (La.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) (ls_aug xs x))
    simp only [Function.comp_def] at this
    rw [this]
    exact h.1
  · refine (h.2 (u - us)).trans ?_
    rw [sub_eq_iff_eq_add, neg_add_eq_sub]

end LSProblem

end Miao.LinearQuadratic
