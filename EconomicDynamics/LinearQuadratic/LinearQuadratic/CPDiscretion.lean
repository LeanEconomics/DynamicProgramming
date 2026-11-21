/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.CPRamsey
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Optimal discretionary policy: Markov perfect equilibrium in linear rules

Miao, §9.5, pp. 311–315. The system (9.18) with `C = I`, `D = [I 0; D₂₁ D₂₂]`, partitioned as
`z_{t+1} = A_zz z_t + A_zy y_t + B_z u_t + ε_{t+1}` and
`D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = A_yz z_t + A_yy y_t + B_y u_t`, with `Cov(ε) = Σ`, the loss
(9.19) and linear rules `y_t = Mz_t`, `u_t = −Fz_t` (9.30). The model data are bundled in
`CPDisc`.

* `cp_disc_loss_eq` (p. 313): the loss written blockwise (Step 2, first line) is (9.19).
* `cp_expected_quadratic` (pp. 312–314): for a mean-zero shock with covariance `Σ`,
  `E[½(m + ε)'V(m + ε) + ½v] = ½m'Vm + ½tr(VΣ) + ½v`; this is how `E_t J_{t+1}(z_{t+1})`
  enters (9.39) and gives `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`.
* Step 1: `eq_9_35_36` (the private sector's expectations `E_t y_{t+1} = M_{t+1}E_t z_{t+1}`
  in the lower block of (9.18)), `eq_9_37` (with `G = D₂₁ + D₂₂M_{t+1}` and
  `A_yy − GA_zy` invertible, the constraint holds iff `y_t = H_z z_t + H_u u_t`), `eq_9_38`
  (`z_{t+1} = A*z_t + B*u_t + ε_{t+1}`).
* Step 2: `eq_step2` (the loss is `½z'Q*z + ½u'R*u + z'S*u` with the corrected `Q*, R*, S*`).
* Step 3: `cp_obj_complete_square` and `eq_9_40` (`u = −Fz` is the unique minimiser of (9.39)
  when `R* + βB*'VB*` is positive definite), `eq_9_41` (the minimised value is
  `½z'V_t z + ½v_t` with the book's (9.41) and `v_t = β tr(VΣ) + βv`), `eq_9_42`
  (`y_t = (H_z − H_uF)z_t`).
* `cp_bellman_step` (9.33): one step of the backward induction — given `(V_{t+1}, v_{t+1},
  M_{t+1})`, the pair `(M_t z, −F_t z)` is the unique minimiser of the period-`t` Bellman
  problem over all `(y, u)` satisfying the constraint, with value `J_t(z) = ½z'V_t z + ½v_t`.
* `definition_9_5_1` (`IsMPE`) and `cp_mpe_of_fixed_point`: a fixed point `(V, v, M)` of the
  Step 1–3 map gives a Markov perfect equilibrium `(M, F)` with `J(z) = ½z'Vz + ½v`.

**Corrections.**
* (9.36) omits `D₂₁E_t z_{t+1}`: the lower block of (9.18) is
  `D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = …`, so `D_yy M_{t+1}` in `H_zt`, `H_ut` must be
  `G = D₂₁ + D₂₂M_{t+1}`; the book's formulas are right only when `D₂₁ = 0`
  (`eq_9_37_book`, counterexample `eq_9_36_false`). (9.35) also takes `C = I`.
* Step 2: the printed `S*_t = Q_zy H_ut + S_z + H_zt S_y` lacks the transpose (`H_zt'S_y`) and
  the cross term `H_zt'Q_yy H_ut`; the printed `R*_t = R + H_ut'Q_yy H_ut + H_ut'S_y` lacks a
  factor 2 on `H_ut'S_y` (symmetrised: `H_ut'S_y + S_y'H_ut`). Counterexamples:
  `step2_book_S_false`, `step2_book_R_false`. The printed `Q*_t` (with `2Q_zy H_zt`) is right
  as a quadratic form (`cp_Qbook_quad`), but not symmetric; we use the symmetric
  `Q_zy H_zt + H_zt'Q_zy'`.
* (9.41) is right as a quadratic form (`eq_9_41`) but the matrix it defines is not symmetric
  (`−2S*F`); the gain formula (9.40) at the next step presumes `V_{t+1}` symmetric, so the
  iteration must use the symmetrised `cpVnext` (`cp_Vnext_quad`, `cp_Vnext_symm`).
* Definition 9.5.1 (i) speaks of `E_t y_{t+1} = f(z_t)` taken as given; the derivation that
  follows (9.32)–(9.33) has the policymaker take the private sector's *rule* `y_{t+1} =
  M_{t+1}z_{t+1}` as given, so that `u_t` affects `E_t y_{t+1}` through `E_t z_{t+1}`. We
  formalise the definition in the form the derivation uses: the constraint set is
  `G(A_zz z + A_zy y + B_z u) = A_yz z + A_yy y + B_y u`, `G = D₂₁ + D₂₂M` (which is (i)–(ii)
  with `f(z_t) = ME_t z_{t+1}`).
* Convergence of the iteration ("iterating this process until convergence") is not proved in
  the book and is not formalised; `cp_mpe_of_fixed_point` proves that a limit that is a fixed
  point is an equilibrium.
-/

namespace Miao.LinearQuadratic

open scoped Matrix
open MeasureTheory

/-! ### Bilinear-form identities -/

/-- `(Hv)'(Mw) = v'(H'M)w`. -/
theorem cp_dot_left {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (H : Matrix α β ℝ)
    (M : Matrix α γ ℝ) (v : β → ℝ) (w : γ → ℝ) :
    (H *ᵥ v) ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ ((Hᵀ * M) *ᵥ w) := by
  calc (H *ᵥ v) ⬝ᵥ (M *ᵥ w) = (M *ᵥ w) ⬝ᵥ (H *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (Hᵀ *ᵥ (M *ᵥ w)) := cp_dotProduct_mulVec_comm H (M *ᵥ w) v
    _ = v ⬝ᵥ ((Hᵀ * M) *ᵥ w) := by rw [Matrix.mulVec_mulVec]

/-- `v'M'v = v'Mv`. -/
theorem cp_quad_transpose {α : Type*} [Fintype α] (M : Matrix α α ℝ) (v : α → ℝ) :
    v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
  rw [cp_dotProduct_mulVec_comm Mᵀ, Matrix.transpose_transpose]

/-- `u'Nz = z'N'u`. -/
theorem cp_dot_swap {α β : Type*} [Fintype α] [Fintype β] (N : Matrix α β ℝ) (u : α → ℝ)
    (z : β → ℝ) : u ⬝ᵥ (N *ᵥ z) = z ⬝ᵥ (Nᵀ *ᵥ u) :=
  cp_dotProduct_mulVec_comm N u z

/-! ### The model -/

/-- The data of §9.5 (Miao, pp. 311–313): the blocks of `A`, `B`, `D` in (9.18) (with `C = I`),
the blocks of the loss (9.19), the discount factor and the shock covariance `Σ`. -/
structure CPDisc (Z Y U : Type*) where
  /-- `A_zz` -/
  Azz : Matrix Z Z ℝ
  /-- `A_zy` -/
  Azy : Matrix Z Y ℝ
  /-- `A_yz` -/
  Ayz : Matrix Y Z ℝ
  /-- `A_yy` -/
  Ayy : Matrix Y Y ℝ
  /-- `B_z` -/
  Bz : Matrix Z U ℝ
  /-- `B_y` -/
  By : Matrix Y U ℝ
  /-- `D₂₁` -/
  D21 : Matrix Y Z ℝ
  /-- `D₂₂` (the book's `D_yy`) -/
  D22 : Matrix Y Y ℝ
  /-- `Q_zz` -/
  Qzz : Matrix Z Z ℝ
  /-- `Q_zy` -/
  Qzy : Matrix Z Y ℝ
  /-- `Q_yy` -/
  Qyy : Matrix Y Y ℝ
  /-- `R` -/
  R : Matrix U U ℝ
  /-- `S_z` -/
  Sz : Matrix Z U ℝ
  /-- `S_y` -/
  Sy : Matrix Y U ℝ
  /-- the discount factor -/
  β : ℝ
  /-- the covariance matrix `Σ` of `ε` -/
  Sig : Matrix Z Z ℝ

variable {Z Y U : Type*} [Fintype Z] [Fintype Y] [Fintype U]

namespace CPDisc

/-- The period loss in block form (Miao, p. 313, Step 2). -/
noncomputable def loss (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (z ⬝ᵥ (P.Qzz *ᵥ z)) + (1 / 2) * (y ⬝ᵥ (P.Qyy *ᵥ y)) + z ⬝ᵥ (P.Qzy *ᵥ y) +
    (1 / 2) * (u ⬝ᵥ (P.R *ᵥ u)) + z ⬝ᵥ (P.Sz *ᵥ u) + y ⬝ᵥ (P.Sy *ᵥ u)

/-- `E_t z_{t+1} = A_zz z + A_zy y + B_z u`. -/
def mean (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : Z → ℝ :=
  P.Azz *ᵥ z + P.Azy *ᵥ y + P.Bz *ᵥ u

/-- `G = D₂₁ + D₂₂M`: the coefficient of `E_t z_{t+1}` in the lower block of (9.18) once the
public expects `y_{t+1} = Mz_{t+1}`. -/
def G (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Z ℝ := P.D21 + P.D22 * M

/-- The constraint on `(y_t, u_t)` (Miao, (9.36) as corrected):
`G(A_zz z + A_zy y + B_z u) = A_yz z + A_yy y + B_y u`. -/
def Feasible (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : Prop :=
  P.G M *ᵥ P.mean z y u = P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u

/-- `A_yy − GA_zy`. -/
def K (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Y ℝ := P.Ayy - P.G M * P.Azy

/-- `H_zt = (A_yy − GA_zy)⁻¹(GA_zz − A_yz)` (Miao, p. 313, with `G = D₂₁ + D₂₂M_{t+1}`). -/
noncomputable def Hz [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Z ℝ :=
  (P.K M)⁻¹ * (P.G M * P.Azz - P.Ayz)

/-- `H_ut = (A_yy − GA_zy)⁻¹(GB_z − B_y)` (Miao, p. 313). -/
noncomputable def Hu [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y U ℝ :=
  (P.K M)⁻¹ * (P.G M * P.Bz - P.By)

/-- `A* = A_zz + A_zy H_z`. -/
def Ast (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ := P.Azz + P.Azy * Hz

/-- `B* = B_z + A_zy H_u`. -/
def Bst (P : CPDisc Z Y U) (Hu : Matrix Y U ℝ) : Matrix Z U ℝ := P.Bz + P.Azy * Hu

/-- `Q* = Q_zz + H_z'Q_yy H_z + Q_zy H_z + H_z'Q_zy'` (symmetric form of the book's
`Q_zz + H_z'Q_yy H_z + 2Q_zy H_z`). -/
def Qst (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  P.Qzz + Hzᵀ * P.Qyy * Hz + P.Qzy * Hz + Hzᵀ * P.Qzyᵀ

/-- `R* = R + H_u'Q_yy H_u + H_u'S_y + S_y'H_u` (corrected). -/
def Rst (P : CPDisc Z Y U) (Hu : Matrix Y U ℝ) : Matrix U U ℝ :=
  P.R + Huᵀ * P.Qyy * Hu + Huᵀ * P.Sy + P.Syᵀ * Hu

/-- `S* = Q_zy H_u + S_z + H_z'S_y + H_z'Q_yy H_u` (corrected). -/
def Sst (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) : Matrix Z U ℝ :=
  P.Qzy * Hu + P.Sz + Hzᵀ * P.Sy + Hzᵀ * P.Qyy * Hu

end CPDisc

/-- Miao, p. 313 (Step 2, first line): the blockwise loss is (9.19) with
`Q = [Q_zz Q_zy; Q_zy' Q_yy]` and `S = [S_z; S_y]`. -/
theorem cp_disc_loss_eq (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) :
    P.loss z y u = cpLoss (Matrix.fromBlocks P.Qzz P.Qzy P.Qzyᵀ P.Qyy) (Matrix.fromRows P.Sz P.Sy)
      P.R (Sum.elim z y) u := by
  simp only [CPDisc.loss, cpLoss, Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, cp_sumElim_dotProduct, dotProduct_add]
  rw [cp_dotProduct_mulVec_comm P.Qzyᵀ y z, Matrix.transpose_transpose]
  ring

/-! ### The expected continuation value -/

/-- Miao, pp. 312–314: for a probability measure `ν` of the shock `ε` with mean zero and
covariance `Σ` (`∫εᵢεⱼ = Σᵢⱼ`), `E[½(m + ε)'V(m + ε) + ½v] = ½m'Vm + ½tr(VΣ) + ½v`. -/
theorem cp_expected_quadratic (ν : Measure (Z → ℝ)) [IsProbabilityMeasure ν]
    (Sig V : Matrix Z Z ℝ) (m : Z → ℝ) (v : ℝ)
    (hint1 : ∀ i, Integrable (fun e : Z → ℝ => e i) ν)
    (hint2 : ∀ i j, Integrable (fun e : Z → ℝ => e i * e j) ν)
    (hmean : ∀ i, ∫ e, e i ∂ν = 0) (hcov : ∀ i j, ∫ e, e i * e j ∂ν = Sig i j) :
    ∫ e, ((1 / 2) * ((m + e) ⬝ᵥ (V *ᵥ (m + e))) + (1 / 2) * v) ∂ν =
      (1 / 2) * (m ⬝ᵥ (V *ᵥ m)) + (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v := by
  have hterm : ∀ i j, (fun e : Z → ℝ => (m + e) i * (V i j * (m + e) j)) =
      fun e => m i * V i j * m j + (m i * V i j) * e j + (V i j * m j) * e i +
        V i j * (e i * e j) := fun i j => by
    funext e
    simp only [Pi.add_apply]
    ring
  have hint : ∀ i j, Integrable (fun e : Z → ℝ => (m + e) i * (V i j * (m + e) j)) ν :=
    fun i j => by
      rw [hterm]
      exact (((integrable_const _).add ((hint1 j).const_mul _)).add
        ((hint1 i).const_mul _)).add ((hint2 i j).const_mul _)
  have hval : ∀ i j, ∫ e, (m + e) i * (V i j * (m + e) j) ∂ν = m i * V i j * m j +
      V i j * Sig i j := fun i j => by
    have i1 : Integrable (fun _ : Z → ℝ => m i * V i j * m j) ν := integrable_const _
    have i2 : Integrable (fun e : Z → ℝ => m i * V i j * e j) ν := (hint1 j).const_mul _
    have i3 : Integrable (fun e : Z → ℝ => V i j * m j * e i) ν := (hint1 i).const_mul _
    have i4 : Integrable (fun e : Z → ℝ => V i j * (e i * e j)) ν := (hint2 i j).const_mul _
    have i12 : Integrable (fun e : Z → ℝ => m i * V i j * m j + m i * V i j * e j) ν :=
      i1.add i2
    have i123 : Integrable (fun e : Z → ℝ => m i * V i j * m j + m i * V i j * e j +
        V i j * m j * e i) ν := i12.add i3
    rw [hterm, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul, hmean, hmean, hcov]
    simp
  have hsym : ∀ i j, Sig i j = Sig j i := fun i j => by
    rw [← hcov, ← hcov]
    simp_rw [mul_comm]
  have hdot : (fun e : Z → ℝ => (1 / 2) * ((m + e) ⬝ᵥ (V *ᵥ (m + e))) + (1 / 2) * v) =
      fun e => (1 / 2) * ∑ i, ∑ j, (m + e) i * (V i j * (m + e) j) + (1 / 2) * v := by
    funext e
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hiint : ∀ i, Integrable (fun e : Z → ℝ => ∑ j, (m + e) i * (V i j * (m + e) j)) ν :=
    fun i => integrable_finsetSum _ fun j _ => hint i j
  have hq : m ⬝ᵥ (V *ᵥ m) = ∑ i, ∑ j, m i * V i j * m j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have htr : Matrix.trace (V * Sig) = ∑ i, ∑ j, V i j * Sig i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  have hint' : Integrable (fun e : Z → ℝ => ∑ i, ∑ j, (m + e) i * (V i j * (m + e) j)) ν :=
    integrable_finsetSum _ fun i _ => hiint i
  rw [hdot, integral_add (hint'.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ fun i _ => hiint i, integral_const]
  simp only [fun i => integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => hint i j, hval,
    Finset.sum_add_distrib, probReal_univ, one_smul, hq, htr]
  ring

/-! ### Step 1 -/

/-- Miao, (9.35)–(9.36), p. 312: if the public expects `y_{t+1} = Mz_{t+1}` and
`E_t z_{t+1} = A_zz z + A_zy y + B_z u` (the upper block of (9.18), `E_tε_{t+1} = 0`), the
lower block `D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = A_yz z + A_yy y + B_y u` is the constraint
`Feasible`. -/
theorem eq_9_35_36 (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ)
    (Ez' : Z → ℝ) (Ey' : Y → ℝ) (hz : Ez' = P.mean z y u) (hy : Ey' = M *ᵥ Ez') :
    (P.D21 *ᵥ Ez' + P.D22 *ᵥ Ey' = P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u) ↔
      P.Feasible M z y u := by
  rw [CPDisc.Feasible, CPDisc.G, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← hz, ← hy]

/-- Miao, (9.37), p. 313 (with `G = D₂₁ + D₂₂M_{t+1}`): if `A_yy − GA_zy` is invertible, the
constraint holds iff `y_t = H_z z_t + H_u u_t`. -/
theorem eq_9_37 [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ)
    (hK : IsUnit (P.K M).det) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) :
    P.Feasible M z y u ↔ y = P.Hz M *ᵥ z + P.Hu M *ᵥ u := by
  have key : P.K M *ᵥ y - ((P.G M * P.Azz - P.Ayz) *ᵥ z + (P.G M * P.Bz - P.By) *ᵥ u) =
      (P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u) - P.G M *ᵥ P.mean z y u := by
    simp only [CPDisc.K, CPDisc.mean, Matrix.sub_mulVec, Matrix.mulVec_add,
      ← Matrix.mulVec_mulVec]
    abel
  have h1 : P.Feasible M z y u ↔
      P.K M *ᵥ y = (P.G M * P.Azz - P.Ayz) *ᵥ z + (P.G M * P.Bz - P.By) *ᵥ u := by
    rw [CPDisc.Feasible]
    constructor
    · intro h
      rw [h, sub_self] at key
      exact sub_eq_zero.1 key
    · intro h
      rw [h, sub_self] at key
      exact (sub_eq_zero.1 key.symm).symm
  rw [h1, CPDisc.Hz, CPDisc.Hu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_add]
  constructor
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hK, Matrix.one_mulVec]
  · intro h
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hK, Matrix.one_mulVec]

omit [Fintype U] in
/-- Miao, p. 313: when `D₂₁ = 0`, `H_z` and `H_u` are the book's
`(A_yy − D_yy M A_zy)⁻¹(D_yy M A_zz − A_yz)` and `(A_yy − D_yy M A_zy)⁻¹(D_yy M B_z − B_y)`. -/
theorem eq_9_37_book [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (h21 : P.D21 = 0) :
    P.Hz M = (P.Ayy - P.D22 * M * P.Azy)⁻¹ * (P.D22 * M * P.Azz - P.Ayz) ∧
      P.Hu M = (P.Ayy - P.D22 * M * P.Azy)⁻¹ * (P.D22 * M * P.Bz - P.By) := by
  simp only [CPDisc.Hz, CPDisc.Hu, CPDisc.K, CPDisc.G, h21, zero_add, and_self]

/-- The data of the counterexample to (9.36): `D₂₁ = D₂₂ = A_zz = A_yy = 1`, all else zero. -/
def cpDiscEx : CPDisc (Fin 1) (Fin 1) (Fin 1) where
  Azz := 1
  Azy := 0
  Ayz := 0
  Ayy := 1
  Bz := 0
  By := 0
  D21 := 1
  D22 := 1
  Qzz := 0
  Qzy := 0
  Qyy := 0
  R := 0
  Sz := 0
  Sy := 0
  β := 0
  Sig := 0

/-- Correction to (9.36) (Miao, p. 312): dropping `D₂₁E_t z_{t+1}` is wrong when `D₂₁ ≠ 0`. With
`cpDiscEx` and `M = 0`, the book's rule `y = (A_yy − D_yy M A_zy)⁻¹(D_yy M A_zz − A_yz)z +
(A_yy − D_yy M A_zy)⁻¹(D_yy M B_z − B_y)u` gives `y = 0` at `z = u = 1`, which violates the
constraint, while `y = 1` satisfies it. -/
theorem eq_9_36_false :
    let P := cpDiscEx
    let O : Matrix (Fin 1) (Fin 1) ℝ := 0
    let ybook := ((P.Ayy - P.D22 * O * P.Azy)⁻¹ * (P.D22 * O * P.Azz - P.Ayz)) *ᵥ (fun _ => 1) +
      ((P.Ayy - P.D22 * O * P.Azy)⁻¹ * (P.D22 * O * P.Bz - P.By)) *ᵥ (fun _ => 1)
    ¬ P.Feasible O (fun _ => 1) ybook (fun _ => 1) ∧ P.Feasible O (fun _ => 1) (fun _ => 1)
      (fun _ => 1) := by
  intro P O ybook
  have hy : ybook = 0 := by
    funext i
    simp [ybook, P, O, cpDiscEx]
  refine ⟨?_, ?_⟩
  · rw [hy]
    intro h
    have := congrFun h 0
    simp [P, O, cpDiscEx, CPDisc.mean, CPDisc.G, Matrix.mulVec, dotProduct] at this
  · funext i
    fin_cases i
    simp [P, O, cpDiscEx, CPDisc.mean, CPDisc.G, Matrix.mulVec, dotProduct]

/-- Miao, (9.38), p. 313: substituting `y = H_z z + H_u u` into the upper block,
`E_t z_{t+1} = A*z + B*u`. -/
theorem eq_9_38 (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) (z : Z → ℝ)
    (u : U → ℝ) : P.mean z (Hz *ᵥ z + Hu *ᵥ u) u = P.Ast Hz *ᵥ z + P.Bst Hu *ᵥ u := by
  simp only [CPDisc.mean, CPDisc.Ast, CPDisc.Bst, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

/-! ### Step 2 -/

/-- Miao, p. 313 (Step 2, as corrected): with `Q_yy` symmetric and `y = H_z z + H_u u`, the
loss is `½z'Q*z + ½u'R*u + z'S*u`. -/
theorem eq_step2 (P : CPDisc Z Y U) (hQ : P.Qyyᵀ = P.Qyy) (Hz : Matrix Y Z ℝ)
    (Hu : Matrix Y U ℝ) (z : Z → ℝ) (u : U → ℝ) :
    P.loss z (Hz *ᵥ z + Hu *ᵥ u) u = (1 / 2) * (z ⬝ᵥ (P.Qst Hz *ᵥ z)) +
      (1 / 2) * (u ⬝ᵥ (P.Rst Hu *ᵥ u)) + z ⬝ᵥ (P.Sst Hz Hu *ᵥ u) := by
  have e1 : u ⬝ᵥ ((Huᵀ * (P.Qyy * Hz)) *ᵥ z) = z ⬝ᵥ ((Hzᵀ * (P.Qyy * Hu)) *ᵥ u) := by
    rw [cp_dot_swap]
    congr 2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ,
      Matrix.mul_assoc]
  have e2 : z ⬝ᵥ ((Hzᵀ * P.Qzyᵀ) *ᵥ z) = z ⬝ᵥ ((P.Qzy * Hz) *ᵥ z) := by
    rw [← cp_quad_transpose (P.Qzy * Hz), Matrix.transpose_mul]
  have e3 : u ⬝ᵥ ((P.Syᵀ * Hu) *ᵥ u) = u ⬝ᵥ ((Huᵀ * P.Sy) *ᵥ u) := by
    rw [← cp_quad_transpose (Huᵀ * P.Sy), Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [CPDisc.loss, CPDisc.Qst, CPDisc.Rst, CPDisc.Sst, Matrix.add_mulVec,
    Matrix.mulVec_add, dotProduct_add, add_dotProduct, cp_dot_left, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
  rw [e1, e2, e3]
  ring

/-- The book's `Q*_t = Q_zz + H_z'Q_yy H_z + 2Q_zy H_z` (Miao, p. 313). -/
def CPDisc.Qbook (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  P.Qzz + Hzᵀ * P.Qyy * Hz + (2 : ℝ) • (P.Qzy * Hz)

omit [Fintype U] in
/-- Miao, p. 313: the book's `Q*` has the same quadratic form as the symmetric `Q*`. -/
theorem cp_Qbook_quad (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (z : Z → ℝ) :
    z ⬝ᵥ (P.Qbook Hz *ᵥ z) = z ⬝ᵥ (P.Qst Hz *ᵥ z) := by
  have e2 : z ⬝ᵥ ((Hzᵀ * P.Qzyᵀ) *ᵥ z) = z ⬝ᵥ ((P.Qzy * Hz) *ᵥ z) := by
    rw [← cp_quad_transpose (P.Qzy * Hz), Matrix.transpose_mul]
  simp only [CPDisc.Qbook, CPDisc.Qst, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, e2, smul_eq_mul]
  ring

/-- The printed data of the Step 2 counterexamples, `Q_yy` and `S_y` free. -/
def cpDiscEx2 (qyy sy : ℝ) : CPDisc (Fin 1) (Fin 1) (Fin 1) where
  Azz := 0
  Azy := 0
  Ayz := 0
  Ayy := 0
  Bz := 0
  By := 0
  D21 := 0
  D22 := 0
  Qzz := 0
  Qzy := 0
  Qyy := Matrix.of fun _ _ => qyy
  R := 0
  Sz := 0
  Sy := Matrix.of fun _ _ => sy
  β := 0
  Sig := 0

/-- Correction to Step 2 (Miao, p. 313): the printed `S* = Q_zy H_u + S_z + H_z'S_y` misses
`H_z'Q_yy H_u`. With `Q_yy = 1`, `H_z = H_u = 1`, all else zero, at `z = u = 1` the loss is `2`
but the printed `½z'Q*z + ½u'R*u + z'S*u` is `1`. -/
theorem step2_book_S_false :
    let P := cpDiscEx2 1 0
    let H : Matrix (Fin 1) (Fin 1) ℝ := 1
    let o : Fin 1 → ℝ := fun _ => 1
    P.loss o (H *ᵥ o + H *ᵥ o) o = 2 ∧
      (1 / 2) * (o ⬝ᵥ (P.Qbook H *ᵥ o)) +
        (1 / 2) * (o ⬝ᵥ ((P.R + Hᵀ * P.Qyy * H + Hᵀ * P.Sy) *ᵥ o)) +
        o ⬝ᵥ ((P.Qzy * H + P.Sz + Hᵀ * P.Sy) *ᵥ o) = 1 := by
  intro P H o
  constructor
  · simp [P, H, o, cpDiscEx2, CPDisc.loss, Matrix.mulVec, dotProduct]
    norm_num
  · simp [P, H, o, cpDiscEx2, CPDisc.Qbook, Matrix.mulVec, dotProduct]
    norm_num

/-- Correction to Step 2 (Miao, p. 313): the printed `R* = R + H_u'Q_yy H_u + H_u'S_y` misses a
factor 2 on `H_u'S_y`. With `S_y = 1`, `H_z = 0`, `H_u = 1`, all else zero, at `z = 0`, `u = 1`
the loss is `1` but the printed form gives `½`. -/
theorem step2_book_R_false :
    let P := cpDiscEx2 0 1
    let Hu : Matrix (Fin 1) (Fin 1) ℝ := 1
    let o : Fin 1 → ℝ := fun _ => 1
    P.loss 0 (Hu *ᵥ o) o = 1 ∧
      (1 / 2) * ((0 : Fin 1 → ℝ) ⬝ᵥ (P.Qbook 0 *ᵥ 0)) +
        (1 / 2) * (o ⬝ᵥ ((P.R + Huᵀ * P.Qyy * Hu + Huᵀ * P.Sy) *ᵥ o)) +
        (0 : Fin 1 → ℝ) ⬝ᵥ ((P.Qzy * Hu + P.Sz) *ᵥ o) = 1 / 2 := by
  intro P Hu o
  constructor
  · simp [P, Hu, o, cpDiscEx2, CPDisc.loss, Matrix.mulVec, dotProduct]
  · simp [P, Hu, o, cpDiscEx2, Matrix.mulVec, dotProduct]

/-! ### Step 3 -/

/-- The objective of (9.39) (Miao, p. 314), with `E_t J_{t+1}(z_{t+1})` evaluated by
`cp_expected_quadratic`: `½z'Q*z + ½u'R*u + z'S*u + β[½m'Vm + ½tr(VΣ) + ½v]`,
`m = A*z + B*u`. -/
noncomputable def cpObj (β : ℝ) (Sig : Matrix Z Z ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ)
    (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (v : ℝ)
    (z : Z → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (z ⬝ᵥ (Qs *ᵥ z)) + (1 / 2) * (u ⬝ᵥ (Rs *ᵥ u)) + z ⬝ᵥ (Ss *ᵥ u) +
    β * ((1 / 2) * ((As *ᵥ z + Bs *ᵥ u) ⬝ᵥ (V *ᵥ (As *ᵥ z + Bs *ᵥ u))) +
      (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v)

/-- `R* + βB*'VB*`. -/
def cpGain (β : ℝ) (Rs : Matrix U U ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) :
    Matrix U U ℝ :=
  Rs + β • (Bsᵀ * V * Bs)

/-- `F = (R* + βB*'VB*)⁻¹(S*' + βB*'VA*)` (Miao, (9.40), p. 314). -/
noncomputable def cpF [DecidableEq U] (β : ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) : Matrix U Z ℝ :=
  (cpGain β Rs Bs V)⁻¹ * (Ssᵀ + β • (Bsᵀ * V * As))

/-- The objective (9.39) is `½u'Gu + u'(S*' + βB*'VA*)z + c(z)`, `G = R* + βB*'VB*`. -/
theorem cp_obj_expand {β : ℝ} (Sig Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (v : ℝ)
    (z : Z → ℝ) (u : U → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z u =
      (1 / 2) * (u ⬝ᵥ (cpGain β Rs Bs V *ᵥ u)) + u ⬝ᵥ ((Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z) +
        ((1 / 2) * (z ⬝ᵥ (Qs *ᵥ z)) + β * ((1 / 2) * ((As *ᵥ z) ⬝ᵥ (V *ᵥ (As *ᵥ z))) +
          (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v)) := by
  have e1 : (As *ᵥ z) ⬝ᵥ (V *ᵥ (Bs *ᵥ u)) = (Bs *ᵥ u) ⬝ᵥ (V *ᵥ (As *ᵥ z)) := by
    rw [cp_dotProduct_mulVec_comm, hV, dotProduct_comm]
  have e2 : z ⬝ᵥ (Ss *ᵥ u) = u ⬝ᵥ (Ssᵀ *ᵥ z) := cp_dot_swap Ss z u
  simp only [cpObj, cpGain, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_eq_mul, e1, e2]
  rw [cp_dot_left Bs V u (Bs *ᵥ u), cp_dot_left Bs V u (As *ᵥ z)]
  simp only [Matrix.mulVec_mulVec]
  ring

/-- **Completing the square in (9.39)** (Miao, p. 314). With `V`, `R*` symmetric and
`G = R* + βB*'VB*` invertible, the objective is `obj(u) = obj(−Fz) + ½(u + Fz)'G(u + Fz)`. -/
theorem cp_obj_complete_square [DecidableEq U] {β : ℝ} (Sig Qs : Matrix Z Z ℝ)
    {Rs : Matrix U U ℝ} (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ)
    (Bs : Matrix Z U ℝ) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (hG : IsUnit (cpGain β Rs Bs V).det)
    (v : ℝ) (z : Z → ℝ) (u : U → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z u =
      cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) +
        (1 / 2) * ((u + cpF β Rs Ss As Bs V *ᵥ z) ⬝ᵥ
          (cpGain β Rs Bs V *ᵥ (u + cpF β Rs Ss As Bs V *ᵥ z))) := by
  set G := cpGain β Rs Bs V with hGdef
  set w := cpF β Rs Ss As Bs V *ᵥ z
  have hGs : Gᵀ = G := by
    rw [hGdef, cpGain, Matrix.transpose_add, Matrix.transpose_smul, hR, Matrix.transpose_mul,
      Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hGw : G *ᵥ w = (Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z := by
    simp only [w, cpF, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hGdef,
      Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hwu : w ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ ((Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z) := by
    rw [cp_dotProduct_mulVec_symm hGs, dotProduct_comm, hGw]
  rw [cp_obj_expand Sig Qs Rs Ss As Bs hV v z u, cp_obj_expand Sig Qs Rs Ss As Bs hV v z (-w)]
  simp only [← hGdef, Matrix.mulVec_neg, Matrix.mulVec_add, neg_dotProduct, dotProduct_neg,
    add_dotProduct, dotProduct_add, hGw, hwu]
  ring

/-- Miao, (9.40), p. 314: if `V` and `R*` are symmetric and `R* + βB*'VB*` is positive
definite, `u = −Fz` is the unique minimiser of the objective (9.39). -/
theorem eq_9_40 [DecidableEq U] {β : ℝ} (Sig Qs : Matrix Z Z ℝ) {Rs : Matrix U U ℝ}
    (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ)
    {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (hG : (cpGain β Rs Bs V).PosDef) (v : ℝ) (z : Z → ℝ) :
    (∀ u, cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) ≤
      cpObj β Sig Qs Rs Ss As Bs V v z u) ∧
    ∀ u, cpObj β Sig Qs Rs Ss As Bs V v z u =
      cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) →
        u = -(cpF β Rs Ss As Bs V *ᵥ z) := by
  have hGu : IsUnit (cpGain β Rs Bs V).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hpos : ∀ x : U → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (cpGain β Rs Bs V *ᵥ x) := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hnn : ∀ x : U → ℝ, 0 ≤ x ⬝ᵥ (cpGain β Rs Bs V *ᵥ x) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [cp_obj_complete_square Sig Qs hR Ss As Bs hV hGu v z u]
    have := hnn (u + cpF β Rs Ss As Bs V *ᵥ z)
    linarith
  · rw [cp_obj_complete_square Sig Qs hR Ss As Bs hV hGu v z u] at hu
    by_contra hne
    have hx : u + cpF β Rs Ss As Bs V *ᵥ z ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    have := hpos _ hx
    linarith

/-- The book's (9.41) (Miao, p. 314):
`V_t = Q* + F'R*F − 2S*F + β(A* − B*F)'V_{t+1}(A* − B*F)`. -/
def cpVbook (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ) :
    Matrix Z Z ℝ :=
  Qs + Fᵀ * Rs * F - (2 : ℝ) • (Ss * F) + β • ((As - Bs * F)ᵀ * V * (As - Bs * F))

/-- The symmetrised (9.41): `Q* + F'R*F − S*F − F'S*' + β(A* − B*F)'V(A* − B*F)`. -/
def cpVnext (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ) :
    Matrix Z Z ℝ :=
  Qs + Fᵀ * Rs * F - (Ss * F + Fᵀ * Ssᵀ) + β • ((As - Bs * F)ᵀ * V * (As - Bs * F))

/-- Miao, (9.41) and the recursion for `v_t`, p. 314: at `u = −Fz` the objective (9.39) equals
`½z'V_t z + ½v_t` with the book's `V_t` and `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`. -/
theorem eq_9_41 (β : ℝ) (Sig Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (v : ℝ) (F : Matrix U Z ℝ)
    (z : Z → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z (-(F *ᵥ z)) =
      (1 / 2) * (z ⬝ᵥ (cpVbook β Qs Rs Ss As Bs V F *ᵥ z)) +
        (1 / 2) * (β * Matrix.trace (V * Sig) + β * v) := by
  have e1 : As *ᵥ z + Bs *ᵥ -(F *ᵥ z) = (As - Bs * F) *ᵥ z := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg, sub_eq_add_neg]
  have e2 : ((As - Bs * F) *ᵥ z) ⬝ᵥ (V *ᵥ ((As - Bs * F) *ᵥ z)) =
      z ⬝ᵥ (((As - Bs * F)ᵀ * V * (As - Bs * F)) *ᵥ z) := by
    rw [cp_dot_left, Matrix.mulVec_mulVec]
  have e3 : (F *ᵥ z) ⬝ᵥ ((Rs * F) *ᵥ z) = z ⬝ᵥ ((Fᵀ * Rs * F) *ᵥ z) := by
    rw [cp_dot_left, Matrix.mul_assoc]
  rw [cpObj, e1, e2]
  simp only [cpVbook, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, Matrix.mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg, Matrix.mulVec_mulVec, e3, smul_eq_mul]
  ring

/-- The symmetrised `V_t` has the same quadratic form as the book's (9.41). -/
theorem cp_Vnext_quad (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ)
    (z : Z → ℝ) :
    z ⬝ᵥ (cpVnext β Qs Rs Ss As Bs V F *ᵥ z) = z ⬝ᵥ (cpVbook β Qs Rs Ss As Bs V F *ᵥ z) := by
  have e : z ⬝ᵥ ((Fᵀ * Ssᵀ) *ᵥ z) = z ⬝ᵥ ((Ss * F) *ᵥ z) := by
    rw [← cp_quad_transpose (Ss * F), Matrix.transpose_mul]
  simp only [cpVnext, cpVbook, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add,
    dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, e, smul_eq_mul]
  ring

/-- The symmetrised `V_t` is symmetric when `Q*`, `R*` and `V_{t+1}` are. -/
theorem cp_Vnext_symm (β : ℝ) {Qs : Matrix Z Z ℝ} (hQ : Qsᵀ = Qs) {Rs : Matrix U U ℝ}
    (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ)
    {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (F : Matrix U Z ℝ) :
    (cpVnext β Qs Rs Ss As Bs V F)ᵀ = cpVnext β Qs Rs Ss As Bs V F := by
  simp only [cpVnext, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hQ, hR, hV, Matrix.mul_assoc]
  abel

omit [Fintype Z] [Fintype U] in
/-- `Q*` is symmetric when `Q_zz`, `Q_yy` are. -/
theorem cp_Qst_symm (P : CPDisc Z Y U) (hQz : P.Qzzᵀ = P.Qzz) (hQy : P.Qyyᵀ = P.Qyy)
    (Hz : Matrix Y Z ℝ) : (P.Qst Hz)ᵀ = P.Qst Hz := by
  simp only [CPDisc.Qst, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    hQz, hQy, Matrix.mul_assoc]
  abel

omit [Fintype Z] [Fintype U] in
/-- `R*` is symmetric when `R`, `Q_yy` are. -/
theorem cp_Rst_symm (P : CPDisc Z Y U) (hR : P.Rᵀ = P.R) (hQy : P.Qyyᵀ = P.Qyy)
    (Hu : Matrix Y U ℝ) : (P.Rst Hu)ᵀ = P.Rst Hu := by
  simp only [CPDisc.Rst, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    hR, hQy, Matrix.mul_assoc]
  abel

omit [Fintype Y] in
/-- Miao, (9.42), p. 314: with `u = −Fz`, `y = H_z z + H_u u = (H_z − H_uF)z`. -/
theorem eq_9_42 (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) (F : Matrix U Z ℝ) (z : Z → ℝ) :
    Hz *ᵥ z + Hu *ᵥ (-(F *ᵥ z)) = (Hz - Hu * F) *ᵥ z := by
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg, sub_eq_add_neg]

/-! ### The Bellman step and Markov perfect equilibrium -/

namespace CPDisc

/-- The right side of the Bellman equations (9.31)/(9.33) with `J_{t+1}(z) = ½z'Vz + ½v`:
`L(z, y, u) + β E_t J_{t+1}(z_{t+1})`, the expectation evaluated by `cp_expected_quadratic`. -/
noncomputable def total (P : CPDisc Z Y U) (V : Matrix Z Z ℝ) (v : ℝ) (z : Z → ℝ) (y : Y → ℝ)
    (u : U → ℝ) : ℝ :=
  P.loss z y u + P.β * ((1 / 2) * (P.mean z y u ⬝ᵥ (V *ᵥ P.mean z y u)) +
    (1 / 2) * Matrix.trace (V * P.Sig) + (1 / 2) * v)

/-- `F_t` of (9.40) for the period-`t` problem given `(V_{t+1}, M_{t+1})`. -/
noncomputable def Fnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix U Z ℝ :=
  cpF P.β (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V

/-- `V_t` (symmetrised (9.41)). -/
noncomputable def Vnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  cpVnext P.β (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M))
    (P.Bst (P.Hu M)) V (P.Fnext V M)

/-- `M_t = H_z − H_uF_t` (9.42). -/
noncomputable def Mnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix Y Z ℝ :=
  P.Hz M - P.Hu M * P.Fnext V M

/-- The gain matrix `R*_t + βB*'V_{t+1}B*`. -/
noncomputable def Gain [DecidableEq Y] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix U U ℝ :=
  cpGain P.β (P.Rst (P.Hu M)) (P.Bst (P.Hu M)) V

end CPDisc

/-- The period-`t` objective is (9.39) once the constraint is used. -/
theorem cp_total_eq [DecidableEq Y] (P : CPDisc Z Y U) (hQy : P.Qyyᵀ = P.Qyy)
    (V : Matrix Z Z ℝ) (v : ℝ) (M : Matrix Y Z ℝ) (z : Z → ℝ) (u : U → ℝ) :
    P.total V v z (P.Hz M *ᵥ z + P.Hu M *ᵥ u) u =
      cpObj P.β P.Sig (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M))
        (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V v z u := by
  rw [CPDisc.total, eq_step2 P hQy, eq_9_38, cpObj]

/-- **One step of the backward induction** (Miao, (9.33)–(9.42), pp. 312–314). Let `Q_yy`, `R`
and `V_{t+1}` be symmetric, `A_yy − GA_zy` invertible and `R*_t + βB*'V_{t+1}B*` positive
definite. For every `z`, among all `(y, u)` satisfying the constraint given the public's rule
`M_{t+1}`, `(M_t z, −F_t z)` is the unique minimiser of `L + βE_t J_{t+1}`, and the minimum is
`J_t(z) = ½z'V_t z + ½v_t` with `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`. -/
theorem cp_bellman_step [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U)
    (hQy : P.Qyyᵀ = P.Qyy) (hR : P.Rᵀ = P.R) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (v : ℝ)
    (M : Matrix Y Z ℝ) (hK : IsUnit (P.K M).det) (hG : (P.Gain V M).PosDef) (z : Z → ℝ) :
    P.Feasible M z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) ∧
    (∀ y u, P.Feasible M z y u →
      P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) ≤ P.total V v z y u) ∧
    (∀ y u, P.Feasible M z y u →
      P.total V v z y u = P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) →
        y = P.Mnext V M *ᵥ z ∧ u = -(P.Fnext V M *ᵥ z)) ∧
    P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) =
      (1 / 2) * (z ⬝ᵥ (P.Vnext V M *ᵥ z)) +
        (1 / 2) * (P.β * Matrix.trace (V * P.Sig) + P.β * v) := by
  have hRs := cp_Rst_symm P hR hQy (P.Hu M)
  have hM : P.Mnext V M *ᵥ z = P.Hz M *ᵥ z + P.Hu M *ᵥ (-(P.Fnext V M *ᵥ z)) := by
    rw [eq_9_42]
    rfl
  have hmin := eq_9_40 P.Sig (P.Qst (P.Hz M)) hRs (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M))
    (P.Bst (P.Hu M)) hV hG v z
  have hopt : P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) =
      cpObj P.β P.Sig (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M))
        (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V v z (-(P.Fnext V M *ᵥ z)) := by
    rw [hM, cp_total_eq P hQy]
  refine ⟨(eq_9_37 P M hK _ _ _).2 hM, fun y u hf => ?_, fun y u hf heq => ?_, ?_⟩
  · rw [(eq_9_37 P M hK z y u).1 hf, cp_total_eq P hQy, hopt]
    exact hmin.1 u
  · have hy := (eq_9_37 P M hK z y u).1 hf
    rw [hy, cp_total_eq P hQy, hopt] at heq
    have hu := hmin.2 u heq
    refine ⟨?_, hu⟩
    rw [hy, hM, hu]
    rfl
  · rw [hopt, eq_9_41, ← cp_Vnext_quad]
    rfl

/-- **Definition 9.5.1** (Miao, p. 311). The linear rules `y_t = Mz_t`, `u_t = −Fz_t` form a
Markov perfect equilibrium if there is a quadratic value function `J(z) = ½z'Vz + ½v` (`V`
symmetric) such that, for every state `z`, (i) `(Mz, −Fz)` solves the Bellman equation (9.31):
it minimises `L(z, y, u) + βE_t J(z_{t+1})` over all `(y, u)` satisfying (9.18) when the public
expects `E_t y_{t+1} = f(z_t)`, and attains `J(z)`; and (ii) `f(z_t) = ME_t z_{t+1}`, i.e. the
constraint is `Feasible` with the public's rule `M`. -/
def IsMPE (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (F : Matrix U Z ℝ) : Prop :=
  ∃ (V : Matrix Z Z ℝ) (v : ℝ), Vᵀ = V ∧ ∀ z,
    P.Feasible M z (M *ᵥ z) (-(F *ᵥ z)) ∧
    (∀ y u, P.Feasible M z y u → P.total V v z (M *ᵥ z) (-(F *ᵥ z)) ≤ P.total V v z y u) ∧
    (1 / 2) * (z ⬝ᵥ (V *ᵥ z)) + (1 / 2) * v = P.total V v z (M *ᵥ z) (-(F *ᵥ z))

/-- **Definition 9.5.1**, unfolded (Miao, p. 311). -/
theorem definition_9_5_1 (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (F : Matrix U Z ℝ) :
    IsMPE P M F ↔ ∃ (V : Matrix Z Z ℝ) (v : ℝ), Vᵀ = V ∧ ∀ z,
      P.Feasible M z (M *ᵥ z) (-(F *ᵥ z)) ∧
      (∀ y u, P.Feasible M z y u → P.total V v z (M *ᵥ z) (-(F *ᵥ z)) ≤ P.total V v z y u) ∧
      (1 / 2) * (z ⬝ᵥ (V *ᵥ z)) + (1 / 2) * v = P.total V v z (M *ᵥ z) (-(F *ᵥ z)) :=
  Iff.rfl

/-- **The fixed point of the iteration is an equilibrium** (Miao, pp. 314–315: "Iterating this
process until convergence gives `V` and `M` in a Markov perfect equilibrium"). If
`V = V_t(V, M)`, `M = M_t(V, M)` and `v = β tr(VΣ) + βv` (the fixed points of (9.41), (9.42) and
the `v`-recursion), with the hypotheses of `cp_bellman_step`, then `(M, F(V, M))` is a Markov
perfect equilibrium with `J(z) = ½z'Vz + ½v`. -/
theorem cp_mpe_of_fixed_point [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U)
    (hQy : P.Qyyᵀ = P.Qyy) (hR : P.Rᵀ = P.R) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) {v : ℝ}
    {M : Matrix Y Z ℝ} (hK : IsUnit (P.K M).det) (hG : (P.Gain V M).PosDef)
    (hVfix : P.Vnext V M = V) (hMfix : P.Mnext V M = M)
    (hvfix : v = P.β * Matrix.trace (V * P.Sig) + P.β * v) :
    IsMPE P M (P.Fnext V M) := by
  refine ⟨V, v, hV, fun z => ?_⟩
  obtain ⟨h1, h2, -, h4⟩ := cp_bellman_step P hQy hR hV v M hK hG z
  rw [hMfix] at h1 h2 h4
  refine ⟨h1, h2, ?_⟩
  rw [h4, hVfix, ← hvfix]

end Miao.LinearQuadratic
