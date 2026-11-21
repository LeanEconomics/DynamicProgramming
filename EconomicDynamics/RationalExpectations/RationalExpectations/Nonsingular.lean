/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.BlockSplit

/-!
# Nonsingular systems: Theorems 1.4.1 and 1.4.2, Corollary 1.4.1

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

Miao, §1.4.1, pp. 17–23: `x_{t+1} = Wx_t + A⁻¹Cz_t` (1.22) with `W = A⁻¹B`.

* (1.22) `eq_1_22`; the backward solution (1.25) in the form
  `x_t = Wᵗx₀ + ∑_{j<t} WʲA⁻¹Cz_{t−1−j}` (`eq_1_25`), and (1.24) for `x* = Px` (`eq_1_24`).
* **Theorem 1.4.1** (`theorem_1_4_1`): with `A`, `I − W` nonsingular and `z_t = z̄` eventually,
  every solution converges to `x̄ = (A − B)⁻¹Cz̄` iff all eigenvalues of `W` are stable. Both
  directions are proved; the book asserts the converse without proof. For the converse, the
  difference of two solutions is `Wᵗ(x₀ − x₀')`, so every orbit of `W` converges to zero.
  `xbar_eq`: the two formulas for `x̄`, `(A − B)⁻¹Cz̄ = (I − W)⁻¹A⁻¹Cz̄`, agree.
* **Theorem 1.4.2** (Blanchard–Kahn, `theorem_1_4_2`), with a real block split
  `PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`, which exists under (iii):
  `exists_real_block_split`), `x = (k, y)`, `n_k` predetermined and `n_y` jump coordinates:
  if `n_u = n_y` and `P_uy` is nonsingular, then for every `k₀` and every stable `z` there is a
  unique stable solution. The proof follows the book: the forward solution (1.29) for `u`
  (`forwardU`, `eq_1_29`; the printed formula `u_t = −∑ⱼ J_u^{−j−1}C_u*z_{t+j}` is correct),
  (1.30)–(1.32) (`eq_1_30`, `eq_1_31`, `eq_1_32`), then `y₀` from (1.32) and the backward
  solution. Existence needs only a right inverse of `P_uy` (`bk_exists`), uniqueness only a
  left inverse (`bk_unique`). (1.33) is checked (`eq_1_33`, the printed coefficients are
  correct), and `R_ks` is nonsingular with `R_ks⁻¹ = P_sk − P_syP_uy⁻¹P_uk` (`rks_inv`); the
  converse (`puy_inv_of_rks`) and the order condition `n_s = n_k ⇔ n_u = n_y` (`bk_order_iff`)
  give the book's reformulation of the Blanchard–Kahn conditions.
* **Corollary 1.4.1** (`corollary_1_4_1`): under Assumption 1.4.2 the stable solution converges
  to `x̄` (here `I − W` and `A − B` are automatically invertible).
* **The stable manifold (1.34)** (`eq_1_34`, `stable_initial_iff`): the initial values of
  stable solutions are the `(k₀, y₀)` with `y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`. The book calls this an
  `n_k`-dimensional subspace. For `z = 0` it is the linear subspace `stableArm P`
  (`{x : (Px)_u = 0}`, `stableArm_iff`) of dimension `n_k` (`finrank_stableArm`); in general
  it is the affine translate `x̂ + stableArm P` with `x̂ = (0, P_uy⁻¹u₀)`
  (`stable_initial_translate`), a linear subspace only when `u₀ = 0`.
* **Unit roots** (p. 23, `remark_unit_root`): for `x_{t+1} = x_t + 1` (`n_k = 1`,
  `n_u = n_y = 0`, eigenvalue `1`) no solution is stable.
-/

open Filter Topology

namespace Miao.RationalExpectations

open Module
open scoped Matrix

/-! ### (1.22), (1.24), (1.25) -/

/-- Miao, (1.22), p. 17: for nonsingular `A`, (1.20) is `x_{t+1} = A⁻¹Bx_t + A⁻¹Cz_t`. -/
theorem eq_1_22 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ) (x : ℕ → n → ℝ) :
    IsSolution A B C z x ↔ ∀ t, x (t + 1) = (A⁻¹ * B) *ᵥ x t + (A⁻¹ * C) *ᵥ z t := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← h,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  · rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.one_mul]

/-- The recursion `x_{t+1} = Wx_t + Gz_t` has a solution from every `x₀`. -/
theorem exists_sol_rec {n m : Type*} [Fintype n] [Fintype m] (W : Matrix n n ℝ)
    (G : Matrix n m ℝ) (z : ℕ → m → ℝ) (x₀ : n → ℝ) :
    ∃ x : ℕ → n → ℝ, x 0 = x₀ ∧ ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t :=
  ⟨fun t => Nat.rec x₀ (fun t xt => W *ᵥ xt + G *ᵥ z t) t, rfl, fun _ => rfl⟩

/-- Solutions of `x_{t+1} = Wx_t + Gz_t` are determined by `x₀`. -/
theorem sol_rec_unique {n m : Type*} [Fintype n] [Fintype m] (W : Matrix n n ℝ)
    (G : Matrix n m ℝ) (z : ℕ → m → ℝ) {x y : ℕ → n → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (hy : ∀ t, y (t + 1) = W *ᵥ y t + G *ᵥ z t)
    (h0 : x 0 = y 0) : x = y := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih => rw [hx, hy, ih]

/-- Miao, p. 18: with `A` nonsingular, (1.22) has a solution for every `x₀` (the backward
solution), and it is unique. -/
theorem exists_unique_solution {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ)
    (x₀ : n → ℝ) : ∃! x : ℕ → n → ℝ, IsSolution A B C z x ∧ x 0 = x₀ := by
  obtain ⟨x, hx0, hx⟩ := exists_sol_rec (A⁻¹ * B) (A⁻¹ * C) z x₀
  refine ⟨x, ⟨(eq_1_22 A B C hA z x).2 hx, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  exact sol_rec_unique _ _ z ((eq_1_22 A B C hA z y).1 hy) hx (hy0.trans hx0.symm)

/-- Miao, (1.24), p. 18: if `PW = JP`, then `x* = Px` solves `x*_{t+1} = Jx*_t + C*z_t`
with `C* = PA⁻¹C`. -/
theorem eq_1_24 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (P J : Matrix n n ℝ) (hPW : P * (A⁻¹ * B) = J * P)
    (z : ℕ → m → ℝ) (x : ℕ → n → ℝ) (hx : IsSolution A B C z x) (t : ℕ) :
    P *ᵥ x (t + 1) = J *ᵥ (P *ᵥ x t) + (P * A⁻¹ * C) *ᵥ z t := by
  rw [(eq_1_22 A B C hA z x).1 hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Miao, (1.25), p. 18, the backward-looking solution in the original coordinates:
`x_t = Wᵗx₀ + ∑_{j<t} WʲA⁻¹Cz_{t−1−j}`. -/
theorem eq_1_25 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ) (x : ℕ → n → ℝ)
    (hx : IsSolution A B C z x) (t : ℕ) :
    x t = ((A⁻¹ * B) ^ t) *ᵥ x 0 +
      ∑ j ∈ Finset.range t, ((A⁻¹ * B) ^ j) *ᵥ ((A⁻¹ * C) *ᵥ z (t - 1 - j)) :=
  backward_sol_eq _ ((eq_1_22 A B C hA z x).1 hx) t

/-! ### Theorem 1.4.1 -/

/-- `A − B = A(I − W)` is invertible when `A` and `I − W` are. -/
theorem isUnit_sub_det {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) (hIW : IsUnit (1 - A⁻¹ * B).det) : IsUnit (A - B).det := by
  have : A - B = A * (1 - A⁻¹ * B) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [this, Matrix.det_mul]
  exact hA.mul hIW

/-- Miao, p. 19 (proof of Theorem 1.4.1): `(I − W)⁻¹A⁻¹Cz̄` is the steady state `x̄` of (1.21). -/
theorem xbar_eq {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (zbar : m → ℝ) (hA : IsUnit A.det) :
    (A - B)⁻¹ *ᵥ (C *ᵥ zbar) = (1 - A⁻¹ * B)⁻¹ *ᵥ ((A⁻¹ * C) *ᵥ zbar) := by
  have : A - B = A * (1 - A⁻¹ * B) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [this, Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Theorem 1.4.1** (Miao, p. 18). Let `A` and `I − W` be nonsingular, `W = A⁻¹B`, and
`z_t = z̄` for `t ≥ T` (Assumption 1.4.2). Every solution of (1.22) converges to
`x̄ = (A − B)⁻¹Cz̄`, whatever `x₀`, if and only if all eigenvalues of `W` are stable. -/
theorem theorem_1_4_1 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det)
    (hIW : IsUnit (1 - A⁻¹ * B).det) (z : ℕ → m → ℝ) (zbar : m → ℝ)
    (hz : EventuallyConst z zbar) :
    (∀ x, IsSolution A B C z x → Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (C *ᵥ zbar)))) ↔
      IsStableMatrix ((A⁻¹ * B).map Complex.ofRealHom) := by
  set W := A⁻¹ * B
  set G := A⁻¹ * C
  have hAB := isUnit_sub_det A B hA hIW
  set xb := (A - B)⁻¹ *ᵥ (C *ᵥ zbar)
  have hbar : xb = W *ᵥ xb + G *ᵥ zbar :=
    (eq_1_22 A B C hA (fun _ => zbar) (fun _ => xb)).1 (eq_1_21_solution A B C zbar hAB) 0
  have hdiff : ∀ x y, IsSolution A B C z x → IsSolution A B C z y →
      ∀ t, x t - y t = (W ^ t) *ᵥ (x 0 - y 0) := by
    intro x y hx hy t
    have hx' := (eq_1_22 A B C hA z x).1 hx
    have hy' := (eq_1_22 A B C hA z y).1 hy
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, hx' t, hy' t, Matrix.mulVec_sub]
      abel
  constructor
  · intro h
    refine isStableMatrix_of_tendsto W fun v => ?_
    obtain ⟨x, hx0, hx⟩ := exists_sol_rec W G z 0
    obtain ⟨y, hy0, hy⟩ := exists_sol_rec W G z v
    have hxs : IsSolution A B C z x := (eq_1_22 A B C hA z x).2 hx
    have hys : IsSolution A B C z y := (eq_1_22 A B C hA z y).2 hy
    have := (h y hys).sub (h x hxs)
    rw [sub_self] at this
    refine this.congr fun t => ?_
    rw [hdiff y x hys hxs t, hy0, hx0, sub_zero]
  · intro hW x hx
    obtain ⟨T, hT⟩ := hz
    have hx' := (eq_1_22 A B C hA z x).1 hx
    have hd : ∀ k, x (k + T) - xb = (W ^ k) *ᵥ (x T - xb) := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, show k + 1 + T = k + T + 1 by ring,
          hx' (k + T), hT (k + T) (by omega), Matrix.mulVec_sub]
        conv_lhs => rw [hbar]
        abel
    have h1 : Tendsto (fun k => x (k + T) - xb) atTop (𝓝 0) := by
      simp_rw [hd]
      exact tendsto_of_isStableMatrix W hW _
    have h2 := h1.add_const xb
    simp only [sub_add_cancel, zero_add] at h2
    exact (tendsto_add_atTop_iff_nat T).1 h2

/-! ### The forward solution (1.29) -/

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- Miao, (1.29), p. 21: the forward-looking solution `u_t = −∑_{j ≥ 0} J_u^{−j−1}c_{t+j}` of
`u_{t+1} = J_uu_t + c_t`. -/
noncomputable def forwardU (Ju : Matrix τ τ ℝ) (c : ℕ → τ → ℝ) (t : ℕ) : τ → ℝ :=
  -(Ju⁻¹ *ᵥ ∑' j, (Ju⁻¹ ^ j) *ᵥ c (t + j))

/-- The forward solution solves `u_{t+1} = J_uu_t + c_t`. -/
theorem forwardU_rec (Ju : Matrix τ τ ℝ) (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) (t : ℕ) :
    forwardU Ju c (t + 1) = Ju *ᵥ forwardU Ju c t + c t := by
  have hS := tsum_geom_series_succ Ju⁻¹ hM (v := fun j => c (t + j)) fun _ => hc _
  have e : (fun j => (Ju⁻¹ ^ j) *ᵥ c (t + (j + 1))) = fun j => (Ju⁻¹ ^ j) *ᵥ c (t + 1 + j) := by
    funext j; rw [show t + (j + 1) = t + 1 + j by ring]
  unfold forwardU
  rw [hS, e, add_zero, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  abel

/-- The forward solution is bounded. -/
theorem forwardU_bounded (Ju : Matrix τ τ ℝ) {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) : ∃ D, ∀ t, ‖forwardU Ju c t‖ ≤ D := by
  obtain ⟨c₀, hc₀, hb⟩ := exists_mulVec_bound Ju⁻¹
  refine ⟨c₀ * (K * C / (1 - a)), fun t => ?_⟩
  rw [forwardU, norm_neg]
  exact (hb _).trans (mul_le_mul_of_nonneg_left
    (summable_geom_series Ju⁻¹ hM (v := fun j => c (t + j)) fun _ => hc _).2 hc₀)

/-- The forward solution is the only bounded solution of `u_{t+1} = J_uu_t + c_t`. -/
theorem forwardU_unique (Ju : Matrix τ τ ℝ) (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    {u : ℕ → τ → ℝ} {D : ℝ} (hu : ∀ t, ‖u t‖ ≤ D) (hrec : ∀ t, u (t + 1) = Ju *ᵥ u t + c t) :
    ∀ t, u t = forwardU Ju c t := by
  obtain ⟨D', hD'⟩ := forwardU_bounded Ju hM hc
  set e := fun t => u t - forwardU Ju c t
  have he : ∀ t, e (t + 1) = Ju *ᵥ e t := fun t => by
    simp only [e, hrec t, forwardU_rec Ju hdet hM hc t, Matrix.mulVec_sub]
    abel
  have hek : ∀ t k, (Ju ^ k) *ᵥ e t = e (t + k) := fun t k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← add_assoc, he]
  intro t
  rw [← sub_eq_zero]
  refine eq_zero_of_bounded_orbit Ju⁻¹ Ju hM (Matrix.nonsing_inv_mul _ hdet)
    (C := D + D') fun k => ?_
  rw [hek]
  exact (norm_sub_le _ _).trans (add_le_add (hu _) (hD' _))

/-! ### Blanchard–Kahn -/

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] {m : Type*}
  [Fintype m]

omit [DecidableEq τ] [DecidableEq ι] [DecidableEq σ] in
/-- (1.26), p. 20: the stable part `s_t = (Px_t)_s` of a solution solves
`s_{t+1} = J_ss_t + C_s*z_t`. -/
theorem split_rec_inl {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix ι m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    (P *ᵥ x (t + 1)) ∘ Sum.inl =
      Js *ᵥ ((P *ᵥ x t) ∘ Sum.inl) + (P *ᵥ (G *ᵥ z t)) ∘ Sum.inl := by
  rw [hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW, ← Matrix.mulVec_mulVec,
    ← blockDiag_mulVec_inl Js Ju]
  rfl

omit [DecidableEq τ] [DecidableEq ι] [DecidableEq σ] in
/-- (1.26), p. 20: the unstable part `u_t = (Px_t)_u` solves `u_{t+1} = J_uu_t + C_u*z_t`. -/
theorem split_rec_inr {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix ι m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    (P *ᵥ x (t + 1)) ∘ Sum.inr =
      Ju *ᵥ ((P *ᵥ x t) ∘ Sum.inr) + (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr := by
  rw [hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW, ← Matrix.mulVec_mulVec,
    ← blockDiag_mulVec_inr Js Ju]
  rfl

/-- A solution whose unstable part is bounded is bounded: the stable part always is
(backward solution of a stable system). -/
theorem bounded_of_split {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (G : Matrix ι m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ}
    (hu : ∀ t, ‖(P *ᵥ x t) ∘ Sum.inr‖ ≤ D) : ∃ D', ∀ t, ‖x t‖ ≤ D' := by
  obtain ⟨hPR, hRP, hPW, hJs, -⟩ := hS
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  have hcs : ∀ t, ‖(P *ᵥ (G *ᵥ z t)) ∘ Sum.inl‖ ≤ Cc := fun t =>
    (norm_comp_inl_le _).trans (hCc t)
  have hs := bounded_backward Js hKa (x := fun t => (P *ᵥ x t) ∘ Sum.inl)
    (split_rec_inl hPW G z hx) hcs
  obtain ⟨r, hr0, hr⟩ := exists_mulVec_bound R
  refine ⟨r * (K * ‖(P *ᵥ x 0) ∘ Sum.inl‖ + K * Cc / (1 - a) + D), fun t => ?_⟩
  have hxt : x t = R *ᵥ (P *ᵥ x t) := by rw [Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  rw [hxt]
  exact (hr _).trans (mul_le_mul_of_nonneg_left ((norm_sum_type_le _).trans
    (add_le_add (hs t) (hu t))) hr0)

/-- Miao, (1.29), p. 21: along any stable solution, `u_t = (Px_t)_u` is the forward solution
`−∑ⱼ J_u^{−j−1}C_u*z_{t+j}`. -/
theorem eq_1_29 {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (G : Matrix ι m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ} (hxb : ∀ t, ‖x t‖ ≤ D) (t : ℕ) :
    (P *ᵥ x t) ∘ Sum.inr = forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) t := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  obtain ⟨Dx, hDx⟩ := bounded_mulVec P hxb
  exact forwardU_unique Ju hdet hKa (fun t => (norm_comp_inr_le _).trans (hCc t))
    (fun t => (norm_comp_inr_le _).trans (hDx t)) (split_rec_inr hPW G z hx) t

variable {κ υ : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
/-- Miao, (1.30), p. 21: `s_t = P_skk_t + P_syy_t`. -/
theorem eq_1_30 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inl = P.toBlocks₁₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₁₂ *ᵥ (x ∘ Sum.inr) :=
  mulVec_comp_inl P x

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
/-- Miao, (1.31), p. 21: `u_t = P_ukk_t + P_uyy_t`. -/
theorem eq_1_31 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inr = P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₂₂ *ᵥ (x ∘ Sum.inr) :=
  mulVec_comp_inr P x

omit [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] in
/-- Miao, (1.32), p. 21: if `QP_uy = I`, `y_t = Qu_t − QP_ukk_t`. -/
theorem eq_1_32 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (x : κ ⊕ υ → ℝ) :
    x ∘ Sum.inr = Q *ᵥ ((P *ᵥ x) ∘ Sum.inr) - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) := by
  rw [eq_1_31, Matrix.mulVec_add, add_sub_cancel_left, Matrix.mulVec_mulVec, hQ,
    Matrix.one_mulVec]

/-- **Existence** in Theorem 1.4.2 (Miao, pp. 20–22): if `P_uy` has a right inverse `Q`, then
for every `k₀` and every bounded `z` there is a bounded solution with `k`-part `k₀`, namely the
one with `y₀ = Q(u₀ − P_ukk₀)`, `u₀` the forward solution (1.29). -/
theorem bk_exists {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (k₀ : κ → ℝ) :
    ∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 = Sum.elim k₀ (Q *ᵥ (forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
        P.toBlocks₂₁ *ᵥ k₀)) ∧ ∃ D, ∀ t, ‖x t‖ ≤ D := by
  have hS' := hS
  obtain ⟨-, -, hPW, -, hJu⟩ := hS'
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  set c := fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  have hc : ∀ t, ‖c t‖ ≤ Cc := fun t => (norm_comp_inr_le _).trans (hCc t)
  obtain ⟨x, hx0, hx⟩ := exists_sol_rec W G z
    (Sum.elim k₀ (Q *ᵥ (forwardU Ju c 0 - P.toBlocks₂₁ *ᵥ k₀)))
  have hu : ∀ t, (P *ᵥ x t) ∘ Sum.inr = forwardU Ju c t := fun t => by
    induction t with
    | zero =>
      rw [mulVec_comp_inr, hx0, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, hQ,
        Matrix.one_mulVec]
      abel
    | succ t ih => rw [split_rec_inr hPW G z hx, ih, forwardU_rec Ju hdet hKa hc]
  obtain ⟨D, hD⟩ := forwardU_bounded Ju hKa hc
  exact ⟨x, hx, hx0, bounded_of_split hS G hz hx (D := D) fun t => by rw [hu]; exact hD t⟩

/-- **Uniqueness** in Theorem 1.4.2 (Miao, pp. 20–22): if `P_uy` has a left inverse, two
bounded solutions with the same `k₀` coincide. -/
theorem bk_unique {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C)
    {x y : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t)
    (hy : ∀ t, y (t + 1) = W *ᵥ y t + G *ᵥ z t) {D D' : ℝ} (hxb : ∀ t, ‖x t‖ ≤ D)
    (hyb : ∀ t, ‖y t‖ ≤ D') (h0 : x 0 ∘ Sum.inl = y 0 ∘ Sum.inl) : x = y := by
  refine sol_rec_unique W G z hx hy ?_
  have hux := eq_1_29 hS G hz hx hxb 0
  have huy := eq_1_29 hS G hz hy hyb 0
  have hx2 := eq_1_32 P Q hQ (x 0)
  have hy2 := eq_1_32 P Q hQ (y 0)
  rw [hux, h0] at hx2
  rw [huy] at hy2
  funext i
  rcases i with i | i
  · exact congrFun h0 i
  · exact congrFun (hx2.trans hy2.symm) i

/-- **Theorem 1.4.2** (Blanchard–Kahn, Miao, p. 20). Let `A` be nonsingular and `W = A⁻¹B`
have a real block split `PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`; by
`exists_real_block_split` one exists when (iii) `W` has no eigenvalue on the unit circle).
Order `x = (k, y)` with `k` predetermined. If (i) `n_u = n_y` and (ii) `P_uy` is nonsingular,
then for every `k₀` and every stable `z` the system (1.22) has a unique stable solution with
`k`-part `k₀`. -/
theorem theorem_1_4_2 (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (_hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → ℝ) (z : ℕ → m → ℝ)
    (hz : IsStableSeq z) :
    ∃! x : ℕ → κ ⊕ υ → ℝ, IsSolution A B Cm z x ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableSeq x := by
  obtain ⟨C, hC⟩ := (isStableSeq_iff_exists_le z).1 hz
  obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hii.1 (A⁻¹ * Cm) hC k₀
  refine ⟨x, ⟨(eq_1_22 A B Cm hA z x).2 hx, by rw [hx0, Sum.elim_comp_inl],
    (isStableSeq_iff_exists_le x).2 hxb⟩, fun y ⟨hy, hy0, hyb⟩ => ?_⟩
  obtain ⟨D, hD⟩ := hxb
  obtain ⟨D', hD'⟩ := (isStableSeq_iff_exists_le y).1 hyb
  exact bk_unique hS Q hii.2 (A⁻¹ * Cm) hC ((eq_1_22 A B Cm hA z y).1 hy) hx hD' hD
    (by rw [hy0, hx0, Sum.elim_comp_inl])

/-! ### (1.33) and the matrix `R_ks` -/

/-- The block equations of `PR = I` and `RP = I`. -/
theorem blocks_of_inv {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) :
    (R.toBlocks₁₁ * P.toBlocks₁₁ + R.toBlocks₁₂ * P.toBlocks₂₁ = 1 ∧
      R.toBlocks₁₁ * P.toBlocks₁₂ + R.toBlocks₁₂ * P.toBlocks₂₂ = 0) ∧
    (P.toBlocks₁₁ * R.toBlocks₁₁ + P.toBlocks₁₂ * R.toBlocks₂₁ = 1 ∧
      P.toBlocks₂₁ * R.toBlocks₁₁ + P.toBlocks₂₂ * R.toBlocks₂₁ = 0) := by
  classical
  have h1 := congrArg Matrix.toBlocks₁₁ hRP
  have h2 := congrArg Matrix.toBlocks₁₂ hRP
  have h3 := congrArg Matrix.toBlocks₁₁ hPR
  have h4 := congrArg Matrix.toBlocks₂₁ hPR
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h1
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at h2
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h3
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h4
  refine ⟨⟨h1.trans ?_, h2.trans ?_⟩, ⟨h3.trans ?_, h4.trans ?_⟩⟩ <;>
    ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.one_apply]

/-- Miao, p. 22: `R_ks` is nonsingular, with `R_ks⁻¹ = P_sk − P_syP_uy⁻¹P_uk`. -/
theorem rks_inv {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) :
    R.toBlocks₁₁ * (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) = 1 ∧
      (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) * R.toBlocks₁₁ = 1 := by
  classical
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := blocks_of_inv hPR hRP
  -- `R_ku = −R_ksP_syQ` and `R_ys = −QP_ukR_ks`
  have hku : R.toBlocks₁₂ = -(R.toBlocks₁₁ * P.toBlocks₁₂ * Q) := by
    have := congrArg (· * Q) h2
    simp only [Matrix.add_mul, Matrix.mul_assoc, hQ.1, Matrix.mul_one, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc] at this
    exact eq_neg_of_add_eq_zero_right this
  have hys : R.toBlocks₂₁ = -(Q * P.toBlocks₂₁ * R.toBlocks₁₁) := by
    have := congrArg (Q * ·) h4
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hQ.2, Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  constructor
  · rw [hku] at h1
    rw [← h1, Matrix.mul_sub]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  · rw [hys] at h3
    rw [← h3, Matrix.sub_mul]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
    abel

/-- Miao, p. 22, the converse: if `R_ks` is nonsingular, so is `P_uy`, with
`P_uy⁻¹ = R_yu − R_ysR_ks⁻¹R_ku`. -/
theorem puy_inv_of_rks {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (S : Matrix σ κ ℝ)
    (hS : R.toBlocks₁₁ * S = 1 ∧ S * R.toBlocks₁₁ = 1) :
    P.toBlocks₂₂ * (R.toBlocks₂₂ - R.toBlocks₂₁ * S * R.toBlocks₁₂) = 1 ∧
      (R.toBlocks₂₂ - R.toBlocks₂₁ * S * R.toBlocks₁₂) * P.toBlocks₂₂ = 1 := by
  classical
  -- the same argument with the roles of `P` and `R` exchanged
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := blocks_of_inv hRP hPR
  have hR := (blocks_of_inv hPR hRP)
  have e1 : P.toBlocks₂₂ * R.toBlocks₂₂ + P.toBlocks₂₁ * R.toBlocks₁₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hPR
    rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂] at this
    rw [add_comm, this]
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  have e2 : R.toBlocks₂₂ * P.toBlocks₂₂ + R.toBlocks₂₁ * P.toBlocks₁₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hRP
    rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂] at this
    rw [add_comm, this]
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  clear h1 h3 hR
  -- `P_uk = −P_uyR_ysS` and `P_sy = −SR_kuP_uy`
  have h4' : P.toBlocks₂₁ * R.toBlocks₁₁ + P.toBlocks₂₂ * R.toBlocks₂₁ = 0 := by
    have := (blocks_of_inv hPR hRP).2.2
    exact this
  have h2' : R.toBlocks₁₁ * P.toBlocks₁₂ + R.toBlocks₁₂ * P.toBlocks₂₂ = 0 :=
    (blocks_of_inv hPR hRP).1.2
  have huk : P.toBlocks₂₁ = -(P.toBlocks₂₂ * R.toBlocks₂₁ * S) := by
    have := congrArg (· * S) h4'
    simp only [Matrix.add_mul, Matrix.mul_assoc, hS.1, Matrix.mul_one, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc] at this
    exact eq_neg_of_add_eq_zero_left this
  have hsy : P.toBlocks₁₂ = -(S * R.toBlocks₁₂ * P.toBlocks₂₂) := by
    have := congrArg (S * ·) h2'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hS.2, Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  constructor
  · rw [huk] at e1
    rw [← e1, Matrix.mul_sub]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  · rw [hsy] at e2
    rw [← e2, Matrix.sub_mul]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
    abel

omit [DecidableEq τ] [DecidableEq σ] in
/-- Miao, p. 22: given `n_s + n_u = n_k + n_y`, the order condition `n_u = n_y` is `n_s = n_k`. -/
theorem bk_order_iff {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    [DecidableEq σ] [DecidableEq τ] (hPR : P * R = 1) (hRP : R * P = 1) :
    Fintype.card τ = Fintype.card υ ↔ Fintype.card σ = Fintype.card κ := by
  have := card_add_card_of_inv hPR hRP
  rw [Fintype.card_sum] at this
  omega

/-- Miao, (1.33), p. 21, checked: along any solution, with `Q = P_uy⁻¹` and
`R_ks⁻¹ = P_sk − P_syQP_uk` (`rks_inv`),
`k_{t+1} = R_ksJ_sR_ks⁻¹k_t + (R_kuC_u* + R_ksC_s*)z_t + (R_kuJ_uP_uy + R_ksJ_sP_sy)P_uy⁻¹u_t`.
The forcing term is written as `R_ku(C*z_t)_u + R_ks(C*z_t)_s` with `C* = PG`. -/
theorem eq_1_33 {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    x (t + 1) ∘ Sum.inl =
      (R.toBlocks₁₁ * Js * (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁)) *ᵥ
          (x t ∘ Sum.inl) +
        (R.toBlocks₁₂ *ᵥ ((P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) +
          R.toBlocks₁₁ *ᵥ ((P *ᵥ (G *ᵥ z t)) ∘ Sum.inl)) +
        ((R.toBlocks₁₂ * Ju * P.toBlocks₂₂ + R.toBlocks₁₁ * Js * P.toBlocks₁₂) * Q) *ᵥ
          ((P *ᵥ x t) ∘ Sum.inr) := by
  obtain ⟨-, hRP, hPW, -, -⟩ := hS
  have hk : x (t + 1) ∘ Sum.inl = R.toBlocks₁₁ *ᵥ ((P *ᵥ x (t + 1)) ∘ Sum.inl) +
      R.toBlocks₁₂ *ᵥ ((P *ᵥ x (t + 1)) ∘ Sum.inr) := by
    rw [← mulVec_comp_inl, Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  have hs : (P *ᵥ x t) ∘ Sum.inl = (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) *ᵥ
      (x t ∘ Sum.inl) + (P.toBlocks₁₂ * Q) *ᵥ ((P *ᵥ x t) ∘ Sum.inr) := by
    rw [mulVec_comp_inl, eq_1_32 P Q hQ.2 (x t)]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    abel
  rw [hk, split_rec_inl hPW G z hx, split_rec_inr hPW G z hx, hs]
  simp only [Matrix.mulVec_add, Matrix.add_mul, Matrix.add_mulVec, Matrix.mul_assoc, hQ.1,
    Matrix.mul_one, ← Matrix.mulVec_mulVec]
  abel

/-! ### Corollary 1.4.1 and the stable manifold -/

/-- **Corollary 1.4.1** (Miao, p. 22). Under the conditions of Theorem 1.4.2 and
Assumption 1.4.2 (`z_t = z̄` for `t ≥ T`), the stable solution converges to the steady state
`x̄ = (A − B)⁻¹Cz̄` of (1.21). (`I − W` is invertible because `W` has no eigenvalue `1`
(`IsRealBlockSplit.isUnit_one_sub`), so `A − B` is.) -/
theorem corollary_1_4_1 (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (z : ℕ → m → ℝ) (zbar : m → ℝ) (hz : EventuallyConst z zbar) (x : ℕ → κ ⊕ υ → ℝ)
    (hx : IsSolution A B Cm z x) (hxs : IsStableSeq x) :
    IsUnit (A - B).det ∧ Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (Cm *ᵥ zbar))) := by
  have hAB := isUnit_sub_det A B hA hS.isUnit_one_sub
  refine ⟨hAB, ?_⟩
  obtain ⟨hPR, hRP, hPW, hJs, hJu⟩ := hS
  set W := A⁻¹ * B
  set G := A⁻¹ * Cm
  set xb := (A - B)⁻¹ *ᵥ (Cm *ᵥ zbar)
  have hbar : xb = W *ᵥ xb + G *ᵥ zbar :=
    (eq_1_22 A B Cm hA (fun _ => zbar) (fun _ => xb)).1 (eq_1_21_solution A B Cm zbar hAB) 0
  obtain ⟨T, hT⟩ := hz
  have hx' := (eq_1_22 A B Cm hA z x).1 hx
  -- deviations from `x̄` after `T` solve the homogeneous system
  set d := fun k => x (k + T) - xb
  have hd : ∀ k, d (k + 1) = W *ᵥ d k + (0 : Matrix (κ ⊕ υ) m ℝ) *ᵥ z k := fun k => by
    simp only [d, Matrix.zero_mulVec, add_zero]
    rw [show k + 1 + T = k + T + 1 by ring, hx' (k + T), hT (k + T) (by omega),
      Matrix.mulVec_sub]
    conv_lhs => rw [hbar]
    abel
  obtain ⟨Dx, hDx⟩ := (isStableSeq_iff_exists_le x).1 hxs
  have hdb : ∀ k, ‖d k‖ ≤ Dx + ‖xb‖ := fun k => (norm_sub_le _ _).trans (add_le_add (hDx _) le_rfl)
  have hz0 : ∀ k, ‖z k‖ ≤ ‖z 0‖ + ‖z (0 + T)‖ + ∑ j ∈ Finset.range T, ‖z j‖ := fun k => by
    rcases lt_or_ge k T with hk | hk
    · have := Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.2 hk)
      linarith [norm_nonneg (z 0), norm_nonneg (z (0 + T))]
    · rw [hT k hk, ← hT (0 + T) (by omega)]
      linarith [norm_nonneg (z 0), Finset.sum_nonneg fun j (_ : j ∈ Finset.range T) =>
        norm_nonneg (z j)]
  -- the unstable part vanishes, the stable part decays
  have hu := eq_1_29 ⟨hPR, hRP, hPW, hJs, hJu⟩ 0 hz0 hd hdb
  have hu0 : ∀ k, (P *ᵥ d k) ∘ Sum.inr = 0 := fun k => by
    rw [hu k]
    simp [forwardU]
  have hs : ∀ k, (P *ᵥ d k) ∘ Sum.inl = (Js ^ k) *ᵥ ((P *ᵥ d 0) ∘ Sum.inl) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [split_rec_inl hPW 0 z hd, ih, pow_succ', ← Matrix.mulVec_mulVec]
      simp
  have hPd : Tendsto (fun k => P *ᵥ d k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_sum_type_le _) ?_
    have e : (fun k => ‖(P *ᵥ d k) ∘ Sum.inl‖ + ‖(P *ᵥ d k) ∘ Sum.inr‖) =
        fun k => ‖(Js ^ k) *ᵥ ((P *ᵥ d 0) ∘ Sum.inl)‖ :=
      funext fun k => by rw [hu0, norm_zero, add_zero, hs k]
    rw [e]
    exact (tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_of_isStableMatrix Js hJs _))
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h := ((Matrix.mulVecLin R).continuous_of_finiteDimensional.tendsto 0).comp hPd
    simp only [map_zero] at h
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hRP,
      Matrix.one_mulVec]
  have h2 := hdlim.add_const xb
  simp only [d, sub_add_cancel, zero_add] at h2
  exact (tendsto_add_atTop_iff_nat T).1 h2

/-- Miao, (1.34), p. 22: the initial value of the stable solution satisfies
`y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`, `u₀` the forward solution (1.29). -/
theorem eq_1_34 {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C)
    {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ}
    (hxb : ∀ t, ‖x t‖ ≤ D) :
    x 0 ∘ Sum.inr = Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
      Q *ᵥ (P.toBlocks₂₁ *ᵥ (x 0 ∘ Sum.inl)) := by
  rw [eq_1_32 P Q hQ (x 0), eq_1_29 hS G hz hx hxb 0]

/-- The stable manifold, Miao, p. 22–23: under the conditions of Theorem 1.4.2, `x₀` is the
initial value of a stable solution iff `y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`. -/
theorem stable_initial_iff {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧ x 0 = x₀ ∧
        ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ ∘ Sum.inr = Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
        Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) := by
  constructor
  · rintro ⟨x, hx, rfl, D, hD⟩
    exact eq_1_34 hS Q hQ.2 G hz hx hD
  · intro h
    obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hQ.1 G hz (x₀ ∘ Sum.inl)
    refine ⟨x, hx, ?_, hxb⟩
    rw [hx0]
    funext i
    rcases i with i | i
    · rfl
    · have := congrFun h i
      simp only [Function.comp_apply] at this
      rw [this, Matrix.mulVec_sub]
      rfl

/-- The stable arm of the homogeneous system: `{x : (Px)_u = 0}`. -/
noncomputable def stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) : Submodule ℝ (κ ⊕ υ → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ Sum.inr ∘ₗ P.mulVecLin)

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
theorem mem_stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    x ∈ stableArm P ↔ (P *ᵥ x) ∘ Sum.inr = 0 := by
  simp [stableArm, LinearMap.funLeft]

/-- The stable manifold (1.34) of the homogeneous system `x_{t+1} = Wx_t` (Miao, p. 23): the
initial values of stable solutions form the linear subspace `stableArm P`. -/
theorem stableArm_iff {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t) ∧ x 0 = x₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ ∈ stableArm P := by
  rw [mem_stableArm]
  have hS' := hS
  obtain ⟨-, -, hPW, -, -⟩ := hS'
  have hz : ∀ t : ℕ, ‖(fun _ => (0 : Fin 0 → ℝ)) t‖ ≤ 0 := fun _ => by simp
  have hrec : ∀ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t) →
      ∀ t, x (t + 1) = W *ᵥ x t + (0 : Matrix (κ ⊕ υ) (Fin 0) ℝ) *ᵥ (fun _ => 0) t :=
    fun x hx t => by rw [hx t, Matrix.zero_mulVec, add_zero]
  constructor
  · rintro ⟨x, hx, rfl, D, hD⟩
    rw [eq_1_29 hS 0 hz (hrec x hx) hD 0]
    simp [forwardU]
  · intro h0
    obtain ⟨x, hx0, hx⟩ := exists_sol_rec W (0 : Matrix (κ ⊕ υ) (Fin 0) ℝ) (fun _ => 0) x₀
    have hu : ∀ t, (P *ᵥ x t) ∘ Sum.inr = 0 := fun t => by
      induction t with
      | zero => rw [hx0, h0]
      | succ t ih => rw [split_rec_inr hPW 0 _ hx, ih]; simp
    refine ⟨x, fun t => by rw [hx t, Matrix.zero_mulVec, add_zero], hx0,
      bounded_of_split hS 0 hz hx (D := 0) fun t => by rw [hu]; simp⟩

omit [Fintype σ] [DecidableEq σ] [DecidableEq κ] in
/-- Miao, p. 23: the stable arm is `n_k`-dimensional when `P_uy` is nonsingular. -/
theorem finrank_stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) :
    finrank ℝ (stableArm P) = Fintype.card κ := by
  classical
  set N : Matrix (κ ⊕ υ) κ ℝ :=
    Matrix.of fun i j => Sum.elim (fun a => (1 : Matrix κ κ ℝ) a j)
      (fun b => (-(Q * P.toBlocks₂₁)) b j) i
  have hNl : ∀ k, (N *ᵥ k) ∘ Sum.inl = k := fun k => by
    funext a; simp [N, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hNr : ∀ k, (N *ᵥ k) ∘ Sum.inr = -(Q * P.toBlocks₂₁) *ᵥ k := fun k => by
    funext b; simp [N, Matrix.mulVec, dotProduct]
  have hrange : LinearMap.range (Matrix.toLin' N) = stableArm P := by
    ext x
    rw [LinearMap.mem_range, mem_stableArm, mulVec_comp_inr]
    constructor
    · rintro ⟨k, rfl⟩
      rw [Matrix.toLin'_apply, hNl, hNr, Matrix.neg_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQ.1, Matrix.one_mul, add_neg_cancel]
    · intro h
      refine ⟨x ∘ Sum.inl, ?_⟩
      rw [Matrix.toLin'_apply]
      funext i
      rcases i with a | b
      · exact congrFun (hNl _) a
      · have h2 := congrArg (fun v => Q *ᵥ v) h
        simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hQ.2, Matrix.one_mulVec,
          Matrix.mulVec_zero] at h2
        have := congrFun (hNr (x ∘ Sum.inl)) b
        change ((N *ᵥ x ∘ Sum.inl) ∘ Sum.inr) b = _
        rw [this, Matrix.neg_mulVec]
        have h3 := congrFun h2 b
        simp only [Pi.add_apply, Function.comp_apply, Pi.zero_apply] at h3 ⊢
        rw [Pi.neg_apply]
        linarith
  have hinj : Function.Injective (Matrix.toLin' N) := fun k k' h => by
    have := congrArg (fun v => v ∘ Sum.inl) h
    simpa [Matrix.toLin'_apply, hNl] using this
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]

/-- Miao, p. 23, corrected: for a nonzero forcing the stable manifold is an affine subspace, the
translate of the `n_k`-dimensional `stableArm P` by `x̂ = (0, P_uy⁻¹u₀)`; it is a linear subspace
only when `u₀ = 0`. -/
theorem stable_initial_translate {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧ x 0 = x₀ ∧
        ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0) ∈
        stableArm P := by
  rw [stable_initial_iff hS Q hQ G hz, mem_stableArm, mulVec_comp_inr]
  set u₀ := forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0
  have hl : (x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ u₀)) ∘ Sum.inl = x₀ ∘ Sum.inl := by funext a; simp
  have hr : (x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ u₀)) ∘ Sum.inr = x₀ ∘ Sum.inr - Q *ᵥ u₀ := by
    funext a; simp
  rw [hl, hr]
  constructor
  · intro h
    rw [h, show Q *ᵥ u₀ - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) - Q *ᵥ u₀ =
        -(Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl))) by abel, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec, add_neg_cancel]
  · intro h
    have h2 : Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) + (x₀ ∘ Sum.inr - Q *ᵥ u₀) = 0 := by
      have := congrArg (fun v => Q *ᵥ v) h
      simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at this
      rwa [Matrix.mulVec_mulVec _ Q P.toBlocks₂₂, hQ.2, Matrix.one_mulVec] at this
    calc x₀ ∘ Sum.inr = (Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) + (x₀ ∘ Sum.inr - Q *ᵥ u₀)) +
          (Q *ᵥ u₀ - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl))) := by abel
      _ = _ := by rw [h2, zero_add]

/-- Miao, p. 23 (eigenvalues on the unit circle): for `x_{t+1} = x_t + z_t` with `z_t = 1`
(`n_k = 1`, `n_u = n_y = 0`, the eigenvalue `1` violates (iii)) no solution is stable: `k_t`
drifts like a random walk with drift, `x_t = x₀ + t`. -/
theorem remark_unit_root (x : ℕ → Fin 1 → ℝ)
    (hx : ∀ t, x (t + 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x t +
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => 1)) :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((1 : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) 1 ∧
      ¬ IsStableSeq x := by
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' ((1 : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) 1 := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ => (1 : ℂ))
      ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · rw [Matrix.toLin'_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
        one_smul]
    · intro h
      simpa using congrFun h 0
  refine ⟨hev, fun hs => ?_⟩
  have hxt : ∀ t : ℕ, x t 0 = x 0 0 + t := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hx t]
      simp [ih]
      ring
  obtain ⟨M, -, hM⟩ := hs
  obtain ⟨t, ht⟩ := exists_nat_gt (M - x 0 0)
  have h1 := (norm_le_pi_norm (x t) 0).trans_lt (hM t)
  rw [hxt, Real.norm_eq_abs] at h1
  linarith [le_abs_self (x 0 0 + t)]

end Miao.RationalExpectations
