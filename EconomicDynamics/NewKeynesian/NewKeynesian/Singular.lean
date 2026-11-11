/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.QZ
import NewKeynesian.Triangular

/-!
# Singular systems: Klein's method

Copied from `EconomicDynamics/RationalExpectations` (module `Singular`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

Miao, §1.4.2, pp. 24–27: the system `Ax_{t+1} = Bx_t + Cz_t` (1.20) with `A` possibly singular,
solved through the ordered QZ form `S = QAZ`, `T = QBZ` of `QZ.lean`.

**Representation.** `x_t ∈ ℂ^{n_k + n_y}` is indexed by `Fin (nk + ny)`; the predetermined block
`k_t` is the coordinates `Fin.castAdd ny i` (`i < n_k`) and `y_t` the coordinates
`Fin.natAdd nk j`. The blocks `S₁₁, S₁₂, S₂₂, …, Z₁₁, Z₁₂` are `Matrix.submatrix` along these
embeddings, and `s_t`, `u_t` are `x*_t ∘ Fin.castAdd ny`, `x*_t ∘ Fin.natAdd nk` with
`x*_t = Zᴴx_t`. Conditions (i) `n_s = n_k` and the stable-first ordering are the one hypothesis
`i < n_k ↔ |tᵢᵢ| < |sᵢᵢ|`.

* `theorem_1_4_5` (Klein): under (i)–(iii), for every `k₀` and stable `z` there is a unique stable
  solution with initial predetermined block `k₀`. The proof follows the book: (1.36)
  (`eq_1_36`), the forward solution for `u_t` (`eq_1_37`, `fwdSum`), the backward recursion
  (1.38) (`eq_1_38`), `s₀ = Z₁₁⁻¹(k₀ − Z₁₂u₀)` (`eq_s0`) and (1.39)–(1.40) (`eq_1_39_40`);
  uniqueness because `T₂₂⁻¹S₂₂` has norm-summable powers, so a bounded `u` is the forward sum.
  `S₁₁⁻¹T₁₁` and `T₂₂⁻¹S₂₂` are upper triangular with diagonal entries of modulus `< 1`
  (`summable_Ms`, `summable_Mu`).
* `theorem_1_4_5_real`: for real `A, B, C, z, k₀` the unique stable solution is real.
* `corollary_1_4_1_singular` (p. 27, "a corollary similar to Corollary 1.4.1"): `A − B` is
  invertible (1 is not a generalized eigenvalue) and every stable solution tends to
  `x̄ = (A − B)⁻¹Cz̄` when `z` is eventually constant.
* `remark_augmented`, `remark_u_eq_zero`: the augmented system for `(z_t, x_t)` (p. 27), whose
  stable solutions have `u_t = 0`.
* The Cagan example (p. 24): `example_cagan_iff`, `example_cagan_det` (`A` singular),
  `example_cagan_regular`, `example_cagan_genEigenvalues` (`λ(A, B) = {1 + 1/α}` for `α ≠ 0`,
  empty for `α = 0`).

**Corrections.**
* (1.37) is printed as `u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂Cz_{t+j}`; the correct forward solution is
  `u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂Cz_{t+j}` (`eq_1_37`); the printed one fails in general
  (`eq_1_37_printed_false`).
-/

open Filter Topology

namespace Miao.NewKeynesian

open scoped Matrix

/-! ### Bounded sequences under matrices -/

/-- `‖Mv‖ ≤ (∑ᵢⱼ |Mᵢⱼ|) ‖v‖` in the max norm, for rectangular `M`. -/
theorem norm_mulVec_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ)
    (v : κ → ℂ) : ‖M *ᵥ v‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ j, M i j * v j‖ := rfl
    _ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
        (norm_nonneg _)

theorem isStableSeq_of_le {E : Type*} [SeminormedAddCommGroup E] {x : ℕ → E} {K : ℝ}
    (h : ∀ t, ‖x t‖ ≤ K) : IsStableSeq x :=
  ⟨max K 0 + 1, by positivity, fun t => (h t).trans_lt (by linarith [le_max_left K 0])⟩

theorem IsStableSeq.bound {E : Type*} [SeminormedAddCommGroup E] {x : ℕ → E}
    (h : IsStableSeq x) : ∃ K, 0 ≤ K ∧ ∀ t, ‖x t‖ ≤ K := by
  obtain ⟨M, hM, hx⟩ := h
  exact ⟨M, hM.le, fun t => (hx t).le⟩

/-- A stable sequence stays stable under a fixed matrix. -/
theorem IsStableSeq.mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ℕ → κ → ℂ}
    (h : IsStableSeq x) (M : Matrix ι κ ℂ) : IsStableSeq fun t => M *ᵥ x t := by
  obtain ⟨K, -, hK⟩ := h.bound
  exact isStableSeq_of_le fun t => (norm_mulVec_le_sum M (x t)).trans
    (mul_le_mul_of_nonneg_left (hK t) (by positivity))

/-! ### The forward solution and the backward recursion -/

/-- The forward sum `∑ⱼ Nʲ w_{t+j}`. -/
noncomputable def fwdSum {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (w : ℕ → Fin m → ℂ) (t : ℕ) :
    Fin m → ℂ :=
  ∑' j, (N ^ j) *ᵥ w (t + j)

theorem summable_fwd {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : Summable fun j => (N ^ j) *ᵥ w (t + j) :=
  Summable.of_norm_bounded (hN.mul_right W) fun _ =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _))

theorem norm_fwdSum_le {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : ‖fwdSum N w t‖ ≤ (∑' j, ‖mclm (N ^ j)‖) * W := by
  have hb : ∀ j, ‖(N ^ j) *ᵥ w (t + j)‖ ≤ ‖mclm (N ^ j)‖ * W := fun j =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _))
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded (hN.mul_right W).hasSum hb

/-- The forward sum solves `u_t = N u_{t+1} + w_t`. -/
theorem fwdSum_rec {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : fwdSum N w t = N *ᵥ fwdSum N w (t + 1) + w t := by
  unfold fwdSum
  have hmap := (mclm N).map_tsum (summable_fwd hN hw (t + 1))
  simp only [mclm_apply] at hmap
  rw [(summable_fwd hN hw t).tsum_eq_zero_add, hmap]
  simp only [pow_zero, Matrix.one_mulVec, add_zero, Matrix.mulVec_mulVec]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_succ', show t + (j + 1) = t + 1 + j by ring]

/-- Any bounded solution of `u_t = N u_{t+1} + w_t` is the forward sum, when the powers of `N`
are summable in norm. -/
theorem eq_fwdSum {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    {u : ℕ → Fin m → ℂ} (hu : IsStableSeq u) (hrec : ∀ t, u t = N *ᵥ u (t + 1) + w t) (t : ℕ) :
    u t = fwdSum N w t := by
  have hiter : ∀ J, u t = (N ^ J) *ᵥ u (t + J) +
      ∑ j ∈ Finset.range J, (N ^ j) *ᵥ w (t + j) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [ih, hrec (t + J), Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        ← pow_succ, show t + J + 1 = t + (J + 1) by ring]
      abel
  obtain ⟨U₀, -, hU₀⟩ := hu.bound
  have h1 : Tendsto (fun J => (N ^ J) *ᵥ u (t + J)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun J => (norm_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_left (hU₀ _) (norm_nonneg _))) ?_
    simpa using hN.tendsto_atTop_zero.mul_const U₀
  have h2 := (summable_fwd hN hw t).hasSum.tendsto_sum_nat
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hiter) h3

/-- The backward recursion `s_{t+1} = M s_t + v_t` with bounded `v` and norm-summable powers of
`M` has bounded solutions. -/
theorem isStableSeq_of_rec {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : Summable fun j => ‖mclm (M ^ j)‖) {v s : ℕ → Fin m → ℂ} (hv : IsStableSeq v)
    (hrec : ∀ t, s (t + 1) = M *ᵥ s t + v t) : IsStableSeq s := by
  have hform : ∀ t, s t = (M ^ t) *ᵥ s 0 + ∑ j ∈ Finset.range t, (M ^ j) *ᵥ v (t - 1 - j) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hrec, ih, Finset.sum_range_succ', Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ',
        Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec, ← pow_succ', pow_zero, Matrix.one_mulVec]
      rw [add_assoc]
      congr 2
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]
  obtain ⟨V, hV0, hV⟩ := hv.bound
  set σ := ∑' j, ‖mclm (M ^ j)‖
  have hσ : ∀ t, ‖mclm (M ^ t)‖ ≤ σ := fun t => hM.le_tsum t fun j _ => norm_nonneg _
  refine isStableSeq_of_le (K := σ * ‖s 0‖ + σ * V) fun t => ?_
  rw [hform t]
  refine (norm_add_le _ _).trans (add_le_add ((norm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_right (hσ t) (norm_nonneg _))) ?_)
  calc ‖∑ j ∈ Finset.range t, (M ^ j) *ᵥ v (t - 1 - j)‖
      ≤ ∑ j ∈ Finset.range t, ‖mclm (M ^ j)‖ * V := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (norm_mulVec_le _ _).trans
          (mul_le_mul_of_nonneg_left (hV _) (norm_nonneg _)))
    _ = (∑ j ∈ Finset.range t, ‖mclm (M ^ j)‖) * V := by rw [Finset.sum_mul]
    _ ≤ σ * V := mul_le_mul_of_nonneg_right
        (hM.sum_le_tsum _ fun j _ => norm_nonneg _) hV0

theorem IsStableSeq.add {E : Type*} [SeminormedAddCommGroup E] {x y : ℕ → E}
    (hx : IsStableSeq x) (hy : IsStableSeq y) : IsStableSeq fun t => x t + y t := by
  obtain ⟨K, -, hK⟩ := hx.bound
  obtain ⟨L, -, hL⟩ := hy.bound
  exact isStableSeq_of_le fun t => (norm_add_le _ _).trans (add_le_add (hK t) (hL t))

theorem IsStableSeq.sub {E : Type*} [SeminormedAddCommGroup E] {x y : ℕ → E}
    (hx : IsStableSeq x) (hy : IsStableSeq y) : IsStableSeq fun t => x t - y t := by
  obtain ⟨K, -, hK⟩ := hx.bound
  obtain ⟨L, -, hL⟩ := hy.bound
  exact isStableSeq_of_le fun t => (norm_sub_le _ _).trans (add_le_add (hK t) (hL t))

theorem IsStableSeq.shift {E : Type*} [Norm E] {x : ℕ → E} (hx : IsStableSeq x) (k : ℕ) :
    IsStableSeq fun t => x (t + k) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t => h _⟩

theorem norm_comp_le {m p : ℕ} (v : Fin p → ℂ) (f : Fin m → Fin p) : ‖v ∘ f‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v (f i)

theorem IsStableSeq.comp {m p : ℕ} {x : ℕ → Fin p → ℂ} (hx : IsStableSeq x) (f : Fin m → Fin p) :
    IsStableSeq fun t => x t ∘ f := by
  obtain ⟨K, -, hK⟩ := hx.bound
  exact isStableSeq_of_le fun t => (norm_comp_le _ f).trans (hK t)

theorem isStableSeq_append {a b : ℕ} {s : ℕ → Fin a → ℂ} {u : ℕ → Fin b → ℂ}
    (hs : IsStableSeq s) (hu : IsStableSeq u) : IsStableSeq fun t => Fin.append (s t) (u t) := by
  obtain ⟨K, hK0, hK⟩ := hs.bound
  obtain ⟨L, hL0, hL⟩ := hu.bound
  refine isStableSeq_of_le (K := K + L) fun t => (pi_norm_le_iff_of_nonneg (by positivity)).2
    fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    exact (norm_le_pi_norm _ i).trans ((hK t).trans (by linarith))
  · rw [Fin.append_right]
    exact (norm_le_pi_norm _ i).trans ((hL t).trans (by linarith))

/-! ### Block form (1.36) -/

theorem upper_castAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) : (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).IsUpperTriangular :=
  fun _ _ h => hM (Fin.lt_def.2 (Fin.lt_def.1 h))

theorem upper_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) : (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).IsUpperTriangular :=
  fun _ _ h => hM ((Fin.natAdd_lt_natAdd_iff a).2 h)

theorem mulVec_castAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (v : Fin (a + b) → ℂ) (i : Fin a) :
    (M *ᵥ v) (Fin.castAdd b i) =
      (M.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (v ∘ Fin.castAdd b)) i +
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (v ∘ Fin.natAdd a)) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.submatrix_apply,
    Function.comp_apply]

theorem mulVec_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) (v : Fin (a + b) → ℂ) (i : Fin b) :
    (M *ᵥ v) (Fin.natAdd a i) =
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (v ∘ Fin.natAdd a)) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.submatrix_apply,
    Function.comp_apply]
  rw [Finset.sum_eq_zero fun j _ => by
    rw [hM (Fin.lt_def.2 (by simp only [id, Fin.val_castAdd, Fin.val_natAdd]; omega)),
      zero_mul], zero_add]

/-- Miao, (1.36), p. 26: with `S`, `T` upper triangular, `Sx*_{t+1} = Tx*_t + c_t` splits into
`S₁₁s_{t+1} + S₁₂u_{t+1} = T₁₁s_t + T₁₂u_t + c¹_t` and `S₂₂u_{t+1} = T₂₂u_t + c²_t`, where `s`
(resp. `u`) is the first `a` (resp. last `b`) coordinates. -/
theorem eq_1_36 {a b : ℕ} {S T : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (y y' c : Fin (a + b) → ℂ) :
    S *ᵥ y' = T *ᵥ y + c ↔
      (S.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (y' ∘ Fin.castAdd b) +
          S.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (y' ∘ Fin.natAdd a) =
        T.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (y ∘ Fin.castAdd b) +
          T.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (y ∘ Fin.natAdd a) + c ∘ Fin.castAdd b) ∧
      S.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (y' ∘ Fin.natAdd a) =
        T.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (y ∘ Fin.natAdd a) + c ∘ Fin.natAdd a := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h (Fin.castAdd b i)
      simp only [Pi.add_apply, mulVec_castAdd] at this
      simp only [Pi.add_apply, Function.comp_apply, this]
    · have := congrFun h (Fin.natAdd a i)
      simp only [Pi.add_apply, mulVec_natAdd hS, mulVec_natAdd hT] at this
      simp only [Pi.add_apply, Function.comp_apply, this]
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have := congrFun h1 i
      simp only [Pi.add_apply, Function.comp_apply] at this
      simp only [Pi.add_apply, mulVec_castAdd, this]
    · have := congrFun h2 i
      simp only [Pi.add_apply, Function.comp_apply] at this
      simp only [Pi.add_apply, mulVec_natAdd hS, mulVec_natAdd hT, this]

/-- Solving the second block of (1.36) for `u_t` (Miao, p. 26): with `T₂₂` invertible,
`S₂₂u' = T₂₂u + c` iff `u = T₂₂⁻¹S₂₂u' − T₂₂⁻¹c`. -/
theorem solve_fwd {m : ℕ} {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (h : T22.det ≠ 0)
    (u u' c : Fin m → ℂ) :
    S22 *ᵥ u' = T22 *ᵥ u + c ↔ u = (T22⁻¹ * S22) *ᵥ u' + -(T22⁻¹ *ᵥ c) := by
  have h1 : T22⁻¹ * T22 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)
  have h2 : T22 * T22⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_add, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec]
    abel
  · intro e
    rw [e, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mulVec_neg, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    abel

/-- Miao, (1.38), p. 26: solving the first block of (1.36) for `s_{t+1}`:
`s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂u_{t+1} + S₁₁⁻¹c¹_t`. -/
theorem eq_1_38 {m p : ℕ} {S11 T11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 : Matrix (Fin m) (Fin p) ℂ} (h : S11.det ≠ 0) (s s' c : Fin m → ℂ)
    (u u' : Fin p → ℂ) :
    S11 *ᵥ s' + S12 *ᵥ u' = T11 *ᵥ s + T12 *ᵥ u + c ↔
      s' = (S11⁻¹ * T11) *ᵥ s + S11⁻¹ *ᵥ (T12 *ᵥ u - S12 *ᵥ u' + c) := by
  have h1 : S11⁻¹ * S11 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)
  have h2 : S11 * S11⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    have e' : S11 *ᵥ s' = T11 *ᵥ s + (T12 *ᵥ u - S12 *ᵥ u' + c) := by
      rw [← sub_eq_of_eq_add' e.symm]
      abel
    calc s' = S11⁻¹ *ᵥ (S11 *ᵥ s') := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      _ = _ := by rw [e', Matrix.mulVec_add, Matrix.mulVec_mulVec]
  · intro e
    rw [e, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    abel

/-! ### The blocks of an ordered QZ form -/

/-- Miao, p. 26: `S₁₁` is invertible, since its diagonal entries are the `sᵢᵢ` of the stable
pairs, `|tᵢᵢ| < |sᵢᵢ|`. -/
theorem det_S11_ne_zero {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖) :
    (S.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (upper_castAdd hS)]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have h := (hord (Fin.castAdd ny i)).1 i.2
  rw [Matrix.submatrix_apply]
  exact norm_pos_iff.1 ((norm_nonneg _).trans_lt h)

/-- Miao, p. 26: `T₂₂` is invertible, since its diagonal entries are the `tᵢᵢ` of the unstable
pairs, `|tᵢᵢ| > |sᵢᵢ|` (no pair on the unit circle). -/
theorem det_T22_ne_zero {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hT : T.IsUpperTriangular) (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) :
    (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk)).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (upper_natAdd hT)]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have h1 : ¬ ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ < ‖S (Fin.natAdd nk i) (Fin.natAdd nk i)‖ :=
    fun h => by have := (hord _).2 h; simp at this
  have h2 := lt_of_le_of_ne (not_lt.1 h1) (hdiag _).symm
  rw [Matrix.submatrix_apply]
  exact norm_pos_iff.1 ((norm_nonneg _).trans_lt h2)

/-- `S₁₁⁻¹T₁₁` is upper triangular with diagonal entries `tᵢᵢ/sᵢᵢ` of modulus less than one, so
the norms of its powers are summable. -/
theorem summable_Ms {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖) :
    Summable fun j => ‖mclm (((S.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
      T.submatrix (Fin.castAdd ny) (Fin.castAdd ny)) ^ j)‖ := by
  have hdet := det_S11_ne_zero hS hord
  have hinv := upper_inv (upper_castAdd hS) hdet
  refine summable_norm_pow_of_triangular _ (hinv.mul (upper_castAdd hT)) fun i => ?_
  rw [diag_mul_of_upper hinv (upper_castAdd hT), diag_inv_of_upper (upper_castAdd hS) hdet]
  simp only [Matrix.submatrix_apply, norm_mul, norm_inv]
  have h := (hord (Fin.castAdd ny i)).1 i.2
  have hpos : 0 < ‖S (Fin.castAdd ny i) (Fin.castAdd ny i)‖ := (norm_nonneg _).trans_lt h
  rw [inv_mul_lt_iff₀ hpos, mul_one]
  exact h

/-- `T₂₂⁻¹S₂₂` is upper triangular with diagonal entries `sᵢᵢ/tᵢᵢ` of modulus less than one. -/
theorem summable_Mu {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) :
    Summable fun j => ‖mclm (((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      S.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j)‖ := by
  have hdet := det_T22_ne_zero hT hord hdiag
  have hinv := upper_inv (upper_natAdd hT) hdet
  refine summable_norm_pow_of_triangular _ (hinv.mul (upper_natAdd hS)) fun i => ?_
  rw [diag_mul_of_upper hinv (upper_natAdd hS), diag_inv_of_upper (upper_natAdd hT) hdet]
  simp only [Matrix.submatrix_apply, norm_mul, norm_inv]
  have h1 : ¬ ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ < ‖S (Fin.natAdd nk i) (Fin.natAdd nk i)‖ :=
    fun h => by have := (hord _).2 h; simp at this
  have h2 := lt_of_le_of_ne (not_lt.1 h1) (hdiag _).symm
  have hpos : 0 < ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ := (norm_nonneg _).trans_lt h2
  rw [inv_mul_lt_iff₀ hpos, mul_one]
  exact h2

/-! ### The transformed system -/

/-- Klein's construction in the transformed coordinates `x* = Zᴴx` (Miao, proof of Theorem 1.4.5,
pp. 25–26). With `S`, `T` upper triangular, the first `n_k` pairs stable and the rest unstable
(none on the unit circle), `Z₁₁` invertible and `c` stable, there is exactly one stable `y`
with `Sy_{t+1} = Ty_t + c_t` and `(Zy₀)ₖ = k₀`. -/
theorem klein_core {nk ny : ℕ} {S T Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    {c : ℕ → Fin (nk + ny) → ℂ} (hc : IsStableSeq c) (k₀ : Fin nk → ℂ) :
    ∃! y : ℕ → Fin (nk + ny) → ℂ, (∀ t, S *ᵥ y (t + 1) = T *ᵥ y t + c t) ∧ IsStableSeq y ∧
      ∀ i, (Z *ᵥ y 0) (Fin.castAdd ny i) = k₀ i := by
  set K := Fin.castAdd (n := nk) ny
  set U := Fin.natAdd (m := ny) nk
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hMs := summable_Ms hS hT hord
  have hN := summable_Mu hS hT hord hdiag
  set N := (T.submatrix U U)⁻¹ * S.submatrix U U
  set Ms := (S.submatrix K K)⁻¹ * T.submatrix K K
  -- Step 1: the forward solution for `u`
  set w : ℕ → Fin ny → ℂ := fun t => -((T.submatrix U U)⁻¹ *ᵥ (c t ∘ U))
  obtain ⟨W, -, hW⟩ := ((hc.comp U).mulVec (T.submatrix U U)⁻¹).bound
  have hW' : ∀ t, ‖w t‖ ≤ W := fun t => by
    simp only [w, norm_neg]
    exact hW t
  set uF := fwdSum N w
  have huF : ∀ t, uF t = N *ᵥ uF (t + 1) + w t := fwdSum_rec hN hW'
  have huFs : IsStableSeq uF := isStableSeq_of_le (norm_fwdSum_le hN hW')
  -- Step 2: the backward recursion for `s`
  set v : ℕ → Fin nk → ℂ := fun t => (S.submatrix K K)⁻¹ *ᵥ
    (T.submatrix K U *ᵥ uF t - S.submatrix K U *ᵥ uF (t + 1) + c t ∘ K)
  have hv : IsStableSeq v := ((((huFs.mulVec _).sub ((huFs.shift 1).mulVec _)).add
    (hc.comp K)).mulVec _)
  set s₀ := (Z.submatrix K K)⁻¹ *ᵥ (k₀ - Z.submatrix K U *ᵥ uF 0)
  set sF : ℕ → Fin nk → ℂ := fun t => Nat.rec s₀ (fun t st => Ms *ᵥ st + v t) t
  have hsF : ∀ t, sF (t + 1) = Ms *ᵥ sF t + v t := fun t => rfl
  have hsFs : IsStableSeq sF := isStableSeq_of_rec hMs hv hsF
  have hZ1 : Z.submatrix K K * (Z.submatrix K K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hZ11)
  have hZ2 : (Z.submatrix K K)⁻¹ * Z.submatrix K K = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hZ11)
  have hK : ∀ (a : Fin nk → ℂ) (b : Fin ny → ℂ), Fin.append a b ∘ K = a :=
    fun a b => funext fun i => Fin.append_left a b i
  have hU : ∀ (a : Fin nk → ℂ) (b : Fin ny → ℂ), Fin.append a b ∘ U = b :=
    fun a b => funext fun i => Fin.append_right a b i
  refine ⟨fun t => Fin.append (sF t) (uF t), ⟨fun t => ?_, isStableSeq_append hsFs huFs,
    fun i => ?_⟩, ?_⟩
  · -- Step 3: the constructed sequence solves the system
    rw [eq_1_36 hS hT, hK, hK, hU, hU, eq_1_38 hS11, solve_fwd hT22]
    exact ⟨hsF t, huF t⟩
  · rw [mulVec_castAdd, hK, hU]
    change (Z.submatrix K K *ᵥ s₀ + Z.submatrix K U *ᵥ uF 0) i = k₀ i
    rw [Matrix.mulVec_mulVec, hZ1, Matrix.one_mulVec, sub_add_cancel]
  · rintro y ⟨hy, hys, hy0⟩
    have hblk := fun t => (eq_1_36 hS hT (y t) (y (t + 1)) (c t)).1 (hy t)
    -- `u` is the forward sum
    have hu : ∀ t, y t ∘ U = uF t :=
      eq_fwdSum hN hW' (hys.comp U) fun t => (solve_fwd hT22 _ _ _).1 (hblk t).2
    -- `s₀` is pinned down by `k₀`
    have hs0 : y 0 ∘ K = s₀ := by
      have h1 : Z.submatrix K K *ᵥ (y 0 ∘ K) + Z.submatrix K U *ᵥ (y 0 ∘ U) = k₀ :=
        funext fun i => by rw [← hy0 i, mulVec_castAdd]; rfl
      rw [hu 0] at h1
      calc y 0 ∘ K = (Z.submatrix K K)⁻¹ *ᵥ (Z.submatrix K K *ᵥ (y 0 ∘ K)) := by
            rw [Matrix.mulVec_mulVec, hZ2, Matrix.one_mulVec]
        _ = s₀ := by
            rw [show s₀ = (Z.submatrix K K)⁻¹ *ᵥ (k₀ - Z.submatrix K U *ᵥ uF 0) from rfl, ← h1,
              add_sub_cancel_right]
    have hs : ∀ t, y t ∘ K = sF t := by
      intro t
      induction t with
      | zero => exact hs0
      | succ t ih =>
        have := (eq_1_38 hS11 _ _ _ _ _).1 (hblk t).1
        rw [this, ih, hu, hu, hsF]
    funext t
    have hy' : y t = Fin.append (y t ∘ K) (y t ∘ U) := funext fun i =>
      Fin.addCases (fun i => (Fin.append_left (y t ∘ K) (y t ∘ U) i).symm)
        (fun i => (Fin.append_right (y t ∘ K) (y t ∘ U) i).symm) i
    rw [hy', hs, hu]

/-- Without forcing, a stable solution of the transformed system has `u_t = 0` and tends to zero
(the backward part is `s_t = (S₁₁⁻¹T₁₁)ᵗs₀`). -/
theorem klein_homog {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) {d : ℕ → Fin (nk + ny) → ℂ} (hd : IsStableSeq d)
    (h : ∀ t, S *ᵥ d (t + 1) = T *ᵥ d t) :
    (∀ t, d t ∘ Fin.natAdd nk = 0) ∧ Tendsto d atTop (𝓝 0) := by
  set K := Fin.castAdd (n := nk) ny
  set U := Fin.natAdd (m := ny) nk
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hMs := summable_Ms hS hT hord
  have hN := summable_Mu hS hT hord hdiag
  have hblk := fun t => (eq_1_36 hS hT (d t) (d (t + 1)) 0).1 (by rw [add_zero]; exact h t)
  have hu : ∀ t, d t ∘ U = 0 := by
    intro t
    have := eq_fwdSum hN (w := fun _ => 0) (W := 0) (fun _ => by simp) (hd.comp U)
      (fun t => by
        have := (solve_fwd hT22 _ _ _).1 (hblk t).2
        simpa using this) t
    rw [this]
    simp [fwdSum]
  set Ms := (S.submatrix K K)⁻¹ * T.submatrix K K
  have hs : ∀ t, d t ∘ K = (Ms ^ t) *ᵥ (d 0 ∘ K) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := (eq_1_38 hS11 _ _ _ _ _).1 (hblk t).1
      rw [this, hu, hu, ih, pow_succ', ← Matrix.mulVec_mulVec]
      simp [Ms, Matrix.mul_assoc]
      rfl
  refine ⟨hu, squeeze_zero_norm (a := fun t => ‖mclm (Ms ^ t)‖ * ‖d 0 ∘ K‖) (fun t => ?_) ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h1 : d t (K i) = (d t ∘ K) i := rfl
      rw [h1, hs]
      exact (norm_le_pi_norm _ i).trans (norm_mulVec_le _ _)
    · have h1 : d t (U i) = (d t ∘ U) i := rfl
      rw [h1, hu]
      simp only [Pi.zero_apply, norm_zero]
      positivity
  · simpa using hMs.tendsto_atTop_zero.mul_const ‖d 0 ∘ K‖

/-- Miao, (1.37) as corrected: in a stable solution of the transformed system,
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ c²_{t+j}`. The book prints `−T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ c²_{t+j}`, which
is wrong unless `T₂₂⁻¹` commutes with `S₂₂` (`eq_1_37_printed_false`). -/
theorem eq_1_37 {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) {c : ℕ → Fin (nk + ny) → ℂ} (hc : IsStableSeq c)
    {y : ℕ → Fin (nk + ny) → ℂ} (hy : IsStableSeq y) (h : ∀ t, S *ᵥ y (t + 1) = T *ᵥ y t + c t)
    (t : ℕ) :
    y t ∘ Fin.natAdd nk = -∑' j, (((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      S.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j *
        (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹) *ᵥ (c (t + j) ∘ Fin.natAdd nk) := by
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hN := summable_Mu hS hT hord hdiag
  obtain ⟨W, -, hW⟩ := ((hc.comp (Fin.natAdd nk)).mulVec
    (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹).bound
  have hW' : ∀ t, ‖-((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *ᵥ
      (c t ∘ Fin.natAdd nk))‖ ≤ W := fun t => by rw [norm_neg]; exact hW t
  rw [eq_fwdSum hN hW' (hy.comp _) (fun t => (solve_fwd hT22 _ _ _).1
    ((eq_1_36 hS hT _ _ _).1 (h t)).2) t, fwdSum, ← tsum_neg]
  simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]

/-- Miao, (1.39)–(1.40), p. 26: with `x_t = Zx*_t`, `k_t = Z₁₁s_t + Z₁₂u_t` and
`y_t = Z₂₁s_t + Z₂₂u_t`. -/
theorem eq_1_39_40 {nk ny : ℕ} (Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ)
    (xs : Fin (nk + ny) → ℂ) :
    (Z *ᵥ xs) ∘ Fin.castAdd ny =
        Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *ᵥ (xs ∘ Fin.castAdd ny) +
          Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk) ∧
      (Z *ᵥ xs) ∘ Fin.natAdd nk =
        Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *ᵥ (xs ∘ Fin.castAdd ny) +
          Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk) := by
  refine ⟨funext fun i => mulVec_castAdd Z xs i, funext fun i => ?_⟩
  simp only [Function.comp_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    Matrix.submatrix_apply]

/-! ### Theorem 1.4.5 -/

/-- The unitary change of variables `x* = Zᴴx` (Miao, p. 25): `x` solves (1.20) iff
`Sx*_{t+1} = Tx*_t + QCz_t` with `S = QAZ`, `T = QBZ`. -/
theorem isSolution_iff_transformed {n nz : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin nz) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℕ → Fin nz → ℂ) (x : ℕ → Fin n → ℂ) :
    IsSolution A B C z x ↔ ∀ t, (Q * A * Z) *ᵥ (star Z *ᵥ x (t + 1)) =
      (Q * B * Z) *ᵥ (star Z *ᵥ x t) + Q *ᵥ (C *ᵥ z t) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ),
      (Q * M * Z) *ᵥ (star Z *ᵥ v) = Q *ᵥ (M *ᵥ v) := fun M v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZZ, Matrix.mul_one,
      Matrix.mulVec_mulVec]
  simp only [IsSolution, key, ← Matrix.mulVec_add]
  refine forall_congr' fun t => ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (star Q *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQQ, Matrix.one_mul,
    Matrix.one_mulVec] using this

/-- Condition (iii) of Theorem 1.4.5 on the diagonal of a QZ form: no generalized eigenvalue on
the unit circle gives `|tᵢᵢ| ≠ |sᵢᵢ|` for every `i`. -/
theorem diag_off_circle {n : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ} (hreg : IsRegular A B)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (i : Fin n) :
    ‖(Q * B * Z) i i‖ ≠ ‖(Q * A * Z) i i‖ := by
  intro h
  by_cases hs : (Q * A * Z) i i = 0
  · rw [hs, norm_zero, norm_eq_zero] at h
    rcases diag_ne_zero_of_regular hreg hQ hZ hS hT i with h' | h'
    · exact h' hs
    · exact h' h
  · have hmem : (Q * B * Z) i i / (Q * A * Z) i i ∈ genEigenvalues A B := by
      rw [genEigenvalues_eq_diag hreg hQ hZ hS hT]
      exact ⟨i, hs, rfl⟩
    refine hcirc _ hmem ?_
    rw [norm_div, h, div_self (norm_ne_zero_iff.2 hs)]

/-- **Theorem 1.4.5** (Klein, Miao, p. 25). Let `(A, B)` be regular, with QZ form `S = QAZ`,
`T = QBZ` whose stable generalized eigenvalues come first, and partition `x_t = (k_t, y_t)` with
`k_t` the first `n_k` (predetermined) coordinates. Suppose (i) `n_s = n_k`, i.e. pair `i` is
stable iff `i < n_k` (`hord`, which also records the ordering); (ii) `Z₁₁` is invertible; (iii)
`(A, B)` has no generalized eigenvalue on the unit circle. Then for every `k₀` and every stable
`{z_t}`, (1.20) has a unique stable solution with initial predetermined block `k₀`. -/
theorem theorem_1_4_5 {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ} (hreg : IsRegular A B)
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (k₀ : Fin nk → ℂ)
    {z : ℕ → Fin nz → ℂ} (hz : IsStableSeq z) :
    ∃! x : ℕ → Fin (nk + ny) → ℂ,
      IsSolution A B C z x ∧ IsStableSeq x ∧ ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hyu⟩ := klein_core hS hT hord
    (diag_off_circle hreg hQ hZ hS hT hcirc) hZ11 ((hz.mulVec C).mulVec Q) k₀
  refine ⟨fun t => Z *ᵥ y t, ⟨(isSolution_iff_transformed hQ hZ z _).2 fun t => ?_,
    hy2.mulVec Z, hy3⟩, ?_⟩
  · simpa only [Matrix.mulVec_mulVec, hZZ', Matrix.one_mulVec] using hy1 t
  · rintro x ⟨hx1, hx2, hx3⟩
    have hback : ∀ t, Z *ᵥ (star Z *ᵥ x t) = x t := fun t => by
      rw [Matrix.mulVec_mulVec, hZZ, Matrix.one_mulVec]
    have := hyu (fun t => star Z *ᵥ x t) ⟨(isSolution_iff_transformed hQ hZ z x).1 hx1,
      hx2.mulVec _, fun i => by rw [hback]; exact hx3 i⟩
    funext t
    rw [← this, hback]

/-! ### Steady state (the analogue of Corollary 1.4.1) -/

/-- Under condition (iii) of Theorem 1.4.5, `1` is not a generalized eigenvalue, so `A − B` is
invertible and the steady state `x̄ = (A − B)⁻¹Cz̄` of (1.21) is defined. -/
theorem det_sub_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) : (A - B).det ≠ 0 := by
  intro h
  have h1 : IsGenEigenvalue A B 1 := by
    rw [isGenEigenvalue_iff_det, one_smul, ← neg_sub, Matrix.det_neg, h, mul_zero]
  exact hcirc 1 h1 (by simp)

/-- **Corollary 1.4.1 for singular systems** (Miao, p. 27, stated but not written out in the
book). Under the conditions of Theorem 1.4.5 and Assumption 1.4.2 (`z_t = z̄` eventually),
`A − B` is invertible and every stable solution of (1.20) converges to the steady state
`x̄ = (A − B)⁻¹Cz̄`. Condition (ii) (`Z₁₁` invertible) is not needed for the convergence. -/
theorem corollary_1_4_1_singular {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ} (hreg : IsRegular A B)
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) {z : ℕ → Fin nz → ℂ} {zbar : Fin nz → ℂ}
    (hzc : EventuallyConst z zbar) {x : ℕ → Fin (nk + ny) → ℂ} (hx : IsSolution A B C z x)
    (hxs : IsStableSeq x) :
    (A - B).det ≠ 0 ∧ Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (C *ᵥ zbar))) := by
  have hdet := det_sub_ne_zero hcirc
  refine ⟨hdet, ?_⟩
  set xbar := (A - B)⁻¹ *ᵥ (C *ᵥ zbar)
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hxbar : IsSolution A B C (fun _ => zbar) (fun _ => xbar) := fun _ => by
    have h1 : (A - B) *ᵥ xbar = C *ᵥ zbar := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    rw [Matrix.sub_mulVec] at h1
    rw [← h1]
    abel
  obtain ⟨T₀, hT₀⟩ := hzc
  set d : ℕ → Fin (nk + ny) → ℂ := fun t => star Z *ᵥ (x (t + T₀) - xbar)
  have hd : IsStableSeq d :=
    ((hxs.shift T₀).sub (isStableSeq_of_le (x := fun _ => xbar) fun _ => le_rfl)).mulVec _
  have e2 := (isSolution_iff_transformed hQ hZ _ _).1 hxbar 0
  have hdeq : ∀ t, (Q * A * Z) *ᵥ d (t + 1) = (Q * B * Z) *ᵥ d t := by
    intro t
    have e1 := (isSolution_iff_transformed hQ hZ z x).1 hx (t + T₀)
    rw [hT₀ (t + T₀) (by omega)] at e1
    simp only [d, Matrix.mulVec_sub, show t + 1 + T₀ = t + T₀ + 1 by ring, e1, e2]
    abel
  obtain ⟨-, hlim⟩ := klein_homog hS hT hord (diag_off_circle hreg hQ hZ hS hT hcirc) hd hdeq
  have h3 : ∀ t, Z *ᵥ d t = x (t + T₀) - xbar := fun t => by
    simp only [d, Matrix.mulVec_mulVec, hZZ, Matrix.one_mulVec]
  have h4 : Tendsto (fun t => x (t + T₀) - xbar) atTop (𝓝 0) := by
    have h2 := ((mclm Z).continuous.tendsto 0).comp hlim
    simpa [Function.comp_def, mclm_apply, h3] using h2
  have h5 := h4.add_const xbar
  simp only [sub_add_cancel, zero_add] at h5
  exact (tendsto_add_atTop_iff_nat T₀).1 h5

/-! ### Real data -/

theorem map_ofReal_mulVec {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (v : κ → ℝ) :
    M.map Complex.ofRealHom *ᵥ (fun j => (v j : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) :=
  funext fun i => (RingHom.map_mulVec Complex.ofRealHom M v i).symm

theorem norm_ofReal_vec {m : ℕ} (v : Fin m → ℝ) : ‖(fun i => (v i : ℂ))‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [Complex.norm_real]
    exact norm_le_pi_norm v i
  · rw [← Complex.norm_real]
    exact norm_le_pi_norm (fun i => (v i : ℂ)) i

/-- A real sequence solves the real system iff its complexification solves the complexified one. -/
theorem isSolution_ofReal_iff {n nz : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin n) (Fin nz) ℝ} (z : ℕ → Fin nz → ℝ) (x : ℕ → Fin n → ℝ) :
    IsSolution A B C z x ↔ IsSolution (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
      (C.map Complex.ofRealHom) (fun t i => (z t i : ℂ)) (fun t i => (x t i : ℂ)) := by
  simp only [IsSolution, map_ofReal_mulVec]
  refine forall_congr' fun t => ⟨fun h => by rw [h]; funext i; simp, fun h => funext fun i => ?_⟩
  have := congrFun h i
  simp only [Pi.add_apply] at this
  exact_mod_cast this

/-- **Theorem 1.4.5, real data** (Miao, p. 25, where `A`, `B`, `C`, `z`, `k₀` are real): the QZ
form is complex, but the unique stable solution is real, because its complex conjugate is
another stable solution with the same `k₀`. -/
theorem theorem_1_4_5_real {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℝ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℝ}
    (hreg : IsRegular (A.map Complex.ofRealHom) (B.map Complex.ofRealHom))
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A.map Complex.ofRealHom * Z).IsUpperTriangular)
    (hT : (Q * B.map Complex.ofRealHom * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔
      ‖(Q * B.map Complex.ofRealHom * Z) i i‖ < ‖(Q * A.map Complex.ofRealHom * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues (A.map Complex.ofRealHom) (B.map Complex.ofRealHom),
      ‖lam‖ ≠ 1) (k₀ : Fin nk → ℝ) {z : ℕ → Fin nz → ℝ} (hz : IsStableSeq z) :
    ∃! x : ℕ → Fin (nk + ny) → ℝ,
      IsSolution A B C z x ∧ IsStableSeq x ∧ ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hzc : IsStableSeq fun t i => (z t i : ℂ) := by
    obtain ⟨M, hM, h⟩ := hz
    exact ⟨M, hM, fun t => by rw [norm_ofReal_vec]; exact h t⟩
  obtain ⟨xc, ⟨h1, h2, h3⟩, hu⟩ := theorem_1_4_5 (C := C.map Complex.ofRealHom) hreg hQ hZ hS hT
    hord hZ11 hcirc (fun i => (k₀ i : ℂ)) hzc
  -- the conjugate is another stable solution
  have hconj : (fun t i => (starRingEnd ℂ) (xc t i)) = xc := by
    refine hu _ ⟨fun t => ?_, ?_, fun i => by simp [h3 i]⟩
    · have hmap : ∀ {κ : Type} [Fintype κ] (M : Matrix (Fin (nk + ny)) κ ℝ) (v : κ → ℂ),
          M.map Complex.ofRealHom *ᵥ (fun j => (starRingEnd ℂ) (v j)) =
            fun i => (starRingEnd ℂ) ((M.map Complex.ofRealHom *ᵥ v) i) := by
        intro κ _ M v
        funext i
        rw [RingHom.map_mulVec]
        congr 1
        ext a b
        simp
      have hz' : (fun j => (z t j : ℂ)) = fun j => (starRingEnd ℂ) ((z t j : ℂ)) :=
        funext fun j => (Complex.conj_ofReal _).symm
      change _ = _ + C.map Complex.ofRealHom *ᵥ (fun j => (z t j : ℂ))
      rw [hz', hmap, hmap, hmap, h1 t]
      funext i
      simp only [Pi.add_apply, map_add]
    · obtain ⟨M, hM, h⟩ := h2
      refine ⟨M, hM, fun t => ?_⟩
      have : ‖fun i => (starRingEnd ℂ) (xc t i)‖ = ‖xc t‖ := by
        refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
        · rw [Complex.norm_conj]
          exact norm_le_pi_norm (xc t) i
        · rw [← Complex.norm_conj]
          exact norm_le_pi_norm (fun i => (starRingEnd ℂ) (xc t i)) i
      rw [this]
      exact h t
  have hreal : ∀ t i, ((xc t i).re : ℂ) = xc t i := fun t i =>
    Complex.conj_eq_iff_re.1 (congrFun (congrFun hconj t) i)
  refine ⟨fun t i => (xc t i).re, ⟨?_, ?_, fun i => ?_⟩, ?_⟩
  · rw [isSolution_ofReal_iff]
    simpa only [hreal] using h1
  · obtain ⟨M, hM, h⟩ := h2
    exact ⟨M, hM, fun t => by
      rw [← norm_ofReal_vec]
      simpa only [hreal] using h t⟩
  · have := congrArg Complex.re (h3 i)
    simpa using this
  · rintro x ⟨hx1, hx2, hx3⟩
    have hxc : (fun t i => (x t i : ℂ)) = xc := hu _ ⟨(isSolution_ofReal_iff z x).1 hx1, by
      obtain ⟨M, hM, h⟩ := hx2
      exact ⟨M, hM, fun t => by rw [norm_ofReal_vec]; exact h t⟩,
      fun i => by simp [hx3 i]⟩
    funext t i
    have := congrArg Complex.re (congrFun (congrFun hxc t) i)
    simpa using this

/-- Miao, p. 26: in any solution with initial predetermined block `k₀`,
`s₀ = Z₁₁⁻¹(k₀ − Z₁₂u₀)`. -/
theorem eq_s0 {nk ny : ℕ} {Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0) (xs : Fin (nk + ny) → ℂ)
    (k₀ : Fin nk → ℂ) (h : (Z *ᵥ xs) ∘ Fin.castAdd ny = k₀) :
    xs ∘ Fin.castAdd ny = (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *ᵥ
      (k₀ - Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk)) := by
  rw [← h, (eq_1_39_40 Z xs).1, add_sub_cancel_right, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hZ11), Matrix.one_mulVec]

/-! ### Remarks on p. 27 -/

/-- Miao, p. 27: with `z_{t+1} = Φz_t`, the system for `(z_t, x_t)` with matrices
`[[I, 0], [0, A]]` and `[[Φ, 0], [C, B]]` and no forcing is equivalent to (1.20) together with
the law of motion of `z`. -/
theorem remark_augmented {K : Type*} [CommRing K] {n nz : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin n) (Fin nz) K) (Φ : Matrix (Fin nz) (Fin nz) K) (z : ℕ → Fin nz → K)
    (x : ℕ → Fin n → K) :
    IsSolution (Matrix.fromBlocks 1 0 0 A) (Matrix.fromBlocks Φ 0 C B)
        (0 : Matrix (Fin nz ⊕ Fin n) (Fin 0) K) (fun _ => 0) (fun t => Sum.elim (z t) (x t)) ↔
      (∀ t, z (t + 1) = Φ *ᵥ z t) ∧ IsSolution A B C z x := by
  simp only [IsSolution, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.mulVec_zero]
  rw [← forall_and]
  refine forall_congr' fun t => ?_
  rw [Sum.elim_eq_iff, add_comm (C *ᵥ z t)]

/-- Miao, p. 27 ("we have `u_t = 0`"): without forcing (as in the augmented system), every
stable solution has `u_t = 0`, where `x*_t = Zᴴx_t = (s_t, u_t)`. -/
theorem remark_u_eq_zero {nk ny : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) {x : ℕ → Fin (nk + ny) → ℂ}
    (hx : ∀ t, A *ᵥ x (t + 1) = B *ᵥ x t) (hxs : IsStableSeq x) (t : ℕ) :
    (star Z *ᵥ x t) ∘ Fin.natAdd nk = 0 := by
  have hsol : IsSolution A B (0 : Matrix (Fin (nk + ny)) (Fin 0) ℂ) (fun _ => 0) x :=
    fun t => by rw [hx t, Matrix.zero_mulVec, add_zero]
  have h := (isSolution_iff_transformed hQ hZ _ x).1 hsol
  simp only [Matrix.mulVec_zero, add_zero] at h
  exact (klein_homog hS hT hord (diag_off_circle hreg hQ hZ hS hT hcirc) (hxs.mulVec _) h).1 t

/-! ### The printed form of (1.37) is wrong -/

/-- **Counterexample to (1.37) as printed** (Miao, p. 26). The book's
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ c²_{t+j}` need not solve `S₂₂u_{t+1} = T₂₂u_t + c²_t`: take
`S₂₂ = [[0, 1], [0, 0]]`, `T₂₂ = diag(1, 2)` (both pairs unstable: infinite eigenvalues) and
`c²_t = e₂` at `t = 1`, zero otherwise. The correct formula is `eq_1_37`. -/
theorem eq_1_37_printed_false :
    ∃ (S₂₂ T₂₂ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℕ → Fin 2 → ℂ),
      S₂₂.IsUpperTriangular ∧ T₂₂.IsUpperTriangular ∧ (∀ i, ‖S₂₂ i i‖ < ‖T₂₂ i i‖) ∧
      IsStableSeq c ∧
      ¬ ∀ t, S₂₂ *ᵥ (-(T₂₂⁻¹ *ᵥ ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (t + 1 + j))) =
        T₂₂ *ᵥ (-(T₂₂⁻¹ *ᵥ ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (t + j))) + c t := by
  set S₂₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  set T₂₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]
  set c : ℕ → Fin 2 → ℂ := fun t => if t = 1 then ![0, 1] else 0
  have hTinv : T₂₂⁻¹ = !![1, 0; 0, 1 / 2] := Matrix.inv_eq_right_inv (by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [T₂₂, Matrix.mul_apply, Fin.sum_univ_two])
  have hN : T₂₂⁻¹ * S₂₂ = !![0, 1; 0, 0] := by
    rw [hTinv]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [S₂₂, Matrix.mul_apply, Fin.sum_univ_two]
  have hc1 : ∀ j, j ≠ 1 → c j = 0 := fun j hj => by simp [c, hj]
  have hsum0 : ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (0 + j) = ![1, 0] := by
    rw [tsum_eq_single 1 fun j hj => by rw [zero_add, hc1 j hj, Matrix.mulVec_zero]]
    rw [hN]
    ext i; fin_cases i <;> simp [c, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsum1 : ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (0 + 1 + j) = ![0, 1] := by
    rw [tsum_eq_single 0 fun j hj => by rw [hc1 _ (by omega), Matrix.mulVec_zero]]
    simp [c]
  refine ⟨S₂₂, T₂₂, c, ?_, ?_, ?_, ?_, fun h => ?_⟩
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [S₂₂]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [T₂₂]
  · intro i; fin_cases i <;> norm_num [S₂₂, T₂₂]
  · refine isStableSeq_of_le (K := 1) fun t => ?_
    by_cases ht : t = 1
    · simp only [c, ht, ↓reduceIte]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      fin_cases i <;> simp
    · simp [c, ht]
  · have h0 := congrFun (h 0) 0
    rw [hsum0, hsum1, hTinv] at h0
    norm_num [S₂₂, T₂₂, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0

/-! ### The Cagan example (p. 24) -/

/-- The matrix `A` of the Cagan model (Miao, p. 24). -/
def caganA {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- The matrix `B` of the Cagan model, with interest semi-elasticity `α`. -/
def caganB {K : Type*} [CommRing K] (α : K) : Matrix (Fin 2) (Fin 2) K := !![1, 1; α, -1]

/-- The matrix `C` of the Cagan model (one forcing variable, the money stock `m_t`). -/
def caganC {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 1) K := !![0; 1]

/-- **Cagan model** (Miao, p. 24): with `x_t = (R_t, p_t)` and `z_t = m_t`, (1.20) with the
matrices above is the Fisher equation `R_t = p_{t+1} − p_t` together with money market
equilibrium `m_t − p_t = −αR_t`. -/
theorem example_cagan_iff (α : ℝ) (R p m : ℕ → ℝ) :
    IsSolution caganA (caganB α) caganC (fun t => ![m t]) (fun t => ![R t, p t]) ↔
      ∀ t, R t = p (t + 1) - p t ∧ m t - p t = -α * R t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, Fin.forall_fin_two]
  have e1 : (caganA *ᵥ ![R (t + 1), p (t + 1)]) 0 = p (t + 1) := by
    simp [caganA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e2 : (caganA *ᵥ ![R (t + 1), p (t + 1)]) 1 = 0 := by
    simp [caganA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e3 : (caganB α *ᵥ ![R t, p t] + caganC *ᵥ ![m t]) 0 = R t + p t := by
    simp [caganB, caganC]
  have e4 : (caganB α *ᵥ ![R t, p t] + caganC *ᵥ ![m t]) 1 = α * R t - p t + m t := by
    simp [caganB, caganC]
    ring
  rw [e1, e2, e3, e4]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Miao, p. 24: in the Cagan model `A` is singular. -/
theorem example_cagan_det {K : Type*} [CommRing K] :
    (caganA : Matrix (Fin 2) (Fin 2) K).det = 0 := by
  simp [caganA, Matrix.det_fin_two]

/-- The Cagan pencil is regular for every `α`: `det(A − B) = −1`. -/
theorem example_cagan_regular {K : Type*} [Field K] (α : K) : IsRegular caganA (caganB α) :=
  ⟨1, by simp [caganA, caganB, Matrix.det_fin_two]⟩

/-- The generalized eigenvalues of the Cagan pencil: `det(B − λA) = −1 − α(1 − λ)`, so for
`α ≠ 0` the only generalized eigenvalue is `1 + 1/α` (the second is infinite). -/
theorem example_cagan_genEigenvalues {α : ℂ} (hα : α ≠ 0) :
    genEigenvalues caganA (caganB α) = {1 + α⁻¹} := by
  ext lam
  change IsGenEigenvalue _ _ lam ↔ lam = 1 + α⁻¹
  have hdet : (caganB α - lam • caganA).det = -1 - α * (1 - lam) := by
    simp [caganA, caganB, Matrix.det_fin_two]
    ring
  rw [isGenEigenvalue_iff_det, hdet]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- For `α = 0` the Cagan pencil has no finite generalized eigenvalue (both are infinite). -/
theorem example_cagan_genEigenvalues_zero : genEigenvalues caganA (caganB (0 : ℂ)) = ∅ := by
  ext lam
  change IsGenEigenvalue _ _ lam ↔ False
  rw [isGenEigenvalue_iff_det]
  simp [caganA, caganB, Matrix.det_fin_two]

end Miao.NewKeynesian
