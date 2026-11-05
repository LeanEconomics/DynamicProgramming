/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Singular
import RationalExpectations.KleinMartingales

/-!
# The Klein method for linear rational expectations models

Miao, §2.3.2, pp. 56–57: the system `A E_t x_{t+1} = Bx_t + Cz_t` (2.11) with `A` possibly
singular, in the abstract setting of `Basics` with `𝕜 = ℂ` (the QZ form is complex): `V` is a
complete complex normed space of random variables with conditional expectations
`E : CondExpSystem ℂ V`, a vector random variable is `Fin m → V` with the max norm.

**Representation.** As in the deterministic `Singular`, `x_t = (k_t, y_t)` is indexed by
`Fin (nk + ny)`, the blocks are `Matrix.submatrix` along `Fin.castAdd ny` and `Fin.natAdd nk`, and
`x*_t = Zᴴx_t = (s_t, u_t)`.

* `klein_stochastic`: under the hypotheses of Theorem 1.4.5 (regular pencil, ordered QZ form with
  (i) `n_s = n_k`, (ii) `Z₁₁` invertible, (iii) no generalized eigenvalue on the unit circle), for
  every stable adapted `{z_t}`, every stable martingale-difference prediction error `{ξ_t}` and
  every `F₀`-measurable `k₀`, there is exactly one stable adapted solution of (2.11) whose
  predetermined block `k_t` is predetermined with prediction error `ξ` (Definition 2.3.4) and
  starts at `k₀`. The proof follows the book's modified steps: the forward solution (2.17)
  (`eq_2_17`, `klS_fwd`, `klS_eq_fwd`), the replacement of (1.38) (`eq_klein_Es`), the prediction
  error identity (`eq_klein_xi`), the formula for `s_{t+1}` (`eq_klein_s`) and
  `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}` (`eq_klein_k`).
* `klein_stochastic_real`: real data. `V` carries a conjugation `cj` (conjugate-linear, isometric,
  commuting with every `E_t`; for complex `L¹` it is pointwise conjugation); if `A`, `B`, `C` are
  real and `z`, `ξ`, `k₀` are fixed by `cj`, the unique solution is fixed by `cj` (real).

**Corrections.**
* (2.17) repeats the misprint of (1.37): it reads `u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂CE_t z_{t+j}`;
  the correct forward solution is `u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂CE_t z_{t+j}` (`eq_2_17`). The
  printed one fails already for the deterministic system `E_t = id` (`eq_2_17_printed_false`).
* The formulas for `E_t s_{t+1}`, the prediction error `ξ_{t+1}` and `s_{t+1}` on pp. 56–57 are
  correct as printed (every term and sign checked).
* The book's hypotheses leave implicit that `ξ_{t+1}` must be `F_{t+1}`-measurable (needed for
  the solution to be adapted) and that `ξ` must be stable (otherwise `k` is not); both are
  assumed.
-/

open Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Matrices acting on vectors of random variables -/

theorem klS_matAct_sub {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x y : κ → V) :
    matAct M (x - y) = matAct M x - matAct M y := by
  funext i
  simp [matAct, smul_sub, Finset.sum_sub_distrib]

theorem klS_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct M (-x) = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem klS_matAct_zero {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) :
    matAct M (0 : κ → V) = 0 := by
  funext i
  simp [matAct]

theorem klS_zero_matAct {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ ℂ) x = 0 := by
  funext i
  simp [matAct]

theorem klS_add_matAct {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℂ) (x : κ → V) :
    matAct (M + N) x = matAct M x + matAct N x := by
  funext i
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem klS_sub_matAct {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℂ) (x : κ → V) :
    matAct (M - N) x = matAct M x - matAct N x := by
  funext i
  simp [matAct, sub_smul, Finset.sum_sub_distrib]

theorem klS_neg_matAct {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct (-M) x = -matAct M x := by
  funext i
  simp [matAct, neg_smul, Finset.sum_neg_distrib]

/-- Rows `f` of `Mv`: `(Mv)∘f = M_{f,·}v`. -/
theorem klS_matAct_comp {ι ι' κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (f : ι' → ι)
    (x : κ → V) : matAct M x ∘ f = matAct (M.submatrix f id) x := rfl

/-- `M` as a continuous linear map on vectors of random variables. -/
noncomputable def klS_matCLM {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) :
    (κ → V) →L[ℂ] (ι → V) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : κ => V) j

theorem klS_matCLM_apply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    klS_matCLM M x = matAct M x := by
  funext i
  simp [klS_matCLM, matAct]

theorem klS_matAct_sum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (s : Finset α)
    (f : α → κ → V) : matAct M (∑ a ∈ s, f a) = ∑ a ∈ s, matAct M (f a) := by
  rw [← klS_matCLM_apply, map_sum]
  simp only [klS_matCLM_apply]

theorem klS_matAct_inv_mul {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0)
    (x : Fin m → V) : matAct M⁻¹ (matAct M x) = x := by
  rw [matAct_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h), matAct_one]

theorem klS_matAct_mul_inv {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0)
    (x : Fin m → V) : matAct M (matAct M⁻¹ x) = x := by
  rw [matAct_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h), matAct_one]

/-- Column blocks: `Mv = M_{·,K}v_K + M_{·,U}v_U`, restricted to rows `f`. -/
theorem klS_matAct_blocks {ι κ : Type*} {a b : ℕ} (M : Matrix ι (Fin (a + b)) ℂ) (f : κ → ι)
    (v : Fin (a + b) → V) :
    matAct M v ∘ f = matAct (M.submatrix f (Fin.castAdd b)) (v ∘ Fin.castAdd b) +
      matAct (M.submatrix f (Fin.natAdd a)) (v ∘ Fin.natAdd a) := by
  funext i
  simp only [matAct, Function.comp_apply, Pi.add_apply, Fin.sum_univ_add, Matrix.submatrix_apply]

/-- For upper triangular `M`, the lower block row is `(Mv)_U = M_{UU}v_U`. -/
theorem klS_matAct_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) (v : Fin (a + b) → V) :
    matAct M v ∘ Fin.natAdd a = matAct (M.submatrix (Fin.natAdd a) (Fin.natAdd a))
      (v ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  have h0 : M.submatrix (Fin.natAdd a) (Fin.castAdd b) = 0 := by
    ext i j
    apply hM
    rw [Fin.lt_def]
    change (j : ℕ) < a + (i : ℕ)
    omega
  rw [h0, klS_zero_matAct, zero_add]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_ext_blocks {a b : ℕ} {f g : Fin (a + b) → V}
    (h1 : f ∘ Fin.castAdd b = g ∘ Fin.castAdd b) (h2 : f ∘ Fin.natAdd a = g ∘ Fin.natAdd a) :
    f = g := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact congrFun h1 i
  · exact congrFun h2 i

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_append_castAdd {a b : ℕ} (x : Fin a → V) (y : Fin b → V) :
    Fin.append x y ∘ Fin.castAdd b = x :=
  funext fun i => Fin.append_left x y i

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_append_natAdd {a b : ℕ} (x : Fin a → V) (y : Fin b → V) :
    Fin.append x y ∘ Fin.natAdd a = y :=
  funext fun i => Fin.append_right x y i

/-! ### Conditional expectations of vectors -/

theorem klS_Evec_add {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x y : ι → V) :
    Evec E t (x + y) = Evec E t x + Evec E t y := by
  funext i
  simp [Evec]

theorem klS_Evec_sub {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x y : ι → V) :
    Evec E t (x - y) = Evec E t x - Evec E t y := by
  funext i
  simp [Evec]

theorem klS_Evec_neg {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) :
    Evec E t (-x) = -Evec E t x := by
  funext i
  simp [Evec]

theorem klS_Evec_zero {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) :
    Evec E t (0 : ι → V) = 0 := by
  funext i
  simp [Evec]

theorem klS_Evec_idem {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) :
    Evec E t (Evec E t x) = Evec E t x :=
  funext fun i => E.idem t (x i)

theorem klS_Evec_tower_le {ι : Type*} (E : CondExpSystem ℂ V) {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E s (Evec E t x) = Evec E s x :=
  funext fun i => E.tower_le_apply h (x i)

theorem klS_Evec_tower_ge {ι : Type*} (E : CondExpSystem ℂ V) {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E t (Evec E s x) = Evec E s x :=
  funext fun i => E.tower_ge_apply h (x i)

theorem klS_Evec_comp {ι κ : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) (f : κ → ι) :
    Evec E t (x ∘ f) = Evec E t x ∘ f := rfl

theorem klS_Evec_append {a b : ℕ} (E : CondExpSystem ℂ V) (t : ℕ) (x : Fin a → V)
    (y : Fin b → V) : Evec E t (Fin.append x y) = Fin.append (Evec E t x) (Evec E t y) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Evec]

/-- `F_t`-measurable variables are `F_{t+1}`-measurable. -/
theorem klS_adapted_succ {ι : Type*} (E : CondExpSystem ℂ V) {t : ℕ} {x : ι → V}
    (h : Evec E t x = x) : Evec E (t + 1) x = x := by
  rw [← h, klS_Evec_tower_ge E (Nat.le_succ t)]

/-- `E_t` as a continuous linear map on vectors. -/
noncomputable def klS_EvecCLM (E : CondExpSystem ℂ V) (t : ℕ) (ι : Type*) :
    (ι → V) →L[ℂ] (ι → V) :=
  ContinuousLinearMap.pi fun i => (E.E t).comp (ContinuousLinearMap.proj i)

theorem klS_EvecCLM_apply (E : CondExpSystem ℂ V) (t : ℕ) {ι : Type*} (x : ι → V) :
    klS_EvecCLM E t ι x = Evec E t x := rfl

/-! ### Norms and stability -/

/-- The entry sum `∑ᵢⱼ |Mᵢⱼ|`, which bounds the action of `M` on vectors of random variables. -/
noncomputable def klS_ent {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖

theorem klS_ent_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    0 ≤ klS_ent M := by
  unfold klS_ent
  positivity

theorem klS_norm_matAct_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ)
    (v : κ → V) : ‖matAct M v‖ ≤ klS_ent M * ‖v‖ := by
  unfold klS_ent
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖matAct M v i‖ = ‖∑ j, M i j • v j‖ := rfl
    _ ≤ ∑ j, ‖M i j • v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
        (norm_nonneg _)

theorem klS_norm_Evec_le {ι : Type*} [Fintype ι] (E : CondExpSystem ℂ V) (t : ℕ) (v : ι → V) :
    ‖Evec E t v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (E.norm_apply_le t (v i)).trans (norm_le_pi_norm v i)

omit [NormedSpace ℂ V] in
theorem klS_stable_bound {ι : Type*} [Fintype ι] {x : ℕ → ι → V} (h : IsStableProc x) :
    ∃ K, 0 ≤ K ∧ ∀ t, ‖x t‖ ≤ K := by
  obtain ⟨M, hM, hx⟩ := h
  exact ⟨M, hM.le, fun t => (pi_norm_le_iff_of_nonneg hM.le).2 fun i => (hx t i).le⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_of_le {ι : Type*} [Fintype ι] {x : ℕ → ι → V} {K : ℝ}
    (h : ∀ t, ‖x t‖ ≤ K) : IsStableProc x :=
  isStableProc_of_uniformly_bounded fun t i => (norm_le_pi_norm (x t) i).trans (h t)

omit [NormedSpace ℂ V] in
theorem klS_stable_add {ι : Type*} [Finite ι] {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t + y t := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  obtain ⟨L, -, hL⟩ := klS_stable_bound hy
  exact klS_stable_of_le fun t => (norm_add_le _ _).trans (add_le_add (hK t) (hL t))

omit [NormedSpace ℂ V] in
theorem klS_stable_sub {ι : Type*} [Finite ι] {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t - y t := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  obtain ⟨L, -, hL⟩ := klS_stable_bound hy
  exact klS_stable_of_le fun t => (norm_sub_le _ _).trans (add_le_add (hK t) (hL t))

theorem klS_stable_matAct {ι κ : Type*} [Finite ι] [Fintype κ] {x : ℕ → κ → V}
    (hx : IsStableProc x) (M : Matrix ι κ ℂ) : IsStableProc fun t => matAct M (x t) := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  exact klS_stable_of_le fun t => (klS_norm_matAct_le M (x t)).trans
    (mul_le_mul_of_nonneg_left (hK t) (klS_ent_nonneg M))

theorem klS_stable_Evec {ι : Type*} [Finite ι] (E : CondExpSystem ℂ V) {x : ℕ → ι → V}
    (hx : IsStableProc x) (k : ℕ) : IsStableProc fun t => Evec E t (x (t + k)) := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  exact klS_stable_of_le fun t => (klS_norm_Evec_le E t _).trans (hK _)

omit [NormedSpace ℂ V] in
theorem klS_stable_shift {ι : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (k : ℕ) :
    IsStableProc fun t => x (t + k) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t => h _⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_comp {ι κ : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (f : κ → ι) :
    IsStableProc fun t => x t ∘ f := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => h t (f i)⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_append {a b : ℕ} {s : ℕ → Fin a → V} {u : ℕ → Fin b → V}
    (hs : IsStableProc s) (hu : IsStableProc u) :
    IsStableProc fun t => Fin.append (s t) (u t) := by
  obtain ⟨K, hK, hs⟩ := hs
  obtain ⟨L, hL, hu⟩ := hu
  refine ⟨K + L, by positivity, fun t i => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change ‖Fin.append (s t) (u t) (Fin.castAdd b i)‖ < K + L
    rw [Fin.append_left]
    linarith [hs t i]
  · change ‖Fin.append (s t) (u t) (Fin.natAdd a i)‖ < K + L
    rw [Fin.append_right]
    linarith [hu t i]

/-! ### Matrix norms -/

theorem klS_entry_le_mclm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i k : Fin m) :
    ‖M i k‖ ≤ ‖mclm M‖ := by
  have h1 : (M *ᵥ Pi.single k 1) i = M i k := by simp [Matrix.mulVec_single]
  have h2 : ‖(Pi.single k (1 : ℂ) : Fin m → ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj]
  calc ‖M i k‖ = ‖(M *ᵥ Pi.single k 1) i‖ := by rw [h1]
    _ ≤ ‖M *ᵥ Pi.single k 1‖ := norm_le_pi_norm _ i
    _ ≤ ‖mclm M‖ * ‖(Pi.single k (1 : ℂ) : Fin m → ℂ)‖ := norm_mulVec_le _ _
    _ ≤ ‖mclm M‖ := mul_le_of_le_one_right (norm_nonneg _) h2

theorem klS_ent_le_mclm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    klS_ent M ≤ (m * m : ℝ) * ‖mclm M‖ := by
  calc klS_ent M ≤ ∑ _i : Fin m, ∑ _j : Fin m, ‖mclm M‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => klS_entry_le_mclm M i j
    _ = (m * m : ℝ) * ‖mclm M‖ := by simp [Finset.sum_const, mul_assoc]

theorem klS_summable_ent {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (h : Summable fun j => ‖mclm (N ^ j)‖) : Summable fun j => klS_ent (N ^ j) :=
  Summable.of_nonneg_of_le (fun _ => klS_ent_nonneg _) (fun _ => klS_ent_le_mclm _)
    (h.mul_left _)

/-! ### The forward solution -/

/-- The forward sum `∑ⱼ Nʲ E_t w_{t+j}`. -/
noncomputable def klS_fwd (E : CondExpSystem ℂ V) {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ)
    (w : ℕ → Fin m → V) (t : ℕ) : Fin m → V :=
  ∑' j, matAct (N ^ j) (Evec E t (w (t + j)))

theorem klS_fwd_summable [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    Summable fun j => matAct (N ^ j) (Evec E t (w (t + j))) :=
  Summable.of_norm_bounded (hN.mul_right W) fun _ => (klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))

theorem klS_norm_fwd_le [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    ‖klS_fwd E N w t‖ ≤ (∑' j, klS_ent (N ^ j)) * W := by
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded (hN.mul_right W).hasSum fun j => (klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))

/-- The forward sum is adapted: `E_t u_t = u_t`. -/
theorem klS_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    Evec E t (klS_fwd E N w t) = klS_fwd E N w t := by
  unfold klS_fwd
  rw [← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin m)).map_tsum (klS_fwd_summable E hN hw t)]
  simp only [klS_EvecCLM_apply, Evec_matAct, klS_Evec_idem]

/-- The forward sum solves `u_t = N E_t u_{t+1} + w_t` for adapted `w`. -/
theorem klS_fwd_rec [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (hwa : ∀ t, Evec E t (w t) = w t)
    (t : ℕ) : klS_fwd E N w t = matAct N (Evec E t (klS_fwd E N w (t + 1))) + w t := by
  have h1 : Evec E t (klS_fwd E N w (t + 1)) =
      ∑' j, matAct (N ^ j) (Evec E t (w (t + 1 + j))) := by
    unfold klS_fwd
    rw [← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin m)).map_tsum
      (klS_fwd_summable E hN hw (t + 1))]
    simp only [klS_EvecCLM_apply, Evec_matAct, klS_Evec_tower_le E (Nat.le_succ t)]
  have hs : Summable fun j => matAct (N ^ j) (Evec E t (w (t + 1 + j))) :=
    Summable.of_norm_bounded (hN.mul_right W) fun _ => (klS_norm_matAct_le _ _).trans
      (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))
  rw [h1, ← klS_matCLM_apply, (klS_matCLM N).map_tsum hs]
  unfold klS_fwd
  rw [(klS_fwd_summable E hN hw t).tsum_eq_zero_add]
  simp only [klS_matCLM_apply, matAct_mul, pow_zero, matAct_one, add_zero, hwa]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_succ', show t + (j + 1) = t + 1 + j by ring]

/-- Any stable adapted solution of `u_t = N E_t u_{t+1} + w_t` is the forward sum, when the powers
of `N` are summable. -/
theorem klS_eq_fwd [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) {u : ℕ → Fin m → V}
    (hu : IsStableProc u) (hua : ∀ t, Evec E t (u t) = u t)
    (hrec : ∀ t, u t = matAct N (Evec E t (u (t + 1))) + w t) (t : ℕ) :
    u t = klS_fwd E N w t := by
  have hiter : ∀ J, u t = matAct (N ^ J) (Evec E t (u (t + J))) +
      ∑ j ∈ Finset.range J, matAct (N ^ j) (Evec E t (w (t + j))) := by
    intro J
    induction J with
    | zero => simp [hua, matAct_one]
    | succ J ih =>
      have e : Evec E t (u (t + J)) = matAct N (Evec E t (u (t + J + 1))) +
          Evec E t (w (t + J)) := by
        rw [hrec (t + J), klS_Evec_add, Evec_matAct, klS_Evec_tower_le E (by omega)]
      rw [ih, e, matAct_add, matAct_mul, ← pow_succ, Finset.sum_range_succ,
        show t + J + 1 = t + (J + 1) by ring]
      abel
  obtain ⟨U₀, -, hU₀⟩ := klS_stable_bound hu
  have h1 : Tendsto (fun J => matAct (N ^ J) (Evec E t (u (t + J)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun J => (klS_norm_matAct_le _ _).trans
      (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hU₀ _))
        (klS_ent_nonneg _))) ?_
    simpa using hN.tendsto_atTop_zero.mul_const U₀
  have h2 := (klS_fwd_summable E hN hw t).hasSum.tendsto_sum_nat
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hiter) h3

/-- The backward recursion `s_{t+1} = Ms_t + v_t` with stable `v` and summable powers of `M` has
stable solutions. -/
theorem klS_stable_of_rec {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : Summable fun j => klS_ent (M ^ j)) {v s : ℕ → Fin m → V} (hv : IsStableProc v)
    (hrec : ∀ t, s (t + 1) = matAct M (s t) + v t) : IsStableProc s := by
  have hform : ∀ t, s t = matAct (M ^ t) (s 0) +
      ∑ j ∈ Finset.range t, matAct (M ^ j) (v (t - 1 - j)) := by
    intro t
    induction t with
    | zero => simp [matAct_one]
    | succ t ih =>
      rw [hrec, ih, matAct_add, matAct_mul, ← pow_succ', klS_matAct_sum,
        Finset.sum_range_succ' _ t]
      simp only [matAct_mul, ← pow_succ', pow_zero, matAct_one]
      rw [add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]
  obtain ⟨Vb, hV0, hV⟩ := klS_stable_bound hv
  set σ := ∑' j, klS_ent (M ^ j)
  have hσ : ∀ t, klS_ent (M ^ t) ≤ σ := fun t =>
    hM.le_tsum t fun j _ => klS_ent_nonneg _
  refine klS_stable_of_le (K := σ * ‖s 0‖ + σ * Vb) fun t => ?_
  rw [hform t]
  refine (norm_add_le _ _).trans (add_le_add ((klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_right (hσ t) (norm_nonneg _))) ?_)
  calc ‖∑ j ∈ Finset.range t, matAct (M ^ j) (v (t - 1 - j))‖
      ≤ ∑ j ∈ Finset.range t, klS_ent (M ^ j) * Vb := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (klS_norm_matAct_le _ _).trans
          (mul_le_mul_of_nonneg_left (hV _) (klS_ent_nonneg _)))
    _ = (∑ j ∈ Finset.range t, klS_ent (M ^ j)) * Vb := by rw [Finset.sum_mul]
    _ ≤ σ * Vb := mul_le_mul_of_nonneg_right
        (hM.sum_le_tsum _ fun j _ => klS_ent_nonneg _) hV0

/-! ### The transformed system in blocks -/

omit [NormedSpace ℂ V] in
theorem klS_norm_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → V) (f : κ → ι) :
    ‖v ∘ f‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v (f i)

/-- Miao, p. 56 (the analogue of (1.36) for (2.11)): with `S`, `T` upper triangular,
`S E_t x*_{t+1} = T x*_t + c_t` splits into the `s`-block
`S₁₁E_t s_{t+1} + S₁₂E_t u_{t+1} = T₁₁s_t + T₁₂u_t + c¹_t` and the `u`-block
`S₂₂E_t u_{t+1} = T₂₂u_t + c²_t` (here `y' = E_t x*_{t+1}`). -/
theorem klS_blocks_iff {a b : ℕ} {S T : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (y y' c : Fin (a + b) → V) :
    matAct S y' = matAct T y + c ↔
      (matAct (S.submatrix (Fin.castAdd b) (Fin.castAdd b)) (y' ∘ Fin.castAdd b) +
          matAct (S.submatrix (Fin.castAdd b) (Fin.natAdd a)) (y' ∘ Fin.natAdd a) =
        matAct (T.submatrix (Fin.castAdd b) (Fin.castAdd b)) (y ∘ Fin.castAdd b) +
          matAct (T.submatrix (Fin.castAdd b) (Fin.natAdd a)) (y ∘ Fin.natAdd a) +
            c ∘ Fin.castAdd b) ∧
      matAct (S.submatrix (Fin.natAdd a) (Fin.natAdd a)) (y' ∘ Fin.natAdd a) =
        matAct (T.submatrix (Fin.natAdd a) (Fin.natAdd a)) (y ∘ Fin.natAdd a) +
          c ∘ Fin.natAdd a := by
  have e1 : (matAct T y + c) ∘ Fin.castAdd b = matAct T y ∘ Fin.castAdd b + c ∘ Fin.castAdd b :=
    rfl
  have e2 : (matAct T y + c) ∘ Fin.natAdd a = matAct T y ∘ Fin.natAdd a + c ∘ Fin.natAdd a :=
    rfl
  constructor
  · intro h
    have h1 : matAct S y' ∘ Fin.castAdd b = (matAct T y + c) ∘ Fin.castAdd b := by rw [h]
    have h2 : matAct S y' ∘ Fin.natAdd a = (matAct T y + c) ∘ Fin.natAdd a := by rw [h]
    rw [e1, klS_matAct_blocks, klS_matAct_blocks] at h1
    rw [e2, klS_matAct_natAdd hS, klS_matAct_natAdd hT] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine klS_ext_blocks ?_ ?_
    · rw [e1, klS_matAct_blocks, klS_matAct_blocks]
      exact h1
    · rw [e2, klS_matAct_natAdd hS, klS_matAct_natAdd hT]
      exact h2

/-- Solving the `u`-block for `u_t` (Miao, p. 56): with `T₂₂` invertible,
`S₂₂a = T₂₂u + d` iff `u = T₂₂⁻¹S₂₂a − T₂₂⁻¹d` (with `a = E_t u_{t+1}`, `d = c²_t`). -/
theorem klS_solve_fwd {m : ℕ} {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (h : T22.det ≠ 0)
    (u a d : Fin m → V) :
    matAct S22 a = matAct T22 u + d ↔ u = matAct (T22⁻¹ * S22) a + -matAct T22⁻¹ d := by
  constructor
  · intro e
    rw [← matAct_mul, e, matAct_add, klS_matAct_inv_mul h]
    abel
  · intro e
    rw [e, matAct_add, klS_matAct_neg, ← matAct_mul, klS_matAct_mul_inv h, klS_matAct_mul_inv h]
    abel

/-- Miao, p. 56 ("We replace equation (1.38) with"): solving the `s`-block for `E_t s_{t+1}`,
`E_t s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂E_t u_{t+1} + S₁₁⁻¹Q₁Cz_t`. Here `Es'`, `Eu'`
stand for `E_t s_{t+1}`, `E_t u_{t+1}` and `c` for `Q₁Cz_t`. The printed formula is correct. -/
theorem eq_klein_Es {m p : ℕ} {S11 T11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 : Matrix (Fin m) (Fin p) ℂ} (h : S11.det ≠ 0) (s Es' c : Fin m → V)
    (u Eu' : Fin p → V) :
    matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c ↔
      Es' = matAct (S11⁻¹ * T11) s + matAct (S11⁻¹ * T12) u - matAct (S11⁻¹ * S12) Eu' +
        matAct S11⁻¹ c := by
  have hI : S11 * S11⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    have e' : matAct S11 Es' = matAct T11 s + matAct T12 u + c - matAct S12 Eu' := by
      rw [← e]
      abel
    calc Es' = matAct S11⁻¹ (matAct S11 Es') := (klS_matAct_inv_mul h Es').symm
      _ = _ := by
        rw [e']
        simp only [klS_matAct_sub, matAct_add, matAct_mul]
        abel
  · intro e
    rw [e]
    simp only [klS_matAct_sub, matAct_add, matAct_mul, ← Matrix.mul_assoc, hI, Matrix.one_mul,
      matAct_one]
    abel

/-- Miao, p. 57: since `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}`, its prediction error is
`ξ_{t+1} = k_{t+1} − E_t k_{t+1} = Z₁₁(s_{t+1} − E_t s_{t+1}) + Z₁₂(u_{t+1} − E_t u_{t+1})`. -/
theorem eq_klein_xi (E : CondExpSystem ℂ V) (t : ℕ) {m p : ℕ} (Z11 : Matrix (Fin m) (Fin m) ℂ)
    (Z12 : Matrix (Fin m) (Fin p) ℂ) (s' : Fin m → V) (u' : Fin p → V) :
    matAct Z11 s' + matAct Z12 u' - Evec E t (matAct Z11 s' + matAct Z12 u') =
      matAct Z11 (s' - Evec E t s') + matAct Z12 (u' - Evec E t u') := by
  rw [klS_Evec_add, Evec_matAct, Evec_matAct, klS_matAct_sub, klS_matAct_sub]
  abel

/-- Miao, p. 56, `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}` (and `y_{t+1} = Z₂₁s_{t+1} + Z₂₂u_{t+1}`),
from `x = Zx*` with `x* = (s, u)`. -/
theorem eq_klein_k {nk ny : ℕ} (Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ)
    (xs : Fin (nk + ny) → V) :
    matAct Z xs ∘ Fin.castAdd ny =
        matAct (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)) (xs ∘ Fin.castAdd ny) +
          matAct (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk)) (xs ∘ Fin.natAdd nk) ∧
      matAct Z xs ∘ Fin.natAdd nk =
        matAct (Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny)) (xs ∘ Fin.castAdd ny) +
          matAct (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) (xs ∘ Fin.natAdd nk) :=
  ⟨klS_matAct_blocks Z _ xs, klS_matAct_blocks Z _ xs⟩

/-- Miao, p. 57: in a solution, the predetermined block gives
`s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂E_t u_{t+1} + S₁₁⁻¹Q₁Cz_t
  − Z₁₁⁻¹Z₁₂(u_{t+1} − E_t u_{t+1}) + Z₁₁⁻¹ξ_{t+1}`
from the `s`-block `h1` and the prediction error `h2` of `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}`
(`Es'`, `Eu'` stand for `E_t s_{t+1}`, `E_t u_{t+1}`). The printed formula is correct, every term
and sign included. -/
theorem eq_klein_s {m p : ℕ} {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ} (hS11 : S11.det ≠ 0) (hZ11 : Z11.det ≠ 0)
    {s s' Es' c ξ' : Fin m → V} {u u' Eu' : Fin p → V}
    (h1 : matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c)
    (h2 : matAct Z11 s' + matAct Z12 u' - (matAct Z11 Es' + matAct Z12 Eu') = ξ') :
    s' = matAct (S11⁻¹ * T11) s + (matAct (S11⁻¹ * T12) u - matAct (S11⁻¹ * S12) Eu' +
      matAct S11⁻¹ c - matAct (Z11⁻¹ * Z12) (u' - Eu') + matAct Z11⁻¹ ξ') := by
  have hEs := (eq_klein_Es hS11 s Es' c u Eu').1 h1
  have h3 : matAct Z11 (s' - Es') = ξ' - matAct Z12 (u' - Eu') := by
    rw [klS_matAct_sub, klS_matAct_sub, ← h2]
    abel
  have h4 : s' - Es' = matAct Z11⁻¹ (ξ' - matAct Z12 (u' - Eu')) := by
    rw [← h3, klS_matAct_inv_mul hZ11]
  calc s' = Es' + (s' - Es') := by abel
    _ = _ := by
      rw [h4, hEs, klS_matAct_sub Z11⁻¹ ξ', matAct_mul]
      abel

/-! ### The core: existence and uniqueness in the transformed coordinates -/

/-- Klein's construction for (2.11) in the transformed coordinates `x* = (s, u)`, written in
blocks (Miao, pp. 56–57). With `S₁₁`, `T₂₂`, `Z₁₁` invertible and the powers of `S₁₁⁻¹T₁₁`,
`T₂₂⁻¹S₂₂` summable, for stable adapted forcing `c¹, c²`, a stable adapted prediction error `ξ`
with `E_t ξ_{t+1} = 0` and an `F₀`-measurable `k₀`, there is exactly one stable adapted `(s, u)`
solving both blocks, with `k = Z₁₁s + Z₁₂u` having prediction error `ξ` and `k₀` as initial
value. -/
theorem klS_core_blocks [CompleteSpace V] (E : CondExpSystem ℂ V) {m p : ℕ}
    {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ} {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ}
    {S22 T22 : Matrix (Fin p) (Fin p) ℂ} (hS11 : S11.det ≠ 0) (hT22 : T22.det ≠ 0)
    (hZ11 : Z11.det ≠ 0) (hMs : Summable fun j => klS_ent ((S11⁻¹ * T11) ^ j))
    (hN : Summable fun j => klS_ent ((T22⁻¹ * S22) ^ j))
    {c1 : ℕ → Fin m → V} {c2 : ℕ → Fin p → V} (hc1 : IsStableProc c1) (hc2 : IsStableProc c2)
    (hc1a : ∀ t, Evec E t (c1 t) = c1 t) (hc2a : ∀ t, Evec E t (c2 t) = c2 t)
    {ξ : ℕ → Fin m → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t, Evec E (t + 1) (ξ (t + 1)) = ξ (t + 1)) (hξm : ∀ t, Evec E t (ξ (t + 1)) = 0)
    (k₀ : Fin m → V) (hk₀ : Evec E 0 k₀ = k₀) :
    ∃! su : (ℕ → Fin m → V) × (ℕ → Fin p → V),
      (∀ t, matAct S11 (Evec E t (su.1 (t + 1))) + matAct S12 (Evec E t (su.2 (t + 1))) =
        matAct T11 (su.1 t) + matAct T12 (su.2 t) + c1 t) ∧
      (∀ t, matAct S22 (Evec E t (su.2 (t + 1))) = matAct T22 (su.2 t) + c2 t) ∧
      IsStableProc su.1 ∧ IsStableProc su.2 ∧
      (∀ t, Evec E t (su.1 t) = su.1 t) ∧ (∀ t, Evec E t (su.2 t) = su.2 t) ∧
      (∀ t, matAct Z11 (su.1 (t + 1)) + matAct Z12 (su.2 (t + 1)) -
        Evec E t (matAct Z11 (su.1 (t + 1)) + matAct Z12 (su.2 (t + 1))) = ξ (t + 1)) ∧
      matAct Z11 (su.1 0) + matAct Z12 (su.2 0) = k₀ := by
  -- Step 1, (2.17): the forward solution for `u`
  obtain ⟨Cb, -, hCb⟩ := klS_stable_bound hc2
  have hW : ∀ t, ‖-matAct T22⁻¹ (c2 t)‖ ≤ klS_ent T22⁻¹ * Cb := fun t => by
    rw [norm_neg]
    exact (klS_norm_matAct_le _ _).trans (mul_le_mul_of_nonneg_left (hCb t) (klS_ent_nonneg _))
  have hwa : ∀ t, Evec E t (-matAct T22⁻¹ (c2 t)) = -matAct T22⁻¹ (c2 t) := fun t => by
    rw [klS_Evec_neg, Evec_matAct, hc2a]
  obtain ⟨uF, huFd⟩ : ∃ uF : ℕ → Fin p → V,
      ∀ t, uF t = klS_fwd E (T22⁻¹ * S22) (fun t => -matAct T22⁻¹ (c2 t)) t := ⟨_, fun _ => rfl⟩
  have huF : ∀ t, uF t = matAct (T22⁻¹ * S22) (Evec E t (uF (t + 1))) +
      -matAct T22⁻¹ (c2 t) := fun t => by
    rw [huFd, huFd]
    exact klS_fwd_rec E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW hwa t
  have huFa : ∀ t, Evec E t (uF t) = uF t := fun t => by
    rw [huFd]
    exact klS_fwd_adapted E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW t
  have huFs : IsStableProc uF := klS_stable_of_le fun t => by
    rw [huFd]
    exact klS_norm_fwd_le E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW t
  -- Step 2: the backward recursion for `s`
  obtain ⟨v, hvd⟩ : ∃ v : ℕ → Fin m → V, ∀ t, v t = matAct (S11⁻¹ * T12) (uF t) -
      matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) + matAct S11⁻¹ (c1 t) -
      matAct (Z11⁻¹ * Z12) (uF (t + 1) - Evec E t (uF (t + 1))) + matAct Z11⁻¹ (ξ (t + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hvs : IsStableProc v := by
    have := klS_stable_add (klS_stable_sub (klS_stable_add (klS_stable_sub
      (klS_stable_matAct huFs (S11⁻¹ * T12))
      (klS_stable_matAct (klS_stable_Evec E huFs 1) (S11⁻¹ * S12)))
      (klS_stable_matAct hc1 S11⁻¹))
      (klS_stable_matAct (klS_stable_sub (klS_stable_shift huFs 1) (klS_stable_Evec E huFs 1))
        (Z11⁻¹ * Z12)))
      (klS_stable_matAct (klS_stable_shift hξ 1) Z11⁻¹)
    rw [show v = _ from funext hvd]
    exact this
  have hEv : ∀ t, Evec E t (v t) = matAct (S11⁻¹ * T12) (uF t) -
      matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) + matAct S11⁻¹ (c1 t) := fun t => by
    rw [hvd]
    simp only [klS_Evec_add, klS_Evec_sub, Evec_matAct, huFa t, klS_Evec_idem, hc1a t, hξm t,
      sub_self, klS_matAct_zero, sub_zero, add_zero]
  have hva : ∀ t, Evec E (t + 1) (v t) = v t := fun t => by
    rw [hvd]
    simp only [klS_Evec_add, klS_Evec_sub, Evec_matAct, klS_adapted_succ E (huFa t),
      klS_Evec_tower_ge E (Nat.le_add_right t 1), klS_adapted_succ E (hc1a t), huFa (t + 1),
      hξa t]
  obtain ⟨sF, hsF0, hsF⟩ : ∃ sF : ℕ → Fin m → V,
      sF 0 = matAct Z11⁻¹ (k₀ - matAct Z12 (uF 0)) ∧
        ∀ t, sF (t + 1) = matAct (S11⁻¹ * T11) (sF t) + v t :=
    ⟨fun t => Nat.rec (matAct Z11⁻¹ (k₀ - matAct Z12 (uF 0)))
      (fun t st => matAct (S11⁻¹ * T11) st + v t) t, rfl, fun _ => rfl⟩
  have hsFs : IsStableProc sF := klS_stable_of_rec hMs hvs hsF
  have hsFa : ∀ t, Evec E t (sF t) = sF t := by
    intro t
    induction t with
    | zero => rw [hsF0, Evec_matAct, klS_Evec_sub, Evec_matAct, hk₀, huFa 0]
    | succ t ih => rw [hsF, klS_Evec_add, Evec_matAct, klS_adapted_succ E ih, hva]
  have hEs : ∀ t, Evec E t (sF (t + 1)) = matAct (S11⁻¹ * T11) (sF t) +
      (matAct (S11⁻¹ * T12) (uF t) - matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) +
        matAct S11⁻¹ (c1 t)) := fun t => by
    rw [hsF, klS_Evec_add, Evec_matAct, hsFa, hEv]
  refine ⟨(sF, uF), ⟨fun t => ?_, fun t => ?_, hsFs, huFs, hsFa, huFa, fun t => ?_, ?_⟩, ?_⟩
  · -- the `s`-block
    refine (eq_klein_Es hS11 _ _ _ _ _).2 ?_
    rw [hEs]
    abel
  · -- the `u`-block
    exact (klS_solve_fwd hT22 _ _ _).2 (huF t)
  · -- the prediction error of `k`
    dsimp only
    rw [eq_klein_xi, hEs, hsF, hvd]
    rw [show ∀ (a P Q R : Fin m → V), a + (P - Q + R) - (a + P) = R - Q from
      fun a P Q R => by abel]
    rw [klS_matAct_sub Z11 (matAct Z11⁻¹ (ξ (t + 1))), klS_matAct_mul_inv hZ11, matAct_mul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hZ11), Matrix.one_mul]
    abel
  · -- the initial condition
    dsimp only
    rw [hsF0, klS_matAct_mul_inv hZ11, sub_add_cancel]
  · -- uniqueness
    rintro ⟨s, u⟩ ⟨h1, h2, -, hus, -, hua, hp, h0⟩
    dsimp only at h1 h2 hus hua hp h0
    have hu : ∀ t, u t = uF t := fun t => by
      rw [huFd]
      exact klS_eq_fwd E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW hus hua
        (fun t => (klS_solve_fwd hT22 _ _ _).1 (h2 t)) t
    have hs : ∀ t, s t = sF t := by
      intro t
      induction t with
      | zero => rw [hsF0, ← h0, hu 0, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
      | succ t ih =>
        have hp' := hp t
        rw [klS_Evec_add, Evec_matAct, Evec_matAct] at hp'
        rw [eq_klein_s hS11 hZ11 (h1 t) hp', hsF, hvd, ih]
        simp only [hu]
    exact Prod.ext (funext hs) (funext hu)

/-- Klein's construction for (2.11) in the transformed coordinates `x* = Zᴴx` (Miao, pp. 56–57):
with `S`, `T` upper triangular, the first `n_k` pairs stable and the rest unstable (none on the
unit circle) and `Z₁₁` invertible, there is exactly one stable adapted `y` with
`S E_t y_{t+1} = T y_t + c_t` whose block `k = (Zy)_K` has prediction error `ξ` and `k₀ = k₀`. -/
theorem klS_core [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny : ℕ}
    {S T Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    {c : ℕ → Fin (nk + ny) → V} (hc : IsStableProc c) (hca : ∀ t, Evec E t (c t) = c t)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t, Evec E (t + 1) (ξ (t + 1)) = ξ (t + 1)) (hξm : ∀ t, Evec E t (ξ (t + 1)) = 0)
    (k₀ : Fin nk → V) (hk₀ : Evec E 0 k₀ = k₀) :
    ∃! y : ℕ → Fin (nk + ny) → V,
      (∀ t, matAct S (Evec E t (y (t + 1))) = matAct T (y t) + c t) ∧ IsStableProc y ∧
      (∀ t, Evec E t (y t) = y t) ∧
      (∀ t, matAct Z (y (t + 1)) ∘ Fin.castAdd ny -
        Evec E t (matAct Z (y (t + 1)) ∘ Fin.castAdd ny) = ξ (t + 1)) ∧
      matAct Z (y 0) ∘ Fin.castAdd ny = k₀ := by
  obtain ⟨⟨s, u⟩, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, huniq⟩ := klS_core_blocks E
    (det_S11_ne_zero hS hord) (det_T22_ne_zero hT hord hdiag) hZ11
    (klS_summable_ent (summable_Ms hS hT hord)) (klS_summable_ent (summable_Mu hS hT hord hdiag))
    (c1 := fun t => c t ∘ Fin.castAdd ny) (c2 := fun t => c t ∘ Fin.natAdd nk)
    (klS_stable_comp hc _) (klS_stable_comp hc _)
    (fun t => by rw [klS_Evec_comp, hca]) (fun t => by rw [klS_Evec_comp, hca]) hξ hξa hξm k₀ hk₀
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨fun t => Fin.append (s t) (u t), ⟨fun t => ?_, klS_stable_append h3 h4, fun t => ?_,
    fun t => ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [klS_Evec_append, klS_blocks_iff hS hT]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact ⟨h1 t, h2 t⟩
  · dsimp only
    rw [klS_Evec_append, h5, h6]
  · dsimp only
    rw [klS_matAct_blocks Z (Fin.castAdd ny)]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact h7 t
  · dsimp only
    rw [klS_matAct_blocks Z (Fin.castAdd ny)]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact h8
  · rintro y ⟨hy1, hy2, hy3, hy4, hy5⟩
    have hb := fun t => (klS_blocks_iff hS hT (y t) (Evec E t (y (t + 1))) (c t)).1 (hy1 t)
    have := huniq (fun t => y t ∘ Fin.castAdd ny, fun t => y t ∘ Fin.natAdd nk)
      ⟨fun t => (hb t).1, fun t => (hb t).2, klS_stable_comp hy2 _, klS_stable_comp hy2 _,
        fun t => by
          change Evec E t (y t ∘ Fin.castAdd ny) = y t ∘ Fin.castAdd ny
          rw [klS_Evec_comp, hy3],
        fun t => by
          change Evec E t (y t ∘ Fin.natAdd nk) = y t ∘ Fin.natAdd nk
          rw [klS_Evec_comp, hy3],
        fun t => by
          have := hy4 t
          rw [klS_matAct_blocks Z (Fin.castAdd ny)] at this
          exact this,
        by
          have := hy5
          rw [klS_matAct_blocks Z (Fin.castAdd ny)] at this
          exact this⟩
    funext t
    refine klS_ext_blocks ?_ ?_
    · rw [klS_append_castAdd]
      exact congrFun (congrArg Prod.fst this) t
    · rw [klS_append_natAdd]
      exact congrFun (congrArg Prod.snd this) t

/-- The unitary change of variables `x* = Zᴴx` (Miao, p. 56, as on p. 25): `x` solves (2.11) iff
`S E_t x*_{t+1} = T x*_t + QCz_t` with `S = QAZ`, `T = QBZ`. -/
theorem klS_isRESolution_iff (E : CondExpSystem ℂ V) {n nz : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin nz) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℕ → Fin nz → V) (x : ℕ → Fin n → V) :
    IsRESolution E A B C z x ↔ ∀ t, matAct (Q * A * Z) (Evec E t (matAct (star Z) (x (t + 1)))) =
      matAct (Q * B * Z) (matAct (star Z) (x t)) + matAct Q (matAct C (z t)) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → V),
      matAct (Q * M * Z) (matAct (star Z) v) = matAct Q (matAct M v) := fun M v => by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ, Matrix.mul_one]
  simp only [IsRESolution, Evec_matAct, key, ← matAct_add]
  refine forall_congr' fun t => ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (matAct (star Q)) h
  simpa only [matAct_mul, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, matAct_one] using this

/-- **Klein's theorem for (2.11)** (Miao, §2.3.2, pp. 56–57). Let `(A, B)` be regular, with QZ
form `S = QAZ`, `T = QBZ` whose stable generalized eigenvalues come first (`theorem_1_4_4_stable`),
and partition `x_t = (k_t, y_t)` with `k_t` the first `n_k` coordinates. Suppose, as in
Theorem 1.4.5, (i) `n_s = n_k` (`hord`), (ii) `Z₁₁` invertible, (iii) no generalized eigenvalue
on the unit circle. Let `{z_t}` be stable and adapted, `{ξ_t}` a stable martingale difference
process with `ξ_{t+1}` `F_{t+1}`-measurable, and `k₀` `F₀`-measurable. Then (2.11) has exactly
one stable adapted solution such that `{k_t}` is predetermined with prediction error `{ξ_t}`
(Definition 2.3.4) and `k₀` is the given one. -/
theorem klein_stochastic [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t i, E.E (t + 1) (ξ (t + 1) i) = ξ (t + 1) i)
    (hξm : IsMartingaleDiffProc E ξ) (k₀ : Fin nk → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) :
    ∃! x : ℕ → Fin (nk + ny) → V,
      IsRESolution E A B C z x ∧ IsStableProc x ∧ IsAdaptedV E x ∧
      IsPredeterminedKlein E ξ (fun t i => x t (Fin.castAdd ny i)) ∧
      ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  have hza' : ∀ t, Evec E t (z t) = z t := fun t => funext (hza t)
  obtain ⟨y, ⟨hy1, hy2, hy3, hy4, hy5⟩, hyu⟩ := klS_core E hS hT hord
    (diag_off_circle hreg hQ hZ hS hT hcirc) hZ11 (c := fun t => matAct Q (matAct C (z t)))
    (klS_stable_matAct (klS_stable_matAct hz C) Q)
    (fun t => by rw [Evec_matAct, Evec_matAct, hza']) hξ (fun t => funext (hξa t))
    (fun t => funext (hξm t)) k₀ (funext hk₀)
  have hback : ∀ v : Fin (nk + ny) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  refine ⟨fun t => matAct Z (y t), ⟨(klS_isRESolution_iff E hQ hZ z _).2 fun t => ?_,
    klS_stable_matAct hy2 Z, fun t i => ?_, ⟨fun t i => congrFun (hy4 t) i, hξm, fun i => ?_⟩,
    fun i => congrFun hy5 i⟩, ?_⟩
  · simpa only [matAct_mul, hZZ', matAct_one] using hy1 t
  · change Evec E t (matAct Z (y t)) i = matAct Z (y t) i
    rw [Evec_matAct, hy3]
  · change E.E 0 (matAct Z (y 0) (Fin.castAdd ny i)) = matAct Z (y 0) (Fin.castAdd ny i)
    have h := congrFun hy5 i
    simp only [Function.comp_apply] at h
    rw [h, hk₀ i]
  · rintro x ⟨hx1, hx2, hx3, ⟨hx4, -, -⟩, hx5⟩
    have := hyu (fun t => matAct (star Z) (x t)) ⟨(klS_isRESolution_iff E hQ hZ z x).1 hx1,
      klS_stable_matAct hx2 _, fun t => by
        rw [Evec_matAct, show Evec E t (x t) = x t from funext (hx3 t)],
      fun t => by
        simp only [hback]
        funext i
        exact hx4 t i,
      by
        simp only [hback]
        funext i
        exact hx5 i⟩
    funext t
    simp only [← this, hback]

/-! ### Real data -/

/-- A real matrix commutes with a conjugation of `V`. -/
theorem klS_cj_matAct {ι κ : Type*} [Fintype κ] (cj : V →ₗ⋆[ℂ] V) (M : Matrix ι κ ℝ)
    (v : κ → V) (i : ι) :
    cj (matAct (M.map Complex.ofRealHom) v i) =
      matAct (M.map Complex.ofRealHom) (fun j => cj (v j)) i := by
  simp only [matAct, map_sum, LinearMap.map_smulₛₗ, Matrix.map_apply, Complex.ofRealHom_eq_coe,
    Complex.conj_ofReal]

/-- **Klein's theorem for (2.11), real data** (Miao, p. 56, where `A`, `B`, `C` and the data are
real). Suppose `V` has a conjugation `cj` (conjugate-linear, isometric, commuting with every
`E_t`; for complex `L¹` it is pointwise conjugation, whose fixed points are the real random
variables). If `A`, `B`, `C` are real and `z`, `ξ`, `k₀` are fixed by `cj`, the unique solution
of `klein_stochastic` is fixed by `cj`, i.e. real: its conjugate is another solution. -/
theorem klein_stochastic_real [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℝ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℝ}
    (cj : V →ₗ⋆[ℂ] V) (hcjE : ∀ t X, cj (E.E t X) = E.E t (cj X)) (hcjn : ∀ X, ‖cj X‖ = ‖X‖)
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
      ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    (hzr : ∀ t i, cj (z t i) = z t i)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t i, E.E (t + 1) (ξ (t + 1) i) = ξ (t + 1) i)
    (hξm : IsMartingaleDiffProc E ξ) (hξr : ∀ t i, cj (ξ t i) = ξ t i)
    (k₀ : Fin nk → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) (hk₀r : ∀ i, cj (k₀ i) = k₀ i) :
    ∃! x : ℕ → Fin (nk + ny) → V,
      (IsRESolution E (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
          (C.map Complex.ofRealHom) z x ∧ IsStableProc x ∧ IsAdaptedV E x ∧
        IsPredeterminedKlein E ξ (fun t i => x t (Fin.castAdd ny i)) ∧
        ∀ i, x 0 (Fin.castAdd ny i) = k₀ i) ∧
      ∀ t i, cj (x t i) = x t i := by
  obtain ⟨x, ⟨hx1, hx2, hx3, ⟨hx4, -, hx6⟩, hx5⟩, hu⟩ := klein_stochastic E hreg hQ hZ hS hT hord
    hZ11 hcirc (C := C.map Complex.ofRealHom) hz hza hξ hξa hξm k₀ hk₀
  have hconj : (fun t i => cj (x t i)) = x := by
    refine hu _ ⟨fun t => funext fun i => ?_, ?_, fun t i => ?_, ⟨fun t i => ?_, hξm, fun i => ?_⟩,
      fun i => ?_⟩
    · have e1 : Evec E t (fun j => cj (x (t + 1) j)) = fun j => cj (Evec E t (x (t + 1)) j) :=
        funext fun j => (hcjE t _).symm
      have e2 : z t = fun j => cj (z t j) := funext fun j => (hzr t j).symm
      rw [e1, Pi.add_apply, e2, ← klS_cj_matAct, ← klS_cj_matAct, ← klS_cj_matAct, ← map_add]
      exact congrArg cj (congrFun (hx1 t) i)
    · obtain ⟨M, hM, h⟩ := hx2
      exact ⟨M, hM, fun t i => by rw [hcjn]; exact h t i⟩
    · rw [← hcjE, hx3 t i]
    · rw [← hcjE, ← map_sub, hx4 t i, hξr]
    · change E.E 0 (cj (x 0 (Fin.castAdd ny i))) = cj (x 0 (Fin.castAdd ny i))
      rw [← hcjE, hx6 i]
    · change cj (x 0 (Fin.castAdd ny i)) = k₀ i
      rw [hx5 i, hk₀r]
  exact ⟨x, ⟨⟨hx1, hx2, hx3, ⟨hx4, hξm, hx6⟩, hx5⟩, fun t i => congrFun (congrFun hconj t) i⟩,
    fun x' hx' => hu x' hx'.1⟩

/-! ### The forward solution (2.17) -/

/-- Miao, (2.17) as corrected, p. 56: in a stable adapted solution of the `u`-block
`S₂₂E_t u_{t+1} = T₂₂u_t + c²_t` (`c²_t = Q₂Cz_t`),
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ E_t c²_{t+j}`. The book prints
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂CE_t z_{t+j}`, repeating the misprint of (1.37)
(`eq_2_17_printed_false`). -/
theorem eq_2_17 [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (hT22 : T22.det ≠ 0)
    (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖) {c2 : ℕ → Fin m → V}
    (hc2 : IsStableProc c2) {u : ℕ → Fin m → V} (hu : IsStableProc u)
    (hua : ∀ t, Evec E t (u t) = u t)
    (h : ∀ t, matAct S22 (Evec E t (u (t + 1))) = matAct T22 (u t) + c2 t) (t : ℕ) :
    u t = -∑' j, matAct ((T22⁻¹ * S22) ^ j * T22⁻¹) (Evec E t (c2 (t + j))) := by
  obtain ⟨Cb, -, hCb⟩ := klS_stable_bound hc2
  have hW : ∀ t, ‖-matAct T22⁻¹ (c2 t)‖ ≤ klS_ent T22⁻¹ * Cb := fun t => by
    rw [norm_neg]
    exact (klS_norm_matAct_le _ _).trans (mul_le_mul_of_nonneg_left (hCb t) (klS_ent_nonneg _))
  rw [klS_eq_fwd E (klS_summable_ent hN) (w := fun t => -matAct T22⁻¹ (c2 t)) hW hu hua
    (fun t => (klS_solve_fwd hT22 _ _ _).1 (h t)) t, klS_fwd, ← tsum_neg]
  congr 1
  funext j
  rw [klS_Evec_neg, Evec_matAct, klS_matAct_neg, matAct_mul]

/-- Miao, (2.17) for the solution of `klein_stochastic`, with `x*_t = Zᴴx_t = (s_t, u_t)`:
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂C E_t z_{t+j}`, where `Q₂C` is the lower block row of `QC`. -/
theorem eq_2_17_solution [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z)
    {x : ℕ → Fin (nk + ny) → V} (hx : IsRESolution E A B C z x) (hxs : IsStableProc x)
    (hxa : IsAdaptedV E x) (t : ℕ) :
    matAct (star Z) (x t) ∘ Fin.natAdd nk = -∑' j,
      matAct ((((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
        (Q * A * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j *
          ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
            (Q * C).submatrix (Fin.natAdd nk) id) (Evec E t (z (t + j))) := by
  have hdiag := diag_off_circle hreg hQ hZ hS hT hcirc
  have h := (klS_isRESolution_iff E hQ hZ z x).1 hx
  rw [eq_2_17 E (det_T22_ne_zero hT hord hdiag) (summable_Mu hS hT hord hdiag)
    (c2 := fun t => matAct Q (matAct C (z t)) ∘ Fin.natAdd nk)
    (klS_stable_comp (klS_stable_matAct (klS_stable_matAct hz C) Q) _)
    (u := fun t => matAct (star Z) (x t) ∘ Fin.natAdd nk)
    (klS_stable_comp (klS_stable_matAct hxs _) _)
    (fun t => by
      rw [klS_Evec_comp, Evec_matAct, show Evec E t (x t) = x t from funext (hxa t)])
    (fun t => by
      have := ((klS_blocks_iff hS hT _ _ _).1 (h t)).2
      rw [← klS_Evec_comp] at this
      exact this) t]
  congr 2
  funext j
  change matAct _ (Evec E t (matAct Q (matAct C (z (t + j))) ∘ Fin.natAdd nk)) = _
  rw [klS_Evec_comp, Evec_matAct, Evec_matAct, matAct_mul Q C, klS_matAct_comp, matAct_mul]

/-- The trivial `CondExpSystem` `E_t = id` on `ℂ` (all information known at date 0): the
deterministic system of Chapter 1. -/
noncomputable def klS_detSystem : CondExpSystem ℂ ℂ where
  E _ := ContinuousLinearMap.id ℂ ℂ
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

theorem klS_Evec_det {ι : Type*} (t : ℕ) (v : ι → ℂ) : Evec klS_detSystem t v = v := rfl

theorem klS_matAct_eq_mulVec {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (v : κ → ℂ) :
    matAct M v = M *ᵥ v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

/-- **Counterexample to (2.17) as printed** (Miao, p. 56). With `E_t = id`, the book's
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ E_t c²_{t+j}` need not solve `S₂₂E_t u_{t+1} = T₂₂u_t + c²_t`; this is
the counterexample to (1.37) (`eq_1_37_printed_false`): `S₂₂ = [[0, 1], [0, 0]]`,
`T₂₂ = diag(1, 2)`, `c²_1 = e₂`, `c²_t = 0` otherwise. The correct formula is `eq_2_17`. -/
theorem eq_2_17_printed_false :
    ∃ (S₂₂ T₂₂ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℕ → Fin 2 → ℂ),
      S₂₂.IsUpperTriangular ∧ T₂₂.IsUpperTriangular ∧ (∀ i, ‖S₂₂ i i‖ < ‖T₂₂ i i‖) ∧
      IsStableProc c ∧ (∀ t, Evec klS_detSystem t (c t) = c t) ∧
      ¬ ∀ t, matAct S₂₂ (Evec klS_detSystem t (-matAct T₂₂⁻¹
          (∑' j, matAct ((T₂₂⁻¹ * S₂₂) ^ j) (Evec klS_detSystem (t + 1) (c (t + 1 + j)))))) =
        matAct T₂₂ (-matAct T₂₂⁻¹
          (∑' j, matAct ((T₂₂⁻¹ * S₂₂) ^ j) (Evec klS_detSystem t (c (t + j))))) + c t := by
  obtain ⟨S₂₂, T₂₂, c, h1, h2, h3, ⟨M, hM, h4⟩, h5⟩ := eq_1_37_printed_false
  refine ⟨S₂₂, T₂₂, c, h1, h2, h3, ⟨M, hM, fun t i => (norm_le_pi_norm (c t) i).trans_lt (h4 t)⟩,
    fun t => rfl, fun h => h5 fun t => ?_⟩
  have := h t
  simpa only [klS_matAct_eq_mulVec, klS_Evec_det] using this

end Miao.RationalExpectations
