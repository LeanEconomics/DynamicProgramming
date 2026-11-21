/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.BKStable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Blanchard–Kahn method for stochastic systems

Copied from `EconomicDynamics/RationalExpectations` (module `StochasticBK`), namespace renamed.

Miao, §2.3.1, pp. 53–54. `A` is nonsingular, `W = A⁻¹B` has a real block split
`PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`, which exists when no eigenvalue of `W` lies on the
unit circle: `exists_real_block_split`), and `x = (k, y)` with `k` predetermined in the sense of
Blanchard and Kahn (`IsPredeterminedBK`: `E_tk_{t+1} = k_{t+1}`). A stable solution
(`bkS_IsStableSol`) is a stable adapted process solving `E_tx_{t+1} = Wx_t + Gz_t` with `k`
predetermined.

* **Theorem 1.4.2 in the stochastic case** (`theorem_1_4_2_stoch`): if `n_u = n_y` and `P_uy` is
  nonsingular, then for every `k₀` with `E_0k₀ = k₀` and every stable adapted `z` there is a
  unique stable solution of (2.11) with `k`-part `k₀`. The hypothesis `E_0k₀ = k₀` is necessary
  (`bkS_k0_adapted`). Existence (`bkS_exists`) needs only a right inverse of `P_uy`, uniqueness
  (`bkS_unique`) only a left inverse. Along any stable solution `u_t = (Px_t)_u` is the forward
  solution (2.12) (`bkS_u_eq_fwd`), `y_t = P_uy⁻¹(u_t − P_ukk_t)` and
  `k_{t+1} = (Wx_t + Gz_t)_k` (`bkS_policy`).
  **Corollary 1.4.1 in the stochastic case** (`corollary_1_4_1_stoch`): if `z_t = z̄` from some
  date on, the stable solution converges in norm to `x̄ = (A − B)⁻¹Cz̄`.
  The construction differs from the deterministic one: `x_{t+1} = Wx_t + Gz_t + (0, η_{t+1})`,
  where the expectational error `η_{t+1} = Q(u_{t+1} − E_tu_{t+1})` of the jump variables keeps
  `u` on the forward solution.
* **Certainty equivalence** (p. 54): for the trivial system `E_t = id` (`bkS_trivial`) on `ℝ`,
  stable stochastic solutions are exactly the stable deterministic solutions of Chapter 1
  (`certainty_equivalence`), the forward solutions agree (`certainty_equivalence_fwd`), and
  Theorem 1.4.2 follows from its stochastic version (`theorem_1_4_2_of_stoch`). In general the
  formulas are the deterministic ones with `z_{t+j}` replaced by `E_tz_{t+j}` (`eq_2_12`,
  `bkS_policy`). If `E_tz_{t+1} = Φz_t` (as for (2.1)), `E_tz_{t+j} = Φʲz_t` and
  `u_t = −∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the same expression as in the deterministic case `Σ = 0`
  (`certainty_equivalence_ar`).
* **Theorem 1.4.3 in the stochastic case** (p. 54, "also applies here"). As printed (Chapter 1)
  it is false; the corrected versions about stable solutions hold. Given `w ≠ 0` with
  `E_0w = w` (a nonzero `F_0`-measurable random variable, e.g. a constant): if `n_u > n_y`, for
  every `z` some `F_0`-measurable `k₀` has no stable solution (`theorem_1_4_3_gt_stoch`); if
  `n_u < n_y`, one stable solution gives infinitely many (`theorem_1_4_3_lt_stoch`), and if
  `P_uy` has a right inverse they exist for every `k₀` (`theorem_1_4_3_lt_exists_stoch`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Blocks -/

omit [NormedSpace ℝ V] in
theorem bkS_add_comp {α β : Type*} (a b : α → V) (f : β → α) : (a + b) ∘ f = a ∘ f + b ∘ f :=
  rfl

omit [NormedSpace ℝ V] in
theorem bkS_sub_comp {α β : Type*} (a b : α → V) (f : β → α) : (a - b) ∘ f = a ∘ f - b ∘ f :=
  rfl

theorem bkS_Evec_comp (E : CondExpSystem ℝ V) {α β : Type*} (t : ℕ) (a : α → V) (f : β → α) :
    Evec E t (a ∘ f) = Evec E t a ∘ f :=
  rfl

/-- `(Px)_s = P_skk + P_syy`. -/
theorem bkS_comp_inl {σ τ κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → V) :
    matAct P x ∘ Sum.inl = matAct P.toBlocks₁₁ (x ∘ Sum.inl) + matAct P.toBlocks₁₂ (x ∘ Sum.inr) :=
  by
  funext i
  simp [matAct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

/-- `(Px)_u = P_ukk + P_uyy`. -/
theorem bkS_comp_inr {σ τ κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → V) :
    matAct P x ∘ Sum.inr = matAct P.toBlocks₂₁ (x ∘ Sum.inl) + matAct P.toBlocks₂₂ (x ∘ Sum.inr) :=
  by
  funext i
  simp [matAct, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem bkS_blockDiag_inl {σ τ : Type*} [Fintype σ] [Fintype τ] (Js : Matrix σ σ ℝ)
    (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → V) :
    matAct (Matrix.fromBlocks Js 0 0 Ju) v ∘ Sum.inl = matAct Js (v ∘ Sum.inl) := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

theorem bkS_blockDiag_inr {σ τ : Type*} [Fintype σ] [Fintype τ] (Js : Matrix σ σ ℝ)
    (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → V) :
    matAct (Matrix.fromBlocks Js 0 0 Ju) v ∘ Sum.inr = matAct Ju (v ∘ Sum.inr) := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

/-- (1.26) for random vectors, stable part: `(PWx)_s = J_s(Px)_s`. -/
theorem bkS_split_inl {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ] {W : Matrix ι ι ℝ}
    {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (x : ι → V) :
    matAct P (matAct W x) ∘ Sum.inl = matAct Js (matAct P x ∘ Sum.inl) := by
  rw [matAct_mul, hPW, ← matAct_mul, bkS_blockDiag_inl]

/-- (1.26) for random vectors, unstable part: `(PWx)_u = J_u(Px)_u`. -/
theorem bkS_split_inr {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ] {W : Matrix ι ι ℝ}
    {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (x : ι → V) :
    matAct P (matAct W x) ∘ Sum.inr = matAct Ju (matAct P x ∘ Sum.inr) := by
  rw [matAct_mul, hPW, ← matAct_mul, bkS_blockDiag_inr]

omit [NormedSpace ℝ V] in
theorem bkS_norm_comp_inl_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v ∘ Sum.inl‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

omit [NormedSpace ℝ V] in
theorem bkS_norm_comp_inr_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v ∘ Sum.inr‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

omit [NormedSpace ℝ V] in
theorem bkS_norm_sum_type_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v‖ ≤ ‖v ∘ Sum.inl‖ + ‖v ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with i | i
  · exact (norm_le_pi_norm (v ∘ Sum.inl) i).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact (norm_le_pi_norm (v ∘ Sum.inr) i).trans (le_add_of_nonneg_left (norm_nonneg _))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem bkS_sumElim_eta {κ υ : Type*} (v : κ ⊕ υ → V) :
    v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  funext i
  rcases i with i | i <;> rfl

/-- The backward solution of `s_{t+1} = Ms_t + g_t` for random vectors:
`s_t = Mᵗs₀ + ∑_{j<t} Mʲg_{t−1−j}`. -/
theorem bkS_backward_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    {s g : ℕ → ι → V} (hs : ∀ t, s (t + 1) = matAct M (s t) + g t) (t : ℕ) :
    s t = matAct (M ^ t) (s 0) + ∑ j ∈ Finset.range t, matAct (M ^ j) (g (t - 1 - j)) := by
  induction t with
  | zero => simp [matAct_one]
  | succ t ih =>
    rw [hs t, ih, matAct_add, bkS_matAct_sum, Finset.sum_range_succ', matAct_mul, ← pow_succ']
    simp only [matAct_mul, ← pow_succ', pow_zero, matAct_one]
    rw [show t + 1 - 1 - 0 = t by omega, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]

/-- With geometric decay of `M` and bounded `g`, the backward solution is bounded. -/
theorem bkS_bounded_backward {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ}
    (hM : HasGeomDecay M K a) {s g : ℕ → ι → V} (hs : ∀ t, s (t + 1) = matAct M (s t) + g t)
    {C : ℝ} (hg : ∀ t, ‖g t‖ ≤ C) : ∀ t, ‖s t‖ ≤ K * ‖s 0‖ + K * C / (1 - a) := by
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hK0 := hM.2.2.1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  intro t
  rw [bkS_backward_eq M hs t]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖matAct (M ^ t) (s 0)‖ ≤ K * a ^ t * ‖s 0‖ := bkS_geom_decay hM t _
      _ ≤ K * 1 * ‖s 0‖ := by
          gcongr
          exact pow_le_one₀ ha0 ha1.le
      _ = K * ‖s 0‖ := by ring
  · calc ‖∑ j ∈ Finset.range t, matAct (M ^ j) (g (t - 1 - j))‖
        ≤ ∑ j ∈ Finset.range t, K * C * a ^ j := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          calc ‖matAct (M ^ j) (g (t - 1 - j))‖ ≤ K * a ^ j * ‖g (t - 1 - j)‖ :=
                bkS_geom_decay hM j _
            _ ≤ K * a ^ j * C := by gcongr; exact hg _
            _ = K * C * a ^ j := by ring
      _ = K * C * ∑ j ∈ Finset.range t, a ^ j := by rw [Finset.mul_sum]
      _ ≤ K * C * (1 - a)⁻¹ := by
          gcongr
          rw [← tsum_geometric_of_lt_one ha0 ha1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg ha0 j)
            (summable_geometric_of_lt_one ha0 ha1)
      _ = K * C / (1 - a) := by ring

/-! ### Stable solutions -/

/-- A stable solution of `E_tx_{t+1} = Wx_t + Gz_t` (Miao, pp. 52–53): adapted, stable, with
the `k`-part predetermined in the sense of Blanchard and Kahn. -/
def bkS_IsStableSol (E : CondExpSystem ℝ V) {κ υ m : Type*} [Fintype κ] [Fintype υ] [Fintype m]
    (W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V)
    (x : ℕ → κ ⊕ υ → V) : Prop :=
  (∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t)) ∧ IsAdaptedV E x ∧
    IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x

variable {κ υ σ τ m : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Fintype m]

omit [DecidableEq κ] [DecidableEq υ] [DecidableEq σ] [DecidableEq τ] in
/-- (2.11) in the transformed variables, unstable part: `E_tu_{t+1} = J_uu_t + C_u*z_t`. -/
theorem bkS_u_rec (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V)
    {x : ℕ → κ ⊕ υ → V} (hx : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t))
    (t : ℕ) :
    Evec E t (matAct P (x (t + 1)) ∘ Sum.inr) =
      matAct Ju (matAct P (x t) ∘ Sum.inr) + matAct P (matAct G (z t)) ∘ Sum.inr := by
  rw [bkS_Evec_comp, Evec_matAct, hx t, matAct_add, bkS_add_comp, bkS_split_inr hPW]

/-- Miao, (2.12), p. 54: along any stable solution, `u_t = (Px_t)_u` is the forward solution
`−∑ⱼ J_u^{−j−1}C_u*E_tz_{t+j}` (`eq_2_12`). -/
theorem bkS_u_eq_fwd [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → V} (hz : IsStableProc z) (hza : IsAdaptedV E z) {x : ℕ → κ ⊕ υ → V}
    (hx : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t)) (hxa : IsAdaptedV E x)
    (hxs : IsStableProc x) (t : ℕ) :
    matAct P (x t) ∘ Sum.inr = bkS_fwd E Ju (fun t => matAct P (matAct G (z t)) ∘ Sum.inr) t := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P (bkS_stable_matAct G hz))
  obtain ⟨D, hD⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P hxs)
  have hza' := (bkS_isAdaptedV_iff E z).1 hza
  have hxa' := (bkS_isAdaptedV_iff E x).1 hxa
  refine bkS_fwd_unique E hdet hKa (C := C) (fun t => (bkS_norm_comp_inr_le _).trans (hC t))
    (fun t => ?_) (fun t => ?_) (D := D) (fun t => (bkS_norm_comp_inr_le _).trans (hD t))
    (bkS_u_rec E hPW G z hx) t
  · rw [bkS_Evec_comp, Evec_matAct, Evec_matAct, hza' t]
  · rw [bkS_Evec_comp, Evec_matAct, hxa' t]

/-- The policy of a stable solution (Miao, pp. 53–54, with (1.32)): if `QP_uy = I`, then
`y_t = Q(u_t − P_ukk_t)` with `u_t` the forward solution (2.12), and
`k_{t+1} = (Wx_t + Gz_t)_k`. These are the deterministic formulas with `E_t` applied to the
forcing terms. -/
theorem bkS_policy [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) {x : ℕ → κ ⊕ υ → V} (hx : bkS_IsStableSol E W G z x) (t : ℕ) :
    x t ∘ Sum.inr = matAct Q (bkS_fwd E Ju (fun t => matAct P (matAct G (z t)) ∘ Sum.inr) t -
      matAct P.toBlocks₂₁ (x t ∘ Sum.inl)) ∧
      x (t + 1) ∘ Sum.inl = (matAct W (x t) + matAct G (z t)) ∘ Sum.inl := by
  obtain ⟨hx, hxa, hxp, hxs⟩ := hx
  constructor
  · rw [← bkS_u_eq_fwd E hS G hz hza hx hxa hxs t, bkS_comp_inr, add_sub_cancel_left,
      matAct_mul, hQ, matAct_one]
  · funext i
    have := congrFun (hx t) (Sum.inl i)
    simp only [Evec] at this
    simp only [Function.comp_apply]
    rw [← this]
    exact (hxp t i).symm

/-- **Uniqueness** in the stochastic Theorem 1.4.2 (Miao, pp. 53–54): if `P_uy` has a left
inverse, two stable solutions with the same `k₀` coincide. -/
theorem bkS_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) {x x' : ℕ → κ ⊕ υ → V} (hx : bkS_IsStableSol E W G z x)
    (hx' : bkS_IsStableSol E W G z x') (h0 : x 0 ∘ Sum.inl = x' 0 ∘ Sum.inl) : x = x' := by
  have hk : ∀ t, x t ∘ Sum.inl = x' t ∘ Sum.inl ∧ x t = x' t := fun t => by
    have key : ∀ t, x t ∘ Sum.inl = x' t ∘ Sum.inl → x t = x' t := fun t ht => by
      rw [bkS_sumElim_eta (x t), bkS_sumElim_eta (x' t), (bkS_policy E hS Q hQ G hz hza hx t).1,
        (bkS_policy E hS Q hQ G hz hza hx' t).1, ht]
    induction t with
    | zero => exact ⟨h0, key 0 h0⟩
    | succ t ih =>
      have h1 : x (t + 1) ∘ Sum.inl = x' (t + 1) ∘ Sum.inl := by
        rw [(bkS_policy E hS Q hQ G hz hza hx t).2, (bkS_policy E hS Q hQ G hz hza hx' t).2,
          ih.2]
      exact ⟨h1, key _ h1⟩
  exact funext fun t => (hk t).2

/-- **Existence** in the stochastic Theorem 1.4.2 (Miao, pp. 53–54): if `P_uy` has a right
inverse `Q`, then for every `F_0`-measurable `k₀` and every stable adapted `z` there is a stable
solution with `k`-part `k₀`: `x₀ = (k₀, Q(u₀ − P_ukk₀))` and
`x_{t+1} = Wx_t + Gz_t + (0, Q(u_{t+1} − E_tu_{t+1}))`, `u` the forward solution (2.12). -/
theorem bkS_exists [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) (k₀ : κ → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) :
    ∃ x, bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀ := by
  have hS' := hS
  obtain ⟨-, hRP, hPW, hJs, hJu⟩ := hS'
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  set c := fun t => matAct P (matAct G (z t)) ∘ Sum.inr
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P (bkS_stable_matAct G hz))
  have hc : ∀ t, ‖c t‖ ≤ C := fun t => (bkS_norm_comp_inr_le _).trans (hC t)
  have hza' := (bkS_isAdaptedV_iff E z).1 hza
  have hca : ∀ t, Evec E t (c t) = c t := fun t => by
    simp only [c]
    rw [bkS_Evec_comp, Evec_matAct, Evec_matAct, hza' t]
  set f := bkS_fwd E Ju c
  have hfa : ∀ t, Evec E t (f t) = f t := bkS_fwd_adapted E hKa hc
  have hfr : ∀ t, Evec E t (f (t + 1)) = matAct Ju (f t) + c t := bkS_fwd_rec E hdet hKa hc hca
  set η : ℕ → υ → V := fun t => matAct Q (f (t + 1) - Evec E t (f (t + 1)))
  set x₀ : κ ⊕ υ → V := Sum.elim k₀ (matAct Q (f 0 - matAct P.toBlocks₂₁ k₀))
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℕ → κ ⊕ υ → V, x 0 = x₀ ∧
      ∀ t, x (t + 1) = matAct W (x t) + matAct G (z t) + Sum.elim (0 : κ → V) (η t) :=
    ⟨fun t => Nat.rec x₀ (fun t xt => matAct W xt + matAct G (z t) + Sum.elim (0 : κ → V) (η t))
      t, rfl,
      fun _ => rfl⟩
  -- the unstable part follows the forward solution
  have hu : ∀ t, matAct P (x t) ∘ Sum.inr = f t := fun t => by
    induction t with
    | zero =>
      rw [hx0, bkS_comp_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, matAct_mul, hQ, matAct_one]
      abel
    | succ t ih =>
      rw [hx t, matAct_add, matAct_add, bkS_add_comp, bkS_add_comp, bkS_split_inr hPW, ih,
        bkS_comp_inr P (Sum.elim (0 : κ → V) (η t)), Sum.elim_comp_inl, Sum.elim_comp_inr,
        bkS_matAct_zero, zero_add]
      simp only [η]
      rw [matAct_mul P.toBlocks₂₂ Q, hQ, matAct_one]
      have := hfr t
      simp only [c] at this ⊢
      rw [this]
      abel
  -- adaptedness
  have hxa : ∀ t, Evec E t (x t) = x t := fun t => by
    induction t with
    | zero =>
      rw [hx0, bkS_Evec_sumElim, Evec_matAct, bkS_Evec_sub, Evec_matAct, hfa 0,
        show Evec E 0 k₀ = k₀ from funext hk₀]
    | succ t ih =>
      rw [hx t, bkS_Evec_add, bkS_Evec_add, Evec_matAct, Evec_matAct,
        bkS_Evec_of_le E (Nat.le_succ t) ih, bkS_Evec_of_le E (Nat.le_succ t) (hza' t),
        bkS_Evec_sumElim, bkS_Evec_zero]
      simp only [η]
      rw [Evec_matAct, bkS_Evec_sub, hfa (t + 1), bkS_Evec_tower_ge E (Nat.le_succ t)]
  have hEη : ∀ t, Evec E t (Sum.elim (0 : κ → V) (η t)) = 0 := fun t => by
    rw [bkS_Evec_sumElim, bkS_Evec_zero]
    simp only [η]
    rw [Evec_matAct, bkS_Evec_sub, bkS_Evec_idem, sub_self, bkS_matAct_zero, Sum.elim_zero_zero]
  have heq : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t) := fun t => by
    rw [hx t, bkS_Evec_add, bkS_Evec_add, Evec_matAct, Evec_matAct, hxa t, hza' t, hEη t,
      add_zero]
  -- stability: the stable part solves a backward equation driven by bounded terms
  obtain ⟨D, hD⟩ := bkS_fwd_bound E hKa hc
  obtain ⟨cQ, hcQ0, hcQ⟩ := bkS_matAct_bound (V := V) Q
  obtain ⟨cP, hcP0, hcP⟩ := bkS_matAct_bound (V := V) P
  obtain ⟨cR, hcR0, hcR⟩ := bkS_matAct_bound (V := V) R
  obtain ⟨Ks, as, hKas⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  have hη : ∀ t, ‖Sum.elim (0 : κ → V) (η t)‖ ≤ cQ * (D + D) := fun t => by
    refine (bkS_norm_sum_type_le _).trans ?_
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, norm_zero, zero_add]
    exact (hcQ _).trans (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
      (add_le_add (hD _) ((bkS_norm_Evec_le E t _).trans (hD _)))) hcQ0)
  set g := fun t => matAct P (matAct G (z t)) ∘ Sum.inl +
    matAct P (Sum.elim (0 : κ → V) (η t)) ∘ Sum.inl
  have hsr : ∀ t, matAct P (x (t + 1)) ∘ Sum.inl =
      matAct Js (matAct P (x t) ∘ Sum.inl) + g t := fun t => by
    rw [hx t, matAct_add, matAct_add, bkS_add_comp, bkS_add_comp, bkS_split_inl hPW, add_assoc]
  have hg : ∀ t, ‖g t‖ ≤ C + cP * (cQ * (D + D)) := fun t =>
    (norm_add_le _ _).trans (add_le_add ((bkS_norm_comp_inl_le _).trans (hC t))
      ((bkS_norm_comp_inl_le _).trans ((hcP _).trans (mul_le_mul_of_nonneg_left (hη t) hcP0))))
  have hsb := bkS_bounded_backward hKas (s := fun t => matAct P (x t) ∘ Sum.inl) hsr hg
  refine ⟨x, ⟨heq, (bkS_isAdaptedV_iff E x).2 hxa, fun t i => ?_, (bkS_isStableProc_iff x).2
    ⟨cR * (Ks * ‖matAct P (x 0) ∘ Sum.inl‖ + Ks * (C + cP * (cQ * (D + D))) / (1 - as) + D),
      fun t => ?_⟩⟩, by rw [hx0, Sum.elim_comp_inl]⟩
  · have h1 : E.E t (x (t + 1) (Sum.inl i)) =
        (matAct W (x t) + matAct G (z t)) (Sum.inl i) := congrFun (heq t) (Sum.inl i)
    have h2 : x (t + 1) (Sum.inl i) = (matAct W (x t) + matAct G (z t)) (Sum.inl i) := by
      rw [hx t]
      simp
    simp only [Function.comp_apply]
    rw [h1, h2]
  · have hxt : x t = matAct R (matAct P (x t)) := by rw [matAct_mul, hRP, matAct_one]
    rw [hxt]
    refine (hcR _).trans (mul_le_mul_of_nonneg_left ((bkS_norm_sum_type_le _).trans
      (add_le_add (hsb t) ?_)) hcR0)
    rw [hu t]
    exact hD t

/-- **Theorem 1.4.2 in the stochastic case** (Blanchard–Kahn, Miao, pp. 53–54). Let `A` be
nonsingular and `W = A⁻¹B` have a real block split `PWP⁻¹ = diag(J_s, J_u)` (no eigenvalue on
the unit circle, condition (iii)). Order `x = (k, y)` with `k` predetermined. If (i)
`n_u = n_y` and (ii) `P_uy` is nonsingular, then for every `F_0`-measurable `k₀` and every
stable adapted `z` the system (2.11) has a unique stable adapted solution with `k`
predetermined and `k`-part `k₀`. -/
theorem theorem_1_4_2_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ) (hA : IsUnit A.det)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (_hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → V)
    (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) (z : ℕ → m → V) (hz : IsStableProc z)
    (hza : IsAdaptedV E z) :
    ∃! x : ℕ → κ ⊕ υ → V, IsRESolution E A B Cm z x ∧ IsAdaptedV E x ∧
      IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableProc x := by
  have hiff : ∀ x, (IsRESolution E A B Cm z x ∧ IsAdaptedV E x ∧
      IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableProc x) ↔
      bkS_IsStableSol E (A⁻¹ * B) (A⁻¹ * Cm) z x ∧ x 0 ∘ Sum.inl = k₀ := fun x => by
    rw [eq_2_11_iff E A B Cm hA z x, bkS_IsStableSol]
    tauto
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hii.1 _ hz hza k₀ hk₀
  refine ⟨x, (hiff x).2 ⟨hx, hx0⟩, fun y hy => ?_⟩
  obtain ⟨hy, hy0⟩ := (hiff y).1 hy
  exact bkS_unique E hS Q hii.2 _ hz hza hy hx (hy0.trans hx0.symm)

omit [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ] in
/-- Miao, p. 53: the hypothesis `E_0k₀ = k₀` of `theorem_1_4_2_stoch` is necessary: the initial
value of an adapted solution is `F_0`-measurable. -/
theorem bkS_k0_adapted (E : CondExpSystem ℝ V) {x : ℕ → κ ⊕ υ → V} (hxa : IsAdaptedV E x)
    (i : κ) : E.E 0 (x 0 (Sum.inl i)) = x 0 (Sum.inl i) :=
  hxa 0 (Sum.inl i)

/-! ### Certainty equivalence -/

/-- The trivial system `E_t = id` (no uncertainty): the deterministic case (Miao, p. 54). -/
noncomputable def bkS_trivial (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    CondExpSystem ℝ V where
  E := fun _ => ContinuousLinearMap.id ℝ V
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

theorem bkS_Evec_trivial {ι : Type*} (t : ℕ) (x : ι → V) : Evec (bkS_trivial V) t x = x :=
  rfl

omit [DecidableEq κ] [DecidableEq υ] in
/-- **Certainty equivalence** (Miao, p. 54), the deterministic case: for `E_t = id` on `ℝ`, the
stable adapted solutions of (2.11) with `k` predetermined are exactly the stable solutions of the
deterministic system (1.20) of Chapter 1. -/
theorem certainty_equivalence (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (z : ℕ → m → ℝ) (x : ℕ → κ ⊕ υ → ℝ) :
    (IsRESolution (bkS_trivial ℝ) A B Cm z x ∧ IsAdaptedV (bkS_trivial ℝ) x ∧
        IsPredeterminedBK (bkS_trivial ℝ) (fun t => x t ∘ Sum.inl) ∧ IsStableProc x) ↔
      IsSolution A B Cm z x ∧ IsStableSeq x := by
  have h1 : IsRESolution (bkS_trivial ℝ) A B Cm z x ↔ IsSolution A B Cm z x := by
    simp only [IsRESolution, IsSolution, bkS_Evec_trivial, bkS_matAct_real]
  have h2 : IsStableProc x ↔ IsStableSeq x := by
    rw [bkS_isStableProc_iff, isStableSeq_iff_exists_le]
  rw [h1, h2]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, fun _ _ => rfl, fun _ _ => rfl, h.2⟩⟩

/-- **Certainty equivalence** (Miao, p. 54), the forward solution: for `E_t = id` on `ℝ` the
stochastic forward solution (2.12) is the deterministic one (1.29). -/
theorem certainty_equivalence_fwd (Ju : Matrix τ τ ℝ) (c : ℕ → τ → ℝ) (t : ℕ) :
    bkS_fwd (bkS_trivial ℝ) Ju c t = forwardU Ju c t := by
  simp only [bkS_fwd, forwardU, bkS_Evec_trivial, bkS_matAct_real]

/-- Theorem 1.4.2 (Miao, p. 20) recovered from its stochastic version with `E_t = id`
(certainty equivalence, p. 54). -/
theorem theorem_1_4_2_of_stoch (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → ℝ) (z : ℕ → m → ℝ)
    (hz : IsStableSeq z) :
    ∃! x : ℕ → κ ⊕ υ → ℝ, IsSolution A B Cm z x ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableSeq x := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  have h := theorem_1_4_2_stoch (bkS_trivial ℝ) A B Cm hA hS hi Q hii k₀ (fun _ => rfl) z hz'
    (fun _ _ => rfl)
  refine (existsUnique_congr fun x => ?_).1 h
  have := certainty_equivalence A B Cm z x
  tauto

omit [Fintype τ] [DecidableEq τ] in
/-- Miao, p. 54: if `E_tz_{t+1} = Φz_t` (as for (2.1)), then `E_tz_{t+j} = Φʲz_t`. -/
theorem bkS_Evec_ar (E : CondExpSystem ℝ V) [DecidableEq m] {Φ : Matrix m m ℝ}
    {z : ℕ → m → V} (hza : IsAdaptedV E z) (hΦ : ∀ t, Evec E t (z (t + 1)) = matAct Φ (z t))
    (t j : ℕ) : Evec E t (z (t + j)) = matAct (Φ ^ j) (z t) := by
  induction j with
  | zero => rw [add_zero, pow_zero, matAct_one]; exact (bkS_isAdaptedV_iff E z).1 hza t
  | succ j ih =>
    rw [← add_assoc, ← bkS_Evec_tower_le E (Nat.le_add_right t j), hΦ, Evec_matAct, ih,
      matAct_mul, ← pow_succ']

/-- **Certainty equivalence** (Miao, p. 54): if `E_tz_{t+1} = Φz_t` (as for (2.1)), the forward
solution (2.12) is `u_t = −∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the same expression as in the deterministic
case `z_{t+1} = Φz_t` (`Σ = 0`, `certainty_equivalence_ar_det`). -/
theorem certainty_equivalence_ar [CompleteSpace V] (E : CondExpSystem ℝ V) [DecidableEq m]
    {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a) (Cu : Matrix τ m ℝ)
    {Φ : Matrix m m ℝ} {z : ℕ → m → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    (hΦ : ∀ t, Evec E t (z (t + 1)) = matAct Φ (z t)) (t : ℕ) :
    bkS_fwd E Ju (fun t => matAct Cu (z t)) t =
      -∑' j, matAct (Ju⁻¹ ^ (j + 1) * Cu * Φ ^ j) (z t) := by
  rw [eq_2_12 E hM Cu hz t]
  congr 1
  refine tsum_congr fun j => ?_
  rw [bkS_Evec_ar E hza hΦ, matAct_mul]

/-- **Certainty equivalence** (Miao, p. 54), deterministic side: for `z_{t+1} = Φz_t` the
deterministic forward solution (1.29) is `−∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the expression of
`certainty_equivalence_ar`. -/
theorem certainty_equivalence_ar_det [DecidableEq m] {Ju : Matrix τ τ ℝ} {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) (Cu : Matrix τ m ℝ) {Φ : Matrix m m ℝ} {z : ℕ → m → ℝ}
    (hz : IsStableSeq z) (hΦ : ∀ t, z (t + 1) = Φ *ᵥ z t) (t : ℕ) :
    forwardU Ju (fun t => Cu *ᵥ z t) t = -∑' j, (Ju⁻¹ ^ (j + 1) * Cu * Φ ^ j) *ᵥ z t := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  have h := certainty_equivalence_ar (bkS_trivial ℝ) hM Cu hz' (fun _ _ => rfl)
    (fun t => by rw [bkS_Evec_trivial, bkS_matAct_real, hΦ]) t
  simp only [bkS_matAct_real] at h
  rw [← certainty_equivalence_fwd, h]

/-! ### Theorem 1.4.3 in the stochastic case -/

/-- The forward solution with zero forcing is zero. -/
theorem bkS_fwd_zero (E : CondExpSystem ℝ V) (Ju : Matrix τ τ ℝ) (t : ℕ) :
    bkS_fwd E Ju (fun _ => (0 : τ → V)) t = 0 := by
  simp [bkS_fwd, bkS_Evec_zero, bkS_matAct_zero]

/-- A stable adapted solution of the homogeneous system `E_td_{t+1} = Wd_t` has `u = 0`. -/
theorem bkS_homog_u_zero [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) {d : ℕ → κ ⊕ υ → V}
    (hd : ∀ t, Evec E t (d (t + 1)) = matAct W (d t)) (hda : ∀ t, Evec E t (d t) = d t)
    {D : ℝ} (hdb : ∀ t, ‖d t‖ ≤ D) (t : ℕ) : matAct P (d t) ∘ Sum.inr = 0 := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨cP, hcP0, hcP⟩ := bkS_matAct_bound (V := V) P
  rw [bkS_fwd_unique E hdet hKa (c := fun _ => 0) (C := 0) (fun _ => by simp)
    (fun t => bkS_Evec_zero E t) (u := fun t => matAct P (d t) ∘ Sum.inr) (D := cP * D)
    (fun t => by rw [bkS_Evec_comp, Evec_matAct, hda t])
    (fun t => (bkS_norm_comp_inr_le _).trans ((hcP _).trans
      (mul_le_mul_of_nonneg_left (hdb t) hcP0)))
    (fun t => by rw [bkS_Evec_comp, Evec_matAct, hd t, add_zero, bkS_split_inr hPW]) t,
    bkS_fwd_zero]

/-- **Theorem 1.4.3, first part, corrected, stochastic case** (Miao, pp. 23, 54): if
`n_u > n_y`, then for every forcing process there is an `F_0`-measurable `k₀` from which no
stable solution starts. (`w ≠ 0` is any `F_0`-measurable random variable, e.g. a constant.) -/
theorem theorem_1_4_3_gt_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card υ < Fintype.card τ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    ∃ k₀ : κ → V, (∀ i, E.E 0 (k₀ i) = k₀ i) ∧
      ¬ ∃ x, bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀ := by
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have hker : LinearMap.ker (Matrix.toLin' R.toBlocks₁₁ᵀ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]; omega)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy
  by_contra h
  push Not at h
  obtain ⟨x, hx, hx0⟩ := h 0 (fun i => by simp)
  obtain ⟨x', hx', hx0'⟩ := h (fun i => y i • w) (fun i => by rw [map_smul, hw0])
  set d := fun t => x' t - x t
  have hd : ∀ t, Evec E t (d (t + 1)) = matAct W (d t) := fun t => by
    simp only [d, bkS_Evec_sub, hx.1 t, hx'.1 t, bkS_matAct_sub]
    abel
  have hda : ∀ t, Evec E t (d t) = d t := fun t => by
    simp only [d, bkS_Evec_sub, (bkS_isAdaptedV_iff E _).1 hx.2.1 t,
      (bkS_isAdaptedV_iff E _).1 hx'.2.1 t]
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff _).1 hx.2.2.2
  obtain ⟨Dx', hDx'⟩ := (bkS_isStableProc_iff _).1 hx'.2.2.2
  have hu := bkS_homog_u_zero E hS hd hda (D := Dx' + Dx)
    (fun t => (norm_sub_le _ _).trans (add_le_add (hDx' t) (hDx t))) 0
  have hd0 : d 0 ∘ Sum.inl = matAct R.toBlocks₁₁ (matAct P (d 0) ∘ Sum.inl) := by
    have e : d 0 = matAct R (matAct P (d 0)) := by rw [matAct_mul, hS.2.1, matAct_one]
    conv_lhs => rw [e]
    rw [bkS_comp_inl R, hu, bkS_matAct_zero, add_zero]
  have hdy : d 0 ∘ Sum.inl = fun i => y i • w := by
    simp only [d]
    rw [bkS_sub_comp, hx0', hx0, sub_zero]
  set s := matAct P (d 0) ∘ Sum.inl
  have key : ∑ i, y i • (d 0 ∘ Sum.inl) i = 0 := by
    rw [hd0]
    simp only [matAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have hj := congrFun hy j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hj
    have hj' : ∑ i, y i * R.toBlocks₁₁ i j = 0 := by
      rw [← hj]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hj', zero_smul]
  rw [hdy] at key
  simp only [smul_smul, ← Finset.sum_smul] at key
  have hpos : ∑ i, y i * y i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
    exact (Finset.sum_pos' (fun i _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩).ne'
  exact hw ((smul_eq_zero.1 key).resolve_left hpos)

/-- **Theorem 1.4.3, second part, corrected, stochastic case** (Miao, pp. 23, 54): if
`n_u < n_y` and there is one stable solution, there are infinitely many with the same `k₀`
(add multiples of `λᵗ`-type stable homogeneous solutions `R(J_sᵗs, 0)w` with `R_kss = 0`, where
`w ≠ 0` is `F_0`-measurable). -/
theorem theorem_1_4_3_lt_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V) {x : ℕ → κ ⊕ υ → V}
    (hx : bkS_IsStableSol E W G z x) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    {x' | bkS_IsStableSol E W G z x' ∧ x' 0 ∘ Sum.inl = x 0 ∘ Sum.inl}.Infinite := by
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have hker : LinearMap.ker (Matrix.toLin' R.toBlocks₁₁) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]; omega)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hs
  set d₀ := R *ᵥ Sum.elim s 0
  have hPd : P *ᵥ d₀ = Sum.elim s 0 := by
    rw [Matrix.mulVec_mulVec, hS.1, Matrix.one_mulVec]
  have hd₀ : d₀ ∈ stableArm P := by
    rw [mem_stableArm, hPd, Sum.elim_comp_inr]
  obtain ⟨d, hd, hd0, Dd, hDd⟩ := (stableArm_iff hS d₀).2 hd₀
  have hdk : d 0 ∘ Sum.inl = 0 := by
    rw [hd0, mulVec_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, hs, Matrix.mulVec_zero,
      add_zero]
  have hdne : d 0 ≠ 0 := fun h => hs0 (by
    have := congrArg (fun v => (P *ᵥ v) ∘ Sum.inl) h
    simpa [hd0, hPd] using this)
  have hwt : ∀ t, E.E t w = w := fun t => by rw [← hw0, E.tower_ge_apply (Nat.zero_le t)]
  set D : ℕ → κ ⊕ υ → V := fun t i => d t i • w
  have hDa : ∀ t s, Evec E s (D t) = D t := fun t s => funext fun i => by
    simp only [D, Evec, map_smul, hwt]
  have hDrec : ∀ t, matAct W (D t) = D (t + 1) := fun t => by
    funext i
    simp only [D, matAct, hd t, Matrix.mulVec, dotProduct, smul_smul, Finset.sum_smul]
  have hDb : ∀ t, ‖D t‖ ≤ Dd * ‖w‖ := fun t =>
    (pi_norm_le_iff_of_nonneg (mul_nonneg ((norm_nonneg _).trans (hDd 0)) (norm_nonneg _))).2
      fun i => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm (d t) i).trans (hDd t))
          (norm_nonneg _)
  have hD0 : D 0 ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hdne
    exact Function.ne_iff.2 ⟨i, smul_ne_zero hi hw⟩
  obtain ⟨hxe, hxa, hxp, hxs⟩ := hx
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff _).1 hxs
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => x + c • D)
    (fun c c' h => ?_) fun c => ⟨⟨fun t => ?_, fun t i => ?_, fun t i => ?_, ?_⟩, ?_⟩
  · have h1 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, add_right_inj] at h1
    exact smul_left_injective ℝ hD0 h1
  · simp only [Pi.add_apply, Pi.smul_apply]
    rw [bkS_Evec_add, bkS_Evec_smul, hxe t, hDa, matAct_add, bkS_matAct_smul, hDrec]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, hxa t i]
    rw [show E.E t (D t i) = D t i from congrFun (hDa t t) i]
  · simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, map_add, map_smul]
    rw [show E.E t (x (t + 1) (Sum.inl i)) = x (t + 1) (Sum.inl i) from hxp t i]
    rw [show E.E t (D (t + 1) (Sum.inl i)) = D (t + 1) (Sum.inl i) from
      congrFun (hDa (t + 1) t) _]
  · refine (bkS_isStableProc_iff _).2 ⟨Dx + |c| * (Dd * ‖w‖), fun t => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans (add_le_add (hDx t) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hDb t) (abs_nonneg c)
  · funext i
    have := congrFun hdk i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [D, this]

/-- Miao, pp. 23, 54, corrected: if `n_u < n_y` and `P_uy` has a right inverse (full row
rank), then for every `F_0`-measurable `k₀` and every stable adapted `z` there are infinitely
many stable solutions with `k`-part `k₀`. -/
theorem theorem_1_4_3_lt_exists_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V}
    (hz : IsStableProc z) (hza : IsAdaptedV E z) (k₀ : κ → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i)
    {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    {x | bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀}.Infinite := by
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hQ G hz hza k₀ hk₀
  have := theorem_1_4_3_lt_stoch E hS hlt G z hx hw hw0
  rwa [hx0] at this

/-- The conditional expectations from date `T` on: `E'_t = E_{t+T}`. -/
def bkS_shift (E : CondExpSystem ℝ V) (T : ℕ) : CondExpSystem ℝ V where
  E := fun t => E.E (t + T)
  norm_le := fun t => E.norm_le (t + T)
  tower_le := fun s t h => E.tower_le (s + T) (t + T) (by omega)
  tower_ge := fun s t h => E.tower_ge (s + T) (t + T) (by omega)

/-- **Corollary 1.4.1 in the stochastic case** (Miao, pp. 22, 53): under the conditions of the
stochastic Theorem 1.4.2, if `z_t = z̄` for `t ≥ T`, the stable solution converges (in norm) to
`x̄ = (A − B)⁻¹Cz̄`. After `T` the deviation `d` from `x̄` solves the homogeneous system, its
`u`-part vanishes, and since `R_ks` is invertible the predetermined `k` makes the stable part
predetermined too, so `s_{t+1} = J_ss_t` exactly. -/
theorem corollary_1_4_1_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ) (hA : IsUnit A.det)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) {z : ℕ → m → V}
    (hza : IsAdaptedV E z) (zbar : m → V) (T : ℕ) (hzT : ∀ t, T ≤ t → z t = zbar)
    {x : ℕ → κ ⊕ υ → V} (hx : IsRESolution E A B Cm z x) (hxa : IsAdaptedV E x)
    (hxp : IsPredeterminedBK E (fun t => x t ∘ Sum.inl)) (hxs : IsStableProc x) :
    Tendsto x atTop (𝓝 (matAct ((A - B)⁻¹ * Cm) zbar)) := by
  have hS' := hS
  obtain ⟨hPR, hRP, hPW, hJs, -⟩ := hS'
  have hx' := (eq_2_11_iff E A B Cm hA z x).1 hx
  set W := A⁻¹ * B
  set G := A⁻¹ * Cm
  have hAB := isUnit_sub_det A B hA hS.isUnit_one_sub
  set xb := matAct ((A - B)⁻¹ * Cm) zbar
  have hzb : ∀ t, T ≤ t → Evec E t zbar = zbar := fun t ht => by
    rw [← hzT t ht]; exact (bkS_isAdaptedV_iff E z).1 hza t
  have hxb : ∀ t, T ≤ t → Evec E t xb = xb := fun t ht => by
    simp only [xb]; rw [Evec_matAct, hzb t ht]
  have hbar : xb = matAct W xb + matAct G zbar := by
    have h1 : (A - B) * ((A - B)⁻¹ * Cm) = Cm := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAB, Matrix.one_mul]
    have h2 : W * ((A - B)⁻¹ * Cm) + G = (A - B)⁻¹ * Cm := by
      simp only [W, G]
      rw [Matrix.mul_assoc, ← Matrix.mul_add]
      nth_rewrite 2 [← h1]
      rw [Matrix.sub_mul, add_sub_cancel, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
        Matrix.one_mul]
    simp only [xb]
    rw [matAct_mul, ← bkS_matAct_add_left, h2]
  set E' := bkS_shift E T
  set d : ℕ → κ ⊕ υ → V := fun k => x (k + T) - xb
  have hd : ∀ k, Evec E' k (d (k + 1)) = matAct W (d k) := fun k => by
    change Evec E (k + T) (x (k + 1 + T) - xb) = matAct W (x (k + T) - xb)
    rw [bkS_Evec_sub, hxb _ (by omega), show k + 1 + T = k + T + 1 by ring, hx' (k + T),
      hzT _ (by omega), bkS_matAct_sub]
    conv_lhs => rw [hbar]
    abel
  have hda : ∀ k, Evec E' k (d k) = d k := fun k => by
    change Evec E (k + T) (x (k + T) - xb) = x (k + T) - xb
    rw [bkS_Evec_sub, (bkS_isAdaptedV_iff E x).1 hxa, hxb _ (by omega)]
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff x).1 hxs
  have hu := bkS_homog_u_zero E' hS hd hda (D := Dx + ‖xb‖)
    (fun k => (norm_sub_le _ _).trans (add_le_add (hDx _) le_rfl))
  obtain ⟨hRS, hSR⟩ := rks_inv hPR hRP Q hii
  set S := P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁
  set s : ℕ → σ → V := fun k => matAct P (d k) ∘ Sum.inl
  have hdk : ∀ k, d k ∘ Sum.inl = matAct R.toBlocks₁₁ (s k) := fun k => by
    have e : d k = matAct R (matAct P (d k)) := by rw [matAct_mul, hRP, matAct_one]
    conv_lhs => rw [e]
    rw [bkS_comp_inl R, hu k, bkS_matAct_zero, add_zero]
  have hsk : ∀ k, s k = matAct S (d k ∘ Sum.inl) := fun k => by
    rw [hdk, matAct_mul, hSR, matAct_one]
  -- the stable part is predetermined, hence `s_{k+1} = J_ss_k`
  have hpre : ∀ k, Evec E' k (d (k + 1) ∘ Sum.inl) = d (k + 1) ∘ Sum.inl := fun k => by
    change Evec E (k + T) ((x (k + 1 + T) - xb) ∘ Sum.inl) = (x (k + 1 + T) - xb) ∘ Sum.inl
    rw [bkS_sub_comp, bkS_Evec_sub, bkS_Evec_comp, bkS_Evec_comp, hxb _ (by omega)]
    congr 1
    funext i
    rw [show k + 1 + T = k + T + 1 by ring]
    exact hxp (k + T) i
  have hsr : ∀ k, s (k + 1) = matAct Js (s k) := fun k => by
    have h1 : Evec E' k (s (k + 1)) = s (k + 1) := by
      rw [hsk, Evec_matAct, hpre]
    have h2 : Evec E' k (s (k + 1)) = matAct Js (s k) := by
      simp only [s]
      rw [bkS_Evec_comp, Evec_matAct, hd k, bkS_split_inl hPW]
    rw [← h1, h2]
  have hs : ∀ k, s k = matAct (Js ^ k) (s 0) := fun k => by
    induction k with
    | zero => rw [pow_zero, matAct_one]
    | succ k ih => rw [hsr, ih, bkS_matAct_pow_succ]
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  obtain ⟨cR, hcR0, hcR⟩ := bkS_matAct_bound (V := V) R
  have hle : ∀ k, ‖d k‖ ≤ cR * (K * ‖s 0‖) * a ^ k := fun k => by
    have e : d k = matAct R (matAct P (d k)) := by rw [matAct_mul, hRP, matAct_one]
    rw [e]
    refine (hcR _).trans ?_
    have h1 : ‖matAct P (d k)‖ ≤ ‖s k‖ := by
      refine (bkS_norm_sum_type_le _).trans ?_
      rw [hu k, norm_zero, add_zero]
    calc cR * ‖matAct P (d k)‖ ≤ cR * ‖s k‖ := mul_le_mul_of_nonneg_left h1 hcR0
      _ ≤ cR * (K * a ^ k * ‖s 0‖) :=
          mul_le_mul_of_nonneg_left (by rw [hs k]; exact bkS_geom_decay hKa k _) hcR0
      _ = cR * (K * ‖s 0‖) * a ^ k := by ring
  have hlim : Tendsto (fun k => cR * (K * ‖s 0‖) * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hKa.1 hKa.2.1).const_mul
      (cR * (K * ‖s 0‖))
  have hdlim : Tendsto d atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hle hlim)
  have h2 := hdlim.add_const xb
  simp only [d, sub_add_cancel, zero_add] at h2
  exact (tendsto_add_atTop_iff_nat T).1 h2

end Miao.NeoclassicalGrowth
