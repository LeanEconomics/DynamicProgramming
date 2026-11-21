/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.Basics
import RationalExpectations.Nonsingular

/-!
# Stable processes and the forward solution (2.12)

Miao, §2.3, pp. 52–54. The system (2.11) `AE_tx_{t+1} = Bx_t + Cz_t` is `IsRESolution`
(Basics); the regularity Assumption 1.4.1 that the book maintains is automatic once `A` is
nonsingular, which is the Blanchard–Kahn case treated here (`isRegular_of_isUnit_det`).
Processes are vectors `ι → V` of elements of a normed space `V` carrying a `CondExpSystem`;
their norm is the max norm `maxⱼ ‖xⱼ‖` of Definition 2.3.1.

* Tools: matrices acting on `ι → V` (`matAct`) are linear, continuous and commute with
  convergent sums (`bkS_matAct_hasSum`); a bound `‖Nv‖ ≤ c‖v‖` on real vectors gives the same
  bound on random vectors (`bkS_norm_matAct_le`), so geometric decay `HasGeomDecay` transfers
  (`bkS_geom_decay`).
* **Definition 2.3.1**: stable processes are the bounded ones (`bkS_isStableProc_iff`); they
  stay stable under `E_t`, at any dates (`bkS_stable_Evec`), under shifts, matrices and sums.
* Summability: for a stable `z` and `M` with geometric decay, `∑ⱼ MʲE_tz_{t+j}` converges, with
  the bound `KC/(1 − a)` (`bkS_summable_geom`).
* **The forward solution (2.12)**: `bkS_fwd`, in the printed form
  `u_t = −∑ⱼ J_u^{−j−1}C_u*E_tz_{t+j}` (`eq_2_12`; the printed formula is right). It is adapted,
  bounded, solves `E_tu_{t+1} = J_uu_t + c_t` (`bkS_fwd_rec`), and is the only bounded adapted
  solution (`bkS_fwd_unique`): the difference `e` of two solutions satisfies
  `e_t = J_u^{−k}E_te_{t+k}` for every `k` (law of iterated expectations), and
  `‖J_u^{−k}‖ → 0`, `‖E_t‖ ≤ 1`.
* **Jump-only systems** (`bkS_jump_unique`): if `W` is invertible and `W⁻¹` decays
  geometrically, `E_tx_{t+1} = Wx_t + c_t` has exactly one stable adapted solution,
  `x_t = −∑ⱼ W^{−j−1}E_tc_{t+j}`.
* (2.11) with `A` nonsingular is `E_tx_{t+1} = Wx_t + A⁻¹Cz_t`, `W = A⁻¹B` (`eq_2_11_iff`).

Departure: the book requires solutions (and `z`) to be adapted without saying so in (2.11);
here adaptedness is an explicit hypothesis or conclusion (`IsAdaptedV`).
-/

open Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Matrices acting on random vectors -/

theorem bkS_matAct_sub {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x y : κ → V) :
    matAct M (x - y) = matAct M x - matAct M y := by
  funext i
  simp [matAct, smul_sub, Finset.sum_sub_distrib]

theorem bkS_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → V) :
    matAct M (-x) = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem bkS_matAct_zero {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) :
    matAct M (0 : κ → V) = 0 := by
  funext i
  simp [matAct]

theorem bkS_matAct_zero_left {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ ℝ) x = 0 := by
  funext i
  simp [matAct]

theorem bkS_matAct_smul {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (c : ℝ) (x : κ → V) :
    matAct M (c • x) = c • matAct M x := by
  funext i
  simp [matAct, Finset.smul_sum, smul_comm c]

theorem bkS_matAct_sum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (s : Finset α)
    (f : α → κ → V) : matAct M (∑ a ∈ s, f a) = ∑ a ∈ s, matAct M (f a) := by
  funext i
  simp only [matAct, Finset.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem bkS_matAct_add_left {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℝ) (x : κ → V) :
    matAct (M + N) x = matAct M x + matAct N x := by
  funext i
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem bkS_matAct_sub_left {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℝ) (x : κ → V) :
    matAct (M - N) x = matAct M x - matAct N x := by
  funext i
  simp [matAct, sub_smul, Finset.sum_sub_distrib]

theorem bkS_matAct_pow_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (k : ℕ)
    (x : ι → V) : matAct (M ^ (k + 1)) x = matAct M (matAct (M ^ k) x) := by
  rw [matAct_mul, pow_succ']

/-- `matAct M` as a continuous linear map. -/
noncomputable def bkS_matCLM {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) :
    (κ → V) →L[ℝ] (ι → V) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : κ => V) j

theorem bkS_matCLM_apply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → V) :
    bkS_matCLM M x = matAct M x := by
  funext i
  simp [bkS_matCLM, matAct]

/-- A matrix commutes with convergent sums of random vectors. -/
theorem bkS_matAct_hasSum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℝ) {f : α → κ → V}
    {s : κ → V} (h : HasSum f s) : HasSum (fun j => matAct M (f j)) (matAct M s) := by
  simpa [bkS_matCLM_apply] using (bkS_matCLM M).hasSum h

/-- `matAct` on real vectors is `*ᵥ`. -/
theorem bkS_matAct_real {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    matAct M x = M *ᵥ x := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

/-- A bound `‖Nv‖ ≤ c‖v‖` on real vectors gives `‖Nx‖ ≤ c‖x‖` on random vectors: the row sums
`∑ⱼ |Nᵢⱼ|` are values `(Ns)ᵢ` at sign vectors `s`. -/
theorem bkS_norm_matAct_le {ι κ : Type*} [Fintype ι] [Fintype κ] (N : Matrix ι κ ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hN : ∀ v : κ → ℝ, ‖N *ᵥ v‖ ≤ c * ‖v‖) (x : κ → V) :
    ‖matAct N x‖ ≤ c * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).2 fun i => ?_
  set s : κ → ℝ := fun j => if 0 ≤ N i j then 1 else -1
  have hs : ‖s‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    simp only [s]
    split_ifs <;> simp
  have hrow : ∑ j, |N i j| ≤ c := by
    have h1 : ∑ j, |N i j| = (N *ᵥ s) i := by
      simp only [Matrix.mulVec, dotProduct, s]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rw [abs_of_nonneg h, mul_one]
      · rw [abs_of_neg (not_le.1 h), mul_neg_one]
    rw [h1]
    calc (N *ᵥ s) i ≤ |(N *ᵥ s) i| := le_abs_self _
      _ = ‖(N *ᵥ s) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖N *ᵥ s‖ := norm_le_pi_norm _ i
      _ ≤ c * ‖s‖ := hN s
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one c
  calc ‖matAct N x i‖ = ‖∑ j, N i j • x j‖ := rfl
    _ ≤ ∑ j, ‖N i j • x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |N i j| * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |N i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ c * ‖x‖ := by gcongr

/-- Every matrix is a bounded operator on random vectors. -/
theorem bkS_matAct_bound {ι κ : Type*} [Fintype ι] [Fintype κ] (N : Matrix ι κ ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ x : κ → V, ‖matAct N x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_bound N
  exact ⟨c, hc0, bkS_norm_matAct_le N hc0 hc⟩

/-- Geometric decay transfers to random vectors: `‖Mᵏx‖ ≤ Kaᵏ‖x‖`. -/
theorem bkS_geom_decay {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ}
    (hM : HasGeomDecay M K a) (k : ℕ) (x : ι → V) :
    ‖matAct (M ^ k) x‖ ≤ K * a ^ k * ‖x‖ :=
  bkS_norm_matAct_le _ (mul_nonneg hM.2.2.1 (pow_nonneg hM.1 k)) (hM.2.2.2 k) x

/-! ### Conditional expectations of random vectors -/

/-- `E_t` on random vectors as a continuous linear map. -/
noncomputable def bkS_ECLM (E : CondExpSystem ℝ V) (ι : Type*) (t : ℕ) :
    (ι → V) →L[ℝ] (ι → V) :=
  ContinuousLinearMap.pi fun i => (E.E t).comp (ContinuousLinearMap.proj i)

theorem bkS_ECLM_apply (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    bkS_ECLM E ι t x = Evec E t x := by
  funext i
  simp [bkS_ECLM, Evec]

theorem bkS_Evec_hasSum (E : CondExpSystem ℝ V) {ι α : Type*} (t : ℕ) {f : α → ι → V}
    {s : ι → V} (h : HasSum f s) : HasSum (fun j => Evec E t (f j)) (Evec E t s) := by
  simpa [bkS_ECLM_apply] using (bkS_ECLM E ι t).hasSum h

theorem bkS_Evec_add (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x y : ι → V) :
    Evec E t (x + y) = Evec E t x + Evec E t y := by
  funext i
  simp [Evec]

theorem bkS_Evec_sub (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x y : ι → V) :
    Evec E t (x - y) = Evec E t x - Evec E t y := by
  funext i
  simp [Evec]

theorem bkS_Evec_neg (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    Evec E t (-x) = -Evec E t x := by
  funext i
  simp [Evec]

theorem bkS_Evec_zero (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) :
    Evec E t (0 : ι → V) = 0 := by
  funext i
  simp [Evec]

theorem bkS_Evec_smul (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (c : ℝ) (x : ι → V) :
    Evec E t (c • x) = c • Evec E t x := by
  funext i
  simp [Evec]

theorem bkS_Evec_sumElim (E : CondExpSystem ℝ V) {κ υ : Type*} (t : ℕ) (a : κ → V)
    (b : υ → V) : Evec E t (Sum.elim a b) = Sum.elim (Evec E t a) (Evec E t b) := by
  funext i
  rcases i with i | i <;> rfl

/-- The law of iterated expectations on random vectors: `E_sE_t = E_s` for `s ≤ t`. -/
theorem bkS_Evec_tower_le (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E s (Evec E t x) = Evec E s x := by
  funext i
  exact E.tower_le_apply h _

/-- `E_tE_s = E_s` for `s ≤ t`. -/
theorem bkS_Evec_tower_ge (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E t (Evec E s x) = Evec E s x := by
  funext i
  exact E.tower_ge_apply h _

theorem bkS_Evec_idem (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    Evec E t (Evec E t x) = Evec E t x :=
  bkS_Evec_tower_le E le_rfl x

/-- An `F_s`-measurable random vector is `F_t`-measurable for `t ≥ s`. -/
theorem bkS_Evec_of_le (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t) {x : ι → V}
    (hx : Evec E s x = x) : Evec E t x = x := by
  rw [← hx, bkS_Evec_tower_ge E h]

theorem bkS_norm_Evec_le (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι] (t : ℕ) (x : ι → V) :
    ‖Evec E t x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (E.norm_apply_le t _).trans (norm_le_pi_norm x i)

theorem bkS_isAdaptedV_iff (E : CondExpSystem ℝ V) {ι : Type*} (x : ℕ → ι → V) :
    IsAdaptedV E x ↔ ∀ t, Evec E t (x t) = x t :=
  ⟨fun h t => funext fun i => h t i, fun h t i => congrFun (h t) i⟩

/-! ### Definition 2.3.1: stable processes -/

omit [NormedSpace ℝ V] in
/-- **Definition 2.3.1** (Miao, p. 52): a process is stable iff it is bounded in the max norm
`maxⱼ ‖xⱼ‖`. -/
theorem bkS_isStableProc_iff {ι : Type*} [Fintype ι] (x : ℕ → ι → V) :
    IsStableProc x ↔ ∃ C, ∀ t, ‖x t‖ ≤ C := by
  constructor
  · rintro ⟨M, hM, h⟩
    exact ⟨M, fun t => (pi_norm_le_iff_of_nonneg hM.le).2 fun i => (h t i).le⟩
  · rintro ⟨C, h⟩
    refine ⟨max C 0 + 1, by positivity, fun t i => ?_⟩
    exact (norm_le_pi_norm (x t) i).trans_lt ((h t).trans_lt (by linarith [le_max_left C 0]))

/-- Miao, p. 52: a stable process stays stable under conditional expectations, at any dates:
`t ↦ E_{f(t)}x_{g(t)}` is stable (e.g. `E_tx_{t+j}`, `E_0x_t`). -/
theorem bkS_stable_Evec (E : CondExpSystem ℝ V) {ι : Type*} {x : ℕ → ι → V}
    (hx : IsStableProc x) (f g : ℕ → ℕ) : IsStableProc fun t => Evec E (f t) (x (g t)) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => (E.norm_apply_le _ _).trans_lt (h _ i)⟩

omit [NormedSpace ℝ V] in
/-- Miao, p. 52: shifts of a stable process are stable. -/
theorem bkS_stable_shift {ι : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (j : ℕ) :
    IsStableProc fun t => x (t + j) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => h _ i⟩

/-- Miao, p. 52: a matrix maps stable processes to stable processes. -/
theorem bkS_stable_matAct {ι κ : Type*} [Finite ι] [Fintype κ] (M : Matrix ι κ ℝ)
    {x : ℕ → κ → V} (hx : IsStableProc x) : IsStableProc fun t => matAct M (x t) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff x).1 hx
  obtain ⟨c, hc0, hc⟩ := bkS_matAct_bound (V := V) M
  exact (bkS_isStableProc_iff _).2 ⟨c * C, fun t => (hc _).trans (by gcongr; exact hC t)⟩

omit [NormedSpace ℝ V] in
/-- Sums of stable processes are stable. -/
theorem bkS_stable_add {ι : Type*} {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t + y t := by
  obtain ⟨M, hM, h⟩ := hx
  obtain ⟨N, hN, h'⟩ := hy
  exact ⟨M + N, by positivity, fun t i => (norm_add_le _ _).trans_lt (add_lt_add (h t i) (h' t i))⟩

/-- Miao, p. 52: for a stable `z` (`‖z_t‖ ≤ C`) and `M` with geometric decay, `∑ⱼ MʲE_tz_{t+j}`
converges, with norm at most `KC/(1 − a)`. -/
theorem bkS_summable_geom [CompleteSpace V] (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ} (hM : HasGeomDecay M K a) {z : ℕ → ι → V}
    {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (t : ℕ) :
    Summable (fun j => matAct (M ^ j) (Evec E t (z (t + j)))) ∧
      ‖∑' j, matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * C / (1 - a) := by
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hb : ∀ j, ‖matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * C * a ^ j := fun j =>
    calc ‖matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * a ^ j * ‖Evec E t (z (t + j))‖ :=
          bkS_geom_decay hM j _
      _ ≤ K * a ^ j * C := mul_le_mul_of_nonneg_left ((bkS_norm_Evec_le E t _).trans (hz _))
          (mul_nonneg hM.2.2.1 (pow_nonneg ha0 j))
      _ = K * C * a ^ j := by ring
  have hg := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (K * C)
  refine ⟨Summable.of_norm_bounded hg.summable hb, ?_⟩
  have := tsum_of_norm_bounded hg hb
  simpa [div_eq_mul_inv] using this

/-! ### The forward solution (2.12) -/

/-- Miao, (2.12), p. 54: the forward-looking solution
`u_t = −J_u⁻¹∑_{j ≥ 0} J_u^{−j}E_tc_{t+j}` of `E_tu_{t+1} = J_uu_t + c_t`. -/
noncomputable def bkS_fwd {τ : Type*} [Fintype τ] [DecidableEq τ] (E : CondExpSystem ℝ V)
    (Ju : Matrix τ τ ℝ) (c : ℕ → τ → V) (t : ℕ) : τ → V :=
  -matAct Ju⁻¹ (∑' j, matAct (Ju⁻¹ ^ j) (Evec E t (c (t + j))))

/-- Miao, (2.12), p. 54, in the printed form: with `c_t = C_u*z_t`,
`u_t = −∑_{j ≥ 0} J_u^{−j−1}C_u*E_tz_{t+j}`. -/
theorem eq_2_12 [CompleteSpace V] (E : CondExpSystem ℝ V) {τ m : Type*} [Fintype τ]
    [DecidableEq τ] [Fintype m] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    (Cu : Matrix τ m ℝ) {z : ℕ → m → V} (hz : IsStableProc z) (t : ℕ) :
    bkS_fwd E Ju (fun t => matAct Cu (z t)) t =
      -∑' j, matAct (Ju⁻¹ ^ (j + 1) * Cu) (Evec E t (z (t + j))) := by
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct Cu hz)
  have hs := (bkS_summable_geom E hM hC t).1
  unfold bkS_fwd
  rw [((bkS_matAct_hasSum Ju⁻¹ hs.hasSum).tsum_eq).symm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [Evec_matAct, matAct_mul, matAct_mul, ← pow_succ']

/-- The forward solution is adapted: `E_tu_t = u_t`. -/
theorem bkS_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) (t : ℕ) :
    Evec E t (bkS_fwd E Ju c t) = bkS_fwd E Ju c t := by
  have hs := (bkS_summable_geom E hM hc t).1
  unfold bkS_fwd
  rw [bkS_Evec_neg, Evec_matAct, ((bkS_Evec_hasSum E t hs.hasSum).tsum_eq).symm]
  congr 2
  refine tsum_congr fun j => ?_
  rw [Evec_matAct, bkS_Evec_idem]

/-- The forward solution is bounded. -/
theorem bkS_fwd_bound [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) :
    ∃ D, ∀ t, ‖bkS_fwd E Ju c t‖ ≤ D := by
  obtain ⟨b, hb0, hb⟩ := bkS_matAct_bound (V := V) Ju⁻¹
  refine ⟨b * (K * C / (1 - a)), fun t => ?_⟩
  rw [bkS_fwd, norm_neg]
  exact (hb _).trans (mul_le_mul_of_nonneg_left (bkS_summable_geom E hM hc t).2 hb0)

/-- The forward solution solves `E_tu_{t+1} = J_uu_t + c_t` when `c` is adapted. -/
theorem bkS_fwd_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    (hca : ∀ t, Evec E t (c t) = c t) (t : ℕ) :
    Evec E t (bkS_fwd E Ju c (t + 1)) = matAct Ju (bkS_fwd E Ju c t) + c t := by
  set M := Ju⁻¹
  have hs := (bkS_summable_geom E hM hc t).1
  have hs1 := (bkS_summable_geom E hM hc (t + 1)).1
  -- `S_t = E_tc_t + M S'_t`
  set S' := ∑' j, matAct (M ^ j) (Evec E t (c (t + 1 + j)))
  have hs' : Summable fun j => matAct (M ^ j) (Evec E t (c (t + 1 + j))) := by
    have := (bkS_summable_geom E hM (z := fun s => c (s + 1)) (fun s => hc _) t).1
    refine this.congr fun j => ?_
    rw [show t + j + 1 = t + 1 + j by ring]
  have hS : ∑' j, matAct (M ^ j) (Evec E t (c (t + j))) = c t + matAct M S' := by
    rw [hs.tsum_eq_zero_add, ((bkS_matAct_hasSum M hs'.hasSum).tsum_eq).symm]
    simp only [pow_zero, matAct_one, add_zero, hca t]
    congr 1
    refine tsum_congr fun j => ?_
    rw [matAct_mul, ← pow_succ', show t + (j + 1) = t + 1 + j by ring]
  -- `E_tS_{t+1} = S'_t`
  have hES : Evec E t (∑' j, matAct (M ^ j) (Evec E (t + 1) (c (t + 1 + j)))) = S' := by
    rw [((bkS_Evec_hasSum E t hs1.hasSum).tsum_eq).symm]
    refine tsum_congr fun j => ?_
    rw [Evec_matAct, bkS_Evec_tower_le E (Nat.le_succ t)]
  unfold bkS_fwd
  rw [bkS_Evec_neg, Evec_matAct, hES, hS, bkS_matAct_neg, matAct_mul,
    Matrix.mul_nonsing_inv _ hdet, matAct_one]
  abel

/-- The forward solution is the only bounded adapted solution of `E_tu_{t+1} = J_uu_t + c_t`
(Miao, p. 54): the difference `e` of two solutions satisfies `e_t = J_u^{−k}E_te_{t+k}`. -/
theorem bkS_fwd_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    (hca : ∀ t, Evec E t (c t) = c t) {u : ℕ → τ → V} (hua : ∀ t, Evec E t (u t) = u t)
    {D : ℝ} (hu : ∀ t, ‖u t‖ ≤ D) (hrec : ∀ t, Evec E t (u (t + 1)) = matAct Ju (u t) + c t)
    (t : ℕ) : u t = bkS_fwd E Ju c t := by
  set M := Ju⁻¹
  obtain ⟨D', hD'⟩ := bkS_fwd_bound E hM hc
  set e := fun s => u s - bkS_fwd E Ju c s
  have he : ∀ s, e s = matAct M (Evec E s (e (s + 1))) := fun s => by
    simp only [e, bkS_Evec_sub, hrec s, bkS_fwd_rec E hdet hM hc hca s]
    rw [show matAct Ju (u s) + c s - (matAct Ju (bkS_fwd E Ju c s) + c s) =
      matAct Ju (u s - bkS_fwd E Ju c s) by rw [bkS_matAct_sub]; abel, matAct_mul,
      Matrix.nonsing_inv_mul _ hdet, matAct_one]
  have hea : ∀ s, Evec E s (e s) = e s := fun s => by
    simp only [e, bkS_Evec_sub, hua s, bkS_fwd_adapted E hM hc s]
  have hk : ∀ k, e t = matAct (M ^ k) (Evec E t (e (t + k))) := fun k => by
    induction k with
    | zero => simp [hea t, matAct_one]
    | succ k ih =>
      rw [ih]
      conv_lhs => rw [he (t + k)]
      rw [Evec_matAct, bkS_Evec_tower_le E (by omega), matAct_mul, ← pow_succ,
        show t + k + 1 = t + (k + 1) by ring]
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hle : ∀ k, ‖e t‖ ≤ K * (D + D') * a ^ k := fun k => by
    rw [hk k]
    calc ‖matAct (M ^ k) (Evec E t (e (t + k)))‖ ≤ K * a ^ k * ‖Evec E t (e (t + k))‖ :=
          bkS_geom_decay hM k _
      _ ≤ K * a ^ k * (D + D') := mul_le_mul_of_nonneg_left ((bkS_norm_Evec_le E t _).trans
          ((norm_sub_le _ _).trans (add_le_add (hu _) (hD' _))))
          (mul_nonneg hM.2.2.1 (pow_nonneg ha0 k))
      _ = K * (D + D') * a ^ k := by ring
  have hlim : Tendsto (fun k => K * (D + D') * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul (K * (D + D'))
  have h0 : e t = 0 := norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)
  exact sub_eq_zero.1 h0

/-- **Jump-only systems** (Miao, pp. 53–54, with `n_k = 0`): if `W` is invertible and `W⁻¹`
decays geometrically (all eigenvalues of `W` outside the unit circle), then for every stable
adapted `c` the system `E_tx_{t+1} = Wx_t + c_t` has exactly one stable adapted solution, the
forward solution `x_t = −∑ⱼ W^{−j−1}E_tc_{t+j}`. -/
theorem bkS_jump_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {W : Matrix ι ι ℝ} (hdet : IsUnit W.det) {K a : ℝ}
    (hM : HasGeomDecay W⁻¹ K a) {c : ℕ → ι → V} (hc : IsStableProc c) (hca : IsAdaptedV E c) :
    ∃! x : ℕ → ι → V, (∀ t, Evec E t (x (t + 1)) = matAct W (x t) + c t) ∧
      IsAdaptedV E x ∧ IsStableProc x := by
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff c).1 hc
  have hca' := (bkS_isAdaptedV_iff E c).1 hca
  obtain ⟨D, hD⟩ := bkS_fwd_bound E hM hC
  refine ⟨bkS_fwd E W c, ⟨bkS_fwd_rec E hdet hM hC hca',
    (bkS_isAdaptedV_iff E _).2 (bkS_fwd_adapted E hM hC), (bkS_isStableProc_iff _).2 ⟨D, hD⟩⟩,
    fun x ⟨hx, hxa, hxs⟩ => funext fun t => ?_⟩
  obtain ⟨D', hD'⟩ := (bkS_isStableProc_iff x).1 hxs
  exact bkS_fwd_unique E hdet hM hC hca' ((bkS_isAdaptedV_iff E x).1 hxa) hD' hx t

/-- Miao, (2.11), p. 52, with `A` nonsingular: `AE_tx_{t+1} = Bx_t + Cz_t` iff
`E_tx_{t+1} = Wx_t + A⁻¹Cz_t` with `W = A⁻¹B`. -/
theorem eq_2_11_iff (E : CondExpSystem ℝ V) {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → V)
    (x : ℕ → n → V) :
    IsRESolution E A B C z x ↔
      ∀ t, Evec E t (x (t + 1)) = matAct (A⁻¹ * B) (x t) + matAct (A⁻¹ * C) (z t) := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← matAct_mul, ← matAct_mul, ← matAct_add, ← h, matAct_mul,
      Matrix.nonsing_inv_mul _ hA, matAct_one]
  · rw [h, matAct_add, matAct_mul, matAct_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.one_mul]

/-- Miao, p. 52: with `A` nonsingular the regularity Assumption 1.4.1 that the book maintains
holds automatically. -/
theorem bkS_regular_of_det {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) : IsRegular A B :=
  isRegular_of_isUnit_det A B hA

end Miao.RationalExpectations
