/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DifferenceEquations.Nonsingular
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# When the Blanchard–Kahn conditions fail: Theorem 1.4.3

Miao, §1.4.1, p. 23. The book states: "If `n_u > n_y`, then there is no solution to (1.22). If
`n_u < n_y`, then there are infinitely many solutions to (1.22)."

**As printed, the first claim is false**: with `A` nonsingular, (1.22) has a (unique) solution
from every `x₀ = (k₀, y₀)` (`exists_unique_solution`); `theorem_1_4_3_printed_gt_false` gives a
block split with `n_u = 1 > n_y = 0` and a solution. The second claim is true but empty: as soon
as `n_y ≥ 1` there are infinitely many solutions with a given `k₀`, whatever `n_u`
(`theorem_1_4_3_printed_lt`). The intended statements concern **stable** solutions:

* `theorem_1_4_3_gt`: if `n_u > n_y`, then for every `z` there is a `k₀` from which no
  stable solution starts (the admissible `k₀` lie in a translate of the range of `R_ks`, of
  dimension at most `n_s < n_k`).
* `theorem_1_4_3_lt`: if `n_u < n_y` and one stable solution with initial `k₀` exists, there
  are infinitely many (add multiples of a stable homogeneous solution `R(J_sᵗs, 0)` with
  `R_kss = 0`, `s ≠ 0`, which exists since `n_s > n_k`).
* `theorem_1_4_3_lt_exists`: if moreover `P_uy` has full row rank (a right inverse), a stable
  solution exists for every `k₀` and every bounded `z`, hence infinitely many.
* Without the rank condition, `n_u < n_y` does not give any stable solution:
  `theorem_1_4_3_lt_counterexample` (`n_k = 1`, `n_y = 2`, `n_u = 1`, the unstable root sits on
  the predetermined variable, and `k₀ = 1` has no stable solution).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

variable {κ υ σ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] {m : Type*} [Fintype m]

/-- The predetermined part of the initial value of a stable homogeneous solution lies in the
range of `R_ks`. -/
theorem homog_stable_mem_range {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t)
    {D : ℝ} (hD : ∀ t, ‖x t‖ ≤ D) :
    x 0 ∘ Sum.inl ∈ LinearMap.range (Matrix.toLin' R.toBlocks₁₁) := by
  have h0 := (mem_stableArm P (x 0)).1 ((stableArm_iff hS (x 0)).1 ⟨x, hx, rfl, D, hD⟩)
  refine ⟨(P *ᵥ x 0) ∘ Sum.inl, ?_⟩
  have : x 0 = R *ᵥ (P *ᵥ x 0) := by rw [Matrix.mulVec_mulVec, hS.2.1, Matrix.one_mulVec]
  conv_rhs => rw [this, mulVec_comp_inl, h0, Matrix.mulVec_zero, add_zero]
  rw [Matrix.toLin'_apply]

/-- **Theorem 1.4.3, first part, corrected** (Miao, p. 23): if `n_u > n_y`, then for every
forcing sequence (bounded or not) there is an initial `k₀` from which (1.22) has no stable
solution. -/
theorem theorem_1_4_3_gt {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card υ < Fintype.card τ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) :
    ∃ k₀ : κ → ℝ, ¬ ∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D := by
  by_contra h
  push Not at h
  choose x hx hx0 D hD using h
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have htop : LinearMap.range (Matrix.toLin' R.toBlocks₁₁) = ⊤ := by
    refine eq_top_iff.2 fun k _ => ?_
    set d := fun t => x k t - x 0 t
    have hd : ∀ t, d (t + 1) = W *ᵥ d t := fun t => by
      simp only [d, hx k t, hx 0 t, Matrix.mulVec_sub]
      abel
    have := homog_stable_mem_range hS hd (D := D k + D 0) fun t =>
      (norm_sub_le _ _).trans (add_le_add (hD k t) (hD 0 t))
    have e : d 0 ∘ Sum.inl = k := by
      funext i
      have h1 := congrFun (hx0 k) i
      have h2 := congrFun (hx0 0) i
      simp only [Function.comp_apply, Pi.zero_apply] at h1 h2
      simp [d, h1, h2]
    rwa [e] at this
  have hle := LinearMap.finrank_range_le (Matrix.toLin' R.toBlocks₁₁)
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hle
  omega

/-- **Theorem 1.4.3, second part, corrected** (Miao, p. 23): if `n_u < n_y` and (1.22) has one
stable solution with initial `k₀`, it has infinitely many. -/
theorem theorem_1_4_3_lt {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (x : ℕ → κ ⊕ υ → ℝ)
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (hxb : ∃ D, ∀ t, ‖x t‖ ≤ D) :
    {x' : ℕ → κ ⊕ υ → ℝ | (∀ t, x' (t + 1) = W *ᵥ x' t + G *ᵥ z t) ∧
      x' 0 ∘ Sum.inl = x 0 ∘ Sum.inl ∧ ∃ D, ∀ t, ‖x' t‖ ≤ D}.Infinite := by
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
  obtain ⟨Dx, hDx⟩ := hxb
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => x + c • d) (fun c c' h => ?_)
    fun c => ⟨fun t => ?_, ?_, ⟨Dx + |c| * Dd, fun t => ?_⟩⟩
  · have h1 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, add_right_inj] at h1
    exact smul_left_injective ℝ hdne h1
  · simp only [Pi.add_apply, Pi.smul_apply, hx t, hd t, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel
  · funext i
    have := congrFun hdk i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [this]
  · simp only [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans (add_le_add (hDx t) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hDd t) (abs_nonneg c)

/-- Miao, p. 23, corrected: if `n_u < n_y` and `P_uy` has full row rank (a right inverse), then
for every `k₀` and every bounded `z` there are infinitely many stable solutions. -/
theorem theorem_1_4_3_lt_exists {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (hlt : Fintype.card τ < Fintype.card υ) (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (hz : ∃ C, ∀ t, ‖z t‖ ≤ C) (k₀ : κ → ℝ) :
    {x : ℕ → κ ⊕ υ → ℝ | (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D}.Infinite := by
  obtain ⟨C, hC⟩ := hz
  obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hQ G hC k₀
  have := theorem_1_4_3_lt hS hlt G z x hx hxb
  rwa [hx0, Sum.elim_comp_inl] at this

omit [DecidableEq κ] [DecidableEq υ] in
/-- Miao, p. 23: the second claim of Theorem 1.4.3 as printed ("infinitely many solutions") holds
whenever there is a jump variable, whatever `n_u`: every `y₀` starts a solution. -/
theorem theorem_1_4_3_printed_lt [Nonempty υ] (W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (k₀ : κ → ℝ) :
    {x : ℕ → κ ⊕ υ → ℝ | (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀}.Infinite := by
  obtain ⟨i₀⟩ := ‹Nonempty υ›
  refine Set.infinite_of_injective_forall_mem
    (f := fun c : ℝ => fun t => Nat.rec (Sum.elim k₀ fun _ => c)
      (fun t xt => W *ᵥ xt + G *ᵥ z t) t) (fun c c' h => ?_) fun c => ⟨fun _ => rfl, rfl⟩
  have := congrFun (congrFun h 0) (Sum.inr i₀)
  simpa using this

/-! ### Counterexamples -/

/-- The eigenvalues of `cI` are `c`. -/
theorem hasEigenvalue_smul_one {c : ℝ} {μ : ℂ}
    (h : Module.End.HasEigenvalue
      (Matrix.toLin' ((c • (1 : Matrix σ σ ℝ)).map Complex.ofRealHom)) μ) : μ = c := by
  classical
  obtain ⟨w, hw⟩ := h.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw.2
  have := congrFun h1 i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
    apply_ite (fun r : ℝ => (r : ℂ)), ite_mul] at this
  exact (this.resolve_right hi).symm

/-- Miao, p. 23: the first claim of Theorem 1.4.3 as printed is false. For `k_{t+1} = 2k_t` with
`k` predetermined and no jump variable, the real block split has `n_u = 1 > n_y = 0`, yet
(1.22) has a solution from `k₀ = 1` (the backward solution `k_t = 2ᵗ`, which is not stable). -/
theorem theorem_1_4_3_printed_gt_false :
    IsRealBlockSplit
      (Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
        (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (Matrix.fromBlocks (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) 0)
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 0) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
      (0 : Matrix (Fin 0) (Fin 0) ℝ) ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      Fintype.card (Fin 0) < Fintype.card (Fin 1) ∧
      ∃ x : ℕ → Fin 1 ⊕ Fin 0 → ℝ,
        (∀ t, x (t + 1) = Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
          (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ x t) ∧ x 0 ∘ Sum.inl = fun _ => 1 := by
  refine ⟨⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩, by simp, ?_⟩
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    exact absurd (funext fun i => i.elim0) hw.2
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · obtain ⟨x, hx0, hx⟩ := exists_sol_rec (Matrix.fromBlocks
      ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (0 : Matrix (Fin 1 ⊕ Fin 0) (Fin 0) ℝ) (fun _ => 0) (Sum.elim (fun _ => 1) 0)
    exact ⟨x, fun t => by rw [hx t, Matrix.zero_mulVec, add_zero], by rw [hx0]; rfl⟩

/-- Miao, p. 23: with `n_u < n_y` but `P_uy` without full row rank, a stable solution need not
exist. Here `n_k = 1`, `n_y = 2`, `W = diag(2, ½, ½)`, the unstable root belongs to the
predetermined variable (`P_uy = 0`), and from `k₀ = 1` no solution is stable. -/
theorem theorem_1_4_3_lt_counterexample :
    IsRealBlockSplit
      (Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 1) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0)
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 2) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 0)
      ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      Fintype.card (Fin 1) < Fintype.card (Fin 2) ∧
      ∀ x : ℕ → Fin 1 ⊕ Fin 2 → ℝ,
        (∀ t, x (t + 1) = Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
          ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ x t) →
        x 0 ∘ Sum.inl = (fun _ => 1) → ¬ IsStableSeq x := by
  refine ⟨⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩, by simp, fun x hx hx0 hs => ?_⟩
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · have hk : ∀ t : ℕ, x t (Sum.inl 0) = 2 ^ t := fun t => by
      induction t with
      | zero => simpa using congrFun hx0 0
      | succ t ih =>
        rw [hx t, Matrix.fromBlocks_mulVec]
        simp [Matrix.mulVec, dotProduct, ih, pow_succ, mul_comm]
    obtain ⟨M, -, hM⟩ := hs
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
    have h1 := (norm_le_pi_norm (x t) (Sum.inl 0)).trans_lt (hM t)
    rw [hk, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith

end Miao.DifferenceEquations
