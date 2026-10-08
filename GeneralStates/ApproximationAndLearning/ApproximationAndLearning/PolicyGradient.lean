/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.FiniteMDP

/-!
# From local to global optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.3.3 (pp. 320–321).

Policy gradient methods maximize `M(θ) = v_{σ(·, θ)}(x₀)` at a single initial state.

* **Theorem 9.2.2**: for a finite MDP with `β ∈ (0, 1)` and a policy `σ` whose transition matrix
  `P_σ` is irreducible, `v_σ(x) = v*(x)` at some state iff `σ` is optimal. The proof iterates
  `h ≥ βP_σh` for `h = v* − v_σ ≥ 0`, (9.27).
* Irreducibility is needed: in a two-state MDP with absorbing states, a policy can be optimal at
  one state and not at the other (`theorem_9_2_2_needs_irreducible`).
-/

open Set Function Filter Topology Matrix

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] [DecidableEq X] (M : FiniteMDP X A)

theorem Pσ_pow_nonneg (σ : M.Policy) (m : ℕ) (x y : X) : 0 ≤ (M.Pσ σ.1 ^ m) x y := by
  induction m generalizing x y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (M.P_nonneg _ _ (σ.2 z) y)

theorem Pσ_pow_mulVec_mono (σ : M.Policy) (m : ℕ) {u w : X → ℝ} (h : u ≤ w) :
    (M.Pσ σ.1 ^ m) *ᵥ u ≤ (M.Pσ σ.1 ^ m) *ᵥ w := fun x =>
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (M.Pσ_pow_nonneg σ m x y)

/-- **Theorem 9.2.2** (p. 320): for a finite MDP with `β > 0` and a policy `σ` such that `P_σ` is
irreducible, (i) `v_σ(x) = v*(x)` for some `x` iff (ii) `σ` is optimal. -/
theorem theorem_9_2_2 [Nonempty X] (hβ : 0 < M.β) (σ : M.Policy)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (M.Pσ σ.1 ^ m) x y) :
    (∃ x, M.toDP.vσ σ x = M.toDP.vstar x) ↔ M.toDP.IsOptimal σ := by
  constructor
  · rintro ⟨x₀, hx₀⟩
    rw [M.toDP.isOptimal_iff]
    set h := M.toDP.vstar - M.toDP.vσ σ
    have hnn : ∀ y, 0 ≤ h y := fun y => sub_nonneg.2 (M.toDP.vσ_le_vstar σ y)
    -- `h ≥ βP_σh`
    have hstep : (M.β • M.Pσ σ.1) *ᵥ h ≤ h := by
      have h1 : M.Tσ σ.1 M.toDP.vstar ≤ M.toDP.vstar := by
        have := M.toDP.T_le_bellman σ (mem_univ M.toDP.vstar)
        rwa [M.toDP.bellman_vstar] at this
      have h2 : M.Tσ σ.1 (M.toDP.vσ σ) = M.toDP.vσ σ := M.toDP.T_vσ σ
      intro y
      have e : ((M.β • M.Pσ σ.1) *ᵥ h) y =
          M.Tσ σ.1 M.toDP.vstar y - M.Tσ σ.1 (M.toDP.vσ σ) y := by
        rw [M.Tσ_eq_mulVec, M.Tσ_eq_mulVec]
        simp only [h, Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
        ring
      rw [e, h2]
      simp only [h, Pi.sub_apply]
      linarith [h1 y]
    -- iterating, `h ≥ βᵐP_σᵐh` (9.27)
    have hiter : ∀ m : ℕ, M.β ^ m • ((M.Pσ σ.1 ^ m) *ᵥ h) ≤ h := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have e : M.β ^ (m + 1) • ((M.Pσ σ.1 ^ (m + 1)) *ᵥ h) =
            M.β ^ m • ((M.Pσ σ.1 ^ m) *ᵥ ((M.β • M.Pσ σ.1) *ᵥ h)) := by
          rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ,
            smul_smul, ← pow_succ]
        rw [e]
        intro y
        have hm := M.Pσ_pow_mulVec_mono σ m hstep y
        have hb : 0 ≤ M.β ^ m := pow_nonneg hβ.le m
        simp only [Pi.smul_apply, smul_eq_mul] at hm ih ⊢
        exact (mul_le_mul_of_nonneg_left hm hb).trans (ih y)
    have hh0 : h x₀ = 0 := by simp only [h, Pi.sub_apply, hx₀, sub_self]
    refine (sub_eq_zero.1 (funext fun y => ?_)).symm
    change h y = 0
    refine le_antisymm ?_ (hnn y)
    by_contra hpos
    obtain ⟨m, hm⟩ := hirr x₀ y
    have h1 := hiter m x₀
    simp only [Pi.smul_apply, smul_eq_mul, hh0] at h1
    have h2 : (M.Pσ σ.1 ^ m) x₀ y * h y ≤ ((M.Pσ σ.1 ^ m) *ᵥ h) x₀ :=
      Finset.single_le_sum (f := fun z => (M.Pσ σ.1 ^ m) x₀ z * h z)
        (fun z _ => mul_nonneg (M.Pσ_pow_nonneg σ m x₀ z) (hnn z)) (Finset.mem_univ y)
    have h3 : 0 < (M.Pσ σ.1 ^ m) x₀ y * h y := mul_pos hm (lt_of_not_ge hpos)
    have h4 : 0 < M.β ^ m := pow_pos hβ m
    nlinarith
  · intro hopt
    rw [M.toDP.isOptimal_iff] at hopt
    exact ⟨Classical.arbitrary X, by rw [hopt]⟩

end FiniteMDP

/-- Two absorbing states `false, true`, two actions, reward `1` for action `true` at state `true`,
`β = 1/2`. -/
noncomputable def absorbingMDP : FiniteMDP Bool Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  r x a := if x && a then 1 else 0
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  P x _ x' := if x' = x then 1 else 0
  P_nonneg _ _ _ _ := by split_ifs <;> norm_num
  P_sum x _ _ := by simp

/-- Theorem 9.2.2 needs irreducibility: in `absorbingMDP` the policy `σ ≡ false` attains
`v*(false) = 0` at the state `false` but is not optimal (`v_σ(true) = 0 < 2 = v*(true)`). -/
theorem theorem_9_2_2_needs_irreducible :
    ∃ σ : absorbingMDP.Policy, absorbingMDP.toDP.vσ σ false = absorbingMDP.toDP.vstar false ∧
      ¬ absorbingMDP.toDP.IsOptimal σ := by
  let σ : absorbingMDP.Policy := ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
  -- `v_σ = 0`
  have hvσ : absorbingMDP.toDP.vσ σ = 0 := by
    refine (absorbingMDP.toDP.eq_vσ (mem_univ _) ?_).symm
    funext x
    simp [FiniteMDP.toDP, FiniteMDP.Tσ, FiniteMDP.Q, absorbingMDP, σ]
  -- `v* = 2·𝟙{true}`
  have hvs : absorbingMDP.toDP.vstar = fun x => if x then 2 else 0 := by
    refine (absorbingMDP.toDP.eq_vstar (mem_univ _) ?_).symm
    funext x
    rw [absorbingMDP.bellman_eq]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun a _ => ?_
      cases x <;> cases a <;> norm_num [FiniteMDP.Q, absorbingMDP]
    · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ true))
      cases x <;> norm_num [FiniteMDP.Q, absorbingMDP]
  refine ⟨σ, by rw [hvσ, hvs]; rfl, fun hopt => ?_⟩
  rw [absorbingMDP.toDP.isOptimal_iff, hvσ, hvs] at hopt
  have := congrFun hopt true
  norm_num at this

end SargentStachurski.ApproximationAndLearning
