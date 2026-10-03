/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Basics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Markov decision processes, policies and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.1 and §5.1.3.1
(pp. 128–136).

An MDP is `M = (Γ, β, r, P)`: a nonempty feasible correspondence `Γ`, a
discount factor `β ∈ (0, 1)`, a reward `r` and a stochastic kernel `P` from the
feasible state–action pairs `G` to `X`. Here `r` and `P` are given on all of
`X × A`, with `P(x, a, ·)` a distribution for every `a`; off `G` their values
never enter, since maximisation is over `Γ(x)` and policies are feasible.

A feasible policy `σ` induces the Markov matrix `P_σ(x, x') = P(x, σ(x), x')`
and reward `r_σ(x) = r(x, σ(x))`; its lifetime value is
`v_σ = ∑ βᵗP_σᵗ r_σ = (I − βP_σ)⁻¹ r_σ`, (5.18), the unique fixed point of the
policy operator `T_σ v = r_σ + βP_σ v`, (5.19)–(5.20), which is an
order-preserving contraction of modulus `β` (Exercise 5.1.7). Exercise 5.1.6
bounds `v_σ`, Exercises 5.1.8–5.1.9 identify the iterates `T_σᵏ v` with
truncated discounted sums.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

/-- A Markov decision process `M = (Γ, β, r, P)` on the finite state space `X` and action space
`A` (p. 129). -/
structure MDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → ℝ
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_rowsum : ∀ x a, ∑ x', P x a x' = 1

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The feasible state–action pairs `G = {(x, a) : a ∈ Γ(x)}` (p. 129). -/
def Feasible (x : X) (a : A) : Prop := a ∈ M.Γ x

/-- A feasible policy (5.16): `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

/-- The set `Σ` of feasible policies (5.16), as a subtype. -/
abbrev Policy := {σ : X → A // M.IsFeasible σ}

/-- A feasible policy exists: choose any feasible action in each state. -/
noncomputable def defaultPolicy : M.Policy :=
  ⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty M.Policy := ⟨M.defaultPolicy⟩

/-- The row `P(x, a, ·)` is a distribution. -/
theorem isDistribution_P (x : X) (a : A) : IsDistribution (M.P x a) :=
  ⟨M.P_nonneg x a, M.P_rowsum x a⟩

/-- The closed-loop transition matrix `P_σ(x, x') = P(x, σ(x), x')` (p. 134). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

theorem Pσ_apply (σ : X → A) (x x' : X) : M.Pσ σ x x' = M.P x (σ x) x' := rfl

/-- `P_σ ∈ M(ℝ^X)` (p. 134). -/
theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The reward under `σ`: `r_σ(x) = r(x, σ(x))` (p. 134). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The action value `B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`, the expression maximised in
the Bellman equation (5.2). -/
def B (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (5.19): `(T_σ v)(x) = r(x, σ(x)) + β ∑ v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.B v x (σ x)

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    M.Tσ σ v x = M.r x (σ x) + M.β * ∑ x', v x' * M.P x (σ x) x' := rfl

/-- (5.20): `T_σ v = r_σ + βP_σ v`. -/
theorem Tσ_eq (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + M.β • (M.Pσ σ *ᵥ v) := by
  funext x
  simp only [Tσ, B, rσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_apply_eq, Pσ_apply]

/-- Exercise 5.1.7 (i), p. 135: `T_σ` is an order-preserving self-map on `ℝ^X`. -/
theorem Tσ_monotone (σ : X → A) : Monotone (M.Tσ σ) := by
  intro v v' hvv' x
  simp only [Tσ_apply]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x (σ x) x')

/-- `|(T_σ v)(x) − (T_σ v')(x)| ≤ β‖v − v'‖`. -/
theorem abs_Tσ_sub_le (σ : X → A) (v v' : X → ℝ) (x : X) :
    |M.Tσ σ v x - M.Tσ σ v' x| ≤ M.β * ‖v - v'‖ := by
  simp only [Tσ_apply]
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ M.β_pos.le
  have := (M.isMarkov_Pσ σ).abs_mulVec_sub_le v v' x
  simp only [mulVec_apply_eq, Pσ_apply] at this
  exact this

/-- Exercise 5.1.7 (ii), p. 135: `T_σ` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_Tσ (σ : X → A) : IsContractionOn (M.Tσ σ) Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Tσ_sub_le σ v v' x

/-- The `σ`-value function `v_σ` (5.17)–(5.18), p. 134: the unique fixed point of `T_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ :=
  Classical.choose ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is a fixed point of `T_σ`. -/
theorem isFixedPt_vσ (σ : X → A) : IsFixedPt (M.Tσ σ) (M.vσ σ) :=
  (Classical.choose_spec
    ((M.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)).2

/-- Exercise 5.1.7 (iii), p. 135: `v_σ` is the only fixed point of `T_σ` in `ℝ^X`. -/
theorem eq_vσ_of_isFixedPt (σ : X → A) {v : X → ℝ} (hv : IsFixedPt (M.Tσ σ) v) : v = M.vσ σ :=
  (M.isContractionOn_Tσ σ).fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv (M.isFixedPt_vσ σ)

/-- Exercise 5.1.7 (iv), p. 135: `T_σᵏ v → v_σ` for every `v ∈ ℝ^X`. -/
theorem tendsto_iterate_Tσ (σ : X → A) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (M.Tσ σ)^[k] v) atTop (𝓝 (M.vσ σ)) :=
  (M.isContractionOn_Tσ σ).tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _)
    (M.isFixedPt_vσ σ)

/-- `v_σ = r_σ + βP_σ v_σ`. -/
theorem vσ_eq (σ : X → A) : M.vσ σ = M.rσ σ + M.β • (M.Pσ σ *ᵥ M.vσ σ) := by
  rw [← Tσ_eq]
  exact (M.isFixedPt_vσ σ).eq.symm

/-- `‖βP_σ u‖ ≤ β‖u‖`. -/
theorem norm_smul_Pσ_mulVec_le (σ : X → A) (u : X → ℝ) :
    ‖M.β • (M.Pσ σ *ᵥ u)‖ ≤ M.β * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg M.β_pos.le]
  exact mul_le_mul_of_nonneg_left ((M.isMarkov_Pσ σ).norm_mulVec_le u) M.β_pos.le

/-- `I − βP_σ` is invertible: `u = βP_σ u` forces `‖u‖ ≤ β‖u‖`. -/
theorem isUnit_one_sub_smul_Pσ [DecidableEq X] (σ : X → A) : IsUnit (1 - M.β • M.Pσ σ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - M.β • M.Pσ σ) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero, smul_mulVec] at hd
  have hnorm : ‖u - v‖ ≤ M.β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖M.β • (M.Pσ σ *ᵥ (u - v))‖ := by rw [← hd]
      _ ≤ M.β * ‖u - v‖ := M.norm_smul_Pσ_mulVec_le σ _
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v), M.β_lt_one]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- (5.18), p. 135: `v_σ = (I − βP_σ)⁻¹ r_σ`, by Lemma 3.2.1. -/
theorem vσ_eq_inv [DecidableEq X] (σ : X → A) : M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by
  have hunit := M.isUnit_one_sub_smul_Pσ σ
  have h1 : (1 - M.β • M.Pσ σ) *ᵥ M.vσ σ = M.rσ σ := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add]
    exact M.vσ_eq σ
  calc M.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ ((1 - M.β • M.Pσ σ) *ᵥ M.vσ σ) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by rw [h1]

/-- `‖βᵗP_σᵗ u‖ ≤ βᵗ‖u‖`. -/
theorem norm_pow_smul_mulVec_le [DecidableEq X] (σ : X → A) (u : X → ℝ) (t : ℕ) :
    ‖M.β ^ t • (M.Pσ σ ^ t *ᵥ u)‖ ≤ M.β ^ t * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg M.β_pos.le t)]
  exact mul_le_mul_of_nonneg_left (((M.isMarkov_Pσ σ).pow t).norm_mulVec_le u)
    (pow_nonneg M.β_pos.le t)

/-- (5.18): the series `∑ₜ βᵗP_σᵗ r_σ` converges. -/
theorem summable_pow_smul_mulVec [DecidableEq X] (σ : X → A) :
    Summable fun t : ℕ => M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_pos.le M.β_lt_one).mul_right
    ‖M.rσ σ‖) (M.norm_pow_smul_mulVec_le σ _)

/-- Exercise 5.1.9 (p. 136) in matrix form: `T_σᵏ v = ∑_{t<k} βᵗP_σᵗ r_σ + βᵏP_σᵏ v`, the payoff
from following `σ` for `k` periods with terminal payoff `v`, the expectations being the entries
of `P_σᵗ`. -/
theorem iterate_Tσ_eq [DecidableEq X] (σ : X → A) (v : X → ℝ) (k : ℕ) :
    (M.Tσ σ)^[k] v =
      (∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) +
        M.β ^ k • (M.Pσ σ ^ k *ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, Tσ_eq, sum_range_succ', pow_zero, one_smul, pow_zero, one_mulVec]
    have h1 : ∀ (w : X → ℝ) (t : ℕ),
        M.β • (M.Pσ σ *ᵥ (M.β ^ t • (M.Pσ σ ^ t *ᵥ w))) =
          M.β ^ (t + 1) • (M.Pσ σ ^ (t + 1) *ᵥ w) := by
      intro w t
      rw [mulVec_smul, mulVec_mulVec, smul_smul, ← pow_succ', ← pow_succ']
    rw [mulVec_add, smul_add, mulVec_sum, smul_sum]
    simp only [h1]
    abel

/-- Exercise 5.1.8 (p. 135): starting from `v ≡ 0`, `T_σᵏ 0 = ∑_{t<k} βᵗP_σᵗ r_σ`. -/
theorem iterate_Tσ_zero [DecidableEq X] (σ : X → A) (k : ℕ) :
    (M.Tσ σ)^[k] 0 = ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  rw [iterate_Tσ_eq]
  simp

/-- (5.18) as a series: `v_σ = ∑ₜ βᵗP_σᵗ r_σ`. -/
theorem vσ_eq_tsum [DecidableEq X] (σ : X → A) :
    M.vσ σ = ∑' t : ℕ, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ) := by
  have hs := M.summable_pow_smul_mulVec σ
  have hlim := hs.hasSum.tendsto_sum_nat
  have hiter : (fun k : ℕ => ∑ t ∈ range k, M.β ^ t • (M.Pσ σ ^ t *ᵥ M.rσ σ)) =
      fun k => (M.Tσ σ)^[k] 0 := funext fun k => (M.iterate_Tσ_zero σ k).symm
  rw [hiter] at hlim
  exact tendsto_nhds_unique (M.tendsto_iterate_Tσ σ 0) hlim

/-- Exercise 5.1.6 (p. 135): if `|r| ≤ R` on the feasible pairs used by `σ`, then
`−R/(1 − β) ≤ v_σ ≤ R/(1 − β)`. -/
theorem abs_vσ_le (σ : X → A) {R : ℝ} (hR : ∀ x, |M.r x (σ x)| ≤ R) (x : X) :
    |M.vσ σ x| ≤ R / (1 - M.β) := by
  have hβ : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR x)
  set C : ℝ := R / (1 - M.β) with hC
  have hCeq : R + M.β * C = C := by
    rw [hC]
    field_simp
    ring
  set S : Set (X → ℝ) := {v | ∀ y, |v y| ≤ C} with hS
  have hclosed : IsClosed S := by
    have : S = ⋂ y, {v : X → ℝ | |v y| ≤ C} := by ext; simp [hS]
    rw [this]
    exact isClosed_iInter fun y => isClosed_le (continuous_abs.comp (continuous_apply y))
      continuous_const
  have hmaps : ∀ v ∈ S, M.Tσ σ v ∈ S := by
    intro v hv y
    rw [Tσ_apply]
    calc |M.r y (σ y) + M.β * ∑ x', v x' * M.P y (σ y) x'|
        ≤ |M.r y (σ y)| + M.β * |∑ x', v x' * M.P y (σ y) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_pos.le]
      _ ≤ R + M.β * C := by
          refine add_le_add (hR y) (mul_le_mul_of_nonneg_left ?_ M.β_pos.le)
          calc |∑ x', v x' * M.P y (σ y) x'| ≤ ∑ x', |v x'| * M.P y (σ y) x' := by
                refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
                rw [abs_mul, abs_of_nonneg (M.P_nonneg y (σ y) x')]
            _ ≤ ∑ x', C * M.P y (σ y) x' := sum_le_sum fun x' _ =>
                mul_le_mul_of_nonneg_right (hv x') (M.P_nonneg y (σ y) x')
            _ = C := by rw [← mul_sum, M.P_rowsum, mul_one]
      _ = C := hCeq
  have hiter : ∀ k : ℕ, (M.Tσ σ)^[k] 0 ∈ S := by
    intro k
    induction k with
    | zero => intro y; simp only [iterate_zero, id, Pi.zero_apply, abs_zero]; positivity
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact hclosed.mem_of_tendsto (M.tendsto_iterate_Tσ σ 0) (Eventually.of_forall hiter) x

end MDP

end SargentStachurski.MarkovDecisionProcesses
