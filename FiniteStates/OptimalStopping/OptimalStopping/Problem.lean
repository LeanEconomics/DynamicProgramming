/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Basics
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Optimal stopping problems, policies and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.1.1–§4.1.1.3
(pp. 105–108).

An optimal stopping problem is `S = (β, P, c, e)`: a discount factor
`β ∈ (0, 1)`, a Markov matrix `P`, a continuation reward `c` and an exit reward
`e`. A policy `σ : X → {0, 1}` says where to stop. The `σ`-value function `v_σ`
solves `v_σ = r_σ + L_σ v_σ`, (4.2)–(4.3), where `r_σ = σe + (1 − σ)c` and
`L_σ = β(1 − σ)P`; it is the unique fixed point of the policy operator `T_σ`
of (4.5), which is order preserving (Exercise 4.1.2) and a contraction of
modulus `β` in the supremum norm (Proposition 4.1.1, Exercise 4.1.3). Hence
`v_σ = (I − L_σ)⁻¹ r_σ = ∑ₜ L_σᵗ r_σ`, (4.4); Exercise 4.1.1, that
`ρ(L_σ) < 1`, is in `SpectralRadius`.

Examples 4.1.1 (IID job search) and 4.1.2 (a perpetual American call) are
constructed as stopping problems.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

/-- An optimal stopping problem `S = (β, P, c, e)` on the finite state space `X` (p. 106). -/
structure StoppingProblem (X : Type*) [Fintype X] where
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  P : Matrix X X ℝ
  P_markov : IsMarkov P
  c : X → ℝ
  e : X → ℝ

/-- A policy (p. 106): `true` means stop, `false` means continue. -/
abbrev Policy (X : Type*) := X → Bool

namespace StoppingProblem

variable {X : Type*} [Fintype X] (S : StoppingProblem X)

/-- The continuation payoff `c(x) + β ∑ v(x')P(x, x')` given a value function `v`. -/
def cont (v : X → ℝ) : X → ℝ := fun x => S.c x + S.β * (S.P *ᵥ v) x

theorem cont_apply (v : X → ℝ) (x : X) : S.cont v x = S.c x + S.β * ∑ x', v x' * S.P x x' := by
  rw [cont, mulVec_apply_eq]

/-- `r_σ = σe + (1 − σ)c` (p. 107). -/
def r (σ : Policy X) : X → ℝ := fun x => if σ x then S.e x else S.c x

/-- `L_σ(x, x') = β(1 − σ(x))P(x, x')` (p. 107). -/
def L (σ : Policy X) : Matrix X X ℝ := Matrix.of fun x x' => if σ x then 0 else S.β * S.P x x'

theorem L_apply (σ : Policy X) (x x' : X) :
    S.L σ x x' = if σ x then 0 else S.β * S.P x x' := rfl

/-- The policy operator (4.5): `(T_σ v)(x) = σ(x)e(x) + (1 − σ(x))[c(x) + β ∑ v(x')P(x, x')]`. -/
def Tσ (σ : Policy X) (v : X → ℝ) : X → ℝ := fun x => if σ x then S.e x else S.cont v x

/-- `T_σ v = r_σ + L_σ v` (p. 108). -/
theorem Tσ_eq (σ : Policy X) (v : X → ℝ) : S.Tσ σ v = S.r σ + S.L σ *ᵥ v := by
  funext x
  simp only [Tσ, r, L, cont, Pi.add_apply, mulVec, dotProduct, Matrix.of_apply]
  by_cases h : σ x
  · simp [h]
  · simp only [h, Bool.false_eq_true, ite_false, mul_sum]
    congr 1
    exact sum_congr rfl fun x' _ => by ring

/-- Exercise 4.1.2 (p. 108): `T_σ` is order preserving. -/
theorem Tσ_monotone (σ : Policy X) : Monotone (S.Tσ σ) := by
  intro v v' hvv' x
  unfold Tσ cont
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (S.P_markov.mulVec_le_mulVec hvv' x)
      S.β_pos.le)

/-- `|(T_σ v)(x) − (T_σ v')(x)| ≤ β‖v − v'‖`. -/
theorem abs_Tσ_sub_le (σ : Policy X) (v v' : X → ℝ) (x : X) :
    |S.Tσ σ v x - S.Tσ σ v' x| ≤ S.β * ‖v - v'‖ := by
  unfold Tσ cont
  split_ifs
  · simp only [sub_self, abs_zero]
    exact mul_nonneg S.β_pos.le (norm_nonneg _)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
    exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_sub_le v v' x) S.β_pos.le

/-- **Proposition 4.1.1** (p. 108, Exercise 4.1.3): `T_σ` is a contraction of modulus `β` on `ℝ^X`
under the supremum norm. -/
theorem isContractionOn_Tσ (σ : Policy X) : IsContractionOn (S.Tσ σ) Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_Tσ_sub_le σ v v' x

/-- The `σ`-value function `v_σ` (p. 107): the unique fixed point of `T_σ`. -/
noncomputable def vσ (σ : Policy X) : X → ℝ :=
  Classical.choose ((S.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)

theorem isFixedPt_vσ (σ : Policy X) : IsFixedPt (S.Tσ σ) (S.vσ σ) :=
  (Classical.choose_spec
    ((S.isContractionOn_Tσ σ).exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩)).2

/-- `v_σ` is the only fixed point of `T_σ` in `ℝ^X` (p. 108). -/
theorem eq_vσ_of_isFixedPt (σ : Policy X) {v : X → ℝ} (hv : IsFixedPt (S.Tσ σ) v) : v = S.vσ σ :=
  (S.isContractionOn_Tσ σ).fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv (S.isFixedPt_vσ σ)

/-- Iterates of `T_σ` converge to `v_σ` from any `v` (p. 108). -/
theorem tendsto_iterate_Tσ (σ : Policy X) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (S.Tσ σ)^[k] v) atTop (𝓝 (S.vσ σ)) :=
  (S.isContractionOn_Tσ σ).tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _)
    (S.isFixedPt_vσ σ)

/-- (4.2), p. 107: `v_σ(x) = σ(x)e(x) + (1 − σ(x))[c(x) + β ∑ v_σ(x')P(x, x')]`. -/
theorem vσ_eq (σ : Policy X) (x : X) :
    S.vσ σ x = if σ x then S.e x else S.c x + S.β * ∑ x', S.vσ σ x' * S.P x x' := by
  have := congrFun (S.isFixedPt_vσ σ).eq x
  rw [← this, Tσ, cont_apply]

/-- Stopping states: `v_σ(x) = e(x)`. -/
theorem vσ_of_stop (σ : Policy X) {x : X} (hx : σ x = true) : S.vσ σ x = S.e x := by
  rw [vσ_eq, hx]
  simp

/-- (4.3), p. 107: at continuation states, `v_σ(x) = c(x) + β ∑ v_σ(x')P(x, x')`. -/
theorem vσ_of_continue (σ : Policy X) {x : X} (hx : σ x = false) :
    S.vσ σ x = S.c x + S.β * ∑ x', S.vσ σ x' * S.P x x' := by
  rw [vσ_eq, hx]
  simp

/-- `v_σ = r_σ + L_σ v_σ`, the matrix form of (4.2). -/
theorem vσ_eq_r_add (σ : Policy X) : S.vσ σ = S.r σ + S.L σ *ᵥ S.vσ σ := by
  rw [← Tσ_eq]
  exact (S.isFixedPt_vσ σ).eq.symm

/-! ### The matrix `L_σ` and the formula (4.4) -/

theorem L_nonneg (σ : Policy X) (x x' : X) : 0 ≤ S.L σ x x' := by
  rw [L_apply]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg S.β_pos.le (S.P_markov.nonneg x x')

/-- Each row of `L_σ` sums to `β(1 − σ(x)) ≤ β`. -/
theorem L_rowsum_le (σ : Policy X) (x : X) : ∑ x', S.L σ x x' ≤ S.β := by
  simp only [L_apply]
  split_ifs
  · simp only [sum_const_zero]
    exact S.β_pos.le
  · rw [← mul_sum, S.P_markov.rowsum, mul_one]

/-- `|(L_σ u)(x)| ≤ β‖u‖`. -/
theorem abs_L_mulVec_le (σ : Policy X) (u : X → ℝ) (x : X) : |(S.L σ *ᵥ u) x| ≤ S.β * ‖u‖ := by
  have h : (S.L σ *ᵥ u) x = if σ x then 0 else S.β * (S.P *ᵥ u) x := by
    simp only [mulVec, dotProduct, L_apply]
    split_ifs
    · simp
    · rw [mul_sum]
      exact sum_congr rfl fun x' _ => by ring
  rw [h]
  split_ifs
  · simp only [abs_zero]
    exact mul_nonneg S.β_pos.le (norm_nonneg _)
  · rw [abs_mul, abs_of_nonneg S.β_pos.le]
    exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_le u x) S.β_pos.le

/-- `‖L_σ u‖ ≤ β‖u‖`. -/
theorem norm_L_mulVec_le (σ : Policy X) (u : X → ℝ) : ‖S.L σ *ᵥ u‖ ≤ S.β * ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
  intro x
  rw [Real.norm_eq_abs]
  exact S.abs_L_mulVec_le σ u x

/-- `‖L_σᵗ u‖ ≤ βᵗ‖u‖`. -/
theorem norm_L_pow_mulVec_le [DecidableEq X] (σ : Policy X) (u : X → ℝ) (t : ℕ) :
    ‖S.L σ ^ t *ᵥ u‖ ≤ S.β ^ t * ‖u‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    calc ‖S.L σ *ᵥ (S.L σ ^ t *ᵥ u)‖ ≤ S.β * ‖S.L σ ^ t *ᵥ u‖ := S.norm_L_mulVec_le σ _
      _ ≤ S.β * (S.β ^ t * ‖u‖) := mul_le_mul_of_nonneg_left ih S.β_pos.le
      _ = S.β ^ (t + 1) * ‖u‖ := by ring

/-- `I − L_σ` is invertible: `u = L_σ u` forces `‖u‖ ≤ β‖u‖`, so `u = 0`. This is the conclusion
the book draws from Exercise 4.1.1 and the Neumann series lemma (p. 107). -/
theorem isUnit_one_sub_L [DecidableEq X] (σ : Policy X) : IsUnit (1 - S.L σ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - S.L σ) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hd
  have hnorm : ‖u - v‖ ≤ S.β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖S.L σ *ᵥ (u - v)‖ := by rw [← hd]
      _ ≤ S.β * ‖u - v‖ := S.norm_L_mulVec_le σ _
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v), S.β_lt_one]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- (4.4), p. 107: `v_σ = (I − L_σ)⁻¹ r_σ`. -/
theorem vσ_eq_inv [DecidableEq X] (σ : Policy X) : S.vσ σ = (1 - S.L σ)⁻¹ *ᵥ S.r σ := by
  have hunit := S.isUnit_one_sub_L σ
  have h1 : (1 - S.L σ) *ᵥ S.vσ σ = S.r σ := by
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add]
    exact S.vσ_eq_r_add σ
  calc S.vσ σ = (1 - S.L σ)⁻¹ *ᵥ ((1 - S.L σ) *ᵥ S.vσ σ) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - S.L σ)⁻¹ *ᵥ S.r σ := by rw [h1]

/-- The Neumann series for `v_σ`: `∑ₜ L_σᵗ r_σ` converges. -/
theorem summable_L_pow_mulVec [DecidableEq X] (σ : Policy X) :
    Summable fun t : ℕ => S.L σ ^ t *ᵥ S.r σ :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one S.β_pos.le S.β_lt_one).mul_right
    ‖S.r σ‖) (S.norm_L_pow_mulVec_le σ _)

/-- (4.4) as a series: `v_σ = ∑ₜ L_σᵗ r_σ`, the Neumann series of the book's argument (p. 107). -/
theorem vσ_eq_tsum [DecidableEq X] (σ : Policy X) : S.vσ σ = ∑' t : ℕ, S.L σ ^ t *ᵥ S.r σ := by
  have hs := S.summable_L_pow_mulVec σ
  have hs' : Summable fun t : ℕ => S.L σ ^ (t + 1) *ᵥ S.r σ := (summable_nat_add_iff 1).2 hs
  -- the series is a fixed point of `T_σ`
  have hfix : IsFixedPt (S.Tσ σ) (∑' t : ℕ, S.L σ ^ t *ᵥ S.r σ) := by
    rw [IsFixedPt, Tσ_eq]
    let M := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (S.L σ))
    have hM : ∀ u, M u = S.L σ *ᵥ u := fun u => rfl
    rw [← hM, M.map_tsum hs]
    simp only [hM, mulVec_mulVec, ← pow_succ']
    rw [hs.tsum_eq_zero_add]
    simp
  exact (S.eq_vσ_of_isFixedPt σ hfix).symm

/-! ### Examples 4.1.1 and 4.1.2 -/

/-- Example 4.1.1 (p. 106): IID job search as a stopping problem. Every row of `P` is the offer
distribution `φ`, the exit reward is `w/(1 − β)` and the continuation reward is unemployment
compensation `c`. -/
noncomputable def iidJobSearch {W : Type*} [Fintype W] (wage : W → ℝ) {φ : W → ℝ}
    (hφ : IsDistribution φ) (c : ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : StoppingProblem W where
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  P := Matrix.of fun _ w' => φ w'
  P_markov := ⟨fun _ w' => hφ.nonneg w', fun _ => hφ.sum_eq_one⟩
  c := fun _ => c
  e := fun w => wage w / (1 - β)

/-- Example 4.1.2 (p. 106): a perpetual American call option on an asset with price `s(Xₜ)`,
strike `K` and interest rate `r > 0`: discount factor `1/(1 + r)`, exit reward `s(x) − K`,
continuation reward zero. -/
noncomputable def perpetualOption {Q : Matrix X X ℝ} (hQ : IsMarkov Q) (s : X → ℝ) (K : ℝ)
    {r : ℝ} (hr : 0 < r) : StoppingProblem X where
  β := 1 / (1 + r)
  β_pos := by positivity
  β_lt_one := by
    rw [div_lt_one (by linarith)]
    linarith
  P := Q
  P_markov := hQ
  c := fun _ => 0
  e := fun x => s x - K

end StoppingProblem

end SargentStachurski.OptimalStopping
