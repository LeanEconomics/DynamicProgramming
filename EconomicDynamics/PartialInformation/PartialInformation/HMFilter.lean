/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Filtering a hidden finite-state Markov chain

Miao, §10.1.2–§10.1.3, pp. 337–340. The probability model behind the filters of the two
sections: a hidden chain `x₀, x₁, …` on a finite set `X` with initial law `μ₀` and transition
matrix `P` (`P i j = Pr(x_{t+1} = j | x_t = i)`), and signals `y_t` drawn independently given
the states with emission weight `f(x, y) = Pr(y_t = y | x_t = x)`. In §10.1.2 `f` is the
`N × M` matrix `Q` and the signals are finite; in §10.1.3 `f(x, ·)` is the density of
`h(x, ε)`, and the same algebra applies with densities in place of probabilities.

The joint weight of a state path `x⁰…xᵗ` and a signal path `y⁰…yᵗ` is
`μ₀(x₀) f(x₀, y₀) ∏ₛ P(xₛ, xₛ₊₁) f(xₛ₊₁, yₛ₊₁)` (`hm_weight`). Everything else is computed from it
by summing out states:

* `hm_joint t ys i = Pr(x_t = i, yᵗ)`, `hm_lik t ys = Pr(yᵗ)` (the likelihood),
  `hm_post t ys i = π_t(i | yᵗ)`;
* `hm_predJoint t ys i = Pr(x_{t+1} = i, yᵗ)` (the last emission factor left out),
  `hm_pred t ys i = π_{t+1}(i | yᵗ)`.

Proved: the prediction step `Pr(x_{t+1} = i, yᵗ) = Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)` and its normalised
form `π_{t+1}(i | yᵗ) = Σⱼ pⱼᵢ π_t(j | yᵗ)` (`hm_predJoint_eq`, `hm_pred_eq`); the updating step
`π_{t+1}(i | yᵗ⁺¹) = f(i, y) π_{t+1}(i | yᵗ) / Σⱼ f(j, y) π_{t+1}(j | yᵗ)` (`hm_post_update`);
the likelihood factorisation `Pr(yᵗ⁺¹) = Pr(yᵗ) Σⱼ f(j, y) π_{t+1}(j | yᵗ)` (`hm_lik_snoc`);
and, when `μ₀`, `P` and `f` are stochastic, that `hm_lik t` is a probability mass function on
signal paths, the states alone form the Markov chain `(μ₀, P)`, and the filter is a
probability vector (`hm_lik_sum`, `hm_stateLaw`, `hm_markov`, `hm_post_sum`).
-/

namespace Miao.PartialInformation

/-- Splitting a sum over `(t + 2)`-tuples into the last entry and the first `t + 1` entries. -/
theorem hm_sum_snoc {α Z : Type*} [Fintype α] [AddCommMonoid Z] (t : ℕ)
    (F : (Fin (t + 2) → α) → Z) :
    ∑ xs, F xs = ∑ j, ∑ xs : Fin (t + 1) → α, F (Fin.snoc xs j) := by
  rw [← (Fintype.sum_equiv (Fin.snocEquiv (fun _ => α)) _ _ (fun _ => rfl)),
    Fintype.sum_prod_type]
  rfl

/-- Splitting a sum over `1`-tuples. -/
theorem hm_sum_fin_one {α Z : Type*} [Fintype α] [AddCommMonoid Z] (F : (Fin 1 → α) → Z) :
    ∑ xs, F xs = ∑ j, F (fun _ => j) :=
  (Fintype.sum_equiv (Equiv.funUnique (Fin 1) α).symm _ _ (fun _ => rfl)).symm

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Miao, pp. 338–339: the joint weight of the state path `xs = (x₀, …, x_t)` and the signal
path `ys = (y₀, …, y_t)`, `μ₀(x₀) f(x₀, y₀) ∏ₛ P(xₛ, xₛ₊₁) f(xₛ₊₁, yₛ₊₁)`. -/
def hm_weight (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) : ℝ :=
  μ0 (xs 0) * f (xs 0) (ys 0) *
    ∏ s : Fin t, (P (xs s.castSucc) (xs s.succ) * f (xs s.succ) (ys s.succ))

omit [Fintype X] [DecidableEq X] in
/-- Extending both paths by one date multiplies the weight by `P(x_t, j) f(j, y)`. -/
theorem hm_weight_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) (j : X) (y : Y) :
    hm_weight μ0 P f (t + 1) (Fin.snoc xs j) (Fin.snoc ys y) =
      hm_weight μ0 P f t xs ys * (P (xs (Fin.last t)) j * f j y) := by
  unfold hm_weight
  rw [Fin.prod_univ_castSucc]
  have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
  simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

/-- `Pr(x_t = i, yᵗ)`: the weight of all state paths ending in `i`. -/
def hm_joint (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  ∑ xs : Fin (t + 1) → X, if xs (Fin.last t) = i then hm_weight μ0 P f t xs ys else 0

/-- The likelihood `Pr(yᵗ) = Σᵢ Pr(x_t = i, yᵗ)`. -/
def hm_lik (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) : ℝ :=
  ∑ i, hm_joint μ0 P f t ys i

/-- The filter `π_t(i | yᵗ) = Pr(x_t = i, yᵗ) / Pr(yᵗ)`. -/
noncomputable def hm_post (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  hm_joint μ0 P f t ys i / hm_lik μ0 P f t ys

/-- `Pr(x_{t+1} = i, yᵗ)`: paths of length `t + 2` ending in `i`, weighted without the emission
factor of date `t + 1`. -/
def hm_predJoint (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  ∑ xs : Fin (t + 2) → X, if xs (Fin.last (t + 1)) = i then
    hm_weight μ0 P f t (Fin.init xs) ys * P (xs (Fin.last t).castSucc) i else 0

/-- The predicted distribution `π_{t+1}(i | yᵗ)`. -/
noncomputable def hm_pred (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  hm_predJoint μ0 P f t ys i / ∑ k, hm_predJoint μ0 P f t ys k

theorem hm_lik_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) : hm_lik μ0 P f t ys = ∑ xs, hm_weight μ0 P f t xs ys := by
  unfold hm_lik hm_joint
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Miao, p. 339 (prediction step): `Pr(x_{t+1} = i, yᵗ) = Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)`. -/
theorem hm_predJoint_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) :
    hm_predJoint μ0 P f t ys i = ∑ j, P j i * hm_joint μ0 P f t ys j := by
  unfold hm_predJoint hm_joint
  rw [hm_sum_snoc]
  simp only [Fin.snoc_last, Fin.init_snoc, Fin.snoc_castSucc, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_comm]

/-- Miao, p. 338 (Bayes' rule, numerator): `Pr(x_{t+1} = i, yᵗ⁺¹) = f(i, y) Pr(x_{t+1} = i, yᵗ)`. -/
theorem hm_joint_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (y : Y) (i : X) :
    hm_joint μ0 P f (t + 1) (Fin.snoc ys y) i = f i y * hm_predJoint μ0 P f t ys i := by
  unfold hm_joint hm_predJoint
  rw [hm_sum_snoc, hm_sum_snoc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  simp only [Fin.snoc_last, Fin.init_snoc, Fin.snoc_castSucc, hm_weight_snoc]
  split_ifs with h
  · rw [h]; ring
  · simp

/-- The forward recursion `Pr(x_{t+1} = i, yᵗ⁺¹) = f(i, y) Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)`. -/
theorem hm_joint_forward (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (y : Y) (i : X) :
    hm_joint μ0 P f (t + 1) (Fin.snoc ys y) i = f i y * ∑ j, P j i * hm_joint μ0 P f t ys j := by
  rw [hm_joint_snoc, hm_predJoint_eq]

/-- The date-0 joint `Pr(x₀ = i, y₀) = μ₀(i) f(i, y₀)`. -/
theorem hm_joint_zero (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (ys : Fin 1 → Y) (i : X) : hm_joint μ0 P f 0 ys i = μ0 i * f i (ys 0) := by
  unfold hm_joint hm_weight
  rw [hm_sum_fin_one]
  simp

/-- With stochastic rows of `P`, `Σᵢ Pr(x_{t+1} = i, yᵗ) = Pr(yᵗ)`. -/
theorem hm_predJoint_sum (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) :
    ∑ k, hm_predJoint μ0 P f t ys k = hm_lik μ0 P f t ys := by
  simp only [hm_predJoint_eq]
  rw [Finset.sum_comm]
  unfold hm_lik
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hP, one_mul]

/-- Miao, p. 339 (prediction step, normalised):
`π_{t+1}(eᵢ | yᵗ) = Σⱼ pⱼᵢ π_t(eⱼ | yᵗ)`. -/
theorem hm_pred_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (i : X) :
    hm_pred μ0 P f t ys i = ∑ j, P j i * hm_post μ0 P f t ys j := by
  unfold hm_pred hm_post
  rw [hm_predJoint_sum μ0 P f hP, hm_predJoint_eq, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => mul_div_assoc _ _ _)

/-- Miao, p. 340 (updating step):
`π_{t+1}(eᵢ | yᵗ⁺¹) = f(eᵢ, y) π_{t+1}(eᵢ | yᵗ) / Σⱼ f(eⱼ, y) π_{t+1}(eⱼ | yᵗ)`, whenever
`Pr(yᵗ) ≠ 0`. -/
theorem hm_post_update (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) (i : X) :
    hm_post μ0 P f (t + 1) (Fin.snoc ys y) i =
      f i y * hm_pred μ0 P f t ys i / ∑ j, f j y * hm_pred μ0 P f t ys j := by
  have e : hm_lik μ0 P f (t + 1) (Fin.snoc ys y) = ∑ j, f j y * hm_predJoint μ0 P f t ys j := by
    unfold hm_lik
    simp only [hm_joint_snoc]
  unfold hm_post hm_pred
  rw [hm_predJoint_sum μ0 P f hP, e, hm_joint_snoc]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hl]

/-- Miao, p. 340: the likelihood factorises as `Pr(yᵗ⁺¹) = Pr(yᵗ) Pr(y_{t+1} | yᵗ)` with
`Pr(y_{t+1} = y | yᵗ) = Σⱼ f(eⱼ, y) π_{t+1}(eⱼ | yᵗ)`. -/
theorem hm_lik_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) :
    hm_lik μ0 P f (t + 1) (Fin.snoc ys y) =
      hm_lik μ0 P f t ys * ∑ j, f j y * hm_pred μ0 P f t ys j := by
  have e : hm_lik μ0 P f (t + 1) (Fin.snoc ys y) = ∑ j, f j y * hm_predJoint μ0 P f t ys j := by
    unfold hm_lik
    simp only [hm_joint_snoc]
  unfold hm_pred
  rw [hm_predJoint_sum μ0 P f hP, e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  field_simp

omit [Fintype X] [DecidableEq X] in
/-- Nonnegative inputs give nonnegative weights. -/
theorem hm_weight_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) : 0 ≤ hm_weight μ0 P f t xs ys :=
  mul_nonneg (mul_nonneg (hμ _) (hf _ _))
    (Finset.prod_nonneg (fun _ _ => mul_nonneg (hP _ _) (hf _ _)))

theorem hm_joint_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : 0 ≤ hm_joint μ0 P f t ys i :=
  Finset.sum_nonneg (fun xs _ => by
    split_ifs
    · exact hm_weight_nonneg μ0 P f hμ hP hf t xs ys
    · exact le_rfl)

/-- The filter is a probability vector whenever `Pr(yᵗ) > 0`. -/
theorem hm_post_sum (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (hl : hm_lik μ0 P f t ys ≠ 0) :
    ∑ i, hm_post μ0 P f t ys i = 1 := by
  unfold hm_post
  rw [← Finset.sum_div]
  exact div_self hl

theorem hm_post_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : 0 ≤ hm_post μ0 P f t ys i :=
  div_nonneg (hm_joint_nonneg μ0 P f hμ hP hf t ys i)
    (Finset.sum_nonneg (fun j _ => hm_joint_nonneg μ0 P f hμ hP hf t ys j))

/-- With stochastic `μ₀`, `P` and `f` (finite signals), the likelihood `Pr(yᵗ)` sums to one over
signal paths: `hm_weight` is a genuine joint probability of state and signal paths. -/
theorem hm_lik_sum [Fintype Y] (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∑ i, μ0 i = 1) (hP : ∀ i, ∑ j, P i j = 1) (hf : ∀ i, ∑ y, f i y = 1) :
    ∀ t : ℕ, ∑ ys : Fin (t + 1) → Y, hm_lik μ0 P f t ys = 1
  | 0 => by
    simp only [hm_lik, hm_joint_zero]
    rw [hm_sum_fin_one, Finset.sum_comm]
    simp only [← Finset.mul_sum, hf, mul_one, hμ]
  | t + 1 => by
    rw [hm_sum_snoc, Finset.sum_comm, ← hm_lik_sum μ0 P f hμ hP hf t]
    refine Finset.sum_congr rfl (fun ys _ => ?_)
    rw [← hm_predJoint_sum μ0 P f hP]
    unfold hm_lik
    simp only [hm_joint_snoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hf, one_mul]

omit [Fintype X] [DecidableEq X] in
/-- The law of the state path alone: `Σ_{yᵗ} weight = μ₀(x₀) ∏ₛ P(xₛ, xₛ₊₁)`. -/
theorem hm_stateLaw [Fintype Y] (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hf : ∀ i, ∑ y, f i y = 1) :
    ∀ (t : ℕ) (xs : Fin (t + 1) → X), ∑ ys, hm_weight μ0 P f t xs ys =
      μ0 (xs 0) * ∏ s : Fin t, P (xs s.castSucc) (xs s.succ)
  | 0, xs => by
    rw [hm_sum_fin_one]
    simp [hm_weight, ← Finset.mul_sum, hf]
  | t + 1, xs => by
    rw [← Fin.snoc_init_self xs, hm_sum_snoc]
    simp only [hm_weight_snoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hm_stateLaw μ0 P f hf t, ← Finset.mul_sum, hf, mul_one]
    rw [Fin.prod_univ_castSucc]
    have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
    simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
    ring

/-- The probability that the states at dates `t` and `t + 1` are `i` and `j`. -/
def hm_pairLaw (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i j : X) : ℝ :=
  ∑ xs : Fin (t + 2) → X, if xs (Fin.last t).castSucc = i ∧ xs (Fin.last (t + 1)) = j then
    μ0 (xs 0) * ∏ s : Fin (t + 1), P (xs s.castSucc) (xs s.succ) else 0

/-- The probability that the state at date `t` is `i`. -/
def hm_margLaw (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i : X) : ℝ :=
  ∑ xs : Fin (t + 1) → X, if xs (Fin.last t) = i then
    μ0 (xs 0) * ∏ s : Fin t, P (xs s.castSucc) (xs s.succ) else 0

/-- Miao, p. 337: the hidden states form a Markov chain with transition matrix `P`,
`Pr(x_t = eᵢ, x_{t+1} = eⱼ) = Pr(x_t = eᵢ) pᵢⱼ`, so `pᵢⱼ = Pr(x_{t+1} = eⱼ | x_t = eᵢ)`. -/
theorem hm_markov (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i j : X) :
    hm_pairLaw μ0 P t i j = hm_margLaw μ0 P t i * P i j := by
  unfold hm_pairLaw hm_margLaw
  rw [hm_sum_snoc, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
  simp only [Fin.prod_univ_castSucc, h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last,
    Fin.snoc_last]
  by_cases hi : xs (Fin.last t) = i
  · simp only [hi, true_and, ↓reduceIte]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  · simp [hi]

end Miao.PartialInformation
