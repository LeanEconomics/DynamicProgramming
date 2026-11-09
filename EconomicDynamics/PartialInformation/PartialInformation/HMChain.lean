/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.HMFilter
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel

/-!
# Hidden Markov chain

Miao, §10.1.2, pp. 337–339. The `N` states are the unit vectors `e₁, …, e_N` of `ℝᴺ`
(`hm_e i = Pi.single i 1`) and the `M` signals the unit vectors `ξ₁, …, ξ_M` of `ℝᴹ`; the hidden
chain has transition matrix `P` (`pᵢⱼ = Pr(x_{t+1} = eⱼ | x_t = eᵢ)`) and the signals have the
`N × M` emission matrix `Q` (`qᵢⱼ = Pr(y_t = ξⱼ | x_t = eᵢ)`).

* (10.13): `E[x_{t+1} | x_t] = P′x_t`, so `v_{t+1} = x_{t+1} − P′x_t` has conditional mean
  zero; the algebra `x x′ = diag(x)` for a unit vector, the expansion of `v v′`, and
  `E[v_{t+1}v′_{t+1} | x_t] = diag(P′x_t) − P′ diag(x_t) P` (`eq_10_13`, `eq_10_13_mds`,
  `hm_unit_outer`, `hm_vv_expansion`, `eq_10_13_cov`). Conditional expectations given
  `x_t = eᵢ` are the finite sums `Σⱼ pᵢⱼ (·)(eⱼ)`; that `pᵢⱼ` is indeed the conditional
  probability in the path model of `HMFilter` is `hm_markov`.
* (10.14): the same for the signals, `E[y_t | x_t] = Q′x_t` and
  `E[w_t w′_t | x_t] = diag(Q′x_t) − Q′ diag(x_t) Q` (`eq_10_14`, `eq_10_14_mds`,
  `eq_10_14_cov`). The book writes the left side as `E[u_t u′_t | x_t]`; the shock is `w_t`.
* Bayes' rule, p. 338: `π_t(eᵢ | yᵗ⁻¹, y_t = ξⱼ) = Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹) /
  Σᵢ Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)` (`hm_bayes`, with the intermediate expression
  `hm_bayes_joint`), and the initial filter `π₀(eᵢ | y₀ = ξⱼ) = qᵢⱼ π^{ss}ᵢ / Σᵢ qᵢⱼ π^{ss}ᵢ`
  (`hm_bayes_initial`); with the stationary prior every `x_t` has law `π^{ss}`
  (`hm_stationary_marg`).
-/

namespace Miao.PartialInformation

open Matrix

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- The unit vector `eᵢ`. -/
def hm_e (i : X) : X → ℝ := Pi.single i 1

omit [Fintype Z] [DecidableEq Z] in
/-- `A′eᵢ` is the `i`-th row of `A`. -/
theorem hm_transpose_mulVec_e (A : Matrix X Z ℝ) (i : X) : Aᵀ *ᵥ hm_e i = fun k => A i k := by
  unfold hm_e
  rw [mulVec_single_one]
  rfl

/-- Conditional expectation of a vector function of the next unit vector, given `eᵢ` today and
the stochastic matrix `A`: `E[g(x′) | x = eᵢ] = Σⱼ aᵢⱼ g(eⱼ)`. -/
def hm_condE (A : Matrix X Z ℝ) (i : X) {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (g : (Z → ℝ) → V) : V :=
  ∑ j, A i j • g (hm_e j)

omit [DecidableEq Z] in
/-- The conditional mean of the next unit vector is `A′eᵢ`. -/
theorem hm_condE_id (A : Matrix X Z ℝ) (i : X) [DecidableEq Z] :
    hm_condE A i id = Aᵀ *ᵥ hm_e i := by
  rw [hm_transpose_mulVec_e]
  funext k
  simp [hm_condE, hm_e, Finset.sum_apply, Pi.single_apply]

/-- Miao, (10.13), p. 337: `E[x_{t+1} | x_t = eᵢ] = P′eᵢ`. -/
theorem eq_10_13 (P : Matrix X X ℝ) (i : X) : hm_condE P i id = Pᵀ *ᵥ hm_e i :=
  hm_condE_id P i

/-- A stochastic matrix leaves a zero-mean shock: `E[x′ − A′x | x = eᵢ] = 0`. -/
theorem hm_condE_mds (A : Matrix X Z ℝ) (hA : ∀ i, ∑ j, A i j = 1) (i : X) :
    hm_condE A i (fun z => z - Aᵀ *ᵥ hm_e i) = 0 := by
  have h := hm_condE_id A i
  unfold hm_condE at h ⊢
  rw [show (∑ j, A i j • (hm_e j - Aᵀ *ᵥ hm_e i)) =
      (∑ j, A i j • hm_e j) - (∑ j, A i j) • Aᵀ *ᵥ hm_e i by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]]
  rw [hA, one_smul]
  simp only [id] at h
  rw [h, sub_self]

/-- Miao, (10.13), p. 337: `v_{t+1} = x_{t+1} − P′x_t` is a martingale difference,
`E[v_{t+1} | x_t] = 0`. -/
theorem eq_10_13_mds (P : Matrix X X ℝ) (hP : ∀ i, ∑ j, P i j = 1) (i : X) :
    hm_condE P i (fun z => z - Pᵀ *ᵥ hm_e i) = 0 :=
  hm_condE_mds P hP i

omit [Fintype X] in
/-- Miao, p. 337: for a unit vector, `x x′ = diag(x)`. -/
theorem hm_unit_outer (j : X) : vecMulVec (hm_e j) (hm_e j) = diagonal (hm_e j) := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hj : k = j
    · subst hj; simp [hm_e, vecMulVec_apply]
    · simp [hm_e, vecMulVec_apply, hj]
  · by_cases hj : k = j
    · subst hj; simp [hm_e, vecMulVec_apply, Ne.symm hkl, hkl]
    · simp [hm_e, vecMulVec_apply, hj, hkl]

omit [Fintype X] in
/-- Miao, p. 337: with `x′ = m + v` (here `m = P′x_t`) the expansion
`x′x′′ = m m′ + m v′ + v m′ + v v′`, and, for a unit vector `x′`,
`v v′ = diag(m) + diag(v) − (m m′ + m v′ + v m′)`. -/
theorem hm_vv_expansion (j : X) (m : X → ℝ) :
    vecMulVec (hm_e j) (hm_e j) = vecMulVec m m + vecMulVec m (hm_e j - m) +
        vecMulVec (hm_e j - m) m + vecMulVec (hm_e j - m) (hm_e j - m) ∧
      diagonal (hm_e j) = diagonal m + diagonal (hm_e j - m) ∧
      vecMulVec (hm_e j - m) (hm_e j - m) = diagonal m + diagonal (hm_e j - m) -
        (vecMulVec m m + vecMulVec m (hm_e j - m) + vecMulVec (hm_e j - m) m) := by
  have h1 : vecMulVec (hm_e j) (hm_e j) = vecMulVec m m + vecMulVec m (hm_e j - m) +
      vecMulVec (hm_e j - m) m + vecMulVec (hm_e j - m) (hm_e j - m) := by
    ext k l; simp only [vecMulVec_apply, Matrix.add_apply, Pi.sub_apply]; ring
  have h2 : diagonal (hm_e j) = diagonal m + diagonal (hm_e j - m) := by
    rw [diagonal_add]; congr 1; funext k; simp
  refine ⟨h1, h2, ?_⟩
  rw [← h2, ← hm_unit_outer, h1]
  abel

/-- The conditional second moment of the shock of a stochastic matrix:
`E[(x′ − A′eᵢ)(x′ − A′eᵢ)′ | x = eᵢ] = diag(A′eᵢ) − A′ diag(eᵢ) A`. -/
theorem hm_condE_cov (A : Matrix X Z ℝ) (hA : ∀ i, ∑ j, A i j = 1) (i : X) :
    hm_condE A i (fun z => vecMulVec (z - Aᵀ *ᵥ hm_e i) (z - Aᵀ *ᵥ hm_e i)) =
      diagonal (Aᵀ *ᵥ hm_e i) - Aᵀ * diagonal (hm_e i) * A := by
  rw [hm_transpose_mulVec_e]
  ext k l
  have hs : ∀ k, ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 k = A i k := by
    intro k; simp [Pi.single_apply]
  simp only [hm_condE, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, hm_e,
    smul_eq_mul, Matrix.sub_apply, diagonal_apply, mul_apply, transpose_apply]
  have e1 : ∑ j, A i j * ((Pi.single (M := fun _ => ℝ) j (1 : ℝ) k - A i k) *
      (Pi.single (M := fun _ => ℝ) j (1 : ℝ) l - A i l)) =
      ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) l)
        - A i k * ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 l
        - A i l * ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 k
        + A i k * A i l * ∑ j, A i j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e1, hs, hs, hA]
  have e2 : ∑ x, (∑ x_1, A x_1 k * (if x_1 = x then Pi.single (M := fun _ => ℝ) i (1 : ℝ) x_1
      else 0)) * A x l = A i k * A i l := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e2]
  by_cases hkl : k = l
  · subst hkl
    have : ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) k) = A i k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    simp only [this, ↓reduceIte]
    ring
  · have : ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) l) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : k = j
      · subst hj; simp [Ne.symm hkl]
      · simp [Pi.single_apply, hj]
    simp only [this, hkl, ↓reduceIte]
    ring

/-- Miao, p. 338: `E[v_{t+1}v′_{t+1} | x_t] = diag(P′x_t) − P′ diag(x_t) P`, for
`x_t = eᵢ`. -/
theorem eq_10_13_cov (P : Matrix X X ℝ) (hP : ∀ i, ∑ j, P i j = 1) (i : X) :
    hm_condE P i (fun z => vecMulVec (z - Pᵀ *ᵥ hm_e i) (z - Pᵀ *ᵥ hm_e i)) =
      diagonal (Pᵀ *ᵥ hm_e i) - Pᵀ * diagonal (hm_e i) * P :=
  hm_condE_cov P hP i

/-- Miao, (10.14), p. 338: `E[y_t | x_t = eᵢ] = Q′eᵢ`. -/
theorem eq_10_14 (Q : Matrix X Z ℝ) (i : X) : hm_condE Q i id = Qᵀ *ᵥ hm_e i :=
  hm_condE_id Q i

/-- Miao, (10.14), p. 338: `w_t = y_t − Q′x_t` satisfies `E[w_t | x_t] = 0`. -/
theorem eq_10_14_mds (Q : Matrix X Z ℝ) (hQ : ∀ i, ∑ j, Q i j = 1) (i : X) :
    hm_condE Q i (fun z => z - Qᵀ *ᵥ hm_e i) = 0 :=
  hm_condE_mds Q hQ i

/-- Miao, p. 338: `E[w_t w′_t | x_t] = diag(Q′x_t) − Q′ diag(x_t) Q` for `x_t = eᵢ` (the book
writes `u_t` for `w_t`). -/
theorem eq_10_14_cov (Q : Matrix X Z ℝ) (hQ : ∀ i, ∑ j, Q i j = 1) (i : X) :
    hm_condE Q i (fun z => vecMulVec (z - Qᵀ *ᵥ hm_e i) (z - Qᵀ *ᵥ hm_e i)) =
      diagonal (Qᵀ *ᵥ hm_e i) - Qᵀ * diagonal (hm_e i) * Q :=
  hm_condE_cov Q hQ i

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 338 (Bayes' rule, first line): `π_t(eᵢ | yᵗ) = Pr(x_t = eᵢ, y_t | yᵗ⁻¹) /
Pr(y_t | yᵗ⁻¹)` with `Pr(x_t = eᵢ, y_t = ξⱼ | yᵗ⁻¹) = Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)` and
`Pr(y_t = ξⱼ | yᵗ⁻¹)` its sum over `i`. Here date `t − 1` is `t`, and `ys` is `yᵗ⁻¹`. -/
theorem hm_bayes_joint (μ0 : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Z) (hl : hm_lik μ0 P Q t ys ≠ 0) (j : Z) (i : X) :
    hm_joint μ0 P Q (t + 1) (Fin.snoc ys j) i / hm_lik μ0 P Q t ys =
      ∑ s, Q i j * P s i * hm_post μ0 P Q t ys s := by
  rw [hm_joint_forward, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold hm_post
  field_simp

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 338 (Bayes' rule): `π_t(eᵢ | yᵗ⁻¹, y_t = ξⱼ) =
Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹) / Σᵢ Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)`, whenever
`Pr(yᵗ⁻¹) ≠ 0`. -/
theorem hm_bayes (μ0 : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Z) (hl : hm_lik μ0 P Q t ys ≠ 0) (j : Z) (i : X) :
    hm_post μ0 P Q (t + 1) (Fin.snoc ys j) i =
      (∑ s, Q i j * P s i * hm_post μ0 P Q t ys s) /
        ∑ i', ∑ s, Q i' j * P s i' * hm_post μ0 P Q t ys s := by
  simp only [← hm_bayes_joint μ0 P Q t ys hl j]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hl]
  rfl

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 339: with prior `π^{ss}` for `x₀`,
`π₀(eᵢ | y₀ = ξⱼ) = qᵢⱼ π^{ss}ᵢ / Σᵢ qᵢⱼ π^{ss}ᵢ`. -/
theorem hm_bayes_initial (pss : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ)
    (ys : Fin 1 → Z) (i : X) :
    hm_post pss P Q 0 ys i = Q i (ys 0) * pss i / ∑ i', Q i' (ys 0) * pss i' := by
  unfold hm_post hm_lik
  simp only [hm_joint_zero, mul_comm (pss _)]

omit [Fintype Z] [DecidableEq Z] in
/-- The law of `x_{t+1}` is the sum over `i` of the pair law of `(x_t, x_{t+1})`. -/
theorem hm_margLaw_succ (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (j : X) :
    hm_margLaw μ0 P (t + 1) j = ∑ i, hm_pairLaw μ0 P t i j := by
  unfold hm_margLaw hm_pairLaw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  by_cases h : xs (Fin.last (t + 1)) = j
  · simp only [h, and_true, ↓reduceIte, Finset.sum_ite_eq, Finset.mem_univ]
  · simp [h]

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 339: when `x₀` has the stationary law `π^{ss}` (`π^{ss}′P = π^{ss}′`), every
`x_t` has law `π^{ss}`. -/
theorem hm_stationary_marg (pss : X → ℝ) (P : Matrix X X ℝ)
    (hss : ∀ j, ∑ i, pss i * P i j = pss j) : ∀ (t : ℕ) (i : X), hm_margLaw pss P t i = pss i
  | 0, i => by
    unfold hm_margLaw
    rw [hm_sum_fin_one]
    simp
  | t + 1, j => by
    rw [hm_margLaw_succ]
    simp only [hm_markov, hm_stationary_marg pss P hss t]
    exact hss j

end Miao.PartialInformation
