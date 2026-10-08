import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Max
import Mathlib.Order.Monotone.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.Group.MinMax
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, distributions, contractions: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 3 uses the
Markov matrices of §2.3.1.3 and §2.3.3.4, distributions on a finite set, and
the contraction machinery of §1.2.2. Each chapter project is self-contained,
so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X]

/-- A stochastic (Markov) matrix on the finite state space `X` (Vol. 1, p. 71): nonnegative with
unit row sums. The book writes `P ∈ M(ℝ^X)`. -/
structure IsMarkov (P : Matrix X X ℝ) : Prop where
  nonneg : ∀ x x', 0 ≤ P x x'
  rowsum : ∀ x, ∑ x', P x x' = 1

/-- A distribution on `X` (Vol. 1, p. 31): nonnegative and summing to one. -/
structure IsDistribution (ψ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  sum_eq_one : ∑ x, ψ x = 1

theorem IsMarkov.mul {P Q : Matrix X X ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg x x' := sum_nonneg fun z _ => mul_nonneg (hP.nonneg x z) (hQ.nonneg z x')
  rowsum x := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

/-- The `k`-step transition matrix `Pᵏ` is Markov (§3.1.1.3, p. 83). -/
theorem IsMarkov.pow [DecidableEq X] {P : Matrix X X ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A Markov matrix preserves `≤` on functions: the step behind monotonicity arguments. -/
theorem IsMarkov.mulVec_le_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {f g : X → ℝ} (hfg : f ≤ g) :
    P *ᵥ f ≤ P *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hP.nonneg x x')

/-- `P𝟙 = 𝟙`: constants are fixed by a Markov matrix. -/
theorem IsMarkov.mulVec_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, ← sum_mul, hP.rowsum, one_mul]

/-- `|Ph| ≤ P|h|` pointwise (Vol. 1, Ex 2.2.7), and hence `|Ph(x)| ≤ ‖h‖_∞`. -/
theorem IsMarkov.abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) (x : X) :
    |(P *ᵥ h) x| ≤ ‖h‖ := by
  have hb : ∀ x', |h x'| ≤ ‖h‖ := fun x' => by
    have := norm_le_pi_norm h x'
    rwa [Real.norm_eq_abs] at this
  calc |(P *ᵥ h) x| = |∑ x', P x x' * h x'| := rfl
    _ ≤ ∑ x', |P x x' * h x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', P x x' * |h x'| := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', P x x' * ‖h‖ :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hb x') (hP.nonneg x x')
    _ = ‖h‖ := by rw [← sum_mul, hP.rowsum, one_mul]

/-- `‖Pf − Pg‖_∞ ≤ ‖f − g‖_∞`. -/
theorem IsMarkov.norm_mulVec_sub_le {P : Matrix X X ℝ} (hP : IsMarkov P) (f g : X → ℝ) :
    ‖P *ᵥ f - P *ᵥ g‖ ≤ ‖f - g‖ := by
  rw [← mulVec_sub, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  exact hP.abs_mulVec_le (f - g) x

/-- Global stability (Vol. 1, p. 22). -/
def GloballyStable {U : Type*} [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

theorem globallyStable_of_tendsto {U : Type*} [TopologicalSpace U] [T2Space U] {T : U → U} {u' : U}
    (hfix : IsFixedPt T u') (hlim : ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) :
    GloballyStable T := by
  refine ⟨u', hfix, fun v hv => ?_, hlim⟩
  have hconst : Tendsto (fun k : ℕ => T^[k] v) atTop (𝓝 v) := by
    have : (fun k : ℕ => T^[k] v) = fun _ => v := funext fun k => IsFixedPt.iterate hv k
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst (hlim v)

variable {E : Type*} [NormedAddCommGroup E]

/-- A contraction of modulus `L` on `U` (Vol. 1, (1.17)). -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : Set.MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact h.mapsTo ih

theorem norm_iterate_sub_fixedPt_le (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') (k : ℕ) :
    ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    calc ‖T (T^[k] u) - u'‖ = ‖T (T^[k] u) - T u'‖ := by rw [hfix.eq]
      _ ≤ L * ‖T^[k] u - u'‖ := h.norm_sub_le _ (h.iterate_mem hu k) _ hu'
      _ ≤ L * (L ^ k * ‖u - u'‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (k + 1) * ‖u - u'‖ := by ring

theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖

/-- Banach's theorem (Vol. 1, Theorem 1.2.3), existence, from Mathlib's `ContractingWith`. -/
theorem exists_fixedPt [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : ∃ u' ∈ U, IsFixedPt T u' := by
  have : CompleteSpace U := hU.completeSpace_coe
  have : Nonempty U := hne.to_subtype
  let T' : U → U := h.mapsTo.restrict T U U
  have hT' : ContractingWith ⟨L, h.nonneg⟩ T' := by
    refine ⟨by exact_mod_cast h.lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [T', Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact h.norm_sub_le x x.2 y y.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, IsFixedPt T' u₀ := ⟨_, hT'.fixedPoint_isFixedPt⟩
  exact ⟨u₀.1, u₀.2, congrArg Subtype.val hu₀⟩

end IsContractionOn

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov chains on a finite state space

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.1 and §3.1.2
(pp. 81–88).

A `P`-Markov chain is a process whose next-state distribution given the
history is `P(Xₜ, ·)`, (3.1). What the chapter proves about such chains is
expressed through `P` alone: the `k`-step transition probabilities are the
entries of `Pᵏ`, (3.2), written here as a sum of path probabilities, with the
law of total probability `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z)P(z, x')` of Exercise
3.1.2; the marginal distributions evolve by `ψₜ₊₁ = ψₜP`, (3.3)–(3.5);
expectations are `E h(Xₜ) = ⟨ψ₀Pᵗ, h⟩`, (3.6), Exercise 3.1.4; stationary
distributions are fixed points of `ψ ↦ ψP`. Lemma 3.1.1 characterises
irreducibility. The ergodic theorem (Theorem 3.1.2) is cited by the book from
Brémaud (2020) and is not claimed here: it is a statement about almost every
sample path, which the finite-dimensional description does not reach.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The probability of a path `z₀, z₁, …, zₖ` under `P`: `∏ P(zᵢ, zᵢ₊₁)` (Algorithm 3.1). -/
def pathProb (P : Matrix X X ℝ) {k : ℕ} (z : Fin (k + 1) → X) : ℝ :=
  ∏ i : Fin k, P (z i.castSucc) (z i.succ)

/-- Paths of length `k` from `x` to `x'`. -/
def paths (k : ℕ) (x x' : X) : Finset (Fin (k + 1) → X) :=
  univ.filter fun z => z 0 = x ∧ z (Fin.last k) = x'

omit [Fintype X] [DecidableEq X] in
/-- Appending a step to a path multiplies its probability by the transition probability. -/
theorem pathProb_snoc (P : Matrix X X ℝ) {k : ℕ} (w : Fin (k + 1) → X) (x' : X) :
    pathProb P (Fin.snoc w x' : Fin (k + 2) → X) = pathProb P w * P (w (Fin.last k)) x' := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

/-- (3.2), p. 85: `Pᵏ(x, x')` is the probability that a `P`-Markov chain started at `x` is at
`x'` after `k` steps, the total probability of all paths from `x` to `x'` of length `k`. -/
theorem pow_apply_eq_sum_paths (P : Matrix X X ℝ) (k : ℕ) (x x' : X) :
    (P ^ k) x x' = ∑ z ∈ paths k x x', pathProb P z := by
  induction k generalizing x' with
  | zero =>
    -- the only path of length `0` is the constant path, present iff `x = x'`
    simp only [pow_zero, Matrix.one_apply, paths, pathProb, Fin.last_zero]
    by_cases hxx : x = x'
    · subst hxx
      have h1 : (if x = x then (1 : ℝ) else 0) = 1 := by simp
      rw [h1]
      have : (univ.filter fun z : Fin 1 → X => z 0 = x ∧ z 0 = x) = {fun _ => x} := by
        ext z
        simp only [mem_filter, mem_univ, true_and, mem_singleton, and_self]
        constructor
        · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
        · rintro rfl; rfl
      rw [this, sum_singleton]
      simp
    · have h1 : (if x = x' then (1 : ℝ) else 0) = 0 := by simp [hxx]
      rw [h1]
      refine (sum_eq_zero fun z hz => ?_).symm
      exfalso
      simp only [mem_filter, mem_univ, true_and] at hz
      exact hxx (hz.1.symm.trans hz.2)
  | succ k ih =>
    -- `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z) P(z, x')`; a path of length `k + 1` from `x` to `x'` is a path of
    -- length `k` from `x` to some `z`, followed by the step `z → x'`
    rw [pow_succ, Matrix.mul_apply]
    have hsplit : ∀ z, (P ^ k) x z * P z x' = ∑ w ∈ paths k x z, pathProb P w * P z x' := by
      intro z
      rw [ih z, sum_mul]
    simp only [hsplit]
    have hfib : ∀ z, paths k x z =
        (univ.filter fun w : Fin (k + 1) → X => w 0 = x).filter (fun w => w (Fin.last k) = z) := by
      intro z
      ext w
      simp [paths]
    have hz : ∀ z, ∑ w ∈ paths k x z, pathProb P w * P z x' =
        ∑ w ∈ (univ.filter fun w : Fin (k + 1) → X => w 0 = x).filter
          (fun w => w (Fin.last k) = z), pathProb P w * P (w (Fin.last k)) x' := by
      intro z
      rw [hfib]
      exact sum_congr rfl fun w hw => by rw [(mem_filter.1 hw).2]
    simp only [hz]
    rw [Finset.sum_fiberwise (univ.filter fun w : Fin (k + 1) → X => w 0 = x)
      (fun w => w (Fin.last k)) (fun w => pathProb P w * P (w (Fin.last k)) x')]
    -- the paths of length `k + 1` from `x` to `x'` are the images of the paths from `x` under
    -- `w ↦ snoc w x'`
    have himage : paths (k + 1) x x' =
        (univ.filter fun w : Fin (k + 1) → X => w 0 = x).image
          (fun w => (Fin.snoc w x' : Fin (k + 2) → X)) := by
      ext v
      simp only [paths, mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨h0, hl⟩
        refine ⟨Fin.init v, ?_, ?_⟩
        · simpa [Fin.init] using h0
        · rw [← hl]
          exact Fin.snoc_init_self v
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, Fin.snoc_last _ _⟩
        change (Fin.snoc w x' : Fin (k + 2) → X) 0 = x
        rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
        exact hw
    rw [himage, sum_image]
    · exact sum_congr rfl fun w _ => (pathProb_snoc P w x').symm
    · intro w _ v _ h
      have := congrArg Fin.init h
      rwa [Fin.init_snoc, Fin.init_snoc] at this

/-- Exercise 3.1.2 (p. 85), the inductive step: `Pᵏ⁺¹(x, x') = ∑_z Pᵏ(x, z) P(z, x')` is the law
of total probability for the `(k + 1)`-step transition. -/
theorem pow_succ_apply (P : Matrix X X ℝ) (k : ℕ) (x x' : X) :
    (P ^ (k + 1)) x x' = ∑ z, (P ^ k) x z * P z x' := by
  rw [pow_succ, Matrix.mul_apply]

/-! ### Marginal distributions (§3.1.2) -/

omit [DecidableEq X] in
/-- (3.3)–(3.4), p. 86: the next marginal distribution is `ψP`, `ψ'(x') = ∑ₓ P(x, x')ψ(x)`. -/
theorem vecMul_apply (P : Matrix X X ℝ) (ψ : X → ℝ) (x' : X) :
    (ψ ᵥ* P) x' = ∑ x, P x x' * ψ x := by
  simp only [vecMul, dotProduct, mul_comm]

omit [DecidableEq X] in
/-- `ψ ↦ ψP` maps distributions to distributions (Vol. 1, Ex 2.3.14). -/
theorem IsMarkov.isDistribution_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) : IsDistribution (ψ ᵥ* P) where
  nonneg x' := by
    rw [vecMul_apply]
    exact sum_nonneg fun x _ => mul_nonneg (hP.nonneg x x') (hψ.nonneg x)
  sum_eq_one := by
    simp only [vecMul_apply]
    rw [sum_comm]
    simp only [← sum_mul, hP.rowsum, one_mul, hψ.sum_eq_one]

/-- `ψPᵗ` is a distribution whenever `ψ` is. -/
theorem IsMarkov.isDistribution_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (t : ℕ) : IsDistribution (ψ ᵥ* P ^ t) := by
  induction t with
  | zero => simpa using hψ
  | succ t ih => rw [pow_succ, ← vecMul_vecMul]; exact hP.isDistribution_vecMul ih

/-- (3.5), p. 86: iterating `ψₜ₊₁ = ψₜP` gives `ψₜ = ψ₀Pᵗ`. -/
theorem iterate_vecMul (P : Matrix X X ℝ) (ψ : X → ℝ) (t : ℕ) :
    (fun φ => φ ᵥ* P)^[t] ψ = ψ ᵥ* P ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, vecMul_vecMul, pow_succ]

/-- Exercise 3.1.4 (p. 87), (3.6): `E h(Xₜ) = ∑ h(x)(ψ₀Pᵗ)(x) = ⟨ψ₀Pᵗ, h⟩`, which also equals
`ψ₀(Pᵗh)`. -/
theorem expectation_eq_dotProduct (P : Matrix X X ℝ) (ψ₀ h : X → ℝ) (t : ℕ) :
    ∑ x, h x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ t) ⬝ᵥ h ∧
      (ψ₀ ᵥ* P ^ t) ⬝ᵥ h = ψ₀ ⬝ᵥ (P ^ t *ᵥ h) := by
  constructor
  · simp only [dotProduct, mul_comm]
  · rw [dotProduct_mulVec]

/-- A stationary distribution (p. 87): `ψ*P = ψ*`. -/
def IsStationary (P : Matrix X X ℝ) (ψ : X → ℝ) : Prop := ψ ᵥ* P = ψ

/-- If `ψ*` is stationary and `Xₜ ∼ ψ*`, then `Xₜ₊ₖ ∼ ψ*` for all `k` (p. 87). -/
theorem IsStationary.vecMul_pow {P : Matrix X X ℝ} {ψ : X → ℝ} (h : IsStationary P ψ) (k : ℕ) :
    ψ ᵥ* P ^ k = ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, h]

/-! ### Irreducibility (Lemma 3.1.1) -/

/-- Irreducibility (Vol. 1, p. 69): `P ≥ 0` and every state leads to every other in some positive
number of steps, `∑_{k≥1} Pᵏ ≫ 0`. -/
def Irreducible (P : Matrix X X ℝ) : Prop :=
  (∀ x x', 0 ≤ P x x') ∧ ∀ x x', ∃ k ≥ 1, 0 < (P ^ k) x x'

/-- Entries of products of nonnegative matrices dominate single terms:
`Pᵃ⁺ᵇ(x, x') ≥ Pᵃ(x, z) Pᵇ(z, x')`. -/
theorem IsMarkov.pow_add_apply_ge {P : Matrix X X ℝ} (hP : IsMarkov P) (a b : ℕ) (x z x' : X) :
    (P ^ a) x z * (P ^ b) z x' ≤ (P ^ (a + b)) x x' := by
  rw [pow_add, Matrix.mul_apply]
  exact single_le_sum (fun y _ => mul_nonneg ((hP.pow a).nonneg x y) ((hP.pow b).nonneg y x'))
    (mem_univ z)

/-- Lemma 3.1.1 (p. 85): a Markov matrix is irreducible iff for all `x, x'` some `k ≥ 0` has
`Pᵏ(x, x') > 0`, i.e. the chain eventually visits every state from every state with positive
probability. The `k = 0` case only arises for `x = x'`, and then a positive-step return exists
through any other state, or by `P(x, x) = 1` when `X = {x}`. -/
theorem IsMarkov.irreducible_iff {P : Matrix X X ℝ} (hP : IsMarkov P) :
    Irreducible P ↔ ∀ x x', ∃ k, 0 < (P ^ k) x x' := by
  constructor
  · rintro ⟨-, h⟩ x x'
    obtain ⟨k, -, hk⟩ := h x x'
    exact ⟨k, hk⟩
  · intro h
    refine ⟨hP.nonneg, fun x x' => ?_⟩
    by_cases hxx : x = x'
    · subst hxx
      -- a return to `x` in a positive number of steps
      by_cases hX : ∃ y, y ≠ x
      · obtain ⟨y, hy⟩ := hX
        obtain ⟨k₁, hk₁⟩ := h x y
        obtain ⟨k₂, hk₂⟩ := h y x
        have hk₁' : 1 ≤ k₁ := by
          rcases Nat.eq_zero_or_pos k₁ with rfl | hpos
          · simp [Ne.symm hy] at hk₁
          · exact hpos
        refine ⟨k₁ + k₂, by omega, ?_⟩
        exact lt_of_lt_of_le (mul_pos hk₁ hk₂) (hP.pow_add_apply_ge k₁ k₂ x y x)
      · -- `X = {x}`: the row sum forces `P(x, x) = 1`
        have hX' : ∀ y, y = x := fun y => by
          by_contra hy
          exact hX ⟨y, hy⟩
        refine ⟨1, le_rfl, ?_⟩
        rw [pow_one]
        have := hP.rowsum x
        rw [Fintype.sum_eq_single x (fun y hy => absurd (hX' y) hy)] at this
        rw [this]
        exact one_pos
    · obtain ⟨k, hk⟩ := h x x'
      refine ⟨k, ?_, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp [hxx] at hk
      · exact hpos

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# S–s inventory dynamics

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.1.2 (pp. 82–84)
and Exercises 3.1.1, 3.1.3.

A firm reorders `S` units whenever its inventory `Xₜ` is at or below `s`;
demand `Dₜ₊₁` is IID geometric with parameter `p`:
`Xₜ₊₁ = max{Xₜ − Dₜ₊₁, 0} + S·1{Xₜ ≤ s}`. Exercise 3.1.1: the state space
`{0, …, S + s}` is invariant. The transition matrix is
`P(x, x') = ∑_d 1{h(x, d) = x'} φ(d)`, and Exercise 3.1.3 shows it is
irreducible: from any state the chain reaches `s`, then `S + s`, then any
state, each step with positive probability. The book proves this for `x > s`
and leaves `x ≤ s` to the reader; here the case `x ≤ s` is handled by a
first step to `S` (demand at least `x`), which needs `s < S` as in the
book's calibration (`S = 100`, `s = 10`). Without `s < S` the chain is still
irreducible but reaches `s` only after several reorders; that case is not
formalised.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

/-- The S–s inventory model: order size `S`, threshold `s`, geometric demand parameter `p`. -/
structure Inventory where
  S : ℕ
  s : ℕ
  p : ℝ
  s_lt_S : s < S
  p_pos : 0 < p
  p_lt_one : p < 1

namespace Inventory

variable (m : Inventory)

/-- The state space `X = {0, …, S + s}`, as `Fin (S + s + 1)`. -/
abbrev State := Fin (m.S + m.s + 1)

/-- The update rule `h(x, d) = max{x − d, 0} + S·1{x ≤ s}` (p. 83); `ℕ` subtraction is the
truncation `max{x − d, 0}`. -/
def h (x d : ℕ) : ℕ := (x - d) + if x ≤ m.s then m.S else 0

/-- Exercise 3.1.1 (p. 83): `X = {0, …, S + s}` is invariant: `x ≤ S + s` implies
`h(x, d) ≤ S + s`. -/
theorem h_le (x d : ℕ) (hx : x ≤ m.S + m.s) : m.h x d ≤ m.S + m.s := by
  unfold h
  split_ifs with hxs <;> omega

/-- The next state, as an element of the state space. -/
def next (x : m.State) (d : ℕ) : m.State :=
  ⟨m.h x d, Nat.lt_succ_of_le (m.h_le x d (Nat.le_of_lt_succ x.2))⟩

/-- The geometric demand distribution `φ(d) = p(1 − p)^d` on `ℤ₊` (p. 83). -/
noncomputable def φ (d : ℕ) : ℝ := m.p * (1 - m.p) ^ d

theorem φ_pos (d : ℕ) : 0 < m.φ d :=
  mul_pos m.p_pos (pow_pos (by linarith [m.p_lt_one]) d)

theorem one_sub_p_nonneg : 0 ≤ 1 - m.p := by linarith [m.p_lt_one]

theorem one_sub_p_lt_one : 1 - m.p < 1 := by linarith [m.p_pos]

theorem summable_φ : Summable m.φ :=
  (summable_geometric_of_lt_one m.one_sub_p_nonneg m.one_sub_p_lt_one).mul_left m.p

/-- The demand distribution sums to one. -/
theorem tsum_φ : ∑' d, m.φ d = 1 := by
  unfold φ
  rw [tsum_mul_left, tsum_geometric_of_lt_one m.one_sub_p_nonneg m.one_sub_p_lt_one]
  have h1 : (1 : ℝ) - (1 - m.p) = m.p := by ring
  rw [h1, inv_eq_one_div, mul_one_div, div_self m.p_pos.ne']

/-- The transition matrix `P(x, x') = ∑_d 1{h(x, d) = x'} φ(d)` (p. 83). -/
noncomputable def P : Matrix m.State m.State ℝ :=
  Matrix.of fun x x' => ∑' d : ℕ, if m.next x d = x' then m.φ d else 0

theorem P_apply (x x' : m.State) : m.P x x' = ∑' d : ℕ, if m.next x d = x' then m.φ d else 0 := rfl

theorem summable_term (x x' : m.State) :
    Summable fun d : ℕ => if m.next x d = x' then m.φ d else 0 :=
  m.summable_φ.of_nonneg_of_le (fun d => by split_ifs <;> [exact (m.φ_pos d).le; exact le_rfl])
    (fun d => by split_ifs <;> [exact le_rfl; exact (m.φ_pos d).le])

/-- `P` is a Markov matrix: nonnegative, and each row sums to `∑_d φ(d) = 1` because every demand
leads to exactly one next state. -/
theorem isMarkov_P : IsMarkov m.P where
  nonneg x x' := tsum_nonneg fun d => by split_ifs <;> [exact (m.φ_pos d).le; exact le_rfl]
  rowsum x := by
    simp only [P_apply]
    rw [← Summable.tsum_finsetSum fun x' _ => m.summable_term x x', ← m.tsum_φ]
    refine tsum_congr fun d => ?_
    rw [sum_ite_eq univ (m.next x d) (fun _ => m.φ d)]
    simp

/-- A single demand realisation gives a lower bound on a transition probability. -/
theorem φ_le_P (x : m.State) (d : ℕ) : m.φ d ≤ m.P x (m.next x d) := by
  rw [P_apply]
  have := (m.summable_term x (m.next x d)).le_tsum d fun d' _ => by
    split_ifs <;> [exact (m.φ_pos d').le; exact le_rfl]
  simpa using this

/-- Transitions realised by some demand have positive probability. -/
theorem P_pos (x : m.State) (d : ℕ) : 0 < m.P x (m.next x d) := (m.φ_pos d).trans_le (m.φ_le_P x d)

theorem next_val (x : m.State) (d : ℕ) : (m.next x d : ℕ) = m.h x d := rfl

/-- The threshold state `s`. -/
def sState : m.State := ⟨m.s, by omega⟩

theorem sState_val : (m.sState : ℕ) = m.s := rfl

/-- The full state `S + s`. -/
def fullState : m.State := ⟨m.S + m.s, by omega⟩

theorem fullState_val : (m.fullState : ℕ) = m.S + m.s := rfl

/-- The state `S`. -/
def SState : m.State := ⟨m.S, by omega⟩

theorem SState_val : (m.SState : ℕ) = m.S := rfl

/-- From `x > s`, demand `x − s` leads to `s`. -/
theorem next_eq_sState {x : m.State} (hx : m.s < x) : m.next x ((x : ℕ) - m.s) = m.sState := by
  rw [Fin.ext_iff, next_val, sState_val]
  unfold h
  split_ifs <;> omega

/-- From `s`, zero demand leads to `S + s`. -/
theorem next_sState_zero : m.next m.sState 0 = m.fullState := by
  rw [Fin.ext_iff, next_val, sState_val, fullState_val]
  unfold h
  split_ifs <;> omega

/-- From `S + s`, demand `S + s − y` leads to any `y`. -/
theorem next_fullState (y : m.State) : m.next m.fullState (m.S + m.s - y) = y := by
  rw [Fin.ext_iff, next_val, fullState_val]
  unfold h
  have hy : (y : ℕ) ≤ m.S + m.s := Nat.le_of_lt_succ y.2
  have hs := m.s_lt_S
  split_ifs <;> omega

/-- From `x ≤ s`, demand `x` leads to `S`. -/
theorem next_eq_SState {x : m.State} (hx : (x : ℕ) ≤ m.s) : m.next x x = m.SState := by
  rw [Fin.ext_iff, next_val, SState_val]
  unfold h
  split_ifs
  omega

/-- Exercise 3.1.3 (p. 85): the inventory chain is irreducible. From `x > s`: `x → s → S + s → y`
in three steps; from `x ≤ s`: `x → S → s → S + s → y` in four, using `s < S`. -/
theorem irreducible_P : Irreducible m.P := by
  have hM := m.isMarkov_P
  refine ⟨hM.nonneg, fun x y => ?_⟩
  -- the three-step path from `s`'s predecessor: `s → S + s → y`
  have h2 : 0 < (m.P ^ 2) m.sState y := by
    have := hM.pow_add_apply_ge 1 1 m.sState m.fullState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ ?_) this
    · have := m.P_pos m.sState 0
      rwa [m.next_sState_zero] at this
    · have := m.P_pos m.fullState (m.S + m.s - y)
      rwa [m.next_fullState y] at this
  by_cases hx : m.s < x
  · refine ⟨3, by norm_num, ?_⟩
    have := hM.pow_add_apply_ge 1 2 x m.sState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ h2) this
    have := m.P_pos x ((x : ℕ) - m.s)
    rwa [m.next_eq_sState hx] at this
  · refine ⟨4, by norm_num, ?_⟩
    have hxs : (x : ℕ) ≤ m.s := not_lt.1 hx
    have hS : m.s < m.SState := m.s_lt_S
    have h3 : 0 < (m.P ^ 3) m.SState y := by
      have := hM.pow_add_apply_ge 1 2 m.SState m.sState y
      rw [pow_one] at this
      refine lt_of_lt_of_le (mul_pos ?_ h2) this
      have := m.P_pos m.SState ((m.SState : ℕ) - m.s)
      rwa [m.next_eq_sState hS] at this
    have := hM.pow_add_apply_ge 1 3 x m.SState y
    rw [pow_one] at this
    refine lt_of_lt_of_le (mul_pos ?_ h3) this
    have := m.P_pos x x
    rwa [m.next_eq_SState hxs] at this

end Inventory

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Everywhere-positive Markov matrices are globally stable on `D(X)`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Exercise 3.1.7
(p. 89): for a Markov matrix `P ≫ 0`, the map `ψ ↦ ψP` is globally stable on
the distributions `D(X)`. The book's hint is the Perron–Frobenius theorem;
the proof here is Dobrushin's ℓ¹ contraction estimate instead. If every
entry of `P` is at least `ε > 0`, then for any `d` with `∑ d = 0`,
`‖dP‖₁ ≤ (1 − nε)‖d‖₁`, since `(dP)(x') = ∑ₓ d(x)(P(x, x') − ε)`. The orbit
of any distribution is therefore Cauchy, its limit `ψ*` is a stationary
distribution, every stationary distribution equals `ψ*`, and `ψPᵗ → ψ*` at
the geometric rate `(1 − nε)ᵗ`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The ℓ¹ norm `‖d‖₁ = ∑ |d(x)|` on `ℝ^X`. -/
def l1 (d : X → ℝ) : ℝ := ∑ x, |d x|

omit [DecidableEq X] in
theorem l1_nonneg (d : X → ℝ) : 0 ≤ l1 d := sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq X] in
/-- The supremum norm is bounded by the ℓ¹ norm. -/
theorem norm_le_l1 (d : X → ℝ) : ‖d‖ ≤ l1 d := by
  rw [pi_norm_le_iff_of_nonneg (l1_nonneg d)]
  intro x
  rw [Real.norm_eq_abs]
  exact single_le_sum (fun y _ => abs_nonneg (d y)) (mem_univ x)

omit [DecidableEq X] in
theorem l1_eq_zero_iff (d : X → ℝ) : l1 d = 0 ↔ d = 0 := by
  constructor
  · intro h
    funext x
    have := (sum_eq_zero_iff_of_nonneg fun y _ => abs_nonneg (d y)).1 h x (mem_univ x)
    simpa using this
  · rintro rfl
    simp [l1]

omit [DecidableEq X] in
/-- `ψ ↦ ψP` preserves total mass: `∑ (dP) = ∑ d`. -/
theorem sum_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) :
    ∑ x', (d ᵥ* P) x' = ∑ x, d x := by
  have h : ∀ x', (d ᵥ* P) x' = ∑ x, P x x' * d x := fun x' => vecMul_apply P d x'
  simp only [h]
  rw [sum_comm]
  simp only [← sum_mul, hP.rowsum, one_mul]

omit [DecidableEq X] in
/-- Dobrushin's estimate: if every entry of the Markov matrix `P` is at least `ε`, then for `d`
with `∑ d = 0`, `‖dP‖₁ ≤ (1 − nε)‖d‖₁`, where `n = |X|`. -/
theorem l1_vecMul_le {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ} (hε : ∀ x x', ε ≤ P x x')
    {d : X → ℝ} (hd : ∑ x, d x = 0) :
    l1 (d ᵥ* P) ≤ (1 - Fintype.card X * ε) * l1 d := by
  -- `(dP)(x') = ∑ₓ d(x)(P(x, x') − ε)` because `∑ d = 0`
  have hkey : ∀ x', (d ᵥ* P) x' = ∑ x, d x * (P x x' - ε) := by
    intro x'
    rw [vecMul_apply]
    have : ∑ x, d x * (P x x' - ε) = ∑ x, d x * P x x' - (∑ x, d x) * ε := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hd, zero_mul, sub_zero]
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hrow : ∀ x, ∑ x', (P x x' - ε) = 1 - Fintype.card X * ε := by
    intro x
    rw [sum_sub_distrib, hP.rowsum, sum_const, card_univ, nsmul_eq_mul]
  unfold l1
  calc ∑ x', |(d ᵥ* P) x'| ≤ ∑ x', ∑ x, |d x| * (P x x' - ε) := by
        refine sum_le_sum fun x' _ => ?_
        rw [hkey]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hε x x'))]
    _ = ∑ x, |d x| * ∑ x', (P x x' - ε) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = (1 - Fintype.card X * ε) * ∑ x, |d x| := by
        simp only [hrow]
        rw [← sum_mul, mul_comm]

/-- `ψ ↦ ψPᵗ` preserves total mass. -/
theorem sum_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) (t : ℕ) :
    ∑ x, (d ᵥ* P ^ t) x = ∑ x, d x := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← vecMul_vecMul, sum_vecMul hP, ih]

/-- The iterated estimate: `‖dPᵗ‖₁ ≤ (1 − nε)ᵗ ‖d‖₁` for `∑ d = 0`. -/
theorem l1_vecMul_pow_le {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ} (hε : ∀ x x', ε ≤ P x x')
    (hlam : 0 ≤ 1 - Fintype.card X * ε) {d : X → ℝ} (hd : ∑ x, d x = 0) (t : ℕ) :
    l1 (d ᵥ* P ^ t) ≤ (1 - Fintype.card X * ε) ^ t * l1 d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← vecMul_vecMul]
    have hsum : ∑ x, (d ᵥ* P ^ t) x = 0 := by rw [sum_vecMul_pow hP, hd]
    calc l1 ((d ᵥ* P ^ t) ᵥ* P) ≤ (1 - Fintype.card X * ε) * l1 (d ᵥ* P ^ t) :=
          l1_vecMul_le hP hε hsum
      _ ≤ (1 - Fintype.card X * ε) * ((1 - Fintype.card X * ε) ^ t * l1 d) :=
          mul_le_mul_of_nonneg_left ih hlam
      _ = (1 - Fintype.card X * ε) ^ (t + 1) * l1 d := by ring

omit [DecidableEq X] in
/-- Coordinatewise continuity of `φ ↦ φP`: limits pass through `ᵥ*`. -/
theorem tendsto_vecMul {P : Matrix X X ℝ} {u : ℕ → X → ℝ} {a : X → ℝ}
    (h : Tendsto u atTop (𝓝 a)) : Tendsto (fun t => u t ᵥ* P) atTop (𝓝 (a ᵥ* P)) := by
  rw [tendsto_pi_nhds] at h ⊢
  intro x'
  simp only [vecMul_apply]
  exact tendsto_finsetSum _ fun x _ => (h x).const_mul _

/-- Exercise 3.1.7 (p. 89), general form: if `P` is a Markov matrix with every entry positive,
then `ψ ↦ ψP` is globally stable on `D(X)`: there is a stationary distribution `ψ*`, it is the
only stationary distribution, and `ψPᵗ → ψ*` for every distribution `ψ`. -/
theorem globallyStable_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ IsStationary P ψ' ∧
      (∀ φ, IsDistribution φ → IsStationary P φ → φ = ψ') ∧
      ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
  -- the smallest entry `ε > 0` and the modulus `λ = 1 − nε ∈ [0, 1)`
  obtain ⟨p, -, hp⟩ := exists_min_image (univ : Finset (X × X)) (fun q => P q.1 q.2) univ_nonempty
  set ε := P p.1 p.2 with hεdef
  have hε : ∀ x x', ε ≤ P x x' := fun x x' => hp (x, x') (mem_univ _)
  have hεpos : 0 < ε := hpos _ _
  set n : ℕ := Fintype.card X with hn
  have hnpos : 0 < n := Fintype.card_pos
  set lam : ℝ := 1 - n * ε with hlam
  have hlam0 : 0 ≤ lam := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have h1 := hP.rowsum x
    have h2 : ∑ x' : X, ε ≤ ∑ x', P x x' := sum_le_sum fun x' _ => hε x x'
    rw [sum_const, card_univ, nsmul_eq_mul, h1] at h2
    rw [hlam]
    linarith
  have hlam1 : lam < 1 := by
    rw [hlam]
    have : (0 : ℝ) < n * ε := by positivity
    linarith
  -- the orbit of the uniform distribution is Cauchy
  set ψ₀ : X → ℝ := fun _ => (n : ℝ)⁻¹ with hψ₀
  have hψ₀dist : IsDistribution ψ₀ := ⟨fun _ => by positivity, by
    rw [hψ₀]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)⟩
  set u : ℕ → X → ℝ := fun t => ψ₀ ᵥ* P ^ t with hu
  have hzero : ∑ x, (ψ₀ - ψ₀ ᵥ* P) x = 0 := by
    simp only [Pi.sub_apply]
    rw [sum_sub_distrib, sum_vecMul hP, sub_self]
  have hstep : ∀ t, dist (u t) (u (t + 1)) ≤ l1 (ψ₀ - ψ₀ ᵥ* P) * lam ^ t := by
    intro t
    rw [dist_eq_norm, hu]
    have h1 : ψ₀ ᵥ* P ^ t - ψ₀ ᵥ* P ^ (t + 1) = (ψ₀ - ψ₀ ᵥ* P) ᵥ* P ^ t := by
      rw [sub_vecMul, pow_succ', ← vecMul_vecMul]
    simp only
    rw [h1]
    refine (norm_le_l1 _).trans ?_
    rw [mul_comm]
    exact l1_vecMul_pow_le hP hε hlam0 hzero t
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric lam _ hlam1 hstep
  obtain ⟨ψ', hψ'⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- `ψ'` is a distribution
  have hψ'dist : IsDistribution ψ' := by
    refine ⟨fun x => ?_, ?_⟩
    · exact ge_of_tendsto' (tendsto_pi_nhds.1 hψ' x) fun t =>
        (hP.isDistribution_vecMul_pow hψ₀dist t).nonneg x
    · have h1 : Tendsto (fun t => ∑ x, u t x) atTop (𝓝 (∑ x, ψ' x)) :=
        tendsto_finsetSum _ fun x _ => tendsto_pi_nhds.1 hψ' x
      have h2 : (fun t => ∑ x, u t x) = fun _ => 1 :=
        funext fun t => (hP.isDistribution_vecMul_pow hψ₀dist t).sum_eq_one
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- `ψ'` is stationary: `u (t + 1) = u t ᵥ* P` has limits `ψ'` and `ψ'P`
  have hstat : IsStationary P ψ' := by
    have h1 : Tendsto (fun t => u (t + 1)) atTop (𝓝 ψ') := hψ'.comp (tendsto_add_atTop_nat 1)
    have h2 : (fun t => u (t + 1)) = fun t => u t ᵥ* P := by
      funext t
      rw [hu]
      simp only
      rw [pow_succ, ← vecMul_vecMul]
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 (tendsto_vecMul hψ')).symm
  -- geometric convergence from any distribution
  have hconv : ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
    intro ψ hψ
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [dist_eq_norm]
    have hd : ∑ x, (ψ - ψ') x = 0 := by
      simp only [Pi.sub_apply]
      rw [sum_sub_distrib, hψ.sum_eq_one, hψ'dist.sum_eq_one, sub_self]
    refine squeeze_zero (g := fun t : ℕ => lam ^ t * l1 (ψ - ψ')) (fun _ => norm_nonneg _)
      (fun t => ?_) ?_
    · have h1 : ψ ᵥ* P ^ t - ψ' = (ψ - ψ') ᵥ* P ^ t := by
        rw [sub_vecMul, hstat.vecMul_pow]
      rw [h1]
      exact (norm_le_l1 _).trans (l1_vecMul_pow_le hP hε hlam0 hd t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (l1 (ψ - ψ'))
  refine ⟨ψ', hψ'dist, hstat, fun φ hφ hφs => ?_, hconv⟩
  -- uniqueness: a stationary `φ` is its own orbit, which converges to `ψ'`
  have h1 : Tendsto (fun t : ℕ => φ ᵥ* P ^ t) atTop (𝓝 ψ') := hconv φ hφ
  have h2 : (fun t : ℕ => φ ᵥ* P ^ t) = fun _ => φ := funext fun t => hφs.vecMul_pow t
  rw [h2] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm

omit [DecidableEq X] in
/-- The map `ψ ↦ ψP` as a self-map of the distributions `D(X)`. -/
def distMap {P : Matrix X X ℝ} (hP : IsMarkov P) (ψ : {ψ : X → ℝ // IsDistribution ψ}) :
    {ψ : X → ℝ // IsDistribution ψ} :=
  ⟨ψ.1 ᵥ* P, hP.isDistribution_vecMul ψ.2⟩

theorem distMap_iterate {P : Matrix X X ℝ} (hP : IsMarkov P) (ψ : {ψ : X → ℝ // IsDistribution ψ})
    (t : ℕ) : ((distMap hP)^[t] ψ).1 = ψ.1 ᵥ* P ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [iterate_succ_apply']
    change ((distMap hP)^[t] ψ).1 ᵥ* P = _
    rw [ih, vecMul_vecMul, pow_succ]

omit [DecidableEq X] in
/-- Exercise 3.1.7 (p. 89) in the vocabulary of §1.2.2: for `P ≫ 0` Markov, `ψ ↦ ψP` is a
globally stable self-map of `D(X)`. -/
theorem globallyStable_distMap [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') : GloballyStable (distMap hP) := by
  classical
  obtain ⟨ψ', hψ'dist, hstat, huniq, hconv⟩ := globallyStable_of_pos hP hpos
  refine ⟨⟨ψ', hψ'dist⟩, Subtype.ext hstat, fun v hv => Subtype.ext (huniq v.1 v.2 ?_),
    fun ψ => ?_⟩
  · exact congrArg Subtype.val hv
  · rw [tendsto_subtype_rng]
    simp only [distMap_iterate]
    exact hconv ψ.1 ψ.2

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional expectations and monotone Markov chains

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.2.1 (pp. 91–94).

`(Ph)(x) = ∑ h(x')P(x, x')` is the conditional expectation `E[h(Xₜ₊₁) | Xₜ = x]`,
(3.12)–(3.13), and `Pᵏh` the `k`-step version (3.14). Exercise 3.2.1: constants
are fixed points of `P` and `max |Ph| ≤ max |h|`. The law of iterated
expectations (3.15) is the identity `⟨ψ₀Pᵗ, Pᵏh⟩ = ⟨ψ₀Pᵗ⁺ᵏ, h⟩`.

A Markov operator on a partially ordered `X` is monotone increasing when
`x ≤ y` implies `P(x, ·) ≼_F P(y, ·)` in the stochastic dominance order of
Vol. 1, §2.2.4. Exercise 3.2.4: this holds iff `P` maps increasing functions to
increasing functions; Exercise 3.2.5: then every `Pᵗ` is monotone increasing.
Exercise 3.2.3 (the two-state matrix) is in `DayLaborer`, Exercise 3.2.2 (the
Tauchen discretisation) in `Tauchen`.
-/

open Finset Matrix Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- (3.12), p. 92: `(Ph)(x) = ∑_{x'} h(x') P(x, x')`, the conditional expectation of `h(Xₜ₊₁)`
given `Xₜ = x`, (3.13). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

/-- (3.14), p. 92: `(Pᵏh)(x) = ∑_{x'} h(x') Pᵏ(x, x')`, the conditional expectation of `h(Xₜ₊ₖ)`
given `Xₜ = x`. -/
theorem pow_mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (k : ℕ) (x : X) :
    (P ^ k *ᵥ h) x = ∑ x', h x' * (P ^ k) x x' :=
  mulVec_apply_eq (P ^ k) h x

omit [DecidableEq X] in
/-- Exercise 3.2.1 (i), p. 92: every constant function is a fixed point of `P`. -/
theorem IsMarkov.isFixedPt_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    IsFixedPt (fun h => P *ᵥ h) (fun _ => c) :=
  hP.mulVec_const c

omit [DecidableEq X] in
/-- Exercise 3.2.1 (ii), p. 92: `maxₓ |Ph(x)| ≤ maxₓ |h(x)|`. -/
theorem IsMarkov.sup'_abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ)
    (hX : (univ : Finset X).Nonempty) :
    univ.sup' hX (fun x => |(P *ᵥ h) x|) ≤ univ.sup' hX fun x => |h x| := by
  refine Finset.sup'_le hX _ fun x _ => ?_
  rw [mulVec_apply_eq]
  calc |∑ x', h x' * P x x'| ≤ ∑ x', |h x' * P x x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', |h x'| * P x x' := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', (univ.sup' hX fun x => |h x|) * P x x' :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
          (Finset.le_sup' (fun x => |h x|) (mem_univ x')) (hP.nonneg x x')
    _ = univ.sup' hX fun x => |h x| := by rw [← mul_sum, hP.rowsum, mul_one]

omit [DecidableEq X] in
/-- Exercise 3.2.1 (ii) in the supremum norm: `‖Ph‖ ≤ ‖h‖`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  have := hP.norm_mulVec_sub_le h 0
  simpa using this

/-- The law of iterated expectations (3.15), p. 92: `E[E_t[h(X_{t+k})]] = E[h(X_{t+k})]`, as
`∑ₓ (Pᵏh)(x)(ψ₀Pᵗ)(x) = ⟨ψ₀Pᵗ⁺ᵏ, h⟩`. -/
theorem iterated_expectations (P : Matrix X X ℝ) (ψ₀ h : X → ℝ) (t k : ℕ) :
    ∑ x, (P ^ k *ᵥ h) x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ (t + k)) ⬝ᵥ h := by
  have h1 : ∑ x, (P ^ k *ᵥ h) x * (ψ₀ ᵥ* P ^ t) x = (ψ₀ ᵥ* P ^ t) ⬝ᵥ (P ^ k *ᵥ h) := by
    simp only [dotProduct, mul_comm]
  rw [h1, dotProduct_mulVec, vecMul_vecMul, ← pow_add]

/-! ### Monotone Markov chains (§3.2.1.3) -/

variable [PartialOrder X]

/-- First-order stochastic dominance (Vol. 1, (2.9)): `φ ≼_F ψ` iff `∑ u φ ≤ ∑ u ψ` for every
increasing `u`. -/
def FOSD (φ ψ : X → ℝ) : Prop := ∀ u : X → ℝ, Monotone u → ∑ x, u x * φ x ≤ ∑ x, u x * ψ x

/-- A monotone increasing Markov operator (p. 93): `x ≤ y` implies `P(x, ·) ≼_F P(y, ·)`. -/
def MonotoneIncreasing (P : Matrix X X ℝ) : Prop := ∀ x y, x ≤ y → FOSD (P x) (P y)

omit [DecidableEq X] in
/-- Exercise 3.2.4 (p. 94): `P` is monotone increasing iff `P` maps increasing functions to
increasing functions, `h ∈ iℝ^X ⇒ Ph ∈ iℝ^X`. -/
theorem monotoneIncreasing_iff (P : Matrix X X ℝ) :
    MonotoneIncreasing P ↔ ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h) := by
  constructor
  · intro hP h hh x y hxy
    rw [mulVec_apply_eq, mulVec_apply_eq]
    exact hP x y hxy h hh
  · intro hP x y hxy u hu
    have := hP u hu hxy
    rwa [mulVec_apply_eq, mulVec_apply_eq] at this

/-- Exercise 3.2.5 (p. 94): if `P` is monotone increasing then so is `Pᵗ` for every `t`. -/
theorem MonotoneIncreasing.pow {P : Matrix X X ℝ} (hP : MonotoneIncreasing P)
    (t : ℕ) : MonotoneIncreasing (P ^ t) := by
  rw [monotoneIncreasing_iff] at hP ⊢
  intro h hh
  induction t with
  | zero => simpa using hh
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact hP _ ih

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The day labourer

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.2.1 (pp. 88–89).

A worker is unemployed (`1`) or employed (`2`); he is hired with probability
`α` and fired with probability `β`, (3.8). Exercise 3.1.6: the unique
stationary distribution is `ψ* = (β, α)/(α + β)`, (3.9). The book then
asserts `ψPᵗ → ψ*` for every distribution `ψ`; here this is proved in closed
form, `(ψPᵗ)(1) − ψ*(1) = (1 − α − β)ᵗ (ψ(1) − ψ*(1))`, with `|1 − α − β| < 1`.
Exercise 3.1.7's general statement for everywhere-positive `P` is proved in
`PositiveChains` and applied here. Exercise 3.2.3: the two-state matrix is
monotone increasing iff `α + β ≤ 1`. Exercises 3.1.5, 3.1.8 and 3.1.9 are
computational.
-/

open Finset Matrix Filter Topology

namespace SargentStachurski.MarkovDynamics

/-- The day labourer's hiring rate `α` and firing rate `β`, both in `(0, 1)`. -/
structure DayLaborer where
  α : ℝ
  β : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  β_lt_one : β < 1

namespace DayLaborer

variable (m : DayLaborer)

/-- The transition matrix (3.8), with state `0` unemployed and `1` employed. -/
noncomputable def P : Matrix (Fin 2) (Fin 2) ℝ := !![1 - m.α, m.α; m.β, 1 - m.β]

theorem isMarkov_P : IsMarkov m.P where
  nonneg i j := by
    have := m.α_pos; have := m.α_lt_one; have := m.β_pos; have := m.β_lt_one
    fin_cases i <;> fin_cases j <;> simp [P] <;> linarith
  rowsum i := by fin_cases i <;> simp [P, Fin.sum_univ_two]

theorem α_add_β_pos : 0 < m.α + m.β := by linarith [m.α_pos, m.β_pos]

/-- The stationary distribution (3.9): `ψ* = (β, α)/(α + β)`. -/
noncomputable def ψstar : Fin 2 → ℝ := ![m.β / (m.α + m.β), m.α / (m.α + m.β)]

theorem isDistribution_ψstar : IsDistribution m.ψstar where
  nonneg i := by
    fin_cases i
    · exact div_nonneg m.β_pos.le m.α_add_β_pos.le
    · exact div_nonneg m.α_pos.le m.α_add_β_pos.le
  sum_eq_one := by
    have := m.α_add_β_pos.ne'
    simp [ψstar, Fin.sum_univ_two]
    field_simp
    ring

/-- Exercise 3.1.6 (p. 88): `ψ*` is stationary. -/
theorem isStationary_ψstar : IsStationary m.P m.ψstar := by
  have hne := m.α_add_β_pos.ne'
  funext j
  fin_cases j <;> simp [P, ψstar, vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Exercise 3.1.6 (p. 88): `ψ*` is the only stationary distribution. -/
theorem eq_ψstar_of_isStationary {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) (hs : IsStationary m.P ψ) :
    ψ = m.ψstar := by
  have hne := m.α_add_β_pos.ne'
  have hsum : ψ 0 + ψ 1 = 1 := by simpa [Fin.sum_univ_two] using hψ.sum_eq_one
  -- `(1 − α)ψ₀ + βψ₁ = ψ₀`, i.e. `αψ₀ = βψ₁`
  have h0 : ψ 0 * (1 - m.α) + ψ 1 * m.β = ψ 0 := by
    have := congrFun hs 0
    simpa [P, vecMul, dotProduct, Fin.sum_univ_two] using this
  have h1 : ψ 1 = 1 - ψ 0 := by linarith
  rw [h1] at h0
  have hψ0' : ψ 0 * (m.α + m.β) = m.β := by linear_combination -h0
  funext j
  fin_cases j
  · change ψ 0 = m.β / (m.α + m.β)
    rw [eq_div_iff hne]
    exact hψ0'
  · change ψ 1 = m.α / (m.α + m.β)
    rw [eq_div_iff hne, h1]
    linear_combination -hψ0'

/-- The one-step recursion for the unemployment probability:
`(ψP)(1) − β/(α + β) = (1 − α − β)(ψ(1) − β/(α + β))` for a distribution `ψ`. -/
theorem vecMul_zero_sub (ψ : Fin 2 → ℝ) (hsum : ψ 0 + ψ 1 = 1) :
    (ψ ᵥ* m.P) 0 - m.β / (m.α + m.β) = (1 - m.α - m.β) * (ψ 0 - m.β / (m.α + m.β)) := by
  have hne := m.α_add_β_pos.ne'
  have h1 : ψ 1 = 1 - ψ 0 := by linarith
  simp only [P, vecMul, dotProduct, Fin.sum_univ_two, h1]
  simp
  field_simp
  ring

/-- The `t`-step recursion: `(ψPᵗ)(1) − ψ*(1) = (1 − α − β)ᵗ (ψ(1) − ψ*(1))`. -/
theorem vecMul_pow_zero_sub {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) (t : ℕ) :
    (ψ ᵥ* m.P ^ t) 0 - m.β / (m.α + m.β) = (1 - m.α - m.β) ^ t * (ψ 0 - m.β / (m.α + m.β)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsum : (ψ ᵥ* m.P ^ t) 0 + (ψ ᵥ* m.P ^ t) 1 = 1 := by
      simpa [Fin.sum_univ_two] using (m.isMarkov_P.isDistribution_vecMul_pow hψ t).sum_eq_one
    rw [pow_succ, ← vecMul_vecMul, m.vecMul_zero_sub _ hsum, ih]
    ring

/-- `|1 − α − β| < 1`. -/
theorem abs_one_sub_lt_one : |1 - m.α - m.β| < 1 := by
  rw [abs_lt]
  constructor <;> linarith [m.α_pos, m.α_lt_one, m.β_pos, m.β_lt_one]

/-- The claim of p. 88: `ψPᵗ → ψ*` for every distribution `ψ`, so `ψ ↦ ψP` is globally stable
on `D(X)`. -/
theorem tendsto_vecMul_pow {ψ : Fin 2 → ℝ} (hψ : IsDistribution ψ) :
    Tendsto (fun t : ℕ => ψ ᵥ* m.P ^ t) atTop (𝓝 m.ψstar) := by
  have hne := m.α_add_β_pos.ne'
  have hgeom : Tendsto (fun t : ℕ => (1 - m.α - m.β) ^ t * (ψ 0 - m.β / (m.α + m.β))) atTop
      (𝓝 0) := by
    have habs := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - m.α - m.β))
      m.abs_one_sub_lt_one
    simp only [← abs_pow] at habs
    have hpow : Tendsto (fun t : ℕ => (1 - m.α - m.β) ^ t) atTop (𝓝 0) :=
      tendsto_zero_iff_abs_tendsto_zero _ |>.2 habs
    simpa using hpow.mul_const (ψ 0 - m.β / (m.α + m.β))
  have h0 : Tendsto (fun t : ℕ => (ψ ᵥ* m.P ^ t) 0) atTop (𝓝 (m.β / (m.α + m.β))) := by
    have := hgeom
    simp_rw [← m.vecMul_pow_zero_sub hψ] at this
    have h := this.add_const (m.β / (m.α + m.β))
    simpa using h
  have hdist : ∀ t, (ψ ᵥ* m.P ^ t) 0 + (ψ ᵥ* m.P ^ t) 1 = 1 := fun t => by
    simpa [Fin.sum_univ_two] using (m.isMarkov_P.isDistribution_vecMul_pow hψ t).sum_eq_one
  have h1 : Tendsto (fun t : ℕ => (ψ ᵥ* m.P ^ t) 1) atTop (𝓝 (m.α / (m.α + m.β))) := by
    have : (fun t : ℕ => (ψ ᵥ* m.P ^ t) 1) = fun t => 1 - (ψ ᵥ* m.P ^ t) 0 := by
      funext t
      linarith [hdist t]
    rw [this]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have heq : 1 - m.β / (m.α + m.β) = m.α / (m.α + m.β) := by
      field_simp
      ring
    rwa [heq] at h
  rw [tendsto_pi_nhds]
  intro j
  fin_cases j
  · simpa [ψstar] using h0
  · simpa [ψstar] using h1

/-- Every entry of `P` is positive. -/
theorem P_pos (i j : Fin 2) : 0 < m.P i j := by
  have := m.α_pos; have := m.α_lt_one; have := m.β_pos; have := m.β_lt_one
  fin_cases i <;> fin_cases j <;> simp [P] <;> linarith

/-- Exercise 3.1.7 (p. 89), first part: the day labourer's `ψ ↦ ψP` is globally stable on `D(X)`,
by the general result for `P ≫ 0`. -/
theorem globallyStable_distMap : GloballyStable (distMap m.isMarkov_P) :=
  MarkovDynamics.globallyStable_distMap m.isMarkov_P m.P_pos

end DayLaborer

/-- Exercise 3.2.3 (p. 93): the two-state matrix `P_w = [[1 − α, α], [β, 1 − β]]` is monotone
increasing iff `α + β ≤ 1`; the bounds `α, β ∈ [0, 1]` are not needed for this equivalence. -/
theorem monotoneIncreasing_two_state_iff (α β : ℝ) :
    MonotoneIncreasing !![1 - α, α; β, 1 - β] ↔ α + β ≤ 1 := by
  constructor
  · intro h
    have hu : Monotone fun i : Fin 2 => ((i : ℕ) : ℝ) := fun a b hab => Nat.cast_le.2 hab
    have := h 0 1 (by decide) _ hu
    simp [Fin.sum_univ_two] at this
    linarith
  · intro h x y hxy u hu
    have h01 : u 0 ≤ u 1 := hu (by decide)
    fin_cases x <;> fin_cases y
    · exact le_rfl
    · simp [Fin.sum_univ_two]
      nlinarith
    · exact absurd hxy (by decide)
    · exact le_rfl

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tauchen's discretisation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.1.3 (pp. 89–91)
and Exercise 3.2.2 (p. 93).

The AR(1) process `Xₜ₊₁ = ρXₜ + νεₜ₊₁` is approximated on an equispaced grid
`x₁ < ⋯ < xₙ` with step `s` by the matrix whose rows are the probabilities
that `ρxᵢ + νε` lands in the cell around `xⱼ`: `P(xᵢ, x₁) = F(x₁ − ρxᵢ + s/2)`,
`P(xᵢ, xₙ) = 1 − F(xₙ − ρxᵢ − s/2)` and
`P(xᵢ, xⱼ) = F(xⱼ − ρxᵢ + s/2) − F(xⱼ − ρxᵢ − s/2)` otherwise, where `F` is the
CDF of `N(0, ν²)`. Only three properties of `F` are used: it is increasing
and takes values in `[0, 1]`, so `F` is kept abstract. Exercise 3.1.12: each
row sums to one, by telescoping. Exercise 3.2.2: `P` is monotone increasing
when `ρ ≥ 0`, because the counter-CDF of row `i`, `∑_{l ≥ j} P(xᵢ, xₗ) =
1 − F(xⱼ − ρxᵢ − s/2)`, is increasing in `xᵢ`, and dominance of counter-CDFs
on a totally ordered set gives stochastic dominance (Vol. 1, Lemma 2.2.5 (ii),
re-proved here by Abel summation).

Exercises 3.1.10–3.1.11 concern the Gaussian stationary distribution and
conditional probabilities of the continuous process and are not formalised.
-/

open Finset Matrix

namespace SargentStachurski.MarkovDynamics

/-- A Tauchen grid: `n ≥ 2` points `xⱼ = x₁ + j·s`, `j = 0, …, n − 1`, autocorrelation `ρ`, and a
distribution function `F` that is increasing with values in `[0, 1]`. -/
structure Tauchen where
  n : ℕ
  two_le_n : 2 ≤ n
  ρ : ℝ
  x₁ : ℝ
  s : ℝ
  s_pos : 0 < s
  F : ℝ → ℝ
  F_mono : Monotone F
  F_nonneg : ∀ t, 0 ≤ F t
  F_le_one : ∀ t, F t ≤ 1

namespace Tauchen

variable (m : Tauchen)

/-- The grid point with index `j` (zero-based): `xⱼ = x₁ + j·s`. -/
noncomputable def x (j : ℕ) : ℝ := m.x₁ + j * m.s

theorem x_mono {j k : ℕ} (hjk : j ≤ k) : m.x j ≤ m.x k := by
  unfold x
  have : (j : ℝ) ≤ k := Nat.cast_le.2 hjk
  nlinarith [m.s_pos]

/-- The counter-CDF of row `i` at `j`: the probability of landing at a grid point with index at
least `j`: `1` for `j = 0`, `1 − F(xⱼ − ρxᵢ − s/2)` for `0 < j < n`, and `0` for `j ≥ n`. -/
noncomputable def G (i j : ℕ) : ℝ :=
  if j = 0 then 1 else if j < m.n then 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) else 0

/-- Tauchen's transition probabilities (p. 91), rules (i)–(iii), on zero-based indices. -/
noncomputable def Pnat (i j : ℕ) : ℝ :=
  if j = 0 then m.F (m.x 0 - m.ρ * m.x i + m.s / 2)
  else if j = m.n - 1 then 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2)
  else m.F (m.x j - m.ρ * m.x i + m.s / 2) - m.F (m.x j - m.ρ * m.x i - m.s / 2)

/-- The transition matrix on the state space `Fin n`. -/
noncomputable def P : Matrix (Fin m.n) (Fin m.n) ℝ := Matrix.of fun i j => m.Pnat i j

theorem P_apply (i j : Fin m.n) : m.P i j = m.Pnat i j := rfl

/-- Rule (i), p. 91. -/
theorem Pnat_zero (i : ℕ) : m.Pnat i 0 = m.F (m.x 0 - m.ρ * m.x i + m.s / 2) := by
  simp [Pnat]

/-- Rule (ii), p. 91. -/
theorem Pnat_last (i : ℕ) :
    m.Pnat i (m.n - 1) = 1 - m.F (m.x (m.n - 1) - m.ρ * m.x i - m.s / 2) := by
  have h := m.two_le_n
  have : m.n - 1 ≠ 0 := by omega
  simp [Pnat, this]

/-- Rule (iii), p. 91. -/
theorem Pnat_mid (i j : ℕ) (hj0 : j ≠ 0) (hjn : j ≠ m.n - 1) :
    m.Pnat i j = m.F (m.x j - m.ρ * m.x i + m.s / 2) - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by
  simp [Pnat, hj0, hjn]

-- The counter-CDF at the two ends.
theorem G_zero (i : ℕ) : m.G i 0 = 1 := by simp [G]

theorem G_n (i : ℕ) : m.G i m.n = 0 := by
  have h := m.two_le_n
  have h1 : m.n ≠ 0 := by omega
  simp [G, h1]

/-- The cell probabilities are differences of the counter-CDF: `P(xᵢ, xⱼ) = G(i, j) − G(i, j+1)`
for `j < n`. -/
theorem Pnat_eq_G_sub (i j : ℕ) (hj : j < m.n) : m.Pnat i j = m.G i j - m.G i (j + 1) := by
  have h2 := m.two_le_n
  have hx : m.x (j + 1) - m.ρ * m.x i - m.s / 2 = m.x j - m.ρ * m.x i + m.s / 2 := by
    unfold x
    push_cast
    ring
  by_cases hj0 : j = 0
  · subst hj0
    have h1 : (1 : ℕ) < m.n := by omega
    have hG1 : m.G i 1 = 1 - m.F (m.x 1 - m.ρ * m.x i - m.s / 2) := by simp [G, h1]
    rw [zero_add] at hx
    rw [Pnat_zero, zero_add, G_zero, hG1, sub_sub_cancel, hx]
  · by_cases hjn : j = m.n - 1
    · subst hjn
      have hG : m.G i (m.n - 1) = 1 - m.F (m.x (m.n - 1) - m.ρ * m.x i - m.s / 2) := by
        simp [G, hj0, hj]
      rw [Pnat_last, hG, show m.n - 1 + 1 = m.n by omega, G_n, sub_zero]
    · have hj1 : j + 1 < m.n := by omega
      have hGj : m.G i j = 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by simp [G, hj0, hj]
      have hGj1 : m.G i (j + 1) = 1 - m.F (m.x (j + 1) - m.ρ * m.x i - m.s / 2) := by
        simp [G, hj1]
      rw [Pnat_mid m i j hj0 hjn, hGj, hGj1, hx]
      ring

/-- `G(i, ·)` is nonincreasing. -/
theorem G_antitone (i : ℕ) {j k : ℕ} (hjk : j ≤ k) : m.G i k ≤ m.G i j := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hj : j = 0 := by omega
    subst hj
    subst hk
    exact le_rfl
  by_cases hkn : k < m.n
  · have hGk : m.G i k = 1 - m.F (m.x k - m.ρ * m.x i - m.s / 2) := by simp [G, hk.ne', hkn]
    rw [hGk]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [G_zero]
      linarith [m.F_nonneg (m.x k - m.ρ * m.x i - m.s / 2)]
    · have hjn : j < m.n := lt_of_le_of_lt hjk hkn
      have hGj : m.G i j = 1 - m.F (m.x j - m.ρ * m.x i - m.s / 2) := by simp [G, hj.ne', hjn]
      rw [hGj]
      exact sub_le_sub_left (m.F_mono (by linarith [m.x_mono hjk])) 1
  · have hGk : m.G i k = 0 := by simp [G, hk.ne', hkn]
    rw [hGk]
    unfold G
    split_ifs
    · exact zero_le_one
    · linarith [m.F_le_one (m.x j - m.ρ * m.x i - m.s / 2)]
    · exact le_rfl

/-- Each entry is nonnegative. -/
theorem Pnat_nonneg (i j : ℕ) (hj : j < m.n) : 0 ≤ m.Pnat i j := by
  rw [Pnat_eq_G_sub m i j hj]
  exact sub_nonneg.2 (m.G_antitone i (Nat.le_succ j))

/-- The tail sums telescope: `∑_{j ≤ l < n} P(xᵢ, xₗ) = G(i, j)` for `j ≤ n`. -/
theorem sum_Ico_Pnat (i j : ℕ) (hj : j ≤ m.n) : ∑ l ∈ Ico j m.n, m.Pnat i l = m.G i j := by
  rw [sum_Ico_eq_sum_range]
  have : ∀ k ∈ range (m.n - j), m.Pnat i (j + k) = m.G i (j + k) - m.G i (j + (k + 1)) := by
    intro k hk
    rw [mem_range] at hk
    rw [← add_assoc]
    exact m.Pnat_eq_G_sub i (j + k) (by omega)
  rw [sum_congr rfl this, sum_range_sub' (fun k => m.G i (j + k))]
  simp only [add_zero]
  rw [show j + (m.n - j) = m.n by omega, G_n, sub_zero]

/-- Exercise 3.1.12 (p. 91): every row of the Tauchen matrix sums to one. -/
theorem sum_Pnat (i : ℕ) : ∑ j ∈ range m.n, m.Pnat i j = 1 := by
  rw [range_eq_Ico, sum_Ico_Pnat m i 0 (Nat.zero_le _), G_zero]

/-- The Tauchen matrix is a Markov matrix. -/
theorem isMarkov_P : IsMarkov m.P where
  nonneg i j := m.Pnat_nonneg i j j.2
  rowsum i := by
    simp only [P_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => m.Pnat i j) m.n]
    exact m.sum_Pnat i

/-- The tail sums of row `i` from index `j`, as a sum over the state space. -/
theorem sum_filter_P (i j : Fin m.n) :
    ∑ l ∈ univ.filter (fun l : Fin m.n => j ≤ l), m.P i l = m.G i j := by
  rw [sum_filter]
  have h1 : ∑ l : Fin m.n, (if j ≤ l then m.P i l else 0) =
      ∑ l ∈ range m.n, (if (j : ℕ) ≤ l then m.Pnat i l else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun l => if (j : ℕ) ≤ l then m.Pnat i l else 0) m.n]
    refine sum_congr rfl fun l _ => ?_
    by_cases h : j ≤ l
    · have h' : (j : ℕ) ≤ l := Fin.le_def.1 h
      simp [h, h', P_apply]
    · have h' : ¬ (j : ℕ) ≤ l := fun hh => h (Fin.le_def.2 hh)
      simp [h, h']
  rw [h1, ← sum_filter]
  have h2 : (range m.n).filter (fun l => (j : ℕ) ≤ l) = Ico (j : ℕ) m.n := by
    ext l
    simp only [mem_filter, mem_range, mem_Ico]
    exact and_comm
  rw [h2, sum_Ico_Pnat m i j j.2.le]

/-! ### Dominance from counter-CDFs on `Fin n` (Vol. 1, Lemma 2.2.5 (ii)) -/

/-- Abel summation on `Fin n`: if `u` is increasing and nonnegative and every tail sum of `d` is
nonnegative, then `∑ u d ≥ 0`. -/
theorem sum_mul_nonneg_of_tails_nonneg : ∀ (n : ℕ) (u d : Fin n → ℝ), Monotone u →
    (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ ∑ j ∈ univ.filter (fun j => i ≤ j), d j) →
    0 ≤ ∑ i, u i * d i := by
  intro n
  induction n with
  | zero => intro u d _ _ _; simp
  | succ n ih =>
    intro u d hu hu0 htail
    have hD0 : ∑ j, d j = ∑ j ∈ univ.filter (fun j => (0 : Fin (n + 1)) ≤ j), d j := by
      congr 1
      ext j
      simp
    have hsplit : ∑ i, u i * d i =
        u 0 * ∑ j, d j + ∑ i : Fin n, (u i.succ - u 0) * d i.succ := by
      simp only [Fin.sum_univ_succ, sub_mul, sum_sub_distrib, mul_sum, mul_add]
      ring
    rw [hsplit]
    refine add_nonneg (mul_nonneg (hu0 0) (hD0 ▸ htail 0)) ?_
    refine ih (fun i => u i.succ - u 0) (fun i => d i.succ) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu (Fin.succ_le_succ_iff.2 hij)) _
    · intro i
      exact sub_nonneg.2 (hu (Fin.zero_le _))
    · intro i
      have := htail i.succ
      have hreindex : ∑ j ∈ univ.filter (fun j : Fin (n + 1) => i.succ ≤ j), d j =
          ∑ j ∈ univ.filter (fun j : Fin n => i ≤ j), d j.succ := by
        refine (Finset.sum_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_).symm
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj ⊢
          exact Fin.succ_le_succ_iff.2 hj
        · intro a _ b _ hab
          exact Fin.succ_injective _ hab
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj
          refine ⟨j.pred (Fin.pos_iff_ne_zero.1 (lt_of_lt_of_le (Fin.succ_pos i) hj)), ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and]
            rw [← Fin.succ_le_succ_iff, Fin.succ_pred]
            exact hj
          · exact Fin.succ_pred _ _
        · intro j _
          rfl
      rwa [hreindex] at this

/-- Vol. 1, Lemma 2.2.5 (ii) on `Fin n`: if two distributions have ordered tail sums,
`∑_{l ≥ j} φ(l) ≤ ∑_{l ≥ j} ψ(l)` for all `j`, then `φ ≼_F ψ`. -/
theorem fosd_of_tails_le {n : ℕ} {φ ψ : Fin n → ℝ} (hφ : ∑ l, φ l = 1) (hψ : ∑ l, ψ l = 1)
    (h : ∀ j, ∑ l ∈ univ.filter (fun l => j ≤ l), φ l ≤ ∑ l ∈ univ.filter (fun l => j ≤ l), ψ l) :
    FOSD φ ψ := by
  intro u hu
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hsum : ∑ x, (ψ x - φ x) = 0 := by rw [sum_sub_distrib, hψ, hφ, sub_self]
  set m : Fin n := ⟨0, hn⟩ with hm
  have hmin : ∀ x, m ≤ x := fun x => Fin.mk_le_of_le_val (Nat.zero_le _)
  have key : 0 ≤ ∑ x, (u x - u m) * (ψ x - φ x) := by
    refine sum_mul_nonneg_of_tails_nonneg n (fun x => u x - u m) (fun x => ψ x - φ x) ?_ ?_ ?_
    · intro i j hij
      exact sub_le_sub_right (hu hij) _
    · intro i
      exact sub_nonneg.2 (hu (hmin i))
    · intro i
      rw [sum_sub_distrib]
      exact sub_nonneg.2 (h i)
  have hexpand : ∑ x, (u x - u m) * (ψ x - φ x) = ∑ x, u x * ψ x - ∑ x, u x * φ x := by
    have h1 : ∑ x, (u x - u m) * (ψ x - φ x) =
        ∑ x, u x * (ψ x - φ x) - u m * ∑ x, (ψ x - φ x) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [h1, hsum, mul_zero, sub_zero, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  linarith

/-- Exercise 3.2.2 (p. 93): the Tauchen matrix is monotone increasing when `ρ ≥ 0`: a higher
current state shifts every tail probability `1 − F(xⱼ − ρxᵢ − s/2)` up. -/
theorem monotoneIncreasing_P (hρ : 0 ≤ m.ρ) : MonotoneIncreasing m.P := by
  intro i k hik
  have hM := m.isMarkov_P
  refine fosd_of_tails_le (hM.rowsum i) (hM.rowsum k) fun j => ?_
  rw [sum_filter_P, sum_filter_P]
  unfold G
  split_ifs with h0 hn
  · exact le_rfl
  · have hx : m.x j - m.ρ * m.x k - m.s / 2 ≤ m.x j - m.ρ * m.x i - m.s / 2 := by
      have := m.x_mono (Fin.le_def.1 hik)
      nlinarith
    exact sub_le_sub_left (m.F_mono hx) 1
  · exact le_rfl

end Tauchen

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Geometric sums

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.2.2 (pp. 94–97).

The lifetime value `v(x) = E_x ∑ βᵗ h(Xₜ)`, (3.16), is `∑ βᵗ Pᵗ h` by (3.14),
(3.18). Lemma 3.2.1: for `β < 1`, `I − βP` is invertible and
`v = ∑ (βP)ᵗ h = (I − βP)⁻¹ h`, (3.17). The book applies the Neumann series lemma
to `βP` with `ρ(βP) = β`; here the series is summed directly in the
supremum norm, where `‖(βP)ᵗh‖ ≤ βᵗ‖h‖`, and `I − βP` is invertible because
`u = βPu` forces `‖u‖ ≤ β‖u‖`.

Applications: the valuation of a firm (3.19) with `β = 1/(1 + r)`, and the
value of a consumption stream (3.20)–(3.21). Exercise 3.2.6: `v` is increasing
when `π` is increasing and `P` monotone increasing, since each `Pᵗπ` is
increasing and the increasing functions are closed. Exercise 3.2.8: with CRRA
utility `u(c) = c^{1−γ}/(1 − γ)`, `c(x) = eˣ` and a Tauchen chain with
`ρ ≥ 0`, the value is increasing in the state.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDynamics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `‖(βP)ᵗ h‖ ≤ βᵗ ‖h‖` for a Markov matrix `P` and `β ≥ 0`. -/
theorem IsMarkov.norm_smul_pow_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ : 0 ≤ β)
    (h : X → ℝ) (t : ℕ) : ‖(β • P) ^ t *ᵥ h‖ ≤ β ^ t * ‖h‖ := by
  rw [smul_pow, smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ t)]
  exact mul_le_mul_of_nonneg_left ((hP.pow t).norm_mulVec_le h) (pow_nonneg hβ t)

/-- (3.18): the series `∑ₜ (βP)ᵗ h` converges in `ℝ^X`. -/
theorem IsMarkov.summable_smul_pow_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) : Summable fun t : ℕ => (β • P) ^ t *ᵥ h :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right ‖h‖)
    (hP.norm_smul_pow_mulVec_le hβ0 h)

/-- The lifetime value (3.16), computed by (3.18): `v = ∑ₜ βᵗ Pᵗ h`. -/
noncomputable def lifetimeValue (P : Matrix X X ℝ) (β : ℝ) (h : X → ℝ) : X → ℝ :=
  ∑' t : ℕ, (β • P) ^ t *ᵥ h

theorem lifetimeValue_eq_tsum_smul (P : Matrix X X ℝ) (β : ℝ) (h : X → ℝ) :
    lifetimeValue P β h = ∑' t : ℕ, β ^ t • (P ^ t *ᵥ h) := by
  unfold lifetimeValue
  refine tsum_congr fun t => ?_
  rw [smul_pow, smul_mulVec]

/-- `(I − βP) ∑ₜ (βP)ᵗ h = h`: the series telescopes. -/
theorem IsMarkov.one_sub_smul_mulVec_lifetimeValue {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (h : X → ℝ) :
    (1 - β • P) *ᵥ lifetimeValue P β h = h := by
  have hs := hP.summable_smul_pow_mulVec hβ0 hβ1 h
  have hs' : Summable fun t : ℕ => (β • P) ^ (t + 1) *ᵥ h :=
    (summable_nat_add_iff 1).2 hs
  -- the matrix acts continuously and linearly, so it passes through the sum
  let L := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (1 - β • P))
  have hL : ∀ u, L u = (1 - β • P) *ᵥ u := fun u => rfl
  unfold lifetimeValue
  rw [← hL, L.map_tsum hs]
  simp only [hL, sub_mulVec, one_mulVec]
  have hterm : ∀ t : ℕ, (β • P) ^ t *ᵥ h - (β • P) *ᵥ ((β • P) ^ t *ᵥ h) =
      (β • P) ^ t *ᵥ h - (β • P) ^ (t + 1) *ᵥ h := by
    intro t
    rw [mulVec_mulVec, ← pow_succ']
  simp only [hterm]
  rw [hs.tsum_sub hs', hs.tsum_eq_zero_add]
  simp

/-- `I − βP` is invertible for `β ∈ [0, 1)`: `u = βPu` forces `‖u‖ ≤ β‖u‖`, so `u = 0`. -/
theorem IsMarkov.isUnit_one_sub_smul {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : IsUnit (1 - β • P) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have hd : (1 - β • P) *ᵥ (u - v) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.2 huv
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hd
  have hnorm : ‖u - v‖ ≤ β * ‖u - v‖ := by
    calc ‖u - v‖ = ‖(β • P) *ᵥ (u - v)‖ := by rw [← hd]
      _ = β * ‖P *ᵥ (u - v)‖ := by
          rw [smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      _ ≤ β * ‖u - v‖ := mul_le_mul_of_nonneg_left (hP.norm_mulVec_le _) hβ0
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this (norm_nonneg _)))

/-- **Lemma 3.2.1** (p. 94), (3.17): if `β < 1` then `I − βP` is invertible and
`v = ∑ₜ (βP)ᵗ h = (I − βP)⁻¹ h`. -/
theorem IsMarkov.lifetimeValue_eq_inv {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) :
    IsUnit (1 - β • P) ∧ lifetimeValue P β h = (1 - β • P)⁻¹ *ᵥ h := by
  have hunit := hP.isUnit_one_sub_smul hβ0 hβ1
  refine ⟨hunit, ?_⟩
  have hv := hP.one_sub_smul_mulVec_lifetimeValue hβ0 hβ1 h
  calc lifetimeValue P β h = (1 - β • P)⁻¹ *ᵥ ((1 - β • P) *ᵥ lifetimeValue P β h) := by
        rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
          one_mulVec]
    _ = (1 - β • P)⁻¹ *ᵥ h := by rw [hv]

/-- The recursive form `v = h + βPv`, the step behind (3.17). -/
theorem IsMarkov.lifetimeValue_eq_add {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (h : X → ℝ) :
    lifetimeValue P β h = h + β • (P *ᵥ lifetimeValue P β h) := by
  have := hP.one_sub_smul_mulVec_lifetimeValue hβ0 hβ1 h
  rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add] at this
  exact this

/-! ### Valuation of firms (§3.2.2.2) -/

/-- The firm's discount factor `β = 1/(1 + r)` lies in `(0, 1)` for `r > 0` (p. 95). -/
theorem firm_discount_mem {r : ℝ} (hr : 0 < r) : 0 < 1 / (1 + r) ∧ 1 / (1 + r) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- The value of the firm (3.19), p. 95: `v = ∑ₜ βᵗ Pᵗ π = (I − βP)⁻¹ π` with `β = 1/(1 + r)`. -/
theorem IsMarkov.firm_value {P : Matrix X X ℝ} (hP : IsMarkov P) {r : ℝ} (hr : 0 < r)
    (π : X → ℝ) :
    lifetimeValue P (1 / (1 + r)) π = (1 - (1 / (1 + r)) • P)⁻¹ *ᵥ π :=
  (hP.lifetimeValue_eq_inv (firm_discount_mem hr).1.le (firm_discount_mem hr).2 π).2

/-- The increasing functions `iℝ^X` on a partially ordered set form a closed set
(Vol. 1, Ex 2.2.30). -/
theorem isClosed_monotone (Y : Type*) [Preorder Y] : IsClosed {h : Y → ℝ | Monotone h} := by
  have : {h : Y → ℝ | Monotone h} = ⋂ (p : Y) (q : Y) (_ : p ≤ q), {h : Y → ℝ | h p ≤ h q} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun hm p q hpq => hm hpq, fun hm p q hpq => hm p q hpq⟩
  rw [this]
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply p) (continuous_apply q)

/-- A finite sum of increasing functions is increasing. -/
theorem monotone_sum {Y : Type*} [Preorder Y] {ι : Type*} (s : Finset ι) {f : ι → Y → ℝ}
    (hf : ∀ i ∈ s, Monotone (f i)) : Monotone fun y => ∑ i ∈ s, f i y :=
  fun _ _ hab => sum_le_sum fun i hi => hf i hi hab

/-- Exercise 3.2.6 (p. 95): if `π` is increasing and `P` is monotone increasing, then the value
`v = ∑ βᵗ Pᵗ π` is increasing on `X`. -/
theorem IsMarkov.monotone_lifetimeValue [PartialOrder X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hmono : MonotoneIncreasing P) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π : X → ℝ}
    (hπ : Monotone π) : Monotone (lifetimeValue P β π) := by
  have hs := hP.summable_smul_pow_mulVec hβ0 hβ1 π
  have hlim := hs.hasSum.tendsto_sum_nat
  have hterm : ∀ t : ℕ, Monotone ((β • P) ^ t *ᵥ π) := by
    intro t
    rw [smul_pow, smul_mulVec]
    have := (monotoneIncreasing_iff (P ^ t)).1 (hmono.pow t) π hπ
    exact fun a b hab => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (this hab) (pow_nonneg hβ0 t)
  have hpartial : ∀ K, Monotone (∑ t ∈ range K, (β • P) ^ t *ᵥ π) := by
    intro K
    have := monotone_sum (range K) (f := fun t => (β • P) ^ t *ᵥ π) fun t _ => hterm t
    convert this using 1
    funext y
    simp [Finset.sum_apply]
  exact (isClosed_monotone X).mem_of_tendsto hlim (Eventually.of_forall hpartial)

/-! ### Valuing consumption streams (§3.2.2.3) -/

/-- The CRRA flow utility (3.22): `u(c) = c^{1−γ}/(1 − γ)`. -/
noncomputable def crra (γ c : ℝ) : ℝ := c ^ (1 - γ) / (1 - γ)

/-- The value of the consumption stream (3.21): `v = (I − βP)⁻¹ r` with `r = u ∘ c`. -/
theorem IsMarkov.consumption_value {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (u : ℝ → ℝ) (c : X → ℝ) :
    lifetimeValue P β (u ∘ c) = (1 - β • P)⁻¹ *ᵥ (u ∘ c) :=
  (hP.lifetimeValue_eq_inv hβ0 hβ1 _).2

/-- `x ↦ u(eˣ)` is increasing for CRRA utility with `γ ≠ 1`: `eˣ^{1−γ}/(1 − γ) = e^{(1−γ)x}/(1 − γ)`
and both the numerator's monotonicity and the sign of `1 − γ` flip together. -/
theorem monotone_crra_exp {γ : ℝ} (hγ : γ ≠ 1) : Monotone fun x : ℝ => crra γ (Real.exp x) := by
  intro a b hab
  change Real.exp a ^ (1 - γ) / (1 - γ) ≤ Real.exp b ^ (1 - γ) / (1 - γ)
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.rpow_def_of_pos (Real.exp_pos b),
    Real.log_exp, Real.log_exp]
  rcases lt_or_gt_of_ne hγ with h | h
  · have hpos : 0 < 1 - γ := by linarith
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hpos.le
  · have hneg : 1 - γ < 0 := by linarith
    rw [div_le_div_right_of_neg hneg]
    exact Real.exp_le_exp.2 (by nlinarith)

/-- Exercise 3.2.8 (p. 96): for the CRRA model with `c(x) = eˣ` on a Tauchen chain with `ρ ≥ 0`
and `γ ≠ 1`, the value function is increasing in the state. -/
theorem Tauchen.monotone_crra_value (m : Tauchen) (hρ : 0 ≤ m.ρ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {γ : ℝ} (hγ : γ ≠ 1) :
    Monotone (lifetimeValue m.P β fun i : Fin m.n => crra γ (Real.exp (m.x i))) :=
  m.isMarkov_P.monotone_lifetimeValue (m.monotoneIncreasing_P hρ) hβ0 hβ1
    fun _ _ hij => monotone_crra_exp hγ (m.x_mono (Fin.le_def.1 hij))

end SargentStachurski.MarkovDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search with Markov wages and with separation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §3.3 (pp. 97–104).

Wages are `P`-Markov on a finite set `W ⊂ ℝ₊`. The Bellman operator (3.23)
`Tv(w) = max{w/(1 − β), c + β ∑ v(w')P(w, w')}` is an order-preserving
self-map of `V = ℝ^W₊` and a contraction of modulus `β` in the supremum norm
(Exercise 3.3.1), so the value function `v*` is its unique fixed point in `V`
and value function iteration converges. Lemma 3.3.1: `v*` is increasing when
`P` is monotone increasing. The continuation value `h* = c + βPv*` satisfies
the recursion of Exercise 3.3.3 and is the unique fixed point in `V` of the
operator `Q` of (3.24), itself an order-preserving `β`-contraction
(Exercise 3.3.4); the optimal policy is `1{w/(1 − β) ≥ h*(w)}`.

With separation at rate `α`, (3.25)–(3.26) reduce to (3.27)–(3.28); the
operator of (3.28) is the upper envelope of two contractions of moduli
`αβ/(1 − β(1 − α))` and `β` (Lemma 2.2.3), so `v_u*` exists uniquely in `V`,
iteration converges, and the pair `(v_u*, v_e*)` is the unique solution of
(3.25)–(3.26) (Exercise 3.3.5). Exercises 3.3.2 and 3.3.6 are discussion and
computation.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.MarkovDynamics

/-- The job search model with Markov wages (§3.3.1): a finite set `W` of offers with nonnegative
wages, a Markov matrix `P`, compensation `c > 0` and discount factor `β ∈ (0, 1)`. -/
structure MarkovJobSearch (W : Type*) [Fintype W] where
  wage : W → ℝ
  wage_nonneg : ∀ w, 0 ≤ wage w
  P : Matrix W W ℝ
  P_markov : IsMarkov P
  c : ℝ
  c_pos : 0 < c
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace MarkovJobSearch

variable {W : Type*} [Fintype W] (m : MarkovJobSearch W)

/-- The candidate value functions `V = ℝ^W₊`. -/
def V : Set (W → ℝ) := {v | ∀ w, 0 ≤ v w}

omit [Fintype W] in
theorem isClosed_V : IsClosed (V : Set (W → ℝ)) := by
  have : (V : Set (W → ℝ)) = ⋂ w, {v | 0 ≤ v w} := by ext; simp [V]
  rw [this]
  exact isClosed_iInter fun w => isClosed_le continuous_const (continuous_apply w)

omit [Fintype W] in
theorem zero_mem_V : (0 : W → ℝ) ∈ V := fun _ => le_rfl

theorem one_sub_β_pos : 0 < 1 - m.β := by linarith [m.β_lt_one]

/-- The stopping value `e(w) = w/(1 − β)`. -/
noncomputable def e (w : W) : ℝ := m.wage w / (1 - m.β)

theorem e_nonneg (w : W) : 0 ≤ m.e w := div_nonneg (m.wage_nonneg w) m.one_sub_β_pos.le

/-- `Pv ≥ 0` for `v ≥ 0`. -/
theorem mulVec_nonneg {v : W → ℝ} (hv : v ∈ V) (w : W) : 0 ≤ (m.P *ᵥ v) w := by
  have := m.P_markov.mulVec_le_mulVec (f := 0) (g := v) hv w
  simpa using this

/-- The Bellman operator (p. 98): `Tv(w) = max{w/(1 − β), c + β(Pv)(w)}`. -/
noncomputable def T (v : W → ℝ) : W → ℝ := fun w => max (m.e w) (m.c + m.β * (m.P *ᵥ v) w)

/-- Exercise 3.3.1 (i), p. 98: `T` maps `V` into `V`. -/
theorem T_mapsTo : MapsTo m.T V V := fun _ hv w =>
  le_max_of_le_right (add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg hv w)))

/-- Exercise 3.3.1 (i), p. 98: `T` is order preserving. -/
theorem T_monotone : Monotone m.T := by
  intro v v' hvv' w
  exact max_le_max le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (m.P_markov.mulVec_le_mulVec hvv' w) m.β_pos.le))

/-- Pointwise estimate: `|Tv(w) − Tv'(w)| ≤ β‖v − v'‖`. -/
theorem abs_T_sub_le (v v' : W → ℝ) (w : W) : |m.T v w - m.T v' w| ≤ m.β * ‖v - v'‖ := by
  unfold T
  rw [max_comm (m.e w), max_comm (m.e w)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
  have := m.P_markov.abs_mulVec_le (v - v') w
  rw [mulVec_sub, Pi.sub_apply] at this
  exact mul_le_mul_of_nonneg_left this m.β_pos.le

/-- Exercise 3.3.1 (ii), p. 98: `T` is a contraction of modulus `β` on `V` in the supremum norm. -/
theorem isContractionOn_T : IsContractionOn m.T V m.β where
  mapsTo := m.T_mapsTo
  nonneg := m.β_pos.le
  lt_one := m.β_lt_one
  norm_sub_le u _ v _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_pos.le (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact m.abs_T_sub_le u v w

/-- The value function `v*`: the fixed point of `T` in `V` given by Banach's theorem. -/
noncomputable def vstar : W → ℝ :=
  Classical.choose (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)

theorem vstar_mem : m.vstar ∈ V :=
  (Classical.choose_spec (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).1

theorem isFixedPt_vstar : IsFixedPt m.T m.vstar :=
  (Classical.choose_spec (m.isContractionOn_T.exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).2

/-- The Bellman equation (3.23), p. 97. -/
theorem bellman_equation (w : W) :
    m.vstar w = max (m.wage w / (1 - m.β)) (m.c + m.β * ∑ w', m.vstar w' * m.P w w') := by
  have := congrFun m.isFixedPt_vstar.eq w
  rw [← this]
  unfold T e
  rw [mulVec_apply_eq]

/-- `v*` is the only fixed point of `T` in `V` (p. 98). -/
theorem eq_vstar_of_isFixedPt {v : W → ℝ} (hv : v ∈ V) (hfix : IsFixedPt m.T v) : v = m.vstar :=
  m.isContractionOn_T.fixedPt_unique hv m.vstar_mem hfix m.isFixedPt_vstar

/-- Value function iteration (p. 98): `Tᵏv → v*` for every `v ∈ V`, at rate `βᵏ`. -/
theorem tendsto_iterate_T {v : W → ℝ} (hv : v ∈ V) :
    Tendsto (fun k : ℕ => m.T^[k] v) atTop (𝓝 m.vstar) :=
  m.isContractionOn_T.tendsto_iterate_fixedPt hv m.vstar_mem m.isFixedPt_vstar

theorem norm_iterate_T_sub_vstar_le {v : W → ℝ} (hv : v ∈ V) (k : ℕ) :
    ‖m.T^[k] v - m.vstar‖ ≤ m.β ^ k * ‖v - m.vstar‖ :=
  m.isContractionOn_T.norm_iterate_sub_fixedPt_le hv m.vstar_mem m.isFixedPt_vstar k

/-- A `v`-greedy policy (p. 98): accept iff `w/(1 − β) ≥ c + β(Pv)(w)`. -/
def IsGreedy (v : W → ℝ) (σ : W → Bool) : Prop :=
  ∀ w, σ w = true ↔ m.c + m.β * (m.P *ᵥ v) w ≤ m.e w

/-- **Lemma 3.3.1** (p. 98): `v*` is increasing on `(W, ≤)` whenever the wage is increasing and `P`
is monotone increasing. The increasing functions in `V` form a closed set that `T` maps into
itself, so the fixed point lies in it (Vol. 1, Ex 1.2.18). -/
theorem monotone_vstar [PartialOrder W] (hw : Monotone m.wage) (hP : MonotoneIncreasing m.P) :
    Monotone m.vstar := by
  set I : Set (W → ℝ) := V ∩ {v | Monotone v} with hI
  have hclosed : IsClosed I := isClosed_V.inter (isClosed_monotone W)
  have hmaps : ∀ v ∈ I, m.T v ∈ I := by
    rintro v ⟨hvV, hvm⟩
    refine ⟨m.T_mapsTo hvV, fun w w' hww' => ?_⟩
    have h1 : m.e w ≤ m.e w' := div_le_div_of_nonneg_right (hw hww') m.one_sub_β_pos.le
    have h2 := (monotoneIncreasing_iff m.P).1 hP v hvm hww'
    exact max_le_max h1 (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 m.β_pos.le))
  have hiter : ∀ k, m.T^[k] 0 ∈ I := by
    intro k
    induction k with
    | zero => exact ⟨zero_mem_V, fun _ _ _ => le_rfl⟩
    | succ k ih => rw [iterate_succ_apply']; exact hmaps _ ih
  exact (hclosed.mem_of_tendsto (m.tendsto_iterate_T zero_mem_V)
    (Eventually.of_forall hiter)).2

/-! ### Continuation values (§3.3.1.2) -/

/-- The continuation value function `h*(w) = c + β ∑ v*(w')P(w, w')` (p. 100). -/
noncomputable def hstar : W → ℝ := fun w => m.c + m.β * (m.P *ᵥ m.vstar) w

theorem hstar_mem : m.hstar ∈ V := fun w =>
  add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg m.vstar_mem w))

/-- `v* = e ∨ h*`: the value is the larger of stopping and continuing. -/
theorem vstar_eq_max (w : W) : m.vstar w = max (m.e w) (m.hstar w) :=
  (congrFun m.isFixedPt_vstar.eq w).symm

/-- The `v*`-greedy policy accepts iff the stopping value is at least the continuation value. -/
theorem isGreedy_vstar : m.IsGreedy m.vstar fun w => decide (m.hstar w ≤ m.e w) := fun w => by
  rw [decide_eq_true_iff]
  rfl

/-- The operator `Q` of (3.24): `(Qh)(w) = c + β ∑ max{w'/(1 − β), h(w')} P(w, w')`. -/
noncomputable def Q (h : W → ℝ) : W → ℝ := fun w =>
  m.c + m.β * (m.P *ᵥ fun w' => max (m.e w') (h w')) w

/-- Exercise 3.3.3 (p. 100): `h*` satisfies `h*(w) = c + β ∑ max{w'/(1 − β), h*(w')} P(w, w')`,
i.e. `h*` is a fixed point of `Q`. -/
theorem isFixedPt_hstar : IsFixedPt m.Q m.hstar := by
  funext w
  unfold Q
  have : (fun w' => max (m.e w') (m.hstar w')) = m.vstar :=
    funext fun w' => (m.vstar_eq_max w').symm
  rw [this]
  rfl

/-- Exercise 3.3.4 (a), p. 101: `Q` maps `V` into `V`. -/
theorem Q_mapsTo : MapsTo m.Q V V := fun h _ w => by
  unfold Q
  refine add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg (fun w' => ?_) w))
  exact le_max_of_le_left (m.e_nonneg w')

/-- Exercise 3.3.4 (a), p. 101: `Q` is order preserving. -/
theorem Q_monotone : Monotone m.Q := by
  intro h h' hhh' w
  unfold Q
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (m.P_markov.mulVec_le_mulVec
    (fun w' => max_le_max le_rfl (hhh' w')) w) m.β_pos.le)

/-- Exercise 3.3.4 (b), p. 101: `Q` is a contraction of modulus `β` on `V` in the supremum
norm. -/
theorem isContractionOn_Q : IsContractionOn m.Q V m.β where
  mapsTo := m.Q_mapsTo
  nonneg := m.β_pos.le
  lt_one := m.β_lt_one
  norm_sub_le h _ h' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg m.β_pos.le (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold Q
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
    have hmv := m.P_markov.abs_mulVec_le ((fun w' => max (m.e w') (h w')) -
      fun w' => max (m.e w') (h' w')) w
    rw [mulVec_sub, Pi.sub_apply] at hmv
    refine mul_le_mul_of_nonneg_left (hmv.trans ?_) m.β_pos.le
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro w'
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [max_comm (m.e w') (h w'), max_comm (m.e w') (h' w')]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := norm_le_pi_norm (h - h') w'
    simpa [Real.norm_eq_abs] using this

/-- `h*` is the unique fixed point of `Q` in `V`, and iterating `Q` from any `h ∈ V` converges to
it (p. 101). -/
theorem eq_hstar_of_isFixedPt {h : W → ℝ} (hh : h ∈ V) (hfix : IsFixedPt m.Q h) : h = m.hstar :=
  m.isContractionOn_Q.fixedPt_unique hh m.hstar_mem hfix m.isFixedPt_hstar

theorem tendsto_iterate_Q {h : W → ℝ} (hh : h ∈ V) :
    Tendsto (fun k : ℕ => m.Q^[k] h) atTop (𝓝 m.hstar) :=
  m.isContractionOn_Q.tendsto_iterate_fixedPt hh m.hstar_mem m.isFixedPt_hstar

/-! ### Job search with separation (§3.3.2) -/

/-- The denominator `1 − β(1 − α)` of (3.27) is positive for `α ≥ 0`. -/
theorem denom_pos {α : ℝ} (hα0 : 0 ≤ α) : 0 < 1 - m.β * (1 - α) := by
  have := m.β_pos; have := m.β_lt_one
  nlinarith

/-- The modulus `αβ/(1 − β(1 − α))` of the stopping branch of (3.28) is below one. -/
theorem sep_modulus_lt_one {α : ℝ} (hα0 : 0 ≤ α) :
    α * m.β / (1 - m.β * (1 - α)) < 1 := by
  rw [div_lt_one (m.denom_pos hα0)]
  have := m.β_lt_one
  nlinarith [m.β_pos]

theorem sep_modulus_nonneg {α : ℝ} (hα0 : 0 ≤ α) :
    0 ≤ α * m.β / (1 - m.β * (1 - α)) :=
  div_nonneg (mul_nonneg hα0 m.β_pos.le) (m.denom_pos hα0).le

/-- The employed worker's value (3.27) given the unemployed value `v`:
`v_e(w) = (w + αβ(Pv)(w)) / (1 − β(1 − α))`. -/
noncomputable def employedValue (α : ℝ) (v : W → ℝ) : W → ℝ := fun w =>
  (m.wage w + α * m.β * (m.P *ᵥ v) w) / (1 - m.β * (1 - α))

/-- The operator of (3.28): `v ↦ max{v_e(v), c + βPv}`. -/
noncomputable def S (α : ℝ) (v : W → ℝ) : W → ℝ := fun w =>
  max (m.employedValue α v w) (m.c + m.β * (m.P *ᵥ v) w)

/-- (3.26) ⟺ (3.27): given `v_u`, the equation `v_e(w) = w + β[α(Pv_u)(w) + (1 − α)v_e(w)]` has
the unique solution `v_e = employedValue α v_u`. -/
theorem employed_recursion_iff {α : ℝ} (hα0 : 0 ≤ α) (vu ve : W → ℝ) :
    (∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) ↔
      ve = m.employedValue α vu := by
  have hD := m.denom_pos hα0
  constructor
  · intro h
    funext w
    unfold employedValue
    rw [eq_div_iff hD.ne']
    linear_combination h w
  · intro h w
    rw [h]
    unfold employedValue
    field_simp
    ring

/-- Substituting (3.27) into (3.25) gives (3.28): the pair `(v_u, v_e)` solves (3.25)–(3.26) iff
`v_u` is a fixed point of `S` and `v_e = employedValue α v_u`. -/
theorem system_iff {α : ℝ} (hα0 : 0 ≤ α) (vu ve : W → ℝ) :
    ((∀ w, vu w = max (ve w) (m.c + m.β * (m.P *ᵥ vu) w)) ∧
      ∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) ↔
      IsFixedPt (m.S α) vu ∧ ve = m.employedValue α vu := by
  rw [m.employed_recursion_iff hα0]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨funext fun w => ?_, h2⟩
    rw [S, ← h2]
    exact (h1 w).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun w => ?_, h2⟩
    rw [h2]
    exact (congrFun h1 w).symm

/-- `S` maps `V` into `V`. -/
theorem S_mapsTo (α : ℝ) : MapsTo (m.S α) V V := fun _ hv w =>
  le_max_of_le_right (add_nonneg m.c_pos.le (mul_nonneg m.β_pos.le (m.mulVec_nonneg hv w)))

/-- Exercise 3.3.5 (p. 102): `S` is a contraction on `V` with modulus
`max{αβ/(1 − β(1 − α)), β} < 1`, as the upper envelope of two contractions (Vol. 1,
Lemma 2.2.3). -/
theorem isContractionOn_S {α : ℝ} (hα0 : 0 ≤ α) :
    IsContractionOn (m.S α) V (max (α * m.β / (1 - m.β * (1 - α))) m.β) where
  mapsTo := m.S_mapsTo α
  nonneg := le_max_of_le_right m.β_pos.le
  lt_one := max_lt (m.sep_modulus_lt_one hα0) m.β_lt_one
  norm_sub_le u _ v _ := by
    have hD := m.denom_pos hα0
    have hL0 : 0 ≤ max (α * m.β / (1 - m.β * (1 - α))) m.β := le_max_of_le_right m.β_pos.le
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hL0 (norm_nonneg _))]
    intro w
    rw [Pi.sub_apply, Real.norm_eq_abs]
    unfold S employedValue
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · have hmv := m.P_markov.abs_mulVec_le (u - v) w
      rw [mulVec_sub, Pi.sub_apply] at hmv
      rw [← sub_div, add_sub_add_left_eq_sub, ← mul_sub, abs_div, abs_mul,
        abs_of_pos hD, abs_of_nonneg (mul_nonneg hα0 m.β_pos.le), mul_div_right_comm]
      exact mul_le_mul (le_max_left _ _) hmv (abs_nonneg _) hL0
    · have hmv := m.P_markov.abs_mulVec_le (u - v) w
      rw [mulVec_sub, Pi.sub_apply] at hmv
      rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg m.β_pos.le]
      exact mul_le_mul (le_max_right _ _) hmv (abs_nonneg _) hL0

/-- The unemployed worker's value `v_u*` with separation: the fixed point of `S` in `V`. -/
noncomputable def vuStar {α : ℝ} (hα0 : 0 ≤ α) : W → ℝ :=
  Classical.choose ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)

theorem vuStar_mem {α : ℝ} (hα0 : 0 ≤ α) : m.vuStar hα0 ∈ V :=
  (Classical.choose_spec
    ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).1

theorem isFixedPt_vuStar {α : ℝ} (hα0 : 0 ≤ α) :
    IsFixedPt (m.S α) (m.vuStar hα0) :=
  (Classical.choose_spec
    ((m.isContractionOn_S hα0).exists_fixedPt isClosed_V ⟨0, zero_mem_V⟩)).2

/-- Exercise 3.3.5 (p. 102): (3.28) has exactly one solution in `V`. -/
theorem eq_vuStar_of_isFixedPt {α : ℝ} (hα0 : 0 ≤ α) {v : W → ℝ} (hv : v ∈ V)
    (hfix : IsFixedPt (m.S α) v) : v = m.vuStar hα0 :=
  (m.isContractionOn_S hα0).fixedPt_unique hv (m.vuStar_mem hα0) hfix
    (m.isFixedPt_vuStar hα0)

/-- Exercise 3.3.5 (p. 102), the convergent method: iterate `S` from any `v ∈ V` to obtain `v_u*`,
then read off `v_e*` from (3.27). -/
theorem tendsto_iterate_S {α : ℝ} (hα0 : 0 ≤ α) {v : W → ℝ} (hv : v ∈ V) :
    Tendsto (fun k : ℕ => (m.S α)^[k] v) atTop (𝓝 (m.vuStar hα0)) :=
  (m.isContractionOn_S hα0).tendsto_iterate_fixedPt hv (m.vuStar_mem hα0)
    (m.isFixedPt_vuStar hα0)

/-- The employed worker's value `v_e*`, (3.27). -/
noncomputable def veStar {α : ℝ} (hα0 : 0 ≤ α) : W → ℝ :=
  m.employedValue α (m.vuStar hα0)

/-- The claim of p. 102: the system (3.25)–(3.26) has the unique solution `(v_u*, v_e*)` in
`V × V`. -/
theorem system_unique {α : ℝ} (hα0 : 0 ≤ α) :
    ((∀ w, m.vuStar hα0 w =
        max (m.veStar hα0 w) (m.c + m.β * (m.P *ᵥ m.vuStar hα0) w)) ∧
      ∀ w, m.veStar hα0 w = m.wage w + m.β * (α * (m.P *ᵥ m.vuStar hα0) w +
        (1 - α) * m.veStar hα0 w)) ∧
    ∀ vu ve : W → ℝ, vu ∈ V →
      (∀ w, vu w = max (ve w) (m.c + m.β * (m.P *ᵥ vu) w)) →
      (∀ w, ve w = m.wage w + m.β * (α * (m.P *ᵥ vu) w + (1 - α) * ve w)) →
      vu = m.vuStar hα0 ∧ ve = m.veStar hα0 := by
  refine ⟨(m.system_iff hα0 _ _).2 ⟨m.isFixedPt_vuStar hα0, rfl⟩, fun vu ve hvu h1 h2 => ?_⟩
  obtain ⟨hfix, hve⟩ := (m.system_iff hα0 vu ve).1 ⟨h1, h2⟩
  have huu := m.eq_vuStar_of_isFixedPt hα0 hvu hfix
  exact ⟨huu, by rw [hve, huu]; rfl⟩

/-- `v_e* ∈ V`: the employed value is nonnegative. -/
theorem veStar_mem {α : ℝ} (hα0 : 0 ≤ α) : m.veStar hα0 ∈ V := fun w =>
  div_nonneg (add_nonneg (m.wage_nonneg w) (mul_nonneg (mul_nonneg hα0 m.β_pos.le)
    (m.mulVec_nonneg (m.vuStar_mem hα0) w))) (m.denom_pos hα0).le

/-- The stopping value `s*` and continuation value `h*_e` of p. 102; `v_u* = s* ∨ h*_e`. -/
theorem vuStar_eq_max {α : ℝ} (hα0 : 0 ≤ α) (w : W) :
    m.vuStar hα0 w =
      max (m.veStar hα0 w) (m.c + m.β * (m.P *ᵥ m.vuStar hα0) w) :=
  (congrFun (m.isFixedPt_vuStar hα0).eq w).symm

end MarkovJobSearch

end SargentStachurski.MarkovDynamics

set_option linter.style.longLine false
#print axioms SargentStachurski.MarkovDynamics.IsMarkov
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.mk
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.nonneg
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.rowsum
#print axioms SargentStachurski.MarkovDynamics.IsDistribution
#print axioms SargentStachurski.MarkovDynamics.IsDistribution.mk
#print axioms SargentStachurski.MarkovDynamics.IsDistribution.nonneg
#print axioms SargentStachurski.MarkovDynamics.IsDistribution.sum_eq_one
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.mul
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.pow
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.mulVec_const
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.norm_mulVec_sub_le
#print axioms SargentStachurski.MarkovDynamics.GloballyStable
#print axioms SargentStachurski.MarkovDynamics.globallyStable_of_tendsto
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.mk
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.mapsTo
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.nonneg
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.lt_one
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.iterate_mem
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.MarkovDynamics.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.MarkovDynamics.pathProb
#print axioms SargentStachurski.MarkovDynamics.paths
#print axioms SargentStachurski.MarkovDynamics.pathProb_snoc
#print axioms SargentStachurski.MarkovDynamics.pow_apply_eq_sum_paths
#print axioms SargentStachurski.MarkovDynamics.pow_succ_apply
#print axioms SargentStachurski.MarkovDynamics.vecMul_apply
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.isDistribution_vecMul
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.isDistribution_vecMul_pow
#print axioms SargentStachurski.MarkovDynamics.iterate_vecMul
#print axioms SargentStachurski.MarkovDynamics.expectation_eq_dotProduct
#print axioms SargentStachurski.MarkovDynamics.IsStationary
#print axioms SargentStachurski.MarkovDynamics.IsStationary.vecMul_pow
#print axioms SargentStachurski.MarkovDynamics.Irreducible
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.pow_add_apply_ge
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.irreducible_iff
#print axioms SargentStachurski.MarkovDynamics.Inventory
#print axioms SargentStachurski.MarkovDynamics.Inventory.mk
#print axioms SargentStachurski.MarkovDynamics.Inventory.S
#print axioms SargentStachurski.MarkovDynamics.Inventory.s
#print axioms SargentStachurski.MarkovDynamics.Inventory.p
#print axioms SargentStachurski.MarkovDynamics.Inventory.s_lt_S
#print axioms SargentStachurski.MarkovDynamics.Inventory.p_pos
#print axioms SargentStachurski.MarkovDynamics.Inventory.p_lt_one
#print axioms SargentStachurski.MarkovDynamics.Inventory.State
#print axioms SargentStachurski.MarkovDynamics.Inventory.h
#print axioms SargentStachurski.MarkovDynamics.Inventory.h_le
#print axioms SargentStachurski.MarkovDynamics.Inventory.next
#print axioms SargentStachurski.MarkovDynamics.Inventory.φ
#print axioms SargentStachurski.MarkovDynamics.Inventory.φ_pos
#print axioms SargentStachurski.MarkovDynamics.Inventory.one_sub_p_nonneg
#print axioms SargentStachurski.MarkovDynamics.Inventory.one_sub_p_lt_one
#print axioms SargentStachurski.MarkovDynamics.Inventory.summable_φ
#print axioms SargentStachurski.MarkovDynamics.Inventory.tsum_φ
#print axioms SargentStachurski.MarkovDynamics.Inventory.P
#print axioms SargentStachurski.MarkovDynamics.Inventory.P_apply
#print axioms SargentStachurski.MarkovDynamics.Inventory.summable_term
#print axioms SargentStachurski.MarkovDynamics.Inventory.isMarkov_P
#print axioms SargentStachurski.MarkovDynamics.Inventory.φ_le_P
#print axioms SargentStachurski.MarkovDynamics.Inventory.P_pos
#print axioms SargentStachurski.MarkovDynamics.Inventory.next_val
#print axioms SargentStachurski.MarkovDynamics.Inventory.sState
#print axioms SargentStachurski.MarkovDynamics.Inventory.sState_val
#print axioms SargentStachurski.MarkovDynamics.Inventory.fullState
#print axioms SargentStachurski.MarkovDynamics.Inventory.fullState_val
#print axioms SargentStachurski.MarkovDynamics.Inventory.SState
#print axioms SargentStachurski.MarkovDynamics.Inventory.SState_val
#print axioms SargentStachurski.MarkovDynamics.Inventory.next_eq_sState
#print axioms SargentStachurski.MarkovDynamics.Inventory.next_sState_zero
#print axioms SargentStachurski.MarkovDynamics.Inventory.next_fullState
#print axioms SargentStachurski.MarkovDynamics.Inventory.next_eq_SState
#print axioms SargentStachurski.MarkovDynamics.Inventory.irreducible_P
#print axioms SargentStachurski.MarkovDynamics.l1
#print axioms SargentStachurski.MarkovDynamics.l1_nonneg
#print axioms SargentStachurski.MarkovDynamics.norm_le_l1
#print axioms SargentStachurski.MarkovDynamics.l1_eq_zero_iff
#print axioms SargentStachurski.MarkovDynamics.sum_vecMul
#print axioms SargentStachurski.MarkovDynamics.l1_vecMul_le
#print axioms SargentStachurski.MarkovDynamics.sum_vecMul_pow
#print axioms SargentStachurski.MarkovDynamics.l1_vecMul_pow_le
#print axioms SargentStachurski.MarkovDynamics.tendsto_vecMul
#print axioms SargentStachurski.MarkovDynamics.globallyStable_of_pos
#print axioms SargentStachurski.MarkovDynamics.distMap
#print axioms SargentStachurski.MarkovDynamics.distMap_iterate
#print axioms SargentStachurski.MarkovDynamics.globallyStable_distMap
#print axioms SargentStachurski.MarkovDynamics.mulVec_apply_eq
#print axioms SargentStachurski.MarkovDynamics.pow_mulVec_apply_eq
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.isFixedPt_const
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.sup'_abs_mulVec_le
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.MarkovDynamics.iterated_expectations
#print axioms SargentStachurski.MarkovDynamics.FOSD
#print axioms SargentStachurski.MarkovDynamics.MonotoneIncreasing
#print axioms SargentStachurski.MarkovDynamics.monotoneIncreasing_iff
#print axioms SargentStachurski.MarkovDynamics.MonotoneIncreasing.pow
#print axioms SargentStachurski.MarkovDynamics.DayLaborer
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.mk
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.α
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.β
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.α_pos
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.α_lt_one
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.β_pos
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.β_lt_one
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.P
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.isMarkov_P
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.α_add_β_pos
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.ψstar
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.isDistribution_ψstar
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.isStationary_ψstar
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.eq_ψstar_of_isStationary
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.vecMul_zero_sub
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.vecMul_pow_zero_sub
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.abs_one_sub_lt_one
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.tendsto_vecMul_pow
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.P_pos
#print axioms SargentStachurski.MarkovDynamics.DayLaborer.globallyStable_distMap
#print axioms SargentStachurski.MarkovDynamics.monotoneIncreasing_two_state_iff
#print axioms SargentStachurski.MarkovDynamics.Tauchen
#print axioms SargentStachurski.MarkovDynamics.Tauchen.mk
#print axioms SargentStachurski.MarkovDynamics.Tauchen.n
#print axioms SargentStachurski.MarkovDynamics.Tauchen.two_le_n
#print axioms SargentStachurski.MarkovDynamics.Tauchen.ρ
#print axioms SargentStachurski.MarkovDynamics.Tauchen.x₁
#print axioms SargentStachurski.MarkovDynamics.Tauchen.s
#print axioms SargentStachurski.MarkovDynamics.Tauchen.s_pos
#print axioms SargentStachurski.MarkovDynamics.Tauchen.F
#print axioms SargentStachurski.MarkovDynamics.Tauchen.F_mono
#print axioms SargentStachurski.MarkovDynamics.Tauchen.F_nonneg
#print axioms SargentStachurski.MarkovDynamics.Tauchen.F_le_one
#print axioms SargentStachurski.MarkovDynamics.Tauchen.x
#print axioms SargentStachurski.MarkovDynamics.Tauchen.x_mono
#print axioms SargentStachurski.MarkovDynamics.Tauchen.G
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat
#print axioms SargentStachurski.MarkovDynamics.Tauchen.P
#print axioms SargentStachurski.MarkovDynamics.Tauchen.P_apply
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat_zero
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat_last
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat_mid
#print axioms SargentStachurski.MarkovDynamics.Tauchen.G_zero
#print axioms SargentStachurski.MarkovDynamics.Tauchen.G_n
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat_eq_G_sub
#print axioms SargentStachurski.MarkovDynamics.Tauchen.G_antitone
#print axioms SargentStachurski.MarkovDynamics.Tauchen.Pnat_nonneg
#print axioms SargentStachurski.MarkovDynamics.Tauchen.sum_Ico_Pnat
#print axioms SargentStachurski.MarkovDynamics.Tauchen.sum_Pnat
#print axioms SargentStachurski.MarkovDynamics.Tauchen.isMarkov_P
#print axioms SargentStachurski.MarkovDynamics.Tauchen.sum_filter_P
#print axioms SargentStachurski.MarkovDynamics.Tauchen.sum_mul_nonneg_of_tails_nonneg
#print axioms SargentStachurski.MarkovDynamics.Tauchen.fosd_of_tails_le
#print axioms SargentStachurski.MarkovDynamics.Tauchen.monotoneIncreasing_P
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.norm_smul_pow_mulVec_le
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.summable_smul_pow_mulVec
#print axioms SargentStachurski.MarkovDynamics.lifetimeValue
#print axioms SargentStachurski.MarkovDynamics.lifetimeValue_eq_tsum_smul
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.one_sub_smul_mulVec_lifetimeValue
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.isUnit_one_sub_smul
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.lifetimeValue_eq_inv
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.lifetimeValue_eq_add
#print axioms SargentStachurski.MarkovDynamics.firm_discount_mem
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.firm_value
#print axioms SargentStachurski.MarkovDynamics.isClosed_monotone
#print axioms SargentStachurski.MarkovDynamics.monotone_sum
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.monotone_lifetimeValue
#print axioms SargentStachurski.MarkovDynamics.crra
#print axioms SargentStachurski.MarkovDynamics.IsMarkov.consumption_value
#print axioms SargentStachurski.MarkovDynamics.monotone_crra_exp
#print axioms SargentStachurski.MarkovDynamics.Tauchen.monotone_crra_value
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.mk
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.wage
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.wage_nonneg
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.P
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.P_markov
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.c
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.c_pos
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.β
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.β_pos
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.β_lt_one
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.V
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isClosed_V
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.zero_mem_V
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.one_sub_β_pos
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.e
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.e_nonneg
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.mulVec_nonneg
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.T
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.T_mapsTo
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.T_monotone
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.abs_T_sub_le
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isContractionOn_T
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vstar_mem
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isFixedPt_vstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.bellman_equation
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.tendsto_iterate_T
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.norm_iterate_T_sub_vstar_le
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.IsGreedy
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.monotone_vstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.hstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.hstar_mem
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vstar_eq_max
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isGreedy_vstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.Q
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isFixedPt_hstar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.Q_mapsTo
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.Q_monotone
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isContractionOn_Q
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.eq_hstar_of_isFixedPt
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.tendsto_iterate_Q
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.denom_pos
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.sep_modulus_lt_one
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.sep_modulus_nonneg
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.employedValue
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.S
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.employed_recursion_iff
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.system_iff
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.S_mapsTo
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isContractionOn_S
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vuStar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vuStar_mem
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.isFixedPt_vuStar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.eq_vuStar_of_isFixedPt
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.tendsto_iterate_S
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.veStar
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.system_unique
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.veStar_mem
#print axioms SargentStachurski.MarkovDynamics.MarkovJobSearch.vuStar_eq_max
