/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

/-! # Stationary distribution and Poisson's equation for a finite irreducible chain

Post #3 measures the quality of a simulated path by its occupation frequencies and its empirical
transition matrix, compared with the stationary distribution `π` of the transition matrix `P`. The
convergence-speed claims of post #3 (`OccupationDiscrepancy`, `StackBound`, `RotorRouter`,
`MCRate`) all go through **Poisson's equation** `h − Ph = f − π(f)` (Meyn and Tweedie, Ch. 17;
Kemeny and Snell's fundamental matrix). This module proves what they need, for a finite
irreducible stochastic matrix; aperiodicity is **not** assumed.

Irreducibility is `∀ i j, ∃ k, 0 < (Pᵏ) i j` (the `k = 0` form; `k = 0` only helps for `i = j`).

**Results.**
* `pow_apply_nonneg_of_nonneg`, `sum_pow_apply_eq_one`: `Pᵏ` is stochastic.
* `eq_of_mulVec_eq_self_of_irreducible`: **maximum principle**: a harmonic function (`Ph = h`) of
  an irreducible chain is constant.
* `exists_isStationaryDistribution`: a stationary distribution exists (for any stochastic `P` on a
  nonempty finite set; the proof takes a left null vector `μ` of `I − P`, which exists by
  rank–nullity, and shows that `|μ|` is stationary).
* `IsStationaryDistribution.pos`: under irreducibility every `π_i > 0`.
* `exists_poisson`: **Poisson's equation** `h − Ph = f − π(f)` has a solution for every `f`. The
  range of `I − P` is the hyperplane `{g : π(g) = 0}`: it is contained in it, and has dimension
  `|S| − 1` because the kernel of `I − P` is the constants (maximum principle).
* `poisson_const_eq` : conversely, if `h − Ph = f − c` then `c = π(f)`.
* `eq_of_vecMul_eq_self` / `existsUnique_isStationaryDistribution`: the stationary distribution
  is unique (indeed any signed `ν` with `νP = ν` and `Σν = 1` equals `π`).
* `poisson_sub_eq`: the solution of Poisson's equation is unique up to an additive constant.
* `exists_poisson_normalized`: it can be normalised to `π(h) = 0`.
-/

namespace RQMCMarkov.MarkovDriving

open Matrix Finset Module

variable {S : Type*} [Fintype S]

/-- A stationary distribution of the transition matrix `P`: a probability vector with `μP = μ`. -/
structure IsStationaryDistribution (P : Matrix S S ℝ) (μ : S → ℝ) : Prop where
  vecMul_eq : μ ᵥ* P = μ
  nonneg : ∀ i, 0 ≤ μ i
  sum_eq_one : ∑ i, μ i = 1

/-- The entries of `Pᵏ` are nonnegative when those of `P` are. -/
theorem pow_apply_nonneg_of_nonneg [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (k : ℕ) (i j : S) : 0 ≤ (P ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, one_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ k ih =>
    rw [pow_succ, mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (ih i l) (hP0 l j)

/-- The row sums of `Pᵏ` are one when those of `P` are. -/
theorem sum_pow_apply_eq_one [DecidableEq S] {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1)
    (k : ℕ) (i : S) :
    ∑ j, (P ^ k) i j = 1 := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero]
    simp only [one_apply, Finset.sum_ite_eq, mem_univ, ite_true]
  | succ k ih =>
    rw [pow_succ]
    simp only [mul_apply]
    rw [Finset.sum_comm]
    calc ∑ l, ∑ j, (P ^ k) i l * P l j = ∑ l, (P ^ k) i l := by
          refine sum_congr rfl fun l _ => ?_
          rw [← mul_sum, hP1 l, mul_one]
      _ = 1 := ih i

/-- `P 1 = 1`: a stochastic matrix fixes the constant function one. -/
theorem mulVec_const_one {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1) :
    P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext i
  simp only [mulVec, dotProduct, mul_one]
  exact hP1 i

/-- One step of the maximum principle: for a stochastic `Q`, if `h` is maximal at `x` and
`(Qh)(x) = h(x)`, then `h y = h x` whenever `Q x y > 0`. -/
theorem eq_of_isMax_of_mulVec_eq {Q : Matrix S S ℝ} (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ1 : ∀ i, ∑ j, Q i j = 1) {h : S → ℝ} {x : S} (hmax : ∀ y, h y ≤ h x)
    (hx : (Q *ᵥ h) x = h x) {y : S} (hy : 0 < Q x y) : h y = h x := by
  have hsum : ∑ z, Q x z * (h x - h z) = 0 := by
    have e : ∑ z, Q x z * (h x - h z) = h x * ∑ z, Q x z - (Q *ᵥ h) x := by
      simp only [mul_sub, sum_sub_distrib, mulVec, dotProduct, mul_sum]
      congr 1
      exact sum_congr rfl fun z _ => mul_comm _ _
    rw [e, hQ1, mul_one, hx, sub_self]
  have hterm := (sum_eq_zero_iff_of_nonneg
    (fun z _ => mul_nonneg (hQ0 x z) (sub_nonneg.2 (hmax z)))).1 hsum y (mem_univ y)
  rcases mul_eq_zero.1 hterm with h1 | h1
  · exact absurd h1 hy.ne'
  · linarith

/-- **Maximum principle.** For an irreducible stochastic matrix, a function with `Ph = h` is
constant. -/
theorem eq_of_mulVec_eq_self_of_irreducible [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {h : S → ℝ} (hh : P *ᵥ h = h) (y z : S) : h y = h z := by
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image univ h ⟨y, mem_univ y⟩
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ h = h := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mulVec]
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hh, ih]
  have key : ∀ w, h w = h x := fun w => by
    obtain ⟨k, hkpos⟩ := hirr x w
    exact eq_of_isMax_of_mulVec_eq (pow_apply_nonneg_of_nonneg hP0 k) (sum_pow_apply_eq_one hP1 k)
      (fun v => hx v (mem_univ v)) (congrFun (hk k) x) hkpos
  rw [key y, key z]

/-- `μ (I − P) = 0` iff `μ P = μ`. -/
theorem vecMul_one_sub_eq_zero_iff [DecidableEq S] {P : Matrix S S ℝ} {μ : S → ℝ} :
    μ ᵥ* (1 - P) = 0 ↔ μ ᵥ* P = μ := by
  rw [vecMul_sub, vecMul_one, sub_eq_zero, eq_comm]

/-- `(I − P) h = h − P h`. -/
theorem one_sub_mulVec [DecidableEq S] (P : Matrix S S ℝ) (h : S → ℝ) :
    (1 - P) *ᵥ h = h - P *ᵥ h := by
  rw [sub_mulVec, one_mulVec]

/-- The constant function one is a nonzero vector in the kernel of `I − P`. -/
theorem const_one_mem_ker [DecidableEq S] {P : Matrix S S ℝ} (hP1 : ∀ i, ∑ j, P i j = 1) :
    (fun _ => (1 : ℝ)) ∈ LinearMap.ker (1 - P).mulVecLin := by
  rw [LinearMap.mem_ker, mulVecLin_apply, one_sub_mulVec, mulVec_const_one hP1, sub_self]

/-- The constant function one is nonzero on a nonempty type. -/
theorem const_one_ne_zero {T : Type*} [Nonempty T] : (fun _ => (1 : ℝ)) ≠ (0 : T → ℝ) := by
  intro h
  have := congrFun h (Classical.arbitrary T)
  exact one_ne_zero this

/-- The rank of `I − P` is less than `|S|`, since its kernel contains the constants. -/
theorem rank_one_sub_lt [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP1 : ∀ i, ∑ j, P i j = 1) :
    (1 - P).rank < Fintype.card S := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (1 - P).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hker : 0 < finrank ℝ (LinearMap.ker (1 - P).mulVecLin) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have hbot := Submodule.finrank_eq_zero.1 h0
    have hmem := const_one_mem_ker hP1
    rw [hbot, Submodule.mem_bot] at hmem
    exact const_one_ne_zero hmem
  unfold Matrix.rank
  omega

/-- **Existence of a stationary distribution**, for any stochastic matrix on a nonempty finite
set: a left null vector `μ ≠ 0` of `I − P` exists by rank–nullity (`rank (I − P)ᵀ = rank (I − P)
< |S|`), and `|μ|`, normalised, is stationary because `|μ| ≤ |μ| P` entrywise with equal sums. -/
theorem exists_isStationaryDistribution [Nonempty S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) :
    ∃ μ, IsStationaryDistribution P μ := by
  classical
  -- a nonzero left null vector of `I − P`
  have hrn := LinearMap.finrank_range_add_finrank_ker (1 - P)ᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hrk : finrank ℝ (LinearMap.range (1 - P)ᵀ.mulVecLin) < Fintype.card S := by
    have h1 := rank_transpose (1 - P)
    have h2 := rank_one_sub_lt hP1
    unfold Matrix.rank at h1 h2
    omega
  have hne : LinearMap.ker (1 - P)ᵀ.mulVecLin ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrn
    omega
  obtain ⟨μ, hμker, hμ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_transpose, vecMul_one_sub_eq_zero_iff] at hμker
  -- `ν = |μ|` is a nonnegative fixed vector
  set ν : S → ℝ := fun i => |μ i| with hν
  have hle : ∀ j, ν j ≤ (ν ᵥ* P) j := by
    intro j
    have e : μ j = ∑ i, μ i * P i j := by
      conv_lhs => rw [← hμker]
      rfl
    change |μ j| ≤ ∑ i, |μ i| * P i j
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_of_nonneg (hP0 i j)]
  have hsumeq : ∑ j, (ν ᵥ* P) j = ∑ j, ν j := by
    change ∑ j, ∑ i, ν i * P i j = ∑ j, ν j
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => by rw [← mul_sum, hP1 i, mul_one]
  have hfix : ν ᵥ* P = ν := by
    have h0 : ∑ j, ((ν ᵥ* P) j - ν j) = 0 := by rw [sum_sub_distrib, hsumeq, sub_self]
    funext j
    have := (sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 h0 j (mem_univ j)
    linarith
  have hpos : 0 < ∑ i, ν i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hμ0
    exact lt_of_lt_of_le (abs_pos.2 hi) (single_le_sum (fun j _ => abs_nonneg (μ j)) (mem_univ i))
  refine ⟨fun i => ν i / ∑ k, ν k, ⟨?_, fun i => div_nonneg (abs_nonneg _) hpos.le, ?_⟩⟩
  · funext j
    change ∑ i, ν i / (∑ k, ν k) * P i j = ν j / ∑ k, ν k
    have e : ∑ i, ν i / (∑ k, ν k) * P i j = (∑ i, ν i * P i j) / ∑ k, ν k := by
      rw [Finset.sum_div]
      exact sum_congr rfl fun i _ => by ring
    rw [e]
    congr 1
    exact congrFun hfix j
  · rw [← Finset.sum_div, div_self hpos.ne']

/-- A stationary distribution is invariant under every power of `P`. -/
theorem IsStationaryDistribution.vecMul_pow [DecidableEq S] {P : Matrix S S ℝ} {μ : S → ℝ}
    (hμ : IsStationaryDistribution P μ) (k : ℕ) : μ ᵥ* P ^ k = μ := by
  induction k with
  | zero => rw [pow_zero, vecMul_one]
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hμ.vecMul_eq]

/-- Under irreducibility the stationary distribution charges every state. -/
theorem IsStationaryDistribution.pos [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {μ : S → ℝ} (hμ : IsStationaryDistribution P μ)
    (j : S) : 0 < μ j := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < μ x := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ i, μ i = 0 :=
      sum_eq_zero fun i _ => le_antisymm (hcon i) (hμ.nonneg i)
    rw [hμ.sum_eq_one] at h0
    exact one_ne_zero h0
  obtain ⟨k, hk⟩ := hirr x j
  have e : μ j = ∑ i, μ i * (P ^ k) i j := by
    conv_lhs => rw [← hμ.vecMul_pow k]
    rfl
  rw [e]
  exact lt_of_lt_of_le (mul_pos hx hk)
    (single_le_sum (fun i _ => mul_nonneg (hμ.nonneg i) (pow_apply_nonneg_of_nonneg hP0 k i j))
      (mem_univ x))

/-- `ν(g − c) = ν(g) − c Σ ν`. -/
theorem dotProduct_sub_const (ν g : S → ℝ) (c : ℝ) :
    ν ⬝ᵥ (fun i => g i - c) = ν ⬝ᵥ g - c * ∑ i, ν i := by
  simp only [dotProduct, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- A left fixed vector annihilates the range of `I − P`: `ν(h − Ph) = 0` when `νP = ν`. -/
theorem dotProduct_sub_mulVec_eq_zero {P : Matrix S S ℝ} {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (h : S → ℝ) : ν ⬝ᵥ (h - P *ᵥ h) = 0 := by
  rw [dotProduct_sub, dotProduct_mulVec, hν, sub_self]

/-- **Poisson's equation.** For a finite irreducible stochastic matrix `P` with stationary
distribution `μ` (aperiodicity is not needed), for every `f` there is `h` with
`h − Ph = f − μ(f)`. -/
theorem exists_poisson [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {μ : S → ℝ}
    (hμ : IsStationaryDistribution P μ) (f : S → ℝ) :
    ∃ h : S → ℝ, ∀ i, h i - (P *ᵥ h) i = f i - μ ⬝ᵥ f := by
  -- the hyperplane `W = {g : μ(g) = 0}`
  let φ : (S → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => μ ⬝ᵥ g
      map_add' := fun a b => dotProduct_add μ a b
      map_smul' := fun c a => dotProduct_smul c μ a }
  have hφ : ∀ g, φ g = μ ⬝ᵥ g := fun _ => rfl
  set A : Matrix S S ℝ := 1 - P with hA
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker φ := by
    rintro g ⟨h, rfl⟩
    rw [LinearMap.mem_ker, hφ, mulVecLin_apply, hA, one_sub_mulVec]
    exact dotProduct_sub_mulVec_eq_zero hμ.vecMul_eq h
  -- `dim W < |S|`
  have hW : finrank ℝ (LinearMap.ker φ) < Fintype.card S := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℝ)]
    refine Submodule.finrank_lt fun htop => ?_
    have hmem : (fun _ => (1 : ℝ)) ∈ LinearMap.ker φ := by rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, hφ, dotProduct_comm] at hmem
    have e : (fun _ => (1 : ℝ)) ⬝ᵥ μ = ∑ i, μ i := by
      simp only [dotProduct, one_mul]
    rw [e, hμ.sum_eq_one] at hmem
    exact one_ne_zero hmem
  -- `dim ker A ≤ 1`, since the kernel is the constants
  have hker : finrank ℝ (LinearMap.ker A.mulVecLin) ≤ 1 := by
    have hsub : LinearMap.ker A.mulVecLin ≤ ℝ ∙ (fun _ => (1 : ℝ)) := by
      intro v hv
      rw [LinearMap.mem_ker, mulVecLin_apply, hA, one_sub_mulVec, sub_eq_zero] at hv
      obtain ⟨x⟩ := (inferInstance : Nonempty S)
      rw [Submodule.mem_span_singleton]
      refine ⟨v x, funext fun y => ?_⟩
      change v x * 1 = v y
      rw [mul_one]
      exact eq_of_mulVec_eq_self_of_irreducible hP0 hP1 hirr hv.symm x y
    calc finrank ℝ (LinearMap.ker A.mulVecLin) ≤ finrank ℝ (ℝ ∙ (fun _ => (1 : ℝ))) :=
          Submodule.finrank_mono hsub
      _ = 1 := finrank_span_singleton const_one_ne_zero
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have heq : LinearMap.range A.mulVecLin = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  -- the centred `f` lies in `W`, hence in the range of `I − P`
  have hg : (fun i => f i - μ ⬝ᵥ f) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, hφ]
    rw [dotProduct_sub_const, hμ.sum_eq_one, mul_one, sub_self]
  rw [← heq] at hg
  obtain ⟨h, hh⟩ := hg
  refine ⟨h, fun i => ?_⟩
  have := congrFun hh i
  rw [mulVecLin_apply, hA, one_sub_mulVec] at this
  exact this

/-- The centring constant in Poisson's equation is forced: if `h − Ph = f − c` then
`c = ν(f)` for every (even signed) `ν` with `νP = ν` and `Σ ν = 1`. -/
theorem poisson_const_eq {P : Matrix S S ℝ} {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (hν1 : ∑ i, ν i = 1) {f h : S → ℝ} {c : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = f i - c) :
    c = ν ⬝ᵥ f := by
  have h0 := dotProduct_sub_mulVec_eq_zero hν h
  have e : h - P *ᵥ h = fun i => f i - c := funext hh
  rw [e] at h0
  rw [dotProduct_sub_const, hν1, mul_one] at h0
  linarith

/-- **Uniqueness of the stationary distribution**: any (even signed) `ν` with `νP = ν` and
`Σ ν = 1` equals the stationary distribution `μ`. Tested against the Poisson solutions for the
indicators `f = 1_{s}`. -/
theorem IsStationaryDistribution.eq_of_vecMul_eq_self [Nonempty S] [DecidableEq S]
    {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : S → ℝ} (hμ : IsStationaryDistribution P μ) {ν : S → ℝ} (hν : ν ᵥ* P = ν)
    (hν1 : ∑ i, ν i = 1) : ν = μ := by
  funext s
  obtain ⟨h, hh⟩ := exists_poisson hP0 hP1 hirr hμ (fun i => if i = s then 1 else 0)
  have hc := poisson_const_eq hν hν1 hh
  have e : ∀ w : S → ℝ, w ⬝ᵥ (fun i => if i = s then (1 : ℝ) else 0) = w s := fun w => by
    simp only [dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [e, e] at hc
  exact hc.symm

/-- **Existence and uniqueness** of the stationary distribution of a finite irreducible
stochastic matrix. -/
theorem existsUnique_isStationaryDistribution [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) :
    ∃! μ, IsStationaryDistribution P μ := by
  obtain ⟨μ, hμ⟩ := exists_isStationaryDistribution hP0 hP1
  exact ⟨μ, hμ, fun ν hν =>
    hμ.eq_of_vecMul_eq_self hP0 hP1 hirr hν.vecMul_eq hν.sum_eq_one⟩

/-- The solution of Poisson's equation is unique up to an additive constant: two solutions of
`h − Ph = g` differ by a constant. -/
theorem poisson_sub_eq [DecidableEq S] {P : Matrix S S ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j) {g h h' : S → ℝ}
    (hh : ∀ i, h i - (P *ᵥ h) i = g i) (hh' : ∀ i, h' i - (P *ᵥ h') i = g i) (y z : S) :
    h y - h' y = h z - h' z := by
  have hd : P *ᵥ (h - h') = h - h' := by
    funext i
    simp only [mulVec_sub, Pi.sub_apply]
    have := hh i
    have := hh' i
    linarith
  have := eq_of_mulVec_eq_self_of_irreducible hP0 hP1 hirr hd y z
  simpa only [Pi.sub_apply] using this

/-- Poisson's equation has a solution normalised by `μ(h) = 0`. -/
theorem exists_poisson_normalized [Nonempty S] [DecidableEq S] {P : Matrix S S ℝ}
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (hirr : ∀ i j, ∃ k, 0 < (P ^ k) i j)
    {μ : S → ℝ} (hμ : IsStationaryDistribution P μ) (f : S → ℝ) :
    ∃ h : S → ℝ, (∀ i, h i - (P *ᵥ h) i = f i - μ ⬝ᵥ f) ∧ μ ⬝ᵥ h = 0 := by
  obtain ⟨h, hh⟩ := exists_poisson hP0 hP1 hirr hμ f
  refine ⟨fun i => h i - μ ⬝ᵥ h, fun i => ?_, ?_⟩
  · have e : P *ᵥ (fun i => h i - μ ⬝ᵥ h) = P *ᵥ h - fun _ => μ ⬝ᵥ h := by
      have e1 : (fun i => h i - μ ⬝ᵥ h) = h - (μ ⬝ᵥ h) • fun _ => (1 : ℝ) := by
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [e1, mulVec_sub, mulVec_smul, mulVec_const_one hP1]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [e, Pi.sub_apply]
    have := hh i
    linarith
  · rw [dotProduct_sub_const, hμ.sum_eq_one, mul_one, sub_self]

end RQMCMarkov.MarkovDriving
