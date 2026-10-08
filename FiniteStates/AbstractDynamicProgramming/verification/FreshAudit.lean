import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.FixedPoints
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 9 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.AbstractDynamicProgramming

variable {X : Type*} [Fintype X]

/-- A stochastic (Markov) matrix on the finite state space `X` (Vol. 1, p. 71): nonnegative with
unit row sums. -/
structure IsMarkov (P : Matrix X X ℝ) : Prop where
  nonneg : ∀ x x', 0 ≤ P x x'
  rowsum : ∀ x, ∑ x', P x x' = 1

/-- A distribution on `X` (Vol. 1, p. 31): nonnegative and summing to one. -/
structure IsDistribution (ψ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  sum_eq_one : ∑ x, ψ x = 1

/-- `(Ph)(x) = ∑ h(x')P(x, x')`, Vol. 1 (3.12). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

theorem IsMarkov.mul {P Q : Matrix X X ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg x x' := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun z _ => mul_nonneg (hP.nonneg x z) (hQ.nonneg z x')
  rowsum x := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

/-- `Pᵏ` is Markov. -/
theorem IsMarkov.pow [DecidableEq X] {P : Matrix X X ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A Markov matrix preserves `≤` on functions. -/
theorem IsMarkov.mulVec_le_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {f g : X → ℝ} (hfg : f ≤ g) :
    P *ᵥ f ≤ P *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hP.nonneg x x')

/-- `P𝟙 = 𝟙`: constants are fixed by a Markov matrix. -/
theorem IsMarkov.mulVec_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, ← sum_mul, hP.rowsum, one_mul]

/-- `|Ph(x)| ≤ ‖h‖_∞` (Vol. 1, Ex 3.2.1). -/
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

/-- `‖Ph‖_∞ ≤ ‖h‖_∞`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  exact hP.abs_mulVec_le h x

/-- `|(Pf)(x) − (Pg)(x)| ≤ ‖f − g‖_∞`. -/
theorem IsMarkov.abs_mulVec_sub_le {P : Matrix X X ℝ} (hP : IsMarkov P) (f g : X → ℝ) (x : X) :
    |(P *ᵥ f) x - (P *ᵥ g) x| ≤ ‖f - g‖ := by
  have := hP.abs_mulVec_le (f - g) x
  rwa [mulVec_sub, Pi.sub_apply] at this

/-- Global stability (Vol. 1, p. 22). -/
def GloballyStable {U : Type*} [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

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

/-- A contraction on the whole of a complete space is globally stable (Vol. 1, Theorem 1.2.3). -/
theorem globallyStable_univ [CompleteSpace E] (h : IsContractionOn T Set.univ L) :
    GloballyStable T := by
  obtain ⟨u', -, hu'⟩ := h.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  exact ⟨u', hu', fun v hv => h.fixedPt_unique (Set.mem_univ v) (Set.mem_univ u') hv hu',
    fun u => h.tendsto_iterate_fixedPt (Set.mem_univ u) (Set.mem_univ u') hu'⟩

end IsContractionOn

omit [Fintype X] in
/-- Vol. 1, Proposition 2.2.7, in the form used here: if `S ≤ T` pointwise, `T` is order
preserving and its iterates from any point converge to `u_T`, then every fixed point of `S` lies
below `u_T`. The ambient space is `ℝ^X` with the pointwise order. -/
theorem fixedPt_le_of_le {S T : (X → ℝ) → (X → ℝ)} (hST : ∀ v, S v ≤ T v) (hT : Monotone T)
    {uS uT : X → ℝ} (huS : IsFixedPt S uS) (hlim : Tendsto (fun k : ℕ => T^[k] uS) atTop (𝓝 uT)) :
    uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

omit [Fintype X] in
/-- If `u ≤ Tu`, `T` is order preserving and `Tᵏu → u*`, then `u ≤ u*`: the monotone-improvement
step behind Howard policy iteration. -/
theorem le_fixedPt_of_le_apply {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T) {u u' : X → ℝ}
    (hu : u ≤ T u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) : u ≤ u' := by
  have hle : ∀ k : ℕ, u ≤ T^[k] u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hu.trans (hT ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

/-- Blackwell's condition (Vol. 1, Lemma 2.2.4) on all of `ℝ^X`: an order-preserving `T` with
`T(u + c) ≤ Tu + βc` for `c ≥ 0` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmono : Monotone T)
    (hdisc : ∀ u : X → ℝ, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T Set.univ β := by
  refine ⟨Set.mapsTo_univ _ _, hβ0, hβ1, fun u _ v _ => ?_⟩
  have key : ∀ u v : X → ℝ, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u v x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono hle x
    have h2 := hdisc v ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u v x, ?_⟩
  have := key v u x
  rwa [norm_sub_rev] at this

omit [Fintype X] in
/-- Vol. 1, Lemma 2.2.2: for a nonempty finite `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} {s : Finset D} (hs : s.Nonempty) (f g : D → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs fun z => |f z - g z| := by
  have key : ∀ f g : D → ℝ, s.sup' hs f - s.sup' hs g ≤ s.sup' hs fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs f fun z hz => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (s.sup' hs fun z => |f z - g z|) + s.sup' hs g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) hz) (Finset.le_sup' g hz)
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

The spectral radius `ρ(A)` of Vol. 1 (1.15) and the facts about it that
Chapters 6–9 use: Gelfand's formula (Lemma 1.2.2), the eventual bound
`‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1), invariance
under transposition, monotonicity in the entries (Exercise 2.2.28), and the
row-sum characterisations of the ℓ∞ operator norm. These are the results of
the `FiniteStates/OperatorsFixedPoints` project restated for a matrix indexed by
an arbitrary finite type `X`, as Chapter 6 needs them on product state spaces
`Y × Z`; each chapter project is self-contained.
-/

open Filter Topology Matrix Finset

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries {A : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ)
    (i j : X) : 0 ≤ (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hA i l) (ih l j)

/-- Exercise 2.2.28 (p. 60), first part: `0 ≤ A ≤ B` implies `Aᵏ ≤ Bᵏ` for all `k`. -/
theorem pow_le_pow_entries {A B : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) (i j : X) : (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    exact sum_le_sum fun l _ =>
      mul_le_mul (hAB i l) (ih l j) (pow_nonneg_entries hA k l j) ((hA i l).trans (hAB i l))




/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ :=
  A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) :
    complexify A i j = (A i j : ℂ) := by
  classical
  exact rfl

theorem complexify_pow (A : Matrix X X ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := X)) A k

omit [Fintype X] [DecidableEq X] in
theorem complexify_transpose (A : Matrix X X ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := by
  classical
  ext i j
  rfl

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (Vol. 1, (1.15)): the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

omit [DecidableEq X] in
theorem spectralRadius_complexify_ne_top [Nonempty X] (A : Matrix X X ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  classical
  exact
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

omit [DecidableEq X] in
theorem specRad_nonneg (A : Matrix X X ℝ) : 0 ≤ specRad A := by
  classical
  exact ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix X X ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ ∃ e : X → ℂ, e ≠ 0 ∧ complexify A *ᵥ e = μ • e := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
    exact h.symm

/-- Gelfand's formula (Vol. 1, Lemma 1.2.2) for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [Nonempty X] (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`. -/
theorem eventually_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- `ρ(A) < 1` implies `‖Aᵏ‖ → 0`. -/
theorem tendsto_norm_pow_zero [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_norm_pow_le A hr1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)

/-- `ρ(A) < 1` implies `∑ₖ Aᵏ` converges. -/
theorem summable_pow [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    Summable fun k : ℕ => A ^ k := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2)
    (eventually_norm_pow_le A hr1)

/-- `(I − A) ∑ₖ Aᵏ = I` when the series converges. -/
theorem one_sub_mul_tsum (A : Matrix X X ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (1 - A) * ∑' k : ℕ, A ^ k = 1 := by
  have h1 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop
      (𝓝 ((1 - A) * ∑' k : ℕ, A ^ k)) :=
    hs.hasSum.tendsto_sum_nat.const_mul (1 - A)
  have h2 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop (𝓝 1) := by
    simp_rw [mul_neg_geom_sum]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

theorem tsum_mul_one_sub (A : Matrix X X ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (∑' k : ℕ, A ^ k) * (1 - A) = 1 := by
  have h1 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop
      (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have h2 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop (𝓝 1) := by
    simp_rw [geom_sum_mul_neg]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- The Neumann series lemma (Vol. 1, Theorem 1.2.1): `ρ(A) < 1` implies `I − A` is invertible with
inverse `∑ₖ Aᵏ`. -/
theorem neumann_series [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  ⟨⟨⟨1 - A, ∑' k : ℕ, A ^ k, one_sub_mul_tsum A (summable_pow A hρ),
    tsum_mul_one_sub A (summable_pow A hρ)⟩, rfl⟩,
    Matrix.inv_eq_right_inv (one_sub_mul_tsum A (summable_pow A hρ))⟩

omit [DecidableEq X] in
/-- `ρ(Aᵀ) = ρ(A)`. -/
theorem specRad_transpose (A : Matrix X X ℝ) : specRad Aᵀ = specRad A := by
  classical
  unfold specRad
  rw [complexify_transpose, Matrix.spectralRadius_transpose]

/-- The ℓ∞ operator norm is monotone in the absolute values of the entries. -/
theorem norm_le_norm_of_abs_le {A B : Matrix X X ℝ} (h : ∀ i j, |A i j| ≤ |B i j|) :
    ‖A‖ ≤ ‖B‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  norm_cast
  refine Finset.sup_mono_fun fun i _ => sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h i j

omit [DecidableEq X] in
/-- Exercise 2.2.28 (p. 60), second half: `0 ≤ A ≤ B` implies `ρ(A) ≤ ρ(B)`, by Gelfand's
formula and `‖Aᵏ‖ ≤ ‖Bᵏ‖`. -/
theorem specRad_le_of_le [Nonempty X] {A B : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) : specRad A ≤ specRad B := by
  classical
  refine le_of_tendsto_of_tendsto' (tendsto_norm_pow_rpow A) (tendsto_norm_pow_rpow B) fun k => ?_
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)
  refine norm_le_norm_of_abs_le fun i j => ?_
  have hAk := pow_nonneg_entries hA k i j
  have hBk := (pow_nonneg_entries hA k i j).trans (pow_le_pow_entries hA hAB k i j)
  rw [abs_of_nonneg hAk, abs_of_nonneg hBk]
  exact pow_le_pow_entries hA hAB k i j

/-- Row sums of absolute values are bounded by the ℓ∞ operator norm. -/
theorem rowsum_abs_le_norm (A : Matrix X X ℝ) (i : X) : ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : (∑ j, ‖A i j‖₊ : NNReal) ≤ univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h := NNReal.coe_le_coe.2 this
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h

/-- The ℓ∞ operator norm is bounded by a bound on the row sums of absolute values. -/
theorem norm_le_of_rowsum_abs_le (A : Matrix X X ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    have hi := h i
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖A i j‖₊) (r₂ := c.toNNReal)).1
      (by simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal c hc] using hi)
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal c hc] at h2

/-- Each entry is bounded in absolute value by the ℓ∞ operator norm. -/
theorem abs_entry_le_norm (A : Matrix X X ℝ) (i j : X) : |A i j| ≤ ‖A‖ :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (mem_univ j)).trans (rowsum_abs_le_norm A i)

/-- For `A ≥ 0` with all row sums equal to `c`, `‖A‖ = c`. -/
theorem norm_eq_of_rowsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : ‖A‖ = c := by
  have habs : ∀ i, ∑ j, |A i j| = c := fun i => by
    rw [← h i]
    exact sum_congr rfl fun j _ => abs_of_nonneg (hA i j)
  refine le_antisymm (norm_le_of_rowsum_abs_le A hc fun i => (habs i).le) ?_
  obtain ⟨i⟩ : Nonempty X := inferInstance
  exact (habs i).symm.le.trans (rowsum_abs_le_norm A i)

/-- `ρ(A) ≤ ‖A‖`. -/
theorem specRad_le_norm [Nonempty X] (A : Matrix X X ℝ) : specRad A ≤ ‖A‖ := by
  have := ENNReal.toReal_mono ENNReal.coe_ne_top
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (complexify A))
  rwa [ENNReal.coe_toReal, coe_nnnorm, norm_complexify] at this

/-- Every eigenvalue is bounded in modulus by the spectral radius. -/
theorem norm_le_specRad_of_mem_spectrum [Nonempty X] (A : Matrix X X ℝ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify A)) : ‖μ‖ ≤ specRad A := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h1 : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify A) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ENNReal)) μ hμ
  have := ENNReal.toReal_mono (spectralRadius_complexify_ne_top A) h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

omit [DecidableEq X] in
/-- For `A ≥ 0` with all row sums equal to `c`, `ρ(A) = c`: the constant vector is an eigenvector
with eigenvalue `c`, and `‖A‖ = c`. -/
theorem specRad_eq_of_rowsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : specRad A = c := by
  classical
  refine le_antisymm ((specRad_le_norm A).trans (norm_eq_of_rowsum_eq A hA hc h).le) ?_
  have hmem : (c : ℂ) ∈ spectrum ℂ (complexify A) := by
    rw [mem_spectrum_iff_eigenpair]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      have := congrFun h0 (Classical.arbitrary X)
      simp at this
    · funext i
      simp only [mulVec, dotProduct, complexify_apply, mul_one, Pi.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_sum, h i]
  have := norm_le_specRad_of_mem_spectrum A hmem
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at this

omit [DecidableEq X] in
/-- For `A ≥ 0` with all column sums equal to `c`, `ρ(A) = c`, by transposition. -/
theorem specRad_eq_of_colsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ∑ i, A i j = c) : specRad A = c := by
  classical
  rw [← specRad_transpose]
  exact specRad_eq_of_rowsum_eq Aᵀ (fun i j => hA j i) hc h

/-- Entrywise Gelfand bound: for `r > ρ(A)`, `|(Aᵏ)ᵢⱼ| ≤ rᵏ` for all large `k`. -/
theorem eventually_abs_entry_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : X) : ∀ᶠ k : ℕ in atTop, |(A ^ k) i j| ≤ r ^ k :=
  (eventually_norm_pow_le A hr).mono fun k hk => (abs_entry_le_norm (A ^ k) i j).trans hk

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The resolvent series, entrywise

For a square matrix `M` over `ℝ` or `ℂ` and a scalar `z` with `|z|` larger than
a bound `r` on the growth of the entries of `Mᵏ`, the series
`∑ₖ z^{−(k+1)} Mᵏ` converges entry by entry to a two-sided inverse of `zI − M`.
This is the Neumann series of Vol. 1, Theorem 1.2.1, written out at the level
of entries so that no topology on the matrix space is needed: partial sums
telescope, `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`, and the correction
term vanishes entrywise.

The Perron–Frobenius argument of `PerronFrobenius` applies this to a
nonnegative real matrix `A` at a real `t > ρ(A)`, where the entries of the
resolvent are nonnegative, and to its complexification at a complex `z` with
`|z| = t`, where they are dominated by the real ones.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.AbstractDynamicProgramming

variable {X : Type*} [Fintype X] [DecidableEq X] {𝕜 : Type*} [RCLike 𝕜]

/-- The partial sums `∑_{k<K} z^{−(k+1)} Mᵏ` of the resolvent series. -/
def resPartial (M : Matrix X X 𝕜) (z : 𝕜) (K : ℕ) : Matrix X X 𝕜 :=
  ∑ k ∈ range K, (z⁻¹) ^ (k + 1) • M ^ k

/-- The resolvent series, entry by entry: `R(z)ᵢⱼ = ∑ₖ z^{−(k+1)} (Mᵏ)ᵢⱼ`. -/
noncomputable def res (M : Matrix X X 𝕜) (z : 𝕜) : Matrix X X 𝕜 :=
  Matrix.of fun i j => ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j

theorem res_apply (M : Matrix X X 𝕜) (z : 𝕜) (i j : X) :
    res M z i j = ∑' k : ℕ, (z⁻¹) ^ (k + 1) * (M ^ k) i j := rfl

/-- Telescoping: `(zI − M) ∑_{k<K} z^{−(k+1)} Mᵏ = I − z^{−K} Mᴷ`. -/
theorem smul_one_sub_mul_resPartial (M : Matrix X X 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    (z • (1 : Matrix X X 𝕜) - M) * resPartial M z K = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, mul_add, ih, Matrix.mul_smul, sub_mul,
      Matrix.smul_mul, one_mul, ← pow_succ', smul_sub, hc]
    abel

/-- Telescoping on the other side: `(∑_{k<K} z^{−(k+1)} Mᵏ)(zI − M) = I − z^{−K} Mᴷ`. -/
theorem resPartial_mul_smul_one_sub (M : Matrix X X 𝕜) {z : 𝕜} (hz : z ≠ 0) (K : ℕ) :
    resPartial M z K * (z • (1 : Matrix X X 𝕜) - M) = 1 - (z⁻¹) ^ K • M ^ K := by
  induction K with
  | zero => simp [resPartial]
  | succ K ih =>
    have hc : (z⁻¹) ^ (K + 1) • (z • M ^ K) = (z⁻¹) ^ K • M ^ K := by
      rw [smul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [resPartial, sum_range_succ, ← resPartial, add_mul, ih, Matrix.smul_mul, mul_sub,
      Matrix.mul_smul, mul_one, ← pow_succ, smul_sub, hc]
    abel

/-- The entry of a partial sum is the partial sum of the entries. -/
theorem resPartial_apply (M : Matrix X X 𝕜) (z : 𝕜) (K : ℕ) (i j : X) :
    resPartial M z K i j = ∑ k ∈ range K, (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  simp [resPartial, Matrix.sum_apply]

/-- Under an eventual bound `‖(Mᵏ)ᵢⱼ‖ ≤ rᵏ` with `r < |z|`, the entry series is summable. -/
theorem summable_res_entry (M : Matrix X X 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : X) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Summable fun k : ℕ => (z⁻¹) ^ (k + 1) * (M ^ k) i j := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_geometric_of_lt_one hq0 hq).mul_left ‖z‖⁻¹) (hM.mono fun k hk => ?_)
  rw [norm_mul, norm_pow, norm_inv, div_pow, pow_succ, ← div_eq_mul_inv]
  calc ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * ‖(M ^ k) i j‖ ≤ ‖z‖⁻¹ ^ k * ‖z‖⁻¹ * r ^ k := by gcongr
    _ = ‖z‖⁻¹ * (r ^ k / ‖z‖ ^ k) := by
        rw [div_eq_mul_inv, ← inv_pow]
        ring

/-- The partial sums converge entrywise to the resolvent series. -/
theorem tendsto_resPartial_apply (M : Matrix X X 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : X) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K => resPartial M z K i j) atTop (𝓝 (res M z i j)) := by
  simp only [resPartial_apply, res_apply]
  exact (summable_res_entry M hr hz i j hM).hasSum.tendsto_sum_nat

/-- The correction term `z^{−K} (Mᴷ)ᵢⱼ` vanishes. -/
theorem tendsto_inv_pow_mul_apply (M : Matrix X X 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (i j : X) (hM : ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    Tendsto (fun K : ℕ => (z⁻¹) ^ K * (M ^ K) i j) atTop (𝓝 0) := by
  have hz0 : 0 < ‖z‖ := hr.trans_lt hz
  have hq : r / ‖z‖ < 1 := (div_lt_one hz0).2 hz
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hz0.le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (hM.mono fun K hK => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq)
  rw [norm_mul, norm_pow, norm_inv, div_pow, div_eq_mul_inv, ← inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- The resolvent series is a right inverse: `(zI − M) R(z) = I`. -/
theorem smul_one_sub_mul_res (M : Matrix X X 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    (z • (1 : Matrix X X 𝕜) - M) * res M z = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  -- the partial products converge to both sides
  have h1 : Tendsto (fun K => ((z • (1 : Matrix X X 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 (((z • (1 : Matrix X X 𝕜) - M) * res M z) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      tendsto_const_nhds.mul (tendsto_resPartial_apply M hr hz l j (hM l j))
  have h2 : Tendsto (fun K => ((z • (1 : Matrix X X 𝕜) - M) * resPartial M z K) i j)
      atTop (𝓝 ((1 : Matrix X X 𝕜) i j)) := by
    simp only [smul_one_sub_mul_resPartial M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-- The resolvent series is a left inverse: `R(z)(zI − M) = I`. -/
theorem res_mul_smul_one_sub (M : Matrix X X 𝕜) {z : 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hz : r < ‖z‖) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(M ^ k) i j‖ ≤ r ^ k) :
    res M z * (z • (1 : Matrix X X 𝕜) - M) = 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact absurd hz (not_lt.2 hr)
  ext i j
  have h1 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix X X 𝕜) - M)) i j)
      atTop (𝓝 ((res M z * (z • (1 : Matrix X X 𝕜) - M)) i j)) := by
    simp only [Matrix.mul_apply]
    exact tendsto_finsetSum _ fun l _ =>
      (tendsto_resPartial_apply M hr hz i l (hM i l)).mul tendsto_const_nhds
  have h2 : Tendsto (fun K => (resPartial M z K * (z • (1 : Matrix X X 𝕜) - M)) i j)
      atTop (𝓝 ((1 : Matrix X X 𝕜) i j)) := by
    simp only [resPartial_mul_smul_one_sub M hz0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    simpa using tendsto_const_nhds.sub (tendsto_inv_pow_mul_apply M hr hz i j (hM i j))
  exact tendsto_nhds_unique h1 h2

/-! ### The real resolvent of a nonnegative matrix -/

/-- For `A ≥ 0` and `t > 0`, the entries of the resolvent series are nonnegative. -/
theorem res_nonneg {A : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 < t)
    (i j : X) : 0 ≤ res A t i j :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (inv_nonneg.2 ht.le) _) (pow_nonneg_entries hA k i j)

/-- For `A ≥ 0` and `t > 0`, each entry of the resolvent dominates the first term `1/t` of the
diagonal series: `R(t)ᵢᵢ ≥ 1/t`. -/
theorem inv_le_res_diag [Nonempty X] {A : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j) {t r : ℝ}
    (hr : 0 ≤ r) (ht : r < t) (hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k) (i : X) :
    t⁻¹ ≤ res A t i i := by
  have ht0 : 0 < t := hr.trans_lt ht
  have hs := summable_res_entry A hr (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i i (hM i i)
  rw [res_apply]
  have h0 : (t⁻¹) ^ (0 + 1) * (A ^ 0) i i = t⁻¹ := by simp
  calc t⁻¹ = (t⁻¹) ^ (0 + 1) * (A ^ 0) i i := h0.symm
    _ ≤ ∑' k : ℕ, (t⁻¹) ^ (k + 1) * (A ^ k) i i :=
        hs.le_tsum 0 fun k _ =>
          mul_nonneg (pow_nonneg (inv_nonneg.2 ht0.le) _) (pow_nonneg_entries hA k i i)

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Perron–Frobenius theorem for nonnegative matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), the part for nonnegative matrices: if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector `e` and a
nonnegative, nonzero left eigenvector `ε`. The book quotes the theorem from
Meyer (2000); the proof here is through the resolvent.

* A complex eigenvalue `μ` of modulus `ρ(A)` exists, since the spectrum is
  finite and nonempty.
* For `|z| = t > ρ(A)` the complex resolvent `(zI − A)⁻¹ = ∑ z^{−(k+1)}Aᵏ` is
  dominated entrywise by the real resolvent `(tI − A)⁻¹ ≥ 0`.
* If the real resolvent stayed bounded on `(ρ, ρ + δ)`, then along `z = (1+s)μ`
  the complex resolvent would stay bounded while `z → μ`, and a Neumann-series
  perturbation would make `μI − A` invertible: `μ` could not be in the
  spectrum. Hence the real resolvent is unbounded near `ρ`.
* Normalising `(tI − A)⁻¹𝟙` to the simplex and letting `t ↓ ρ` along a sequence
  where the entries blow up, compactness of the simplex yields a limit `e ≥ 0`
  with `∑ e = 1` and `(ρI − A)e = 0`.

The statements for irreducible and everywhere-positive matrices (positivity and
uniqueness of the eigenvectors, the convergence (2.11)) are not claimed here;
the irreducible case is proved in `Irreducible`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A complex eigenvalue of maximal modulus exists: `‖μ‖ = ρ(A)` for some `μ` in the spectrum. -/
theorem exists_mem_spectrum_norm_eq (A : Matrix X X ℝ) :
    ∃ μ ∈ spectrum ℂ (complexify A), ‖μ‖ = specRad A := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have hne : (spectrum ℂ (complexify A)).Nonempty := spectrum.nonempty _
  have hfin : (spectrum ℂ (complexify A)).Finite := Matrix.finite_spectrum _
  obtain ⟨μ₀, hμ₀⟩ := hne
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun z => ‖z‖)
    ⟨μ₀, hfin.mem_toFinset.2 hμ₀⟩
  have hμ' : μ ∈ spectrum ℂ (complexify A) := hfin.mem_toFinset.1 hμ
  refine ⟨μ, hμ', le_antisymm (norm_le_specRad_of_mem_spectrum A hμ') ?_⟩
  have h1 : spectralRadius ℂ (complexify A) ≤ (‖μ‖₊ : ENNReal) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    refine iSup₂_le fun z hz => ?_
    exact_mod_cast hmax z (hfin.mem_toFinset.2 hz)
  have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

/-- Entrywise Gelfand bound for the complexification. -/
theorem eventually_norm_entry_pow_complexify_le (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : X) :
    ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k :=
  (eventually_abs_entry_pow_le A hr i j).mono fun k hk => by
    rw [← complexify_pow, complexify_apply, Complex.norm_real, Real.norm_eq_abs]
    exact hk

/-- The real resolvent series at `t > ρ(A)` is a two-sided inverse of `tI − A`. -/
theorem smul_one_sub_mul_res_real (A : Matrix X X ℝ) {t : ℝ} (hρ : specRad A < t) :
    (t • (1 : Matrix X X ℝ) - A) * res A t = 1 ∧
      res A t * (t • (1 : Matrix X X ℝ) - A) = 1 := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrt : r < ‖t‖ := by rwa [Real.norm_eq_abs, abs_of_pos (hr0.trans_lt hr2)]
  have hM : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ r ^ k := fun i j =>
    (eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs]
  exact ⟨smul_one_sub_mul_res A hr0 hrt hM, res_mul_smul_one_sub A hr0 hrt hM⟩

/-- Domination: for `|z| = t > ρ(A)`, `|R_ℂ(z)ᵢⱼ| ≤ R_ℝ(t)ᵢⱼ`. -/
theorem norm_res_complexify_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {z : ℂ}
    {t : ℝ} (hzt : ‖z‖ = t) (hρ : specRad A < t) (i j : X) :
    ‖res (complexify A) z i j‖ ≤ res A t i j := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have ht0 : 0 < t := hr0.trans_lt hr2
  have hterm : ∀ k : ℕ, ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ =
      (t⁻¹) ^ (k + 1) * (A ^ k) i j := by
    intro k
    rw [norm_mul, norm_pow, norm_inv, hzt, ← complexify_pow, complexify_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg_entries hA k i j)]
  have hreal : Summable fun k : ℕ => (t⁻¹) ^ (k + 1) * (A ^ k) i j :=
    summable_res_entry A hr0 (by rwa [Real.norm_eq_abs, abs_of_pos ht0]) i j
      ((eventually_abs_entry_pow_le A hr1 i j).mono fun k hk => by rwa [Real.norm_eq_abs])
  have hnorm : Summable fun k : ℕ => ‖(z⁻¹) ^ (k + 1) * ((complexify A) ^ k) i j‖ := by
    simp_rw [hterm]
    exact hreal
  rw [res_apply, res_apply]
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq ?_)
  exact tsum_congr hterm

omit [Nonempty X] in
/-- The ℓ∞ operator norm of a complex matrix is bounded by `n` times a bound on its entries. -/
theorem norm_le_card_mul_of_entry_norm_le (M' : Matrix X X ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, ‖M' i j‖ ≤ M) : ‖M'‖ ≤ Fintype.card X * M := by
  rw [Matrix.linfty_opNorm_def]
  have hnM : (0 : ℝ) ≤ Fintype.card X * M := by positivity
  have hrow : ∀ i, (∑ j, ‖M' i j‖₊ : NNReal) ≤ (Fintype.card X * M).toNNReal := by
    intro i
    refine (NNReal.coe_le_coe (r₁ := ∑ j, ‖M' i j‖₊) (r₂ := (Fintype.card X * M).toNNReal)).1 ?_
    rw [NNReal.coe_sum, Real.coe_toNNReal _ hnM]
    simp only [coe_nnnorm]
    calc ∑ j, ‖M' i j‖ ≤ ∑ _j : X, M := sum_le_sum fun j _ => h i j
      _ = Fintype.card X * M := by simp
  have hsup : (univ.sup fun i => ∑ j, ‖M' i j‖₊) ≤ (Fintype.card X * M).toNNReal :=
    Finset.sup_le fun i _ => hrow i
  have := NNReal.coe_le_coe.2 hsup
  rwa [Real.coe_toNNReal _ hnM] at this

/-- If the real resolvent were bounded on `(ρ, ρ + δ)`, no complex number of modulus `ρ > 0`
could be in the spectrum: along `z = (1 + s)μ → μ` the complex resolvent stays bounded, and a
Neumann perturbation makes `μI − A` invertible. -/
theorem notMem_spectrum_of_res_bounded (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hρpos : 0 < specRad A) {μ : ℂ} (hμ : ‖μ‖ = specRad A) {M δ : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M)
    (hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M) :
    μ ∉ spectrum ℂ (complexify A) := by
  set ρ := specRad A with hρ
  set C : ℝ := Fintype.card X * M + 1 with hC
  have hCpos : 0 < C := by positivity
  -- the step `s`
  set ε : ℝ := min δ (1 / C) with hε
  have hεpos : 0 < ε := lt_min hδ (by positivity)
  set s : ℝ := ε / (2 * ρ) with hs
  have hspos : 0 < s := by positivity
  have hsρ : s * ρ = ε / 2 := by rw [hs]; field_simp
  have hsρδ : s * ρ < δ := by rw [hsρ]; linarith [min_le_left δ (1 / C)]
  have hsρC : s * ρ * C < 1 := by
    rw [hsρ]
    have : ε ≤ 1 / C := min_le_right _ _
    have : ε * C ≤ 1 := by rwa [le_div_iff₀ hCpos] at this
    linarith
  -- the point `z = (1 + s) μ`, of modulus `t = (1 + s) ρ`
  set z : ℂ := ((1 + s : ℝ) : ℂ) * μ with hz
  set t : ℝ := (1 + s) * ρ with ht
  have hzt : ‖z‖ = t := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hμ]
  have hρt : ρ < t := by rw [ht]; nlinarith
  have htδ : t < ρ + δ := by rw [ht]; nlinarith
  -- the complex resolvent at `z` is a two-sided inverse and is bounded
  obtain ⟨r, hr1, hr2⟩ := exists_between hρt
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  have hrz : r < ‖z‖ := by rw [hzt]; exact hr2
  have hMc : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖((complexify A) ^ k) i j‖ ≤ r ^ k := fun i j =>
    eventually_norm_entry_pow_complexify_le A hr1 i j
  set R := res (complexify A) z with hR
  have hR1 : (z • (1 : Matrix X X ℂ) - complexify A) * R = 1 :=
    smul_one_sub_mul_res (complexify A) hr0 hrz hMc
  have hR2 : R * (z • (1 : Matrix X X ℂ) - complexify A) = 1 :=
    res_mul_smul_one_sub (complexify A) hr0 hrz hMc
  have hRnorm : ‖R‖ ≤ Fintype.card X * M :=
    norm_le_card_mul_of_entry_norm_le R hM0 fun i j =>
      (norm_res_complexify_le A hA hzt hρt i j).trans (hM t hρt htδ i j)
  -- the perturbation `(z − μ) • R` has norm `< 1`
  have hzμ : z - μ = ((s : ℝ) : ℂ) * μ := by rw [hz]; push_cast; ring
  have hpert : ‖(z - μ) • R‖ < 1 := by
    rw [norm_smul, hzμ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le, hμ]
    calc s * ρ * ‖R‖ ≤ s * ρ * (Fintype.card X * M) := by gcongr
      _ < s * ρ * C := by rw [hC]; nlinarith
      _ < 1 := hsρC
  -- `μI − A = (zI − A)(I − (z − μ)R)`, a product of units
  have hfactor : (z • (1 : Matrix X X ℂ) - complexify A) * (1 - (z - μ) • R) =
      μ • (1 : Matrix X X ℂ) - complexify A := by
    calc (z • (1 : Matrix X X ℂ) - complexify A) * (1 - (z - μ) • R)
        = (z • (1 : Matrix X X ℂ) - complexify A) -
            (z - μ) • ((z • (1 : Matrix X X ℂ) - complexify A) * R) := by
          rw [mul_sub, mul_one, Matrix.mul_smul]
      _ = (z • (1 : Matrix X X ℂ) - complexify A) -
            (z - μ) • (1 : Matrix X X ℂ) := by rw [hR1]
      _ = μ • (1 : Matrix X X ℂ) - complexify A := by
          rw [sub_smul]
          abel
  have hunit1 : IsUnit (z • (1 : Matrix X X ℂ) - complexify A) :=
    ⟨⟨z • 1 - complexify A, R, hR1, hR2⟩, rfl⟩
  have hunit2 : IsUnit (1 - (z - μ) • R) := (Units.oneSub ((z - μ) • R) hpert).isUnit
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, ← hfactor]
  exact hunit1.mul hunit2

/-- The real resolvent is unbounded as `t ↓ ρ(A)`: for every bound `M` and every `δ > 0` some
entry of `R(t)` exceeds `M` at some `t ∈ (ρ, ρ + δ)`. -/
theorem exists_res_entry_gt (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) (M : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, specRad A < t ∧ t < specRad A + δ ∧ ∃ i j, M < res A t i j := by
  rcases (specRad_nonneg A).lt_or_eq with hρpos | hρ0
  · by_contra hcon
    have hM : ∀ t, specRad A < t → t < specRad A + δ → ∀ i j, res A t i j ≤ M :=
      fun t h1 h2 i j => le_of_not_gt fun hgt => hcon ⟨t, h1, h2, i, j, hgt⟩
    have hM0 : 0 ≤ M := by
      have h1 : specRad A < specRad A + δ / 2 := by linarith
      have h2 : specRad A + δ / 2 < specRad A + δ := by linarith
      exact (res_nonneg hA (hρpos.trans h1) (Classical.arbitrary X) (Classical.arbitrary X)).trans
        (hM _ h1 h2 _ _)
    obtain ⟨μ, hμmem, hμ⟩ := exists_mem_spectrum_norm_eq A
    exact notMem_spectrum_of_res_bounded A hA hρpos hμ hδ hM0 hM hμmem
  · -- `ρ = 0`: the diagonal entries are at least `1/t`
    have hρ : specRad A = 0 := hρ0.symm
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (δ / 2) (1 / (2 * (|M| + 1))) := ⟨_, rfl⟩
    have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by positivity)
    have htδ : t < δ := by rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
    have htM : t ≤ 1 / (2 * (|M| + 1)) := by rw [ht]; exact min_le_right _ _
    refine ⟨t, by rw [hρ]; exact htpos, by rw [hρ]; linarith, (Classical.arbitrary X),
      (Classical.arbitrary X), ?_⟩
    have hbound : ∀ i j, ∀ᶠ k : ℕ in atTop, ‖(A ^ k) i j‖ ≤ (t / 2) ^ k := fun i j =>
      (eventually_abs_entry_pow_le A (r := t / 2) (by rw [hρ]; positivity) i j).mono
        fun k hk => by rwa [Real.norm_eq_abs]
    have hdiag := inv_le_res_diag hA (r := t / 2) (by positivity) (half_lt_self htpos) hbound
      (Classical.arbitrary X)
    have h2 : 2 * (|M| + 1) ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by positivity) htpos]
      simpa [one_div] using htM
    have hMabs : M ≤ |M| := le_abs_self M
    have habs0 : 0 ≤ |M| := abs_nonneg M
    linarith

omit [Nonempty X] [DecidableEq X] in
/-- The simplex `{y ≥ 0 : ∑ y = 1}` is compact. -/
theorem isCompact_simplex :
    IsCompact {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
  classical
  have hsub : {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ⊆ Set.Icc 0 1 := by
    rintro y ⟨hy0, hy1⟩
    refine ⟨fun i => hy0 i, fun i => ?_⟩
    calc y i ≤ ∑ j, y j := single_le_sum (fun j _ => hy0 j) (mem_univ i)
      _ = 1 := hy1
  have hclosed : IsClosed {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    have h1 : IsClosed {y : X → ℝ | ∀ i, 0 ≤ y i} := by
      have : {y : X → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y | 0 ≤ y i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {y : X → ℝ | ∑ i, y i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

omit [DecidableEq X] in
/-- **Theorem 2.3.1 (Perron–Frobenius), nonnegative case** (p. 69): if `A ≥ 0` then `ρ(A)` is an
eigenvalue of `A` with a nonnegative, nonzero right eigenvector. -/
theorem perron_frobenius (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ e : X → ℝ, (∀ i, 0 ≤ e i) ∧ e ≠ 0 ∧ A *ᵥ e = specRad A • e := by
  classical
  set ρ := specRad A with hρ
  -- a sequence `tₖ ↓ ρ` along which some entry of `R(tₖ)` exceeds `k`
  choose t ht using fun k : ℕ => exists_res_entry_gt A hA (k : ℝ) (δ := 1 / (k + 1))
    (by positivity)
  have htρ : ∀ k, ρ < t k := fun k => (ht k).1
  have htlim : Tendsto t atTop (𝓝 ρ) := by
    have h1 : ∀ k, t k ≤ ρ + 1 / ((k : ℝ) + 1) := fun k => (ht k).2.1.le
    have h2 : Tendsto (fun k : ℕ => ρ + 1 / ((k : ℝ) + 1)) atTop (𝓝 (ρ + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun k => (htρ k).le) h1
  -- the row-sum vectors `vₖ = R(tₖ)𝟙 ≥ 0` and their totals `Nₖ > k`
  set v : ℕ → X → ℝ := fun k i => ∑ j, res A (t k) i j with hv
  have hv_eq : ∀ k, v k = res A (t k) *ᵥ fun _ => 1 := by
    intro k
    funext i
    simp [hv, mulVec, dotProduct]
  have hv0 : ∀ k i, 0 ≤ v k i := fun k i =>
    sum_nonneg fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j
  set N : ℕ → ℝ := fun k => ∑ i, v k i with hN
  have hNgt : ∀ k : ℕ, (k : ℝ) < N k := by
    intro k
    obtain ⟨i, j, hij⟩ := (ht k).2.2
    calc (k : ℝ) < res A (t k) i j := hij
      _ ≤ v k i := single_le_sum
            (fun j _ => res_nonneg hA ((specRad_nonneg A).trans_lt (htρ k)) i j) (mem_univ j)
      _ ≤ N k := single_le_sum (fun i _ => hv0 k i) (mem_univ i)
  have hNpos : ∀ k, 0 < N k := fun k => (Nat.cast_nonneg k).trans_lt (hNgt k)
  -- `(tₖ I − A) vₖ = 𝟙`
  have hres : ∀ k, (t k • (1 : Matrix X X ℝ) - A) *ᵥ v k = fun _ => 1 := by
    intro k
    rw [hv_eq, mulVec_mulVec, (smul_one_sub_mul_res_real A (htρ k)).1, one_mulVec]
  -- the normalised vectors lie in the simplex
  set y : ℕ → X → ℝ := fun k => (N k)⁻¹ • v k with hy
  have hyS : ∀ k, y k ∈ {y : X → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    intro k
    refine ⟨fun i => mul_nonneg (inv_nonneg.2 (hNpos k).le) (hv0 k i), ?_⟩
    simp only [hy, Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ (hNpos k).ne'
  obtain ⟨e, heS, φ, hφ, hlim⟩ := isCompact_simplex.tendsto_subseq hyS
  refine ⟨e, heS.1, ?_, ?_⟩
  · intro he
    have := heS.2
    rw [he] at this
    simp at this
  · -- `(tₖ I − A) yₖ = Nₖ⁻¹ 𝟙 → 0`, and the left side tends to `(ρI − A) e`
    have hφlim : Tendsto (fun k => t (φ k)) atTop (𝓝 ρ) := htlim.comp hφ.tendsto_atTop
    have hNinv : Tendsto (fun k => (N (φ k))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => N (φ k)) atTop atTop :=
        tendsto_atTop_mono (fun k => (hNgt (φ k)).le)
          (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      exact tendsto_inv_atTop_zero.comp h1
    funext i
    -- the `i`-th coordinate of `(tₖI − A) yₖ`
    have hcoord : ∀ k, (t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k) =
        (N (φ k))⁻¹ • fun _ => (1 : ℝ) := by
      intro k
      simp only [hy, mulVec_smul, hres]
    have h1 : Tendsto (fun k => ((t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 (((ρ • (1 : Matrix X X ℝ) - A) *ᵥ e) i)) := by
      simp only [mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine tendsto_finsetSum _ fun x _ => ?_
      exact ((hφlim.mul tendsto_const_nhds).sub tendsto_const_nhds).mul
        (tendsto_pi_nhds.1 hlim x)
    have h2 : Tendsto (fun k => ((t (φ k) • (1 : Matrix X X ℝ) - A) *ᵥ y (φ k)) i)
        atTop (𝓝 0) := by
      simp only [hcoord, Pi.smul_apply, smul_eq_mul, mul_one]
      exact hNinv
    have h3 := tendsto_nhds_unique h1 h2
    rw [sub_mulVec, smul_mulVec, one_mulVec] at h3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith

omit [DecidableEq X] in
/-- Theorem 2.3.1 (p. 69), left eigenvector: `εA = ρ(A)ε` for some nonnegative, nonzero `ε`,
by applying the right-eigenvector statement to `Aᵀ`. -/
theorem perron_frobenius_left (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∃ ε : X → ℝ, (∀ i, 0 ≤ ε i) ∧ ε ≠ 0 ∧ ε ᵥ* A = specRad A • ε := by
  classical
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius Aᵀ fun i j => hA j i
  refine ⟨ε, hε0, hεne, ?_⟩
  rw [← mulVec_transpose, hε, specRad_transpose]



/-! ### Lemma 2.3.2 -/

omit [DecidableEq X] in
/-- Lemma 2.3.2 (ii), p. 70, lower bound: if every column sum of `A ≥ 0` is at least `c`, then
`ρ(A) ≥ c`. Summing `Ae = ρe` over the coordinates of a nonnegative eigenvector `e` with `∑ e = S`
gives `ρS = ∑ⱼ colsumⱼ eⱼ ≥ cS`. -/
theorem le_specRad_of_colsum_ge (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ j, c ≤ ∑ i, A i j) : c ≤ specRad A := by
  classical
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hge : c * ∑ j, e j ≤ ∑ j, (∑ i, A i j) * e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (he0 j)
  rw [← hsum] at hge
  exact le_of_mul_le_mul_right hge hS

omit [DecidableEq X] in
/-- Lemma 2.3.2 (ii), p. 70, upper bound: if every column sum of `A ≥ 0` is at most `C`, then
`ρ(A) ≤ C`. -/
theorem specRad_le_of_colsum_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ j, ∑ i, A i j ≤ C) : specRad A ≤ C := by
  classical
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA
  have hS : 0 < ∑ j, e j := by
    rcases (sum_nonneg fun j _ => he0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hene
      funext j
      exact (sum_eq_zero_iff_of_nonneg fun j _ => he0 j).1 h.symm j (mem_univ j)
  have hsum : specRad A * ∑ j, e j = ∑ j, (∑ i, A i j) * e j := by
    calc specRad A * ∑ j, e j = ∑ i, (A *ᵥ e) i := by
          rw [he]
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
      _ = ∑ i, ∑ j, A i j * e j := rfl
      _ = ∑ j, ∑ i, A i j * e j := sum_comm
      _ = ∑ j, (∑ i, A i j) * e j := by simp only [sum_mul]
  have hle : ∑ j, (∑ i, A i j) * e j ≤ C * ∑ j, e j := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (he0 j)
  rw [← hsum] at hle
  exact le_of_mul_le_mul_right hle hS

omit [DecidableEq X] in
/-- Lemma 2.3.2 (i), p. 70: `ρ(A)` lies between the smallest and largest row sums of `A ≥ 0`, by
transposition. -/
theorem le_specRad_of_rowsum_ge (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {c : ℝ}
    (hc : ∀ i, c ≤ ∑ j, A i j) : c ≤ specRad A := by
  classical
  rw [← specRad_transpose]
  exact le_specRad_of_colsum_ge Aᵀ (fun i j => hA j i) hc

omit [DecidableEq X] in
theorem specRad_le_of_rowsum_le (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hC : ∀ i, ∑ j, A i j ≤ C) : specRad A ≤ C := by
  classical
  rw [← specRad_transpose]
  exact specRad_le_of_colsum_le Aᵀ (fun i j => hA j i) hC

/-! ### Lemma 2.3.3: the local spectral radius -/

/-- `c^{1/k} → 1` for `c > 0`. -/
theorem tendsto_rpow_one_div_natCast {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => Real.log c * (1 / (k : ℝ))) atTop (𝓝 (Real.log c * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h1
  have h2 := (Real.continuous_exp.tendsto 0).comp h1
  rw [Real.exp_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos hc, mul_comm]

omit [Nonempty X] in
/-- For `A ≥ 0` and `h ≥ m𝟙 > 0`, the row sums of `Aᵏ` are bounded by `(Aᵏh)ᵢ/m`, hence
`m‖Aᵏ‖ ≤ ‖Aᵏh‖`. -/
theorem norm_pow_mul_le_norm_mulVec (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : X → ℝ} {m : ℝ} (hm : 0 < m) (hmh : ∀ j, m ≤ h j) (k : ℕ) :
    m * ‖A ^ k‖ ≤ ‖A ^ k *ᵥ h‖ := by
  have hAk := pow_nonneg_entries hA k
  rw [← le_div_iff₀' hm]
  refine norm_le_of_rowsum_abs_le (A ^ k) (div_nonneg (norm_nonneg _) hm.le) fun i => ?_
  rw [le_div_iff₀ hm]
  calc (∑ j, |(A ^ k) i j|) * m = ∑ j, (A ^ k) i j * m := by
        rw [sum_mul]
        exact sum_congr rfl fun j _ => by rw [abs_of_nonneg (hAk i j)]
    _ ≤ ∑ j, (A ^ k) i j * h j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmh j) (hAk i j)
    _ = (A ^ k *ᵥ h) i := rfl
    _ ≤ ‖A ^ k *ᵥ h‖ := by
        have := norm_le_pi_norm (A ^ k *ᵥ h) i
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this

/-- Lemma 2.3.3 (p. 70): for `A ≥ 0` and `h ≫ 0`, `‖Aᵏh‖^{1/k} → ρ(A)`, in the supremum norm. -/
theorem tendsto_norm_pow_mulVec_rpow (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {h : X → ℝ} (hh : ∀ j, 0 < h j) :
    Tendsto (fun k : ℕ => ‖A ^ k *ᵥ h‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  -- the minimum `m` of `h` and the norm `‖h‖`
  obtain ⟨j₀, -, hj₀⟩ := exists_min_image univ h univ_nonempty
  set m := h j₀ with hm
  have hmpos : 0 < m := hh j₀
  have hmh : ∀ j, m ≤ h j := fun j => hj₀ j (mem_univ j)
  have hhnorm : 0 < ‖h‖ := by
    have := norm_le_pi_norm h j₀
    rw [Real.norm_eq_abs, abs_of_pos (hh j₀)] at this
    exact hmpos.trans_le this
  have hG := tendsto_norm_pow_rpow A
  -- upper: `‖Aᵏh‖^{1/k} ≤ ‖Aᵏ‖^{1/k} ‖h‖^{1/k}`
  have hup : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ)) * ‖h‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (specRad A * 1)) := hG.mul (tendsto_rpow_one_div_natCast hhnorm)
  -- lower: `m^{1/k} ‖Aᵏ‖^{1/k} ≤ ‖Aᵏh‖^{1/k}`
  have hlo : Tendsto (fun k : ℕ => m ^ (1 / (k : ℝ)) * ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (1 * specRad A)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [mul_one] at hup
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun k => ?_) (fun k => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (norm_pow_mul_le_norm_mulVec A hA hmpos hmh k)
      (by positivity)
  · rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.linfty_opNorm_mulVec _ _) (by positivity)

/-! ### Markov matrices (§2.3.1.3) -/

omit [DecidableEq X] in
/-- Exercise 2.3.2 (ii), p. 71: `ρ(P) = 1` for a Markov matrix. -/
theorem IsMarkov.specRad_eq_one {P : Matrix X X ℝ} (hP : IsMarkov P) : specRad P = 1 := by
  classical
  exact
  specRad_eq_of_rowsum_eq P hP.nonneg zero_le_one hP.rowsum

omit [DecidableEq X] in
/-- Exercise 2.3.2 (iii), p. 71: a Markov matrix has a stationary distribution, a row vector
`ψ ≥ 0` with `ψ𝟙 = 1` and `ψP = ψ`, by the left Perron–Frobenius eigenvector for `ρ(P) = 1`. -/
theorem IsMarkov.exists_stationary {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ∃ ψ : X → ℝ, (∀ i, 0 ≤ ψ i) ∧ ∑ i, ψ i = 1 ∧ ψ ᵥ* P = ψ := by
  classical
  obtain ⟨ε, hε0, hεne, hε⟩ := perron_frobenius_left P hP.nonneg
  rw [hP.specRad_eq_one, one_smul] at hε
  have hS : 0 < ∑ i, ε i := by
    rcases (sum_nonneg fun i _ => hε0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hεne
      funext i
      exact (sum_eq_zero_iff_of_nonneg fun i _ => hε0 i).1 h.symm i (mem_univ i)
  refine ⟨(∑ i, ε i)⁻¹ • ε, fun i => mul_nonneg (inv_nonneg.2 hS.le) (hε0 i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hS.ne'
  · rw [smul_vecMul, hε]

omit [DecidableEq X] in
/-- Exercise 2.3.3 (p. 71): for a Markov matrix `P` and `ε > 0` there is no `h` with
`Ph ≥ h + ε`: at a maximiser `x̄` of `h`, `(Ph)(x̄) ≤ h(x̄)`. -/
theorem IsMarkov.not_mulVec_ge_add {P : Matrix X X ℝ} (hP : IsMarkov P) {ε : ℝ}
    (hε : 0 < ε) : ¬ ∃ h : X → ℝ, ∀ x, h x + ε ≤ (P *ᵥ h) x := by
  classical
  rintro ⟨h, hh⟩
  obtain ⟨x, -, hx⟩ := exists_max_image univ h univ_nonempty
  have : (P *ᵥ h) x ≤ h x := by
    calc (P *ᵥ h) x = ∑ y, P x y * h y := rfl
      _ ≤ ∑ y, P x y * h x :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx y (mem_univ y)) (hP.nonneg x y)
      _ = h x := by rw [← sum_mul, hP.rowsum, one_mul]
  linarith [hh x]

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Perron–Frobenius theorem for irreducible matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), second sentence: if `A ≥ 0` is irreducible, then the right and left
Perron–Frobenius eigenvectors are everywhere positive and unique, and
`ρ(A) > 0`. The `FiniteStates/OperatorsFixedPoints` project proved the
nonnegative case and deferred this part, which Chapter 6 needs through its
corollary Exercise 2.3.2 (iv) (p. 71): an irreducible Markov matrix has a
unique stationary distribution, and it is everywhere positive. Restated from the
`FiniteStates/NonlinearValuation` project.

The proofs are elementary once the nonnegative case is available. If `Ae = λe`
with `e ≥ 0` nonzero, pick `y` with `e(y) > 0`; for any `x` some `k ≥ 1` has
`Aᵏ(x, y) > 0`, and `λᵏe(x) = (Aᵏe)(x) ≥ Aᵏ(x, y)e(y) > 0`, so `e ≫ 0` and
`λ > 0`. Uniqueness: a left eigenvector `ε ≫ 0` for `ρ(A)` gives
`λ⟨ε, e'⟩ = ⟨ε, Ae'⟩ = ρ(A)⟨ε, e'⟩` for any nonnegative eigenvector `e'`, so
`λ = ρ(A)`; and if `e, e'` are two such eigenvectors for `ρ(A)`, then
`e' − ce` with `c = min e'/e` is a nonnegative eigenvector with a zero
coordinate, hence zero. These are restated from the `FiniteStates/StochasticDiscounting`
project, where they were first proved.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Irreducibility (Vol. 1, p. 69): `A ≥ 0` and every state leads to every other in some
positive number of steps, `∑_{k≥1} Aᵏ ≫ 0`. -/
def Irreducible (A : Matrix X X ℝ) : Prop :=
  (∀ x x', 0 ≤ A x x') ∧ ∀ x x', ∃ k ≥ 1, 0 < (A ^ k) x x'

/-- An everywhere-positive matrix is irreducible (take `k = 1`). -/
theorem irreducible_of_pos {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') : Irreducible A :=
  ⟨fun x x' => (hpos x x').le, fun x x' => ⟨1, le_rfl, by rw [pow_one]; exact hpos x x'⟩⟩

/-- Irreducibility is preserved by transposition. -/
theorem Irreducible.transpose {A : Matrix X X ℝ} (hA : Irreducible A) : Irreducible Aᵀ :=
  ⟨fun x x' => hA.1 x' x, fun x x' => by
    obtain ⟨k, hk, hpos⟩ := hA.2 x' x
    refine ⟨k, hk, ?_⟩
    rw [← Matrix.transpose_pow, Matrix.transpose_apply]
    exact hpos⟩

/-- `Ae = λe` implies `Aᵏe = λᵏe`. -/
theorem pow_mulVec_eq_of_mulVec_eq {A : Matrix X X ℝ} {e : X → ℝ} {lam : ℝ}
    (he : A *ᵥ e = lam • e) (k : ℕ) : A ^ k *ᵥ e = lam ^ k • e := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, he, smul_smul, ← pow_succ]

/-- For irreducible `A`, a nonnegative nonzero eigenvector is everywhere positive, and its
eigenvalue is positive. -/
theorem Irreducible.pos_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A) {e : X → ℝ}
    {lam : ℝ} (he0 : ∀ x, 0 ≤ e x) (hene : e ≠ 0) (he : A *ᵥ e = lam • e) :
    (∀ x, 0 < e x) ∧ 0 < lam := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < e y := by
    by_contra h
    exact hene (funext fun x => le_antisymm (not_lt.1 fun hx => h ⟨x, hx⟩) (he0 x))
  -- `λ e(y) = (Ae)(y) ≥ 0` gives `λ ≥ 0`
  have hlam0 : 0 ≤ lam := by
    have h1 : 0 ≤ (A *ᵥ e) y := sum_nonneg fun z _ => mul_nonneg (hA.1 y z) (he0 z)
    rw [he, Pi.smul_apply, smul_eq_mul] at h1
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) hy
    linarith
  -- `λᵏ e(x) = (Aᵏe)(x) ≥ Aᵏ(x, y) e(y) > 0`
  have hpos : ∀ x, 0 < e x := by
    intro x
    obtain ⟨k, -, hkpos⟩ := hA.2 x y
    have h1 : (A ^ k) x y * e y ≤ (A ^ k *ᵥ e) x :=
      single_le_sum (fun z _ => mul_nonneg (pow_nonneg_entries hA.1 k x z) (he0 z)) (mem_univ y)
    rw [pow_mulVec_eq_of_mulVec_eq he, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : 0 < lam ^ k * e x := lt_of_lt_of_le (mul_pos hkpos hy) h1
    rcases (he0 x).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h2
      exact absurd h2 (lt_irrefl 0)
  refine ⟨hpos, ?_⟩
  rcases hlam0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk, hkpos⟩ := hA.2 y y
    have h1 : (A ^ k) y y * e y ≤ (A ^ k *ᵥ e) y :=
      single_le_sum (fun z _ => mul_nonneg (pow_nonneg_entries hA.1 k y z) (he0 z)) (mem_univ y)
    rw [pow_mulVec_eq_of_mulVec_eq he, Pi.smul_apply, smul_eq_mul, ← h, zero_pow (by omega),
      zero_mul] at h1
    exact absurd (mul_pos hkpos hy) (not_lt.2 h1)

variable [Nonempty X]

/-- **Theorem 2.3.1, irreducible case** (p. 69): `ρ(A) > 0` for irreducible `A`. -/
theorem Irreducible.specRad_pos {A : Matrix X X ℝ} (hA : Irreducible A) : 0 < specRad A := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA.1
  exact (hA.pos_of_mulVec_eq_smul he0 hene he).2

/-- **Theorem 2.3.1, irreducible case** (p. 69): the right Perron–Frobenius eigenvector is
everywhere positive. -/
theorem Irreducible.exists_pos_eigenvector {A : Matrix X X ℝ} (hA : Irreducible A) :
    ∃ e : X → ℝ, (∀ x, 0 < e x) ∧ A *ᵥ e = specRad A • e := by
  obtain ⟨e, he0, hene, he⟩ := perron_frobenius A hA.1
  exact ⟨e, (hA.pos_of_mulVec_eq_smul he0 hene he).1, he⟩

/-- **Theorem 2.3.1, irreducible case** (p. 69): the left Perron–Frobenius eigenvector is
everywhere positive. -/
theorem Irreducible.exists_pos_left_eigenvector {A : Matrix X X ℝ} (hA : Irreducible A) :
    ∃ ε : X → ℝ, (∀ x, 0 < ε x) ∧ ε ᵥ* A = specRad A • ε := by
  obtain ⟨ε, hε, hεA⟩ := hA.transpose.exists_pos_eigenvector
  refine ⟨ε, hε, ?_⟩
  rw [← mulVec_transpose, hεA, specRad_transpose]

/-- For irreducible `A`, the only eigenvalue with a nonnegative nonzero eigenvector is `ρ(A)`:
pair with a positive left eigenvector. -/
theorem Irreducible.eq_specRad_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A)
    {e' : X → ℝ} {lam : ℝ} (he'0 : ∀ x, 0 ≤ e' x) (hne : e' ≠ 0) (he' : A *ᵥ e' = lam • e') :
    lam = specRad A := by
  obtain ⟨ε, hε, hεA⟩ := hA.exists_pos_left_eigenvector
  have h1 : ε ⬝ᵥ (A *ᵥ e') = (ε ᵥ* A) ⬝ᵥ e' := dotProduct_mulVec ε A e'
  rw [he', hεA, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
  have hpos : 0 < ε ⬝ᵥ e' := by
    have he'pos := (hA.pos_of_mulVec_eq_smul he'0 hne he').1
    exact sum_pos (fun x _ => mul_pos (hε x) (he'pos x)) univ_nonempty
  exact mul_right_cancel₀ hpos.ne' h1

/-- **Theorem 2.3.1, irreducible case** (p. 69), uniqueness: a nonnegative nonzero eigenvector
for `ρ(A)` is a positive multiple of any positive one. -/
theorem Irreducible.exists_eq_smul_of_mulVec_eq_smul {A : Matrix X X ℝ} (hA : Irreducible A)
    {e e' : X → ℝ} (he : ∀ x, 0 < e x) (heA : A *ᵥ e = specRad A • e) (he'0 : ∀ x, 0 ≤ e' x)
    (hne : e' ≠ 0) (he'A : A *ᵥ e' = specRad A • e') : ∃ c : ℝ, 0 < c ∧ e' = c • e := by
  obtain ⟨x₀, -, hx₀⟩ := exists_min_image univ (fun x => e' x / e x) univ_nonempty
  set c := e' x₀ / e x₀ with hc
  have he'pos := (hA.pos_of_mulVec_eq_smul he'0 hne he'A).1
  have hcpos : 0 < c := div_pos (he'pos x₀) (he x₀)
  set φ : X → ℝ := e' - c • e with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := by
    intro x
    have := hx₀ x (mem_univ x)
    rw [le_div_iff₀ (he x)] at this
    simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hφA : A *ᵥ φ = specRad A • φ := by
    rw [hφ, mulVec_sub, mulVec_smul, heA, he'A]
    module
  have hφx₀ : φ x₀ = 0 := by
    simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    rw [div_mul_cancel₀ _ (he x₀).ne', sub_self]
  by_cases hφne : φ = 0
  · rw [hφ] at hφne
    exact ⟨c, hcpos, sub_eq_zero.1 hφne⟩
  · exfalso
    have := (hA.pos_of_mulVec_eq_smul hφ0 hφne hφA).1 x₀
    rw [hφx₀] at this
    exact lt_irrefl 0 this

/-- Exercise 2.3.2 (iv), p. 71: an irreducible Markov matrix has exactly one stationary
distribution, and it is everywhere positive. -/
theorem IsMarkov.exists_unique_stationary_of_irreducible {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) :
    ∃ ψ : X → ℝ, IsDistribution ψ ∧ ψ ᵥ* P = ψ ∧ (∀ x, 0 < ψ x) ∧
      ∀ φ, IsDistribution φ → φ ᵥ* P = φ → φ = ψ := by
  obtain ⟨ψ, hψ0, hψ1, hψP⟩ := hP.exists_stationary
  have hρ : specRad Pᵀ = 1 := by rw [specRad_transpose, hP.specRad_eq_one]
  have hψne : ψ ≠ 0 := by
    intro h
    rw [h] at hψ1
    simp at hψ1
  have hψT : Pᵀ *ᵥ ψ = specRad Pᵀ • ψ := by rw [mulVec_transpose, hψP, hρ, one_smul]
  have hψpos := (hirr.transpose.pos_of_mulVec_eq_smul hψ0 hψne hψT).1
  refine ⟨ψ, ⟨hψ0, hψ1⟩, hψP, hψpos, fun φ hφ hφP => ?_⟩
  have hφne : φ ≠ 0 := by
    intro h
    have := hφ.sum_eq_one
    rw [h] at this
    simp at this
  have hφT : Pᵀ *ᵥ φ = specRad Pᵀ • φ := by rw [mulVec_transpose, hφP, hρ, one_smul]
  obtain ⟨c, -, hφc⟩ :=
    hirr.transpose.exists_eq_smul_of_mulVec_eq_smul hψpos hψT hφ.nonneg hφne hφT
  have hsum : ∑ x, φ x = c * ∑ x, ψ x := by
    rw [hφc]
    simp [mul_sum]
  rw [hφ.sum_eq_one, hψ1, mul_one] at hsum
  rw [hφc, ← hsum, one_smul]

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear valuation and eventual contractions, restated

Facts from Vol. 1, Chapter 6 used in Chapters 7–9, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- The discount operator (6.4): `L(x, x') = b(x, x')P(x, x')`. -/
def discountOp (b : X → X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => b x x' * P x x'

omit [Fintype X] [DecidableEq X] in
theorem discountOp_apply (b : X → X → ℝ) (P : Matrix X X ℝ) (x x' : X) :
    discountOp b P x x' = b x x' * P x x' := rfl

omit [Fintype X] [DecidableEq X] in
theorem discountOp_nonneg {b : X → X → ℝ} {P : Matrix X X ℝ} (hb : ∀ x x', 0 ≤ b x x')
    (hP : ∀ x x', 0 ≤ P x x') (x x' : X) : 0 ≤ discountOp b P x x' :=
  mul_nonneg (hb x x') (hP x x')

omit [Fintype X] [DecidableEq X] in
/-- Constant discounting `b ≡ β` gives `L = βP`. -/
theorem discountOp_const (β : ℝ) (P : Matrix X X ℝ) : discountOp (fun _ _ => β) P = β • P := by
  ext x x'
  simp [discountOp]

omit [DecidableEq X] in
/-- `ρ(βP) = β` for a Markov matrix `P` and `β ≥ 0`, so Theorem 6.1.1 contains Lemma 3.2.1. -/
theorem specRad_smul_isMarkov [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ : 0 ≤ β) : specRad (β • P) = β := by
  classical
  exact
  specRad_eq_of_rowsum_eq _ (fun x x' => mul_nonneg hβ (hP.nonneg x x')) hβ fun x => by
    simp only [← mul_sum, hP.rowsum, mul_one]

variable [Nonempty X]

/-- Under `ρ(L) < 1` the entries of `Lᵗ` are summable in `t`. -/
theorem summable_pow_apply {L : Matrix X X ℝ} (hρ : specRad L < 1) (x x' : X) :
    Summable fun t : ℕ => (L ^ t) x x' := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg L).trans hr1.le
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2) ?_
  exact (eventually_abs_entry_pow_le L hr1 x x').mono fun t ht => by rwa [Real.norm_eq_abs]

/-- Under `ρ(L) < 1` the series `∑ₜ Lᵗh` converges. -/
theorem summable_pow_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    Summable fun t : ℕ => L ^ t *ᵥ h := by
  rw [Pi.summable]
  intro x
  simp only [mulVec, dotProduct]
  exact summable_sum fun x' _ => (summable_pow_apply hρ x x').mul_right (h x')

/-- `L ∑ₜ Lᵗh = ∑ₜ Lᵗ⁺¹h`. -/
theorem mulVec_tsum_pow_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    L *ᵥ (∑' t : ℕ, L ^ t *ᵥ h) = ∑' t : ℕ, L ^ (t + 1) *ᵥ h := by
  have hs := summable_pow_mulVec hρ h
  let f : (X → ℝ) →L[ℝ] (X → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hf : L *ᵥ (∑' t : ℕ, L ^ t *ᵥ h) = f (∑' t : ℕ, L ^ t *ᵥ h) := rfl
  rw [hf, f.map_tsum hs]
  refine tsum_congr fun t => ?_
  change L *ᵥ (L ^ t *ᵥ h) = _
  rw [mulVec_mulVec, ← pow_succ']

/-- (6.5): `v = ∑ₜ Lᵗh` solves `v = h + Lv`. -/
theorem tsum_pow_mulVec_eq {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (∑' t : ℕ, L ^ t *ᵥ h) = h + L *ᵥ ∑' t : ℕ, L ^ t *ᵥ h := by
  rw [mulVec_tsum_pow_mulVec hρ h, (summable_pow_mulVec hρ h).tsum_eq_zero_add]
  simp

omit [DecidableEq X] in
/-- Uniqueness in Theorem 6.1.1: `I − L` is invertible, so `v = h + Lv` has at most one
solution. -/
theorem eq_of_eq_add_mulVec {L : Matrix X X ℝ} (hρ : specRad L < 1) {h v w : X → ℝ}
    (hv : v = h + L *ᵥ v) (hw : w = h + L *ᵥ w) : v = w := by
  classical
  have hunit := (neumann_series L hρ).1
  apply Matrix.mulVec_injective_iff_isUnit.2 hunit
  change (1 - L) *ᵥ v = (1 - L) *ᵥ w
  rw [sub_mulVec, one_mulVec, sub_mulVec, one_mulVec, sub_eq_of_eq_add hv, sub_eq_of_eq_add hw]

/-- `(I − L)⁻¹h` solves `v = h + Lv`. -/
theorem inv_mulVec_eq_add {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (1 - L)⁻¹ *ᵥ h = h + L *ᵥ ((1 - L)⁻¹ *ᵥ h) := by
  have hunit := (neumann_series L hρ).1
  have h1 : (1 - L) *ᵥ ((1 - L)⁻¹ *ᵥ h) = h := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      one_mulVec]
  rw [sub_mulVec, one_mulVec] at h1
  exact eq_add_of_sub_eq h1

/-- **Theorem 6.1.1** (p. 185), the formula (6.5): `∑ₜ Lᵗh = (I − L)⁻¹h` when `ρ(L) < 1`. -/
theorem inv_mulVec_eq_tsum {L : Matrix X X ℝ} (hρ : specRad L < 1) (h : X → ℝ) :
    (1 - L)⁻¹ *ᵥ h = ∑' t : ℕ, L ^ t *ᵥ h :=
  eq_of_eq_add_mulVec hρ (inv_mulVec_eq_add hρ h) (tsum_pow_mulVec_eq hρ h)

/-- **Theorem 6.1.1** (p. 185), the equation: `v = h + Lv` iff `v = (I − L)⁻¹h`. -/
theorem eq_add_mulVec_iff {L : Matrix X X ℝ} (hρ : specRad L < 1) (h v : X → ℝ) :
    v = h + L *ᵥ v ↔ v = (1 - L)⁻¹ *ᵥ h :=
  ⟨fun hv => eq_of_eq_add_mulVec hρ hv (inv_mulVec_eq_add hρ h), fun hv => by
    rw [hv]; exact inv_mulVec_eq_add hρ h⟩

omit [DecidableEq X] in
/-- **Lemma 6.1.4** (p. 189): for a positive linear operator `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff
`v = h + Lv` has a unique solution in `V = (0, ∞)^X`. Sufficiency is Theorem 6.1.1 with
`v = ∑ Lᵗh ≥ h ≫ 0`; necessity pairs any positive solution with a Perron–Frobenius left eigenvector
`ε ≥ 0`, `ε ≠ 0`: `⟨ε, v⟩ = ρ(L)⟨ε, v⟩ + ⟨ε, h⟩` with `⟨ε, h⟩, ⟨ε, v⟩ > 0`. -/
theorem specRad_lt_one_iff_existsUnique_pos {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    {h : X → ℝ} (hh : ∀ x, 0 < h x) :
    specRad L < 1 ↔ ∃! v : X → ℝ, (∀ x, 0 < v x) ∧ v = h + L *ᵥ v := by
  classical
  constructor
  · intro hρ
    have hv0 : ∀ x, 0 ≤ ((1 - L)⁻¹ *ᵥ h) x := by
      intro x
      rw [inv_mulVec_eq_tsum hρ, Pi.tsum_apply (summable_pow_mulVec hρ h)]
      exact tsum_nonneg fun t =>
        sum_nonneg fun x' _ => mul_nonneg (pow_nonneg_entries hL t x x') (hh x').le
    refine ⟨(1 - L)⁻¹ *ᵥ h, ⟨fun x => ?_, inv_mulVec_eq_add hρ h⟩,
      fun v hv => (eq_add_mulVec_iff hρ h v).1 hv.2⟩
    have := congrFun (inv_mulVec_eq_add hρ h) x
    rw [this, Pi.add_apply]
    exact add_pos_of_pos_of_nonneg (hh x)
      (sum_nonneg fun x' _ => mul_nonneg (hL x x') (hv0 x'))
  · rintro ⟨v, ⟨hvpos, hv⟩, -⟩
    obtain ⟨ε, hε0, hεne, hεL⟩ := perron_frobenius_left L hL
    have hεv : ε ⬝ᵥ v = ε ⬝ᵥ h + specRad L * (ε ⬝ᵥ v) := by
      conv_lhs => rw [hv]
      rw [dotProduct_add, dotProduct_mulVec, hεL, smul_dotProduct, smul_eq_mul]
    obtain ⟨y, hy⟩ : ∃ y, 0 < ε y := by
      by_contra hcon
      exact hεne (funext fun x => le_antisymm (not_lt.1 fun hx => hcon ⟨x, hx⟩) (hε0 x))
    have hεh : 0 < ε ⬝ᵥ h :=
      sum_pos' (fun x _ => mul_nonneg (hε0 x) (hh x).le) ⟨y, mem_univ y, mul_pos hy (hh y)⟩
    have hεv' : 0 < ε ⬝ᵥ v :=
      sum_pos' (fun x _ => mul_nonneg (hε0 x) (hvpos x).le) ⟨y, mem_univ y, mul_pos hy (hvpos y)⟩
    by_contra hcon
    have h1 : 1 ≤ specRad L := not_lt.1 hcon
    nlinarith

/-! ### Eventual contractions -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **Theorem 6.1.5** (p. 190), Exercise 6.1.4: if `T` maps the closed set `U` into itself and
`Tᵏ` is a contraction on `U` for some `k ≥ 1`, then `T` is globally stable on `U`: it has a unique
fixed point `u*` in `U`, and `Tⁿu → u*` for every `u ∈ U`. -/
theorem globallyStable_of_iterate_contraction [CompleteSpace E] {T : E → E} {U : Set E}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {k : ℕ} (hk : 0 < k) {L : ℝ}
    (hc : IsContractionOn (T^[k]) U L) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  obtain ⟨u', hu'U, hfix⟩ := hc.exists_fixedPt hU hne
  -- `T u'` is a fixed point of `Tᵏ` in `U`, hence equals `u'`
  have hTfix : IsFixedPt T u' := by
    have h1 : IsFixedPt (T^[k]) (T u') := by
      change T^[k] (T u') = T u'
      rw [← iterate_succ_apply, iterate_succ_apply', hfix.eq]
    exact hc.fixedPt_unique (hT hu'U) hu'U h1 hfix
  refine ⟨u', hu'U, hTfix, fun v hv hvfix => hc.fixedPt_unique hv hu'U (hvfix.iterate k) hfix,
    fun u hu => ?_⟩
  -- `Tⁿu = (Tᵏ)^{n/k}(T^{n%k}u)`, and `‖T^{n%k}u − u'‖ ≤ M := ∑_{r<k} ‖Tʳu − u'‖`
  set M : ℝ := ∑ r ∈ range k, ‖T^[r] u - u'‖ with hM
  have hM0 : 0 ≤ M := sum_nonneg fun _ _ => norm_nonneg _
  have hbound : ∀ n : ℕ, ‖T^[n] u - u'‖ ≤ L ^ (n / k) * M := by
    intro n
    have hn : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
    have h1 : T^[n] u = (T^[k])^[n / k] (T^[n % k] u) := by
      conv_lhs => rw [hn]
      rw [iterate_add_apply, iterate_mul]
    rw [h1]
    have h2 := hc.norm_iterate_sub_fixedPt_le (hT.iterate (n % k) hu) hu'U hfix (n / k)
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc.nonneg _))
    exact single_le_sum (fun r _ => norm_nonneg (T^[r] u - u')) (mem_range.2 (Nat.mod_lt n hk))
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  have h3 : Tendsto (fun n : ℕ => L ^ (n / k)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.nonneg hc.lt_one).comp
      (Nat.tendsto_div_const_atTop hk.ne')
  simpa using h3.mul_const M

/-- Theorem 6.1.5 on the whole space, in the vocabulary of §1.2.2: an eventual contraction of
a complete space is globally stable. -/
theorem globallyStable_of_iterate_contraction_univ [CompleteSpace E] {T : E → E} {k : ℕ}
    (hk : 0 < k) {L : ℝ} (hc : IsContractionOn (T^[k]) Set.univ L) : GloballyStable T := by
  obtain ⟨u', -, hfix, huniq, hconv⟩ := globallyStable_of_iterate_contraction isClosed_univ
    ⟨0, Set.mem_univ 0⟩ (Set.mapsTo_univ T Set.univ) hk hc
  exact ⟨u', hfix, fun v hv => huniq v (Set.mem_univ v) hv, fun u => hconv u (Set.mem_univ u)⟩

omit [Fintype X] [DecidableEq X] in
/-- The affine map `Tu = Au + b` of Example 6.1.2. -/
def affineOp (A : Matrix X X ℝ) (b : X → ℝ) (u : X → ℝ) : X → ℝ := A *ᵥ u + b

omit [Nonempty X] in
/-- `Tᵏu − Tᵏv = Aᵏ(u − v)`. -/
theorem affineOp_iterate_sub (A : Matrix X X ℝ) (b u v : X → ℝ) (k : ℕ) :
    (affineOp A b)^[k] u - (affineOp A b)^[k] v = A ^ k *ᵥ (u - v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', affineOp, affineOp, add_sub_add_right_eq_sub,
      ← mulVec_sub, ih, mulVec_mulVec, ← pow_succ']

/-- Example 6.1.2 (p. 190): if `ρ(A) < 1` then some `Tᵏ` is a contraction under the supremum
norm, with modulus `‖Aᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_affineOp {A : Matrix X X ℝ}
    (hρ : specRad A < 1) (b : X → ℝ) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn ((affineOp A b)^[k]) Set.univ ‖A ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero A hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun u _ v _ => ?_⟩
  rw [affineOp_iterate_sub]
  exact Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq X] in
/-- Example 6.1.2 (p. 190): `Tu = Au + b` with `ρ(A) < 1` is globally stable, by Theorem 6.1.5. -/
theorem globallyStable_affineOp {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : GloballyStable (affineOp A b) := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_affineOp hρ b
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Example 6.1.2 (p. 190): the fixed point is `(I − A)⁻¹b`, by the Neumann series lemma. -/
theorem isFixedPt_affineOp_inv {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : IsFixedPt (affineOp A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  rw [add_comm]
  exact (inv_mulVec_eq_add hρ b).symm

omit [DecidableEq X] [Nonempty X] in
/-- A nonnegative matrix preserves `≤`. -/
theorem mulVec_le_mulVec_of_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {f g : X → ℝ}
    (hfg : f ≤ g) : L *ᵥ f ≤ L *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hL x x')

omit [DecidableEq X] [Nonempty X] in
/-- `‖|f|‖_∞ = ‖f‖_∞`. -/
theorem norm_abs_fun (f : X → ℝ) : ‖fun y => |f y|‖ = ‖f‖ := by
  simp only [Pi.norm_def, Real.nnnorm_abs]

omit [DecidableEq X] [Nonempty X] in
/-- If `|u| ≤ w` pointwise with `w ≥ 0`, then `‖u‖_∞ ≤ ‖w‖_∞`. -/
theorem norm_le_norm_of_abs_le_fun {u w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (h : ∀ x, |u x| ≤ w x) :
    ‖u‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  refine (h x).trans ?_
  have := norm_le_pi_norm w x
  rwa [Real.norm_eq_abs, abs_of_nonneg (hw x)] at this

omit [Nonempty X] in
/-- Iterating (6.13): `|Tᵏv − Tᵏw| ≤ Lᵏ|v − w|`, (6.14). -/
theorem abs_iterate_sub_le_pow_mulVec {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) (k : ℕ) :
    ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T^[k] v x - T^[k] w x| ≤ (L ^ k *ᵥ fun y => |v y - w y|) x := by
  induction k with
  | zero => intro v _ w _ x; simp
  | succ k ih =>
    intro v hv w hw x
    rw [iterate_succ_apply', iterate_succ_apply']
    refine (hdom _ (hT.iterate k hv) _ (hT.iterate k hw) x).trans ?_
    have h1 := mulVec_le_mulVec_of_nonneg hL (fun y => ih v hv w hw y) x
    rw [mulVec_mulVec, ← pow_succ'] at h1
    exact h1

/-- **Proposition 6.1.6** (p. 191): if `T` maps `U` into itself and `|Tv − Tw| ≤ L|v − w|` for a
positive linear `L` with `ρ(L) < 1`, then some `Tᵏ` is a contraction on `U` under the supremum norm,
with modulus `‖Lᵏ‖ < 1`. -/
theorem exists_isContractionOn_iterate_of_abs_sub_le {T : (X → ℝ) → (X → ℝ)}
    {U : Set (X → ℝ)} (hT : Set.MapsTo T U U) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (T^[k]) U ‖L ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero L hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, hT.iterate k, norm_nonneg _, hk1, fun v hv w hw => ?_⟩
  have hLk := pow_nonneg_entries hL k
  calc ‖T^[k] v - T^[k] w‖ ≤ ‖L ^ k *ᵥ fun y => |v y - w y|‖ :=
        norm_le_norm_of_abs_le_fun
          (fun x => sum_nonneg fun y _ => mul_nonneg (hLk x y) (abs_nonneg _))
          (abs_iterate_sub_le_pow_mulVec hT hL hdom k v hv w hw)
    _ ≤ ‖L ^ k‖ * ‖fun y => |v y - w y|‖ := Matrix.linfty_opNorm_mulVec _ _
    _ = ‖L ^ k‖ * ‖v - w‖ := by
        rw [show (fun y => |v y - w y|) = fun y => |(v - w) y| from rfl, norm_abs_fun]

omit [DecidableEq X] in
/-- Proposition 6.1.6 with Theorem 6.1.5: under (6.13) on a closed `U`, `T` is globally stable on
`U`. -/
theorem globallyStable_of_abs_sub_le {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ hdom
  exact globallyStable_of_iterate_contraction hU hne hT hk hc

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fixed points of order-preserving maps: Knaster–Tarski and Du

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.1–§7.1.2.2
(pp. 213–217).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapters 8–9; each chapter project is self-contained.

* Global stability relative to a set: a unique fixed point in `U` to which the
  iterates from every point of `U` converge.
* Theorem 7.1.1 (Knaster–Tarski) on an order interval `[v₁, v₂]` of `ℝ^X`: the
  fixed points of an order-preserving self-map form a nonempty set with least and
  greatest elements `a ≤ b`, and `Tᵏv₁ ≤ a ≤ b ≤ Tᵏv₂`. The interval is a complete
  lattice because `ℝ^X` is conditionally complete.
* Exercise 7.1.1: when `v₁ ≠ v₂`, the identity has a continuum of fixed points.
* Theorem 7.1.3 (Du): an order-preserving self-map of `[v₁, v₂]` is globally stable
  if it is concave with `Tv₁ ≥ v₁ + δ(v₂ − v₁)` for some `δ > 0` (condition (ii)),
  or with `Tv₁ ≫ v₁` (condition (i)), or convex with the mirror conditions (iii)
  and (iv). The book cites Du (1990) and Zhang (2012); the proof here tracks
  `λₖ = 1 − (1 − δ)ᵏ` with `Tᵏv₁ ≥ (1 − λₖ)v₁ + λₖTᵏv₂`, so that every orbit is
  squeezed between `Tᵏv₁` and `Tᵏv₂`, which are `(1 − δ)ᵏ‖v₂ − v₁‖` apart. The
  convex case follows by the reflection `v ↦ −T(−v)`.
* Exercise 7.1.6: composites of order-preserving concave maps are concave.
* Topological conjugacy preserves global stability (Vol. 1, p. 45), used for the
  Epstein–Zin operators.
-/

open Finset Filter Topology Function

namespace SargentStachurski.AbstractDynamicProgramming

/-! ### Global stability on a set -/

/-- `T` is globally stable on `U`: it has a fixed point `u` in `U`, `u` is the only fixed point in
`U`, and `Tᵏv → u` for every `v ∈ U`. -/
def GloballyStableOn {E : Type*} [TopologicalSpace E] (T : E → E) (U : Set E) : Prop :=
  ∃ u ∈ U, IsFixedPt T u ∧ (∀ v ∈ U, IsFixedPt T v → v = u) ∧
    ∀ v ∈ U, Tendsto (fun k : ℕ => T^[k] v) atTop (𝓝 u)

/-- Global stability on the whole space is global stability on `univ`. -/
theorem globallyStableOn_univ_iff {E : Type*} [TopologicalSpace E] (T : E → E) :
    GloballyStableOn T Set.univ ↔ GloballyStable T := by
  constructor
  · rintro ⟨u, -, hu, huniq, hconv⟩
    exact ⟨u, hu, fun v hv => huniq v (Set.mem_univ v) hv, fun v => hconv v (Set.mem_univ v)⟩
  · rintro ⟨u, hu, huniq, hconv⟩
    exact ⟨u, Set.mem_univ u, hu, fun v _ hv => huniq v hv, fun v _ => hconv v⟩

/-- A globally stable map has a unique fixed point in `U`. -/
theorem GloballyStableOn.existsUnique {E : Type*} [TopologicalSpace E] {T : E → E} {U : Set E}
    (h : GloballyStableOn T U) : ∃! u, u ∈ U ∧ IsFixedPt T u := by
  obtain ⟨u, hu, hfix, huniq, -⟩ := h
  exact ⟨u, ⟨hu, hfix⟩, fun v hv => huniq v hv.1 hv.2⟩

/-- Topological conjugacy (Vol. 1, p. 45): if `Φ` is continuous on `U`, maps `U` into `U'`, has a
two-sided inverse `Ψ` from `U'` onto `U`, and `Φ ∘ T = T' ∘ Φ` on `U`, then global stability of `T`
on `U` gives global stability of `T'` on `U'`. -/
theorem GloballyStableOn.of_conj {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']
    {T : E → E} {U : Set E} {T' : E' → E'} {U' : Set E'} (Φ : E → E') (Ψ : E' → E)
    (hΦ : Set.MapsTo Φ U U') (hΨ : Set.MapsTo Ψ U' U) (hΦΨ : ∀ u ∈ U', Φ (Ψ u) = u)
    (hΨΦ : ∀ u ∈ U, Ψ (Φ u) = u) (hΦc : ContinuousOn Φ U) (hT : Set.MapsTo T U U)
    (hconj : ∀ u ∈ U, Φ (T u) = T' (Φ u)) (h : GloballyStableOn T U) :
    GloballyStableOn T' U' := by
  obtain ⟨u, hu, hfix, huniq, hconv⟩ := h
  refine ⟨Φ u, hΦ hu, ?_, fun v hv hvfix => ?_, fun v hv => ?_⟩
  · change T' (Φ u) = Φ u
    rw [← hconj u hu, hfix.eq]
  · -- `Ψ v` is a fixed point of `T`
    have h1 : Φ (T (Ψ v)) = Φ (Ψ v) := by rw [hconj _ (hΨ hv), hΦΨ v hv, hvfix.eq]
    have h2 : IsFixedPt T (Ψ v) := by
      change T (Ψ v) = Ψ v
      rw [← hΨΦ _ (hT (hΨ hv)), h1, hΨΦ _ (hΨ hv)]
    rw [← hΦΨ v hv, huniq _ (hΨ hv) h2]
  · -- `T'ᵏ v = Φ (Tᵏ (Ψ v))`
    have hiter : ∀ k, T'^[k] v = Φ (T^[k] (Ψ v)) := by
      intro k
      induction k with
      | zero => simp [hΦΨ v hv]
      | succ k ih =>
        rw [iterate_succ_apply', ih, iterate_succ_apply', hconj _ (hT.iterate k (hΨ hv))]
    simp only [hiter]
    have hlim := hconv (Ψ v) (hΨ hv)
    have hwithin : Tendsto (fun k => T^[k] (Ψ v)) atTop (𝓝[U] u) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => hT.iterate k (hΨ hv)⟩
    exact ((hΦc u hu).tendsto).comp hwithin

/-- Topological conjugacy preserves global stability in both directions. -/
theorem globallyStableOn_iff_of_conj {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']
    {T : E → E} {U : Set E} {T' : E' → E'} {U' : Set E'} (Φ : E → E') (Ψ : E' → E)
    (hΦ : Set.MapsTo Φ U U') (hΨ : Set.MapsTo Ψ U' U) (hΦΨ : ∀ u ∈ U', Φ (Ψ u) = u)
    (hΨΦ : ∀ u ∈ U, Ψ (Φ u) = u) (hΦc : ContinuousOn Φ U) (hΨc : ContinuousOn Ψ U')
    (hT : Set.MapsTo T U U) (hconj : ∀ u ∈ U, Φ (T u) = T' (Φ u)) :
    GloballyStableOn T U ↔ GloballyStableOn T' U' := by
  have hT' : Set.MapsTo T' U' U' := fun v hv => by
    rw [← hΦΨ v hv, ← hconj _ (hΨ hv)]
    exact hΦ (hT (hΨ hv))
  have hconj' : ∀ v ∈ U', Ψ (T' v) = T (Ψ v) := fun v hv => by
    rw [← hΦΨ v hv, ← hconj _ (hΨ hv), hΨΦ _ (hT (hΨ hv)), hΨΦ _ (hΨ hv)]
  exact ⟨fun h => h.of_conj Φ Ψ hΦ hΨ hΦΨ hΨΦ hΦc hT hconj,
    fun h => h.of_conj Ψ Φ hΨ hΦ hΨΦ hΦΨ hΨc hT' hconj'⟩

/-! ### Theorem 7.1.1: Knaster–Tarski on an order interval -/

variable {X : Type*}

/-- Iterates of an order-preserving self-map of `[v₁, v₂]` preserve the order. -/
theorem iterate_le_iterate_of_monotoneOn {v₁ v₂ : X → ℝ} {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    {u w : X → ℝ} (hu : u ∈ Set.Icc v₁ v₂) (hw : w ∈ Set.Icc v₁ v₂) (huw : u ≤ w) (k : ℕ) :
    T^[k] u ≤ T^[k] w := by
  induction k with
  | zero => simpa using huw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact hmono (hmaps.iterate k hu) (hmaps.iterate k hw) ih

/-- **Theorem 7.1.1 (Knaster–Tarski)** (p. 214): an order-preserving self-map `T` of `[v₁, v₂]` has
least and greatest fixed points `a ≤ b`, and `Tᵏv₁ ≤ a ≤ b ≤ Tᵏv₂` for all `k`. -/
theorem knaster_tarski {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂)) :
    ∃ a ∈ Set.Icc v₁ v₂, ∃ b ∈ Set.Icc v₁ v₂, IsFixedPt T a ∧ IsFixedPt T b ∧
      (∀ v ∈ Set.Icc v₁ v₂, IsFixedPt T v → a ≤ v ∧ v ≤ b) ∧
      ∀ k : ℕ, T^[k] v₁ ≤ a ∧ b ≤ T^[k] v₂ := by
  have : Fact (v₁ ≤ v₂) := ⟨h12⟩
  let f : Set.Icc v₁ v₂ →o Set.Icc v₁ v₂ :=
    ⟨fun w => ⟨T w.1, hmaps w.2⟩, fun w w' hww' => hmono w.2 w'.2 hww'⟩
  have hfa : IsFixedPt T f.lfp.1 := congrArg Subtype.val f.isFixedPt_lfp
  have hfb : IsFixedPt T f.gfp.1 := congrArg Subtype.val f.isFixedPt_gfp
  have hv1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, h12⟩
  have hv2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨h12, le_rfl⟩
  refine ⟨f.lfp.1, f.lfp.2, f.gfp.1, f.gfp.2, hfa, hfb, fun v hv hvfix => ?_, fun k => ⟨?_, ?_⟩⟩
  · have hv' : f ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext hvfix
    exact ⟨OrderHom.lfp_le_fixed f hv', OrderHom.le_gfp f hv'.ge⟩
  · have := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 f.lfp.2 f.lfp.2.1 k
    rwa [(hfa.iterate k).eq] at this
  · have := iterate_le_iterate_of_monotoneOn hmaps hmono f.gfp.2 hv2 f.gfp.2.2 k
    rwa [(hfb.iterate k).eq] at this

/-- Exercise 7.1.1 (p. 214): if `v₁ ≠ v₂`, some order-preserving self-map of `[v₁, v₂]` (the
identity) has a continuum of fixed points, the segment `t ↦ v₁ + t(v₂ − v₁)`, `t ∈ [0, 1]`. -/
theorem exists_continuum_fixedPts {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) (hne : v₁ ≠ v₂) :
    ∃ T : (X → ℝ) → (X → ℝ), Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂) ∧
      MonotoneOn T (Set.Icc v₁ v₂) ∧ ∃ φ : ℝ → X → ℝ, Set.InjOn φ (Set.Icc 0 1) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ∈ Set.Icc v₁ v₂ ∧ IsFixedPt T (φ t) := by
  refine ⟨id, fun v hv => hv, fun _ _ _ _ h => h, fun t => v₁ + t • (v₂ - v₁), ?_, fun t ht => ?_⟩
  · intro s _ t _ hst
    have h1 : (s - t) • (v₂ - v₁) = 0 := by
      have := congrArg (fun w => w - v₁) hst
      simp only [add_sub_cancel_left] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.1 h1 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd (sub_eq_zero.1 h).symm hne
  · refine ⟨⟨fun x => ?_, fun x => ?_⟩, rfl⟩
    · have := mul_nonneg ht.1 (sub_nonneg.2 (h12 x))
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linarith
    · have := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.2 (h12 x))
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linarith

/-! ### Theorem 7.1.3 (Du) -/

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (ii): an order-preserving concave self-map of
`[v₁, v₂]` with `Tv₁ ≥ v₁ + δ(v₂ − v₁)` for some `δ > 0` is globally stable on `[v₁, v₂]`. -/
theorem du_concave {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconc : ConcaveOn ℝ (Set.Icc v₁ v₂) T) {δ : ℝ} (hδ : 0 < δ)
    (hT1 : v₁ + δ • (v₂ - v₁) ≤ T v₁) : GloballyStableOn T (Set.Icc v₁ v₂) := by
  set d := min δ 1 with hd
  have hd0 : 0 < d := lt_min hδ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdδ : d ≤ δ := min_le_left _ _
  have hv1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, h12⟩
  have hv2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨h12, le_rfl⟩
  have hT1' : ∀ x, v₁ x + d * (v₂ x - v₁ x) ≤ T v₁ x := fun x => by
    have h1 := hT1 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    nlinarith [sub_nonneg.2 (h12 x)]
  set q : ℕ → ℝ := fun k => (1 - d) ^ k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => pow_nonneg (by linarith) k
  have hq1 : ∀ k, q k ≤ 1 := fun k => pow_le_one₀ (by linarith) (by linarith)
  -- `Tᵏv₁ ≥ v₁ + (1 − qₖ)(Tᵏv₂ − v₁)`
  have key : ∀ k x, v₁ x + (1 - q k) * (T^[k] v₂ x - v₁ x) ≤ T^[k] v₁ x := by
    intro k
    induction k with
    | zero => intro x; simp [hq]
    | succ k ih =>
      intro x
      have hwk := hmaps.iterate k hv2
      have huk := hmaps.iterate k hv1
      set z : X → ℝ := q k • v₁ + (1 - q k) • T^[k] v₂ with hz
      have hzmem : z ∈ Set.Icc v₁ v₂ :=
        (convex_Icc v₁ v₂) hv1 hwk (hq0 k) (by linarith [hq1 k]) (by ring)
      have hzle : z ≤ T^[k] v₁ := fun y => by
        have := ih y
        simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      have hA := hmono hzmem huk hzle x
      have hB := hconc.2 hv1 hwk (hq0 k) (by linarith [hq1 k]) (by ring : q k + (1 - q k) = 1) x
      have hD := (hmaps hwk).2 x
      rw [iterate_succ_apply', iterate_succ_apply']
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hB
      have hqs : q (k + 1) = q k * (1 - d) := by simp only [hq]; ring
      rw [hqs]
      nlinarith [mul_nonneg (mul_nonneg (hq0 k) hd0.le) (sub_nonneg.2 hD),
        mul_le_mul_of_nonneg_left (hT1' x) (hq0 k)]
  -- the orbits of `v₁` and `v₂` are `qₖ(v₂ − v₁)` apart
  have gap : ∀ k x, T^[k] v₂ x - T^[k] v₁ x ≤ q k * (v₂ x - v₁ x) := fun k x => by
    have h1 := key k x
    have h2 := ((hmaps.iterate k hv2).2 x)
    nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right h2 (v₁ x)) (hq0 k)]
  have hqlim : Tendsto q atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  obtain ⟨a, ha, -, -, hafix, -, -, -⟩ := knaster_tarski h12 hmaps hmono
  -- every orbit is squeezed onto `a`
  have hsq : ∀ v ∈ Set.Icc v₁ v₂, ∀ k x,
      a x - q k * (v₂ x - v₁ x) ≤ T^[k] v x ∧ T^[k] v x ≤ a x + q k * (v₂ x - v₁ x) := by
    intro v hv k x
    have hlo := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 hv hv.1 k x
    have hhi := iterate_le_iterate_of_monotoneOn hmaps hmono hv hv2 hv.2 k x
    have halo := iterate_le_iterate_of_monotoneOn hmaps hmono hv1 ha ha.1 k x
    have hahi := iterate_le_iterate_of_monotoneOn hmaps hmono ha hv2 ha.2 k x
    rw [(hafix.iterate k).eq] at halo hahi
    have := gap k x
    constructor <;> linarith
  refine ⟨a, ha, hafix, fun v hv hvfix => ?_, fun v hv => ?_⟩
  · funext x
    have h1 : ∀ k, |v x - a x| ≤ q k * (v₂ x - v₁ x) := fun k => by
      have := hsq v hv k x
      rw [(hvfix.iterate k).eq] at this
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    have h2 : Tendsto (fun k => q k * (v₂ x - v₁ x)) atTop (𝓝 0) := by
      simpa using hqlim.mul_const (v₂ x - v₁ x)
    have h3 : |v x - a x| ≤ 0 := ge_of_tendsto' h2 h1
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h3)
  · rw [tendsto_pi_nhds]
    intro x
    have h2 : Tendsto (fun k => q k * (v₂ x - v₁ x)) atTop (𝓝 0) := by
      simpa using hqlim.mul_const (v₂ x - v₁ x)
    have hl : Tendsto (fun k => a x - q k * (v₂ x - v₁ x)) atTop (𝓝 (a x)) := by
      simpa using (tendsto_const_nhds (x := a x)).sub h2
    have hu : Tendsto (fun k => a x + q k * (v₂ x - v₁ x)) atTop (𝓝 (a x)) := by
      simpa using (tendsto_const_nhds (x := a x)).add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun k => (hsq v hv k x).1)
      (fun k => (hsq v hv k x).2)

/-- Condition (i) of Theorem 7.1.3 implies condition (ii): if `Tv₁ ≫ v₁` there is a `δ > 0` with
`Tv₁ ≥ v₁ + δ(v₂ − v₁)` (p. 217). -/
theorem exists_delta_of_lt [Finite X] {v₁ v₂ w : X → ℝ} (h12 : v₁ ≤ v₂) (hw : ∀ x, v₁ x < w x) :
    ∃ δ : ℝ, 0 < δ ∧ v₁ + δ • (v₂ - v₁) ≤ w := by
  classical
  have := Fintype.ofFinite X
  set g : X → ℝ := fun x => (w x - v₁ x) / (v₂ x - v₁ x + 1) with hg
  have hgpos : ∀ x, 0 < g x := fun x =>
    div_pos (sub_pos.2 (hw x)) (by linarith [sub_nonneg.2 (h12 x)])
  set S : Finset ℝ := insert 1 (univ.image g) with hS
  have hSne : S.Nonempty := insert_nonempty _ _
  refine ⟨S.min' hSne, ?_, fun x => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases mem_insert.1 hy with h | h
    · rw [h]; exact one_pos
    · obtain ⟨x, -, rfl⟩ := mem_image.1 h
      exact hgpos x
  · have hle : S.min' hSne ≤ g x :=
      min'_le _ _ (mem_insert_of_mem (mem_image_of_mem g (mem_univ x)))
    have hpos : 0 < S.min' hSne := by
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases mem_insert.1 hy with h | h
      · rw [h]; exact one_pos
      · obtain ⟨x, -, rfl⟩ := mem_image.1 h
        exact hgpos x
    have h0 := sub_nonneg.2 (h12 x)
    have hden : 0 < v₂ x - v₁ x + 1 := by linarith
    have h1 : g x * (v₂ x - v₁ x) ≤ w x - v₁ x := by
      rw [hg]
      simp only
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [sub_pos.2 (hw x)]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_right hle h0]

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (i): an order-preserving concave self-map of
`[v₁, v₂]` with `Tv₁ ≫ v₁` is globally stable on `[v₁, v₂]`. -/
theorem du_concave_of_lt [Finite X] {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconc : ConcaveOn ℝ (Set.Icc v₁ v₂) T) (hT1 : ∀ x, v₁ x < T v₁ x) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_lt h12 hT1
  exact du_concave h12 hmaps hmono hconc hδ h

/-- `w ∈ [−v₂, −v₁]` iff `−w ∈ [v₁, v₂]`. -/
theorem neg_mem_Icc_iff {v₁ v₂ w : X → ℝ} : -w ∈ Set.Icc v₁ v₂ ↔ w ∈ Set.Icc (-v₂) (-v₁) := by
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨neg_le.1 h2, le_neg.1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_neg.2 h2, neg_le.2 h1⟩

/-- If the reflection `w ↦ −T(−w)` is globally stable on `[−v₂, −v₁]`, then `T` is globally stable
on `[v₁, v₂]`. -/
theorem globallyStableOn_of_reflect {v₁ v₂ : X → ℝ} {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂))
    (h : GloballyStableOn (fun w => -T (-w)) (Set.Icc (-v₂) (-v₁))) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  refine h.of_conj (fun w => -w) (fun w => -w) (fun w hw => neg_mem_Icc_iff.2 hw)
    (fun w hw => by rw [← neg_mem_Icc_iff, neg_neg]; exact hw) (fun w _ => neg_neg w)
    (fun w _ => neg_neg w) continuous_neg.continuousOn (fun w hw => ?_) (fun w _ => by simp)
  rw [← neg_mem_Icc_iff]
  simpa using hmaps (neg_mem_Icc_iff.2 hw)

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (iv): an order-preserving convex self-map of
`[v₁, v₂]` with `Tv₂ ≤ v₂ − δ(v₂ − v₁)` for some `δ > 0` is globally stable on `[v₁, v₂]`. -/
theorem du_convex {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconv : ConvexOn ℝ (Set.Icc v₁ v₂) T) {δ : ℝ} (hδ : 0 < δ)
    (hT2 : T v₂ ≤ v₂ - δ • (v₂ - v₁)) : GloballyStableOn T (Set.Icc v₁ v₂) := by
  have hmem : ∀ w ∈ Set.Icc (-v₂) (-v₁), -w ∈ Set.Icc v₁ v₂ := fun w hw => neg_mem_Icc_iff.2 hw
  refine globallyStableOn_of_reflect hmaps (du_concave (neg_le_neg h12) ?_ ?_ ?_ hδ ?_)
  · intro w hw
    rw [← neg_mem_Icc_iff, neg_neg]
    exact hmaps (hmem w hw)
  · intro u hu w hw huw
    exact neg_le_neg (hmono (hmem w hw) (hmem u hu) (neg_le_neg huw))
  · refine ⟨convex_Icc _ _, fun u hu w hw a b ha hb hab => ?_⟩
    have := hconv.2 (hmem u hu) (hmem w hw) ha hb hab
    have h2 : -(a • u + b • w) = a • -u + b • -w := by rw [neg_add, smul_neg, smul_neg]
    change a • -T (-u) + b • -T (-w) ≤ -T (-(a • u + b • w))
    rw [h2, smul_neg, smul_neg, ← neg_add]
    exact neg_le_neg this
  · intro x
    have := hT2 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply, neg_neg]
      at this ⊢
    linarith

/-- **Theorem 7.1.3 (Du)** (p. 217), condition (iii): an order-preserving convex self-map of
`[v₁, v₂]` with `Tv₂ ≪ v₂` is globally stable on `[v₁, v₂]`. -/
theorem du_convex_of_lt [Finite X] {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂) {T : (X → ℝ) → (X → ℝ)}
    (hmaps : Set.MapsTo T (Set.Icc v₁ v₂) (Set.Icc v₁ v₂)) (hmono : MonotoneOn T (Set.Icc v₁ v₂))
    (hconv : ConvexOn ℝ (Set.Icc v₁ v₂) T) (hT2 : ∀ x, T v₂ x < v₂ x) :
    GloballyStableOn T (Set.Icc v₁ v₂) := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_lt (neg_le_neg h12) (w := -T v₂)
    (fun x => by simpa using hT2 x)
  refine du_convex h12 hmaps hmono hconv hδ fun x => ?_
  have := h x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.neg_apply] at this ⊢
  linarith

/-- Exercise 7.1.6 (p. 217): if `F` and `G` are self-maps of a convex set `D`, `F` is order
preserving and both are concave, then `F ∘ G` is concave on `D`. -/
theorem concaveOn_comp {D : Set (X → ℝ)} {F G : (X → ℝ) → (X → ℝ)} (hG : Set.MapsTo G D D)
    (hFm : MonotoneOn F D) (hF : ConcaveOn ℝ D F) (hGc : ConcaveOn ℝ D G) :
    ConcaveOn ℝ D (F ∘ G) := by
  refine ⟨hF.1, fun u hu w hw a b ha hb hab => ?_⟩
  have h1 := hF.2 (hG hu) (hG hw) ha hb hab
  have hmem : a • G u + b • G w ∈ D := hF.1 (hG hu) (hG hw) ha hb hab
  have h2 := hFm hmem (hG (hF.1 hu hw ha hb hab)) (hGc.2 hu hw ha hb hab)
  exact h1.trans h2

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.1–§8.1.3.2
(pp. 246–256). Restated from the `FiniteStates/RecursiveDecisionProcesses` project
(Chapter 8), whose optimality results Chapter 9 proves through abstract dynamic programs.

A recursive decision process `(Γ, V, B)` has a nonempty feasible correspondence
`Γ`, a value space `V ⊆ ℝ^X` and an aggregator `B(x, a, v)` that is monotone in
`v` on `V` (8.2) and consistent (8.3): every policy operator
`(T_σ v)(x) = B(x, σ(x), v)` maps `V` into itself.

* Exercise 8.1.6: policy operators are order-preserving self-maps of `V`.
* Well-posedness (unique `σ`-value functions `v_σ`), global stability and
  continuity (§8.1.2).
* Greedy policies (8.13), the Bellman operator, Exercise 8.1.7 (least and
  greatest elements of `{T_σ v}`), Exercise 8.1.8 (`T = ⋁_σ T_σ`, greedy iff
  `T_σ v = Tv`, `T` an order-preserving self-map of `V`) and Exercise 8.1.9
  ((8.14)–(8.15)).
* The value function `v* = ⋁_σ v_σ` (8.19) and optimal policies.
* The Howard operator (8.17), the OPI operator `W_m`, the HPI and OPI sequences
  (Algorithms 8.1–8.2, (8.18)), and Exercise 8.1.10 (OPI with `m = 1` is VFI).
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- A recursive decision process `(Γ, V, B)` (§8.1.1) on finite state and action spaces. The
aggregator is defined on all of `ℝ^X`; monotonicity (8.2) is required on `V` at feasible pairs, and
consistency (8.3) says that every policy operator maps `V` into itself. -/
structure RDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  V : Set (X → ℝ)
  B : X → A → (X → ℝ) → ℝ
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ V, ∀ w ∈ V, v ≤ w → B x a v ≤ B x a w
  consistent : ∀ σ : X → A, (∀ x, σ x ∈ Γ x) → ∀ v ∈ V, (fun x => B x (σ x) v) ∈ V

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- A feasible policy: `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ R.Γ x

/-- The set `Σ` of feasible policies, as a subtype. -/
abbrev Policy := {σ : X → A // R.IsFeasible σ}

/-- A feasible policy, choosing any feasible action in each state. -/
noncomputable def defaultPolicy : R.Policy :=
  ⟨fun x => (R.Γ_nonempty x).choose, fun x => (R.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty R.Policy := ⟨R.defaultPolicy⟩

/-! ### Policy operators (§8.1.2.1) -/

/-- The policy operator (8.12): `(T_σ v)(x) = B(x, σ(x), v)`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => R.B x (σ x) v

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) : R.Tσ σ v x = R.B x (σ x) v := rfl

/-- Exercise 8.1.6 (p. 251): `T_σ` maps `V` into itself. -/
theorem Tσ_mapsTo {σ : X → A} (hσ : R.IsFeasible σ) : MapsTo (R.Tσ σ) R.V R.V :=
  fun v hv => R.consistent σ hσ v hv

/-- Exercise 8.1.6 (p. 251): `T_σ` is order preserving on `V`. -/
theorem Tσ_monotoneOn {σ : X → A} (hσ : R.IsFeasible σ) : MonotoneOn (R.Tσ σ) R.V :=
  fun v hv w hw hvw x => R.mono x (σ x) (hσ x) v hv w hw hvw

/-- `R` is well-posed (§8.1.2.2) if every `T_σ` has a unique fixed point in `V`. -/
def WellPosed : Prop := ∀ σ : X → A, R.IsFeasible σ → ∃! v, v ∈ R.V ∧ IsFixedPt (R.Tσ σ) v

/-- `R` is globally stable (§8.1.2.2) if every `T_σ` is globally stable on `V`. -/
def IsGloballyStable : Prop := ∀ σ : X → A, R.IsFeasible σ → GloballyStableOn (R.Tσ σ) R.V

/-- Every globally stable RDP is well-posed (p. 253). -/
theorem IsGloballyStable.wellPosed {R : RDP X A} (h : R.IsGloballyStable) : R.WellPosed :=
  fun σ hσ => (h σ hσ).existsUnique

/-- `R` is continuous (§8.1.2.3) if `B(x, a, ·)` is sequentially continuous on `V` at feasible
pairs. -/
def IsContinuous : Prop :=
  ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ vk : ℕ → X → ℝ, (∀ k, vk k ∈ R.V) →
    Tendsto vk atTop (𝓝 v) → Tendsto (fun k => R.B x a (vk k)) atTop (𝓝 (R.B x a v))

open Classical in
/-- The `σ`-value function: the unique fixed point of `T_σ` in `V` when it exists (§8.1.2.2). -/
noncomputable def vσ (σ : X → A) : X → ℝ :=
  if h : ∃! v, v ∈ R.V ∧ IsFixedPt (R.Tσ σ) v then h.exists.choose else 0

theorem vσ_spec {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.vσ σ ∈ R.V ∧ IsFixedPt (R.Tσ σ) (R.vσ σ) := by
  classical
  have h := hw σ hσ
  unfold vσ
  split_ifs
  exact h.exists.choose_spec

theorem vσ_mem {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.vσ σ ∈ R.V := (vσ_spec hw hσ).1

theorem isFixedPt_vσ {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    IsFixedPt (R.Tσ σ) (R.vσ σ) := (vσ_spec hw hσ).2

/-- `v_σ` is the only fixed point of `T_σ` in `V`. -/
theorem eq_vσ_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ)
    {v : X → ℝ} (hv : v ∈ R.V) (hfix : IsFixedPt (R.Tσ σ) v) : v = R.vσ σ :=
  (hw σ hσ).unique ⟨hv, hfix⟩ (vσ_spec hw hσ)

/-- Under global stability, `T_σᵏ v → v_σ` for every `v ∈ V`. -/
theorem tendsto_iterate_Tσ {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) {v : X → ℝ} (hv : v ∈ R.V) :
    Tendsto (fun k : ℕ => (R.Tσ σ)^[k] v) atTop (𝓝 (R.vσ σ)) := by
  obtain ⟨u, hu, hfix, -, hconv⟩ := hR σ hσ
  rw [← eq_vσ_of_isFixedPt hR.wellPosed hσ hu hfix]
  exact hconv v hv

/-! ### Greedy policies and the Bellman operator (§8.1.3.1) -/

/-- The Bellman operator: `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a v

theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ R.Γ x) : R.B x a v ≤ R.T v x :=
  Finset.le_sup' (fun a => R.B x a v) ha

theorem Tσ_le_T {σ : X → A} (hσ : R.IsFeasible σ) (v : X → ℝ) : R.Tσ σ v ≤ R.T v := fun x =>
  R.B_le_T v (hσ x)

/-- A `v`-greedy policy (8.13): feasible, with `σ(x)` maximising `B(x, ·, v)` over `Γ(x)`. -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  R.IsFeasible σ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v ≤ R.B x (σ x) v

/-- A `v`-greedy policy, chosen by maximising in each state (p. 254). -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : R.greedy v x ∈ R.Γ x :=
  ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1

/-- At least one `v`-greedy policy exists (p. 254). -/
theorem isGreedy_greedy (v : X → ℝ) : R.IsGreedy v (R.greedy v) :=
  ⟨R.greedy_mem v, fun x a ha =>
    ((R.Γ x).exists_max_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : R.Policy := ⟨R.greedy v, R.greedy_mem v⟩

/-- Exercise 8.1.8 (ii) (p. 254): a feasible `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.IsGreedy v σ ↔ R.Tσ σ v = R.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (R.B_le_T v (hσ x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨hσ, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ_apply] at this
    rw [this]
    exact R.B_le_T v ha

theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : R.IsGreedy v σ) :
    R.Tσ σ v = R.T v := (R.isGreedy_iff_Tσ_eq_T v hσ.1).1 hσ

/-- Exercise 8.1.8 (iii) (p. 254): `T` maps `V` into itself, since `Tv = T_σ v` for a `v`-greedy
`σ`. -/
theorem T_mapsTo : MapsTo R.T R.V R.V := fun v hv => by
  rw [← R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
  exact R.Tσ_mapsTo (R.greedy_mem v) hv

/-- Exercise 8.1.8 (iii) (p. 254): `T` is order preserving on `V`. -/
theorem T_monotoneOn : MonotoneOn R.T R.V := fun v hv w hw hvw x =>
  Finset.sup'_mono_fun fun a ha => R.mono x a ha v hv w hw hvw

/-- Exercise 8.1.8 (i) (p. 254): `Tv = ⋁_σ T_σ v`. -/
theorem T_apply_eq_sup' [DecidableEq X] [DecidableEq A] (v : X → ℝ) (x : X) :
    R.T v x = univ.sup' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy =>
      R.Tσ σ.1 v x := by
  apply le_antisymm
  · rw [← congrFun (R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)) x]
    exact Finset.le_sup' (fun σ : R.Policy => R.Tσ σ.1 v x) (mem_univ (R.greedyPolicy v))
  · exact Finset.sup'_le _ _ fun σ _ => R.Tσ_le_T σ.2 v x

/-- Exercise 8.1.7 (p. 254): `{T_σ v}` has a greatest element, `Tv`, attained by the greedy
policies. -/
theorem isGreatest_Tσ (v : X → ℝ) : IsGreatest (Set.range fun σ : R.Policy => R.Tσ σ.1 v) (R.T v) :=
  ⟨⟨R.greedyPolicy v, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)⟩, by
    rintro _ ⟨σ, rfl⟩
    exact R.Tσ_le_T σ.2 v⟩

/-- A policy minimising `B(x, ·, v)` in each state. -/
noncomputable def antiGreedy (v : X → ℝ) : X → A := fun x =>
  ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose

/-- Exercise 8.1.7 (p. 254): `{T_σ v}` has a least element. -/
theorem isLeast_Tσ (v : X → ℝ) :
    IsLeast (Set.range fun σ : R.Policy => R.Tσ σ.1 v) (R.Tσ (R.antiGreedy v) v) :=
  ⟨⟨⟨R.antiGreedy v, fun x =>
      ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1⟩, rfl⟩, by
    rintro _ ⟨σ, rfl⟩ x
    exact ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.2 _
      (σ.2 x)⟩

/-- Exercise 8.1.9 (8.14) (p. 255): `(Tᵏv)(x) = max_{a ∈ Γ(x)} B(x, a, Tᵏ⁻¹v)`. -/
theorem iterate_T_succ (v : X → ℝ) (k : ℕ) (x : X) :
    R.T^[k + 1] v x = (R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a (R.T^[k] v) := by
  rw [iterate_succ_apply']
  rfl

/-- Exercise 8.1.9 (8.15) (p. 255): `(T_σᵏv)(x) = B(x, σ(x), T_σᵏ⁻¹v)`. -/
theorem iterate_Tσ_succ (σ : X → A) (v : X → ℝ) (k : ℕ) (x : X) :
    (R.Tσ σ)^[k + 1] v x = R.B x (σ x) ((R.Tσ σ)^[k] v) := by
  rw [iterate_succ_apply']
  rfl

/-- `Tᵏ` maps `V` into itself and is order preserving on `V`. -/
theorem iterate_T_mono {v w : X → ℝ} (hv : v ∈ R.V) (hw : w ∈ R.V) (hvw : v ≤ w) (k : ℕ) :
    R.T^[k] v ≤ R.T^[k] w := by
  induction k with
  | zero => simpa using hvw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact R.T_monotoneOn (R.T_mapsTo.iterate k hv) (R.T_mapsTo.iterate k hw) ih

theorem iterate_Tσ_mono {σ : X → A} (hσ : R.IsFeasible σ) {v w : X → ℝ} (hv : v ∈ R.V)
    (hw : w ∈ R.V) (hvw : v ≤ w) (k : ℕ) : (R.Tσ σ)^[k] v ≤ (R.Tσ σ)^[k] w := by
  induction k with
  | zero => simpa using hvw
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact R.Tσ_monotoneOn hσ ((R.Tσ_mapsTo hσ).iterate k hv) ((R.Tσ_mapsTo hσ).iterate k hw) ih

/-! ### Value function and optimality (§8.1.3.3) -/

variable [DecidableEq X] [DecidableEq A]

/-- The value function (8.19): `v*(x) = max_{σ ∈ Σ} v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy => R.vσ σ.1 x

theorem vσ_le_vstar {σ : X → A} (hσ : R.IsFeasible σ) : R.vσ σ ≤ R.vstar := fun x =>
  Finset.le_sup' (fun τ : R.Policy => R.vσ τ.1 x) (mem_univ (⟨σ, hσ⟩ : R.Policy))

/-- An optimal policy (p. 257): `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := R.IsFeasible σ ∧ R.vσ σ = R.vstar

/-- `R` satisfies Bellman's principle of optimality (p. 257). -/
def PrincipleOfOptimality : Prop := ∀ σ, R.IsFeasible σ → (R.IsOptimal σ ↔ R.IsGreedy R.vstar σ)

/-! ### Algorithms (§8.1.3.2) -/

omit [DecidableEq X] [DecidableEq A] in
/-- The Howard operator (8.17): `Hv = v_σ` for the chosen `v`-greedy `σ`. -/
noncomputable def howard (v : X → ℝ) : X → ℝ := R.vσ (R.greedy v)

omit [DecidableEq X] [DecidableEq A] in
/-- The OPI operator: `W_m v = T_σᵐ v` for the chosen `v`-greedy `σ`. -/
noncomputable def opiW (m : ℕ) (v : X → ℝ) : X → ℝ := (R.Tσ (R.greedy v))^[m] v

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI policies of Algorithm 8.1 started from `σ`: `σ₀ = σ` and `σₖ₊₁` is `v_{σₖ}`-greedy. -/
noncomputable def hpiPolicy (σ : R.Policy) : ℕ → R.Policy
  | 0 => σ
  | k + 1 => R.greedyPolicy (R.vσ (hpiPolicy σ k).1)

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI values: `vₖ = v_{σₖ}`, so `vₖ₊₁ = H vₖ`. -/
noncomputable def hpiValue (σ : R.Policy) (k : ℕ) : X → ℝ := R.vσ (R.hpiPolicy σ k).1

omit [DecidableEq X] [DecidableEq A] in
theorem hpiValue_succ (σ : R.Policy) (k : ℕ) :
    R.hpiValue σ (k + 1) = R.howard (R.hpiValue σ k) := rfl

omit [DecidableEq X] [DecidableEq A] in
/-- The OPI value sequence (8.18): `vₖ = W_mᵏ v_σ`. -/
noncomputable def opiValue (m : ℕ) (σ : X → A) (k : ℕ) : X → ℝ := (R.opiW m)^[k] (R.vσ σ)

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.10 (p. 256): with `m = 1`, OPI is value function iteration, `vₖ = Tᵏv₀`. -/
theorem opiValue_one (σ : X → A) (k : ℕ) : R.opiValue 1 σ k = R.T^[k] (R.vσ σ) := by
  have h : R.opiW 1 = R.T := by
    funext v
    simp only [opiW, iterate_one]
    exact R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)
  simp [opiValue, h]

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.11 (p. 259): for policies `σ₁, σ₂, …` and `v ∈ V`,
`T_{σₖ} ⋯ T_{σ₁} v ≤ Tᵏ v`. -/
theorem nonstationary_le (σs : ℕ → X → A) (hσs : ∀ k, R.IsFeasible (σs k)) {v : X → ℝ}
    (hv : v ∈ R.V) : ∀ k, (Nat.rec v fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k ∈ R.V ∧
      (Nat.rec v fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k ≤ R.T^[k] v := by
  intro k
  induction k with
  | zero => exact ⟨hv, le_rfl⟩
  | succ k ih =>
    refine ⟨R.Tσ_mapsTo (hσs k) ih.1, ?_⟩
    rw [iterate_succ_apply']
    exact (R.Tσ_le_T (hσs k) _).trans (R.T_monotoneOn ih.1 (R.T_mapsTo.iterate k hv) ih.2)

end RDP

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.1 (pp. 292–294).

A self-map `S` of a partially ordered set with exactly one fixed point `v̄` is upward stable if
`v ≼ Sv` implies `v ≼ v̄`, downward stable if `Sv ≼ v` implies `v̄ ≼ v`, and order stable if both
hold. No topology is involved.

* Exercise 9.1.1: `Tv = r + Av` with `A ≥ 0` and `ρ(A) < 1` is order stable on `ℝ^X`.
* Lemma 9.1.1: an order-preserving globally stable self-map of `V ⊆ ℝ^X` is order stable on `V`.
* Lemma 9.1.2: `S` is order stable on `V` iff it is order stable on the order dual `Vᵒᵈ`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- `S` is order stable (p. 293): it has exactly one fixed point `v̄`, and it is upward stable
(`v ≼ Sv ⇒ v ≼ v̄`) and downward stable (`Sv ≼ v ⇒ v̄ ≼ v`). -/
def OrderStable {V : Type*} [PartialOrder V] (S : V → V) : Prop :=
  ∃ u, IsFixedPt S u ∧ (∀ w, IsFixedPt S w → w = u) ∧ (∀ v, v ≤ S v → v ≤ u) ∧
    ∀ v, S v ≤ v → u ≤ v

/-- Upward and downward stability around some fixed point already force it to be the only one. -/
theorem orderStable_of_up_down {V : Type*} [PartialOrder V] {S : V → V} {u : V}
    (hu : IsFixedPt S u) (hup : ∀ v, v ≤ S v → v ≤ u) (hdown : ∀ v, S v ≤ v → u ≤ v) :
    OrderStable S :=
  ⟨u, hu, fun w hw => le_antisymm (hup w hw.eq.ge) (hdown w hw.eq.le), hup, hdown⟩

/-- Lemma 9.1.1 (p. 293), on a whole space: an order-preserving globally stable map on an
order-closed space (such as `ℝ^X` or `ℝ^{X × A}`) is order stable. -/
theorem orderStable_of_globallyStable {W : Type*} [TopologicalSpace W] [PartialOrder W]
    [OrderClosedTopology W] {S : W → W} (hm : Monotone S) (hs : GloballyStable S) :
    OrderStable S := by
  obtain ⟨u, hu, -, hlim⟩ := hs
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · have hk : ∀ k, v ≤ S^[k] v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact hv.trans (hm ih)
    exact ge_of_tendsto' (hlim v) hk
  · have hk : ∀ k, S^[k] v ≤ v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact (hm ih).trans hv
    exact le_of_tendsto' (hlim v) hk

/-- **Lemma 9.1.1** (p. 293): if `T` is an order-preserving self-map of `V ⊆ ℝ^X` that is globally
stable on `V`, then `T` (restricted to `V`) is order stable on `V`. -/
theorem orderStable_restrict {X : Type*} {U : Set (X → ℝ)} {S : (X → ℝ) → (X → ℝ)}
    (hmaps : MapsTo S U U) (hm : MonotoneOn S U) (hs : GloballyStableOn S U) :
    OrderStable (hmaps.restrict S U U) := by
  obtain ⟨u, huU, hu, -, hlim⟩ := hs
  have hfix : IsFixedPt (hmaps.restrict S U U) ⟨u, huU⟩ := Subtype.ext hu.eq
  have hiter : ∀ (v : U) k, (S^[k] v) ∈ U := fun v k => hmaps.iterate k v.2
  refine orderStable_of_up_down hfix (fun v hv => ?_) fun v hv => ?_
  · have hv' : (v : X → ℝ) ≤ S v := hv
    have hk : ∀ k, (v : X → ℝ) ≤ S^[k] v := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact hv'.trans (hm v.2 (hiter v k) ih)
    change (v : X → ℝ) ≤ u
    intro x
    exact ge_of_tendsto' (tendsto_pi_nhds.1 (hlim v v.2) x) fun k => hk k x
  · have hv' : S v ≤ (v : X → ℝ) := hv
    have hk : ∀ k, S^[k] v ≤ (v : X → ℝ) := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        exact (hm (hiter v k) v.2 ih).trans hv'
    change u ≤ (v : X → ℝ)
    intro x
    exact le_of_tendsto' (tendsto_pi_nhds.1 (hlim v v.2) x) fun k => hk k x

/-- **Exercise 9.1.1** (p. 293): for `A ≥ 0` with `ρ(A) < 1`, `Tv = r + Av` is order stable on
`ℝ^X`. -/
theorem orderStable_affineOp {X : Type*} [Fintype X] [Nonempty X]
    {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x') (hρ : specRad A < 1) (r : X → ℝ) :
    OrderStable (affineOp A r) := by
  classical
  exact orderStable_of_globallyStable (fun _ _ huv => add_le_add (mulVec_le_mulVec_of_nonneg hA huv)
    le_rfl) (globallyStable_affineOp hρ r)

/-- **Lemma 9.1.2** (p. 294): `S` is order stable on `V` iff it is order stable on the order dual
`Vᵒᵈ`. -/
theorem orderStable_dual_iff {V : Type*} [PartialOrder V] (S : V → V) :
    OrderStable (OrderDual.toDual ∘ S ∘ OrderDual.ofDual : Vᵒᵈ → Vᵒᵈ) ↔ OrderStable S := by
  constructor
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.ofDual u) (congrArg OrderDual.ofDual hu.eq)
      (fun v hv => hdown (OrderDual.toDual v) hv) fun v hv => hup (OrderDual.toDual v) hv
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.toDual u) (congrArg OrderDual.toDual hu.eq)
      (fun v hv => hdown (OrderDual.ofDual v) hv) fun v hv => hup (OrderDual.ofDual v) hv

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Abstract dynamic programs and max-optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.2 and §9.2.1.1–§9.2.1.5
(pp. 294–300), with the proofs of §B.4 (pp. 349–351).

An abstract dynamic program (ADP) `(V, {T_σ}_{σ ∈ Σ})` is a family of self-maps of a partially
ordered set `V` such that every `{T_σ v}_σ` has a greatest and a least element. Nothing else is
assumed: no topology, no finiteness of `V`.

* Greedy policies, the Bellman operator `Tv = ⋁_σ T_σ v` (9.5), Exercise 9.2.1, well-posedness,
  `σ`-value functions, `V_u = {v ≼ Tv}` and Exercise 9.2.3 (`V_Σ ⊆ V_u`), the Howard operator
  and HPI.
* Finite, order stable and max-stable ADPs (§9.2.1.3).
* Lemma B.4.1, Proposition 9.2.1 (finite and order stable implies max-stable),
  Proposition 9.2.5 (max-stable ADPs: the value function exists, is the unique fixed point of
  `T`, Bellman's principle of optimality, an optimal policy exists) and **Theorem 9.2.4**
  (max-optimality for finite order stable ADPs, with finite termination of HPI).
-/

open Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- An abstract dynamic program (§9.1.2.2): policy operators `T_σ`, `σ ∈ P`, on a partially
ordered set `V`, such that each `{T_σ v}_σ` has a greatest and a least element. -/
structure ADP (V P : Type*) [PartialOrder V] where
  T : P → V → V
  exists_greedy : ∀ v, ∃ σ, ∀ τ, T τ v ≤ T σ v
  exists_minGreedy : ∀ v, ∃ σ, ∀ τ, T σ v ≤ T τ v

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- `σ` is `v`-greedy (p. 295): `T_τ v ≼ T_σ v` for all `τ`. -/
def IsGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T τ v ≤ A.T σ v

/-- A chosen `v`-greedy policy. -/
noncomputable def greedy (v : V) : P := (A.exists_greedy v).choose

theorem isGreedy_greedy (v : V) : A.IsGreedy v (A.greedy v) := (A.exists_greedy v).choose_spec

/-- The Bellman operator (9.5): `Tv = ⋁_σ T_σ v`, attained at any `v`-greedy policy. -/
noncomputable def bellman (v : V) : V := A.T (A.greedy v) v

theorem T_le_bellman (σ : P) (v : V) : A.T σ v ≤ A.bellman v := A.isGreedy_greedy v σ

/-- `Tv` is the greatest element of `{T_σ v}_σ`. -/
theorem isGreatest_bellman (v : V) : IsGreatest (range fun σ => A.T σ v) (A.bellman v) :=
  ⟨⟨_, rfl⟩, by rintro _ ⟨τ, rfl⟩; exact A.T_le_bellman τ v⟩

/-- **Exercise 9.2.1 (i)** (p. 298): `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff (v : V) (σ : P) : A.IsGreedy v σ ↔ A.T σ v = A.bellman v :=
  ⟨fun h => le_antisymm (A.T_le_bellman σ v) (h _), fun h τ => h ▸ A.T_le_bellman τ v⟩

/-- **Exercise 9.2.1 (ii)** (p. 298): if every `T_σ` is order preserving, so is `T`. -/
theorem monotone_bellman (h : ∀ σ, Monotone (A.T σ)) : Monotone A.bellman :=
  fun _ w hvw => (h _ hvw).trans (A.T_le_bellman _ w)

/-- `A` is well-posed (p. 297): every `T_σ` has a unique fixed point. -/
def WellPosed : Prop := ∀ σ, ∃! v, IsFixedPt (A.T σ) v

/-- The `σ`-value function `v_σ` of a well-posed ADP. -/
noncomputable def vσ (hw : A.WellPosed) (σ : P) : V := (hw σ).exists.choose

variable {A}

theorem isFixedPt_vσ (hw : A.WellPosed) (σ : P) : IsFixedPt (A.T σ) (A.vσ hw σ) :=
  (hw σ).exists.choose_spec

theorem eq_vσ_of_isFixedPt (hw : A.WellPosed) {σ : P} {v : V} (h : IsFixedPt (A.T σ) v) :
    v = A.vσ hw σ :=
  (hw σ).unique h (isFixedPt_vσ hw σ)

variable (A)

/-- `V_u = {v ∈ V : v ≼ Tv}` (p. 299). -/
def Vu : Set V := {v | v ≤ A.bellman v}

/-- **Exercise 9.2.3** (p. 300): `V_Σ ⊆ V_u`. -/
theorem vσ_mem_Vu (hw : A.WellPosed) (σ : P) : A.vσ hw σ ∈ A.Vu :=
  (isFixedPt_vσ hw σ).eq.symm.le.trans (A.T_le_bellman σ _)

/-- The Howard operator: `Hv = v_σ` for the chosen `v`-greedy `σ` (p. 298). -/
noncomputable def howard (hw : A.WellPosed) (v : V) : V := A.vσ hw (A.greedy v)

/-- The HPI policies of Algorithm 8.1 for an ADP: `σ₀` given, `σₖ₊₁` is `v_{σₖ}`-greedy. -/
noncomputable def hpiPolicy (hw : A.WellPosed) (σ₀ : P) : ℕ → P
  | 0 => σ₀
  | k + 1 => A.greedy (A.vσ hw (hpiPolicy hw σ₀ k))

/-- The HPI values `vₖ = v_{σₖ}`, so that `vₖ₊₁ = H vₖ`. -/
noncomputable def hpiValue (hw : A.WellPosed) (σ₀ : P) (k : ℕ) : V :=
  A.vσ hw (A.hpiPolicy hw σ₀ k)

theorem hpiValue_succ (hw : A.WellPosed) (σ₀ : P) (k : ℕ) :
    A.hpiValue hw σ₀ (k + 1) = A.howard hw (A.hpiValue hw σ₀ k) := rfl

/-- `A` is order stable (p. 298): every policy operator is order stable. -/
def IsOrderStable : Prop := ∀ σ, OrderStable (A.T σ)

/-- `A` is max-stable (p. 298): order stable, and `T` has a fixed point. -/
def IsMaxStable : Prop := A.IsOrderStable ∧ ∃ v, IsFixedPt A.bellman v

variable {A}

/-- Order stable ADPs are well-posed. -/
theorem IsOrderStable.wellPosed (h : A.IsOrderStable) : A.WellPosed := fun σ => by
  obtain ⟨u, hu, huniq, -, -⟩ := h σ
  exact ⟨u, hu, huniq⟩

/-- Upward stability of `T_σ` around `v_σ`. -/
theorem IsOrderStable.le_vσ (h : A.IsOrderStable) {σ : P} {v : V} (hv : v ≤ A.T σ v) :
    v ≤ A.vσ h.wellPosed σ := by
  obtain ⟨u, hu, huniq, hup, -⟩ := h σ
  rw [huniq _ (isFixedPt_vσ h.wellPosed σ)]
  exact hup v hv

/-- Downward stability of `T_σ` around `v_σ`. -/
theorem IsOrderStable.vσ_le (h : A.IsOrderStable) {σ : P} {v : V} (hv : A.T σ v ≤ v) :
    A.vσ h.wellPosed σ ≤ v := by
  obtain ⟨u, hu, huniq, -, hdown⟩ := h σ
  rw [huniq _ (isFixedPt_vσ h.wellPosed σ)]
  exact hdown v hv

variable (A)

/-- `σ` is optimal: `v_σ` is the greatest element of `V_Σ = {v_τ}` (p. 300). -/
def IsOptimal (hw : A.WellPosed) (σ : P) : Prop := ∀ τ, A.vσ hw τ ≤ A.vσ hw σ

variable {A}

/-- **Lemma B.4.1 (i)** (p. 350): `v ∈ V_u ⇒ v ≼ Hv`. -/
theorem IsOrderStable.le_howard (h : A.IsOrderStable) {v : V} (hv : v ∈ A.Vu) :
    v ≤ A.howard h.wellPosed v :=
  h.le_vσ (hv.trans (A.isGreedy_greedy v (A.greedy v)) |>.trans_eq rfl)

/-- **Lemma B.4.1 (ii)** (p. 350): if `T v_σ = v_σ` then `v_σ` dominates every `v_τ`. -/
theorem IsOrderStable.isOptimal_of_isFixedPt (h : A.IsOrderStable) {σ : P}
    (hσ : IsFixedPt A.bellman (A.vσ h.wellPosed σ)) : A.IsOptimal h.wellPosed σ :=
  fun τ => h.vσ_le ((A.T_le_bellman τ _).trans_eq hσ.eq)

/-- If `Hv = v` then `v` is the value of the greedy policy and a fixed point of `T`. -/
theorem IsOrderStable.isFixedPt_of_howard (h : A.IsOrderStable) {v : V}
    (hv : A.howard h.wellPosed v = v) : IsFixedPt A.bellman v := by
  have h1 : A.vσ h.wellPosed (A.greedy v) = v := hv
  have h2 := (isFixedPt_vσ h.wellPosed (A.greedy v)).eq
  rw [h1] at h2
  exact h2

/-- **Lemma B.4.1 (iii)** (p. 350): if `Hv = v` then `v = v*` (`v` is the value of an optimal
policy) and `Tv = v`. -/
theorem IsOrderStable.howard_fixed (h : A.IsOrderStable) {v : V}
    (hv : A.howard h.wellPosed v = v) :
    A.IsOptimal h.wellPosed (A.greedy v) ∧ A.vσ h.wellPosed (A.greedy v) = v ∧
      IsFixedPt A.bellman v := by
  have hfix := h.isFixedPt_of_howard hv
  have h1 : A.vσ h.wellPosed (A.greedy v) = v := hv
  refine ⟨h.isOptimal_of_isFixedPt ?_, h1, hfix⟩
  rw [h1]
  exact hfix

/-- The HPI values increase. -/
theorem IsOrderStable.hpiValue_le_succ (h : A.IsOrderStable) (σ₀ : P) (k : ℕ) :
    A.hpiValue h.wellPosed σ₀ k ≤ A.hpiValue h.wellPosed σ₀ (k + 1) :=
  h.le_howard (A.vσ_mem_Vu h.wellPosed _)

/-- **Lemma B.4.1 (iv)** (p. 350), termination: for finite `Σ`, HPI repeats a value after finitely
many steps. -/
theorem IsOrderStable.exists_hpiValue_succ_eq [Finite P] (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k := by
  by_contra hcon
  have hsm : StrictMono (A.hpiValue h.wellPosed σ₀) :=
    strictMono_nat_of_lt_succ fun k => lt_of_le_of_ne (h.hpiValue_le_succ σ₀ k)
      fun he => hcon ⟨k, he.symm⟩
  have hinj : Injective (A.hpiPolicy h.wellPosed σ₀) := fun i j hij =>
    hsm.injective (by simp only [hpiValue, hij])
  exact not_injective_infinite_finite _ hinj

/-- **Lemma B.4.1 (iv)–(v)** (p. 350): for finite `Σ`, HPI from any `σ₀` reaches a `k` with
`vₖ₊₁ = vₖ`; there `vₖ` is a fixed point of `T` and the returned `vₖ`-greedy policy `σₖ₊₁` is
optimal. -/
theorem IsOrderStable.hpi_terminates [Finite P] (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k ∧
      IsFixedPt A.bellman (A.hpiValue h.wellPosed σ₀ k) ∧
      A.IsOptimal h.wellPosed (A.hpiPolicy h.wellPosed σ₀ (k + 1)) := by
  obtain ⟨k, hk⟩ := h.exists_hpiValue_succ_eq σ₀
  obtain ⟨hopt, -, hfix⟩ := h.howard_fixed hk
  exact ⟨k, hk, hfix, hopt⟩

/-- **Proposition 9.2.1** (p. 299): a finite order stable ADP is max-stable. -/
theorem IsOrderStable.isMaxStable [Finite P] [Nonempty P] (h : A.IsOrderStable) :
    A.IsMaxStable := by
  obtain ⟨σ₀⟩ := ‹Nonempty P›
  obtain ⟨k, -, hfix, -⟩ := h.hpi_terminates σ₀
  exact ⟨h, _, hfix⟩

/-- **Proposition 9.2.5** (p. 300): for a max-stable ADP, (i) `V_Σ` has a greatest element `v*`,
(ii) `v*` is the unique fixed point of `T`, (iii) `σ` is optimal iff it is `v*`-greedy and
(iv) an optimal policy exists. -/
theorem IsMaxStable.optimality (h : A.IsMaxStable) :
    ∃ vstar, IsGreatest (range (A.vσ h.1.wellPosed)) vstar ∧
      (∀ v, IsFixedPt A.bellman v ↔ v = vstar) ∧
      (∀ σ, A.IsOptimal h.1.wellPosed σ ↔ A.IsGreedy vstar σ) ∧
      ∃ σ, A.IsOptimal h.1.wellPosed σ := by
  obtain ⟨hs, vbar, hvbar⟩ := h
  have hw := hs.wellPosed
  -- any fixed point `w` of `T` is the value of its greedy policy and dominates every `v_τ`
  have key : ∀ w, IsFixedPt A.bellman w →
      w = A.vσ hw (A.greedy w) ∧ IsGreatest (range (A.vσ hw)) w := by
    intro w hw'
    have e : w = A.vσ hw (A.greedy w) := eq_vσ_of_isFixedPt hw hw'.eq
    refine ⟨e, ⟨⟨_, e.symm⟩, ?_⟩⟩
    rintro _ ⟨τ, rfl⟩
    exact hs.vσ_le ((A.T_le_bellman τ w).trans_eq hw'.eq)
  obtain ⟨e, hgr⟩ := key vbar hvbar
  refine ⟨vbar, hgr, fun v => ⟨fun hv => (key v hv).2.unique hgr, fun hv => hv ▸ hvbar⟩,
    fun σ => ?_, A.greedy vbar, fun τ => e ▸ hgr.2 ⟨τ, rfl⟩⟩
  have hopt : A.IsOptimal hw σ ↔ A.vσ hw σ = vbar :=
    ⟨fun ho => le_antisymm (hgr.2 ⟨σ, rfl⟩) (e ▸ ho _), fun he τ => he ▸ hgr.2 ⟨τ, rfl⟩⟩
  rw [hopt, A.isGreedy_iff, hvbar.eq]
  constructor
  · intro he
    rw [← he]
    exact (isFixedPt_vσ hw σ).eq
  · intro he
    exact (eq_vσ_of_isFixedPt hw he).symm

/-- **Theorem 9.2.4 (max-optimality)** (p. 300): if `A` is finite and order stable, then (i) `V_Σ`
has a greatest element `v*`, (ii) `v*` is the unique solution of the Bellman equation, (iii) `A`
obeys Bellman's principle of optimality, (iv) an optimal policy exists and (v) HPI returns an
optimal policy in finitely many steps. -/
theorem IsOrderStable.maxOptimality [Finite P] [Nonempty P] (h : A.IsOrderStable) :
    ∃ vstar, IsGreatest (range (A.vσ h.wellPosed)) vstar ∧
      (∀ v, IsFixedPt A.bellman v ↔ v = vstar) ∧
      (∀ σ, A.IsOptimal h.wellPosed σ ↔ A.IsGreedy vstar σ) ∧
      (∃ σ, A.IsOptimal h.wellPosed σ) ∧
      ∀ σ₀, ∃ k, A.hpiValue h.wellPosed σ₀ (k + 1) = A.hpiValue h.wellPosed σ₀ k ∧
        A.IsOptimal h.wellPosed (A.hpiPolicy h.wellPosed σ₀ (k + 1)) := by
  obtain ⟨vstar, h1, h2, h3, h4⟩ := h.isMaxStable.optimality
  exact ⟨vstar, h1, h2, h3, h4, fun σ₀ => by
    obtain ⟨k, hk, -, hopt⟩ := h.hpi_terminates σ₀
    exact ⟨k, hk, hopt⟩⟩

end ADP

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# ADPs generated by RDPs, MDPs and Q-factors

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Examples 9.1.1–9.1.4, 9.2.1,
Corollary 9.2.2, Exercise 9.2.2 and Proposition 9.2.3 (pp. 295–299).

* Example 9.1.1: an RDP `R` generates the ADP `A_R = (V, {T_σ})`, with greedy and anti-greedy
  policies giving the greatest and least elements of `{T_σ v}`.
* Corollary 9.2.2: if `R` is globally stable then `A_R` is max-stable (Lemma 9.1.1 and
  Proposition 9.2.1).
* Proposition 9.2.3: if `V` is an order interval, `A_R` is well-posed iff it is order stable
  (by Knaster–Tarski on `[v₁, v]` and `[v, v₂]`).
* Examples 9.1.2 and 9.2.1: the ADP of an MDP, with `v_σ = (I − βP_σ)⁻¹r_σ`.
* Example 9.1.3 and Exercise 9.2.2: the Q-factor ADP on `ℝ^{X × A}` is an ADP and is max-stable.
* Example 9.1.4: the risk-sensitive Q-factor operators form an ADP.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- **Example 9.1.1** (p. 295): the ADP `A_R = (V, {T_σ}_{σ ∈ Σ})` generated by an RDP. -/
noncomputable def toADP : ADP R.V R.Policy where
  T σ v := ⟨R.Tσ σ.1 v, R.Tσ_mapsTo σ.2 v.2⟩
  exists_greedy v := ⟨R.greedyPolicy v, fun τ =>
    (R.Tσ_le_T τ.2 v).trans_eq (R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)).symm⟩
  exists_minGreedy v := by
    obtain ⟨⟨σ, hσ⟩, hle⟩ := R.isLeast_Tσ v
    refine ⟨σ, fun τ => ?_⟩
    change R.Tσ σ.1 v ≤ R.Tσ τ.1 v
    have hσ' : R.Tσ σ.1 v = R.Tσ (R.antiGreedy v) v := hσ
    rw [hσ']
    exact hle ⟨τ, rfl⟩

theorem toADP_T (σ : R.Policy) (v : R.V) : (R.toADP.T σ v : X → ℝ) = R.Tσ σ.1 v := rfl

/-- The ADP of a well-posed RDP is well-posed. -/
theorem toADP_wellPosed {R : RDP X A} (hw : R.WellPosed) : R.toADP.WellPosed := fun σ => by
  refine ⟨⟨R.vσ σ.1, vσ_mem hw σ.2⟩, Subtype.ext (isFixedPt_vσ hw σ.2).eq, fun w hw' => ?_⟩
  exact Subtype.ext (eq_vσ_of_isFixedPt hw σ.2 w.2 (congrArg Subtype.val hw'.eq))

/-- The `σ`-value functions of `A_R` are those of `R`. -/
theorem toADP_vσ {R : RDP X A} (hw : R.WellPosed) (hw' : R.toADP.WellPosed) (σ : R.Policy) :
    (R.toADP.vσ hw' σ : X → ℝ) = R.vσ σ.1 :=
  eq_vσ_of_isFixedPt hw σ.2 (R.toADP.vσ hw' σ).2
    (congrArg Subtype.val (ADP.isFixedPt_vσ hw' σ).eq)

/-- The Bellman operator of `A_R` is the Bellman operator of `R` (p. 298). -/
theorem toADP_bellman (v : R.V) : (R.toADP.bellman v : X → ℝ) = R.T v := by
  have h1 := (R.toADP.isGreedy_iff v (R.greedyPolicy v)).1 fun τ =>
    (R.Tσ_le_T τ.2 v).trans_eq (R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)).symm
  rw [← h1]
  exact R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)

/-- Lemma 9.1.1 for RDPs: if `R` is globally stable, `A_R` is order stable. -/
theorem toADP_isOrderStable {R : RDP X A} (hR : R.IsGloballyStable) : R.toADP.IsOrderStable :=
  fun σ => orderStable_restrict (R.Tσ_mapsTo σ.2) (R.Tσ_monotoneOn σ.2) (hR σ.1 σ.2)

/-- **Corollary 9.2.2** (p. 299): if `R` is globally stable, `A_R` is max-stable. -/
theorem toADP_isMaxStable {R : RDP X A} (hR : R.IsGloballyStable) : R.toADP.IsMaxStable :=
  have := R.policy_nonempty
  (toADP_isOrderStable hR).isMaxStable

/-- **Proposition 9.2.3** (p. 299): if `V = [v₁, v₂]` then `A_R` is well-posed iff it is order
stable. -/
theorem toADP_wellPosed_iff {R : RDP X A} {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂)
    (hV : R.V = Icc v₁ v₂) : R.toADP.WellPosed ↔ R.toADP.IsOrderStable := by
  refine ⟨fun hw σ => ?_, fun h => h.wellPosed⟩
  have hu := ADP.isFixedPt_vσ hw σ
  have huniq : ∀ w : R.V, IsFixedPt (R.toADP.T σ) w → w = R.toADP.vσ hw σ := fun w hw' =>
    ADP.eq_vσ_of_isFixedPt hw hw'
  have hmono : MonotoneOn (R.Tσ σ.1) R.V := R.Tσ_monotoneOn σ.2
  have hmaps : MapsTo (R.Tσ σ.1) R.V R.V := R.Tσ_mapsTo σ.2
  have hsub : ∀ {a b : X → ℝ}, v₁ ≤ a → b ≤ v₂ → Icc a b ⊆ R.V := fun ha hb z hz => by
    rw [hV]
    exact ⟨ha.trans hz.1, hz.2.trans hb⟩
  have hv1 : v₁ ∈ R.V := by rw [hV]; exact ⟨le_rfl, h12⟩
  have hv2 : v₂ ∈ R.V := by rw [hV]; exact ⟨h12, le_rfl⟩
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · -- `T_σ` maps `[v, v₂]` into itself
    have hv' : (v : X → ℝ) ≤ R.Tσ σ.1 v := hv
    have hvV : (v : X → ℝ) ∈ Icc v₁ v₂ := hV ▸ v.2
    have hm : MapsTo (R.Tσ σ.1) (Icc (v : X → ℝ) v₂) (Icc (v : X → ℝ) v₂) := fun z hz => by
      have hzV := hsub hvV.1 le_rfl hz
      have h2 : R.Tσ σ.1 z ∈ Icc v₁ v₂ := hV ▸ hmaps hzV
      exact ⟨hv'.trans (hmono v.2 hzV hz.1), h2.2⟩
    obtain ⟨a, ha, -, -, hafix, -⟩ :=
      knaster_tarski hvV.2 hm (hmono.mono (hsub hvV.1 le_rfl))
    have haV : a ∈ R.V := hsub hvV.1 le_rfl ha
    have := huniq ⟨a, haV⟩ (Subtype.ext hafix.eq)
    rw [← this]
    exact ha.1
  · have hv' : R.Tσ σ.1 v ≤ (v : X → ℝ) := hv
    have hvV : (v : X → ℝ) ∈ Icc v₁ v₂ := hV ▸ v.2
    have hm : MapsTo (R.Tσ σ.1) (Icc v₁ (v : X → ℝ)) (Icc v₁ (v : X → ℝ)) := fun z hz => by
      have hzV := hsub le_rfl hvV.2 hz
      have h2 : R.Tσ σ.1 z ∈ Icc v₁ v₂ := hV ▸ hmaps hzV
      exact ⟨h2.1, (hmono hzV v.2 hz.2).trans hv'⟩
    obtain ⟨a, ha, -, -, hafix, -⟩ :=
      knaster_tarski hvV.1 hm (hmono.mono (hsub le_rfl hvV.2))
    have haV : a ∈ R.V := hsub le_rfl hvV.2 ha
    have := huniq ⟨a, haV⟩ (Subtype.ext hafix.eq)
    rw [← this]
    exact ha.2

end RDP

/-! ### MDPs (Examples 9.1.2 and 9.2.1) -/

/-- A Markov decision process `M = (Γ, β, r, P)` (§5.1.1, restated). -/
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

/-- The closed-loop matrix `P_σ(x, x') = P(x, σ(x), x')`. -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

/-- `P_σ` is Markov. -/
theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The reward `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The RDP of an MDP (Example 8.1.1, restated): `V = ℝ^X`,
`B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`. -/
def toRDP : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := univ
  B := fun x a v => M.r x a + M.β * ∑ x', v x' * M.P x a x'
  mono := fun x a _ _ _ _ _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hvw x') (M.P_nonneg x a x')) M.β_pos.le)
  consistent := fun _ _ _ _ => mem_univ _

/-- The policy operators are `T_σ v = r_σ + βP_σ v` (5.19). -/
theorem toRDP_Tσ (σ : X → A) (v : X → ℝ) :
    M.toRDP.Tσ σ v = affineOp (M.β • M.Pσ σ) (M.rσ σ) v := by
  funext x
  simp only [RDP.Tσ, toRDP, affineOp, Pi.add_apply, mulVec, dotProduct, Matrix.smul_apply,
    smul_eq_mul, Pσ, Matrix.of_apply, rσ, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- **Example 9.1.2** (p. 295): the ADP `A_M` generated by an MDP. -/
noncomputable def toADP : ADP M.toRDP.V M.toRDP.Policy := M.toRDP.toADP

/-- Each `T_σ` of an MDP is globally stable on `ℝ^X`. -/
theorem toRDP_isGloballyStable [Nonempty X] : M.toRDP.IsGloballyStable := by
  classical
  intro σ _
  have hρ : specRad (M.β • M.Pσ σ) < 1 := by
    rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ) M.β_pos.le]
    exact M.β_lt_one
  have hT : M.toRDP.Tσ σ = affineOp (M.β • M.Pσ σ) (M.rσ σ) := funext (M.toRDP_Tσ σ)
  change GloballyStableOn (M.toRDP.Tσ σ) univ
  rw [hT, globallyStableOn_univ_iff]
  exact globallyStable_affineOp hρ _

/-- **Example 9.2.1** (p. 297): the `σ`-value functions of `A_M` are `v_σ = (I − βP_σ)⁻¹r_σ`. -/
theorem toADP_vσ [DecidableEq X] [Nonempty X] (hw : M.toADP.WellPosed) (σ : M.toRDP.Policy) :
    (M.toADP.vσ hw σ : X → ℝ) = (1 - M.β • M.Pσ σ.1)⁻¹ *ᵥ M.rσ σ.1 := by
  have hρ : specRad (M.β • M.Pσ σ.1) < 1 := by
    rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ.1) M.β_pos.le]
    exact M.β_lt_one
  have hfix := isFixedPt_affineOp_inv hρ (M.rσ σ.1)
  have h := ADP.eq_vσ_of_isFixedPt hw (σ := σ)
    (v := ⟨(1 - M.β • M.Pσ σ.1)⁻¹ *ᵥ M.rσ σ.1, mem_univ _⟩) (Subtype.ext (by
      change M.toRDP.Tσ σ.1 _ = _
      rw [M.toRDP_Tσ]
      exact hfix))
  rw [← h]

end MDP

/-! ### Q-factors (Examples 9.1.3–9.1.4, Exercise 9.2.2) -/

/-- The entropic aggregate `θ⁻¹ ln ∑ exp(θ g(x'))p(x')` is increasing in `g` for a distribution
`p` and `θ ≠ 0`. -/
theorem entropic_mono {X : Type*} [Fintype X] {p : X → ℝ} (hp0 : ∀ x', 0 ≤ p x')
    (hp1 : ∑ x', p x' = 1) {θ : ℝ} (hθ : θ ≠ 0) {g h : X → ℝ} (hgh : g ≤ h) :
    θ⁻¹ * Real.log (∑ x', Real.exp (θ * g x') * p x') ≤
      θ⁻¹ * Real.log (∑ x', Real.exp (θ * h x') * p x') := by
  have hpos : ∀ f : X → ℝ, 0 < ∑ x', Real.exp (θ * f x') * p x' := fun f => by
    obtain ⟨x, hx⟩ : ∃ x, 0 < p x := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ x', p x' ≤ 0 := sum_nonpos fun x' _ => hcon x'
      linarith
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hx) (single_le_sum
      (f := fun x' => Real.exp (θ * f x') * p x')
      (fun y _ => mul_nonneg (Real.exp_pos _).le (hp0 y)) (mem_univ x))
  rcases lt_or_gt_of_ne hθ with hneg | hpos'
  · have hs : ∑ x', Real.exp (θ * h x') * p x' ≤ ∑ x', Real.exp (θ * g x') * p x' :=
      sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (hgh x') hneg.le)) (hp0 x')
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hpos h) hs) (inv_nonpos.2 hneg.le)
  · have hs : ∑ x', Real.exp (θ * g x') * p x' ≤ ∑ x', Real.exp (θ * h x') * p x' :=
      sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hgh x') hpos'.le)) (hp0 x')
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos g) hs) (inv_nonneg.2 hpos'.le)


namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The Q-factor policy operators (9.2): `(S_σ q)(x, a) = r(x, a) + β ∑ q(x', σ(x'))P(x, a, x')`,
on `ℝ^{X × A}` (the values off `G` are carried along and never used). -/
def qOp (σ : X → A) (q : X → A → ℝ) : X → A → ℝ :=
  fun x a => M.r x a + M.β * ∑ x', q x' (σ x') * M.P x a x'

/-- A policy maximising `q(x, ·)` over `Γ(x)`. -/
noncomputable def qGreedy (q : X → A → ℝ) : M.toRDP.Policy :=
  ⟨fun x => ((M.Γ x).exists_max_image (q x) (M.Γ_nonempty x)).choose,
    fun x => ((M.Γ x).exists_max_image (q x) (M.Γ_nonempty x)).choose_spec.1⟩

/-- A policy minimising `q(x, ·)` over `Γ(x)`. -/
noncomputable def qMinGreedy (q : X → A → ℝ) : M.toRDP.Policy :=
  ⟨fun x => ((M.Γ x).exists_min_image (q x) (M.Γ_nonempty x)).choose,
    fun x => ((M.Γ x).exists_min_image (q x) (M.Γ_nonempty x)).choose_spec.1⟩

theorem qOp_mono {σ τ : X → A} {q : X → A → ℝ} (h : ∀ x', q x' (τ x') ≤ q x' (σ x')) :
    M.qOp τ q ≤ M.qOp σ q := fun x a =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (h x') (M.P_nonneg x a x')) M.β_pos.le)

/-- **Example 9.1.3** (p. 296): the Q-factor operators `{S_σ}` form an ADP on `ℝ^{X × A}`. -/
noncomputable def qADP : ADP (X → A → ℝ) M.toRDP.Policy where
  T σ q := M.qOp σ.1 q
  exists_greedy q := ⟨M.qGreedy q, fun τ => M.qOp_mono fun x' =>
    ((M.Γ x').exists_max_image (q x') (M.Γ_nonempty x')).choose_spec.2 _ (τ.2 x')⟩
  exists_minGreedy q := ⟨M.qMinGreedy q, fun τ => M.qOp_mono fun x' =>
    ((M.Γ x').exists_min_image (q x') (M.Γ_nonempty x')).choose_spec.2 _ (τ.2 x')⟩

/-- Each Q-factor policy operator is a contraction of modulus `β` on `ℝ^{X × A}`. -/
theorem qOp_isContractionOn (σ : X → A) : IsContractionOn (M.qOp σ) univ M.β := by
  refine ⟨mapsTo_univ _ _, M.β_pos.le, M.β_lt_one, fun q _ q' _ => ?_⟩
  have hq : ∀ x', |q x' (σ x') - q' x' (σ x')| ≤ ‖q - q'‖ := fun x' => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm ((q - q') x') (σ x')).trans (norm_le_pi_norm (q - q') x')
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))).2 fun x => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))).2 fun a => ?_
  simp only [Pi.sub_apply, qOp, Real.norm_eq_abs, add_sub_add_left_eq_sub, ← mul_sub,
    ← sum_sub_distrib, ← sub_mul, abs_mul, abs_of_pos M.β_pos]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans ?_) M.β_pos.le
  calc ∑ x', |(q x' (σ x') - q' x' (σ x')) * M.P x a x'| ≤ ∑ x', ‖q - q'‖ * M.P x a x' :=
        sum_le_sum fun x' _ => by
          rw [abs_mul, abs_of_nonneg (M.P_nonneg x a x')]
          exact mul_le_mul_of_nonneg_right (hq x') (M.P_nonneg x a x')
    _ = ‖q - q'‖ := by rw [← Finset.mul_sum, M.P_rowsum, mul_one]

/-- **Exercise 9.2.2** (p. 299): the Q-factor ADP is max-stable. -/
theorem qADP_isMaxStable : M.qADP.IsMaxStable := by
  have := M.toRDP.policy_nonempty
  refine ADP.IsOrderStable.isMaxStable fun σ => ?_
  refine orderStable_of_globallyStable (fun q q' hqq' => M.qOp_mono (q := q) (τ := σ.1)
    (σ := σ.1) (fun _ => le_rfl) |>.trans ?_) (M.qOp_isContractionOn σ.1).globallyStable_univ
  intro x a
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (hqq' x' (σ.1 x')) (M.P_nonneg x a x')) M.β_pos.le)

/-- The risk-sensitive Q-factor policy operators (9.4):
`(Q_σ f)(x, a) = r(x, a) + (β/θ) ln ∑ exp[θf(x', σ(x'))]P(x, a, x')`. -/
noncomputable def rsqOp (θ : ℝ) (σ : X → A) (f : X → A → ℝ) : X → A → ℝ :=
  fun x a => M.r x a + M.β * (θ⁻¹ * Real.log (∑ x', Real.exp (θ * f x' (σ x')) * M.P x a x'))

theorem rsqOp_mono {θ : ℝ} (hθ : θ ≠ 0) {σ τ : X → A} {f : X → A → ℝ}
    (h : ∀ x', f x' (τ x') ≤ f x' (σ x')) : M.rsqOp θ τ f ≤ M.rsqOp θ σ f := fun x a =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (entropic_mono (M.P_nonneg x a)
    (M.P_rowsum x a) hθ (g := fun x' => f x' (τ x')) (h := fun x' => f x' (σ x')) h)
    M.β_pos.le)

/-- **Example 9.1.4** (p. 296): the risk-sensitive Q-factor operators form an ADP on
`ℝ^{X × A}`. -/
noncomputable def rsqADP {θ : ℝ} (hθ : θ ≠ 0) : ADP (X → A → ℝ) M.toRDP.Policy where
  T σ f := M.rsqOp θ σ.1 f
  exists_greedy f := ⟨M.qGreedy f, fun τ => M.rsqOp_mono hθ fun x' =>
    ((M.Γ x').exists_max_image (f x') (M.Γ_nonempty x')).choose_spec.2 _ (τ.2 x')⟩
  exists_minGreedy f := ⟨M.qMinGreedy f, fun τ => M.rsqOp_mono hθ fun x' =>
    ((M.Γ x').exists_min_image (f x') (M.Γ_nonempty x')).choose_spec.2 _ (τ.2 x')⟩

end MDP

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality results for RDPs via ADPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.2.2 (pp. 302–304): the proofs of
Theorems 8.1.1 and 8.1.2 through the ADP generated by an RDP.

* Translation: when `A_R` is order stable, Theorem 9.2.4 for `A_R` gives, for `R`, that `v*` is
  the unique solution of the Bellman equation in `V`, Bellman's principle of optimality, the
  existence of an optimal policy and finite termination of HPI.
* OPI: Lemma 9.2.6 (`Tᵏv → v*` from `v ∈ V_Σ`), Lemma 9.2.7 (`W_m` maps `V_u` into itself and
  `Tv ≼ W_m v ≼ Tᵐv`), Lemma 9.2.8 (`Tᵏv ≼ W_mᵏv`), Lemma 9.2.9 (if OPI repeats a value it has
  found `v*`) and Lemma 9.2.10 (along a sequence in `V_u` converging to `v*`, greedy policies are
  eventually optimal).
* **Theorem 8.1.1** for globally stable RDPs, (i)–(v).
* Bounded RDPs (Exercises 8.1.12–8.1.13, restated) and **Theorem 8.1.2**, through
  Proposition 9.2.3 on the reduced RDP `(Γ, [v₁, v₂], B)`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] {R : RDP X A}

/-- Upward stability of `T_σ` around `v_σ`, from order stability of `A_R`. -/
theorem le_vσ_of_le_Tσ (hw : R.WellPosed) (hs : R.toADP.IsOrderStable) {σ : X → A}
    (hσ : R.IsFeasible σ) {v : X → ℝ} (hv : v ∈ R.V) (h : v ≤ R.Tσ σ v) : v ≤ R.vσ σ := by
  have := hs.le_vσ (σ := ⟨σ, hσ⟩) (v := ⟨v, hv⟩) h
  have e := toADP_vσ hw hs.wellPosed ⟨σ, hσ⟩
  change v ≤ (R.toADP.vσ hs.wellPosed ⟨σ, hσ⟩ : X → ℝ) at this
  rwa [e] at this

/-- Downward stability of `T_σ` around `v_σ`, from order stability of `A_R`. -/
theorem vσ_le_of_Tσ_le (hw : R.WellPosed) (hs : R.toADP.IsOrderStable) {σ : X → A}
    (hσ : R.IsFeasible σ) {v : X → ℝ} (hv : v ∈ R.V) (h : R.Tσ σ v ≤ v) : R.vσ σ ≤ v := by
  have := hs.vσ_le (σ := ⟨σ, hσ⟩) (v := ⟨v, hv⟩) h
  have e := toADP_vσ hw hs.wellPosed ⟨σ, hσ⟩
  change (R.toADP.vσ hs.wellPosed ⟨σ, hσ⟩ : X → ℝ) ≤ v at this
  rwa [e] at this

variable [DecidableEq X] [DecidableEq A]

/-- Theorem 9.2.4 for `A_R`, translated to `R`: if `R` is well-posed and `A_R` is order stable,
then `v*` is the unique solution of the Bellman equation in `V`, Bellman's principle of optimality
holds, an optimal policy exists, and HPI (on `A_R`) returns an optimal policy in finitely many
steps. -/
theorem optimality_of_orderStable (hw : R.WellPosed) (hs : R.toADP.IsOrderStable) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      (∀ σ, R.IsFeasible σ → (R.IsOptimal σ ↔ R.IsGreedy R.vstar σ)) ∧
      (∃ σ, R.IsOptimal σ) ∧
      ∀ σ₀ : R.Policy, ∃ k, R.toADP.hpiValue hs.wellPosed σ₀ (k + 1) =
        R.toADP.hpiValue hs.wellPosed σ₀ k ∧
        R.IsOptimal (R.toADP.hpiPolicy hs.wellPosed σ₀ (k + 1)).1 := by
  have := R.policy_nonempty
  obtain ⟨w, hgr, hfixiff, hprin, ⟨σ0, hσ0⟩, hhpi⟩ := hs.maxOptimality
  have hv : ∀ σ : R.Policy, (R.toADP.vσ hs.wellPosed σ : X → ℝ) = R.vσ σ.1 :=
    toADP_vσ hw hs.wellPosed
  have hwv : (w : X → ℝ) = R.vstar := by
    obtain ⟨σw, hσw⟩ := hgr.1
    funext x
    refine le_antisymm ?_ (Finset.sup'_le _ _ fun τ _ => ?_)
    · rw [← hσw, hv]
      exact R.vσ_le_vstar σw.2 x
    · rw [← hv]
      exact hgr.2 ⟨τ, rfl⟩ x
  have hopt : ∀ σ : R.Policy, R.toADP.IsOptimal hs.wellPosed σ ↔ R.IsOptimal σ.1 := by
    intro σ
    constructor
    · intro h
      refine ⟨σ.2, le_antisymm (R.vσ_le_vstar σ.2) fun x => ?_⟩
      refine Finset.sup'_le _ _ fun τ _ => ?_
      rw [← hv, ← hv]
      exact h τ x
    · intro h τ x
      rw [hv, hv, h.2]
      exact R.vσ_le_vstar τ.2 x
  have hfix : IsFixedPt R.T R.vstar := by
    have h1 := ((hfixiff w).2 rfl).eq
    have h2 := congrArg Subtype.val h1
    rw [toADP_bellman] at h2
    rw [← hwv]
    exact h2
  refine ⟨⟨hwv ▸ w.2, hfix, fun v hvV hvfix => ?_⟩, fun σ hσ => ?_, ?_, fun σ₀ => ?_⟩
  · have h1 : IsFixedPt R.toADP.bellman ⟨v, hvV⟩ :=
      Subtype.ext ((toADP_bellman R ⟨v, hvV⟩).trans hvfix.eq)
    rw [← hwv]
    exact congrArg Subtype.val ((hfixiff _).1 h1)
  · rw [← hopt ⟨σ, hσ⟩, hprin, ADP.isGreedy_iff, R.isGreedy_iff_Tσ_eq_T _ hσ, ← hwv]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rwa [toADP_bellman] at this
    · intro h
      exact Subtype.ext (h.trans (toADP_bellman R w).symm)
  · exact ⟨σ0.1, (hopt σ0).1 hσ0⟩
  · obtain ⟨k, hk, hk'⟩ := hhpi σ₀
    exact ⟨k, hk, (hopt _).1 hk'⟩

/-! ### OPI (Lemmas 9.2.6–9.2.10) -/

/-- **Lemma 9.2.6** (p. 302): for globally stable `R` and `v ∈ V_Σ`, `Tᵏv → v*`. -/
theorem tendsto_iterate_T_vσ (hR : R.IsGloballyStable) {σ : X → A} (hσ : R.IsFeasible σ) :
    Tendsto (fun k : ℕ => R.T^[k] (R.vσ σ)) atTop (𝓝 R.vstar) := by
  have hw := hR.wellPosed
  obtain ⟨⟨hstar, hfix, -⟩, -, ⟨σs, hσs⟩, -⟩ :=
    optimality_of_orderStable hw (toADP_isOrderStable hR)
  have hv := vσ_mem hw hσ
  have hlow : ∀ k, (R.Tσ σs)^[k] (R.vσ σ) ≤ R.T^[k] (R.vσ σ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply']
      exact (R.Tσ_monotoneOn hσs.1 ((R.Tσ_mapsTo hσs.1).iterate k hv) (R.T_mapsTo.iterate k hv)
        ih).trans (R.Tσ_le_T hσs.1 _)
  have hup : ∀ k, R.T^[k] (R.vσ σ) ≤ R.vstar := fun k => by
    have := R.iterate_T_mono hv hstar (R.vσ_le_vstar hσ) k
    rwa [(hfix.iterate k).eq] at this
  have hlim := tendsto_iterate_Tσ hR hσs.1 hv
  rw [hσs.2] at hlim
  rw [tendsto_pi_nhds] at hlim ⊢
  intro x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim x) tendsto_const_nhds
    (fun k => hlow k x) (fun k => hup k x)

omit [DecidableEq X] [DecidableEq A] in
/-- `T_σᵐ v ≼ Tᵐ v` on `V` (Exercise 2.2.36). -/
theorem iterate_Tσ_le_iterate_T {σ : X → A} (hσ : R.IsFeasible σ) {v : X → ℝ} (hv : v ∈ R.V)
    (m : ℕ) : (R.Tσ σ)^[m] v ≤ R.T^[m] v := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (R.Tσ_le_T hσ _).trans (R.T_monotoneOn ((R.Tσ_mapsTo hσ).iterate m hv)
      (R.T_mapsTo.iterate m hv) ih)

omit [DecidableEq X] [DecidableEq A] in
/-- **Lemma 9.2.7** (p. 302): `W_m` maps `V_u = {v ∈ V : v ≼ Tv}` into itself, and
`Tv ≼ W_m v ≼ Tᵐv` for `v ∈ V_u` and `m ≥ 1`. -/
theorem opiW_spec {m : ℕ} (hm : 1 ≤ m) {v : X → ℝ} (hv : v ∈ R.V) (hvT : v ≤ R.T v) :
    R.opiW m v ∈ R.V ∧ R.opiW m v ≤ R.T (R.opiW m v) ∧ R.T v ≤ R.opiW m v ∧
      R.opiW m v ≤ R.T^[m] v := by
  set g := R.greedy v
  have hg := R.isGreedy_greedy v
  have hgv : v ≤ R.Tσ g v := by rw [R.Tσ_eq_T_of_isGreedy hg]; exact hvT
  have hmon : ∀ j, (R.Tσ g)^[j] v ≤ (R.Tσ g)^[j + 1] v := by
    intro j
    have := R.iterate_Tσ_mono hg.1 hv ((R.Tσ_mapsTo hg.1) hv) hgv j
    rwa [← iterate_succ_apply] at this
  have hge : ∀ j, R.Tσ g v ≤ (R.Tσ g)^[j + 1] v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => exact ih.trans (hmon (j + 1))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨(R.Tσ_mapsTo hg.1).iterate _ hv, ?_, ?_, iterate_Tσ_le_iterate_T hg.1 hv _⟩
  · calc R.opiW (m' + 1) v = (R.Tσ g)^[m' + 1] v := rfl
      _ ≤ (R.Tσ g)^[m' + 1 + 1] v := hmon (m' + 1)
      _ = R.Tσ g ((R.Tσ g)^[m' + 1] v) := iterate_succ_apply' _ _ _
      _ ≤ R.T ((R.Tσ g)^[m' + 1] v) := R.Tσ_le_T hg.1 _
  · rw [← R.Tσ_eq_T_of_isGreedy hg]
    exact hge m'

omit [DecidableEq X] [DecidableEq A] in
/-- **Lemma 9.2.8** (p. 303): for `v ∈ V_u`, `Tᵏv ≼ W_mᵏv`, and the OPI iterates stay in `V_u`. -/
theorem iterate_T_le_opi {m : ℕ} (hm : 1 ≤ m) {v : X → ℝ} (hv : v ∈ R.V) (hvT : v ≤ R.T v)
    (k : ℕ) : (R.opiW m)^[k] v ∈ R.V ∧ (R.opiW m)^[k] v ≤ R.T ((R.opiW m)^[k] v) ∧
      R.T^[k] v ≤ (R.opiW m)^[k] v := by
  induction k with
  | zero => exact ⟨hv, hvT, le_rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨g1, g2, g3, -⟩ := opiW_spec hm h1 h2
    rw [iterate_succ_apply', iterate_succ_apply']
    exact ⟨g1, g2, (R.T_monotoneOn (R.T_mapsTo.iterate k hv) h1 h3).trans g3⟩

/-- **Lemma 9.2.9** (p. 303): for globally stable `R`, `v₀ ∈ V_Σ` and `vₖ = W_mᵏv₀`, if
`vₖ = vₖ₊₁` then `vₖ = v*` and every `vₖ`-greedy policy is optimal. -/
theorem opi_stop (hR : R.IsGloballyStable) {m : ℕ} (hm : 1 ≤ m) {σ₀ : X → A}
    (hσ₀ : R.IsFeasible σ₀) {k : ℕ} (hk : R.opiValue m σ₀ (k + 1) = R.opiValue m σ₀ k) :
    R.opiValue m σ₀ k = R.vstar ∧ ∀ σ, R.IsGreedy (R.opiValue m σ₀ k) σ → R.IsOptimal σ := by
  have hw := hR.wellPosed
  obtain ⟨⟨-, -, huniq⟩, hprin, -, -⟩ := optimality_of_orderStable hw (toADP_isOrderStable hR)
  have hv0 := vσ_mem hw hσ₀
  have hv0T : R.vσ σ₀ ≤ R.T (R.vσ σ₀) :=
    (isFixedPt_vσ hw hσ₀).eq.symm.le.trans (R.Tσ_le_T hσ₀ _)
  obtain ⟨h1, h2, -⟩ := iterate_T_le_opi hm hv0 hv0T k
  set v := R.opiValue m σ₀ k
  obtain ⟨-, -, g3, g4⟩ := opiW_spec hm h1 h2
  have hW : R.opiW m v = v := by
    have : R.opiValue m σ₀ (k + 1) = R.opiW m v := iterate_succ_apply' _ _ _
    rw [← this, hk]
  -- `v ≼ Tv ≼ W_m v = v`
  have hfix : IsFixedPt R.T v := le_antisymm (g3.trans_eq hW) h2
  have hvstar := huniq v h1 hfix
  refine ⟨hvstar, fun σ hσ => ?_⟩
  rw [hvstar] at hσ
  exact (hprin σ hσ.1).2 hσ

/-- **Lemma 9.2.10** (p. 303): for globally stable `R`, if `(vₖ) ⊆ V_u` and `vₖ → v*`, then from
some `K` on every `vₖ`-greedy policy is optimal. -/
theorem eventually_optimal (hR : R.IsGloballyStable) {vs : ℕ → X → ℝ}
    (hvs : ∀ k, vs k ∈ R.V ∧ vs k ≤ R.T (vs k)) (hlim : Tendsto vs atTop (𝓝 R.vstar)) :
    ∃ K, ∀ k ≥ K, ∀ σ, R.IsGreedy (vs k) σ → R.IsOptimal σ := by
  have hw := hR.wellPosed
  have hs := toADP_isOrderStable hR
  have hgap : ∀ τ : R.Policy, ∀ᶠ k in atTop,
      ¬ R.IsOptimal τ.1 → ∃ x, R.vσ τ.1 x < vs k x := by
    intro τ
    by_cases hopt : R.IsOptimal τ.1
    · exact Eventually.of_forall fun _ h => absurd hopt h
    · have hlt : ∃ x, R.vσ τ.1 x < R.vstar x := by
        by_contra hcon
        exact hopt ⟨τ.2, le_antisymm (R.vσ_le_vstar τ.2) fun x => not_lt.1 fun h => hcon ⟨x, h⟩⟩
      obtain ⟨x, hx⟩ := hlt
      filter_upwards [(tendsto_pi_nhds.1 hlim x).eventually (lt_mem_nhds hx)] with k hk _
      exact ⟨x, hk⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_all.2 hgap)
  refine ⟨K, fun k hk σ hσ => ?_⟩
  by_contra hnot
  obtain ⟨x, hx⟩ := hK k hk ⟨σ, hσ.1⟩ hnot
  have hle : vs k ≤ R.vσ σ := le_vσ_of_le_Tσ hw hs hσ.1 (hvs k).1
    ((hvs k).2.trans_eq (R.Tσ_eq_T_of_isGreedy hσ).symm)
  exact absurd (hle x) (not_le.2 hx)

/-- **Theorem 8.1.1** (p. 257), proved as in §9.2.2.2: for a globally stable RDP, (i) `v*` is the
unique solution of the Bellman equation in `V`, (ii) Bellman's principle of optimality holds,
(iii) an optimal policy exists, (iv) HPI returns an optimal policy in finitely many steps, and
(v) for every `m ≥ 1` and `v₀ = v_σ` the OPI values converge to `v*` and the greedy policies `σₖ`
are optimal from some `K` on. -/
theorem optimality_of_globallyStable (hR : R.IsGloballyStable) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      (∀ σ, R.IsFeasible σ → (R.IsOptimal σ ↔ R.IsGreedy R.vstar σ)) ∧
      (∃ σ, R.IsOptimal σ) ∧
      (∀ σ₀ : R.Policy, ∃ k, R.toADP.hpiValue (toADP_isOrderStable hR).wellPosed σ₀ (k + 1) =
        R.toADP.hpiValue (toADP_isOrderStable hR).wellPosed σ₀ k ∧
        R.IsOptimal (R.toADP.hpiPolicy (toADP_isOrderStable hR).wellPosed σ₀ (k + 1)).1) ∧
      ∀ m, 1 ≤ m → ∀ σ, R.IsFeasible σ → Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) ∧
        ∃ K, ∀ k ≥ K, R.IsOptimal (R.greedy (R.opiValue m σ k)) := by
  have hw := hR.wellPosed
  obtain ⟨h1, h2, h3, h4⟩ := optimality_of_orderStable hw (toADP_isOrderStable hR)
  refine ⟨h1, h2, h3, h4, fun m hm σ hσ => ?_⟩
  obtain ⟨hstar, hfix, -⟩ := h1
  have hv0 := vσ_mem hw hσ
  have hv0T : R.vσ σ ≤ R.T (R.vσ σ) :=
    (isFixedPt_vσ hw hσ).eq.symm.le.trans (R.Tσ_le_T hσ _)
  have hspec := iterate_T_le_opi hm hv0 hv0T
  -- `W_m` preserves `≼ v*`
  have hWup : ∀ w ∈ R.V, w ≤ R.vstar → R.opiW m w ≤ R.vstar := fun w hwV hw' => by
    have hg := R.isGreedy_greedy w
    have hk : ∀ j, (R.Tσ (R.greedy w))^[j] w ≤ R.vstar := by
      intro j
      induction j with
      | zero => exact hw'
      | succ j ih =>
        rw [iterate_succ_apply']
        exact (R.Tσ_le_T hg.1 _).trans ((R.T_monotoneOn ((R.Tσ_mapsTo hg.1).iterate j hwV) hstar
          ih).trans hfix.eq.le)
    exact hk m
  have hup : ∀ k, R.opiValue m σ k ≤ R.vstar := by
    intro k
    induction k with
    | zero => exact R.vσ_le_vstar hσ
    | succ k ih =>
      change (R.opiW m)^[k + 1] (R.vσ σ) ≤ R.vstar
      rw [iterate_succ_apply']
      exact hWup _ (hspec k).1 ih
  have hconv : Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) := by
    have hlim := tendsto_iterate_T_vσ hR hσ
    rw [tendsto_pi_nhds] at hlim ⊢
    intro x
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim x) tendsto_const_nhds
      (fun k => (hspec k).2.2 x) (fun k => hup k x)
  obtain ⟨K, hK⟩ := eventually_optimal hR (fun k => ⟨(hspec k).1, (hspec k).2.1⟩) hconv
  exact ⟨hconv, K, fun k hk => hK k hk _ (R.isGreedy_greedy _)⟩

/-! ### Bounded RDPs and Theorem 8.1.2 -/

omit [DecidableEq X] [DecidableEq A] in
/-- `R` is bounded by `v₁ ≤ v₂` (§8.1.3.6, restated): `[v₁, v₂] ⊆ V` and (8.20). -/
def IsBoundedBy (R : RDP X A) (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ Icc v₁ v₂ ⊆ R.V ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x ≤ R.B x a v₁ ∧ R.B x a v₂ ≤ v₂ x

omit [DecidableEq X] [DecidableEq A] in
/-- Policy operators of a bounded RDP map `[v₁, v₂]` into itself. -/
theorem Tσ_mapsTo_Icc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) : MapsTo (R.Tσ σ) (Icc v₁ v₂) (Icc v₁ v₂) := by
  intro v hv
  have h1 : v₁ ∈ R.V := hb.2.1 ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ R.V := hb.2.1 ⟨hb.1, le_rfl⟩
  exact ⟨fun x => (hb.2.2 x _ (hσ x)).1.trans (R.mono x _ (hσ x) v₁ h1 v (hb.2.1 hv) hv.1),
    fun x => (R.mono x _ (hσ x) v (hb.2.1 hv) v₂ h2 hv.2).trans (hb.2.2 x _ (hσ x)).2⟩

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.12 (p. 259, restated): the reduced RDP `(Γ, [v₁, v₂], B)`. -/
def restrictIcc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) : RDP X A where
  Γ := R.Γ
  Γ_nonempty := R.Γ_nonempty
  V := Icc v₁ v₂
  B := R.B
  mono := fun x a ha v hv w hw hvw => R.mono x a ha v (hb.2.1 hv) w (hb.2.1 hw) hvw
  consistent := fun _ hσ _ hv => Tσ_mapsTo_Icc hb hσ hv

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.13 (p. 259, restated): in a well-posed bounded RDP, `v_σ ∈ [v₁, v₂]`. -/
theorem vσ_mem_Icc (hw : R.WellPosed) {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) : R.vσ σ ∈ Icc v₁ v₂ := by
  have hmono : MonotoneOn (R.Tσ σ) (Icc v₁ v₂) := (R.Tσ_monotoneOn hσ).mono hb.2.1
  obtain ⟨z, hz, -, -, hzfix, -⟩ := knaster_tarski hb.1 (Tσ_mapsTo_Icc hb hσ) hmono
  rw [← eq_vσ_of_isFixedPt hw hσ (hb.2.1 hz) hzfix]
  exact hz

omit [DecidableEq X] [DecidableEq A] in
/-- The reduced RDP is well-posed, with the same `σ`-value functions. -/
theorem restrictIcc_wellPosed (hw : R.WellPosed) {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) :
    (R.restrictIcc hb).WellPosed ∧ ∀ σ, R.IsFeasible σ → (R.restrictIcc hb).vσ σ = R.vσ σ := by
  have hw' : (R.restrictIcc hb).WellPosed := fun σ hσ =>
    ⟨R.vσ σ, ⟨vσ_mem_Icc hw hb hσ, isFixedPt_vσ hw hσ⟩, fun w ⟨hwI, hwfix⟩ =>
      eq_vσ_of_isFixedPt hw hσ (hb.2.1 hwI) hwfix⟩
  exact ⟨hw', fun σ hσ => (eq_vσ_of_isFixedPt hw' hσ (vσ_mem_Icc hw hb hσ)
    (isFixedPt_vσ hw hσ)).symm⟩

/-- **Theorem 8.1.2** (p. 260), proved as in §9.2.2.2: for a well-posed RDP bounded by `v₁ ≤ v₂`,
(i) `v*` is the unique solution of the Bellman equation in `V`, (ii) Bellman's principle of
optimality holds, (iii) an optimal policy exists, and (iv) HPI on the reduced RDP returns an
optimal policy in finitely many steps. -/
theorem optimality_of_bounded (hw : R.WellPosed) {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      (∀ σ, R.IsFeasible σ → (R.IsOptimal σ ↔ R.IsGreedy R.vstar σ)) ∧
      (∃ σ, R.IsOptimal σ) ∧
      ∃ hs : (R.restrictIcc hb).toADP.IsOrderStable, ∀ σ₀ : (R.restrictIcc hb).Policy,
        ∃ k, (R.restrictIcc hb).toADP.hpiValue hs.wellPosed σ₀ (k + 1) =
          (R.restrictIcc hb).toADP.hpiValue hs.wellPosed σ₀ k ∧
          R.IsOptimal ((R.restrictIcc hb).toADP.hpiPolicy hs.wellPosed σ₀ (k + 1)).1 := by
  set Rb := R.restrictIcc hb
  obtain ⟨hwb, hvb⟩ := restrictIcc_wellPosed hw hb
  have hsb : Rb.toADP.IsOrderStable := (toADP_wellPosed_iff hb.1 rfl).1 (toADP_wellPosed hwb)
  obtain ⟨⟨hmem, hfix, huniq⟩, hprin, ⟨σs, hσs⟩, hhpi⟩ := optimality_of_orderStable hwb hsb
  have hvstar : Rb.vstar = R.vstar := by
    funext x
    refine le_antisymm (Finset.sup'_le _ _ fun τ _ => ?_) (Finset.sup'_le _ _ fun τ _ => ?_)
    · rw [hvb τ.1 τ.2]
      exact R.vσ_le_vstar τ.2 x
    · rw [← hvb τ.1 τ.2]
      exact Rb.vσ_le_vstar τ.2 x
  have hopt : ∀ σ, R.IsFeasible σ → (Rb.IsOptimal σ ↔ R.IsOptimal σ) := fun σ hσ =>
    ⟨fun h => ⟨hσ, (hvb σ hσ).symm.trans (h.2.trans hvstar)⟩,
      fun h => ⟨h.1, (hvb σ hσ).trans (h.2.trans hvstar.symm)⟩⟩
  rw [hvstar] at hmem hfix huniq
  refine ⟨⟨hb.2.1 hmem, hfix, fun v hv hvfix => ?_⟩, fun σ hσ => ?_,
    ⟨σs, (hopt σs hσs.1).1 hσs⟩, hsb, fun σ₀ => ?_⟩
  · -- a fixed point of `T` in `V` is the value of its greedy policy, so it lies in `[v₁, v₂]`
    have hg := R.isGreedy_greedy v
    have hvg : v = R.vσ (R.greedy v) := eq_vσ_of_isFixedPt hw hg.1 hv (by
      change R.Tσ (R.greedy v) v = v
      rw [R.Tσ_eq_T_of_isGreedy hg, hvfix.eq])
    have hvI : v ∈ Icc v₁ v₂ := hvg ▸ vσ_mem_Icc hw hb hg.1
    exact huniq v hvI hvfix
  · rw [← hopt σ hσ, hprin σ hσ, hvstar]
    rfl
  · obtain ⟨k, hk, hk'⟩ := hhpi σ₀
    exact ⟨k, hk, (hopt _ (Rb.toADP.hpiPolicy hsb.wellPosed σ₀ (k + 1)).2).1 hk'⟩

end RDP

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Mixed strategies

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.2.1.6 (pp. 301–302).

A mixed strategy draws the action at `x` from a distribution `φ_x` on `Γ(x)`; its policy operator
is `(T̂_φ v)(x) = ∑_a B(x, a, v)φ_x(a)`. The set of mixed strategies is infinite, so
Proposition 9.2.5 (not Theorem 9.2.4) is the tool.

* Exercise 9.2.4: a mixed strategy supported on `argmax_a B(x, a, v)` is `v`-greedy among mixed
  strategies; Exercise 9.2.5: `max_φ (T̂_φ v)(x) = max_a B(x, a, v)`; the mixed strategies form
  an ADP `A_M` whose Bellman operator is `T` (9.6).
* Contracting RDPs (Proposition 8.2.1 and Corollary 8.2.2, restated) and Exercise 9.2.6: if `R`
  is contracting with modulus `β` and `V` is closed, every `T̂_φ` and `T̂ = T` are contractions.
* Conclusion: `A_M` is max-stable, and its value function equals `v*`: mixing does not raise
  the maximal lifetime value.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.AbstractDynamicProgramming

/-- A contraction of a closed nonempty set is globally stable on it (Banach). -/
theorem globallyStableOn_of_isContractionOn {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {S : E → E} {U : Set E} {L : ℝ} (hc : IsContractionOn S U L) (hU : IsClosed U)
    (hne : U.Nonempty) : GloballyStableOn S U := by
  obtain ⟨u, hu, hfix⟩ := hc.exists_fixedPt hU hne
  exact ⟨u, hu, hfix, fun v hv hv' => hc.fixedPt_unique hv hu hv' hfix,
    fun v hv => hc.tendsto_iterate_fixedPt hv hu hfix⟩

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-! ### Contracting RDPs (restated from §8.2.1) -/

/-- `R` is contracting with modulus `β ∈ [0, 1)` (8.26). -/
def IsContracting (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V, |R.B x a v - R.B x a w| ≤ β * ‖v - w‖

variable {R}

/-- Proposition 8.2.1: each `T_σ` is a contraction of modulus `β`. -/
theorem IsContracting.isContractionOn_Tσ {β : ℝ} (h : R.IsContracting β) {σ : X → A}
    (hσ : R.IsFeasible σ) : IsContractionOn (R.Tσ σ) R.V β :=
  ⟨R.Tσ_mapsTo hσ, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact h.2.2 x _ (hσ x) v hv w hw⟩

/-- Proposition 8.2.1: `T` is a contraction of modulus `β`. -/
theorem IsContracting.isContractionOn_T {β : ℝ} (h : R.IsContracting β) :
    IsContractionOn R.T R.V β :=
  ⟨R.T_mapsTo, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_sup'_sub_sup'_le (R.Γ_nonempty x) _ _).trans
      (Finset.sup'_le _ _ fun a ha => h.2.2 x a ha v hv w hw)⟩

/-- Corollary 8.2.2: a contracting RDP with `V` closed and nonempty is globally stable. -/
theorem IsContracting.isGloballyStable {β : ℝ} (h : R.IsContracting β) (hV : IsClosed R.V)
    (hne : R.V.Nonempty) : R.IsGloballyStable := fun _ hσ =>
  globallyStableOn_of_isContractionOn (h.isContractionOn_Tσ hσ) hV hne

variable (R)

/-! ### Mixed strategies -/

/-- `φ` is a mixed strategy: each `φ_x` is a distribution on `A` supported on `Γ(x)`. -/
def IsMixed (φ : X → A → ℝ) : Prop :=
  ∀ x, (∀ a, 0 ≤ φ x a) ∧ (∀ a, a ∉ R.Γ x → φ x a = 0) ∧ ∑ a, φ x a = 1

/-- The set `Φ` of mixed strategies. -/
abbrev Mixed := {φ : X → A → ℝ // R.IsMixed φ}

/-- The mixed-strategy policy operator `(T̂_φ v)(x) = ∑_a B(x, a, v)φ_x(a)`. -/
def Tmix (φ : X → A → ℝ) (v : X → ℝ) : X → ℝ := fun x => ∑ a, R.B x a v * φ x a

/-- The pure strategy `σ` as a mixed strategy (a point mass at `σ(x)`). -/
def dirac [DecidableEq A] (σ : X → A) : X → A → ℝ := fun x a => if a = σ x then 1 else 0

theorem isMixed_dirac [DecidableEq A] {σ : X → A} (hσ : R.IsFeasible σ) :
    R.IsMixed (dirac σ) := fun x => by
  refine ⟨fun a => by unfold dirac; split_ifs <;> norm_num, fun a ha => ?_, ?_⟩
  · unfold dirac
    split_ifs with h
    · exact absurd (h ▸ hσ x) ha
    · rfl
  · simp [dirac]

theorem Tmix_dirac [DecidableEq A] (σ : X → A) (v : X → ℝ) :
    R.Tmix (dirac σ) v = R.Tσ σ v := by
  funext x
  simp [Tmix, dirac, Tσ_apply]

/-- A mixed operator lies between the minimising and the maximising actions. -/
theorem Tmix_le_T {φ : X → A → ℝ} (hφ : R.IsMixed φ) (v : X → ℝ) : R.Tmix φ v ≤ R.T v := by
  intro x
  obtain ⟨h0, hsupp, h1⟩ := hφ x
  calc R.Tmix φ v x = ∑ a, R.B x a v * φ x a := rfl
    _ ≤ ∑ a, R.T v x * φ x a := sum_le_sum fun a _ => by
        by_cases ha : a ∈ R.Γ x
        · exact mul_le_mul_of_nonneg_right (R.B_le_T v ha) (h0 a)
        · rw [hsupp a ha, mul_zero, mul_zero]
    _ = R.T v x := by rw [← Finset.mul_sum, h1, mul_one]

theorem Tmin_le_Tmix {φ : X → A → ℝ} (hφ : R.IsMixed φ) (v : X → ℝ) :
    R.Tσ (R.antiGreedy v) v ≤ R.Tmix φ v := by
  intro x
  obtain ⟨h0, hsupp, h1⟩ := hφ x
  have hmin := ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec
  calc R.Tσ (R.antiGreedy v) v x = ∑ a, R.Tσ (R.antiGreedy v) v x * φ x a := by
        rw [← Finset.mul_sum, h1, mul_one]
    _ ≤ ∑ a, R.B x a v * φ x a := sum_le_sum fun a _ => by
        by_cases ha : a ∈ R.Γ x
        · exact mul_le_mul_of_nonneg_right (hmin.2 a ha) (h0 a)
        · rw [hsupp a ha, mul_zero, mul_zero]

/-- **Exercise 9.2.4** (p. 301): if every `φ_x` is supported on `argmax_{a ∈ Γ(x)} B(x, a, v)`,
then `T̂_φ v ≥ T̂_ψ v` for every mixed `ψ`. -/
theorem Tmix_le_Tmix_of_supported {φ ψ : X → A → ℝ} (hφ : R.IsMixed φ) (hψ : R.IsMixed ψ)
    (v : X → ℝ) (hsupp : ∀ x a, φ x a ≠ 0 → R.B x a v = R.T v x) :
    R.Tmix ψ v ≤ R.Tmix φ v := by
  have heq : R.Tmix φ v = R.T v := by
    funext x
    calc R.Tmix φ v x = ∑ a, R.T v x * φ x a := sum_congr rfl fun a _ => by
          by_cases h : φ x a = 0
          · rw [h, mul_zero, mul_zero]
          · rw [hsupp x a h]
      _ = R.T v x := by rw [← Finset.mul_sum, (hφ x).2.2, mul_one]
  rw [heq]
  exact R.Tmix_le_T hψ v

/-- **Exercise 9.2.5** (p. 301): `max_{φ ∈ Φ} (T̂_φ v)(x) = max_{a ∈ Γ(x)} B(x, a, v)`. -/
theorem isGreatest_Tmix (v : X → ℝ) (x : X) :
    IsGreatest (range fun φ : R.Mixed => R.Tmix φ.1 v x) (R.T v x) := by
  classical
  exact ⟨⟨⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩, by
      simp only
      rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]⟩,
    by rintro _ ⟨φ, rfl⟩; exact R.Tmix_le_T φ.2 v x⟩

/-- Mixed operators are order preserving on `V`. -/
theorem Tmix_monotoneOn {φ : X → A → ℝ} (hφ : R.IsMixed φ) : MonotoneOn (R.Tmix φ) R.V :=
  fun v hv w hw hvw x => sum_le_sum fun a _ => by
    by_cases ha : a ∈ R.Γ x
    · exact mul_le_mul_of_nonneg_right (R.mono x a ha v hv w hw hvw) ((hφ x).1 a)
    · rw [(hφ x).2.1 a ha, mul_zero, mul_zero]

/-- The ADP `A_M = (V, {T̂_φ}_{φ ∈ Φ})` of mixed strategies (p. 301), when each `T̂_φ` maps `V`
into itself. -/
noncomputable def mixedADP [DecidableEq A]
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) : ADP R.V R.Mixed where
  T φ v := ⟨R.Tmix φ.1 v, hmix φ.1 φ.2 v v.2⟩
  exists_greedy v := ⟨⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩, fun ψ => by
    change R.Tmix ψ.1 v ≤ R.Tmix (dirac (R.greedy v)) v
    rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
    exact R.Tmix_le_T ψ.2 v⟩
  exists_minGreedy v := ⟨⟨dirac (R.antiGreedy v), R.isMixed_dirac fun x =>
      ((R.Γ x).exists_min_image (fun a => R.B x a v) (R.Γ_nonempty x)).choose_spec.1⟩,
    fun ψ => by
      change R.Tmix (dirac (R.antiGreedy v)) v ≤ R.Tmix ψ.1 v
      rw [Tmix_dirac]
      exact R.Tmin_le_Tmix ψ.2 v⟩

/-- (9.6) (p. 301): the Bellman operator of `A_M` is the Bellman operator `T` of `R`. -/
theorem mixedADP_bellman [DecidableEq A]
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) (v : R.V) :
    ((R.mixedADP hmix).bellman v : X → ℝ) = R.T v := by
  have hg : (R.mixedADP hmix).IsGreedy v
      ⟨dirac (R.greedy v), R.isMixed_dirac (R.isGreedy_greedy v).1⟩ :=
    fun ψ => by
        change R.Tmix ψ.1 v ≤ R.Tmix (dirac (R.greedy v)) v
        rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]
        exact R.Tmix_le_T ψ.2 v
  rw [← ((R.mixedADP hmix).isGreedy_iff v _).1 hg]
  change R.Tmix (dirac (R.greedy v)) v = R.T v
  rw [Tmix_dirac, R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v)]

variable {R}

/-- **Exercise 9.2.6** (p. 301): if `R` is contracting with modulus `β`, each `T̂_φ` is a
contraction of modulus `β` on `V`. -/
theorem IsContracting.isContractionOn_Tmix {β : ℝ} (h : R.IsContracting β)
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) {φ : X → A → ℝ}
    (hφ : R.IsMixed φ) : IsContractionOn (R.Tmix φ) R.V β :=
  ⟨fun v hv => hmix φ hφ v hv, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    obtain ⟨h0, hsupp, h1⟩ := hφ x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    calc |R.Tmix φ v x - R.Tmix φ w x| = |∑ a, (R.B x a v - R.B x a w) * φ x a| := by
          simp only [Tmix, sub_mul, sum_sub_distrib]
      _ ≤ ∑ a, |(R.B x a v - R.B x a w) * φ x a| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, β * ‖v - w‖ * φ x a := sum_le_sum fun a _ => by
          rw [abs_mul, abs_of_nonneg (h0 a)]
          by_cases ha : a ∈ R.Γ x
          · exact mul_le_mul_of_nonneg_right (h.2.2 x a ha v hv w hw) (h0 a)
          · rw [hsupp a ha, mul_zero, mul_zero]
      _ = β * ‖v - w‖ := by rw [← Finset.mul_sum, h1, mul_one]⟩

/-- §9.2.1.6 (p. 302): for a contracting RDP with `V` closed and nonempty and mixed operators
mapping `V` into itself, the mixed-strategy ADP `A_M` is max-stable and its value function is
`v*`: mixing does not raise maximal lifetime value. -/
theorem mixed_value_eq_vstar [DecidableEq X] [DecidableEq A] {β : ℝ} (h : R.IsContracting β)
    (hV : IsClosed R.V) (hne : R.V.Nonempty)
    (hmix : ∀ φ, R.IsMixed φ → ∀ v ∈ R.V, R.Tmix φ v ∈ R.V) :
    ∃ hs : (R.mixedADP hmix).IsMaxStable, ∃ vhat,
      IsGreatest (range ((R.mixedADP hmix).vσ hs.1.wellPosed)) vhat ∧ (vhat : X → ℝ) = R.vstar := by
  have hos : (R.mixedADP hmix).IsOrderStable := fun φ =>
    orderStable_restrict (fun v hv => hmix φ.1 φ.2 v hv) (R.Tmix_monotoneOn φ.2)
      (globallyStableOn_of_isContractionOn (h.isContractionOn_Tmix hmix φ.2) hV hne)
  obtain ⟨u, hu, hufix⟩ := h.isContractionOn_T.exists_fixedPt hV hne
  have hbfix : IsFixedPt (R.mixedADP hmix).bellman ⟨u, hu⟩ :=
    Subtype.ext ((R.mixedADP_bellman hmix ⟨u, hu⟩).trans hufix.eq)
  have hs : (R.mixedADP hmix).IsMaxStable := ⟨hos, _, hbfix⟩
  obtain ⟨vhat, hgr, hfixiff, -, -⟩ := hs.optimality
  refine ⟨hs, vhat, hgr, ?_⟩
  have hvfix : IsFixedPt R.T vhat := by
    have := congrArg Subtype.val ((hfixiff vhat).2 rfl).eq
    rwa [mixedADP_bellman] at this
  exact (optimality_of_globallyStable (h.isGloballyStable hV hne)).1.2.2 _ vhat.2 hvfix

end RDP

end SargentStachurski.AbstractDynamicProgramming

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Min-optimality by order duality

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.2.3 (pp. 305–306).

The dual of an ADP `A = (V, {T_σ})` is `A^∂ = (V^∂, {T_σ})`, the same operators on the order dual.
Min-greedy policies, the Bellman min-operator, min-stability, min-optimal policies and min-HPI for
`A` are the max-greedy policies, Bellman operator, max-stability, optimal policies and HPI of
`A^∂`.

* Exercise 9.2.7 (i)–(vi), with `A^{∂∂} = A`.
* **Theorem 9.2.11 (min-optimality)**: for min-stable `A`, the min-value function exists, is the
  unique solution of the Bellman min-equation, Bellman's principle of min-optimality holds, a
  min-optimal policy exists, and for finite `Σ` min-HPI terminates at a min-optimal policy.
* For a globally stable RDP `R`, `A_R` is min-stable (the ADP form of Theorem 8.3.7).
-/

open Function Set

namespace SargentStachurski.AbstractDynamicProgramming

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- The dual ADP `A^∂ = (V^∂, {T_σ})` (p. 305). -/
def dual : ADP Vᵒᵈ P where
  T σ v := OrderDual.toDual (A.T σ (OrderDual.ofDual v))
  exists_greedy v := A.exists_minGreedy (OrderDual.ofDual v)
  exists_minGreedy v := A.exists_greedy (OrderDual.ofDual v)

/-- `A^{∂∂} = A`. -/
theorem dual_dual : A.dual.dual = A := rfl

/-- `σ` is `v`-min-greedy: `T_σ v ≼ T_τ v` for all `τ` (p. 305). -/
def IsMinGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T σ v ≤ A.T τ v

/-- The Bellman min-operator `Tv = ⋀_σ T_σ v` (p. 305). -/
noncomputable def minBellman (v : V) : V := OrderDual.ofDual (A.dual.bellman (OrderDual.toDual v))

/-- `σ` is min-optimal: `v_σ` is the least element of `V_Σ`. -/
def IsMinOptimal (hw : A.WellPosed) (σ : P) : Prop := ∀ τ, A.vσ hw σ ≤ A.vσ hw τ

/-- `A` is min-stable (p. 305): order stable, and the Bellman min-operator has a fixed point. -/
def IsMinStable : Prop := A.IsOrderStable ∧ ∃ v, IsFixedPt A.minBellman v

/-- **Exercise 9.2.7 (i)** (p. 306): `σ` is `v`-min-greedy for `A` iff it is `v`-greedy for
`A^∂`. -/
theorem isMinGreedy_iff (v : V) (σ : P) :
    A.IsMinGreedy v σ ↔ A.dual.IsGreedy (OrderDual.toDual v) σ := Iff.rfl

/-- **Exercise 9.2.7 (ii)** (p. 306): the Bellman min-operator is the least element of
`{T_σ v}`, and `σ` is `v`-min-greedy iff `T_σ v = Tv`. -/
theorem isLeast_minBellman (v : V) : IsLeast (range fun σ => A.T σ v) (A.minBellman v) :=
  ⟨⟨A.dual.greedy (OrderDual.toDual v), rfl⟩, by
    rintro _ ⟨τ, rfl⟩
    exact A.dual.T_le_bellman τ (OrderDual.toDual v)⟩

theorem isMinGreedy_iff_eq (v : V) (σ : P) : A.IsMinGreedy v σ ↔ A.T σ v = A.minBellman v :=
  A.dual.isGreedy_iff (OrderDual.toDual v) σ

/-- **Exercise 9.2.7 (iv)** (p. 306): `A` is order stable iff `A^∂` is. -/
theorem isOrderStable_dual_iff : A.dual.IsOrderStable ↔ A.IsOrderStable :=
  forall_congr' fun σ => orderStable_dual_iff (A.T σ)

/-- Well-posedness transfers to the dual. -/
theorem WellPosed.dual {A : ADP V P} (hw : A.WellPosed) : A.dual.WellPosed := hw

/-- The `σ`-value functions of `A^∂` are those of `A`. -/
theorem dual_vσ {A : ADP V P} (hw : A.WellPosed) (σ : P) :
    OrderDual.ofDual (A.dual.vσ hw.dual σ) = A.vσ hw σ :=
  eq_vσ_of_isFixedPt hw (isFixedPt_vσ (A := A.dual) hw.dual σ)

/-- **Exercise 9.2.7 (v)** (p. 306): `A` is min-stable iff `A^∂` is max-stable. -/
theorem isMinStable_iff : A.IsMinStable ↔ A.dual.IsMaxStable := by
  rw [IsMinStable, IsMaxStable, isOrderStable_dual_iff]
  exact and_congr Iff.rfl ⟨fun ⟨v, hv⟩ => ⟨OrderDual.toDual v, congrArg OrderDual.toDual hv.eq⟩,
    fun ⟨v, hv⟩ => ⟨OrderDual.ofDual v, congrArg OrderDual.ofDual hv.eq⟩⟩

/-- **Exercise 9.2.7 (vi)** (p. 306): `σ` is min-optimal for `A` iff it is (max-)optimal for
`A^∂`. -/
theorem isMinOptimal_iff {A : ADP V P} (hw : A.WellPosed) (σ : P) :
    A.IsMinOptimal hw σ ↔ A.dual.IsOptimal hw.dual σ := by
  refine forall_congr' fun τ => ?_
  rw [← dual_vσ hw σ, ← dual_vσ hw τ]
  rfl

/-- **Theorem 9.2.11 (min-optimality)** (p. 305): if `A` is min-stable, then (i) `V_Σ` has a
least element `v_*`, (ii) `v_*` is the unique solution of the Bellman min-equation, (iii) `A` obeys
Bellman's principle of min-optimality and (iv) a min-optimal policy exists. If moreover `Σ` is
finite, min-HPI (HPI for `A^∂`, whose greedy policies are the min-greedy policies of `A`)
terminates at a min-optimal policy. -/
theorem minOptimality {A : ADP V P} (h : A.IsMinStable) :
    ∃ vmin, IsLeast (range (A.vσ h.1.wellPosed)) vmin ∧
      (∀ v, IsFixedPt A.minBellman v ↔ v = vmin) ∧
      (∀ σ, A.IsMinOptimal h.1.wellPosed σ ↔ A.IsMinGreedy vmin σ) ∧
      ∃ σ, A.IsMinOptimal h.1.wellPosed σ := by
  have hd := (A.isMinStable_iff).1 h
  have hw := h.1.wellPosed
  obtain ⟨w, hgr, hfix, hprin, ⟨σ0, hσ0⟩⟩ := hd.optimality
  have hvd : ∀ σ, A.dual.vσ hd.1.wellPosed σ = OrderDual.toDual (A.vσ hw σ) := fun σ =>
    congrArg OrderDual.toDual (dual_vσ hw σ)
  refine ⟨OrderDual.ofDual w, ⟨?_, ?_⟩, fun v => ?_, fun σ => ?_, σ0, ?_⟩
  · obtain ⟨σ, hσ⟩ := hgr.1
    exact ⟨σ, by rw [← hσ, hvd]; rfl⟩
  · rintro _ ⟨τ, rfl⟩
    have := hgr.2 ⟨τ, rfl⟩
    rw [hvd] at this
    exact this
  · have := hfix (OrderDual.toDual v)
    constructor
    · intro hv
      exact congrArg OrderDual.ofDual (this.1 (congrArg OrderDual.toDual hv.eq))
    · intro hv
      have h2 := (this.2 (congrArg OrderDual.toDual hv))
      exact congrArg OrderDual.ofDual h2.eq
  · rw [isMinOptimal_iff hw, isMinGreedy_iff]
    exact hprin σ
  · exact (isMinOptimal_iff hw σ0).2 hσ0

/-- Theorem 9.2.11, final claim: for finite `Σ`, min-HPI from any `σ₀` reaches a repeated value,
and the returned policy is min-optimal. -/
theorem minHpi_terminates [Finite P] {A : ADP V P} (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.dual.hpiValue h.wellPosed.dual σ₀ (k + 1) = A.dual.hpiValue h.wellPosed.dual σ₀ k ∧
      A.IsMinOptimal h.wellPosed (A.dual.hpiPolicy h.wellPosed.dual σ₀ (k + 1)) := by
  have hd : A.dual.IsOrderStable := (A.isOrderStable_dual_iff).2 h
  obtain ⟨k, hk, -, hopt⟩ := hd.hpi_terminates σ₀
  exact ⟨k, hk, (isMinOptimal_iff h.wellPosed _).2 hopt⟩

/-- Min-HPI chooses min-greedy policies: `σₖ₊₁` is `v_{σₖ}`-min-greedy for `A`. -/
theorem minHpi_isMinGreedy {A : ADP V P} (hw : A.WellPosed) (σ₀ : P) (k : ℕ) :
    A.IsMinGreedy (OrderDual.ofDual (A.dual.hpiValue hw.dual σ₀ k))
      (A.dual.hpiPolicy hw.dual σ₀ (k + 1)) :=
  A.dual.isGreedy_greedy _

end ADP

/-- For a globally stable RDP `R`, the ADP `A_R` is min-stable, so Theorem 9.2.11 applies (the
ADP form of Theorem 8.3.7). -/
theorem RDP.toADP_isMinStable {X A : Type*} [Fintype X] [Fintype A] {R : RDP X A}
    (hR : R.IsGloballyStable) : R.toADP.IsMinStable := by
  have := R.policy_nonempty
  have hs := RDP.toADP_isOrderStable hR
  exact (R.toADP.isMinStable_iff).2 ((R.toADP.isOrderStable_dual_iff).2 hs).isMaxStable

end SargentStachurski.AbstractDynamicProgramming

set_option linter.style.longLine false
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.rowsum
#print axioms SargentStachurski.AbstractDynamicProgramming.IsDistribution
#print axioms SargentStachurski.AbstractDynamicProgramming.IsDistribution.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.IsDistribution.nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.IsDistribution.sum_eq_one
#print axioms SargentStachurski.AbstractDynamicProgramming.mulVec_apply_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.mul
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.pow
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.mulVec_const
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.AbstractDynamicProgramming.GloballyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.mapsTo
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.lt_one
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.iterate_mem
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.AbstractDynamicProgramming.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.AbstractDynamicProgramming.fixedPt_le_of_le
#print axioms SargentStachurski.AbstractDynamicProgramming.le_fixedPt_of_le_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.isContractionOn_of_blackwell
#print axioms SargentStachurski.AbstractDynamicProgramming.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.AbstractDynamicProgramming.pow_nonneg_entries
#print axioms SargentStachurski.AbstractDynamicProgramming.pow_le_pow_entries
#print axioms SargentStachurski.AbstractDynamicProgramming.complexify
#print axioms SargentStachurski.AbstractDynamicProgramming.complexify_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.complexify_pow
#print axioms SargentStachurski.AbstractDynamicProgramming.complexify_transpose
#print axioms SargentStachurski.AbstractDynamicProgramming.nnnorm_complexify
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_complexify
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad
#print axioms SargentStachurski.AbstractDynamicProgramming.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_norm_pow_rpow
#print axioms SargentStachurski.AbstractDynamicProgramming.eventually_norm_pow_le
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_norm_pow_zero
#print axioms SargentStachurski.AbstractDynamicProgramming.summable_pow
#print axioms SargentStachurski.AbstractDynamicProgramming.one_sub_mul_tsum
#print axioms SargentStachurski.AbstractDynamicProgramming.tsum_mul_one_sub
#print axioms SargentStachurski.AbstractDynamicProgramming.neumann_series
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_transpose
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_le_norm_of_abs_le
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_le_of_le
#print axioms SargentStachurski.AbstractDynamicProgramming.rowsum_abs_le_norm
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.AbstractDynamicProgramming.abs_entry_le_norm
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_le_norm
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.eventually_abs_entry_pow_le
#print axioms SargentStachurski.AbstractDynamicProgramming.resPartial
#print axioms SargentStachurski.AbstractDynamicProgramming.res
#print axioms SargentStachurski.AbstractDynamicProgramming.res_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.AbstractDynamicProgramming.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.AbstractDynamicProgramming.resPartial_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.summable_res_entry
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_resPartial_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.smul_one_sub_mul_res
#print axioms SargentStachurski.AbstractDynamicProgramming.res_mul_smul_one_sub
#print axioms SargentStachurski.AbstractDynamicProgramming.res_nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.inv_le_res_diag
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.AbstractDynamicProgramming.smul_one_sub_mul_res_real
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_res_complexify_le
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.AbstractDynamicProgramming.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_res_entry_gt
#print axioms SargentStachurski.AbstractDynamicProgramming.isCompact_simplex
#print axioms SargentStachurski.AbstractDynamicProgramming.perron_frobenius
#print axioms SargentStachurski.AbstractDynamicProgramming.perron_frobenius_left
#print axioms SargentStachurski.AbstractDynamicProgramming.le_specRad_of_colsum_ge
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_le_of_colsum_le
#print axioms SargentStachurski.AbstractDynamicProgramming.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_le_of_rowsum_le
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.exists_stationary
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible
#print axioms SargentStachurski.AbstractDynamicProgramming.irreducible_of_pos
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.transpose
#print axioms SargentStachurski.AbstractDynamicProgramming.pow_mulVec_eq_of_mulVec_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.pos_of_mulVec_eq_smul
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.specRad_pos
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.exists_pos_eigenvector
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.exists_pos_left_eigenvector
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms SargentStachurski.AbstractDynamicProgramming.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms SargentStachurski.AbstractDynamicProgramming.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms SargentStachurski.AbstractDynamicProgramming.discountOp
#print axioms SargentStachurski.AbstractDynamicProgramming.discountOp_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.discountOp_nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.discountOp_const
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_smul_isMarkov
#print axioms SargentStachurski.AbstractDynamicProgramming.summable_pow_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.summable_pow_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.mulVec_tsum_pow_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.tsum_pow_mulVec_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.eq_of_eq_add_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.inv_mulVec_eq_add
#print axioms SargentStachurski.AbstractDynamicProgramming.inv_mulVec_eq_tsum
#print axioms SargentStachurski.AbstractDynamicProgramming.eq_add_mulVec_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.specRad_lt_one_iff_existsUnique_pos
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStable_of_iterate_contraction
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStable_of_iterate_contraction_univ
#print axioms SargentStachurski.AbstractDynamicProgramming.affineOp
#print axioms SargentStachurski.AbstractDynamicProgramming.affineOp_iterate_sub
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_isContractionOn_iterate_affineOp
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStable_affineOp
#print axioms SargentStachurski.AbstractDynamicProgramming.isFixedPt_affineOp_inv
#print axioms SargentStachurski.AbstractDynamicProgramming.mulVec_le_mulVec_of_nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_abs_fun
#print axioms SargentStachurski.AbstractDynamicProgramming.norm_le_norm_of_abs_le_fun
#print axioms SargentStachurski.AbstractDynamicProgramming.abs_iterate_sub_le_pow_mulVec
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStable_of_abs_sub_le
#print axioms SargentStachurski.AbstractDynamicProgramming.GloballyStableOn
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStableOn_univ_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.GloballyStableOn.existsUnique
#print axioms SargentStachurski.AbstractDynamicProgramming.GloballyStableOn.of_conj
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStableOn_iff_of_conj
#print axioms SargentStachurski.AbstractDynamicProgramming.iterate_le_iterate_of_monotoneOn
#print axioms SargentStachurski.AbstractDynamicProgramming.knaster_tarski
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_continuum_fixedPts
#print axioms SargentStachurski.AbstractDynamicProgramming.du_concave
#print axioms SargentStachurski.AbstractDynamicProgramming.exists_delta_of_lt
#print axioms SargentStachurski.AbstractDynamicProgramming.du_concave_of_lt
#print axioms SargentStachurski.AbstractDynamicProgramming.neg_mem_Icc_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStableOn_of_reflect
#print axioms SargentStachurski.AbstractDynamicProgramming.du_convex
#print axioms SargentStachurski.AbstractDynamicProgramming.du_convex_of_lt
#print axioms SargentStachurski.AbstractDynamicProgramming.concaveOn_comp
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Γ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Γ_nonempty
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.V
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.B
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.mono
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.consistent
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsFeasible
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Policy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.defaultPolicy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.policy_nonempty
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_apply
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_mapsTo
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_monotoneOn
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.WellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsGloballyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContinuous
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ_spec
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ_mem
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isFixedPt_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.tendsto_iterate_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.B_le_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_le_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.greedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.greedy_mem
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isGreedy_greedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.greedyPolicy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isGreedy_iff_Tσ_eq_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_eq_T_of_isGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.T_mapsTo
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.T_monotoneOn
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.T_apply_eq_sup'
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isGreatest_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.antiGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isLeast_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_T_succ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_Tσ_succ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_T_mono
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_Tσ_mono
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vstar
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ_le_vstar
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsOptimal
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.PrincipleOfOptimality
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.howard
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.opiW
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.hpiPolicy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.hpiValue
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.hpiValue_succ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.opiValue
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.opiValue_one
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.nonstationary_le
#print axioms SargentStachurski.AbstractDynamicProgramming.OrderStable
#print axioms SargentStachurski.AbstractDynamicProgramming.orderStable_of_up_down
#print axioms SargentStachurski.AbstractDynamicProgramming.orderStable_of_globallyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.orderStable_restrict
#print axioms SargentStachurski.AbstractDynamicProgramming.orderStable_affineOp
#print axioms SargentStachurski.AbstractDynamicProgramming.orderStable_dual_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.T
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.exists_greedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.exists_minGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.greedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isGreedy_greedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.T_le_bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isGreatest_bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isGreedy_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.monotone_bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.WellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isFixedPt_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.Vu
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.vσ_mem_Vu
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.howard
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.hpiPolicy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.hpiValue
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.hpiValue_succ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsMaxStable
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOptimal
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.le_howard
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.isOptimal_of_isFixedPt
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.isFixedPt_of_howard
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.howard_fixed
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.hpiValue_le_succ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.exists_hpiValue_succ_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.hpi_terminates
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.isMaxStable
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsMaxStable.optimality
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsOrderStable.maxOptimality
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_wellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_isOrderStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_isMaxStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_wellPosed_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.mk
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.Γ
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.Γ_nonempty
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.β
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.β_pos
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.β_lt_one
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.r
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.P
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.P_nonneg
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.P_rowsum
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.Pσ
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.isMarkov_Pσ
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.rσ
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.toRDP
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.toRDP_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.toADP
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.toRDP_isGloballyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.toADP_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.entropic_mono
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qOp
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qMinGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qOp_mono
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qADP
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qOp_isContractionOn
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.qADP_isMaxStable
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.rsqOp
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.rsqOp_mono
#print axioms SargentStachurski.AbstractDynamicProgramming.MDP.rsqADP
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.le_vσ_of_le_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ_le_of_Tσ_le
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.optimality_of_orderStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.tendsto_iterate_T_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_Tσ_le_iterate_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.opiW_spec
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.iterate_T_le_opi
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.opi_stop
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.eventually_optimal
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.optimality_of_globallyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsBoundedBy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tσ_mapsTo_Icc
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.restrictIcc
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.vσ_mem_Icc
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.restrictIcc_wellPosed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.optimality_of_bounded
#print axioms SargentStachurski.AbstractDynamicProgramming.globallyStableOn_of_isContractionOn
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContracting
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContracting.isContractionOn_Tσ
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContracting.isContractionOn_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContracting.isGloballyStable
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsMixed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Mixed
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmix
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.dirac
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isMixed_dirac
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmix_dirac
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmix_le_T
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmin_le_Tmix
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmix_le_Tmix_of_supported
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.isGreatest_Tmix
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.Tmix_monotoneOn
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.mixedADP
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.mixedADP_bellman
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.IsContracting.isContractionOn_Tmix
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.mixed_value_eq_vstar
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.dual
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.dual_dual
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsMinGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.minBellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsMinOptimal
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.IsMinStable
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isMinGreedy_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isLeast_minBellman
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isMinGreedy_iff_eq
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isOrderStable_dual_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.WellPosed.dual
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.dual_vσ
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isMinStable_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.isMinOptimal_iff
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.minOptimality
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.minHpi_terminates
#print axioms SargentStachurski.AbstractDynamicProgramming.ADP.minHpi_isMinGreedy
#print axioms SargentStachurski.AbstractDynamicProgramming.RDP.toADP_isMinStable
