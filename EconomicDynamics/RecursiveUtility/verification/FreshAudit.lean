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
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Basics`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 8 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `SpectralRadius`), namespace renamed
to `Miao.RecursiveUtility.SS`.

The spectral radius `ρ(A)` of Vol. 1 (1.15) and the facts about it that
Chapters 6–8 use: Gelfand's formula (Lemma 1.2.2), the eventual bound
`‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1), invariance
under transposition, monotonicity in the entries (Exercise 2.2.28), and the
row-sum characterisations of the ℓ∞ operator norm. These are the results of
the `FiniteStates/OperatorsFixedPoints` project restated for a matrix indexed by
an arbitrary finite type `X`, as Chapter 6 needs them on product state spaces
`Y × Z`; each chapter project is self-contained.
-/

open Filter Topology Matrix Finset

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The resolvent series, entrywise

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Resolvent`), namespace renamed to
`Miao.RecursiveUtility.SS`.

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

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Perron–Frobenius theorem for nonnegative matrices

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `PerronFrobenius`), namespace renamed
to `Miao.RecursiveUtility.SS`.

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

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Perron–Frobenius theorem for irreducible matrices

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Irreducible`), namespace renamed to
`Miao.RecursiveUtility.SS`.

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

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear valuation and eventual contractions, restated

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `LinearValuation`), namespace renamed
to `Miao.RecursiveUtility.SS`.

Facts from Vol. 1, Chapter 6 used in Chapters 7–8, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fixed points of order-preserving maps: Knaster–Tarski and Du

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `OrderFixedPoints`), namespace renamed
to `Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.1–§7.1.2.2
(pp. 213–217).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapter 8; each chapter project is self-contained.

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

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A power-transformed affine equation

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `PowerAffine`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.3 (pp. 218–219).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapter 8; each chapter project is self-contained.

For `A ≥ 0` irreducible, `h ≫ 0` and `θ ≠ 0`, the map (7.2)
`Gv = [h + (Av)^{1/θ}]^θ` on `V = (0, ∞)^X`.

* Exercise 7.1.7: `F(t) = (h + t^{1/θ})^θ` is increasing on `(0, ∞)`, convex for
  `θ ∈ (0, 1]` and concave otherwise. Its derivative simplifies to
  `F'(t) = (1 + h t^{−1/θ})^{θ−1}`, whose monotonicity in each case gives the shape.
* Exercise 7.1.8: `G` is an order-preserving self-map of `V`, convex for
  `θ ∈ (0, 1]` and concave otherwise.
* Theorem 7.1.4: `ρ(A)^{1/θ} < 1` iff `G` is globally stable on `V`, and when
  `ρ(A)^{1/θ} ≥ 1`, `G` has no fixed point in `V`. Necessity pairs a fixed point with
  the positive left Perron–Frobenius eigenvector. Sufficiency, which the book
  proves in Stachurski et al. (2022), is proved here with Du's theorem on order
  intervals `[ce, Ce]` around any finite set of points, `e ≫ 0` the right
  Perron–Frobenius eigenvector: `G(se) ≫ se` for small `s` and `G(se) ≪ se` for large
  `s`, so `G` is a convex or concave self-map of each such interval satisfying
  Du's strict condition.
* Exercise 7.1.9: the consumption rate equation of Kleinman et al. (2023) has a
  unique positive Markov solution iff `ρ(A)^ψ < 1`.
-/

open Matrix Finset Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

/-! ### The positive cone -/

/-- The interior `(0, ∞)^X` of the positive cone of `ℝ^X`. -/
def posCone (X : Type*) : Set (X → ℝ) := {v | ∀ x, 0 < v x}

variable {X : Type*}

theorem convex_posCone : Convex ℝ (posCone X) := by
  intro u hu w hw a b ha hb hab x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hu' := hu x
  have hw' := hw x
  have hm := lt_min hu' hw'
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left (u x) (w x)) ha,
    mul_le_mul_of_nonneg_left (min_le_right (u x) (w x)) hb]

variable [Fintype X] [DecidableEq X]

/-- An irreducible matrix has a positive entry in every row. -/
theorem Irreducible.exists_pos_row {A : Matrix X X ℝ} (hA : Irreducible A) (x : X) :
    ∃ x', 0 < A x x' := by
  obtain ⟨k, hk, hpos⟩ := hA.2 x x
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ', Matrix.mul_apply] at hpos
  by_contra hcon
  have : ∑ y, A x y * (A ^ j) y x ≤ 0 := sum_nonpos fun y _ => by
    have h1 : A x y ≤ 0 := not_lt.1 fun h => hcon ⟨y, h⟩
    rw [le_antisymm h1 (hA.1 x y), zero_mul]
  linarith

omit [DecidableEq X] in
/-- `Av ≫ 0` for `v ≫ 0` when every row of `A ≥ 0` has a positive entry. -/
theorem mulVec_pos_of_row {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {v : X → ℝ} (hv : v ∈ posCone X) (x : X) :
    0 < (A *ᵥ v) x := by
  obtain ⟨x', hx'⟩ := hrow x
  calc 0 < A x x' * v x' := mul_pos hx' (hv x')
    _ ≤ ∑ y, A x y * v y :=
        single_le_sum (fun y _ => mul_nonneg (hA x y) (hv y).le) (mem_univ x')

/-- Multiplying the entries of an irreducible matrix by positive numbers preserves
irreducibility. -/
theorem Irreducible.of_pos_mul {P : Matrix X X ℝ} (hP : Irreducible P) {c : X → X → ℝ}
    (hc : ∀ x x', 0 < c x x') : Irreducible (Matrix.of fun x x' => c x x' * P x x') := by
  set B : Matrix X X ℝ := Matrix.of fun x x' => c x x' * P x x' with hB
  have hB0 : ∀ x x', 0 ≤ B x x' := fun x x' => mul_nonneg (hc x x').le (hP.1 x x')
  have key : ∀ k x x', 0 < (P ^ k) x x' → 0 < (B ^ k) x x' := by
    intro k
    induction k with
    | zero => intro x x' h; simpa using h
    | succ k ih =>
      intro x x' h
      rw [pow_succ', Matrix.mul_apply] at h ⊢
      obtain ⟨y, hy⟩ : ∃ y, 0 < P x y * (P ^ k) y x' := by
        by_contra hcon
        have : ∑ y, P x y * (P ^ k) y x' ≤ 0 :=
          sum_nonpos fun y _ => not_lt.1 fun h' => hcon ⟨y, h'⟩
        linarith
      have hPxy : 0 < P x y := by
        rcases (hP.1 x y).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, zero_mul] at hy; exact absurd hy (lt_irrefl 0)
      have hPk : 0 < (P ^ k) y x' := by
        rcases (pow_nonneg_entries hP.1 k y x').lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
      calc 0 < B x y * (B ^ k) y x' := mul_pos (mul_pos (hc x y) hPxy) (ih y x' hPk)
        _ ≤ ∑ z, B x z * (B ^ k) z x' :=
            single_le_sum (fun z _ => mul_nonneg (hB0 x z) (pow_nonneg_entries hB0 k z x'))
              (mem_univ y)
  exact ⟨hB0, fun x x' => by
    obtain ⟨k, hk, hpos⟩ := hP.2 x x'
    exact ⟨k, hk, key k x x' hpos⟩⟩

/-! ### Exercise 7.1.7: the scalar map `F(t) = (h + t^{1/θ})^θ` -/

/-- The scalar map `F(t) = (h + t^{1/θ})^θ` of Exercise 7.1.7. -/
noncomputable def powF (h θ t : ℝ) : ℝ := (h + t ^ θ⁻¹) ^ θ

omit [Fintype X] [DecidableEq X] in
theorem powF_pos {h θ t : ℝ} (hh : 0 ≤ h) (ht : 0 < t) : 0 < powF h θ t :=
  Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos ht _)) _

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (p. 218): `F` is increasing on `(0, ∞)`. -/
theorem powF_monotoneOn {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) : MonotoneOn (powF h θ) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  have hbs : 0 < h + s ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos hs' _)
  unfold powF
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ ≤ 0 := (inv_lt_zero.2 hneg).le
    have h1 : t ^ θ⁻¹ ≤ s ^ θ⁻¹ := Real.rpow_le_rpow_of_nonpos hs' hst hp
    have hbt : 0 < h + t ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh (Real.rpow_pos_of_pos ht' _)
    exact Real.rpow_le_rpow_of_nonpos hbt (by linarith) hneg.le
  · have h1 : s ^ θ⁻¹ ≤ t ^ θ⁻¹ := Real.rpow_le_rpow hs'.le hst (inv_nonneg.2 hpos.le)
    exact Real.rpow_le_rpow hbs.le (by linarith) hpos.le

omit [Fintype X] [DecidableEq X] in
/-- The derivative of `F`: `F'(t) = (1 + h t^{−1/θ})^{θ−1}` for `t > 0`. -/
theorem hasDerivAt_powF {h θ t : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) (ht : 0 < t) :
    HasDerivAt (powF h θ) ((1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)) t := by
  have htp : 0 < t ^ θ⁻¹ := Real.rpow_pos_of_pos ht _
  have htn : 0 < t ^ (-θ⁻¹) := Real.rpow_pos_of_pos ht _
  have hB : 0 < 1 + h * t ^ (-θ⁻¹) := by positivity
  have hbase : 0 < h + t ^ θ⁻¹ := add_pos_of_nonneg_of_pos hh htp
  have h1 : HasDerivAt (fun t => h + t ^ θ⁻¹) (θ⁻¹ * t ^ (θ⁻¹ - 1)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_add h
  have h2 := h1.rpow_const (p := θ) (Or.inl hbase.ne')
  have hF : powF h θ = fun y => (h + y ^ θ⁻¹) ^ θ := rfl
  rw [hF]
  convert h2 using 1
  have e1 : h + t ^ θ⁻¹ = t ^ θ⁻¹ * (1 + h * t ^ (-θ⁻¹)) := by
    rw [Real.rpow_neg ht.le]
    field_simp
    ring
  have e2 : (t ^ θ⁻¹ * (1 + h * t ^ (-θ⁻¹))) ^ (θ - 1) =
      t ^ (θ⁻¹ * (θ - 1)) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1) := by
    rw [Real.mul_rpow htp.le hB.le, ← Real.rpow_mul ht.le]
  have e3 : θ⁻¹ * (θ - 1) = 1 - θ⁻¹ := by field_simp
  have e4 : t ^ (θ⁻¹ - 1) * t ^ (1 - θ⁻¹) = 1 := by
    rw [← Real.rpow_add ht]
    simp
  have e5 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ
  rw [e1, e2, e3]
  calc (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)
      = (θ⁻¹ * θ) * (t ^ (θ⁻¹ - 1) * t ^ (1 - θ⁻¹)) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1) := by
        rw [e5, e4]; ring
    _ = θ⁻¹ * t ^ (θ⁻¹ - 1) * θ * (t ^ (1 - θ⁻¹) * (1 + h * t ^ (-θ⁻¹)) ^ (θ - 1)) := by ring

omit [Fintype X] [DecidableEq X] in
theorem continuousOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) :
    ContinuousOn (powF h θ) (Ioi 0) :=
  fun _ ht => (hasDerivAt_powF hh hθ ht).continuousAt.continuousWithinAt

omit [Fintype X] [DecidableEq X] in
theorem differentiableOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) :
    DifferentiableOn ℝ (powF h θ) (interior (Ioi 0)) := by
  rw [interior_Ioi]
  exact fun _ ht => (hasDerivAt_powF hh hθ ht).differentiableAt.differentiableWithinAt

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (i) (p. 218): `F` is convex on `(0, ∞)` when `θ ∈ (0, 1]`. -/
theorem convexOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ConvexOn ℝ (Ioi 0) (powF h θ) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (continuousOn_powF hh hθ0.ne')
    (differentiableOn_powF hh hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(hasDerivAt_powF hh hθ0.ne' hs').deriv, (hasDerivAt_powF hh hθ0.ne' ht').deriv]
  have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hs' hst (by have := inv_pos.2 hθ0; linarith)
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  exact Real.rpow_le_rpow_of_nonpos hBt (by nlinarith) (by linarith)

omit [Fintype X] [DecidableEq X] in
/-- Exercise 7.1.7 (ii) (p. 218): `F` is concave on `(0, ∞)` when `θ > 1` or `θ < 0`. -/
theorem concaveOn_powF {h θ : ℝ} (hh : 0 ≤ h) (hθ : θ ≠ 0) (hθ1 : ¬ (0 < θ ∧ θ ≤ 1)) :
    ConcaveOn ℝ (Ioi 0) (powF h θ) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) (continuousOn_powF hh hθ)
    (differentiableOn_powF hh hθ) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(hasDerivAt_powF hh hθ hs').deriv, (hasDerivAt_powF hh hθ ht').deriv]
  have hBs : 0 < 1 + h * s ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos hs' (-θ⁻¹); positivity
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · -- `θ < 0`: `B` increasing, exponent `θ − 1 < 0`
    have h1 : s ^ (-θ⁻¹) ≤ t ^ (-θ⁻¹) :=
      Real.rpow_le_rpow hs'.le hst (by have := inv_lt_zero.2 hneg; linarith)
    exact Real.rpow_le_rpow_of_nonpos hBs (by nlinarith) (by linarith)
  · -- `θ > 1`: `B` decreasing, exponent `θ − 1 > 0`
    have hθ1' : 1 < θ := by
      by_contra hle
      exact hθ1 ⟨hpos, not_lt.1 hle⟩
    have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
      Real.rpow_le_rpow_of_nonpos hs' hst (by have := inv_pos.2 hpos; linarith)
    exact Real.rpow_le_rpow hBt.le (by nlinarith) (by linarith)

/-! ### Exercise 7.1.8: the map `G` -/

/-- The map (7.2): `(Gv)(x) = [h(x) + (Av)(x)^{1/θ}]^θ`. -/
noncomputable def powG (A : Matrix X X ℝ) (h : X → ℝ) (θ : ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => powF (h x) θ ((A *ᵥ v) x)

omit [DecidableEq X] in
theorem powG_apply (A : Matrix X X ℝ) (h : X → ℝ) (θ : ℝ) (v : X → ℝ) (x : X) :
    powG A h θ v x = (h x + (A *ᵥ v) x ^ θ⁻¹) ^ θ := by
  classical
  exact rfl

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` maps `V = (0, ∞)^X` into itself. -/
theorem powG_mapsTo {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x') (hrow : ∀ x, ∃ x', 0 < A x x')
    {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) (θ : ℝ) : MapsTo (powG A h θ) (posCone X) (posCone X) :=
  fun _ hv x => powF_pos (hh x) (mulVec_pos_of_row hA hrow hv x)

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is order preserving on `V`. -/
theorem powG_monotoneOn {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ : θ ≠ 0) :
    MonotoneOn (powG A h θ) (posCone X) := by
  intro u hu w hw huw x
  exact powF_monotoneOn (hh x) hθ (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x)
    (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (huw y) (hA x y))

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is convex on `V` when `θ ∈ (0, 1]`. -/
theorem convexOn_powG {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : ConvexOn ℝ (posCone X) (powG A h θ) := by
  refine ⟨convex_posCone, fun u hu w hw a b ha hb hab x => ?_⟩
  have := (convexOn_powF (hh x) hθ0 hθ1).2 (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x) ha hb hab
  simpa [powG, mulVec_add, mulVec_smul] using this

omit [DecidableEq X] in
/-- Exercise 7.1.8 (p. 219): `G` is concave on `V` when `θ > 1` or `θ < 0`. -/
theorem concaveOn_powG {A : Matrix X X ℝ} (hA : ∀ x x', 0 ≤ A x x')
    (hrow : ∀ x, ∃ x', 0 < A x x') {h : X → ℝ} (hh : ∀ x, 0 ≤ h x) {θ : ℝ} (hθ : θ ≠ 0)
    (hθ1 : ¬ (0 < θ ∧ θ ≤ 1)) : ConcaveOn ℝ (posCone X) (powG A h θ) := by
  refine ⟨convex_posCone, fun u hu w hw a b ha hb hab x => ?_⟩
  have := (concaveOn_powF (hh x) hθ hθ1).2 (mulVec_pos_of_row hA hrow hu x)
    (mulVec_pos_of_row hA hrow hw x) ha hb hab
  simpa [powG, mulVec_add, mulVec_smul] using this

/-! ### Theorem 7.1.4 -/

variable [Nonempty X]

/-- Theorem 7.1.4 (p. 218), necessity: if `G` has a fixed point in `V`, then `ρ(A)^{1/θ} < 1`.
With `ε ≫ 0` the left Perron–Frobenius eigenvector, `v = Gv` gives `v^{1/θ} = h + (Av)^{1/θ}`, so
`Av ≪ v` (`θ > 0`) or `Av ≫ v` (`θ < 0`), and pairing with `ε` gives `ρ(A) < 1` or `ρ(A) > 1`. -/
theorem specRad_rpow_lt_one_of_isFixedPt {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X)
    (hfix : IsFixedPt (powG A h θ) v) : specRad A ^ θ⁻¹ < 1 := by
  obtain ⟨ε, hε, hεA⟩ := hA.exists_pos_left_eigenvector
  have hρ := hA.specRad_pos
  have hAv := mulVec_pos_of_row hA.1 hA.exists_pos_row hv
  have key : ∀ x, (A *ᵥ v) x ^ θ⁻¹ < v x ^ θ⁻¹ := fun x => by
    have h1 : v x = (h x + (A *ᵥ v) x ^ θ⁻¹) ^ θ := (congrFun hfix x).symm
    have hb : 0 ≤ h x + (A *ᵥ v) x ^ θ⁻¹ :=
      add_nonneg (hh x).le (Real.rpow_nonneg (hAv x).le _)
    have h2 : v x ^ θ⁻¹ = h x + (A *ᵥ v) x ^ θ⁻¹ := by rw [h1, Real.rpow_rpow_inv hb hθ]
    linarith [hh x]
  have hpair : ε ⬝ᵥ (A *ᵥ v) = specRad A * (ε ⬝ᵥ v) := by
    rw [dotProduct_mulVec, hεA, smul_dotProduct, smul_eq_mul]
  have hεv : 0 < ε ⬝ᵥ v := sum_pos (fun x _ => mul_pos (hε x) (hv x)) univ_nonempty
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    have hlt : ∀ x, v x < (A *ᵥ v) x := fun x =>
      (Real.rpow_lt_rpow_iff_of_neg (hAv x) (hv x) hp).1 (key x)
    have h1 : ε ⬝ᵥ v < ε ⬝ᵥ (A *ᵥ v) :=
      sum_lt_sum_of_nonempty univ_nonempty fun x _ => mul_lt_mul_of_pos_left (hlt x) (hε x)
    have hρ1 : 1 < specRad A := by nlinarith
    exact Real.rpow_lt_one_of_one_lt_of_neg hρ1 hp
  · have hp : 0 < θ⁻¹ := inv_pos.2 hpos
    have hlt : ∀ x, (A *ᵥ v) x < v x := fun x =>
      (Real.rpow_lt_rpow_iff (hAv x).le (hv x).le hp).1 (key x)
    have h1 : ε ⬝ᵥ (A *ᵥ v) < ε ⬝ᵥ v :=
      sum_lt_sum_of_nonempty univ_nonempty fun x _ => mul_lt_mul_of_pos_left (hlt x) (hε x)
    have hρ1 : specRad A < 1 := by nlinarith
    exact Real.rpow_lt_one (specRad_nonneg A) hρ1 hp

/-- **Theorem 7.1.4** (p. 218): if `ρ(A)^{1/θ} ≥ 1`, then `G` has no fixed point in `V`. -/
theorem not_isFixedPt_powG {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (h1 : 1 ≤ specRad A ^ θ⁻¹) {v : X → ℝ}
    (hv : v ∈ posCone X) : ¬ IsFixedPt (powG A h θ) v := fun hfix =>
  absurd (specRad_rpow_lt_one_of_isFixedPt hA hh hθ hv hfix) (not_lt.2 h1)

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- The scalar comparison behind Theorem 7.1.4: with `r = ρ^{1/θ} < 1`, `K = h/(1 − r)` and `y > 0`,
`y < (h + r y^{1/θ})^θ` below `min(h^θ, K^θ)` and `(h + r y^{1/θ})^θ < y` above `max(h^θ, K^θ)`. -/
theorem scalar_bounds {h θ r y : ℝ} (hh : 0 < h) (hθ : θ ≠ 0) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy : 0 < y) :
    (y < min (h ^ θ) ((h / (1 - r)) ^ θ) → y < (h + r * y ^ θ⁻¹) ^ θ) ∧
      (max (h ^ θ) ((h / (1 - r)) ^ θ) < y → (h + r * y ^ θ⁻¹) ^ θ < y) := by
  have hK : 0 < h / (1 - r) := div_pos hh (by linarith)
  have hyp : 0 < y ^ θ⁻¹ := Real.rpow_pos_of_pos hy _
  have hyinv : (y ^ θ⁻¹) ^ θ = y := Real.rpow_inv_rpow hy.le hθ
  have hhinv : (h ^ θ) ^ θ⁻¹ = h := Real.rpow_rpow_inv hh.le hθ
  have hKinv : ((h / (1 - r)) ^ θ) ^ θ⁻¹ = h / (1 - r) := Real.rpow_rpow_inv hK.le hθ
  have hb : 0 < h + r * y ^ θ⁻¹ := by positivity
  have hKy : ∀ z, h / (1 - r) < z → h + r * z < z := fun z hz => by
    rw [div_lt_iff₀ (by linarith)] at hz
    linarith
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hp : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    constructor
    · intro hlt
      have h1 : y < (h / (1 - r)) ^ θ := lt_of_lt_of_le hlt (min_le_right _ _)
      have h2 : h / (1 - r) < y ^ θ⁻¹ := by
        have := Real.rpow_lt_rpow_of_neg hy h1 hp
        rwa [hKinv] at this
      have h3 := Real.rpow_lt_rpow_of_neg hb (hKy _ h2) hneg
      rwa [hyinv] at h3
    · intro hlt
      have h1 : h ^ θ < y := lt_of_le_of_lt (le_max_left _ _) hlt
      have h2 : y ^ θ⁻¹ < h := by
        have := Real.rpow_lt_rpow_of_neg (Real.rpow_pos_of_pos hh θ) h1 hp
        rwa [hhinv] at this
      have h3 := Real.rpow_lt_rpow_of_neg hyp (by nlinarith : y ^ θ⁻¹ < h + r * y ^ θ⁻¹) hneg
      rwa [hyinv] at h3
  · have hp : 0 < θ⁻¹ := inv_pos.2 hpos
    constructor
    · intro hlt
      have h1 : y < h ^ θ := lt_of_lt_of_le hlt (min_le_left _ _)
      have h2 : y ^ θ⁻¹ < h := by
        have := Real.rpow_lt_rpow hy.le h1 hp
        rwa [hhinv] at this
      have h3 := Real.rpow_lt_rpow hyp.le (by nlinarith : y ^ θ⁻¹ < h + r * y ^ θ⁻¹) hpos
      rwa [hyinv] at h3
    · intro hlt
      have h1 : (h / (1 - r)) ^ θ < y := lt_of_le_of_lt (le_max_right _ _) hlt
      have h2 : h / (1 - r) < y ^ θ⁻¹ := by
        have := Real.rpow_lt_rpow (Real.rpow_pos_of_pos hK θ).le h1 hp
        rwa [hKinv] at this
      have h3 := Real.rpow_lt_rpow hb.le (hKy _ h2) hpos
      rwa [hyinv] at h3

omit [Nonempty X] [DecidableEq X] in
/-- `G(se)(x) = (h(x) + ρ^{1/θ}(s e(x))^{1/θ})^θ` for an eigenvector `Ae = ρe`. -/
theorem powG_smul_eigen {A : Matrix X X ℝ} {h : X → ℝ} {θ ρ : ℝ} (hρ : 0 ≤ ρ) {e : X → ℝ}
    (he0 : ∀ x, 0 ≤ e x) (he : A *ᵥ e = ρ • e) {s : ℝ} (hs : 0 ≤ s) (x : X) :
    powG A h θ (s • e) x = (h x + ρ ^ θ⁻¹ * (s * e x) ^ θ⁻¹) ^ θ := by
  classical
  rw [powG_apply, mulVec_smul, he]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show s * (ρ * e x) = ρ * (s * e x) by ring, Real.mul_rpow hρ (mul_nonneg hs (he0 x))]

omit [DecidableEq X] in
/-- Below a positive threshold, `se ≪ G(se)`; above another, `G(se) ≪ se`. -/
theorem exists_thresholds {A : Matrix X X ℝ} {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) {e : X → ℝ}
    (he0 : ∀ x, 0 < e x) (he : A *ᵥ e = specRad A • e) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ (∀ s, 0 < s → s < c₀ → ∀ x, (s • e) x < powG A h θ (s • e) x) ∧
      ∀ s, C₀ < s → ∀ x, powG A h θ (s • e) x < (s • e) x := by
  set r := specRad A ^ θ⁻¹ with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (specRad_nonneg A) _
  set m : X → ℝ := fun x => min (h x ^ θ) ((h x / (1 - r)) ^ θ) / e x with hm
  set M : X → ℝ := fun x => max (h x ^ θ) ((h x / (1 - r)) ^ θ) / e x with hM
  have hmpos : ∀ x, 0 < m x := fun x =>
    div_pos (lt_min (Real.rpow_pos_of_pos (hh x) _)
      (Real.rpow_pos_of_pos (div_pos (hh x) (by linarith)) _)) (he0 x)
  refine ⟨univ.inf' univ_nonempty m, univ.sup' univ_nonempty M, ?_, fun s hs hsc x => ?_,
    fun s hsC x => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun x _ => hmpos x
  · have hsx : s < m x := hsc.trans_le (Finset.inf'_le _ (mem_univ x))
    have hy : 0 < s * e x := mul_pos hs (he0 x)
    have h1 : s * e x < min (h x ^ θ) ((h x / (1 - r)) ^ θ) := by
      rwa [hm, lt_div_iff₀ (he0 x)] at hsx
    rw [powG_smul_eigen (specRad_nonneg A) (fun x => (he0 x).le) he hs.le x]
    exact (scalar_bounds (hh x) hθ hr0 hρ1 hy).1 h1
  · have hsx : M x < s := lt_of_le_of_lt (Finset.le_sup' _ (mem_univ x)) hsC
    have hM0 : 0 < M x := div_pos (lt_max_of_lt_left (Real.rpow_pos_of_pos (hh x) _)) (he0 x)
    have hs : 0 < s := hM0.trans hsx
    have hy : 0 < s * e x := mul_pos hs (he0 x)
    have h1 : max (h x ^ θ) ((h x / (1 - r)) ^ θ) < s * e x := by
      rwa [hM, div_lt_iff₀ (he0 x)] at hsx
    rw [powG_smul_eigen (specRad_nonneg A) (fun x => (he0 x).le) he hs.le x]
    exact (scalar_bounds (hh x) hθ hr0 hρ1 hy).2 h1

omit [Nonempty X] in
/-- On an order interval `[ce, Ce]` whose endpoints satisfy `ce ≪ G(ce)` and `G(Ce) ≪ Ce`, `G` is
globally stable, by Du's theorem. -/
theorem globallyStableOn_powG_Icc {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) {e : X → ℝ} (he0 : ∀ x, 0 < e x) {c C : ℝ}
    (hc : 0 < c) (hcC : c • e ≤ C • e) (hlo : ∀ x, (c • e) x < powG A h θ (c • e) x)
    (hhi : ∀ x, powG A h θ (C • e) x < (C • e) x) :
    GloballyStableOn (powG A h θ) (Set.Icc (c • e) (C • e)) := by
  have hrow := hA.exists_pos_row
  have hh' : ∀ x, 0 ≤ h x := fun x => (hh x).le
  have hsub : Set.Icc (c • e) (C • e) ⊆ posCone X := fun z hz x =>
    lt_of_lt_of_le (by simpa using mul_pos hc (he0 x)) (hz.1 x)
  have hce : c • e ∈ posCone X := hsub ⟨le_rfl, hcC⟩
  have hCe : C • e ∈ posCone X := hsub ⟨hcC, le_rfl⟩
  have hmono := (powG_monotoneOn hA.1 hrow hh' hθ).mono hsub
  have hmaps : MapsTo (powG A h θ) (Set.Icc (c • e) (C • e)) (Set.Icc (c • e) (C • e)) := by
    intro z hz
    exact ⟨fun x => (hlo x).le.trans (powG_monotoneOn hA.1 hrow hh' hθ hce (hsub hz) hz.1 x),
      fun x => (powG_monotoneOn hA.1 hrow hh' hθ (hsub hz) hCe hz.2 x).trans (hhi x).le⟩
  by_cases hθc : 0 < θ ∧ θ ≤ 1
  · exact du_convex_of_lt hcC hmaps hmono
      ((convexOn_powG hA.1 hrow hh' hθc.1 hθc.2).subset hsub (convex_Icc _ _)) hhi
  · exact du_concave_of_lt hcC hmaps hmono
      ((concaveOn_powG hA.1 hrow hh' hθ hθc).subset hsub (convex_Icc _ _)) hlo

omit [DecidableEq X] in
/-- Any two points of `V` lie in a common interval `[ce, Ce]` with `ce ≪ G(ce)` and
`G(Ce) ≪ Ce`. -/
theorem exists_interval {A : Matrix X X ℝ} {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) {e : X → ℝ}
    (he0 : ∀ x, 0 < e x) (he : A *ᵥ e = specRad A • e) {v w : X → ℝ} (hv : v ∈ posCone X)
    (hw : w ∈ posCone X) :
    ∃ c C : ℝ, 0 < c ∧ c • e ≤ C • e ∧ (∀ x, (c • e) x < powG A h θ (c • e) x) ∧
      (∀ x, powG A h θ (C • e) x < (C • e) x) ∧ v ∈ Set.Icc (c • e) (C • e) ∧
      w ∈ Set.Icc (c • e) (C • e) := by
  obtain ⟨c₀, C₀, hc₀, hsmall, hlarge⟩ := exists_thresholds hh hθ hρ1 he0 he
  set lo : X → ℝ := fun x => min (v x) (w x) / e x with hlo
  set hi : X → ℝ := fun x => max (v x) (w x) / e x with hhi
  set c := min (c₀ / 2) (univ.inf' univ_nonempty lo) with hc
  set C := max (C₀ + 1) (univ.sup' univ_nonempty hi) with hC
  have hlopos : ∀ x, 0 < lo x := fun x => div_pos (lt_min (hv x) (hw x)) (he0 x)
  have hcpos : 0 < c :=
    lt_min (by linarith) ((Finset.lt_inf'_iff _).2 fun x _ => hlopos x)
  have hclo : ∀ x, c * e x ≤ min (v x) (w x) := fun x => by
    have : c ≤ lo x := (min_le_right _ _).trans (Finset.inf'_le _ (mem_univ x))
    rwa [hlo, le_div_iff₀ (he0 x)] at this
  have hChi : ∀ x, max (v x) (w x) ≤ C * e x := fun x => by
    have : hi x ≤ C := (Finset.le_sup' _ (mem_univ x)).trans (le_max_right _ _)
    rwa [hhi, div_le_iff₀ (he0 x)] at this
  have hvI : v ∈ Set.Icc (c • e) (C • e) := ⟨fun x => by
      simpa using (hclo x).trans (min_le_left _ _), fun x => by
      simpa using (le_max_left _ _).trans (hChi x)⟩
  have hwI : w ∈ Set.Icc (c • e) (C • e) := ⟨fun x => by
      simpa using (hclo x).trans (min_le_right _ _), fun x => by
      simpa using (le_max_right _ _).trans (hChi x)⟩
  exact ⟨c, C, hcpos, hvI.1.trans hvI.2,
    hsmall c hcpos (lt_of_le_of_lt (min_le_left _ _) (by linarith)),
    hlarge C (lt_of_lt_of_le (by linarith) (le_max_left _ _)), hvI, hwI⟩

/-- **Theorem 7.1.4** (p. 218), sufficiency: if `A ≥ 0` is irreducible, `h ≫ 0` and
`ρ(A)^{1/θ} < 1`, then `G` is globally stable on `V = (0, ∞)^X`. -/
theorem globallyStableOn_powG {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) (hρ1 : specRad A ^ θ⁻¹ < 1) :
    GloballyStableOn (powG A h θ) (posCone X) := by
  obtain ⟨e, he0, he⟩ := hA.exists_pos_eigenvector
  have hepos : e ∈ posCone X := he0
  obtain ⟨c, C, hc, hcC, hlo, hhi, -, -⟩ := exists_interval hh hθ hρ1 he0 he hepos hepos
  obtain ⟨u, hu, hufix, -, -⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc hcC hlo hhi
  have hupos : u ∈ posCone X := fun x =>
    lt_of_lt_of_le (by simpa using mul_pos hc (he0 x)) (hu.1 x)
  refine ⟨u, hupos, hufix, fun w hw hwfix => ?_, fun v hv => ?_⟩
  · obtain ⟨c', C', hc', hcC', hlo', hhi', huI, hwI⟩ := exists_interval hh hθ hρ1 he0 he hupos hw
    obtain ⟨u', -, -, huniq, -⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc' hcC' hlo' hhi'
    rw [huniq w hwI hwfix, huniq u huI hufix]
  · obtain ⟨c', C', hc', hcC', hlo', hhi', hvI, huI⟩ := exists_interval hh hθ hρ1 he0 he hv hupos
    obtain ⟨u', -, -, huniq, hconv⟩ := globallyStableOn_powG_Icc hA hh hθ he0 hc' hcC' hlo' hhi'
    rw [huniq u huI hufix]
    exact hconv v hvI

/-- **Theorem 7.1.4** (p. 218): for `A ≥ 0` irreducible and `h ≫ 0`, `ρ(A)^{1/θ} < 1` iff `G` is
globally stable on `V`. -/
theorem globallyStableOn_powG_iff {A : Matrix X X ℝ} (hA : Irreducible A) {h : X → ℝ}
    (hh : ∀ x, 0 < h x) {θ : ℝ} (hθ : θ ≠ 0) :
    specRad A ^ θ⁻¹ < 1 ↔ GloballyStableOn (powG A h θ) (posCone X) := by
  refine ⟨globallyStableOn_powG hA hh hθ, fun hst => ?_⟩
  obtain ⟨v, hv, hfix, -, -⟩ := hst
  exact specRad_rpow_lt_one_of_isFixedPt hA hh hθ hv hfix

/-! ### Exercise 7.1.9: a migration model with savings -/

/-- The operator of Exercise 7.1.9: `(Av)(x) = β ∑ f(x')^{(ψ−1)/ψ} v(x') P(x, x')`. -/
noncomputable def kleinmanA (β : ℝ) (f : X → ℝ) (ψ : ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => β * f x' ^ ((ψ - 1) / ψ) * P x x'

/-- Equation (7.3) in Markov form, `σₜ = σ(Xₜ)`, `Rₜ = f(Xₜ)`:
`σ(x)⁻¹ = 1 + β^ψ [∑ f(x')^{(ψ−1)/ψ} σ(x')^{−1/ψ} P(x, x')]^ψ`. -/
def IsKleinmanSol (β : ℝ) (f : X → ℝ) (ψ : ℝ) (P : Matrix X X ℝ) (σ : X → ℝ) : Prop :=
  ∀ x, (σ x)⁻¹ = 1 + β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ

omit [Nonempty X] [DecidableEq X] in
/-- `σ ≫ 0` solves (7.3) iff `w = σ^{−1/ψ}` is a fixed point of `G` with `h = 1` and `θ = 1/ψ`. -/
theorem isKleinmanSol_iff {β : ℝ} (hβ : 0 < β) {f : X → ℝ} (hf : ∀ x, 0 < f x) {ψ : ℝ}
    (hψ : ψ ≠ 0) {P : Matrix X X ℝ} (hP : ∀ x x', 0 ≤ P x x') {σ : X → ℝ} (hσ : σ ∈ posCone X) :
    IsKleinmanSol β f ψ P σ ↔
      IsFixedPt (powG (kleinmanA β f ψ P) (fun _ => 1) ψ⁻¹) fun x => σ x ^ (-ψ⁻¹) := by
  classical
  have hwpos : ∀ x, 0 < σ x ^ (-ψ⁻¹) := fun x => Real.rpow_pos_of_pos (hσ x) _
  have hwψ : ∀ x, (σ x ^ (-ψ⁻¹)) ^ ψ = (σ x)⁻¹ := fun x => by
    rw [← Real.rpow_mul (hσ x).le, neg_mul, inv_mul_cancel₀ hψ, Real.rpow_neg_one]
  have hS0 : ∀ x, 0 ≤ ∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x' := fun x =>
    sum_nonneg fun x' _ => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hf x').le _)
      (Real.rpow_nonneg (hσ x').le _)) (hP x x')
  have hAw : ∀ x, (kleinmanA β f ψ P *ᵥ fun x => σ x ^ (-ψ⁻¹)) x =
      β * ∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x' := fun x => by
    change ∑ x', kleinmanA β f ψ P x x' * σ x' ^ (-ψ⁻¹) = _
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by simp only [kleinmanA, Matrix.of_apply]; ring
  have hAwψ : ∀ x, (kleinmanA β f ψ P *ᵥ fun x => σ x ^ (-ψ⁻¹)) x ^ ψ =
      β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ := fun x => by
    rw [hAw, Real.mul_rpow hβ.le (hS0 x)]
  constructor
  · intro hsol
    funext x
    rw [powG_apply, inv_inv, hAwψ x, ← hsol x, ← hwψ x, Real.rpow_rpow_inv (hwpos x).le hψ]
  · intro hfix x
    have h1 := congrFun hfix x
    rw [powG_apply, inv_inv, hAwψ x] at h1
    have hb : 0 ≤ 1 + β ^ ψ * (∑ x', f x' ^ ((ψ - 1) / ψ) * σ x' ^ (-ψ⁻¹) * P x x') ^ ψ :=
      add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg (hS0 x) _))
    have h2 := congrArg (fun t => t ^ ψ) h1
    rw [Real.rpow_inv_rpow hb hψ, hwψ x] at h2
    exact h2.symm

/-- **Exercise 7.1.9** (p. 219): if `β > 0`, `ψ ≠ 0`, `f ≫ 0` and `P` is irreducible, then (7.3)
has a unique solution of the form `σₜ = σ(Xₜ)` with `σ ≫ 0` iff `ρ(A)^ψ < 1`. -/
theorem existsUnique_kleinmanSol_iff {β : ℝ} (hβ : 0 < β) {f : X → ℝ} (hf : ∀ x, 0 < f x)
    {ψ : ℝ} (hψ : ψ ≠ 0) {P : Matrix X X ℝ} (hP : Irreducible P) :
    (∃! σ, σ ∈ posCone X ∧ IsKleinmanSol β f ψ P σ) ↔ specRad (kleinmanA β f ψ P) ^ ψ < 1 := by
  have hA : Irreducible (kleinmanA β f ψ P) :=
    hP.of_pos_mul (c := fun _ x' => β * f x' ^ ((ψ - 1) / ψ))
      fun _ x' => mul_pos hβ (Real.rpow_pos_of_pos (hf x') _)
  have hψ' : ψ⁻¹ ≠ 0 := inv_ne_zero hψ
  have h1 : ∀ x : X, (0 : ℝ) < (fun _ => (1 : ℝ)) x := fun _ => one_pos
  constructor
  · rintro ⟨σ, ⟨hσ, hsol⟩, -⟩
    have hwpos : (fun x => σ x ^ (-ψ⁻¹)) ∈ posCone X := fun x => Real.rpow_pos_of_pos (hσ x) _
    have := specRad_rpow_lt_one_of_isFixedPt hA h1 hψ' hwpos
      ((isKleinmanSol_iff hβ hf hψ hP.1 hσ).1 hsol)
    rwa [inv_inv] at this
  · intro hρ
    have hρ' : specRad (kleinmanA β f ψ P) ^ (ψ⁻¹)⁻¹ < 1 := by rwa [inv_inv]
    obtain ⟨w, hw, hwfix, hwuniq, -⟩ := globallyStableOn_powG hA h1 hψ' hρ'
    -- `σ = w^{−ψ}` and back
    have hback : ∀ x, (w x ^ (-ψ)) ^ (-ψ⁻¹) = w x := fun x => by
      rw [← Real.rpow_mul (hw x).le, neg_mul_neg, mul_inv_cancel₀ hψ, Real.rpow_one]
    have hσpos : (fun x => w x ^ (-ψ)) ∈ posCone X := fun x => Real.rpow_pos_of_pos (hw x) _
    refine ⟨fun x => w x ^ (-ψ), ⟨hσpos, ?_⟩, fun σ ⟨hσ, hsol⟩ => ?_⟩
    · rw [isKleinmanSol_iff hβ hf hψ hP.1 hσpos]
      convert hwfix using 1
      funext x
      exact hback x
    · have hwσ := hwuniq _ (fun x => Real.rpow_pos_of_pos (hσ x) _)
        ((isKleinmanSol_iff hβ hf hψ hP.1 hσ).1 hsol)
      funext x
      have := congrFun hwσ x
      rw [← this, ← Real.rpow_mul (hσ x).le, neg_mul_neg, inv_mul_cancel₀ hψ, Real.rpow_one]

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Certainty equivalent operators

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `CertaintyEquivalents`), namespace
renamed to `Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.1–§7.3.1.3
(pp. 232–236).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapter 8; each chapter project is self-contained.

* A certainty equivalent operator on `V` is an order-preserving self-map fixing the
  constants. Example 7.3.1 and Exercise 7.3.1: a linear operator (a matrix) is a
  certainty equivalent on `ℝ^X` iff it is a Markov matrix.
* The entropic operator `R_θ v = θ⁻¹ log P exp(θv)` (Example 7.3.2, Exercise 7.3.2),
  the Kreps–Porteus operator `R_γ v = (Pv^γ)^{1/γ}` on `(0, ∞)^X` (Example 7.3.3,
  Exercise 7.3.3) and the quantile operator `R_τ` (Exercise 7.3.4).
* Exercises 7.3.5 and 7.3.6; the properties of §7.3.1.2: positive homogeneity,
  super- and subadditivity and constant-subadditivity; Example 7.3.4; Example 7.3.5,
  the Kreps–Porteus operator is subadditive for `γ ≥ 1` and superadditive for
  `γ ≤ 1`, by a level-set argument: with `a = (Pv^γ)^{1/γ}` and `b = (Pw^γ)^{1/γ}`,
  `(v + w)/(a + b)` is a convex combination of `v/a` and `w/b`, both on the unit
  level set of the convex or concave map `u ↦ Pu^γ`. The book cites Minkowski's
  inequality and Bullen (2003).
* Exercises 7.3.7–7.3.9: the quantile and entropic operators are
  constant-subadditive (indeed translation equivariant), and constant-subadditive
  operators are nonexpansive in the supremum norm.
* (7.17) and Example 7.3.6 (Exercise 7.3.10): the entropic operator is concave for
  `θ < 0`, from the convexity of log-sum-exp, proved by the weighted
  arithmetic–geometric mean inequality. The book cites Föllmer and Knispel (2011).
* Exercise 7.3.11 and Lemma 7.3.1: subadditive (superadditive) positively
  homogeneous operators are convex (concave), so `R_γ` is convex for `γ ≥ 1` and concave for
  `γ ≤ 1`.
* Exercises 7.3.12–7.3.13: the entropic and Kreps–Porteus operators are monotone
  increasing when `P` is.
-/

open Matrix Finset Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

variable {X : Type*} [Fintype X]

/-! ### Definition and the linear case -/

/-- A certainty equivalent operator on `V` (§7.3.1.1): an order-preserving self-map of `V` that
fixes every constant function in `V`. -/
structure IsCertEquiv (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop where
  mapsTo : MapsTo R V V
  mono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → R v ≤ R w
  const : ∀ c : ℝ, (fun _ : X => c) ∈ V → R (fun _ => c) = fun _ => c

/-- Example 7.3.1 (p. 232): conditional expectation `v ↦ Pv` under a Markov matrix is a certainty
equivalent operator on `ℝ^X`. -/
theorem IsMarkov.isCertEquiv {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (fun v => P *ᵥ v) Set.univ :=
  ⟨fun _ _ => mem_univ _, fun _ _ _ _ h => hP.mulVec_le_mulVec h, fun c _ => hP.mulVec_const c⟩

/-- Exercise 7.3.1 (p. 233): a linear operator `v ↦ Mv` is a certainty equivalent operator on `ℝ^X`
iff `M` is a Markov matrix. -/
theorem isCertEquiv_mulVec_iff (M : Matrix X X ℝ) :
    IsCertEquiv (fun v => M *ᵥ v) Set.univ ↔ IsMarkov M := by
  classical
  refine ⟨fun h => ⟨fun x x' => ?_, fun x => ?_⟩, fun h => h.isCertEquiv⟩
  · have h1 := h.mono 0 (mem_univ _) (Pi.single x' 1) (mem_univ _)
      (fun y => by rw [Pi.single_apply]; split_ifs <;> norm_num) x
    simpa [mulVec, dotProduct, Pi.single_apply] using h1
  · have h1 := congrFun (h.const 1 (mem_univ _)) x
    simpa [mulVec, dotProduct] using h1

/-- A Markov matrix maps strictly positive functions to strictly positive functions. -/
theorem IsMarkov.mulVec_pos {P : Matrix X X ℝ} (hP : IsMarkov P) {f : X → ℝ}
    (hf : ∀ x, 0 < f x) (x : X) : 0 < (P *ᵥ f) x := by
  obtain ⟨x', hx'⟩ : ∃ x', 0 < P x x' := by
    by_contra hcon
    have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => not_lt.1 fun h => hcon ⟨x', h⟩
    linarith [hP.rowsum x]
  calc 0 < P x x' * f x' := mul_pos hx' (hf x')
    _ ≤ ∑ y, P x y * f y := single_le_sum (fun y _ => mul_nonneg (hP.nonneg x y) (hf y).le)
        (mem_univ x')

/-! ### Exercises 7.3.5 and 7.3.6 -/

omit [Fintype X] in
/-- Exercise 7.3.5 (p. 233): a certainty equivalent on `V ⊆ ℝ^X₊` containing the nonnegative
constants maps `0` to `0` and nonnegative functions to nonnegative functions. -/
theorem IsCertEquiv.zero_and_nonneg {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hR : IsCertEquiv R V) (h0 : (fun _ : X => (0 : ℝ)) ∈ V) :
    R 0 = 0 ∧ ∀ v ∈ V, 0 ≤ v → 0 ≤ R v := by
  have hR0 : R 0 = 0 := hR.const 0 h0
  exact ⟨hR0, fun v hv hv0 => by simpa [hR0] using hR.mono 0 h0 v hv hv0⟩

omit [Fintype X] in
/-- Exercise 7.3.6 (p. 234): convex combinations of certainty equivalent operators on `ℝ^X` are
certainty equivalent operators. -/
theorem IsCertEquiv.convex_comb {Ra Rb : (X → ℝ) → (X → ℝ)} (ha : IsCertEquiv Ra Set.univ)
    (hb : IsCertEquiv Rb Set.univ) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    IsCertEquiv (fun v => l • Ra v + (1 - l) • Rb v) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · have h1 := ha.mono v (mem_univ _) w (mem_univ _) hvw x
    have h2 := hb.mono v (mem_univ _) w (mem_univ _) hvw x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · rw [ha.const c (mem_univ _), hb.const c (mem_univ _)]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### Properties (§7.3.1.2) -/

/-- Positive homogeneity on `V`: `R(λv) = λRv` for `λ ≥ 0` with `λv ∈ V`. -/
def PosHomogeneous (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ c : ℝ, 0 ≤ c → c • v ∈ V → R (c • v) = c • R v

/-- Superadditivity on `V`: `R(v + w) ≥ Rv + Rw`. -/
def Superadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, v + w ∈ V → R v + R w ≤ R (v + w)

/-- Subadditivity on `V`: `R(v + w) ≤ Rv + Rw`. -/
def Subadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, v + w ∈ V → R (v + w) ≤ R v + R w

/-- Constant-subadditivity on `V`: `R(v + λ𝟙) ≤ Rv + λ𝟙` for `λ ≥ 0`. -/
def ConstSubadditive (R : (X → ℝ) → (X → ℝ)) (V : Set (X → ℝ)) : Prop :=
  ∀ v ∈ V, ∀ c : ℝ, 0 ≤ c → v + (fun _ => c) ∈ V → R (v + fun _ => c) ≤ R v + fun _ => c

/-- Example 7.3.4 (p. 234): `R = P` is positively homogeneous, superadditive and subadditive. -/
theorem mulVec_properties (P : Matrix X X ℝ) :
    PosHomogeneous (fun v => P *ᵥ v) Set.univ ∧ Superadditive (fun v => P *ᵥ v) Set.univ ∧
      Subadditive (fun v => P *ᵥ v) Set.univ :=
  ⟨fun v _ c _ _ => mulVec_smul P c v, fun v _ w _ _ => (mulVec_add P v w).ge,
    fun v _ w _ _ => (mulVec_add P v w).le⟩

/-- Exercise 7.3.9 (p. 234): a constant-subadditive certainty equivalent on `ℝ^X` is nonexpansive in
the supremum norm. -/
theorem nonexpansive_of_constSubadditive {R : (X → ℝ) → (X → ℝ)}
    (hR : IsCertEquiv R Set.univ) (hc : ConstSubadditive R Set.univ) (v w : X → ℝ) :
    ‖R v - R w‖ ≤ ‖v - w‖ := by
  have key : ∀ v w : X → ℝ, ∀ x, R v x - R w x ≤ ‖v - w‖ := by
    intro v w x
    have hle : v ≤ w + fun _ => ‖v - w‖ := fun y => by
      have := norm_le_pi_norm (v - w) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have h1 := hR.mono v (mem_univ _) _ (mem_univ _) hle x
    have h2 := hc w (mem_univ _) ‖v - w‖ (norm_nonneg _) (mem_univ _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨key v w x, by rw [norm_sub_rev]; exact key w v x⟩

omit [Fintype X] in
/-- Exercise 7.3.11 (i) (p. 235): on a convex cone, a subadditive positively homogeneous operator is
convex. -/
theorem convexOn_of_subadditive {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ c : ℝ, 0 < c → c • v ∈ V) (hh : PosHomogeneous R V)
    (hs : Subadditive R V) : ConvexOn ℝ V R := by
  refine ⟨hV, fun u hu w hw a b ha hb hab => ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := hs (a • u) (hcone u hu a ha') (b • w) (hcone w hw b hb') (hV hu hw ha hb hab)
      rwa [hh u hu a ha (hcone u hu a ha'), hh w hw b hb (hcone w hw b hb')] at h1
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

omit [Fintype X] in
/-- Exercise 7.3.11 (ii) (p. 235): on a convex cone, a superadditive positively homogeneous operator
is concave. -/
theorem concaveOn_of_superadditive {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)} (hV : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ c : ℝ, 0 < c → c • v ∈ V) (hh : PosHomogeneous R V)
    (hs : Superadditive R V) : ConcaveOn ℝ V R := by
  refine ⟨hV, fun u hu w hw a b ha hb hab => ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := hs (a • u) (hcone u hu a ha') (b • w) (hcone w hw b hb') (hV hu hw ha hb hab)
      rwa [hh u hu a ha (hcone u hu a ha'), hh w hw b hb (hcone w hw b hb')] at h1
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-! ### The entropic certainty equivalent (Example 7.3.2) -/

/-- The entropic certainty equivalent `(R_θ v)(x) = θ⁻¹ log ∑ exp(θv(x'))P(x, x')`
(Example 7.3.2). -/
noncomputable def entR (θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x)

/-- Exercise 7.3.8, in the stronger form of translation equivariance: `R_θ(v + c) = R_θ v + c`. -/
theorem entR_add_const {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) (v : X → ℝ)
    (c : ℝ) : entR θ P (v + fun _ => c) = entR θ P v + fun _ => c := by
  funext x
  have hpos := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
  have h1 : (P *ᵥ fun x' => Real.exp (θ * (v x' + c))) =
      Real.exp (θ * c) • (P *ᵥ fun x' => Real.exp (θ * v x')) := by
    rw [← mulVec_smul]
    congr 1
    funext x'
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Real.exp_add]
    ring
  change θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * (v x' + c))) x) =
    θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x) + c
  rw [h1, Pi.smul_apply, smul_eq_mul, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  field_simp
  ring

/-- Exercise 7.3.2 (p. 233): `R_θ` is a certainty equivalent operator on `ℝ^X` for `θ ≠ 0`. -/
theorem isCertEquiv_entR {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (entR θ P) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · have hv := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
    have hw := hP.mulVec_pos (f := fun x' => Real.exp (θ * w x')) (fun _ => Real.exp_pos _) x
    unfold entR
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have h1 : (P *ᵥ fun x' => Real.exp (θ * w x')) x ≤ (P *ᵥ fun x' => Real.exp (θ * v x')) x :=
        hP.mulVec_le_mulVec (fun y => Real.exp_le_exp.2 (by nlinarith [hvw y])) x
      exact mul_le_mul_of_nonpos_left (Real.log_le_log hw h1) (inv_lt_zero.2 hneg).le
    · have h1 : (P *ᵥ fun x' => Real.exp (θ * v x')) x ≤ (P *ᵥ fun x' => Real.exp (θ * w x')) x :=
        hP.mulVec_le_mulVec (fun y => Real.exp_le_exp.2 (by nlinarith [hvw y])) x
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hv h1) (inv_pos.2 hpos).le
  · funext x
    simp only [entR, hP.mulVec_const, Real.log_exp]
    field_simp

/-- Exercise 7.3.8 (p. 234): `R_θ` is constant-subadditive. -/
theorem constSubadditive_entR {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConstSubadditive (entR θ P) Set.univ := fun v _ c _ _ => (entR_add_const hθ hP v c).le

/-- Convexity of log-sum-exp: `log ∑ q e^{αa + (1−α)b} ≤ α log ∑ q e^a + (1 − α) log ∑ q e^b` for
weights `q ≥ 0` with a positive entry, by the weighted AM–GM inequality. -/
theorem log_sum_exp_le {q : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hq1 : ∃ x, 0 < q x) (a b : X → ℝ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Real.log (∑ x, q x * Real.exp (α * a x + (1 - α) * b x)) ≤
      α * Real.log (∑ x, q x * Real.exp (a x)) +
        (1 - α) * Real.log (∑ x, q x * Real.exp (b x)) := by
  obtain ⟨x₀, hx₀⟩ := hq1
  have hpos : ∀ f : X → ℝ, 0 < ∑ x, q x * Real.exp (f x) := fun f =>
    lt_of_lt_of_le (mul_pos hx₀ (Real.exp_pos _))
      (single_le_sum (fun x _ => mul_nonneg (hq x) (Real.exp_pos _).le) (mem_univ x₀))
  set A := ∑ x, q x * Real.exp (a x) with hA
  set B := ∑ x, q x * Real.exp (b x) with hB
  have hA0 := hpos a
  have hB0 := hpos b
  -- `∑ q (e^a)^α (e^b)^{1−α} ≤ A^α B^{1−α}`
  have hterm : ∀ x, Real.exp (α * a x + (1 - α) * b x) =
      Real.exp (a x) ^ α * Real.exp (b x) ^ (1 - α) := fun x => by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hamgm : ∀ x, (Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α) ≤
      α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B) := fun x =>
    Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith) (by positivity) (by positivity)
      (by ring)
  have hsum : ∑ x, q x * Real.exp (α * a x + (1 - α) * b x) ≤ A ^ α * B ^ (1 - α) := by
    have h1 : ∑ x, q x * ((Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α)) ≤
        ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hamgm x) (hq x)
    have h2 : ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) = 1 := by
      have : ∑ x, q x * (α * (Real.exp (a x) / A) + (1 - α) * (Real.exp (b x) / B)) =
          α * (A / A) + (1 - α) * (B / B) := by
        rw [hA, hB, sum_div, sum_div, mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun x _ => by ring
      rw [this, div_self hA0.ne', div_self hB0.ne']
      ring
    have h3 : ∑ x, q x * ((Real.exp (a x) / A) ^ α * (Real.exp (b x) / B) ^ (1 - α)) =
        (∑ x, q x * Real.exp (α * a x + (1 - α) * b x)) / (A ^ α * B ^ (1 - α)) := by
      rw [sum_div]
      refine sum_congr rfl fun x _ => ?_
      rw [hterm, Real.div_rpow (Real.exp_pos _).le hA0.le,
        Real.div_rpow (Real.exp_pos _).le hB0.le]
      ring
    rw [h3, h2, div_le_one (by positivity)] at h1
    exact h1
  have hS0 : 0 < ∑ x, q x * Real.exp (α * a x + (1 - α) * b x) := hpos _
  calc Real.log (∑ x, q x * Real.exp (α * a x + (1 - α) * b x))
      ≤ Real.log (A ^ α * B ^ (1 - α)) := Real.log_le_log hS0 hsum
    _ = α * Real.log A + (1 - α) * Real.log B := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hA0, Real.log_rpow hB0]

/-- (7.17) and Example 7.3.6, Exercise 7.3.10 (p. 235): for `θ < 0` the entropic certainty
equivalent is concave on `ℝ^X`. -/
theorem concaveOn_entR {θ : ℝ} (hθ : θ < 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConcaveOn ℝ Set.univ (entR θ P) := by
  refine ⟨convex_univ, fun u _ w _ a b ha hb hab x => ?_⟩
  have hrow : ∃ x', 0 < P x x' := by
    by_contra hcon
    have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => not_lt.1 fun h => hcon ⟨x', h⟩
    linarith [hP.rowsum x]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have h1 := log_sum_exp_le (q := P x) (hP.nonneg x) hrow (fun x' => θ * u x')
    (fun x' => θ * w x') ha (by linarith)
  simp only [entR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
  have h2 : ∀ x', θ * (a * u x' + (1 - a) * w x') = a * (θ * u x') + (1 - a) * (θ * w x') :=
    fun x' => by ring
  simp only [h2]
  have hθ' : θ⁻¹ < 0 := inv_lt_zero.2 hθ
  nlinarith [mul_le_mul_of_nonpos_left h1 hθ'.le]

/-! ### The Kreps–Porteus certainty equivalent (Example 7.3.3) -/

/-- The Kreps–Porteus certainty equivalent `(R_γ v)(x) = (∑ v(x')^γ P(x, x'))^{1/γ}` (7.16). -/
noncomputable def kpR (γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => (P *ᵥ fun x' => v x' ^ γ) x ^ γ⁻¹

theorem kpR_pos {γ : ℝ} {P : Matrix X X ℝ} (hP : IsMarkov P) {v : X → ℝ} (hv : v ∈ posCone X)
    (x : X) : 0 < kpR γ P v x :=
  Real.rpow_pos_of_pos (hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') _) x) _

/-- Exercise 7.3.3 (p. 233): `R_γ` is a certainty equivalent operator on `(0, ∞)^X` for `γ ≠ 0`. -/
theorem isCertEquiv_kpR {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    IsCertEquiv (kpR γ P) (posCone X) := by
  refine ⟨fun v hv x => kpR_pos hP hv x, fun v hv w hw hvw x => ?_, fun c hc => ?_⟩
  · have hpv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
    have hpw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
    unfold kpR
    rcases lt_or_gt_of_ne hγ with hneg | hpos
    · have h1 : (P *ᵥ fun x' => w x' ^ γ) x ≤ (P *ᵥ fun x' => v x' ^ γ) x :=
        hP.mulVec_le_mulVec (fun y => Real.rpow_le_rpow_of_nonpos (hv y) (hvw y) hneg.le) x
      exact Real.rpow_le_rpow_of_nonpos hpw h1 (inv_lt_zero.2 hneg).le
    · have h1 : (P *ᵥ fun x' => v x' ^ γ) x ≤ (P *ᵥ fun x' => w x' ^ γ) x :=
        hP.mulVec_le_mulVec (fun y => Real.rpow_le_rpow (hv y).le (hvw y) hpos.le) x
      exact Real.rpow_le_rpow hpv.le h1 (inv_pos.2 hpos).le
  · funext x
    have hc0 : 0 < c := hc x
    simp only [kpR, hP.mulVec_const]
    exact Real.rpow_rpow_inv hc0.le hγ

/-- `R_γ` is positively homogeneous on `(0, ∞)^X`. -/
theorem posHomogeneous_kpR {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    PosHomogeneous (kpR γ P) (posCone X) := by
  intro v hv c hc _
  funext x
  have hpv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  simp only [kpR, Pi.smul_apply, smul_eq_mul]
  have h1 : (P *ᵥ fun x' => (c * v x') ^ γ) = c ^ γ • (P *ᵥ fun x' => v x' ^ γ) := by
    rw [← mulVec_smul]
    congr 1
    funext x'
    rw [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hc (hv x').le]
  rw [h1, Pi.smul_apply, smul_eq_mul, Real.mul_rpow (Real.rpow_nonneg hc _) hpv.le,
    Real.rpow_rpow_inv hc hγ]

/-- On the unit level set: `∑ q (a⁻¹ v)^γ = 1` when `a = (∑ q v^γ)^{1/γ}`. -/
theorem sum_rpow_normalize {γ : ℝ} (hγ : γ ≠ 0) {q v : X → ℝ}
    (hS : 0 < ∑ x, q x * v x ^ γ) :
    ∑ x, q x * ((∑ y, q y * v y ^ γ) ^ γ⁻¹)⁻¹ ^ γ * v x ^ γ = 1 := by
  have ha : 0 < (∑ y, q y * v y ^ γ) ^ γ⁻¹ := Real.rpow_pos_of_pos hS _
  have h1 : ((∑ y, q y * v y ^ γ) ^ γ⁻¹)⁻¹ ^ γ = (∑ y, q y * v y ^ γ)⁻¹ := by
    rw [Real.inv_rpow ha.le, Real.rpow_inv_rpow hS.le hγ]
  rw [h1]
  have : ∑ x, q x * (∑ y, q y * v y ^ γ)⁻¹ * v x ^ γ =
      (∑ y, q y * v y ^ γ)⁻¹ * ∑ x, q x * v x ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [this, inv_mul_cancel₀ hS.ne']

/-- The level-set inequality behind Example 7.3.5. For `φ(t) = t^γ` convex on `(0, ∞)` and
`a = (∑ q v^γ)^{1/γ}`, `b = (∑ q w^γ)^{1/γ}`: `∑ q (v + w)^γ ≤ (a + b)^γ`; for `φ` concave the
reverse. -/
theorem sum_rpow_add_le {γ : ℝ} (hγ : γ ≠ 0) (hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ)
    {q v w : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hv : ∀ x, 0 < v x) (hw : ∀ x, 0 < w x)
    (hSv : 0 < ∑ x, q x * v x ^ γ) (hSw : 0 < ∑ x, q x * w x ^ γ) :
    ∑ x, q x * (v x + w x) ^ γ ≤
      ((∑ x, q x * v x ^ γ) ^ γ⁻¹ + (∑ x, q x * w x ^ γ) ^ γ⁻¹) ^ γ := by
  set a := (∑ x, q x * v x ^ γ) ^ γ⁻¹ with hadef
  set b := (∑ x, q x * w x ^ γ) ^ γ⁻¹ with hbdef
  have ha : 0 < a := Real.rpow_pos_of_pos hSv _
  have hb : 0 < b := Real.rpow_pos_of_pos hSw _
  have hab : 0 < a + b := by linarith
  -- convex combination of the normalised points
  have hcomb : ∀ x, (a + b)⁻¹ * (v x + w x) =
      a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := fun x => by
    field_simp
  have hpt : ∀ x, ((a + b)⁻¹ * (v x + w x)) ^ γ ≤
      a / (a + b) * (a⁻¹ * v x) ^ γ + b / (a + b) * (b⁻¹ * w x) ^ γ := fun x => by
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw x))
      (by positivity) (by positivity) (by field_simp)
  have hnv := sum_rpow_normalize hγ hSv
  have hnw := sum_rpow_normalize hγ hSw
  rw [← hadef] at hnv
  rw [← hbdef] at hnw
  have hsum' : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ ≤
      a / (a + b) * (∑ x, q x * a⁻¹ ^ γ * v x ^ γ) +
        b / (a + b) * (∑ x, q x * b⁻¹ ^ γ * w x ^ γ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have := mul_le_mul_of_nonneg_left (hpt x) (hq x)
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv x).le, Real.mul_rpow (inv_pos.2 hb).le (hw x).le]
      at this
    linarith
  have hsum : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ ≤ a / (a + b) * 1 + b / (a + b) * 1 := by
    rwa [hnv, hnw] at hsum'
  have h1 : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ =
      (a + b)⁻¹ ^ γ * ∑ x, q x * (v x + w x) ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by
      rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv x) (hw x)).le]; ring
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2, Real.inv_rpow hab.le] at hsum
  have h3 : 0 < (a + b) ^ γ := Real.rpow_pos_of_pos hab _
  rwa [inv_mul_le_iff₀ h3, mul_one] at hsum

/-- The concave counterpart of `sum_rpow_add_le`. -/
theorem le_sum_rpow_add {γ : ℝ} (hγ : γ ≠ 0) (hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ γ)
    {q v w : X → ℝ} (hq : ∀ x, 0 ≤ q x) (hv : ∀ x, 0 < v x) (hw : ∀ x, 0 < w x)
    (hSv : 0 < ∑ x, q x * v x ^ γ) (hSw : 0 < ∑ x, q x * w x ^ γ) :
    ((∑ x, q x * v x ^ γ) ^ γ⁻¹ + (∑ x, q x * w x ^ γ) ^ γ⁻¹) ^ γ ≤
      ∑ x, q x * (v x + w x) ^ γ := by
  set a := (∑ x, q x * v x ^ γ) ^ γ⁻¹ with hadef
  set b := (∑ x, q x * w x ^ γ) ^ γ⁻¹ with hbdef
  have ha : 0 < a := Real.rpow_pos_of_pos hSv _
  have hb : 0 < b := Real.rpow_pos_of_pos hSw _
  have hab : 0 < a + b := by linarith
  have hcomb : ∀ x, (a + b)⁻¹ * (v x + w x) =
      a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := fun x => by
    field_simp
  have hpt : ∀ x, a / (a + b) * (a⁻¹ * v x) ^ γ + b / (a + b) * (b⁻¹ * w x) ^ γ ≤
      ((a + b)⁻¹ * (v x + w x)) ^ γ := fun x => by
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw x))
      (by positivity) (by positivity) (by field_simp)
  have hnv := sum_rpow_normalize hγ hSv
  have hnw := sum_rpow_normalize hγ hSw
  rw [← hadef] at hnv
  rw [← hbdef] at hnw
  have hsum' : a / (a + b) * (∑ x, q x * a⁻¹ ^ γ * v x ^ γ) +
        b / (a + b) * (∑ x, q x * b⁻¹ ^ γ * w x ^ γ) ≤
      ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have := mul_le_mul_of_nonneg_left (hpt x) (hq x)
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv x).le, Real.mul_rpow (inv_pos.2 hb).le (hw x).le]
      at this
    linarith
  have hsum : a / (a + b) * 1 + b / (a + b) * 1 ≤ ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ := by
    rwa [hnv, hnw] at hsum'
  have h1 : ∑ x, q x * ((a + b)⁻¹ * (v x + w x)) ^ γ =
      (a + b)⁻¹ ^ γ * ∑ x, q x * (v x + w x) ^ γ := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by
      rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv x) (hw x)).le]; ring
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2, Real.inv_rpow hab.le] at hsum
  have h3 : 0 < (a + b) ^ γ := Real.rpow_pos_of_pos hab _
  rwa [le_inv_mul_iff₀ h3, mul_one] at hsum

/-- `t ↦ t^γ` is convex on `(0, ∞)` for `γ < 0`. -/
theorem convexOn_rpow_of_neg {γ : ℝ} (hγ : γ < 0) : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    (fun t ht =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).continuousAt.continuousWithinAt)
    (by
      rw [interior_Ioi]
      exact fun t ht =>
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))).differentiableAt.differentiableWithinAt)
    ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  rw [Real.deriv_rpow_const, Real.deriv_rpow_const]
  have h1 : t ^ (γ - 1) ≤ s ^ (γ - 1) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  nlinarith

/-- Example 7.3.5 (p. 234): the Kreps–Porteus operator is subadditive on `(0, ∞)^X` for `γ ≥ 1`. -/
theorem subadditive_kpR {γ : ℝ} (hγ : 1 ≤ γ) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    Subadditive (kpR γ P) (posCone X) := by
  intro v hv w hw _ x
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ γ :=
    (convexOn_rpow hγ).subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hSv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hSw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
  have h1 := sum_rpow_add_le hγ0.ne' hφ (hP.nonneg x) hv hw hSv hSw
  have h0 : 0 ≤ ∑ x', P x x' * (v x' + w x') ^ γ :=
    sum_nonneg fun x' _ => mul_nonneg (hP.nonneg x x')
      (Real.rpow_nonneg (add_pos (hv x') (hw x')).le _)
  have h2 := Real.rpow_le_rpow h0 h1 (inv_nonneg.2 hγ0.le)
  rw [Real.rpow_rpow_inv (by positivity) hγ0.ne'] at h2
  simpa [kpR, mulVec, dotProduct] using h2

/-- Example 7.3.5 (p. 234): the Kreps–Porteus operator is superadditive on `(0, ∞)^X` for `γ ≤ 1`,
`γ ≠ 0`. -/
theorem superadditive_kpR {γ : ℝ} (hγ0 : γ ≠ 0) (hγ : γ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) : Superadditive (kpR γ P) (posCone X) := by
  intro v hv w hw _ x
  have hSv := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hSw := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hw x') γ) x
  have hsum0 : 0 < ∑ x', P x x' * (v x' + w x') ^ γ := by
    have := hP.mulVec_pos (f := fun x' => (v x' + w x') ^ γ)
      (fun x' => Real.rpow_pos_of_pos (add_pos (hv x') (hw x')) γ) x
    simpa [mulVec, dotProduct] using this
  have hab : 0 < (∑ x', P x x' * v x' ^ γ) ^ γ⁻¹ + (∑ x', P x x' * w x' ^ γ) ^ γ⁻¹ := by
    have h1 : 0 < ∑ x', P x x' * v x' ^ γ := by simpa [mulVec, dotProduct] using hSv
    have h2 : 0 < ∑ x', P x x' * w x' ^ γ := by simpa [mulVec, dotProduct] using hSw
    positivity
  rcases lt_or_gt_of_ne hγ0 with hneg | hpos
  · have h1 := sum_rpow_add_le hγ0 (convexOn_rpow_of_neg hneg) (hP.nonneg x) hv hw
      (by simpa [mulVec, dotProduct] using hSv) (by simpa [mulVec, dotProduct] using hSw)
    have h2 := Real.rpow_le_rpow_of_nonpos hsum0 h1 (inv_lt_zero.2 hneg).le
    rw [Real.rpow_rpow_inv hab.le hγ0] at h2
    simpa [kpR, mulVec, dotProduct] using h2
  · have hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ γ :=
      (Real.concaveOn_rpow hpos.le hγ).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h1 := le_sum_rpow_add hγ0 hφ (hP.nonneg x) hv hw
      (by simpa [mulVec, dotProduct] using hSv) (by simpa [mulVec, dotProduct] using hSw)
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hab.le _) h1 (inv_nonneg.2 hpos.le)
    rw [Real.rpow_rpow_inv hab.le hγ0] at h2
    simpa [kpR, mulVec, dotProduct] using h2

omit [Fintype X] in
/-- `(0, ∞)^X` is closed under positive scaling. -/
theorem smul_mem_posCone {v : X → ℝ} (hv : v ∈ posCone X) {c : ℝ} (hc : 0 < c) :
    c • v ∈ posCone X := fun x => by simpa using mul_pos hc (hv x)

/-- **Lemma 7.3.1** (p. 235): the Kreps–Porteus operator is convex on `(0, ∞)^X` when `γ ≥ 1`. -/
theorem convexOn_kpR {γ : ℝ} (hγ : 1 ≤ γ) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConvexOn ℝ (posCone X) (kpR γ P) :=
  convexOn_of_subadditive convex_posCone (fun _ hv _ hc => smul_mem_posCone hv hc)
    (posHomogeneous_kpR (by linarith) hP) (subadditive_kpR hγ hP)

/-- **Lemma 7.3.1** (p. 235): the Kreps–Porteus operator is concave on `(0, ∞)^X` when `γ ≤ 1`,
`γ ≠ 0`. -/
theorem concaveOn_kpR {γ : ℝ} (hγ0 : γ ≠ 0) (hγ : γ ≤ 1) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    ConcaveOn ℝ (posCone X) (kpR γ P) :=
  concaveOn_of_superadditive convex_posCone (fun _ hv _ hc => smul_mem_posCone hv hc)
    (posHomogeneous_kpR hγ0 hP) (superadditive_kpR hγ0 hγ hP)

/-! ### The quantile certainty equivalent (Exercise 7.3.4) -/

/-- The conditional distribution function `y ↦ ∑ 1{v(x') ≤ y} P(x, x')`. -/
noncomputable def condCdf (P : Matrix X X ℝ) (v : X → ℝ) (x : X) (y : ℝ) : ℝ :=
  ∑ x', if v x' ≤ y then P x x' else 0

open Classical in
/-- The quantile certainty equivalent of Exercise 7.3.4: the smallest value `y` of `v` with
`∑ 1{v(x') ≤ y} P(x, x') ≥ τ`. For `τ ∈ (0, 1]` and Markov `P` it is the least real `y` with that
property (`isLeast_quantR`). -/
noncomputable def quantR (τ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ := fun x =>
  if h : ((univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v).Nonempty then
    ((univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v).min' h else 0

/-- For `τ ∈ (0, 1]`, `P` Markov and `X` nonempty, `R_τ v(x)` is the least `y` with
`∑ 1{v(x') ≤ y} P(x, x') ≥ τ`, the minimum in Exercise 7.3.4. -/
theorem isLeast_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) (v : X → ℝ) (x : X) :
    IsLeast {y | τ ≤ condCdf P v x y} (quantR τ P v x) := by
  classical
  set S := (univ.filter fun x' => τ ≤ condCdf P v x (v x')).image v with hS
  have hne : S.Nonempty := by
    obtain ⟨xm, -, hxm⟩ := exists_max_image univ v univ_nonempty
    refine ⟨v xm, mem_image.2 ⟨xm, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩⟩
    have : condCdf P v x (v xm) = 1 := by
      rw [condCdf, ← hP.rowsum x]
      exact sum_congr rfl fun x' _ => by simp [hxm x' (mem_univ _)]
    linarith
  have hq : quantR τ P v x = S.min' hne := by
    unfold quantR
    split_ifs with h
    · rfl
    · exact absurd hne h
  rw [hq]
  constructor
  · obtain ⟨x₀, hx₀, he⟩ := mem_image.1 (S.min'_mem hne)
    rw [← he]
    exact (mem_filter.1 hx₀).2
  · intro y hy
    -- some `x''` with `v x'' ≤ y`, else the cdf at `y` is zero
    have hex : (univ.filter fun x' => v x' ≤ y).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have : condCdf P v x y = 0 := sum_eq_zero fun x' _ => by
        have : ¬ v x' ≤ y := fun h => by
          have : x' ∈ univ.filter fun x' => v x' ≤ y := mem_filter.2 ⟨mem_univ x', h⟩
          rw [hcon] at this
          exact absurd this (Finset.notMem_empty _)
        simp [this]
      change τ ≤ condCdf P v x y at hy
      linarith
    obtain ⟨x₁, hx₁, hmax⟩ := exists_max_image _ v hex
    have hx₁y : v x₁ ≤ y := (mem_filter.1 hx₁).2
    have hcdf : condCdf P v x (v x₁) = condCdf P v x y := by
      refine sum_congr rfl fun x' _ => ?_
      by_cases h : v x' ≤ y
      · simp [h, hmax x' (mem_filter.2 ⟨mem_univ _, h⟩)]
      · have : ¬ v x' ≤ v x₁ := fun h' => h (h'.trans hx₁y)
        simp [h, this]
    have hmem : v x₁ ∈ S := mem_image.2 ⟨x₁, mem_filter.2 ⟨mem_univ _, by rw [hcdf]; exact hy⟩,
      rfl⟩
    exact (S.min'_le _ hmem).trans hx₁y

/-- Exercise 7.3.4 (p. 233): for `τ ∈ (0, 1]` and `P` Markov, `R_τ` is a certainty equivalent
operator on `ℝ^X`. -/
theorem isCertEquiv_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) : IsCertEquiv (quantR τ P) Set.univ := by
  refine ⟨fun _ _ => mem_univ _, fun v _ w _ hvw x => ?_, fun c _ => ?_⟩
  · obtain ⟨hw1, -⟩ := isLeast_quantR hτ0 hτ1 hP w x
    refine (isLeast_quantR hτ0 hτ1 hP v x).2 ?_
    change τ ≤ condCdf P v x (quantR τ P w x)
    refine hw1.trans (sum_le_sum fun x' _ => ?_)
    by_cases h : w x' ≤ quantR τ P w x
    · simp [h, (hvw x').trans h]
    · by_cases h' : v x' ≤ quantR τ P w x
      · simp [h, h', hP.nonneg x x']
      · simp [h, h']
  · funext x
    have hcdf : ∀ y, condCdf P (fun _ => c) x y = if c ≤ y then 1 else 0 := fun y => by
      by_cases h : c ≤ y
      · simp [condCdf, h, hP.rowsum x]
      · simp [condCdf, h]
    obtain ⟨h1, h2⟩ := isLeast_quantR hτ0 hτ1 hP (fun _ => c) x
    have hle : quantR τ P (fun _ => c) x ≤ c := h2 (by
      change τ ≤ condCdf P (fun _ => c) x c
      rw [hcdf]
      simp only [le_refl, ↓reduceIte]
      exact hτ1)
    have hge : c ≤ quantR τ P (fun _ => c) x := by
      change τ ≤ condCdf P (fun _ => c) x _ at h1
      rw [hcdf] at h1
      by_contra hlt
      simp only [hlt, ↓reduceIte] at h1
      linarith
    exact le_antisymm hle hge

/-- Exercise 7.3.7, in the stronger form of translation equivariance: `R_τ(v + c) = R_τ v + c`. -/
theorem quantR_add_const [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) {P : Matrix X X ℝ}
    (hP : IsMarkov P) (v : X → ℝ) (c : ℝ) :
    quantR τ P (v + fun _ => c) = quantR τ P v + fun _ => c := by
  funext x
  have hcdf : ∀ y, condCdf P (v + fun _ => c) x y = condCdf P v x (y - c) := fun y =>
    sum_congr rfl fun x' _ => by
      by_cases h : v x' ≤ y - c
      · have : v x' + c ≤ y := by linarith
        simp [h, this]
      · have : ¬ v x' + c ≤ y := fun h' => h (by linarith)
        simp [h, this]
  obtain ⟨h1, h2⟩ := isLeast_quantR hτ0 hτ1 hP (v + fun _ => c) x
  obtain ⟨g1, g2⟩ := isLeast_quantR hτ0 hτ1 hP v x
  change τ ≤ condCdf P (v + fun _ => c) x _ at h1
  change τ ≤ condCdf P v x _ at g1
  simp only [Pi.add_apply]
  apply le_antisymm
  · refine h2 ?_
    change τ ≤ condCdf P (v + fun _ => c) x _
    rw [hcdf, add_sub_cancel_right]
    exact g1
  · have : quantR τ P v x ≤ quantR τ P (v + fun _ => c) x - c :=
      g2 (by change τ ≤ condCdf P v x _; rw [← hcdf]; exact h1)
    linarith

/-- Exercise 7.3.7 (p. 234): `R_τ` is constant-subadditive. -/
theorem constSubadditive_quantR [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : ConstSubadditive (quantR τ P) Set.univ :=
  fun v _ c _ _ => (quantR_add_const hτ0 hτ1 hP v c).le

/-! ### Monotone increasing certainty equivalents (§7.3.1.3) -/

/-- A matrix maps increasing functions to increasing functions (Vol. 1, §3.2.1.3). -/
def MonotoneKernel [Preorder X] (P : Matrix X X ℝ) : Prop :=
  ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h)

/-- A monotone kernel maps decreasing functions to decreasing functions. -/
theorem MonotoneKernel.antitone [Preorder X] {P : Matrix X X ℝ} (hP : MonotoneKernel P)
    {h : X → ℝ} (hh : Antitone h) : Antitone (P *ᵥ h) := by
  have := hP (-h) fun x y hxy => neg_le_neg (hh hxy)
  intro x y hxy
  have h1 := this hxy
  rw [mulVec_neg] at h1
  exact neg_le_neg_iff.1 h1

/-- Exercise 7.3.12 (p. 235): the entropic certainty equivalent maps increasing functions to
increasing functions when `P` is monotone increasing, for every `θ ≠ 0`. -/
theorem monotone_entR [Preorder X] {θ : ℝ} (hθ : θ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {v : X → ℝ} (hv : Monotone v) : Monotone (entR θ P v) := by
  intro x y hxy
  have hpx := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) x
  have hpy := hP.mulVec_pos (f := fun x' => Real.exp (θ * v x')) (fun _ => Real.exp_pos _) y
  unfold entR
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hanti : Antitone fun x' => Real.exp (θ * v x') := fun a b hab =>
      Real.exp_le_exp.2 (by nlinarith [hv hab])
    have h1 := hPm.antitone hanti hxy
    exact mul_le_mul_of_nonpos_left (Real.log_le_log hpy h1) (inv_lt_zero.2 hneg).le
  · have hmono : Monotone fun x' => Real.exp (θ * v x') := fun a b hab =>
      Real.exp_le_exp.2 (by nlinarith [hv hab])
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpx (hPm _ hmono hxy)) (inv_pos.2 hpos).le

/-- Exercise 7.3.13 (p. 236): the Kreps–Porteus certainty equivalent maps increasing positive
functions to increasing functions when `P` is monotone increasing, for every `γ ≠ 0`. -/
theorem monotone_kpR [Preorder X] {γ : ℝ} (hγ : γ ≠ 0) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {v : X → ℝ} (hv0 : v ∈ posCone X) (hv : Monotone v) :
    Monotone (kpR γ P v) := by
  intro x y hxy
  have hpx := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv0 x') γ) x
  have hpy := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv0 x') γ) y
  unfold kpR
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · have hanti : Antitone fun x' => v x' ^ γ := fun a b hab =>
      Real.rpow_le_rpow_of_nonpos (hv0 a) (hv hab) hneg.le
    exact Real.rpow_le_rpow_of_nonpos hpy (hPm.antitone hanti hxy) (inv_lt_zero.2 hneg).le
  · have hmono : Monotone fun x' => v x' ^ γ := fun a b hab =>
      Real.rpow_le_rpow (hv0 a).le (hv hab) hpos.le
    exact Real.rpow_le_rpow hpx.le (hPm _ hmono hxy) (inv_pos.2 hpos).le

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregators, Koopmans operators and lifetime values

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Koopmans`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.4–§7.3.3.2
(pp. 236–242).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapter 8; each chapter project is self-contained.

* Aggregators (§7.3.1.4): Leontief, Uzawa, CES, additive and CES–Uzawa; the
  additive aggregator is the CES aggregator with `α = 1`.
* Koopmans operators `K = A ∘ R` (7.18) are order-preserving self-maps; the
  risk-sensitive and Epstein–Zin operators (Examples 7.3.7–7.3.8) and the time
  additive operator (Remark 7.3.1).
* Exercise 7.3.14: the CES aggregator has elasticity of intertemporal substitution
  `1/(1 − α)`: `log(U_c/U_y) = log((1 − β)/β) + (1 − α) log(y/c)`.
* Example 7.3.9 and Exercise 7.3.15: time additive lifetime value
  `(I − βP)⁻¹r = ∑ (βP)ᵗr`, the finite-horizon value `Kᵐw = ∑_{t<m}(βP)ᵗr + (βP)ᵐw` and
  its convergence.
* Lemma 7.3.2: fixed points of globally stable Koopmans operators that preserve
  increasing functions are increasing.
* Blackwell aggregators (7.19), Exercise 7.3.17 and Proposition 7.3.3: with a
  constant-subadditive certainty equivalent, `K` is a contraction; hence
  Proposition 7.2.2 (risk-sensitive preferences), Exercise 7.3.18 and quantile
  preferences (7.20) with Exercise 7.3.19.
* Uzawa aggregation (§7.3.3): with conditional expectations, `K v = r + Lv` is
  globally stable when `ρ(L) < 1`, its fixed point is the lifetime value (7.22), and
  for `b, r ≫ 0` and `P` irreducible there is no positive fixed point when
  `ρ(L) ≥ 1`; Exercise 7.3.20; Proposition 7.3.4 via Du's theorem.
-/

open Matrix Finset Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X]

/-! ### Aggregators -/

/-- An aggregator on `V` (§7.3.1.4): `x ↦ A(x, v(x))` maps `V` into `V`, and `y ↦ A(x, y)` is
increasing on a set `D` containing the values of the functions in `V`. -/
structure IsAggregator (Agg : X → ℝ → ℝ) (V : Set (X → ℝ)) (D : Set ℝ) : Prop where
  values : ∀ v ∈ V, ∀ x, v x ∈ D
  mapsTo : ∀ v ∈ V, (fun x => Agg x (v x)) ∈ V
  mono : ∀ x, MonotoneOn (Agg x) D

/-- The Leontief aggregator `A(x, y) = min{r(x), βy}`. -/
def leontief (r : X → ℝ) (β : ℝ) : X → ℝ → ℝ := fun x y => min (r x) (β * y)

/-- The Uzawa aggregator `A(x, y) = r(x) + b(x)y`. -/
def uzawa (r b : X → ℝ) : X → ℝ → ℝ := fun x y => r x + b x * y

/-- The CES aggregator `A(x, y) = (r(x)^α + βy^α)^{1/α}`. -/
noncomputable def cesAgg (r : X → ℝ) (β α : ℝ) : X → ℝ → ℝ :=
  fun x y => (r x ^ α + β * y ^ α) ^ α⁻¹

/-- The additive aggregator `A(x, y) = r(x) + βy`. -/
def additive (r : X → ℝ) (β : ℝ) : X → ℝ → ℝ := fun x y => r x + β * y

/-- The CES–Uzawa aggregator `A(x, y) = (r(x)^α + b(x)y^α)^{1/α}`. -/
noncomputable def cesUzawa (r b : X → ℝ) (α : ℝ) : X → ℝ → ℝ :=
  fun x y => (r x ^ α + b x * y ^ α) ^ α⁻¹

omit [Fintype X] in
/-- The additive aggregator is the Uzawa aggregator with constant `b ≡ β`. -/
theorem additive_eq_uzawa (r : X → ℝ) (β : ℝ) : additive r β = uzawa r fun _ => β := rfl

omit [Fintype X] in
/-- The additive aggregator is the CES aggregator with `α = 1` (p. 236). -/
theorem additive_eq_cesAgg (r : X → ℝ) (β : ℝ) : cesAgg r β 1 = additive r β := by
  funext x y
  simp [cesAgg, additive]

omit [Fintype X] in
theorem isAggregator_leontief (r : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    IsAggregator (leontief r β) Set.univ Set.univ :=
  ⟨fun _ _ _ => mem_univ _, fun _ _ => mem_univ _, fun _ _ _ _ _ hyz =>
    min_le_min le_rfl (mul_le_mul_of_nonneg_left hyz hβ)⟩

omit [Fintype X] in
theorem isAggregator_uzawa (r : X → ℝ) {b : X → ℝ} (hb : ∀ x, 0 ≤ b x) :
    IsAggregator (uzawa r b) Set.univ Set.univ :=
  ⟨fun _ _ _ => mem_univ _, fun _ _ => mem_univ _, fun x _ _ _ _ hyz =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hyz (hb x))⟩

omit [Fintype X] in
theorem isAggregator_additive (r : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    IsAggregator (additive r β) Set.univ Set.univ :=
  isAggregator_uzawa r fun _ => hβ

omit [Fintype X] in
/-- The CES–Uzawa aggregator is an aggregator on `(0, ∞)^X` for `r ≫ 0`, `b ≥ 0`, `α ≠ 0`. -/
theorem isAggregator_cesUzawa {r b : X → ℝ} (hr : ∀ x, 0 < r x) (hb : ∀ x, 0 ≤ b x) {α : ℝ}
    (hα : α ≠ 0) : IsAggregator (cesUzawa r b α) (posCone X) (Ioi 0) := by
  have hbase : ∀ x, ∀ y : ℝ, 0 < y → 0 < r x ^ α + b x * y ^ α := fun x y hy =>
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (hr x) _)
      (mul_nonneg (hb x) (Real.rpow_nonneg hy.le _))
  refine ⟨fun v hv x => hv x, fun v hv x => Real.rpow_pos_of_pos (hbase x _ (hv x)) _,
    fun x y hy z hz hyz => ?_⟩
  have hy' : (0 : ℝ) < y := hy
  have hz' : (0 : ℝ) < z := hz
  unfold cesUzawa
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : z ^ α ≤ y ^ α := Real.rpow_le_rpow_of_nonpos hy' hyz hneg.le
    exact Real.rpow_le_rpow_of_nonpos (hbase x z hz')
      (by nlinarith [hb x]) (inv_lt_zero.2 hneg).le
  · have h1 : y ^ α ≤ z ^ α := Real.rpow_le_rpow hy'.le hyz hpos.le
    exact Real.rpow_le_rpow (hbase x y hy').le (by nlinarith [hb x]) (inv_pos.2 hpos).le

omit [Fintype X] in
/-- The CES aggregator is an aggregator on `(0, ∞)^X` for `r ≫ 0`, `β ≥ 0`, `α ≠ 0` (p. 236). -/
theorem isAggregator_cesAgg {r : X → ℝ} (hr : ∀ x, 0 < r x) {β : ℝ} (hβ : 0 ≤ β) {α : ℝ}
    (hα : α ≠ 0) : IsAggregator (cesAgg r β α) (posCone X) (Ioi 0) :=
  isAggregator_cesUzawa (b := fun _ => β) hr (fun _ => hβ) hα

/-! ### Koopmans operators -/

/-- The Koopmans operator `K = A ∘ R` (7.18): `(Kv)(x) = A(x, (Rv)(x))`. -/
def koopmans (Agg : X → ℝ → ℝ) (R : (X → ℝ) → (X → ℝ)) (v : X → ℝ) : X → ℝ :=
  fun x => Agg x (R v x)

omit [Fintype X] in
/-- A Koopmans operator is an order-preserving self-map of `V` (p. 237). -/
theorem koopmans_mapsTo_monotoneOn {Agg : X → ℝ → ℝ} {R : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    {D : Set ℝ} (hA : IsAggregator Agg V D) (hR : IsCertEquiv R V) :
    MapsTo (koopmans Agg R) V V ∧ MonotoneOn (koopmans Agg R) V :=
  ⟨fun _ hv => hA.mapsTo _ (hR.mapsTo hv), fun v hv w hw hvw x =>
    hA.mono x (hA.values _ (hR.mapsTo hv) x) (hA.values _ (hR.mapsTo hw) x)
      (hR.mono v hv w hw hvw x)⟩

/-- Example 7.3.7 (p. 237): the risk-sensitive Koopmans operator (7.10) is `A_ADD ∘ R_θ`. -/
theorem koopmans_additive_entR (r : X → ℝ) (β θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    koopmans (additive r β) (entR θ P) v x =
      r x + β * (θ⁻¹ * Real.log ((P *ᵥ fun x' => Real.exp (θ * v x')) x)) := rfl

/-- Example 7.3.8 (p. 237): the Epstein–Zin Koopmans operator (7.13) is `A_CES ∘ R_γ`. -/
theorem koopmans_cesAgg_kpR (r : X → ℝ) (β α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    koopmans (cesAgg r β α) (kpR γ P) v x =
      (r x ^ α + β * ((P *ᵥ fun x' => v x' ^ γ) x ^ γ⁻¹) ^ α) ^ α⁻¹ := rfl

/-- Remark 7.3.1 (p. 237): the time additive Koopmans operator is `v ↦ r + βPv`. -/
theorem koopmans_additive_mulVec (r : X → ℝ) (β : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    koopmans (additive r β) (fun v => P *ᵥ v) v = r + β • (P *ᵥ v) := rfl

/-! ### Exercise 7.3.14: the elasticity of intertemporal substitution -/

/-- Exercise 7.3.14 (p. 237): for `U(c, y) = ((1 − β)c^α + βy^α)^{1/α}` with `c, y > 0`,
`0 < β < 1` and `α ≠ 0`, the partial derivatives satisfy
`log(U_c/U_y) = log((1 − β)/β) + (1 − α) log(y/c)`, so `d log(y/c)/d log(U_c/U_y) = 1/(1 − α)`. -/
theorem ces_eis {β α c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : α ≠ 0) (hc : 0 < c)
    (hy : 0 < y) :
    ∃ Uc Uy : ℝ, HasDerivAt (fun c' => ((1 - β) * c' ^ α + β * y ^ α) ^ α⁻¹) Uc c ∧
      HasDerivAt (fun y' => ((1 - β) * c ^ α + β * y' ^ α) ^ α⁻¹) Uy y ∧ 0 < Uc ∧ 0 < Uy ∧
      Real.log (Uc / Uy) = Real.log ((1 - β) / β) + (1 - α) * Real.log (y / c) := by
  have hβ1' : 0 < 1 - β := by linarith
  set S := (1 - β) * c ^ α + β * y ^ α with hS
  have hca : 0 < c ^ α := Real.rpow_pos_of_pos hc _
  have hya : 0 < y ^ α := Real.rpow_pos_of_pos hy _
  have hSpos : 0 < S := by positivity
  have hdc : HasDerivAt (fun c' => (1 - β) * c' ^ α + β * y ^ α) ((1 - β) * (α * c ^ (α - 1))) c :=
    ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - β)).add_const _
  have hdy : HasDerivAt (fun y' => (1 - β) * c ^ α + β * y' ^ α) (β * (α * y ^ (α - 1))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul β).const_add _
  have hUc := hdc.rpow_const (p := α⁻¹) (Or.inl hSpos.ne')
  have hUy := hdy.rpow_const (p := α⁻¹) (Or.inl hSpos.ne')
  refine ⟨_, _, hUc, hUy, ?_, ?_, ?_⟩
  · have e : (1 - β) * (α * c ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) =
        (1 - β) * c ^ (α - 1) * S ^ (α⁻¹ - 1) := by field_simp
    rw [e]
    have := Real.rpow_pos_of_pos hc (α - 1)
    have := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    positivity
  · have e : β * (α * y ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) = β * y ^ (α - 1) * S ^ (α⁻¹ - 1) := by
      field_simp
    rw [e]
    have := Real.rpow_pos_of_pos hy (α - 1)
    have := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    positivity
  · have hSa := Real.rpow_pos_of_pos hSpos (α⁻¹ - 1)
    have hc1 := Real.rpow_pos_of_pos hc (α - 1)
    have hy1 := Real.rpow_pos_of_pos hy (α - 1)
    have e : (1 - β) * (α * c ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1) /
        (β * (α * y ^ (α - 1)) * α⁻¹ * S ^ (α⁻¹ - 1)) =
        ((1 - β) / β) * (c ^ (α - 1) / y ^ (α - 1)) := by
      field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_div hc1.ne' hy1.ne',
      Real.log_rpow hc, Real.log_rpow hy, Real.log_div hy.ne' hc.ne']
    ring

/-! ### Lifetime value (§7.3.1.7) -/

variable [DecidableEq X]

/-- Exercise 7.3.15 (i)–(ii) (p. 238): the `m`-period time additive value with terminal condition
`w` is `Kᵐw = ∑_{t<m} (βP)ᵗr + (βP)ᵐw`. -/
theorem iterate_additive_eq (r : X → ℝ) (β : ℝ) (P : Matrix X X ℝ) (w : X → ℝ) (m : ℕ) :
    (koopmans (additive r β) fun v => P *ᵥ v)^[m] w =
      (∑ t ∈ range m, (β • P) ^ t *ᵥ r) + (β • P) ^ m *ᵥ w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iterate_succ_apply', ih, koopmans_additive_mulVec, sum_range_succ', pow_zero, one_mulVec,
      mulVec_add, mulVec_sum, smul_add, smul_sum]
    have h1 : ∀ (u : X → ℝ) (t : ℕ), β • (P *ᵥ ((β • P) ^ t *ᵥ u)) = (β • P) ^ (t + 1) *ᵥ u :=
      fun u t => by rw [← smul_mulVec, mulVec_mulVec, ← pow_succ']
    simp only [h1]
    abel

variable [Nonempty X]

/-- Example 7.3.9 and Exercise 7.3.15 (iii) (p. 238): for `P` Markov and `0 ≤ β < 1`, the time
additive Koopmans operator is globally stable on `ℝ^X`, with fixed point
`(I − βP)⁻¹r = ∑ (βP)ᵗr`, and `Kᵐw → (I − βP)⁻¹r` for every terminal condition `w`. -/
theorem additive_lifetimeValue {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (r : X → ℝ) :
    GloballyStable (koopmans (additive r β) fun v => P *ᵥ v) ∧
      IsFixedPt (koopmans (additive r β) fun v => P *ᵥ v) ((1 - β • P)⁻¹ *ᵥ r) ∧
      (1 - β • P)⁻¹ *ᵥ r = ∑' t : ℕ, (β • P) ^ t *ᵥ r ∧
      ∀ w, Tendsto (fun m => (koopmans (additive r β) fun v => P *ᵥ v)^[m] w) atTop
        (𝓝 ((1 - β • P)⁻¹ *ᵥ r)) := by
  have hρ : specRad (β • P) < 1 := by rw [specRad_smul_isMarkov hP hβ0]; exact hβ1
  have hK : (koopmans (additive r β) fun v => P *ᵥ v) = affineOp (β • P) r := by
    funext v
    rw [koopmans_additive_mulVec, affineOp, smul_mulVec, add_comm]
  rw [hK]
  have hst := globallyStable_affineOp hρ r
  have hfix := isFixedPt_affineOp_inv hρ r
  obtain ⟨u, hu, huniq, hconv⟩ := hst
  have hu' : (1 - β • P)⁻¹ *ᵥ r = u := huniq _ hfix
  refine ⟨⟨u, hu, huniq, hconv⟩, hfix, inv_mulVec_eq_tsum hρ r, fun w => ?_⟩
  rw [hu']
  exact hconv w

omit [DecidableEq X] [Nonempty X] [Fintype X] in
/-- **Lemma 7.3.2** (p. 239), abstract form: if `K` is globally stable on `V`, `V` contains an
increasing function, and `K` maps increasing functions in `V` to increasing functions, then the
fixed point of `K` is increasing. -/
theorem monotone_of_globallyStableOn [Preorder X] {K : (X → ℝ) → (X → ℝ)} {V : Set (X → ℝ)}
    (hst : GloballyStableOn K V) (hmaps : MapsTo K V V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ V)
    (hm₀ : Monotone v₀) (hinv : ∀ v ∈ V, Monotone v → Monotone (K v)) {u : X → ℝ}
    (hu : u ∈ V) (hfix : IsFixedPt K u) : Monotone u := by
  obtain ⟨u', -, -, huniq, hconv⟩ := hst
  rw [huniq u hu hfix]
  have hmono : ∀ k, Monotone (K^[k] v₀) ∧ K^[k] v₀ ∈ V := by
    intro k
    induction k with
    | zero => exact ⟨hm₀, hv₀⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      exact ⟨hinv _ ih.2 ih.1, hmaps ih.2⟩
  intro x y hxy
  have hlim := tendsto_pi_nhds.1 (hconv v₀ hv₀)
  exact le_of_tendsto_of_tendsto' (hlim x) (hlim y) fun k => (hmono k).1 hxy

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- **Lemma 7.3.2** (p. 239): if `K = A ∘ R` is globally stable on `V`, `V` contains an increasing
function, (i) `A(x, y) ≤ A(x', y)` for `x ≤ x'`, and (ii) `R` maps increasing functions in `V` to
increasing functions, then the lifetime value `v*` is increasing. -/
theorem monotone_koopmans_fixedPt [Preorder X] {Agg : X → ℝ → ℝ} {R : (X → ℝ) → (X → ℝ)}
    {V : Set (X → ℝ)} {D : Set ℝ} (hA : IsAggregator Agg V D) (hR : IsCertEquiv R V)
    (hst : GloballyStableOn (koopmans Agg R) V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ V) (hm₀ : Monotone v₀)
    (hAx : ∀ x x', x ≤ x' → ∀ y ∈ D, Agg x y ≤ Agg x' y)
    (hRm : ∀ v ∈ V, Monotone v → Monotone (R v)) {u : X → ℝ} (hu : u ∈ V)
    (hfix : IsFixedPt (koopmans Agg R) u) : Monotone u := by
  refine monotone_of_globallyStableOn hst (koopmans_mapsTo_monotoneOn hA hR).1 hv₀ hm₀
    (fun v hv hm x x' hxx' => ?_) hu hfix
  have hD := hA.values _ (hR.mapsTo hv)
  exact (hA.mono x (hD x) (hD x') (hRm v hv hm hxx')).trans (hAx x x' hxx' _ (hD x'))

/-! ### A Blackwell-type condition (§7.3.2) -/

omit [DecidableEq X] [Nonempty X] in
/-- A Blackwell aggregator (7.19): `A(x, y + λ) ≤ A(x, y) + βλ` for `λ ≥ 0`, with `0 ≤ β < 1`. -/
def IsBlackwellAgg (Agg : X → ℝ → ℝ) (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ ∀ x y c, 0 ≤ c → Agg x (y + c) ≤ Agg x y + β * c

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.17 (p. 240): the additive aggregator is a Blackwell aggregator for `0 ≤ β < 1`. -/
theorem isBlackwellAgg_additive (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsBlackwellAgg (additive r β) β :=
  ⟨hβ0, hβ1, fun x y c _ => by simp only [additive]; linarith⟩

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.17 (p. 240): the Leontief aggregator is a Blackwell aggregator for `0 ≤ β < 1`. -/
theorem isBlackwellAgg_leontief (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsBlackwellAgg (leontief r β) β := by
  refine ⟨hβ0, hβ1, fun x y c hc => ?_⟩
  simp only [leontief]
  rcases le_total (r x) (β * y) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith)

omit [DecidableEq X] [Nonempty X] in
/-- **Proposition 7.3.3** (p. 240): if `A` is a Blackwell aggregator, increasing in `y`, and `R` is
a constant-subadditive certainty equivalent on `ℝ^X`, then `K = A ∘ R` is a contraction of
modulus `β` on `ℝ^X` in the supremum norm. -/
theorem isContractionOn_koopmans {Agg : X → ℝ → ℝ} {β : ℝ} (hA : IsBlackwellAgg Agg β)
    (hmono : ∀ x, Monotone (Agg x)) {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ)
    (hc : ConstSubadditive R Set.univ) : IsContractionOn (koopmans Agg R) Set.univ β := by
  refine isContractionOn_of_blackwell hA.1 hA.2.1
    (fun v w hvw x => hmono x (hR.mono v (mem_univ _) w (mem_univ _) hvw x)) fun u c hc0 x => ?_
  have h1 := hc u (mem_univ _) c hc0 (mem_univ _) x
  calc koopmans Agg R (u + fun _ => c) x = Agg x (R (u + fun _ => c) x) := rfl
    _ ≤ Agg x (R u x + c) := hmono x (by simpa using h1)
    _ ≤ Agg x (R u x) + β * c := hA.2.2 x _ c hc0

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Proposition 7.3.3: under its hypotheses `K` is globally stable on `ℝ^X`. -/
theorem globallyStable_koopmans [Finite X] {Agg : X → ℝ → ℝ} {β : ℝ} (hA : IsBlackwellAgg Agg β)
    (hmono : ∀ x, Monotone (Agg x)) {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ)
    (hc : ConstSubadditive R Set.univ) : GloballyStable (koopmans Agg R) := by
  have := Fintype.ofFinite X
  exact (isContractionOn_koopmans hA hmono hR hc).globallyStable_univ

omit [DecidableEq X] [Nonempty X] in
/-- **Proposition 7.2.2** (p. 224), proved on p. 240: for `0 ≤ β < 1` and `θ ≠ 0` the risk-sensitive
Koopmans operator `K_θ` is globally stable on `ℝ^X`. -/
theorem globallyStable_riskSensitive {P : Matrix X X ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0)
    (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (additive r β) (entR θ P)) :=
  globallyStable_koopmans (isBlackwellAgg_additive r hβ0 hβ1)
    (fun _ _ _ hyz => by simp only [additive]; nlinarith) (isCertEquiv_entR hθ hP)
    (constSubadditive_entR hθ hP)

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 7.3.18 (p. 240): with the Leontief aggregator, `0 ≤ β < 1`, and a constant-subadditive
certainty equivalent on `ℝ^X`, `K = A_MIN ∘ R` is globally stable. -/
theorem globallyStable_leontief [Finite X] (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {R : (X → ℝ) → (X → ℝ)} (hR : IsCertEquiv R Set.univ) (hc : ConstSubadditive R Set.univ) :
    GloballyStable (koopmans (leontief r β) R) :=
  globallyStable_koopmans (isBlackwellAgg_leontief r hβ0 hβ1)
    (fun _ _ _ hyz => min_le_min le_rfl (mul_le_mul_of_nonneg_left hyz hβ0)) hR hc

omit [DecidableEq X] in
/-- Quantile preferences (7.20) (p. 241): for `0 ≤ β < 1` and `τ ∈ (0, 1]`, `K_τ = A_ADD ∘ R_τ` is
globally stable on `ℝ^X`. -/
theorem globallyStable_quantile {P : Matrix X X ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (additive r β) (quantR τ P)) :=
  globallyStable_koopmans (isBlackwellAgg_additive r hβ0 hβ1)
    (fun _ _ _ hyz => by simp only [additive]; nlinarith) (isCertEquiv_quantR hτ0 hτ1 hP)
    (constSubadditive_quantR hτ0 hτ1 hP)

omit [DecidableEq X] in
/-- Exercise 7.3.19 (p. 241): `A_MIN ∘ R_τ` is globally stable on `ℝ^X`. -/
theorem globallyStable_leontief_quantile {P : Matrix X X ℝ} (hP : IsMarkov P) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    GloballyStable (koopmans (leontief r β) (quantR τ P)) :=
  globallyStable_leontief r hβ0 hβ1 (isCertEquiv_quantR hτ0 hτ1 hP)
    (constSubadditive_quantR hτ0 hτ1 hP)

/-! ### Uzawa aggregation (§7.3.3) -/

omit [Nonempty X] [DecidableEq X] in
/-- With `R = P`, the Uzawa Koopmans operator is `Kv = r + Lv`, `L(x, x') = b(x)P(x, x')`
(§7.3.3.1). -/
theorem koopmans_uzawa_mulVec (r b : X → ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    koopmans (uzawa r b) (fun v => P *ᵥ v) v =
      affineOp (Matrix.of fun x x' => b x * P x x') r v := by
  classical
  funext x
  simp only [koopmans, uzawa, affineOp, Pi.add_apply, mulVec, dotProduct, Matrix.of_apply,
    mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- §7.3.3.1 (p. 241): if `ρ(L) < 1` the Uzawa Koopmans operator with conditional expectations is
globally stable on `ℝ^X`, and its fixed point is the lifetime value (7.22),
`(I − L)⁻¹r = ∑ₜ Lᵗr`. -/
theorem uzawa_lifetimeValue (r b : X → ℝ) (P : Matrix X X ℝ)
    (hρ : specRad (Matrix.of fun x x' => b x * P x x') < 1) :
    GloballyStable (koopmans (uzawa r b) fun v => P *ᵥ v) ∧
      IsFixedPt (koopmans (uzawa r b) fun v => P *ᵥ v)
        ((1 - Matrix.of fun x x' => b x * P x x')⁻¹ *ᵥ r) ∧
      (1 - Matrix.of fun x x' => b x * P x x')⁻¹ *ᵥ r =
        ∑' t : ℕ, (Matrix.of fun x x' => b x * P x x') ^ t *ᵥ r := by
  have hK : (koopmans (uzawa r b) fun v => P *ᵥ v) =
      affineOp (Matrix.of fun x x' => b x * P x x') r :=
    funext (koopmans_uzawa_mulVec r b P)
  rw [hK]
  exact ⟨globallyStable_affineOp hρ r, isFixedPt_affineOp_inv hρ r, inv_mulVec_eq_tsum hρ r⟩

omit [Nonempty X] in
/-- Exercise 7.3.20 (p. 242): `L(x, x') = b(x)P(x, x')` is irreducible when `b ≫ 0` and `P` is
irreducible. -/
theorem irreducible_uzawa {b : X → ℝ} (hb : ∀ x, 0 < b x) {P : Matrix X X ℝ}
    (hP : Irreducible P) : Irreducible (Matrix.of fun x x' => b x * P x x') :=
  hP.of_pos_mul (c := fun x _ => b x) fun x _ => hb x

/-- §7.3.3.1 (p. 242): if `b ≫ 0`, `P` is irreducible, `r ≫ 0` and `ρ(L) ≥ 1`, then `Kv = r + Lv`
has no fixed point in `(0, ∞)^X`, by Lemma 6.1.4 (here via Theorem 7.1.4 with `θ = 1`). -/
theorem uzawa_no_pos_fixedPt {b : X → ℝ} (hb : ∀ x, 0 < b x) {P : Matrix X X ℝ}
    (hP : Irreducible P) {r : X → ℝ} (hr : ∀ x, 0 < r x)
    (hρ : 1 ≤ specRad (Matrix.of fun x x' => b x * P x x')) {v : X → ℝ} (hv : v ∈ posCone X) :
    ¬ IsFixedPt (koopmans (uzawa r b) fun v => P *ᵥ v) v := by
  intro hfix
  have hL := irreducible_uzawa hb hP
  have hAv := mulVec_pos_of_row hL.1 hL.exists_pos_row hv
  have hG : IsFixedPt (powG (Matrix.of fun x x' => b x * P x x') r 1) v := by
    funext x
    have h1 := congrFun hfix x
    rw [koopmans_uzawa_mulVec] at h1
    simp only [powG_apply, inv_one, Real.rpow_one]
    rw [← h1, affineOp, Pi.add_apply, add_comm]
  have := specRad_rpow_lt_one_of_isFixedPt hL hr one_ne_zero hv hG
  rw [inv_one, Real.rpow_one] at this
  linarith

/-- The nonnegative cone `ℝ^X₊`. -/
def nonnegCone (X : Type*) : Set (X → ℝ) := {v | ∀ x, 0 ≤ v x}

/-- **Proposition 7.3.4** (p. 242): let `Kv = r + b ⊙ Rv` with `b ≥ 0`, `r ≫ 0` and `R` a concave
certainty equivalent on `ℝ^X₊`. If `b ⊙ Rv ≤ c + Lv` on `ℝ^X₊` for some `c` and some `L ≥ 0` with
`ρ(L) < 1`, then `K` is globally stable on `[0, v̄]`, `v̄ = (I − L)⁻¹(r + c)`. -/
theorem globallyStableOn_uzawa_concave {R : (X → ℝ) → (X → ℝ)}
    (hR : IsCertEquiv R (nonnegCone X)) (hRc : ConcaveOn ℝ (nonnegCone X) R) {b r c : X → ℝ}
    (hb : ∀ x, 0 ≤ b x) (hr : ∀ x, 0 < r x) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (ha : ∀ v ∈ nonnegCone X, ∀ x, b x * R v x ≤ c x + (L *ᵥ v) x) :
    GloballyStableOn (koopmans (uzawa r b) R) (Set.Icc 0 ((1 - L)⁻¹ *ᵥ (r + c))) := by
  set vbar := (1 - L)⁻¹ *ᵥ (r + c) with hvbar
  have h0 : (0 : X → ℝ) ∈ nonnegCone X := fun _ => le_rfl
  have hR0 : R 0 = 0 := hR.const 0 h0
  -- `c ≥ 0`, from (a) at `v = 0`
  have hc : ∀ x, 0 ≤ c x := fun x => by
    have := ha 0 h0 x
    rw [hR0, mulVec_zero] at this
    simpa using this
  have hvbar_eq : vbar = (r + c) + L *ᵥ vbar := inv_mulVec_eq_add hρ (r + c)
  have hvbar0 : ∀ x, 0 ≤ vbar x := fun x => by
    rw [hvbar, inv_mulVec_eq_tsum hρ, Pi.tsum_apply (summable_pow_mulVec hρ _)]
    exact tsum_nonneg fun t => sum_nonneg fun x' _ =>
      mul_nonneg (pow_nonneg_entries hL t x x') (add_nonneg (hr x').le (hc x'))
  have hsub : Set.Icc (0 : X → ℝ) vbar ⊆ nonnegCone X := fun z hz x => hz.1 x
  have hvbarmem : vbar ∈ nonnegCone X := hvbar0
  have hmono : MonotoneOn (koopmans (uzawa r b) R) (nonnegCone X) := fun u hu w hw huw x =>
    add_le_add le_rfl (mul_le_mul_of_nonneg_left (hR.mono u hu w hw huw x) (hb x))
  have hK0 : koopmans (uzawa r b) R 0 = r := by
    funext x
    simp [koopmans, uzawa, hR0]
  have hKbar : koopmans (uzawa r b) R vbar ≤ vbar := fun x => by
    have h1 := ha vbar hvbarmem x
    have h2 := congrFun hvbar_eq x
    simp only [Pi.add_apply] at h2
    change r x + b x * R vbar x ≤ vbar x
    linarith
  have hmaps : MapsTo (koopmans (uzawa r b) R) (Set.Icc 0 vbar) (Set.Icc 0 vbar) := by
    intro z hz
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := hmono h0 (hsub hz) hz.1 x
      rw [hK0] at this
      exact (hr x).le.trans this
    · exact (hmono (hsub hz) hvbarmem hz.2 x).trans (hKbar x)
  have hconc : ConcaveOn ℝ (Set.Icc 0 vbar) (koopmans (uzawa r b) R) := by
    refine ⟨convex_Icc _ _, fun u hu w hw a a' ha ha' haa' x => ?_⟩
    have h1 := hRc.2 (hsub hu) (hsub hw) ha ha' haa' x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [koopmans, uzawa, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h2 := mul_le_mul_of_nonneg_left h1 (hb x)
    have h3 : a * r x + a' * r x = r x := by rw [← add_mul, haa', one_mul]
    nlinarith
  refine du_concave_of_lt (v₁ := 0) (fun x => hvbar0 x) hmaps (hmono.mono hsub) hconc fun x => ?_
  rw [hK0]
  exact hr x

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin preferences

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `EpsteinZin`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.2.3 (pp. 227–232),
Exercise 7.3.16 and §7.3.3.3 (p. 243).

Restated from the `FiniteStates/NonlinearValuation` project (Chapter 7) for use in
Chapter 8; each chapter project is self-contained.

The Epstein–Zin Koopmans operator with state-dependent discounting (7.23),
`Kv = (h + b(Pv^γ)^{α/γ})^{1/α}` on `V = (0, ∞)^X`, contains (7.14), `b ≡ β`, which in
turn is (7.13) when `h = (1 − β)c^α`.

* Exercise 7.2.7 and Exercise 7.3.21: `K` is a self-map of `V`.
* Lemma 7.2.4, Exercise 7.2.8 and Exercise 7.3.22: with `θ = γ/α`, `Φv = v^γ` is a
  homeomorphism of `V` conjugating `K` to `K̂v = (h + (Bv)^{1/θ})^θ`,
  `B(x, x') = b(x)^θP(x, x')`, the map of Theorem 7.1.4.
* Proposition 7.3.5: for `h, b ≫ 0` and `P` irreducible, `K` is globally stable on
  `V` iff `ρ(B)^{α/γ} < 1`.
* Proposition 7.2.3: for `b ≡ β ∈ (0, 1)`, `ρ(B)^{1/θ} = (β^θ)^{1/θ} = β < 1`, so the
  Epstein–Zin Koopmans operator is globally stable.
* Exercise 7.2.9: `F(t) = (h + βt^{1/θ})^θ` with `θ = 5`, `h = β = 1/2` has
  `F'(t) → ∞` as `t ↓ 0`, so `K̂` is not a contraction near zero.
* Exercise 7.3.16: if `P` is monotone increasing and `c` is increasing, Epstein–Zin
  lifetime utility (7.13) is increasing.
-/

open Matrix Finset Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X]

/-- The Epstein–Zin Koopmans operator with state-dependent discounting (7.23):
`(Kv)(x) = (h(x) + b(x)(R_γ v)(x)^α)^{1/α}`, with `R_γ v = (Pv^γ)^{1/γ}`. -/
noncomputable def ezK (h b : X → ℝ) (α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => (h x + b x * kpR γ P v x ^ α) ^ α⁻¹

/-- (7.23) is the Koopmans operator of the CES–Uzawa aggregator and the Kreps–Porteus certainty
equivalent, with `r = h^{1/α}` (§7.3.3.3). -/
theorem ezK_eq_koopmans (h b : X → ℝ) (α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) :
    ezK h b α γ P v = koopmans (fun x y => (h x + b x * y ^ α) ^ α⁻¹) (kpR γ P) v := rfl

/-- (7.13) as an instance of (7.14): with `h = (1 − β)c^α` and `b ≡ β`,
`(Kv)(x) = ((1 − β)c(x)^α + β[∑ v(x')^γ P(x, x')]^{α/γ})^{1/α}`. -/
theorem ezK_apply_ez (c : X → ℝ) (β α γ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X)
    (hpos : 0 ≤ (P *ᵥ fun x' => v x' ^ γ) x) :
    ezK (fun x => (1 - β) * c x ^ α) (fun _ => β) α γ P v x =
      ((1 - β) * c x ^ α + β * ((P *ᵥ fun x' => v x' ^ γ) x) ^ (α / γ)) ^ α⁻¹ := by
  simp only [ezK, kpR]
  rw [← Real.rpow_mul hpos, div_eq_inv_mul]

/-- Exercise 7.2.7 (p. 228) and Exercise 7.3.21 (p. 243): for `P` Markov, `h ≥ 0` and `b ≫ 0`,
`K` is a self-map of `V = (0, ∞)^X`. -/
theorem ezK_mapsTo {P : Matrix X X ℝ} (hP : IsMarkov P) {h b : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hb : ∀ x, 0 < b x) (α γ : ℝ) : MapsTo (ezK h b α γ P) (posCone X) (posCone X) := by
  intro v hv x
  have hR := kpR_pos (γ := γ) hP hv x
  exact Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (hh x)
    (mul_pos (hb x) (Real.rpow_pos_of_pos hR _))) _

/-- The conjugating map `Φv = v^γ` of Lemma 7.2.4. -/
noncomputable def powMap (γ : ℝ) (v : X → ℝ) : X → ℝ := fun x => v x ^ γ

omit [Fintype X] in
theorem powMap_mapsTo (γ : ℝ) : MapsTo (powMap γ) (posCone X) (posCone X) :=
  fun _ hv x => Real.rpow_pos_of_pos (hv x) _

omit [Fintype X] in
theorem powMap_inv {γ : ℝ} (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ⁻¹ (powMap γ v) = v := by
  funext x
  exact Real.rpow_rpow_inv (hv x).le hγ

omit [Fintype X] in
theorem powMap_inv' {γ : ℝ} (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ (powMap γ⁻¹ v) = v := by
  funext x
  exact Real.rpow_inv_rpow (hv x).le hγ

omit [Fintype X] in
/-- Lemma 7.2.4 (p. 230): `Φ` is continuous on `V`; with `powMap_inv` and `powMap_inv'` it is a
homeomorphism of `V` with inverse `v ↦ v^{1/γ}`. -/
theorem continuousOn_powMap (γ : ℝ) : ContinuousOn (powMap γ) (posCone X) :=
  continuousOn_pi.2 fun x => (continuous_apply x).continuousOn.rpow_const
    fun _ hv => Or.inl (hv x).ne'

/-- The discount matrix `B(x, x') = b(x)^θP(x, x')` of Proposition 7.3.5. -/
noncomputable def ezB (b : X → ℝ) (θ : ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => b x ^ θ * P x x'

/-- Exercise 7.3.22 (p. 243), and Lemma 7.2.4 and Exercise 7.2.8 for `b ≡ β`: with `θ = γ/α`,
`Φ(Kv) = K̂(Φv)` on `V`, where `K̂v = (h + (Bv)^{1/θ})^θ`. -/
theorem powMap_ezK {P : Matrix X X ℝ} (hP : IsMarkov P) {h b : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hb : ∀ x, 0 < b x) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X) :
    powMap γ (ezK h b α γ P v) = powG (ezB b (γ / α) P) h (γ / α) (powMap γ v) := by
  classical
  have hθ : γ / α ≠ 0 := div_ne_zero hγ hα
  funext x
  have hS := hP.mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') γ) x
  have hbase : 0 ≤ h x + b x * kpR γ P v x ^ α :=
    add_nonneg (hh x) (mul_nonneg (hb x).le (Real.rpow_nonneg (kpR_pos hP hv x).le _))
  -- `(Bv^γ)(x) = b(x)^θ (Pv^γ)(x)`
  have hB : (ezB b (γ / α) P *ᵥ powMap γ v) x = b x ^ (γ / α) * (P *ᵥ fun x' => v x' ^ γ) x := by
    simp only [mulVec, dotProduct, ezB, Matrix.of_apply, powMap, mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  have hinv : (γ / α)⁻¹ = γ⁻¹ * α := by rw [inv_div, div_eq_inv_mul]
  have hBθ : (ezB b (γ / α) P *ᵥ powMap γ v) x ^ (γ / α)⁻¹ = b x * kpR γ P v x ^ α := by
    rw [hB, Real.mul_rpow (Real.rpow_nonneg (hb x).le _) hS.le,
      Real.rpow_rpow_inv (hb x).le hθ, kpR, ← Real.rpow_mul hS.le, hinv]
  simp only [powMap, ezK]
  rw [powG_apply, hBθ, ← Real.rpow_mul hbase, inv_mul_eq_div]

/-- `B` is irreducible when `b ≫ 0` and `P` is irreducible. -/
theorem irreducible_ezB {b : X → ℝ} (hb : ∀ x, 0 < b x) (θ : ℝ) {P : Matrix X X ℝ}
    [DecidableEq X] (hP : Irreducible P) : Irreducible (ezB b θ P) :=
  hP.of_pos_mul (c := fun x _ => b x ^ θ) fun x _ => Real.rpow_pos_of_pos (hb x) _

/-- **Proposition 7.3.5** (p. 243): for `h, b ≫ 0` and `P` irreducible Markov, the Epstein–Zin
Koopmans operator with state-dependent discounting is globally stable on `V = (0, ∞)^X` iff
`ρ(B)^{α/γ} < 1`. -/
theorem globallyStableOn_ezK_iff [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ}
    (hP : IsMarkov P) (hirr : Irreducible P) {h b : X → ℝ} (hh : ∀ x, 0 < h x)
    (hb : ∀ x, 0 < b x) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    GloballyStableOn (ezK h b α γ P) (posCone X) ↔ specRad (ezB b (γ / α) P) ^ (α / γ) < 1 := by
  have hθ : γ / α ≠ 0 := div_ne_zero hγ hα
  rw [globallyStableOn_iff_of_conj (powMap γ) (powMap γ⁻¹) (powMap_mapsTo γ) (powMap_mapsTo γ⁻¹)
    (fun u hu => powMap_inv' hγ hu) (fun u hu => powMap_inv hγ hu) (continuousOn_powMap γ)
    (continuousOn_powMap γ⁻¹) (ezK_mapsTo hP (fun x => (hh x).le) hb α γ)
    (fun u hu => powMap_ezK hP (fun x => (hh x).le) hb hα hγ hu),
    ← globallyStableOn_powG_iff (irreducible_ezB hb _ hirr) hh hθ, inv_div]

/-- **Proposition 7.2.3** (p. 228): for `P` irreducible Markov, `h ≫ 0` and `0 < β < 1`, the
Epstein–Zin Koopmans operator (7.14) is globally stable on `V = (0, ∞)^X`. -/
theorem globallyStableOn_ez [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) {h : X → ℝ} (hh : ∀ x, 0 < h x) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    GloballyStableOn (ezK h (fun _ => β) α γ P) (posCone X) := by
  rw [globallyStableOn_ezK_iff hP hirr hh (fun _ => hβ0) hα hγ]
  have hB : ezB (fun _ => β) (γ / α) P = β ^ (γ / α) • P := by
    ext x x'
    simp [ezB]
  rw [hB, specRad_smul_isMarkov hP (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
    div_mul_div_cancel₀ hα, div_self hγ, Real.rpow_one]
  exact hβ1

/-- Exercise 7.2.9 (p. 232): `F(t) = (1/2 + (1/2)t^{1/5})^5` has derivative
`F'(t) = (1/2)(1/2 + (1/2)t^{1/5})^4 t^{−4/5}`, which tends to `∞` as `t ↓ 0`; so `K̂` has infinite
slope at zero and is not a contraction. -/
theorem ez_deriv_tendsto_atTop :
    (∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (5 : ℝ))
      (1 / 2 * (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) * t ^ (-(4 / 5 : ℝ))) t) ∧
      Tendsto (fun t : ℝ => 1 / 2 * (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) * t ^ (-(4 / 5 : ℝ)))
        (𝓝[>] 0) atTop := by
  constructor
  · intro t ht
    have hb : 0 < 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹ := by
      have := Real.rpow_pos_of_pos ht (5 : ℝ)⁻¹; positivity
    have h1 : HasDerivAt (fun t : ℝ => 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹)
        (1 / 2 * ((5 : ℝ)⁻¹ * t ^ ((5 : ℝ)⁻¹ - 1))) t :=
      ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (1 / 2)).const_add _
    convert h1.rpow_const (p := 5) (Or.inl hb.ne') using 1
    have e1 : ((5 : ℝ)⁻¹ - 1) = -(4 / 5) := by norm_num
    have e2 : (5 : ℝ) - 1 = 4 := by norm_num
    rw [e1, e2]
    ring
  · -- the factor `(1/2 + t^{1/5}/2)^4 ≥ 1/16` and `t^{−4/5} → ∞`
    have hlim := tendsto_rpow_neg_nhdsGT_zero (y := -(4 / 5 : ℝ)) (by norm_num)
    refine tendsto_atTop_mono' _ ?_ (hlim.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 32))
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : (1 / 2 : ℝ) ≤ 1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹ := by
      have := Real.rpow_pos_of_pos ht' (5 : ℝ)⁻¹; linarith
    have h2 : (1 / 2 : ℝ) ^ (4 : ℝ) ≤ (1 / 2 + 1 / 2 * t ^ (5 : ℝ)⁻¹) ^ (4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
    have h3 : (1 / 2 : ℝ) ^ (4 : ℝ) = 1 / 16 := by norm_num
    have h4 := Real.rpow_pos_of_pos ht' (-(4 / 5 : ℝ))
    rw [h3] at h2
    nlinarith

/-- Exercise 7.3.16 (p. 239): if `P` is irreducible, Markov and monotone increasing, `c ≫ 0` is
increasing and `0 < β < 1`, then Epstein–Zin lifetime utility (7.13) is increasing in the state. -/
theorem monotone_ez_lifetimeValue [Preorder X] [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ}
    (hP : IsMarkov P) (hirr : Irreducible P) (hPm : MonotoneKernel P) {c : X → ℝ}
    (hc : ∀ x, 0 < c x) (hcm : Monotone c) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {α γ : ℝ}
    (hα : α ≠ 0) (hγ : γ ≠ 0) {v : X → ℝ} (hv : v ∈ posCone X)
    (hfix : IsFixedPt (ezK (fun x => (1 - β) * c x ^ α) (fun _ => β) α γ P) v) : Monotone v := by
  have hh : ∀ x, 0 < (1 - β) * c x ^ α := fun x =>
    mul_pos (by linarith) (Real.rpow_pos_of_pos (hc x) _)
  have hst := globallyStableOn_ez hP hirr hh hβ0 hβ1 hα hγ
  refine monotone_of_globallyStableOn hst (ezK_mapsTo hP (fun x => (hh x).le) (fun _ => hβ0) α γ)
    (v₀ := fun _ => 1) (fun _ => one_pos) (fun _ _ _ => le_rfl) (fun w hw hwm x y hxy => ?_) hv
    hfix
  have hR := monotone_kpR hγ hP hPm hw hwm hxy
  have hRx := kpR_pos (γ := γ) hP hw x
  have hRy := kpR_pos (γ := γ) hP hw y
  have hcx := hc x
  have hcy := hc y
  have hbx : 0 < (1 - β) * c x ^ α + β * kpR γ P w x ^ α := by
    have := Real.rpow_pos_of_pos hcx α; have := Real.rpow_pos_of_pos hRx α
    have : 0 < 1 - β := by linarith
    positivity
  have hby : 0 < (1 - β) * c y ^ α + β * kpR γ P w y ^ α := by
    have := Real.rpow_pos_of_pos hcy α; have := Real.rpow_pos_of_pos hRy α
    have : 0 < 1 - β := by linarith
    positivity
  simp only [ezK]
  have h1β : 0 < 1 - β := by linarith
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : c y ^ α ≤ c x ^ α := Real.rpow_le_rpow_of_nonpos hcx (hcm hxy) hneg.le
    have h2 : kpR γ P w y ^ α ≤ kpR γ P w x ^ α := Real.rpow_le_rpow_of_nonpos hRx hR hneg.le
    exact Real.rpow_le_rpow_of_nonpos hby (by nlinarith) (inv_lt_zero.2 hneg).le
  · have h1 : c x ^ α ≤ c y ^ α := Real.rpow_le_rpow hcx.le (hcm hxy) hpos.le
    have h2 : kpR γ P w x ^ α ≤ kpR γ P w y ^ α := Real.rpow_le_rpow hRx.le hR hpos.le
    exact Real.rpow_le_rpow hbx.le (by nlinarith) (inv_pos.2 hpos).le

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive decision processes

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `RDP`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.1–§8.1.3.2
(pp. 246–256).

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

namespace Miao.RecursiveUtility.SS

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

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality for recursive decision processes

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Optimality`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.3.3–§8.1.4
(pp. 257–262).

The book states Theorems 8.1.1 and 8.1.2 and defers their proofs to Chapter 9.
Both are proved here from one lemma. Call `R` *comparable* if, for feasible `σ, τ`,
`T_τ v_σ ≤ v_σ` implies `v_τ ≤ v_σ` and `v_σ ≤ T_τ v_σ` implies `v_σ ≤ v_τ`.
Global stability gives this by iterating `T_τ` from `v_σ`; boundedness gives it
by the Knaster–Tarski theorem on `[v₁, v_σ]` and `[v_σ, v₂]`. For a well-posed
comparable RDP:

* HPI improves: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_σ'`; the HPI values are
  monotone and take finitely many values, so some step repeats a value, and there
  the value is a fixed point of `T`.
* Every fixed point `v ∈ V` of `T` is `v_σ` for its greedy `σ` and dominates every
  `v_τ`, so it is `v*`: (i) of Theorem 8.1.1. Then (ii) Bellman's principle,
  (iii) existence and (iv) finite termination of HPI follow.
* Under global stability, (v): VFI from any `v_σ` converges to `v*`, squeezed
  between `T_{σ*}ᵏ v_σ` and `v*`; the OPI values satisfy `Tᵏv₀ ≤ vₖ ≤ v_{σₖ} ≤ v*`, so
  they converge to `v*`, and since there are finitely many policies, each
  suboptimal one falls short of `v*` somewhere and is eventually never greedy.

Also: the nonstationary-policy bound of §8.1.3.5, bounded RDPs with Exercises
8.1.12–8.1.13, and Proposition 8.1.3 on topologically conjugate RDPs with
Exercise 8.1.18.
-/

open Finset Matrix Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The comparison property behind Theorems 8.1.1 and 8.1.2. -/
def Comparable : Prop :=
  ∀ σ τ : X → A, R.IsFeasible σ → R.IsFeasible τ →
    (R.Tσ τ (R.vσ σ) ≤ R.vσ σ → R.vσ τ ≤ R.vσ σ) ∧ (R.vσ σ ≤ R.Tσ τ (R.vσ σ) → R.vσ σ ≤ R.vσ τ)

/-- Under global stability, `T_τ v ≤ v` with `v ∈ V` gives `v_τ ≤ v`. -/
theorem vσ_le_of_Tσ_le {R : RDP X A} (hR : R.IsGloballyStable) {τ : X → A}
    (hτ : R.IsFeasible τ) {v : X → ℝ} (hv : v ∈ R.V) (hle : R.Tσ τ v ≤ v) : R.vσ τ ≤ v := by
  have hk : ∀ k, (R.Tσ τ)^[k] v ≤ v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (R.Tσ_monotoneOn hτ ((R.Tσ_mapsTo hτ).iterate k hv) hv ih).trans hle
  intro x
  exact le_of_tendsto' (tendsto_pi_nhds.1 (tendsto_iterate_Tσ hR hτ hv) x) fun k => hk k x

/-- Under global stability, `v ≤ T_τ v` with `v ∈ V` gives `v ≤ v_τ`. -/
theorem le_vσ_of_le_Tσ {R : RDP X A} (hR : R.IsGloballyStable) {τ : X → A}
    (hτ : R.IsFeasible τ) {v : X → ℝ} (hv : v ∈ R.V) (hle : v ≤ R.Tσ τ v) : v ≤ R.vσ τ := by
  have hk : ∀ k, v ≤ (R.Tσ τ)^[k] v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hle.trans (R.Tσ_monotoneOn hτ hv ((R.Tσ_mapsTo hτ).iterate k hv) ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 (tendsto_iterate_Tσ hR hτ hv) x) fun k => hk k x

/-- A globally stable RDP is comparable. -/
theorem IsGloballyStable.comparable {R : RDP X A} (hR : R.IsGloballyStable) : R.Comparable :=
  fun _ _ hσ hτ => ⟨vσ_le_of_Tσ_le hR hτ (vσ_mem hR.wellPosed hσ),
    le_vσ_of_le_Tσ hR hτ (vσ_mem hR.wellPosed hσ)⟩

/-! ### The optimality argument -/

/-- HPI improvement: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_{σ'}`. -/
theorem vσ_le_vσ_greedy {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {σ : X → A}
    (hσ : R.IsFeasible σ) : R.vσ σ ≤ R.vσ (R.greedy (R.vσ σ)) := by
  refine (hc σ _ hσ (R.greedy_mem _)).2 ?_
  rw [R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy _)]
  calc R.vσ σ = R.Tσ σ (R.vσ σ) := (isFixedPt_vσ hw hσ).eq.symm
    _ ≤ R.T (R.vσ σ) := R.Tσ_le_T hσ _

/-- A fixed point `v ∈ V` of `T` is the value of its greedy policy. -/
theorem eq_vσ_greedy_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) {v : X → ℝ} (hv : v ∈ R.V)
    (hfix : IsFixedPt R.T v) : v = R.vσ (R.greedy v) := by
  refine eq_vσ_of_isFixedPt hw (R.greedy_mem v) hv ?_
  change R.Tσ (R.greedy v) v = v
  rw [R.Tσ_eq_T_of_isGreedy (R.isGreedy_greedy v), hfix.eq]

/-- A fixed point `v ∈ V` of `T` dominates every `v_τ`. -/
theorem vσ_le_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {v : X → ℝ}
    (hv : v ∈ R.V) (hfix : IsFixedPt R.T v) {τ : X → A} (hτ : R.IsFeasible τ) : R.vσ τ ≤ v := by
  have hv' := eq_vσ_greedy_of_isFixedPt hw hv hfix
  have h1 : R.Tσ τ (R.vσ (R.greedy v)) ≤ R.vσ (R.greedy v) := by
    rw [← hv']
    exact (R.Tσ_le_T hτ v).trans_eq hfix.eq
  rw [hv']
  exact (hc _ τ (R.greedy_mem v) hτ).1 h1

variable [DecidableEq X] [DecidableEq A]

omit [DecidableEq X] [DecidableEq A] in
/-- The HPI values are monotone. -/
theorem hpiValue_mono {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) (σ : R.Policy) :
    Monotone (R.hpiValue σ) := by
  classical
  exact
  monotone_nat_of_le_succ fun k => vσ_le_vσ_greedy hw hc (R.hpiPolicy σ k).2

omit [DecidableEq X] [DecidableEq A] in
/-- HPI terminates: some step leaves the value unchanged, since a strictly increasing sequence of
values would make the finitely many policies infinitely many. -/
theorem exists_hpiValue_succ_eq {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable)
    (σ : R.Policy) : ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k := by
  classical
  by_contra hcon
  have hne : ∀ k, R.hpiValue σ k ≠ R.hpiValue σ (k + 1) := fun k h =>
    hcon ⟨k, h.symm⟩
  have hsm : StrictMono (R.hpiValue σ) :=
    strictMono_nat_of_lt_succ fun k =>
      lt_of_le_of_ne (hpiValue_mono hw hc σ (Nat.le_succ k)) (hne k)
  have hinj : Injective (R.hpiPolicy σ) := fun i j hij => hsm.injective (by
    simp only [hpiValue, hij])
  exact not_injective_infinite_finite _ hinj

omit [DecidableEq X] [DecidableEq A] in
/-- Where HPI stops, the value is a fixed point of `T`. -/
theorem isFixedPt_T_hpiValue {R : RDP X A} (hw : R.WellPosed) {σ : R.Policy} {k : ℕ}
    (hk : R.hpiValue σ (k + 1) = R.hpiValue σ k) : IsFixedPt R.T (R.hpiValue σ k) := by
  classical
  have hg := R.isGreedy_greedy (R.hpiValue σ k)
  change R.T (R.hpiValue σ k) = R.hpiValue σ k
  rw [← R.Tσ_eq_T_of_isGreedy hg]
  have h1 : R.vσ (R.greedy (R.hpiValue σ k)) = R.hpiValue σ k := hk
  have h2 := (isFixedPt_vσ hw (R.greedy_mem (R.hpiValue σ k))).eq
  rw [h1] at h2
  exact h2

/-- `T` has a fixed point in `V` that dominates every `v_σ`, so it equals `v*`. -/
theorem vstar_spec {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar := by
  obtain ⟨k, hk⟩ := exists_hpiValue_succ_eq hw hc R.defaultPolicy
  have hfix := isFixedPt_T_hpiValue hw hk
  have hmem : R.hpiValue R.defaultPolicy k ∈ R.V := vσ_mem hw (R.hpiPolicy _ k).2
  have heq : R.vstar = R.hpiValue R.defaultPolicy k := by
    funext x
    refine le_antisymm (Finset.sup'_le _ _ fun τ _ => vσ_le_of_isFixedPt hw hc hmem hfix τ.2 x) ?_
    exact R.vσ_le_vstar (R.hpiPolicy _ k).2 x
  rw [heq]
  exact ⟨hmem, hfix⟩

/-- **Theorem 8.1.1 (i)** / **Theorem 8.1.2 (i)**, uniqueness: `v*` is the only fixed point of `T`
in `V`. -/
theorem eq_vstar_of_isFixedPt {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) {v : X → ℝ}
    (hv : v ∈ R.V) (hfix : IsFixedPt R.T v) : v = R.vstar := by
  funext x
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun τ _ => vσ_le_of_isFixedPt hw hc hv hfix τ.2 x)
  rw [eq_vσ_greedy_of_isFixedPt hw hv hfix]
  exact R.vσ_le_vstar (R.greedy_mem v) x

/-- **Theorem 8.1.1 (ii)** / **Theorem 8.1.2 (ii)**: Bellman's principle of optimality. -/
theorem principleOfOptimality {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    R.PrincipleOfOptimality := by
  obtain ⟨hmem, hfix⟩ := vstar_spec hw hc
  intro σ hσ
  constructor
  · rintro ⟨-, h⟩
    rw [R.isGreedy_iff_Tσ_eq_T _ hσ, ← h, (isFixedPt_vσ hw hσ).eq, h, hfix.eq]
  · intro hg
    refine ⟨hσ, (eq_vσ_of_isFixedPt hw hσ hmem ?_).symm⟩
    change R.Tσ σ R.vstar = R.vstar
    rw [R.Tσ_eq_T_of_isGreedy hg, hfix.eq]

/-- **Theorem 8.1.1 (iii)** / **Theorem 8.1.2 (iii)**: an optimal policy exists. -/
theorem exists_isOptimal {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) :
    ∃ σ, R.IsOptimal σ :=
  ⟨_, (principleOfOptimality hw hc _ (R.greedy_mem _)).2 (R.isGreedy_greedy _)⟩

/-- **Theorem 8.1.1 (iv)** / **Theorem 8.1.2 (iv)**: HPI returns an optimal policy in finitely many
steps: from any `σ` there is a `k` with `vₖ₊₁ = vₖ`, where Algorithm 8.1 stops, and the returned
`vₖ`-greedy policy `σₖ₊₁` is optimal. -/
theorem hpi_terminates {R : RDP X A} (hw : R.WellPosed) (hc : R.Comparable) (σ : R.Policy) :
    ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧ R.IsOptimal (R.hpiPolicy σ (k + 1)).1 := by
  obtain ⟨k, hk⟩ := exists_hpiValue_succ_eq hw hc σ
  refine ⟨k, hk, (R.hpiPolicy σ (k + 1)).2, ?_⟩
  have hmem : R.hpiValue σ k ∈ R.V := vσ_mem hw (R.hpiPolicy σ k).2
  change R.hpiValue σ (k + 1) = R.vstar
  rw [hk]
  exact eq_vstar_of_isFixedPt hw hc hmem (isFixedPt_T_hpiValue hw hk)

/-! ### Theorem 8.1.1 (v): VFI and OPI -/

/-- Value function iteration from any `v_σ` converges to `v*` under global stability. -/
theorem tendsto_iterate_T_vσ {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) : Tendsto (fun k : ℕ => R.T^[k] (R.vσ σ)) atTop (𝓝 R.vstar) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  obtain ⟨hstar, hfix⟩ := vstar_spec hw hc
  obtain ⟨σs, hσs⟩ := exists_isOptimal hw hc
  have hv := vσ_mem hw hσ
  -- lower bound `T_{σ*}ᵏ v_σ ≤ Tᵏ v_σ`, upper bound `Tᵏ v_σ ≤ v*`
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
/-- The OPI values stay in `{v ∈ V : v ≤ Tv}`, dominate the VFI values `Tᵏv₀` and lie below the
value of their greedy policy. -/
theorem opiValue_spec {R : RDP X A} (hR : R.IsGloballyStable) {m : ℕ} (hm : 1 ≤ m) {σ : X → A}
    (hσ : R.IsFeasible σ) (k : ℕ) :
    R.opiValue m σ k ∈ R.V ∧ R.opiValue m σ k ≤ R.T (R.opiValue m σ k) ∧
      R.T^[k] (R.vσ σ) ≤ R.opiValue m σ k ∧
      R.opiValue m σ k ≤ R.vσ (R.greedy (R.opiValue m σ k)) := by
  classical
  have hw := hR.wellPosed
  -- the key step: `W_m` maps `{v ∈ V : v ≤ Tv}` into itself and `Tv ≤ W_m v`
  have step : ∀ v ∈ R.V, v ≤ R.T v →
      R.opiW m v ∈ R.V ∧ R.opiW m v ≤ R.T (R.opiW m v) ∧ R.T v ≤ R.opiW m v ∧
        v ≤ R.vσ (R.greedy v) := by
    intro v hv hvT
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
    have hWmem : R.opiW m v ∈ R.V := (R.Tσ_mapsTo hg.1).iterate m hv
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨hWmem, ?_, ?_, le_vσ_of_le_Tσ hR hg.1 hv hgv⟩
    · calc R.opiW (m' + 1) v = (R.Tσ g)^[m' + 1] v := rfl
        _ ≤ (R.Tσ g)^[m' + 1 + 1] v := hmon (m' + 1)
        _ = R.Tσ g ((R.Tσ g)^[m' + 1] v) := iterate_succ_apply' _ _ _
        _ ≤ R.T ((R.Tσ g)^[m' + 1] v) := R.Tσ_le_T hg.1 _
    · rw [← R.Tσ_eq_T_of_isGreedy hg]
      exact hge m'
  have hv0 := vσ_mem hw hσ
  have hv0T : R.vσ σ ≤ R.T (R.vσ σ) :=
    ((isFixedPt_vσ hw hσ).eq.symm.le).trans (R.Tσ_le_T hσ _)
  have main : ∀ k, R.opiValue m σ k ∈ R.V ∧ R.opiValue m σ k ≤ R.T (R.opiValue m σ k) ∧
      R.T^[k] (R.vσ σ) ≤ R.opiValue m σ k := by
    intro k
    induction k with
    | zero => exact ⟨hv0, hv0T, le_rfl⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3, -⟩ := step _ h1 h2
      have e : R.opiValue m σ (k + 1) = R.opiW m (R.opiValue m σ k) :=
        iterate_succ_apply' _ _ _
      rw [e, iterate_succ_apply']
      exact ⟨g1, g2, (R.T_monotoneOn (R.T_mapsTo.iterate k hv0) h1 h3).trans g3⟩
  obtain ⟨h1, h2, h3⟩ := main k
  exact ⟨h1, h2, h3, (step _ h1 h2).2.2.2⟩

/-- **Theorem 8.1.1 (v)** (p. 257): under global stability, for every `m ≥ 1` and initial `v_σ`, the
OPI values converge to `v*`, and the greedy policies are optimal from some step on. With `m = 1`
this is value function iteration. -/
theorem opi_converges {R : RDP X A} (hR : R.IsGloballyStable) {m : ℕ} (hm : 1 ≤ m) {σ : X → A}
    (hσ : R.IsFeasible σ) :
    Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) ∧
      ∃ K, ∀ k ≥ K, R.IsOptimal (R.greedy (R.opiValue m σ k)) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  have hspec := opiValue_spec hR hm hσ
  have hup : ∀ k, R.opiValue m σ k ≤ R.vstar := fun k =>
    (hspec k).2.2.2.trans (R.vσ_le_vstar (R.greedy_mem _))
  have hconv : Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) := by
    have hlim := tendsto_iterate_T_vσ hR hσ
    rw [tendsto_pi_nhds] at hlim ⊢
    intro x
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim x) tendsto_const_nhds
      (fun k => (hspec k).2.2.1 x) (fun k => hup k x)
  refine ⟨hconv, ?_⟩
  -- each suboptimal policy falls short of `v*` at some state
  have hgap : ∀ τ : R.Policy, ∀ᶠ k in atTop,
      ¬ R.IsOptimal τ.1 → ∃ x, R.vσ τ.1 x < R.opiValue m σ k x := by
    intro τ
    by_cases hopt : R.IsOptimal τ.1
    · exact Eventually.of_forall fun _ h => absurd hopt h
    · have hlt : ∃ x, R.vσ τ.1 x < R.vstar x := by
        by_contra hcon
        exact hopt ⟨τ.2, le_antisymm (R.vσ_le_vstar τ.2) fun x => not_lt.1 fun h => hcon ⟨x, h⟩⟩
      obtain ⟨x, hx⟩ := hlt
      filter_upwards [(tendsto_pi_nhds.1 hconv x).eventually (lt_mem_nhds hx)] with k hk _
      exact ⟨x, hk⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_all.2 hgap)
  refine ⟨K, fun k hk => ?_⟩
  by_contra hnot
  obtain ⟨x, hx⟩ := hK k hk (R.greedyPolicy (R.opiValue m σ k)) hnot
  exact absurd ((hspec k).2.2.2 x) (not_le.2 hx)

/-- **Theorem 8.1.1** (p. 257): for a globally stable RDP, (i) `v*` is the unique solution of the
Bellman equation in `V`, (ii) Bellman's principle of optimality holds, (iii) an optimal policy
exists, (iv) HPI returns an optimal policy in finitely many steps, and (v) OPI converges, with
eventually optimal greedy policies. -/
theorem optimality_of_globallyStable {R : RDP X A} (hR : R.IsGloballyStable) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      R.PrincipleOfOptimality ∧ (∃ σ, R.IsOptimal σ) ∧
      (∀ σ : R.Policy, ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧
        R.IsOptimal (R.hpiPolicy σ (k + 1)).1) ∧
      ∀ m, 1 ≤ m → ∀ σ, R.IsFeasible σ → Tendsto (R.opiValue m σ) atTop (𝓝 R.vstar) ∧
        ∃ K, ∀ k ≥ K, R.IsOptimal (R.greedy (R.opiValue m σ k)) := by
  have hw := hR.wellPosed
  have hc := hR.comparable
  exact ⟨⟨(vstar_spec hw hc).1, (vstar_spec hw hc).2,
    fun v hv h => eq_vstar_of_isFixedPt hw hc hv h⟩,
    principleOfOptimality hw hc, exists_isOptimal hw hc, hpi_terminates hw hc,
    fun m hm σ hσ => opi_converges hR hm hσ⟩

/-! ### Nonstationary policies (§8.1.3.5) -/

omit [DecidableEq X] [DecidableEq A] in
/-- §8.1.3.5 (p. 259): under global stability, the finite-horizon values of any policy sequence are
eventually within `ε` of `v*` from below: `T_{σₖ} ⋯ T_{σ₁} v ≤ Tᵏv` and `Tᵏv_σ → v*`, so the
lifetime value `limsup` of a nonstationary policy is at most `v*`. -/
theorem nonstationary_le_vstar [DecidableEq X] [DecidableEq A] {R : RDP X A}
    (hR : R.IsGloballyStable) (σs : ℕ → X → A) (hσs : ∀ k, R.IsFeasible (σs k)) {σ : X → A}
    (hσ : R.IsFeasible σ) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (Nat.rec (R.vσ σ) fun j w => R.Tσ (σs j) w : ℕ → X → ℝ) k x ≤ R.vstar x + ε := by
  have hlim := tendsto_pi_nhds.1 (tendsto_iterate_T_vσ hR hσ) x
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : R.vstar x < R.vstar x + ε))]
    with k hk
  exact ((R.nonstationary_le σs hσs (vσ_mem hR.wellPosed hσ) k).2 x).trans hk.le

/-! ### Bounded RDPs (§8.1.3.6) -/

omit [DecidableEq X] [DecidableEq A] in
/-- `R` is bounded (§8.1.3.6) by `v₁ ≤ v₂` in `V` with `[v₁, v₂] ⊆ V` and (8.20):
`v₁(x) ≤ B(x, a, v₁)` and `B(x, a, v₂) ≤ v₂(x)` on `G`. -/
def IsBoundedBy (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ Set.Icc v₁ v₂ ⊆ R.V ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x ≤ R.B x a v₁ ∧ R.B x a v₂ ≤ v₂ x

omit [DecidableEq X] [DecidableEq A] in
/-- Policy operators of a bounded RDP map `[v₁, v₂]` into itself. -/
theorem Tσ_mapsTo_Icc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) : MapsTo (R.Tσ σ) (Set.Icc v₁ v₂) (Set.Icc v₁ v₂) := by
  intro v hv
  have h1 : v₁ ∈ R.V := hb.2.1 ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ R.V := hb.2.1 ⟨hb.1, le_rfl⟩
  exact ⟨fun x => (hb.2.2 x _ (hσ x)).1.trans (R.mono x _ (hσ x) v₁ h1 v (hb.2.1 hv) hv.1),
    fun x => (R.mono x _ (hσ x) v (hb.2.1 hv) v₂ h2 hv.2).trans (hb.2.2 x _ (hσ x)).2⟩

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.12 (p. 259): a bounded RDP restricts to an RDP on `[v₁, v₂]`. -/
def restrictIcc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) : RDP X A where
  Γ := R.Γ
  Γ_nonempty := R.Γ_nonempty
  V := Set.Icc v₁ v₂
  B := R.B
  mono := fun x a ha v hv w hw hvw => R.mono x a ha v (hb.2.1 hv) w (hb.2.1 hw) hvw
  consistent := fun _ hσ _ hv => R.Tσ_mapsTo_Icc hb hσ hv

omit [DecidableEq X] [DecidableEq A] in
/-- A fixed point of `T_σ` in a subinterval `[u, w] ⊆ [v₁, v₂]` with `u ≤ T_σ u` and `T_σ w ≤ w`,
by Knaster–Tarski. -/
theorem exists_fixedPt_Icc {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂) {σ : X → A}
    (hσ : R.IsFeasible σ) {u w : X → ℝ} (hu : u ∈ Set.Icc v₁ v₂) (hw : w ∈ Set.Icc v₁ v₂)
    (huw : u ≤ w) (hTu : u ≤ R.Tσ σ u) (hTw : R.Tσ σ w ≤ w) :
    ∃ z ∈ Set.Icc u w, IsFixedPt (R.Tσ σ) z := by
  have hsub : Set.Icc u w ⊆ R.V := fun z hz => hb.2.1 ⟨hu.1.trans hz.1, hz.2.trans hw.2⟩
  have hmono : MonotoneOn (R.Tσ σ) (Set.Icc u w) := (R.Tσ_monotoneOn hσ).mono hsub
  have hmaps : MapsTo (R.Tσ σ) (Set.Icc u w) (Set.Icc u w) := fun z hz =>
    ⟨hTu.trans (hmono ⟨le_rfl, huw⟩ hz hz.1), (hmono hz ⟨huw, le_rfl⟩ hz.2).trans hTw⟩
  obtain ⟨a, ha, -, -, hafix, -⟩ := knaster_tarski huw hmaps hmono
  exact ⟨a, ha, hafix⟩

omit [DecidableEq X] [DecidableEq A] in
/-- Exercise 8.1.13 (p. 259): in a well-posed bounded RDP, `v_σ ∈ [v₁, v₂]`. -/
theorem vσ_mem_Icc {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ} (hb : R.IsBoundedBy v₁ v₂)
    {σ : X → A} (hσ : R.IsFeasible σ) : R.vσ σ ∈ Set.Icc v₁ v₂ := by
  have h1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨hb.1, le_rfl⟩
  obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hσ h1 h2 hb.1
    (fun x => (hb.2.2 x _ (hσ x)).1) (fun x => (hb.2.2 x _ (hσ x)).2)
  rw [← eq_vσ_of_isFixedPt hw hσ (hb.2.1 hz) hzfix]
  exact hz

omit [DecidableEq X] [DecidableEq A] in
/-- A well-posed bounded RDP is comparable, by Knaster–Tarski on `[v₁, v_σ]` and `[v_σ, v₂]`. -/
theorem comparable_of_bounded {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ}
    (hb : R.IsBoundedBy v₁ v₂) : R.Comparable := by
  intro σ τ hσ hτ
  have hvσ := vσ_mem_Icc hw hb hσ
  have h1 : v₁ ∈ Set.Icc v₁ v₂ := ⟨le_rfl, hb.1⟩
  have h2 : v₂ ∈ Set.Icc v₁ v₂ := ⟨hb.1, le_rfl⟩
  constructor
  · intro hle
    obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hτ h1 hvσ hvσ.1
      (fun x => (hb.2.2 x _ (hτ x)).1) hle
    rw [← eq_vσ_of_isFixedPt hw hτ (hb.2.1 ⟨hz.1, hz.2.trans hvσ.2⟩) hzfix]
    exact hz.2
  · intro hle
    obtain ⟨z, hz, hzfix⟩ := R.exists_fixedPt_Icc hb hτ hvσ h2 hvσ.2 hle
      (fun x => (hb.2.2 x _ (hτ x)).2)
    rw [← eq_vσ_of_isFixedPt hw hτ (hb.2.1 ⟨hvσ.1.trans hz.1, hz.2⟩) hzfix]
    exact hz.1

/-- **Theorem 8.1.2** (p. 260): for a well-posed bounded RDP, (i) `v*` is the unique solution of the
Bellman equation in `V`, (ii) Bellman's principle of optimality holds, (iii) an optimal policy
exists and (iv) HPI returns an optimal policy in finitely many steps. -/
theorem optimality_of_bounded {R : RDP X A} (hw : R.WellPosed) {v₁ v₂ : X → ℝ}
    (hb : R.IsBoundedBy v₁ v₂) :
    (R.vstar ∈ R.V ∧ IsFixedPt R.T R.vstar ∧ ∀ v ∈ R.V, IsFixedPt R.T v → v = R.vstar) ∧
      R.PrincipleOfOptimality ∧ (∃ σ, R.IsOptimal σ) ∧
      ∀ σ : R.Policy, ∃ k, R.hpiValue σ (k + 1) = R.hpiValue σ k ∧
        R.IsOptimal (R.hpiPolicy σ (k + 1)).1 := by
  have hc := comparable_of_bounded hw hb
  exact ⟨⟨(vstar_spec hw hc).1, (vstar_spec hw hc).2,
    fun v hv h => eq_vstar_of_isFixedPt hw hc hv h⟩,
    principleOfOptimality hw hc, exists_isOptimal hw hc, hpi_terminates hw hc⟩

end RDP

/-! ### Topologically conjugate RDPs (§8.1.4) -/

/-- Exercise 8.1.18 (p. 261): if `φ` is continuous on `M` then `Φv = φ ∘ v` is continuous on
`M^X`. -/
theorem continuousOn_comp_pi {X : Type*} {M : Set ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ M) :
    ContinuousOn (fun v : X → ℝ => φ ∘ v) {v | ∀ x, v x ∈ M} :=
  continuousOn_pi.2 fun x => hφ.comp (continuous_apply x).continuousOn fun _ hv => hv x

/-- **Proposition 8.1.3** (p. 261): if `R = (Γ, M^X, B)` and `R̂ = (Γ, M̂^X, B̂)` are topologically
conjugate under a homeomorphism `φ : M → M̂` with inverse `ψ`, i.e.
`B(x, a, v) = ψ(B̂(x, a, φ ∘ v))`, then `R` is globally stable iff `R̂` is. -/
theorem RDP.isGloballyStable_iff_of_conj {X A : Type*} [Fintype X] [Fintype A] {R R' : RDP X A}
    (hΓ : R.Γ = R'.Γ) {M M' : Set ℝ} (hV : R.V = {v | ∀ x, v x ∈ M})
    (hV' : R'.V = {v | ∀ x, v x ∈ M'}) {φ ψ : ℝ → ℝ} (hφ : MapsTo φ M M') (hψ : MapsTo ψ M' M)
    (hφψ : ∀ t ∈ M', φ (ψ t) = t) (hψφ : ∀ t ∈ M, ψ (φ t) = t) (hφc : ContinuousOn φ M)
    (hψc : ContinuousOn ψ M')
    (hB : ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, R.B x a v = ψ (R'.B x a (φ ∘ v))) :
    R.IsGloballyStable ↔ R'.IsGloballyStable := by
  have hfeas : ∀ σ : X → A, R.IsFeasible σ ↔ R'.IsFeasible σ := fun σ => by
    simp only [RDP.IsFeasible, hΓ]
  have hΦ : MapsTo (fun v : X → ℝ => φ ∘ v) R.V R'.V := fun v hv => by
    rw [hV] at hv; rw [hV']; exact fun x => hφ (hv x)
  have hΨ : MapsTo (fun v : X → ℝ => ψ ∘ v) R'.V R.V := fun v hv => by
    rw [hV'] at hv; rw [hV]; exact fun x => hψ (hv x)
  have hΦΨ : ∀ v ∈ R'.V, (fun v : X → ℝ => φ ∘ v) ((fun v : X → ℝ => ψ ∘ v) v) = v :=
    fun v hv => by rw [hV'] at hv; funext x; exact hφψ _ (hv x)
  have hΨΦ : ∀ v ∈ R.V, (fun v : X → ℝ => ψ ∘ v) ((fun v : X → ℝ => φ ∘ v) v) = v :=
    fun v hv => by rw [hV] at hv; funext x; exact hψφ _ (hv x)
  have hΦc : ContinuousOn (fun v : X → ℝ => φ ∘ v) R.V := by
    rw [hV]; exact continuousOn_comp_pi hφc
  have hΨc : ContinuousOn (fun v : X → ℝ => ψ ∘ v) R'.V := by
    rw [hV']; exact continuousOn_comp_pi hψc
  have key : ∀ σ, R.IsFeasible σ →
      (GloballyStableOn (R.Tσ σ) R.V ↔ GloballyStableOn (R'.Tσ σ) R'.V) := by
    intro σ hσ
    have hσ' := (hfeas σ).1 hσ
    have hconj : ∀ v ∈ R.V, (fun v : X → ℝ => φ ∘ v) (R.Tσ σ v) =
        R'.Tσ σ ((fun v : X → ℝ => φ ∘ v) v) := by
      intro v hv
      have hmem : R'.Tσ σ (φ ∘ v) ∈ R'.V := R'.Tσ_mapsTo hσ' (hΦ hv)
      rw [hV'] at hmem
      funext x
      have e : R.Tσ σ v x = ψ (R'.Tσ σ (φ ∘ v) x) := hB x (σ x) (hσ x) v hv
      change φ (R.Tσ σ v x) = R'.Tσ σ (φ ∘ v) x
      rw [e, hφψ _ (hmem x)]
    exact globallyStableOn_iff_of_conj _ _ hΦ hΨ hΦΨ hΨΦ hΦc hΨc (R.Tσ_mapsTo hσ) hconj
  exact ⟨fun h σ hσ' => (key σ ((hfeas σ).2 hσ')).1 (h σ ((hfeas σ).2 hσ')),
    fun h σ hσ => (key σ hσ).2 (h σ ((hfeas σ).1 hσ))⟩

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of recursive decision processes

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Examples`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.1 (pp. 248–251) and
Example 8.1.14 (p. 252).

Every example is an RDP `(Γ, V, B)`; the constructions below check (8.2) and (8.3).

* Example 8.1.1: an MDP `(Γ, β, r, P)` with `B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`.
* Example 8.1.2: cake eating, `B(x, x', v) = u(x − x') + βv(x')`.
* Example 8.1.3 and Exercise 8.1.1: optimal stopping, `B(x, a, v) = e(x)` when stopping and
  `c(x) + β(Pv)(x)` when continuing; the Bellman operator is (8.5).
* Example 8.1.4 and Exercise 8.1.2: the Stokey–Lucas form (8.7) with exogenous `Z` and
  endogenous `Y` is an MDP.
* Example 8.1.5 and Exercise 8.1.3: state-dependent discounting (8.8).
* Example 8.1.6 and Exercise 8.1.4: risk-sensitive preferences (8.9), for every `θ ≠ 0`.
* Example 8.1.7 and Exercise 8.1.5: Epstein–Zin preferences (8.10) on `V = (0, ∞)^X`.
* Example 8.1.8: shortest paths, `B(x, x', v) = c(x, x') + v(x')` (and, for §8.3.5.2,
  `c(x, x') + βv(x')`); Example 8.1.14: a two-cycle of positive total cost makes it ill-posed.
* Quantile preferences (Exercise 8.3.1) and the quantile job search model (§8.2.1.4).

Kernels `P : X → A → X → ℝ` are read at a fixed action as the matrix `P_a(x, x') = P(x, a, x')`
(`kernelAt`), whose row `x` is all that `B(x, a, ·)` uses.
-/

open Finset Matrix Function Set

namespace Miao.RecursiveUtility.SS

variable {X A : Type*} [Fintype X] [Fintype A]

/-- The matrix `P_a(x, x') = P(x, a, x')` of a kernel at a fixed action `a`. -/
def kernelAt (P : X → A → X → ℝ) (a : A) : Matrix X X ℝ := Matrix.of fun x x' => P x a x'

omit [Fintype X] [Fintype A] in
theorem kernelAt_apply (P : X → A → X → ℝ) (a : A) (x x' : X) : kernelAt P a x x' = P x a x' :=
  rfl

omit [Fintype A] in
/-- A kernel whose rows are distributions is Markov at every action. -/
theorem isMarkov_kernelAt {P : X → A → X → ℝ} (h0 : ∀ x a x', 0 ≤ P x a x')
    (h1 : ∀ x a, ∑ x', P x a x' = 1) (a : A) : IsMarkov (kernelAt P a) :=
  ⟨fun x x' => h0 x a x', fun x => h1 x a⟩

/-! ### Markov decision processes (Example 8.1.1) -/

/-- A Markov decision process `M = (Γ, β, r, P)` (§5.1.1, restated from
`FiniteStates/MarkovDecisionProcesses`). -/
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

variable (M : MDP X A)

/-- `P_a` is Markov. -/
theorem isMarkov_P (a : A) : IsMarkov (kernelAt M.P a) :=
  isMarkov_kernelAt M.P_nonneg M.P_rowsum a

/-- The closed-loop matrix `P_σ(x, x') = P(x, σ(x), x')`. -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

/-- `P_σ` is Markov. -/
theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The reward under `σ`, `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- **Example 8.1.1** (p. 248), (8.4): the RDP generated by an MDP, with `V = ℝ^X` and
`B(x, a, v) = r(x, a) + β ∑ v(x')P(x, a, x')`. -/
def toRDP : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := univ
  B := fun x a v => M.r x a + M.β * ∑ x', v x' * M.P x a x'
  mono := fun x a _ _ _ _ _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hvw x') (M.P_nonneg x a x')) M.β_pos.le)
  consistent := fun _ _ _ _ => mem_univ _

theorem toRDP_B (x : X) (a : A) (v : X → ℝ) :
    M.toRDP.B x a v = M.r x a + M.β * ∑ x', v x' * M.P x a x' := rfl

/-- The policy operator of the MDP RDP is the affine map `T_σ v = r_σ + βP_σ v` (5.19). -/
theorem toRDP_Tσ (σ : X → A) (v : X → ℝ) :
    M.toRDP.Tσ σ v = affineOp (M.β • M.Pσ σ) (M.rσ σ) v := by
  funext x
  simp only [RDP.Tσ, toRDP, affineOp, Pi.add_apply, mulVec, dotProduct, Matrix.smul_apply,
    smul_eq_mul, Pσ, Matrix.of_apply, rσ, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

end MDP

/-! ### Cake eating (Example 8.1.2) -/

/-- **Example 8.1.2** (p. 248): cake eating on a finite set of sizes `size : X → ℝ`, with
`Γ(x) = {x' : x' ≤ x}`, `V = ℝ^X` and `B(x, x', v) = u(x − x') + βv(x')`, `β ≥ 0`. -/
noncomputable def cakeEating (size : X → ℝ) (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) : RDP X X where
  Γ := fun x => univ.filter fun x' => size x' ≤ size x
  Γ_nonempty := fun x => ⟨x, by simp⟩
  V := univ
  B := fun x x' v => u (size x - size x') + β * v x'
  mono := fun _ x' _ _ _ _ _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw x') hβ)
  consistent := fun _ _ _ _ => mem_univ _

/-! ### Optimal stopping (Example 8.1.3) -/

/-- **Example 8.1.3** (p. 249), (8.6), and **Exercise 8.1.1**: optimal stopping as an RDP with
actions `Bool` (`true` = stop), `Γ(x) = {stop, continue}`, `V = ℝ^X` and `B(x, a, v) = e(x)` if
stopping and `c(x) + β(Pv)(x)` if continuing, for `β ≥ 0` and `P` Markov. -/
def stopping (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) {P : Matrix X X ℝ} (hP : IsMarkov P) :
    RDP X Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun x a v => bif a then e x else c x + β * (P *ᵥ v) x
  mono := fun x a _ v _ w _ hvw => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hP.mulVec_le_mulVec hvw x) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- Example 8.1.3: the Bellman operator of the stopping RDP is (8.5),
`(Tv)(x) = max{e(x), c(x) + β(Pv)(x)}`. -/
theorem stopping_T (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) {P : Matrix X X ℝ} (hP : IsMarkov P)
    (v : X → ℝ) (x : X) : (stopping e c hβ hP).T v x = max (e x) (c x + β * (P *ᵥ v) x) := by
  refine le_antisymm (Finset.sup'_le _ _ fun a _ => ?_) (max_le ?_ ?_)
  · cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact (stopping e c hβ hP).B_le_T v (a := true) (mem_univ _)
  · exact (stopping e c hβ hP).B_le_T v (a := false) (mem_univ _)

/-! ### The Stokey–Lucas form (Example 8.1.4) -/

/-- **Exercise 8.1.2** (p. 250): the Stokey–Lucas problem (8.7), with states `(y, z)`, exogenous
`Q`-Markov `z`, actions `y' ∈ Γ(y, z)` and reward `F(y, z, y')`, is an MDP with kernel
`P((y, z), y', (y'', z')) = 1{y'' = y'} Q(z, z')`. -/
def stokeyLucas {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y] (Γ : Y × Z → Finset Y)
    (hΓ : ∀ x, (Γ x).Nonempty) (F : Y → Z → Y → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) : MDP (Y × Z) Y where
  Γ := Γ
  Γ_nonempty := hΓ
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x y' => F x.1 x.2 y'
  P := fun x y' x' => if x'.1 = y' then Q x.2 x'.2 else 0
  P_nonneg := fun x y' x' => by
    split_ifs
    · exact hQ.nonneg _ _
    · exact le_rfl
  P_rowsum := fun x y' => by
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single y' (fun b _ hb => by simp [hb]) (by simp)]
    simpa using hQ.rowsum x.2

/-- **Example 8.1.4** (p. 249): the aggregator of the Stokey–Lucas RDP is
`B((y, z), y', v) = F(y, z, y') + β ∑ v(y', z')Q(z, z')`, whose Bellman equation is (8.7). -/
theorem stokeyLucas_B {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y]
    (Γ : Y × Z → Finset Y) (hΓ : ∀ x, (Γ x).Nonempty) (F : Y → Z → Y → ℝ) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (y : Y) (z : Z) (y' : Y)
    (v : Y × Z → ℝ) :
    (stokeyLucas Γ hΓ F hβ0 hβ1 hQ).toRDP.B (y, z) y' v =
      F y z y' + β * ∑ z', v (y', z') * Q z z' := by
  simp only [MDP.toRDP_B, stokeyLucas]
  congr 2
  rw [Fintype.sum_prod_type, Finset.sum_eq_single y' (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-! ### State-dependent discounting, risk sensitivity, Epstein–Zin (Examples 8.1.5–8.1.7) -/

namespace MDP

variable (M : MDP X A)

/-- **Example 8.1.5** (p. 250), (8.8), and **Exercise 8.1.3**: state-dependent discounting,
`B(x, a, v) = r(x, a) + ∑ v(x') b(x, a, x')P(x, a, x')` with `b ≥ 0`, on `V = ℝ^X` (the discount
factor `β` of `M` is not used). -/
def withDiscount (b : X → A → X → ℝ) (hb : ∀ x a x', 0 ≤ b x a x') : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := univ
  B := fun x a v => M.r x a + ∑ x', v x' * b x a x' * M.P x a x'
  mono := fun x a _ _ _ _ _ hvw => add_le_add le_rfl (sum_le_sum fun x' _ =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hvw x') (hb x a x'))
      (M.P_nonneg x a x'))
  consistent := fun _ _ _ _ => mem_univ _

/-- **Example 8.1.6** (p. 250), (8.9), and **Exercise 8.1.4**: risk-sensitive preferences,
`B(x, a, v) = r(x, a) + (β/θ) ln ∑ exp(θv(x'))P(x, a, x')`, an RDP on `V = ℝ^X` for every
`θ ≠ 0`. -/
noncomputable def riskSensitive {θ : ℝ} (hθ : θ ≠ 0) : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := univ
  B := fun x a v => M.r x a + M.β * entR θ (kernelAt M.P a) v x
  mono := fun x a _ v _ w _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((isCertEquiv_entR hθ (M.isMarkov_P a)).mono v (mem_univ _) w (mem_univ _) hvw x)
    M.β_pos.le)
  consistent := fun _ _ _ _ => mem_univ _

/-- The risk-sensitive aggregator written out: (8.9). -/
theorem riskSensitive_B {θ : ℝ} (hθ : θ ≠ 0) (x : X) (a : A) (v : X → ℝ) :
    (M.riskSensitive hθ).B x a v =
      M.r x a + M.β / θ * Real.log (∑ x', Real.exp (θ * v x') * M.P x a x') := by
  simp only [riskSensitive, entR, mulVec_apply_eq, kernelAt_apply]
  ring

/-- **Exercise 8.3.1** (p. 275): quantile preferences, `B(x, a, v) = r(x, a) + β(R^a_τ v)(x)` with
`R^a_τ` the `τ`-quantile operator of `P_a`, an RDP on `V = ℝ^X` for `τ ∈ (0, 1]`. -/
noncomputable def quantile [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := univ
  B := fun x a v => M.r x a + M.β * quantR τ (kernelAt M.P a) v x
  mono := fun x a _ v _ w _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((isCertEquiv_quantR hτ0 hτ1 (M.isMarkov_P a)).mono v (mem_univ _) w (mem_univ _) hvw x)
    M.β_pos.le)
  consistent := fun _ _ _ _ => mem_univ _

end MDP

omit [Fintype X] in
/-- The Epstein–Zin aggregator `y ↦ (h + by^α)^{1/α}` is increasing on `(0, ∞)` for `h > 0`,
`b ≥ 0` and `α ≠ 0`. -/
theorem ezAgg_monotoneOn {h b α : ℝ} (hh : 0 < h) (hb : 0 ≤ b) (hα : α ≠ 0) :
    MonotoneOn (fun y : ℝ => (h + b * y ^ α) ^ α⁻¹) (Ioi 0) := by
  intro y hy z hz hyz
  have hy' : (0 : ℝ) < y := hy
  have hz' : (0 : ℝ) < z := hz
  have hbase : ∀ t : ℝ, 0 < t → 0 < h + b * t ^ α := fun t ht =>
    add_pos_of_pos_of_nonneg hh (mul_nonneg hb (Real.rpow_nonneg ht.le _))
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : z ^ α ≤ y ^ α := Real.rpow_le_rpow_of_nonpos hy' hyz hneg.le
    exact Real.rpow_le_rpow_of_nonpos (hbase z hz') (by nlinarith) (inv_lt_zero.2 hneg).le
  · have h1 : y ^ α ≤ z ^ α := Real.rpow_le_rpow hy'.le hyz hpos.le
    exact Real.rpow_le_rpow (hbase y hy').le (by nlinarith) (inv_pos.2 hpos).le

namespace MDP

variable (M : MDP X A)

/-- **Example 8.1.7** (p. 250), (8.10), and **Exercise 8.1.5**: Epstein–Zin preferences,
`B(x, a, v) = [r(x, a) + β(∑ v(x')^γ P(x, a, x'))^{α/γ}]^{1/α}` for `r ≫ 0` and `α, γ ≠ 0`, an RDP
on `V = (0, ∞)^X`. Here `B(x, a, ·)` is the Koopmans operator (7.14) of `P_a` with `h = r(·, a)`
and `b ≡ β`, evaluated at `x`. -/
noncomputable def epsteinZin (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := posCone X
  B := fun x a v => ezK (fun x => M.r x a) (fun _ => M.β) α γ (kernelAt M.P a) v x
  mono := fun x a _ v hv w hw hvw => ezAgg_monotoneOn (hr x a) M.β_pos.le hα
    (kpR_pos (M.isMarkov_P a) hv x) (kpR_pos (M.isMarkov_P a) hw x)
    ((isCertEquiv_kpR hγ (M.isMarkov_P a)).mono v hv w hw hvw x)
  consistent := fun σ _ _ hv x => ezK_mapsTo (M.isMarkov_P (σ x)) (fun x => (hr x (σ x)).le)
    (fun _ => M.β_pos) α γ hv x

/-- The Epstein–Zin aggregator written out: (8.10). -/
theorem epsteinZin_B (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) (x : X)
    (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    (M.epsteinZin hr hα hγ).B x a v =
      (M.r x a + M.β * (∑ x', v x' ^ γ * M.P x a x') ^ (α / γ)) ^ α⁻¹ := by
  have hpos : 0 ≤ ∑ x', v x' ^ γ * M.P x a x' :=
    sum_nonneg fun x' _ => mul_nonneg (Real.rpow_nonneg (hv x').le _) (M.P_nonneg x a x')
  simp only [epsteinZin, ezK, kpR, mulVec_apply_eq, kernelAt_apply]
  rw [← Real.rpow_mul hpos, div_eq_inv_mul]

end MDP

/-! ### Shortest paths (Example 8.1.8) -/

/-- **Example 8.1.8** (p. 251): the shortest path RDP on a graph with successor sets `O(x)`, edge
costs `c` and (for §8.3.5.2) a weight `β ≥ 0` on the cost-to-go: `Γ = O`, `V = ℝ^X` and
`B(x, x', v) = c(x, x') + βv(x')`. Example 8.1.8 itself is `β = 1`. -/
def pathRDP (O : X → Finset X) (hO : ∀ x, (O x).Nonempty) (c : X → X → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) : RDP X X where
  Γ := O
  Γ_nonempty := hO
  V := univ
  B := fun x x' v => c x x' + β * v x'
  mono := fun _ x' _ _ _ _ _ hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw x') hβ)
  consistent := fun _ _ _ _ => mem_univ _

/-- **Example 8.1.14** (p. 252): if `x ≠ y` are successors of each other and
`c(x, y) + c(y, x) ≠ 0`, the shortest path RDP is not well-posed: the policy `x ↦ y ↦ x` has no
cost-to-go. -/
theorem pathRDP_not_wellPosed (O : X → Finset X) (hO : ∀ x, (O x).Nonempty)
    (c : X → X → ℝ) {x y : X} (hxy : x ≠ y) (hy : y ∈ O x) (hx : x ∈ O y)
    (hc : c x y + c y x ≠ 0) : ¬ (pathRDP O hO c zero_le_one).WellPosed := by
  classical
  intro hw
  let σ : X → X := fun z => if z = x then y else if z = y then x else (hO z).choose
  have hσ : (pathRDP O hO c zero_le_one).IsFeasible σ := by
    intro z
    change σ z ∈ O z
    by_cases hzx : z = x
    · subst hzx
      simpa [σ] using hy
    · by_cases hzy : z = y
      · subst hzy
        simpa [σ, hzx] using hx
      · simpa [σ, hzx, hzy] using (hO z).choose_spec
  obtain ⟨v, ⟨-, hfix⟩, -⟩ := hw σ hσ
  have h1 : c x y + v y = v x := by
    have := congrFun hfix.eq x
    simpa [RDP.Tσ, pathRDP, σ] using this
  have h2 : c y x + v x = v y := by
    have := congrFun hfix.eq y
    simpa [RDP.Tσ, pathRDP, σ, Ne.symm hxy] using this
  exact hc (by linarith)

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contracting RDPs

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Contracting`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.1 (pp. 263–270) and §8.3.1
(pp. 274–276), with the contracting cases of §8.1.

`R` is contracting with modulus `β < 1` if `|B(x, a, v) − B(x, a, w)| ≤ β‖v − w‖∞` on `G`, (8.26).

* Proposition 8.2.1: `T` and every `T_σ` are contractions of modulus `β` on `V`;
  Exercise 8.2.2: contracting RDPs are continuous; Corollary 8.2.2: if `V` is closed (and
  nonempty) a contracting RDP is globally stable, so Theorem 8.1.1 applies.
* Proposition 8.2.3: if `σ` is `Tᵏv`-greedy then `‖v* − v_σ‖ ≤ 2β/(1 − β) ‖Tᵏv − Tᵏ⁻¹v‖`.
* Exercise 8.2.3: Blackwell's condition implies contraction; with `V = ℝ^X` it also gives
  boundedness by the constants `±M/(1 − β)` when `|B(x, a, 0)| ≤ M`.
* Applications of Blackwell's condition: MDPs (Exercise 8.2.1, Examples 8.1.13 and 8.1.16 with
  `v_σ = (I − βP_σ)⁻¹ r_σ`, Exercise 8.1.14), optimal stopping (Example 8.2.1, Examples 8.1.12
  and 8.1.15, Exercise 8.1.15), state-dependent discounting bounded by `b < 1` (Exercise 8.2.4),
  the Stokey–Lucas form and the optimal savings model (Exercise 8.2.5), job search with
  quantile preferences (Exercise 8.2.6), optimal default (Exercise 8.2.7), risk-sensitive
  RDPs (Proposition 8.3.1) and job search, and quantile RDPs (Exercise 8.3.1).
-/

open Finset Matrix Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- `R` is contracting with modulus `β` (8.26). The modulus is taken nonnegative. -/
def IsContracting (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V, |R.B x a v - R.B x a w| ≤ β * ‖v - w‖

/-- **Proposition 8.2.1** (p. 263), policy operators: each `T_σ` is a contraction of modulus `β`
on `V` in the supremum norm. -/
theorem IsContracting.isContractionOn_Tσ {R : RDP X A} {β : ℝ} (h : R.IsContracting β)
    {σ : X → A} (hσ : R.IsFeasible σ) : IsContractionOn (R.Tσ σ) R.V β :=
  ⟨R.Tσ_mapsTo hσ, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact h.2.2 x _ (hσ x) v hv w hw⟩

/-- **Proposition 8.2.1** (p. 263), Bellman operator: `T` is a contraction of modulus `β` on `V`,
by Lemma 2.2.2. -/
theorem IsContracting.isContractionOn_T {R : RDP X A} {β : ℝ} (h : R.IsContracting β) :
    IsContractionOn R.T R.V β :=
  ⟨R.T_mapsTo, h.1, h.2.1, fun v hv w hw => by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_sup'_sub_sup'_le (R.Γ_nonempty x) _ _).trans
      (Finset.sup'_le _ _ fun a ha => h.2.2 x a ha v hv w hw)⟩

/-- **Exercise 8.2.2** (p. 263): a contracting RDP is continuous. -/
theorem IsContracting.isContinuous {R : RDP X A} {β : ℝ} (h : R.IsContracting β) :
    R.IsContinuous := by
  intro x a ha v hv vk hvk hlim
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hlim.const_mul β)
  rw [Real.norm_eq_abs]
  exact h.2.2 x a ha _ (hvk k) v hv

/-- **Corollary 8.2.2** (p. 264): a contracting RDP with `V` closed and nonempty is globally
stable, so every conclusion of Theorem 8.1.1 holds. -/
theorem IsContracting.isGloballyStable {R : RDP X A} {β : ℝ} (h : R.IsContracting β)
    (hV : IsClosed R.V) (hne : R.V.Nonempty) : R.IsGloballyStable := by
  intro σ hσ
  have hc := h.isContractionOn_Tσ hσ
  obtain ⟨u, hu, hfix⟩ := hc.exists_fixedPt hV hne
  exact ⟨u, hu, hfix, fun v hv hv' => hc.fixedPt_unique hv hu hv' hfix,
    fun v hv => hc.tendsto_iterate_fixedPt hv hu hfix⟩

/-- **Proposition 8.2.3** (p. 264), (8.28): for a contracting RDP with `V` closed and nonempty,
`v ∈ V`, `v_k = Tᵏv` and `σ` a `v_{k+1}`-greedy policy,
`‖v* − v_σ‖ ≤ 2β/(1 − β) ‖v_{k+1} − v_k‖`. -/
theorem IsContracting.norm_vstar_sub_vσ_le [DecidableEq X] [DecidableEq A] {R : RDP X A}
    {β : ℝ} (h : R.IsContracting β) (hV : IsClosed R.V) (hne : R.V.Nonempty) {v : X → ℝ}
    (hv : v ∈ R.V) (k : ℕ) {σ : X → A} (hσ : R.IsGreedy (R.T^[k + 1] v) σ) :
    ‖R.vstar - R.vσ σ‖ ≤ 2 * β / (1 - β) * ‖R.T^[k + 1] v - R.T^[k] v‖ := by
  have hGS := h.isGloballyStable hV hne
  have hw := hGS.wellPosed
  obtain ⟨hstar, hfix⟩ := vstar_spec hw hGS.comparable
  have hT := h.isContractionOn_T
  have hσc := h.isContractionOn_Tσ hσ.1
  set vk := R.T^[k + 1] v with hvk
  set vk1 := R.T^[k] v
  have hvk1m : vk1 ∈ R.V := R.T_mapsTo.iterate k hv
  have hvkm : vk ∈ R.V := R.T_mapsTo.iterate (k + 1) hv
  have hvkT : vk = R.T vk1 := iterate_succ_apply' _ _ _
  have hvσ := vσ_mem hw hσ.1
  have hβ1 : 0 < 1 - β := by linarith [h.2.1]
  -- (8.30)
  have h1 : (1 - β) * ‖R.vstar - vk‖ ≤ β * ‖vk - vk1‖ := by
    have e1 : ‖R.vstar - vk‖ ≤ ‖R.T R.vstar - R.T vk‖ + ‖R.T vk - R.T vk1‖ := by
      rw [hfix.eq, ← hvkT]
      calc ‖R.vstar - vk‖ = ‖(R.vstar - R.T vk) + (R.T vk - vk)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e2 := hT.norm_sub_le _ hstar _ hvkm
    have e3 := hT.norm_sub_le _ hvkm _ hvk1m
    nlinarith
  -- (8.31)
  have h2 : (1 - β) * ‖vk - R.vσ σ‖ ≤ β * ‖vk - vk1‖ := by
    have hTσ : R.T vk = R.Tσ σ vk := (R.Tσ_eq_T_of_isGreedy hσ).symm
    have e1 : ‖vk - R.vσ σ‖ ≤ ‖R.T vk1 - R.T vk‖ + ‖R.Tσ σ vk - R.Tσ σ (R.vσ σ)‖ := by
      rw [← hvkT, (isFixedPt_vσ hw hσ.1).eq, ← hTσ]
      calc ‖vk - R.vσ σ‖ = ‖(vk - R.T vk) + (R.T vk - R.vσ σ)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e2 := hT.norm_sub_le _ hvk1m _ hvkm
    have e3 := hσc.norm_sub_le _ hvkm _ hvσ
    rw [norm_sub_rev vk1 vk] at e2
    nlinarith
  have h3 : ‖R.vstar - R.vσ σ‖ ≤ ‖R.vstar - vk‖ + ‖vk - R.vσ σ‖ := by
    calc ‖R.vstar - R.vσ σ‖ = ‖(R.vstar - vk) + (vk - R.vσ σ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ1]
  nlinarith

/-! ### Blackwell's condition (§8.2.1.3) -/

/-- `R` satisfies Blackwell's condition with `β ∈ [0, 1)` (p. 265): `V` is closed under adding
nonnegative constants and `B(x, a, v + λ) ≤ B(x, a, v) + βλ` for `λ ≥ 0`. -/
def SatisfiesBlackwell (β : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ (∀ v ∈ R.V, ∀ c : ℝ, 0 ≤ c → v + (fun _ => c) ∈ R.V) ∧
    ∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ c : ℝ, 0 ≤ c → R.B x a (v + fun _ => c) ≤ R.B x a v + β * c

/-- **Exercise 8.2.3** (p. 265): Blackwell's condition implies that `R` is contracting with
modulus `β`. -/
theorem SatisfiesBlackwell.isContracting {R : RDP X A} {β : ℝ} (h : R.SatisfiesBlackwell β) :
    R.IsContracting β := by
  refine ⟨h.1, h.2.1, fun x a ha v hv w hw => ?_⟩
  have key : ∀ v ∈ R.V, ∀ w ∈ R.V, R.B x a v - R.B x a w ≤ β * ‖v - w‖ := by
    intro v hv w hw
    have hle : v ≤ w + fun _ => ‖v - w‖ := fun y => by
      have := norm_le_pi_norm (v - w) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have hmem := h.2.2.1 w hw _ (norm_nonneg (v - w))
    have h1 := R.mono x a ha v hv _ hmem hle
    have h2 := h.2.2.2 x a ha w hw _ (norm_nonneg (v - w))
    linarith
  rw [abs_sub_le_iff]
  refine ⟨key v hv w hw, ?_⟩
  have := key w hw v hv
  rwa [norm_sub_rev] at this

/-- Blackwell's condition on `V = ℝ^X` with `|B(x, a, 0)| ≤ M` on `G` makes `R` bounded by the
constants `±M/(1 − β)`. -/
theorem SatisfiesBlackwell.isBoundedBy {R : RDP X A} {β : ℝ} (h : R.SatisfiesBlackwell β)
    (hV : R.V = univ) {M : ℝ} (hM : ∀ x, ∀ a ∈ R.Γ x, |R.B x a 0| ≤ M) :
    R.IsBoundedBy (fun _ => -(M / (1 - β))) (fun _ => M / (1 - β)) := by
  have hβ1 : 0 < 1 - β := by linarith [h.2.1]
  have hKM : M / (1 - β) * (1 - β) = M := div_mul_cancel₀ M hβ1.ne'
  refine ⟨fun x => ?_, by rw [hV]; exact subset_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a ha)
    have : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    linarith
  · obtain ⟨a', ha'⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a' ha')
    have hK0 : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    have e : ((fun _ : X => -(M / (1 - β))) + fun _ => M / (1 - β)) = 0 := by
      funext y
      simp
    have h1 := h.2.2.2 x a ha (fun _ => -(M / (1 - β))) (by rw [hV]; exact mem_univ _) _ hK0
    rw [e] at h1
    have h2 := (abs_le.1 (hM x a ha)).1
    nlinarith
  · obtain ⟨a', ha'⟩ := R.Γ_nonempty x
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x a' ha')
    have hK0 : 0 ≤ M / (1 - β) := div_nonneg hM0 hβ1.le
    have e : ((0 : X → ℝ) + fun _ => M / (1 - β)) = fun _ => M / (1 - β) := by
      funext y
      simp
    have h1 := h.2.2.2 x a ha 0 (by rw [hV]; exact mem_univ _) _ hK0
    rw [e] at h1
    have h2 := (abs_le.1 (hM x a ha)).2
    nlinarith

end RDP

/-! ### MDPs and optimal stopping -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The MDP RDP satisfies Blackwell's condition with equality: `B(x, a, v + λ) = B(x, a, v) + βλ`.
-/
theorem satisfiesBlackwell : M.toRDP.SatisfiesBlackwell M.β := by
  refine ⟨M.β_pos.le, M.β_lt_one, fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  simp only [toRDP_B, Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum, M.P_rowsum,
    mul_one]
  ring

/-- **Exercise 8.2.1** (p. 263): every MDP is a contracting RDP, with modulus `β`. -/
theorem isContracting : M.toRDP.IsContracting M.β := M.satisfiesBlackwell.isContracting

/-- **Example 8.1.16** (p. 253): the MDP RDP is globally stable (hence well-posed, Example 8.1.13),
so Theorem 8.1.1 applies (Example 8.1.19). -/
theorem isGloballyStable : M.toRDP.IsGloballyStable :=
  M.isContracting.isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Example 8.1.13** (p. 252): `v_σ = (I − βP_σ)⁻¹ r_σ`. -/
theorem vσ_eq [DecidableEq X] [Nonempty X] {σ : X → A} (hσ : M.toRDP.IsFeasible σ) :
    M.toRDP.vσ σ = (1 - M.β • M.Pσ σ)⁻¹ *ᵥ M.rσ σ := by
  have hρ : specRad (M.β • M.Pσ σ) < 1 := by
    rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ) M.β_pos.le]
    exact M.β_lt_one
  refine (RDP.eq_vσ_of_isFixedPt M.isGloballyStable.wellPosed hσ (mem_univ _) ?_).symm
  have := isFixedPt_affineOp_inv hρ (M.rσ σ)
  change M.toRDP.Tσ σ _ = _
  rw [M.toRDP_Tσ]
  exact this

/-- **Exercise 8.1.14** (p. 260): the MDP RDP is bounded, by `±‖r‖/(1 − β)`. -/
theorem isBoundedBy :
    M.toRDP.IsBoundedBy (fun _ => -(‖M.r‖ / (1 - M.β))) (fun _ => ‖M.r‖ / (1 - M.β)) := by
  refine M.satisfiesBlackwell.isBoundedBy rfl fun x a _ => ?_
  have h1 : M.toRDP.B x a 0 = M.r x a := by simp [toRDP_B]
  rw [h1, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm (M.r x) a).trans (norm_le_pi_norm M.r x)

end MDP

variable {X : Type*} [Fintype X]

/-- **Example 8.2.1** (p. 263): the optimal stopping RDP satisfies Blackwell's condition with
modulus `β` (adding `λ` to `v` raises the continuation value by `βλ`). -/
theorem stopping_satisfiesBlackwell (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).SatisfiesBlackwell β := by
  refine ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _, fun x a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c x + β * (P *ᵥ (v + fun _ => k)) x = c x + β * (P *ᵥ v) x + β * k
    rw [mulVec_add, hP.mulVec_const, Pi.add_apply]
    ring
  · change e x ≤ e x + β * k
    nlinarith

/-- **Example 8.2.1** (p. 263): the optimal stopping RDP is contracting with modulus `β`. -/
theorem stopping_isContracting (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).IsContracting β :=
  (stopping_satisfiesBlackwell e c hβ hβ1 hP).isContracting

/-- **Examples 8.1.12 and 8.1.15** (pp. 252–253): the optimal stopping RDP is globally stable (so
well-posed), and Theorem 8.1.1 applies (Example 8.1.18). -/
theorem stopping_isGloballyStable (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) : (stopping e c hβ hP).IsGloballyStable :=
  (stopping_isContracting e c hβ hβ1 hP).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Exercise 8.1.15** (p. 260): the optimal stopping RDP is bounded, by
`±(‖e‖ + ‖c‖)/(1 − β)`. -/
theorem stopping_isBoundedBy (e c : X → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    {P : Matrix X X ℝ} (hP : IsMarkov P) :
    (stopping e c hβ hP).IsBoundedBy (fun _ => -((‖e‖ + ‖c‖) / (1 - β)))
      (fun _ => (‖e‖ + ‖c‖) / (1 - β)) := by
  refine (stopping_satisfiesBlackwell e c hβ hβ1 hP).isBoundedBy rfl fun x a _ => ?_
  have he : |e x| ≤ ‖e‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm e x
  have hc : |c x| ≤ ‖c‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c x
  cases a
  · change |c x + β * (P *ᵥ 0) x| ≤ _
    rw [mulVec_zero, Pi.zero_apply, mul_zero, add_zero]
    linarith [norm_nonneg e]
  · change |e x| ≤ _
    linarith [norm_nonneg c]

/-! ### State-dependent discounting, Stokey–Lucas and savings -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- **Exercise 8.2.4** (p. 265): with state-dependent discounting bounded by `b < 1`, the RDP of
Example 8.1.5 satisfies Blackwell's condition with modulus `b`, so it is contracting. -/
theorem withDiscount_satisfiesBlackwell {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hβb : ∀ x a x', β x a x' ≤ b) :
    (M.withDiscount β hβ).SatisfiesBlackwell b := by
  refine ⟨hb0, hb1, fun _ _ _ _ => mem_univ _, fun x a _ v _ c hc => ?_⟩
  change M.r x a + ∑ x', (v + fun _ => c : X → ℝ) x' * β x a x' * M.P x a x' ≤
    M.r x a + ∑ x', v x' * β x a x' * M.P x a x' + b * c
  have hsum : ∑ x', c * β x a x' * M.P x a x' ≤ b * c := by
    calc ∑ x', c * β x a x' * M.P x a x' ≤ ∑ x', c * b * M.P x a x' :=
          sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hβb x a x') hc) (M.P_nonneg x a x')
      _ = b * c := by rw [← Finset.mul_sum, M.P_rowsum, mul_one, mul_comm]
  simp only [Pi.add_apply, add_mul, sum_add_distrib]
  linarith

/-- **Exercise 8.2.4** (p. 265): state-dependent discounting bounded by `b < 1` gives a contracting
RDP on `ℝ^X`. -/
theorem withDiscount_isContracting {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x') {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hβb : ∀ x a x', β x a x' ≤ b) :
    (M.withDiscount β hβ).IsContracting b :=
  (M.withDiscount_satisfiesBlackwell hβ hb0 hb1 hβb).isContracting

end MDP

/-- **Exercise 8.2.5** (p. 265): the discrete optimal savings model of §5.2.2, the Stokey–Lucas
model with wealth `w`, `Q`-Markov income `y`, savings `s ∈ Γ(w, y) = {s : s ≤ R(w + y)}` and reward
`u(w + y − s/R)`, satisfies Blackwell's condition. -/
theorem savings_satisfiesBlackwell {W Y : Type*} [Fintype W] [Fintype Y] [DecidableEq W]
    (wealth : W → ℝ) (inc : Y → ℝ) (Rr : ℝ) (u : ℝ → ℝ)
    (hΓ : ∀ x : W × Y, ((univ : Finset W).filter fun s =>
      wealth s ≤ Rr * (wealth x.1 + inc x.2)).Nonempty)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    (stokeyLucas (fun x => (univ : Finset W).filter fun s =>
      wealth s ≤ Rr * (wealth x.1 + inc x.2)) hΓ (fun w y s => u (wealth w + inc y - wealth s / Rr))
      hβ0 hβ1 hQ).toRDP.SatisfiesBlackwell β :=
  MDP.satisfiesBlackwell _

/-! ### Job search with quantile preferences (§8.2.1.4) -/

variable {W : Type*} [Fintype W]

/-- The job search RDP with quantile preferences (§8.2.1.4): `Γ(w) = {accept, reject}`, `V = ℝ^W`
and `B_τ(w, a, v) = w/(1 − β)` on accepting, `c + β(R_τ v)(w)` on rejecting, for `τ ∈ (0, 1]`. -/
noncomputable def quantileJobSearch [Nonempty W] (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {P : Matrix W W ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * quantR τ P v w
  mono := fun w a _ v _ v' _ hvv' => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((isCertEquiv_quantR hτ0 hτ1 hP).mono v (mem_univ _) v' (mem_univ _) hvv' w) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- **Exercise 8.2.6** (p. 266): the quantile job search RDP is contracting, with modulus `β`. -/
theorem quantileJobSearch_isContracting [Nonempty W] (wage : W → ℝ) (c : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β < 1) {P : Matrix W W ℝ} (hP : IsMarkov P) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ ≤ 1) : (quantileJobSearch wage c hβ hP hτ0 hτ1).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * quantR τ P (v + fun _ => k) w = c + β * quantR τ P v w + β * k
    rw [quantR_add_const hτ0 hτ1 hP, Pi.add_apply]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-- The risk-sensitive job search RDP (§8.3.1.2): `B(w, a, v) = w/(1 − β)` on accepting and
`c + (β/θ) ln ∑ exp(θv(w'))P(w, w')` on rejecting. -/
noncomputable def riskSensitiveJobSearch (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {P : Matrix W W ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * entR θ P v w
  mono := fun w a _ v _ v' _ hvv' => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((isCertEquiv_entR hθ hP).mono v (mem_univ _) v' (mem_univ _) hvv' w) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- §8.3.1.2 (p. 276): the risk-sensitive job search RDP is contracting with modulus `β`, so it
is globally stable and Theorem 8.1.1 applies. -/
theorem riskSensitiveJobSearch_isContracting (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β < 1) {P : Matrix W W ℝ} (hP : IsMarkov P) {θ : ℝ} (hθ : θ ≠ 0) :
    (riskSensitiveJobSearch wage c hβ hP hθ).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k hk => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * entR θ P (v + fun _ => k) w = c + β * entR θ P v w + β * k
    rw [entR_add_const hθ hP, Pi.add_apply]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-! ### Optimal default (§8.2.1.5) -/

variable {Y Bd : Type*} [Fintype Y] [Fintype Bd]

/-- The optimal default RDP (§8.2.1.5). States `(y, b, d)` with income index `y`, bond position
`b` and default flag `d`; actions `(b_a, d_a)`. Out of default every action is feasible; in default
only `(0, 1)`, where `b₀` is the zero bond. With `Q`-Markov income, consumption utility `u`, income
levels `inc`, bond values `bond`, price `q`, default cost `h`, reentry probability `θ ∈ [0, 1]`:
(8.32) `B((y, b, 0), (b_a, 0), v) = u(y + b − qb_a) + β ∑ v(y', b_a, 0)Q(y, y')`, and (8.33)
`B((y, b, d), (b_a, 1), v) = u(h(y)) + β[θ ∑ v(y', 0, 0)Q(y, y') + (1 − θ) ∑ v(y', 0, 1)Q(y, y')]`.
-/
noncomputable def optimalDefault (inc : Y → ℝ) (bond : Bd → ℝ) (b₀ : Bd) (q : ℝ) (u h : ℝ → ℝ)
    {β θ : ℝ} (hβ : 0 ≤ β) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    RDP (Y × Bd × Bool) (Bd × Bool) where
  Γ := fun s => bif s.2.2 then {(b₀, true)} else univ
  Γ_nonempty := fun s => ⟨(b₀, true), by rcases s with ⟨_, _, d⟩; cases d <;> simp⟩
  V := univ
  B := fun s a v => bif a.2 then
      u (h (inc s.1)) + β * (θ * ∑ y', v (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', v (y', b₀, true) * Q s.1 y')
    else u (inc s.1 + bond s.2.1 - q * bond a.1) + β * ∑ y', v (y', a.1, false) * Q s.1 y'
  mono := fun s a _ v _ w _ hvw => by
    have hs : ∀ b d, ∑ y', v (y', b, d) * Q s.1 y' ≤ ∑ y', w (y', b, d) * Q s.1 y' :=
      fun b d => sum_le_sum fun y' _ => mul_le_mul_of_nonneg_right (hvw _) (hQ.nonneg _ _)
    cases a.2
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hs _ _) hβ)
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hβ)
      · exact mul_le_mul_of_nonneg_left (hs _ _) hθ0
      · exact mul_le_mul_of_nonneg_left (hs _ _) (by linarith)
  consistent := fun _ _ _ _ => mem_univ _

/-- **Exercise 8.2.7** (p. 270): the optimal default RDP is contracting with modulus `β < 1`: it
satisfies Blackwell's condition with equality in both cases (8.32)–(8.33). -/
theorem optimalDefault_isContracting (inc : Y → ℝ) (bond : Bd → ℝ) (b₀ : Bd) (q : ℝ)
    (u h : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Q : Matrix Y Y ℝ} (hQ : IsMarkov Q) :
    (optimalDefault inc bond b₀ q u h hβ hθ0 hθ1 hQ).IsContracting β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun s a _ v _ k _ => le_of_eq ?_⟩
  have hs : ∀ b d, ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b, d) * Q s.1 y' =
      ∑ y', v (y', b, d) * Q s.1 y' + k := fun b d => by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum, hQ.rowsum, mul_one]
  rcases a with ⟨ba, da⟩
  cases da
  · change u _ + β * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', ba, false) * Q s.1 y' =
      u _ + β * ∑ y', v (y', ba, false) * Q s.1 y' + β * k
    rw [hs]
    ring
  · change u _ + β * (θ * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', (v + fun _ => k : Y × Bd × Bool → ℝ) (y', b₀, true) * Q s.1 y') =
      u _ + β * (θ * ∑ y', v (y', b₀, false) * Q s.1 y' +
        (1 - θ) * ∑ y', v (y', b₀, true) * Q s.1 y') + β * k
    rw [hs, hs]
    ring

/-! ### Risk-sensitive and quantile RDPs (§8.3.1) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- **Proposition 8.3.1** (p. 275): the risk-sensitive RDP is contracting with modulus `β`, since
the entropic certainty equivalent is constant-subadditive (with equality). -/
theorem riskSensitive_isContracting {θ : ℝ} (hθ : θ ≠ 0) :
    (M.riskSensitive hθ).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_pos.le, M.β_lt_one,
    fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  change M.r x a + M.β * entR θ (kernelAt M.P a) (v + fun _ => c) x =
    M.r x a + M.β * entR θ (kernelAt M.P a) v x + M.β * c
  rw [entR_add_const hθ (M.isMarkov_P a), Pi.add_apply]
  ring

/-- **Proposition 8.3.1** with Corollary 8.2.2: the risk-sensitive RDP is globally stable. -/
theorem riskSensitive_isGloballyStable {θ : ℝ} (hθ : θ ≠ 0) :
    (M.riskSensitive hθ).IsGloballyStable :=
  (M.riskSensitive_isContracting hθ).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- **Exercise 8.3.1** (p. 275): the quantile RDP is contracting with modulus `β`. -/
theorem quantile_isContracting [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (M.quantile hτ0 hτ1).IsContracting M.β := by
  refine RDP.SatisfiesBlackwell.isContracting ⟨M.β_pos.le, M.β_lt_one,
    fun _ _ _ _ => mem_univ _, fun x a _ v _ c _ => le_of_eq ?_⟩
  change M.r x a + M.β * quantR τ (kernelAt M.P a) (v + fun _ => c) x =
    M.r x a + M.β * quantR τ (kernelAt M.P a) v x + M.β * c
  rw [quantR_add_const hτ0 hτ1 (M.isMarkov_P a), Pi.add_apply]
  ring

/-- **Exercise 8.3.1** (p. 275): for `β < 1` the quantile RDP is globally stable. -/
theorem quantile_isGloballyStable [Nonempty X] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (M.quantile hτ0 hτ1).IsGloballyStable :=
  (M.quantile_isContracting hτ0 hτ1).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

end MDP

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Eventually contracting RDPs

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `EventuallyContracting`), namespace
renamed to `Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.2 (pp. 270–272) and
Exercise 8.1.16 (p. 260).

`R` is eventually contracting (8.34) if `|B(x, a, v) − B(x, a, w)| ≤ ∑ |v(x') − w(x')| L(x, a, x')`
for some `L ≥ 0` with `ρ(L_σ) < 1` for every feasible `σ`, where `L_σ(x, x') = L(x, σ(x), x')`.

* Proposition 8.2.4: with `V` closed (and nonempty), an eventually contracting RDP is globally
  stable, via Proposition 6.1.6 and Theorem 6.1.5.
* §8.2.2.2: the MDP with state-dependent discounting is eventually contracting when
  `ρ(L_σ) < 1` for `L(x, a, x') = β(x, a, x')P(x, a, x')`, completing the proof of
  Proposition 6.2.2: Theorem 8.1.1 applies.
* Exercise 8.2.8: optimal firm exit with state-dependent discounting, `B(x, a, v) = s` on exit and
  `π(x) + β(x)(Qv)(x)` otherwise, is globally stable when `β(x)Q(x, x') ≤ L(x, x')` with
  `ρ(L) < 1`; its Bellman equation is `v = max{s, π + βQv}`.
* Exercise 8.1.16: under the conditions of Proposition 6.2.2, state-dependent discounting gives
  a bounded RDP, with `v₂ = w*` and `v₁ = −w*` for the value function `w*` of the same problem with
  rewards `|r|`.
-/

open Finset Matrix Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The matrix `L_σ(x, x') = L(x, σ(x), x')`. -/
def Lσ (L : X → A → X → ℝ) (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => L x (σ x) x'

/-- `R` is eventually contracting (8.34) with dominating kernel `L ≥ 0`. -/
def IsEventuallyContracting (L : X → A → X → ℝ) : Prop :=
  (∀ x a x', 0 ≤ L x a x') ∧
    (∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V,
      |R.B x a v - R.B x a w| ≤ ∑ x', |v x' - w x'| * L x a x') ∧
    ∀ σ, R.IsFeasible σ → specRad (Lσ L σ) < 1

/-- **Proposition 8.2.4** (p. 271): an eventually contracting RDP with `V` closed and nonempty is
globally stable, so Theorem 8.1.1 applies. -/
theorem IsEventuallyContracting.isGloballyStable {R : RDP X A} {L : X → A → X → ℝ}
    (h : R.IsEventuallyContracting L) (hV : IsClosed R.V) (hne : R.V.Nonempty) :
    R.IsGloballyStable := by
  intro σ hσ
  rcases isEmpty_or_nonempty X with hX | hX
  · obtain ⟨u, hu⟩ := hne
    refine ⟨u, hu, Subsingleton.elim _ _, fun v _ _ => Subsingleton.elim _ _, fun v _ => ?_⟩
    have hk : ∀ k, (R.Tσ σ)^[k] v = u := fun k => Subsingleton.elim _ _
    simp only [hk]
    exact tendsto_const_nhds
  obtain ⟨u, hu, hfix, huniq, hconv⟩ := globallyStable_of_abs_sub_le hV hne (R.Tσ_mapsTo hσ)
    (fun x x' => h.1 x (σ x) x') (h.2.2 σ hσ) fun v hv w hw x => by
      refine (h.2.1 x _ (hσ x) v hv w hw).trans_eq ?_
      simp only [mulVec, dotProduct]
      exact sum_congr rfl fun _ _ => mul_comm _ _
  exact ⟨u, hu, hfix, huniq, hconv⟩

end RDP

/-! ### State-dependent discounting (§8.2.2.2) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- §8.2.2.2 (p. 272): the RDP of an MDP with state-dependent discounting is eventually
contracting with `L(x, a, x') = β(x, a, x')P(x, a, x')` whenever every `ρ(L_σ) < 1`. -/
theorem withDiscount_isEventuallyContracting {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsEventuallyContracting fun x a x' => β x a x' * M.P x a x' := by
  refine ⟨fun x a x' => mul_nonneg (hβ x a x') (M.P_nonneg x a x'), fun x a _ v _ w _ => ?_, hρ⟩
  change |M.r x a + ∑ x', v x' * β x a x' * M.P x a x' -
    (M.r x a + ∑ x', w x' * β x a x' * M.P x a x')| ≤ _
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => le_of_eq ?_)
  rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg (hβ x a x'),
    abs_of_nonneg (M.P_nonneg x a x')]
  ring

/-- **Proposition 6.2.2** via Proposition 8.2.4 (p. 272): under `ρ(L_σ) < 1` for every `σ`, the
MDP with state-dependent discounting is globally stable, so Theorem 8.1.1 applies. -/
theorem withDiscount_isGloballyStable {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsGloballyStable :=
  (M.withDiscount_isEventuallyContracting hβ hρ).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- The same MDP with rewards `|r|`. -/
def absReward : MDP X A := { M with r := fun x a => |M.r x a| }

/-- **Exercise 8.1.16** (p. 260): under the conditions of Proposition 6.2.2 the state-dependent
discounting RDP is bounded, by `v₁ = −w*` and `v₂ = w*`, where `w*` is the value function of the
problem with rewards `|r|`. -/
theorem withDiscount_isBoundedBy [DecidableEq X] [DecidableEq A] {β : X → A → X → ℝ}
    (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsBoundedBy (-(M.absReward.withDiscount β hβ).vstar)
      (M.absReward.withDiscount β hβ).vstar := by
  set Rb := M.absReward.withDiscount β hβ with hRb
  have hGS : Rb.IsGloballyStable := M.absReward.withDiscount_isGloballyStable hβ hρ
  have hw := hGS.wellPosed
  obtain ⟨-, hfix⟩ := RDP.vstar_spec hw hGS.comparable
  -- `w* ≥ 0`: it dominates `v_σ`, the limit of `T_σᵏ 0 ≥ 0`
  have hnonneg : 0 ≤ Rb.vstar := by
    obtain ⟨σ, hσ⟩ := Rb.policy_nonempty
    have hk : ∀ k, 0 ≤ (Rb.Tσ σ)^[k] 0 := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        intro x
        change 0 ≤ |M.r x (σ x)| + ∑ x', _ * β x (σ x) x' * M.P x (σ x) x'
        exact add_nonneg (abs_nonneg _) (sum_nonneg fun x' _ =>
          mul_nonneg (mul_nonneg (ih x') (hβ _ _ _)) (M.P_nonneg _ _ _))
    have hlim := RDP.tendsto_iterate_Tσ hGS hσ (mem_univ (0 : X → ℝ))
    intro x
    exact (ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hk k x).trans
      (Rb.vσ_le_vstar hσ x)
  have hB : ∀ x a, a ∈ M.Γ x → |M.r x a| + ∑ x', Rb.vstar x' * β x a x' * M.P x a x' ≤
      Rb.vstar x := fun x a ha => by
    have := Rb.B_le_T Rb.vstar (x := x) ha
    rw [hfix.eq] at this
    exact this
  have hS : ∀ x a, 0 ≤ ∑ x', Rb.vstar x' * β x a x' * M.P x a x' := fun x a =>
    sum_nonneg fun x' _ => mul_nonneg (mul_nonneg (hnonneg x') (hβ _ _ _)) (M.P_nonneg _ _ _)
  refine ⟨fun x => by
    have := hnonneg x
    simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
    linarith,
    fun _ _ => mem_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · change -Rb.vstar x ≤ M.r x a + ∑ x', (-Rb.vstar) x' * β x a x' * M.P x a x'
    have e : ∑ x', (-Rb.vstar) x' * β x a x' * M.P x a x' =
        -∑ x', Rb.vstar x' * β x a x' * M.P x a x' := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun x' _ => by simp only [Pi.neg_apply]; ring
    rw [e]
    have := hB x a ha
    have := neg_abs_le (M.r x a)
    linarith
  · change M.r x a + ∑ x', Rb.vstar x' * β x a x' * M.P x a x' ≤ Rb.vstar x
    have := hB x a ha
    have := le_abs_self (M.r x a)
    linarith

end MDP

/-! ### Optimal firm exit with state-dependent discounting (Exercise 8.2.8) -/

variable {X : Type*} [Fintype X]

/-- The firm exit RDP of Exercise 8.2.8: `Γ(x) = {exit, stay}`, `V = ℝ^X` and
`B(x, a, v) = s` on exit, `π(x) + β(x) ∑ v(x')Q(x, x')` on staying, with `β ≥ 0` and `Q` Markov.
-/
def firmExit (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ} (hQ : IsMarkov Q) :
    RDP X Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun x a v => bif a then s else π x + β x * (Q *ᵥ v) x
  mono := fun x a _ _ _ _ _ hvw => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQ.mulVec_le_mulVec hvw x) (hβ x))
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- Exercise 8.2.8 (p. 271): the Bellman equation is `v(x) = max{s, π(x) + β(x)(Qv)(x)}`. -/
theorem firmExit_T (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ}
    (hQ : IsMarkov Q) (v : X → ℝ) (x : X) :
    (firmExit s π β hβ hQ).T v x = max s (π x + β x * (Q *ᵥ v) x) := by
  refine le_antisymm (Finset.sup'_le _ _ fun a _ => ?_) (max_le ?_ ?_)
  · cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact (firmExit s π β hβ hQ).B_le_T v (a := true) (mem_univ _)
  · exact (firmExit s π β hβ hQ).B_le_T v (a := false) (mem_univ _)

/-- **Exercise 8.2.8** (p. 271): if `β(x)Q(x, x') ≤ L(x, x')` with `ρ(L) < 1`, the firm exit RDP is
eventually contracting (with `L` not depending on the action), hence globally stable. -/
theorem firmExit_isGloballyStable (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ}
    (hQ : IsMarkov Q) {L : Matrix X X ℝ} (hρ : specRad L < 1)
    (hL : ∀ x x', β x * Q x x' ≤ L x x') : (firmExit s π β hβ hQ).IsGloballyStable := by
  have hL0 : ∀ x x', 0 ≤ L x x' := fun x x' =>
    (mul_nonneg (hβ x) (hQ.nonneg x x')).trans (hL x x')
  refine RDP.IsEventuallyContracting.isGloballyStable (L := fun x _ x' => L x x')
    ⟨fun x _ x' => hL0 x x', fun x a _ v _ w _ => ?_, fun σ _ => ?_⟩ isClosed_univ
    ⟨0, mem_univ _⟩
  · cases a
    · change |π x + β x * (Q *ᵥ v) x - (π x + β x * (Q *ᵥ w) x)| ≤ _
      rw [add_sub_add_left_eq_sub, ← mul_sub, mulVec_apply_eq, mulVec_apply_eq,
        ← sum_sub_distrib, abs_mul, abs_of_nonneg (hβ x)]
      refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hβ x)).trans ?_
      rw [Finset.mul_sum]
      refine sum_le_sum fun x' _ => ?_
      change β x * |v x' * Q x x' - w x' * Q x x'| ≤ |v x' - w x'| * L x x'
      rw [← sub_mul, abs_mul, abs_of_nonneg (hQ.nonneg x x')]
      calc β x * (|v x' - w x'| * Q x x') = |v x' - w x'| * (β x * Q x x') := by ring
        _ ≤ |v x' - w x'| * L x x' := mul_le_mul_of_nonneg_left (hL x x') (abs_nonneg _)
    · change |s - s| ≤ _
      rw [sub_self, abs_zero]
      exact sum_nonneg fun x' _ => mul_nonneg (abs_nonneg _) (hL0 x x')
  · have : RDP.Lσ (fun x (_ : Bool) x' => L x x') σ = L := by
      ext x x'
      rfl
    rw [this]
    exact hρ

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convex and concave RDPs

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `ConcaveRDP`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.3 (pp. 272–274).

An RDP with `V = [v₁, v₂]` is convex if each `B(x, a, ·)` is convex on `V`, (8.36), and
`B(x, a, v₂) ≤ v₂(x) − δ[v₂(x) − v₁(x)]` for some `δ > 0`, (8.37); concave if each `B(x, a, ·)` is
concave, (8.38), and `B(x, a, v₁) ≥ v₁(x) + δ[v₂(x) − v₁(x)]`, (8.39).

* Exercise 8.2.9: the strict inequalities (8.40) and (8.41) give (8.37) and (8.39).
* Proposition 8.2.5: convex and concave RDPs are globally stable, by Du's theorem applied to each
  policy operator, so Theorem 8.1.1 applies.
* §8.2.3.2, Exercises 8.2.10–8.2.11: an MDP restricted to
  `V̂ = [(r₁ − ε)/(1 − β), (r₂ + ε)/(1 − β)]` is both convex and concave.
-/

open Finset Matrix Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- `R` is a convex RDP on `[v₁, v₂]`, (8.36)–(8.37). -/
def IsConvexRDP (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ R.V = Icc v₁ v₂ ∧ (∀ x, ∀ a ∈ R.Γ x, ConvexOn ℝ (Icc v₁ v₂) (R.B x a)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ ≤ v₂ x - δ * (v₂ x - v₁ x)

/-- `R` is a concave RDP on `[v₁, v₂]`, (8.38)–(8.39). -/
def IsConcaveRDP (v₁ v₂ : X → ℝ) : Prop :=
  v₁ ≤ v₂ ∧ R.V = Icc v₁ v₂ ∧ (∀ x, ∀ a ∈ R.Γ x, ConcaveOn ℝ (Icc v₁ v₂) (R.B x a)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x + δ * (v₂ x - v₁ x) ≤ R.B x a v₁

/-- **Exercise 8.2.9** (p. 273), concave case: (8.41) `B(x, a, v₁) > v₁(x)` on `G` gives (8.39). -/
theorem exists_delta_concave {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂)
    (h : ∀ x, ∀ a ∈ R.Γ x, v₁ x < R.B x a v₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, v₁ x + δ * (v₂ x - v₁ x) ≤ R.B x a v₁ := by
  set w : X → ℝ := fun x => (R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a v₁
  have hw : ∀ x, v₁ x < w x := fun x => by
    obtain ⟨a, ha, hmin⟩ := (R.Γ x).exists_min_image (fun a => R.B x a v₁) (R.Γ_nonempty x)
    have : w x = R.B x a v₁ :=
      le_antisymm (Finset.inf'_le _ ha) (Finset.le_inf' _ _ fun b hb => hmin b hb)
    rw [this]
    exact h x a ha
  obtain ⟨δ, hδ, hle⟩ := exists_delta_of_lt h12 hw
  refine ⟨δ, hδ, fun x a ha => ?_⟩
  have h1 := hle x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
  exact h1.trans (Finset.inf'_le _ ha)

/-- **Exercise 8.2.9** (p. 273), convex case: (8.40) `B(x, a, v₂) < v₂(x)` on `G` gives (8.37). -/
theorem exists_delta_convex {v₁ v₂ : X → ℝ} (h12 : v₁ ≤ v₂)
    (h : ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ < v₂ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x a v₂ ≤ v₂ x - δ * (v₂ x - v₁ x) := by
  set w : X → ℝ := fun x => -(R.Γ x).sup' (R.Γ_nonempty x) fun a => R.B x a v₂
  have hw : ∀ x, (-v₂) x < w x := fun x => by
    obtain ⟨a, ha, hmax⟩ := (R.Γ x).exists_max_image (fun a => R.B x a v₂) (R.Γ_nonempty x)
    have : (R.Γ x).sup' (R.Γ_nonempty x) (fun a => R.B x a v₂) = R.B x a v₂ :=
      le_antisymm (Finset.sup'_le _ _ fun b hb => hmax b hb)
        (Finset.le_sup' (fun a => R.B x a v₂) ha)
    simp only [w, Pi.neg_apply, this, neg_lt_neg_iff]
    exact h x a ha
  obtain ⟨δ, hδ, hle⟩ := exists_delta_of_lt (neg_le_neg h12) hw
  refine ⟨δ, hδ, fun x a ha => ?_⟩
  have h1 := hle x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, w] at h1
  have h2 := Finset.le_sup' (fun a => R.B x a v₂) ha
  linarith

/-- Pointwise concavity of `B(x, σ(x), ·)` makes `T_σ` concave on `[v₁, v₂]`. -/
theorem concaveOn_Tσ {v₁ v₂ : X → ℝ} (hc : ∀ x, ∀ a ∈ R.Γ x, ConcaveOn ℝ (Icc v₁ v₂) (R.B x a))
    {σ : X → A} (hσ : R.IsFeasible σ) : ConcaveOn ℝ (Icc v₁ v₂) (R.Tσ σ) :=
  ⟨convex_Icc v₁ v₂, fun v hv w hw a b ha hb hab x => by
    exact (hc x (σ x) (hσ x)).2 hv hw ha hb hab⟩

/-- Pointwise convexity of `B(x, σ(x), ·)` makes `T_σ` convex on `[v₁, v₂]`. -/
theorem convexOn_Tσ {v₁ v₂ : X → ℝ} (hc : ∀ x, ∀ a ∈ R.Γ x, ConvexOn ℝ (Icc v₁ v₂) (R.B x a))
    {σ : X → A} (hσ : R.IsFeasible σ) : ConvexOn ℝ (Icc v₁ v₂) (R.Tσ σ) :=
  ⟨convex_Icc v₁ v₂, fun v hv w hw a b ha hb hab x => by
    exact (hc x (σ x) (hσ x)).2 hv hw ha hb hab⟩

/-- **Proposition 8.2.5** (p. 273), concave case: a concave RDP is globally stable. -/
theorem IsConcaveRDP.isGloballyStable {R : RDP X A} {v₁ v₂ : X → ℝ}
    (h : R.IsConcaveRDP v₁ v₂) : R.IsGloballyStable := by
  obtain ⟨h12, hV, hc, δ, hδ, hB⟩ := h
  intro σ hσ
  rw [hV]
  have hmaps : MapsTo (R.Tσ σ) (Icc v₁ v₂) (Icc v₁ v₂) := hV ▸ R.Tσ_mapsTo hσ
  have hmono : MonotoneOn (R.Tσ σ) (Icc v₁ v₂) := hV ▸ R.Tσ_monotoneOn hσ
  refine du_concave h12 hmaps hmono (R.concaveOn_Tσ hc hσ) hδ fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact hB x (σ x) (hσ x)

/-- **Proposition 8.2.5** (p. 273), convex case: a convex RDP is globally stable. -/
theorem IsConvexRDP.isGloballyStable {R : RDP X A} {v₁ v₂ : X → ℝ}
    (h : R.IsConvexRDP v₁ v₂) : R.IsGloballyStable := by
  obtain ⟨h12, hV, hc, δ, hδ, hB⟩ := h
  intro σ hσ
  rw [hV]
  have hmaps : MapsTo (R.Tσ σ) (Icc v₁ v₂) (Icc v₁ v₂) := hV ▸ R.Tσ_mapsTo hσ
  have hmono : MonotoneOn (R.Tσ σ) (Icc v₁ v₂) := hV ▸ R.Tσ_monotoneOn hσ
  refine du_convex h12 hmaps hmono (R.convexOn_Tσ hc hσ) hδ fun x => ?_
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact hB x (σ x) (hσ x)

end RDP

/-! ### Application to MDPs (§8.2.3.2) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The constant bounds (8.42): `v₁ = (r₁ − ε)/(1 − β)` and `v₂ = (r₂ + ε)/(1 − β)`. -/
theorem isBoundedBy_eps {r₁ r₂ ε : ℝ} (hr : ∀ x a, r₁ ≤ M.r x a ∧ M.r x a ≤ r₂) (hε : 0 < ε) :
    M.toRDP.IsBoundedBy (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) := by
  have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hP : ∀ x a (c : ℝ), ∑ x', c * M.P x a x' = c := fun x a c => by
    rw [← Finset.mul_sum, M.P_rowsum, mul_one]
  refine ⟨fun x => ?_, fun _ _ => mem_univ _, fun x a _ => ⟨?_, ?_⟩⟩
  · obtain ⟨a, -⟩ := M.Γ_nonempty x
    have := (hr x a).1.trans (hr x a).2
    exact div_le_div_of_nonneg_right (by linarith) hβ1.le
  · change (r₁ - ε) / (1 - M.β) ≤ M.r x a + M.β * ∑ x', (r₁ - ε) / (1 - M.β) * M.P x a x'
    rw [hP, div_le_iff₀ hβ1]
    have h1 := (hr x a).1
    have : M.β * ((r₁ - ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₁ - ε) := by field_simp
    nlinarith [M.β_pos]
  · change M.r x a + M.β * ∑ x', (r₂ + ε) / (1 - M.β) * M.P x a x' ≤ (r₂ + ε) / (1 - M.β)
    rw [hP, le_div_iff₀ hβ1]
    have h1 := (hr x a).2
    have : M.β * ((r₂ + ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₂ + ε) := by field_simp
    nlinarith [M.β_pos]

/-- The MDP aggregator is affine in `v`. -/
theorem toRDP_B_combo (x : X) (a : A) (v w : X → ℝ) {s t : ℝ} (hst : s + t = 1) :
    M.toRDP.B x a (s • v + t • w) = s • M.toRDP.B x a v + t • M.toRDP.B x a w := by
  simp only [toRDP_B, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∑ x', (s * v x' + t * w x') * M.P x a x' =
      s * ∑ x', v x' * M.P x a x' + t * ∑ x', w x' * M.P x a x' := by
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [e]
  obtain rfl : t = 1 - s := by linarith
  ring

/-- **Exercises 8.2.10–8.2.11** (p. 274): the MDP RDP restricted to `V̂` of (8.42) satisfies the
strict bounds (8.40)–(8.41) and is both convex and concave, hence globally stable. -/
theorem restrict_isConvex_isConcave {r₁ r₂ ε : ℝ} (hr : ∀ x a, r₁ ≤ M.r x a ∧ M.r x a ≤ r₂)
    (hε : 0 < ε) :
    let R := M.toRDP.restrictIcc (M.isBoundedBy_eps hr hε)
    R.IsConvexRDP (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) ∧
      R.IsConcaveRDP (fun _ => (r₁ - ε) / (1 - M.β)) (fun _ => (r₂ + ε) / (1 - M.β)) := by
  intro R
  have hb := M.isBoundedBy_eps hr hε
  have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hP : ∀ x a (c : ℝ), ∑ x', c * M.P x a x' = c := fun x a c => by
    rw [← Finset.mul_sum, M.P_rowsum, mul_one]
  have haff : ∀ x a, ConvexOn ℝ (Icc (fun _ => (r₁ - ε) / (1 - M.β))
      (fun _ => (r₂ + ε) / (1 - M.β))) (R.B x a) ∧ ConcaveOn ℝ (Icc (fun _ => (r₁ - ε) / (1 - M.β))
      (fun _ => (r₂ + ε) / (1 - M.β))) (R.B x a) := fun x a =>
    ⟨⟨convex_Icc _ _, fun v _ w _ s t _ _ hst => (M.toRDP_B_combo x a v w hst).le⟩,
      ⟨convex_Icc _ _, fun v _ w _ s t _ _ hst => (M.toRDP_B_combo x a v w hst).ge⟩⟩
  -- (8.40) and (8.41)
  have h40 : ∀ x, ∀ a ∈ R.Γ x, R.B x a (fun _ => (r₂ + ε) / (1 - M.β)) < (r₂ + ε) / (1 - M.β) :=
    fun x a _ => by
      change M.r x a + M.β * ∑ x', (r₂ + ε) / (1 - M.β) * M.P x a x' < (r₂ + ε) / (1 - M.β)
      rw [hP, lt_div_iff₀ hβ1]
      have h1 := (hr x a).2
      have : M.β * ((r₂ + ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₂ + ε) := by field_simp
      nlinarith [M.β_pos]
  have h41 : ∀ x, ∀ a ∈ R.Γ x, (r₁ - ε) / (1 - M.β) < R.B x a (fun _ => (r₁ - ε) / (1 - M.β)) :=
    fun x a _ => by
      change (r₁ - ε) / (1 - M.β) < M.r x a + M.β * ∑ x', (r₁ - ε) / (1 - M.β) * M.P x a x'
      rw [hP, div_lt_iff₀ hβ1]
      have h1 := (hr x a).1
      have : M.β * ((r₁ - ε) / (1 - M.β)) * (1 - M.β) = M.β * (r₁ - ε) := by field_simp
      nlinarith [M.β_pos]
  exact ⟨⟨hb.1, rfl, fun x a _ => (haff x a).1, R.exists_delta_convex hb.1 h40⟩,
    ⟨hb.1, rfl, fun x a _ => (haff x a).2, R.exists_delta_concave hb.1 h41⟩⟩

end MDP

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Adversarial agents, robustness and KL penalties

Copied from `FiniteStates/RecursiveDecisionProcesses` (module `Adversarial`), namespace renamed to
`Miao.RecursiveUtility.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.2–§8.3.3.3 (pp. 276–283).

The decision maker chooses `a ∈ Γ(x)`, then an adversary chooses `d ∈ D(x, a)` to minimise
`B(x, a, d, v)`, giving the Bellman equation (8.43) and the aggregator
`B̂(x, a, v) = inf_{d ∈ D(x, a)} B(x, a, d, v)` on `V = [v₁, v₂]`.

* Exercise 8.3.3: `inf (f + g) ≥ inf f + inf g` for functions bounded below.
* Proposition 8.3.2: under (a) monotonicity, (b) `v₁ + ε ≤ B(·, v₁)`, (c) `B(·, v₂) ≤ v₂` and
  (d) concavity, `(Γ, V, B̂)` is a concave RDP, hence globally stable.
* §8.3.2.2: the perturbed MDP `B(x, a, d, v) = r(x, a, d) + β ∑ v(x')P(x, a, d, x')`; Exercise
  8.3.4 (conditions (b)–(c) for `v₁ = (r₁ − ε)/(1 − β)`, `v₂ = r₂/(1 − β)`) and Lemma 8.3.3.
* §8.3.3.1: robust control (8.48) is the perturbed MDP (8.49) with the adversary choosing the
  kernel, so it is a concave RDP (Proposition 8.3.4).
* §8.3.3.2: a penalty `d(P, P̄)` in (8.50) is absorbed into the reward, `r̂ = r + βd`.
* §8.3.3.3: the variational formula (8.51) for KL divergence on a finite set, and its
  consequence: with the penalty `−(1/θ)d_KL`, `θ < 0`, the robust aggregator is the
  risk-sensitive aggregator (8.9) under the baseline kernel.
-/

open Finset Matrix Filter Topology Function Set

namespace Miao.RecursiveUtility.SS

/-- **Exercise 8.3.3** (p. 279): for `f, g` bounded below on a nonempty set,
`inf (f + g) ≥ inf f + inf g`. -/
theorem iInf_add_iInf_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddBelow (range f))
    (hg : BddBelow (range g)) : (⨅ i, f i) + ⨅ i, g i ≤ ⨅ i, (f i + g i) :=
  le_ciInf fun i => add_le_add (ciInf_le hf i) (ciInf_le hg i)

/-- `r + β inf f = inf (r + βf)` for `β ≥ 0` and `f` bounded below on a nonempty set. -/
theorem add_mul_iInf {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf : BddBelow (range f)) (r : ℝ)
    {β : ℝ} (hβ : 0 ≤ β) : r + β * ⨅ i, f i = ⨅ i, (r + β * f i) := by
  rw [Real.mul_iInf_of_nonneg hβ]
  have hg : BddBelow (range fun i => β * f i) := by
    obtain ⟨m, hm⟩ := hf
    exact ⟨β * m, by rintro _ ⟨i, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨i, rfl⟩) hβ⟩
  refine le_antisymm (le_ciInf fun i => add_le_add le_rfl (ciInf_le hg i)) ?_
  have hb : BddBelow (range fun i => r + β * f i) := by
    obtain ⟨m, hm⟩ := hg
    exact ⟨r + m, by rintro _ ⟨i, rfl⟩; exact add_le_add le_rfl (hm ⟨i, rfl⟩)⟩
  have : (⨅ i, (r + β * f i)) - r ≤ ⨅ i, β * f i := le_ciInf fun i => by
    have := ciInf_le hb i
    linarith
  linarith

/-! ### Adversarial agents (§8.3.2.1) -/

variable {X A D : Type*} [Fintype X] [Fintype A]
variable (Γ₀ : X → Finset A) (D₀ : X → A → Set D) (B₀ : X → A → D → (X → ℝ) → ℝ)

/-- The adversarial aggregator `B̂(x, a, v) = inf_{d ∈ D(x, a)} B(x, a, d, v)`. -/
noncomputable def advB (x : X) (a : A) (v : X → ℝ) : ℝ := ⨅ d : D₀ x a, B₀ x a d v

/-- Conditions (a)–(d) of §8.3.2.1 (p. 278), with `D(x, a)` nonempty on `G`. -/
structure AdvConditions (v₁ v₂ : X → ℝ) (ε : ℝ) : Prop where
  nonempty : ∀ x, ∀ a ∈ Γ₀ x, (D₀ x a).Nonempty
  mono : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, Monotone (B₀ x a d)
  eps_pos : 0 < ε
  lower : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, v₁ x + ε ≤ B₀ x a d v₁
  le : v₁ ≤ v₂
  upper : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, B₀ x a d v₂ ≤ v₂ x
  concave : ∀ x, ∀ a ∈ Γ₀ x, ∀ d ∈ D₀ x a, ConcaveOn ℝ univ (B₀ x a d)

variable {Γ₀ D₀ B₀}

namespace AdvConditions

variable {v₁ v₂ : X → ℝ} {ε : ℝ} (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε)
include h

omit [Fintype X] [Fintype A] in
/-- On `[v₁, v₂]` each `d ↦ B(x, a, d, v)` is bounded below by `v₁(x) + ε`. -/
theorem lower_mem {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) (d : D₀ x a) :
    v₁ x + ε ≤ B₀ x a d v :=
  (h.lower x a ha d d.2).trans (h.mono x a ha d d.2 hv.1)

omit [Fintype X] [Fintype A] in
theorem bddBelow {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    BddBelow (range fun d : D₀ x a => B₀ x a d v) :=
  ⟨v₁ x + ε, by rintro _ ⟨d, rfl⟩; exact h.lower_mem ha hv d⟩

omit [Fintype X] [Fintype A] in
theorem le_advB {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    v₁ x + ε ≤ advB D₀ B₀ x a v :=
  have := (h.nonempty x a ha).to_subtype
  le_ciInf fun d => h.lower_mem ha hv d

omit [Fintype X] [Fintype A] in
theorem advB_le {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) {d : D}
    (hd : d ∈ D₀ x a) : advB D₀ B₀ x a v ≤ B₀ x a d v :=
  ciInf_le (h.bddBelow ha hv) ⟨d, hd⟩

omit [Fintype X] [Fintype A] in
theorem advB_mono {x : X} {a : A} (ha : a ∈ Γ₀ x) {v w : X → ℝ} (hv : v ∈ Icc v₁ v₂)
    (hvw : v ≤ w) : advB D₀ B₀ x a v ≤ advB D₀ B₀ x a w :=
  have := (h.nonempty x a ha).to_subtype
  ciInf_mono (h.bddBelow ha hv) fun d => h.mono x a ha d d.2 hvw

omit [Fintype X] [Fintype A] in
/-- (8.44): `v₁(x) < B̂(x, a, v)` and `B̂(x, a, v) ≤ v₂(x)` on `[v₁, v₂]`. -/
theorem advB_mem {x : X} {a : A} (ha : a ∈ Γ₀ x) {v : X → ℝ} (hv : v ∈ Icc v₁ v₂) :
    advB D₀ B₀ x a v ∈ Icc (v₁ x) (v₂ x) := by
  obtain ⟨d, hd⟩ := h.nonempty x a ha
  exact ⟨by linarith [h.le_advB ha hv, h.eps_pos],
    (h.advB_le ha hv hd).trans ((h.mono x a ha d hd hv.2).trans (h.upper x a ha d hd))⟩

end AdvConditions

/-- The adversarial RDP `(Γ, [v₁, v₂], B̂)` of §8.3.2.1. -/
noncomputable def adversarialRDP (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : RDP X A where
  Γ := Γ₀
  Γ_nonempty := hΓ
  V := Icc v₁ v₂
  B := advB D₀ B₀
  mono := fun _ _ ha _ hv _ _ hvw => h.advB_mono ha hv hvw
  consistent := fun _ hσ _ hv => ⟨fun x => (h.advB_mem (hσ x) hv).1,
    fun x => (h.advB_mem (hσ x) hv).2⟩

/-- **Proposition 8.3.2** (p. 278): under (a)–(d), `(Γ, [v₁, v₂], B̂)` is a concave RDP. -/
theorem adversarialRDP_isConcaveRDP (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : (adversarialRDP hΓ h).IsConcaveRDP v₁ v₂ := by
  refine ⟨h.le, rfl, fun x a ha => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst => ?_⟩, ?_⟩
  · have := (h.nonempty x a ha).to_subtype
    have hvw : s • v + t • w ∈ Icc v₁ v₂ := convex_Icc v₁ v₂ hv hw hs ht hst
    change s • advB D₀ B₀ x a v + t • advB D₀ B₀ x a w ≤ advB D₀ B₀ x a (s • v + t • w)
    have hbs : BddBelow (range fun d : D₀ x a => s * B₀ x a d v) := by
      obtain ⟨m, hm⟩ := h.bddBelow ha hv
      exact ⟨s * m, by rintro _ ⟨d, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨d, rfl⟩) hs⟩
    have hbt : BddBelow (range fun d : D₀ x a => t * B₀ x a d w) := by
      obtain ⟨m, hm⟩ := h.bddBelow ha hw
      exact ⟨t * m, by rintro _ ⟨d, rfl⟩; exact mul_le_mul_of_nonneg_left (hm ⟨d, rfl⟩) ht⟩
    simp only [advB, smul_eq_mul]
    rw [Real.mul_iInf_of_nonneg hs, Real.mul_iInf_of_nonneg ht]
    refine (iInf_add_iInf_le hbs hbt).trans (ciInf_mono ?_ fun d => ?_)
    · obtain ⟨m, hm⟩ := hbs
      obtain ⟨m', hm'⟩ := hbt
      exact ⟨m + m', by rintro _ ⟨d, rfl⟩; exact add_le_add (hm ⟨d, rfl⟩) (hm' ⟨d, rfl⟩)⟩
    · have := (h.concave x a ha d d.2).2 (mem_univ v) (mem_univ w) hs ht hst
      simpa only [smul_eq_mul] using this
  · refine RDP.exists_delta_concave _ h.le fun x a ha => ?_
    have := h.le_advB ha ⟨le_rfl, h.le⟩
    change v₁ x < advB D₀ B₀ x a v₁
    linarith [h.eps_pos]

/-- Proposition 8.3.2 with Proposition 8.2.5: the adversarial RDP is globally stable, so
Theorem 8.1.1 applies. -/
theorem adversarialRDP_isGloballyStable (hΓ : ∀ x, (Γ₀ x).Nonempty) {v₁ v₂ : X → ℝ} {ε : ℝ}
    (h : AdvConditions Γ₀ D₀ B₀ v₁ v₂ ε) : (adversarialRDP hΓ h).IsGloballyStable :=
  (adversarialRDP_isConcaveRDP hΓ h).isGloballyStable

/-! ### The perturbed MDP (§8.3.2.2) -/

/-- The perturbed MDP of §8.3.2.2: rewards `r(x, a, d)` in `[r₁, r₂]` and kernels `P(x, a, d, ·)`
that are distributions, for the adversary's `d ∈ D(x, a)`. -/
structure PerturbedMDP (X A D : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  Dset : X → A → Set D
  Dset_nonempty : ∀ x a, (Dset x a).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → D → ℝ
  r₁ : ℝ
  r₂ : ℝ
  r_bounds : ∀ x a, ∀ d ∈ Dset x a, r₁ ≤ r x a d ∧ r x a d ≤ r₂
  P : X → A → D → X → ℝ
  P_nonneg : ∀ x a, ∀ d ∈ Dset x a, ∀ x', 0 ≤ P x a d x'
  P_rowsum : ∀ x a, ∀ d ∈ Dset x a, ∑ x', P x a d x' = 1

namespace PerturbedMDP

variable {X A D : Type*} [Fintype X] [Fintype A] (M : PerturbedMDP X A D)

/-- `B(x, a, d, v) = r(x, a, d) + β ∑ v(x')P(x, a, d, x')`, as in (8.46). -/
def Bd (x : X) (a : A) (d : D) (v : X → ℝ) : ℝ := M.r x a d + M.β * ∑ x', v x' * M.P x a d x'

/-- The constant `v₁ = (r₁ − ε)/(1 − β)` of (8.47). -/
noncomputable def v₁ (ε : ℝ) : X → ℝ := fun _ => (M.r₁ - ε) / (1 - M.β)

/-- The constant `v₂ = r₂/(1 − β)` of (8.47). -/
noncomputable def v₂ : X → ℝ := fun _ => M.r₂ / (1 - M.β)

theorem Bd_const (x : X) (a : A) {d : D} (hd : d ∈ M.Dset x a) (c : ℝ) :
    M.Bd x a d (fun _ => c) = M.r x a d + M.β * c := by
  simp only [Bd]
  rw [← Finset.mul_sum, M.P_rowsum x a d hd, mul_one]

/-- **Exercise 8.3.4** (p. 280) with conditions (a) and (d): the perturbed MDP satisfies
conditions (a)–(d) of §8.3.2.1 for `v₁, v₂` in (8.47), for any `ε > 0`. -/
theorem advConditions {ε : ℝ} (hε : 0 < ε) : AdvConditions M.Γ M.Dset M.Bd (M.v₁ ε) M.v₂ ε where
  nonempty := fun x a _ => M.Dset_nonempty x a
  mono := fun x a _ d hd v w hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (hvw x') (M.P_nonneg x a d hd x'))
    M.β_pos.le)
  eps_pos := hε
  lower := fun x a _ d hd => by
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    change (M.r₁ - ε) / (1 - M.β) + ε ≤ M.Bd x a d (fun _ => (M.r₁ - ε) / (1 - M.β))
    rw [M.Bd_const x a hd]
    have h1 := (M.r_bounds x a d hd).1
    have e : (M.r₁ - ε) / (1 - M.β) + ε = M.r₁ - ε + M.β * ((M.r₁ - ε) / (1 - M.β)) + ε := by
      field_simp
      ring
    rw [e]
    nlinarith [M.β_pos]
  le := fun x => by
    obtain ⟨a, ha⟩ := M.Γ_nonempty x
    obtain ⟨d, hd⟩ := M.Dset_nonempty x a
    have h := M.r_bounds x a d hd
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    exact div_le_div_of_nonneg_right (by linarith [h.1.trans h.2]) hβ1.le
  upper := fun x a _ d hd => by
    have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
    change M.Bd x a d (fun _ => M.r₂ / (1 - M.β)) ≤ M.r₂ / (1 - M.β)
    rw [M.Bd_const x a hd]
    have h1 := (M.r_bounds x a d hd).2
    have e : M.r₂ / (1 - M.β) = M.r₂ + M.β * (M.r₂ / (1 - M.β)) := by
      field_simp
      ring
    rw [e]
    nlinarith [M.β_pos]
  concave := fun x a _ d hd => ⟨convex_univ, fun v _ w _ s t _ _ hst => le_of_eq (by
    simp only [Bd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∑ x', (s * v x' + t * w x') * M.P x a d x' =
        s * ∑ x', v x' * M.P x a d x' + t * ∑ x', w x' * M.P x a d x' := by
      rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [e]
    obtain rfl : t = 1 - s := by linarith
    ring)⟩

/-- **Lemma 8.3.3** (p. 280): the perturbed MDP `(Γ, V, B̂)` is a concave RDP, hence globally
stable (Proposition 8.2.5) and Theorem 8.1.1 applies. -/
theorem isConcaveRDP {ε : ℝ} (hε : 0 < ε) :
    (adversarialRDP M.Γ_nonempty (M.advConditions hε)).IsConcaveRDP (M.v₁ ε) M.v₂ :=
  adversarialRDP_isConcaveRDP _ _

end PerturbedMDP

/-! ### Robust control (§8.3.3.1) -/

variable {X A : Type*} [Fintype X] [Fintype A]

/-- Robust control (8.48) as a perturbed MDP (8.49): the adversary chooses the kernel row
`p ∈ 𝒫(x, a)`, a nonempty set of distributions, and `r(x, a)` does not depend on it. -/
noncomputable def robustMDP (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) : PerturbedMDP X A (X → ℝ) where
  Γ := Γ
  Γ_nonempty := hΓ
  Dset := Pset
  Dset_nonempty := hne
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  r := fun x a _ => r x a
  r₁ := r₁
  r₂ := r₂
  r_bounds := fun x a _ _ => hr x a
  P := fun _ _ p x' => p x'
  P_nonneg := fun x a p hp x' => (hdist x a p hp).nonneg x'
  P_rowsum := fun x a p hp => (hdist x a p hp).sum_eq_one

/-- (8.48) = (8.49) (p. 281): the robust aggregator `r(x, a) + β inf_p ∑ v(x')p(x')` is the
perturbed-MDP aggregator `inf_p {r(x, a) + β ∑ v(x')p(x')}`. -/
theorem robustMDP_advB (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) (x : X) (a : A) (v : X → ℝ) :
    advB (robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist).Dset
        (robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist).Bd x a v =
      r x a + β * ⨅ p : Pset x a, ∑ x', v x' * p.1 x' := by
  have := (hne x a).to_subtype
  have hbdd : BddBelow (range fun p : Pset x a => ∑ x', v x' * p.1 x') := by
    refine ⟨-‖v‖, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hd := hdist x a p.1 p.2
    calc -‖v‖ = ∑ x', -‖v‖ * p.1 x' := by rw [← Finset.mul_sum, hd.sum_eq_one, mul_one]
      _ ≤ ∑ x', v x' * p.1 x' := sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right
          (by have := norm_le_pi_norm v x'; rw [Real.norm_eq_abs] at this
              linarith [neg_abs_le (v x')]) (hd.nonneg x')
  rw [add_mul_iInf hbdd _ hβ0.le]
  rfl

/-- **Proposition 8.3.4** (p. 281): the robust control RDP is a concave RDP on `V` of (8.47), hence
globally stable. -/
theorem robustMDP_isConcaveRDP (Γ : X → Finset A) (hΓ : ∀ x, (Γ x).Nonempty) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (r : X → A → ℝ) {r₁ r₂ : ℝ} (hr : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂)
    (Pset : X → A → Set (X → ℝ)) (hne : ∀ x a, (Pset x a).Nonempty)
    (hdist : ∀ x a, ∀ p ∈ Pset x a, IsDistribution p) {ε : ℝ} (hε : 0 < ε) :
    let M := robustMDP Γ hΓ hβ0 hβ1 r hr Pset hne hdist
    (adversarialRDP M.Γ_nonempty (M.advConditions hε)).IsConcaveRDP (M.v₁ ε) M.v₂ :=
  PerturbedMDP.isConcaveRDP _ hε

/-- `p ↦ ∑ v p` is bounded below, by `−‖v‖`, on any set of distributions. -/
theorem bddBelow_sum_mul_dist {W : Type*} [Fintype W] (Φ : Set (W → ℝ))
    (hdist : ∀ φ ∈ Φ, IsDistribution φ) (v : W → ℝ) :
    BddBelow (range fun φ : Φ => ∑ w', v w' * φ.1 w') := by
  refine ⟨-‖v‖, ?_⟩
  rintro _ ⟨φ, rfl⟩
  have hd := hdist φ.1 φ.2
  calc -‖v‖ = ∑ w', -‖v‖ * φ.1 w' := by rw [← Finset.mul_sum, hd.sum_eq_one, mul_one]
    _ ≤ ∑ w', v w' * φ.1 w' := sum_le_sum fun w' _ => mul_le_mul_of_nonneg_right
        (by have := norm_le_pi_norm v w'; rw [Real.norm_eq_abs] at this
            linarith [neg_abs_le (v w')]) (hd.nonneg w')

variable {W : Type*} [Fintype W]

/-- **Example 8.3.1** (p. 281): robust job search, the worker distrusting the wage offer
distribution and using the worst case over a nonempty set `Φ` of distributions. The continuation
value is taken as `c + β inf_{φ ∈ Φ} ∑ v φ` (printed without `c` and `β`). -/
noncomputable def robustJobSearch (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) (Φ : Set (W → ℝ))
    (hΦ : Φ.Nonempty) (hdist : ∀ φ ∈ Φ, IsDistribution φ) : RDP W Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun w a v => bif a then wage w / (1 - β) else c + β * ⨅ φ : Φ, ∑ w', v w' * φ.1 w'
  mono := fun w a _ v _ v' _ hvv' => by
    have := hΦ.to_subtype
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ciInf_mono
        (bddBelow_sum_mul_dist Φ hdist v) fun φ => sum_le_sum fun w' _ =>
          mul_le_mul_of_nonneg_right (hvv' w') ((hdist φ.1 φ.2).nonneg w')) hβ)
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- Example 8.3.1: robust job search satisfies Blackwell's condition with modulus `β < 1`, so it is
contracting and globally stable. -/
theorem robustJobSearch_isContracting (wage : W → ℝ) (c : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (Φ : Set (W → ℝ)) (hΦ : Φ.Nonempty) (hdist : ∀ φ ∈ Φ, IsDistribution φ) :
    (robustJobSearch wage c hβ Φ hΦ hdist).IsContracting β := by
  have := hΦ.to_subtype
  refine RDP.SatisfiesBlackwell.isContracting ⟨hβ, hβ1, fun _ _ _ _ => mem_univ _,
    fun w a _ v _ k _ => ?_⟩
  cases a
  · apply le_of_eq
    change c + β * ⨅ φ : Φ, ∑ w', (v + fun _ => k : W → ℝ) w' * φ.1 w' =
      c + β * (⨅ φ : Φ, ∑ w', v w' * φ.1 w') + β * k
    have e : (fun φ : Φ => ∑ w', (v + fun _ => k : W → ℝ) w' * φ.1 w') =
        fun φ => k + 1 * ∑ w', v w' * φ.1 w' := funext fun φ => by
      simp only [Pi.add_apply, add_mul, sum_add_distrib, ← Finset.mul_sum,
        (hdist φ.1 φ.2).sum_eq_one, mul_one, one_mul]
      ring
    rw [e, ← add_mul_iInf (bddBelow_sum_mul_dist Φ hdist v) k zero_le_one]
    ring
  · change wage w / (1 - β) ≤ wage w / (1 - β) + β * k
    nlinarith

/-- §8.3.3.2 (p. 282), (8.50): a penalty `d(p)` is absorbed into the reward:
`r + β inf_p {∑ v p + d(p)} = inf_p {r̂(p) + β ∑ v p}` with `r̂(p) = r + βd(p)`. -/
theorem penalty_absorbed {X ι : Type*} [Fintype X] [Nonempty ι] (p : ι → X → ℝ) (d : ι → ℝ)
    (v : X → ℝ) (hb : BddBelow (range fun i => ∑ x', v x' * p i x' + d i)) (r : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) :
    r + β * ⨅ i, (∑ x', v x' * p i x' + d i) = ⨅ i, ((r + β * d i) + β * ∑ x', v x' * p i x') := by
  rw [add_mul_iInf hb r hβ]
  exact congrArg _ (funext fun i => by ring)

/-! ### KL divergence and risk sensitivity (§8.3.3.3) -/

variable {X : Type*} [Fintype X]

/-- The Kullback–Leibler divergence `d_KL(q | p) = ∑ q(x) ln(q(x)/p(x))` (p. 282); terms with
`q(x) = 0` vanish. -/
noncomputable def klDiv (q p : X → ℝ) : ℝ := ∑ x, q x * Real.log (q x / p x)

/-- `q ≺ac p`: `q(x) = 0` whenever `p(x) = 0`. -/
def AbsCont (q p : X → ℝ) : Prop := ∀ x, p x = 0 → q x = 0

/-- The normaliser `∑ exp(h(x))p(x)` is positive for a distribution `p`. -/
theorem sum_exp_mul_pos {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    0 < ∑ x, Real.exp (h x) * p x := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < p x := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : ∑ x, p x ≤ 0 := sum_nonpos fun x _ => hcon x
    linarith [hp.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hx) (single_le_sum
    (f := fun x => Real.exp (h x) * p x) (fun y _ => mul_nonneg (Real.exp_pos _).le (hp.nonneg y))
    (mem_univ x))

/-- (8.51), upper bound: `∑ h q − d_KL(q | p) ≤ ln ∑ exp(h)p` for distributions `q ≺ac p`. -/
theorem sum_mul_sub_klDiv_le {p q : X → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hac : AbsCont q p) (h : X → ℝ) :
    ∑ x, h x * q x - klDiv q p ≤ Real.log (∑ x, Real.exp (h x) * p x) := by
  set Z := ∑ x, Real.exp (h x) * p x
  have hZ : 0 < Z := sum_exp_mul_pos hp h
  have key : ∀ x, h x * q x - q x * Real.log (q x / p x) - q x * Real.log Z ≤
      Real.exp (h x) * p x / Z - q x := by
    intro x
    rcases (hq.nonneg x).lt_or_eq with hqx | hqx
    · have hpx : 0 < p x := by
        rcases (hp.nonneg x).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (hac x h'.symm) hqx.ne'
      have ht : 0 < Real.exp (h x) * p x / (q x * Z) :=
        div_pos (mul_pos (Real.exp_pos _) hpx) (mul_pos hqx hZ)
      have hlog : Real.log (Real.exp (h x) * p x / (q x * Z)) =
          h x - Real.log (q x / p x) - Real.log Z := by
        rw [Real.log_div (mul_pos (Real.exp_pos _) hpx).ne' (mul_pos hqx hZ).ne',
          Real.log_mul (Real.exp_pos _).ne' hpx.ne', Real.log_mul hqx.ne' hZ.ne', Real.log_exp,
          Real.log_div hqx.ne' hpx.ne']
        ring
      have h1 := Real.log_le_sub_one_of_pos ht
      rw [hlog] at h1
      have h2 : q x * (Real.exp (h x) * p x / (q x * Z) - 1) = Real.exp (h x) * p x / Z - q x := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 hqx.le]
    · rw [← hqx]
      simp only [mul_zero, zero_mul, sub_zero, zero_div]
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hp.nonneg x)) hZ.le
  have hL : ∑ x, (h x * q x - q x * Real.log (q x / p x) - q x * Real.log Z) =
      ∑ x, h x * q x - klDiv q p - Real.log Z := by
    rw [sum_sub_distrib, sum_sub_distrib, ← Finset.sum_mul, hq.sum_eq_one, one_mul]
    rfl
  have hR : ∑ x, (Real.exp (h x) * p x / Z - q x) = 0 := by
    rw [sum_sub_distrib, ← Finset.sum_div, div_self hZ.ne', hq.sum_eq_one, sub_self]
  have hsum := sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset X)) => key x
  rw [hL, hR] at hsum
  linarith

/-- The maximiser in (8.51), `q*(x) = exp(h(x))p(x) / ∑ exp(h)p`. -/
noncomputable def gibbs (p h : X → ℝ) : X → ℝ :=
  fun x => Real.exp (h x) * p x / ∑ y, Real.exp (h y) * p y

theorem isDistribution_gibbs {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    IsDistribution (gibbs p h) :=
  ⟨fun x => div_nonneg (mul_nonneg (Real.exp_pos _).le (hp.nonneg x)) (sum_exp_mul_pos hp h).le,
    by unfold gibbs; rw [← Finset.sum_div, div_self (sum_exp_mul_pos hp h).ne']⟩

theorem absCont_gibbs (p h : X → ℝ) : AbsCont (gibbs p h) p := fun x hx => by
  simp [gibbs, hx]

/-- (8.51), attained: `∑ h q* − d_KL(q* | p) = ln ∑ exp(h)p`. -/
theorem sum_mul_sub_klDiv_gibbs {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    ∑ x, h x * gibbs p h x - klDiv (gibbs p h) p = Real.log (∑ x, Real.exp (h x) * p x) := by
  have hZ := sum_exp_mul_pos hp h
  set Z := ∑ x, Real.exp (h x) * p x with hZdef
  have hterm : ∀ x, gibbs p h x * Real.log (gibbs p h x / p x) =
      gibbs p h x * h x - gibbs p h x * Real.log Z := by
    intro x
    rcases (hp.nonneg x).lt_or_eq with hpx | hpx
    · have e : gibbs p h x / p x = Real.exp (h x) / Z := by
        simp only [gibbs, ← hZdef]
        field_simp
      rw [e, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
      ring
    · simp [gibbs, ← hpx]
  have hg := (isDistribution_gibbs hp h).sum_eq_one
  unfold klDiv
  simp only [hterm, sum_sub_distrib]
  rw [← Finset.sum_mul, hg, one_mul]
  have hs : ∑ x, gibbs p h x * h x = ∑ x, h x * gibbs p h x :=
    sum_congr rfl fun _ _ => mul_comm _ _
  linarith

/-- **The variational formula (8.51)** (p. 283), for distributions on a finite set:
`ln ∑ exp(h(x))p(x) = max_{q ≺ac p} {∑ h(x)q(x) − d_KL(q | p)}`. -/
theorem klDuality {p : X → ℝ} (hp : IsDistribution p) (h : X → ℝ) :
    IsGreatest {y | ∃ q, IsDistribution q ∧ AbsCont q p ∧ y = ∑ x, h x * q x - klDiv q p}
      (Real.log (∑ x, Real.exp (h x) * p x)) :=
  ⟨⟨gibbs p h, isDistribution_gibbs hp h, absCont_gibbs p h, (sum_mul_sub_klDiv_gibbs hp h).symm⟩,
    by rintro y ⟨q, hq, hac, rfl⟩; exact sum_mul_sub_klDiv_le hp hq hac h⟩

/-- §8.3.3.3 (p. 283): for `θ < 0`, with `d_θ = −(1/θ)d_KL`,
`(1/θ) ln ∑ exp(θv(x))p(x) = min_{q ≺ac p} {∑ v(x)q(x) + d_θ(q | p)}`. -/
theorem entropic_isLeast {θ : ℝ} (hθ : θ < 0) {p : X → ℝ} (hp : IsDistribution p) (v : X → ℝ) :
    IsLeast {y | ∃ q, IsDistribution q ∧ AbsCont q p ∧ y = ∑ x, v x * q x - θ⁻¹ * klDiv q p}
      (θ⁻¹ * Real.log (∑ x, Real.exp (θ * v x) * p x)) := by
  have hinv : θ⁻¹ < 0 := inv_lt_zero.2 hθ
  have hθ0 : θ ≠ 0 := hθ.ne
  have e : ∀ q : X → ℝ, θ⁻¹ * (∑ x, θ * v x * q x - klDiv q p) =
      ∑ x, v x * q x - θ⁻¹ * klDiv q p := fun q => by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun x _ => by field_simp
  refine ⟨⟨gibbs p (fun x => θ * v x), isDistribution_gibbs hp _, absCont_gibbs p _, ?_⟩, ?_⟩
  · have h0 : ∑ x, θ * v x * gibbs p (fun x => θ * v x) x - klDiv (gibbs p (fun x => θ * v x)) p =
        Real.log (∑ x, Real.exp (θ * v x) * p x) := sum_mul_sub_klDiv_gibbs hp _
    rw [← h0, e]
  · rintro y ⟨q, hq, hac, rfl⟩
    have hle : ∑ x, θ * v x * q x - klDiv q p ≤ Real.log (∑ x, Real.exp (θ * v x) * p x) :=
      sum_mul_sub_klDiv_le hp hq hac fun x => θ * v x
    rw [← e]
    exact mul_le_mul_of_nonpos_left hle hinv.le

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- §8.3.3.3 (p. 283): for `θ < 0`, the robust control aggregator (8.50) with the KL penalty
`d_θ = −(1/θ)d_KL` over all `q ≺ac P(x, a, ·)` is the risk-sensitive aggregator (8.9) under the
baseline kernel. -/
theorem riskSensitive_B_eq_robust {θ : ℝ} (hθ : θ < 0) (x : X) (a : A) (v : X → ℝ) :
    (M.riskSensitive hθ.ne).B x a v = M.r x a + M.β * sInf {y | ∃ q, IsDistribution q ∧
      AbsCont q (M.P x a) ∧ y = ∑ x', v x' * q x' - θ⁻¹ * klDiv q (M.P x a)} := by
  rw [(entropic_isLeast hθ ⟨M.P_nonneg x a, M.P_rowsum x a⟩ v).csInf_eq, riskSensitive_B]
  ring

end MDP

end Miao.RecursiveUtility.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The weighted space `C_ϕ(S)` and the Weighted Contraction Mapping Theorem

Copied from `EconomicDynamics/InfiniteHorizonDP` (modules `WNSpace` and `WNWeighted`), with the
namespace renamed to `Miao.RecursiveUtility` and every name prefixed `ku_`. Miao §7.3.2,
pp. 212–213, (7.23), Exercise 7.1 and Theorem 7.3.6, which the proof of Theorem 20.1.2 (p. 682)
applies.

* `ku_InC ϕ f`: `f ∈ C_ϕ(S)`, continuous with `|f| ≤ Bϕ`; `ku_norm ϕ f = sup |f/ϕ|`.
* `ku_exists_unique_fixedPoint`: the Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)`.
* `ku_thm_7_3_6`, `ku_thm_7_3_6_of_continuous`: the Weighted Contraction Mapping
  Theorem (monotone + weighted discounting, `T0 ∈ C_ϕ(S)`).
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [TopologicalSpace S]

/-- Miao, p. 212: `f ∈ C_ϕ(S)`: `f` is continuous and `sup_s |f(s)/ϕ(s)| < ∞`. The finiteness is
stated as a bound `|f(s)| ≤ Bϕ(s)`; for `ϕ > 0` this is the same (`ku_inC_iff`). -/
def ku_InC (ϕ : S → ℝ) (f : S → ℝ) : Prop :=
  Continuous f ∧ ∃ B, ∀ s, |f s| ≤ B * ϕ s

/-- Miao, (7.23), p. 212: the weighted sup norm `‖f‖_ϕ = sup_s |f(s)/ϕ(s)|`. -/
noncomputable def ku_norm (ϕ : S → ℝ) (f : S → ℝ) : ℝ := ⨆ s, |f s / ϕ s|

variable {ϕ : S → ℝ}

/-- Miao, p. 212: for `ϕ > 0`, the bound in `ku_InC` is `sup_s |f(s)/ϕ(s)| < ∞`. -/
theorem ku_inC_iff (hϕ : ∀ s, 0 < ϕ s) (f : S → ℝ) :
    ku_InC ϕ f ↔ Continuous f ∧ BddAbove (Set.range fun s => |f s / ϕ s|) := by
  refine and_congr_right fun _ => ⟨fun ⟨B, hB⟩ => ⟨B, ?_⟩, fun ⟨C, hC⟩ => ⟨C, fun s => ?_⟩⟩
  · rintro _ ⟨s, rfl⟩
    change |f s / ϕ s| ≤ B
    rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]
    exact hB s
  · have h : |f s / ϕ s| ≤ C := hC ⟨s, rfl⟩
    rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

theorem ku_bdd (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : ku_InC ϕ f) :
    BddAbove (Set.range fun s => |f s / ϕ s|) :=
  ((ku_inC_iff hϕ f).1 hf).2

omit [TopologicalSpace S] in
theorem ku_norm_nonneg (f : S → ℝ) : 0 ≤ ku_norm ϕ f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- On `C_ϕ(S)`, `|f(s)| ≤ ‖f‖_ϕ ϕ(s)`. -/
theorem ku_abs_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} (hf : ku_InC ϕ f) (s : S) :
    |f s| ≤ ku_norm ϕ f * ϕ s := by
  have h : |f s / ϕ s| ≤ ku_norm ϕ f := le_ciSup (ku_bdd hϕ hf) s
  rwa [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)] at h

omit [TopologicalSpace S] in
/-- `|f| ≤ Cϕ` with `C ≥ 0` gives `‖f‖_ϕ ≤ C`. -/
theorem ku_norm_le (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s, |f s| ≤ C * ϕ s) : ku_norm ϕ f ≤ C :=
  Real.iSup_le (fun s => by rw [abs_div, abs_of_pos (hϕ s), div_le_iff₀ (hϕ s)]; exact h s) hC

omit [TopologicalSpace S] in
theorem ku_norm_sub_comm (f g : S → ℝ) : ku_norm ϕ (f - g) = ku_norm ϕ (g - f) := by
  simp only [ku_norm, Pi.sub_apply]
  congr 1
  funext s
  rw [← neg_sub, neg_div, abs_neg]

theorem ku_inC_add {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) : ku_InC ϕ (f + g) := by
  obtain ⟨B, hB⟩ := hf.2
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨hf.1.add hg.1, B + C, fun s => ?_⟩
  calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
    _ ≤ B * ϕ s + C * ϕ s := add_le_add (hB s) (hC s)
    _ = (B + C) * ϕ s := by ring

theorem ku_inC_smul {f : S → ℝ} (hf : ku_InC ϕ f) (r : ℝ) : ku_InC ϕ (r • f) := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1.const_smul r, |r| * B, fun s => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB s) (abs_nonneg r)

theorem ku_inC_sub {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) : ku_InC ϕ (f - g) := by
  have h := ku_inC_add hf (ku_inC_smul hg (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

theorem ku_inC_zero : ku_InC ϕ (0 : S → ℝ) :=
  ⟨continuous_const, 0, fun _ => by simp⟩

/-- `ϕ ∈ C_ϕ(S)`, with `‖ϕ‖_ϕ ≤ 1`. -/
theorem ku_inC_self (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) : ku_InC ϕ ϕ :=
  ⟨hϕc, 1, fun s => by rw [abs_of_pos (hϕ s), one_mul]⟩

/-- **Exercise 7.1** (Miao, p. 228; the norm part of p. 212). `‖·‖_ϕ` of (7.23) is a norm on
`C_ϕ(S)`: it is nonnegative, vanishes only at `0`, is absolutely homogeneous and satisfies the
triangle inequality. -/
theorem ku_ex_7_1_norm (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g)
    (r : ℝ) :
    0 ≤ ku_norm ϕ f ∧ (ku_norm ϕ f = 0 ↔ f = 0) ∧ ku_norm ϕ (r • f) = |r| * ku_norm ϕ f ∧
      ku_norm ϕ (f + g) ≤ ku_norm ϕ f + ku_norm ϕ g := by
  refine ⟨ku_norm_nonneg f, ⟨fun h0 => funext fun s => ?_, fun h => ?_⟩, ?_, ?_⟩
  · have h := ku_abs_le hϕ hf s
    rw [h0, zero_mul] at h
    exact abs_nonpos_iff.1 h
  · subst h
    simp [ku_norm]
  · simp only [ku_norm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, abs_mul]
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · refine ku_norm_le hϕ (add_nonneg (ku_norm_nonneg f) (ku_norm_nonneg g)) fun s => ?_
    calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
      _ ≤ ku_norm ϕ f * ϕ s + ku_norm ϕ g * ϕ s :=
          add_le_add (ku_abs_le hϕ hf s) (ku_abs_le hϕ hg s)
      _ = (ku_norm ϕ f + ku_norm ϕ g) * ϕ s := by ring

/-- `f/ϕ` as a bounded continuous function, for `f ∈ C_ϕ(S)`. -/
noncomputable def ku_toBCF (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : ku_InC ϕ f) : BoundedContinuousFunction S ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => f s / ϕ s)
    (hf.1.div hϕc fun s => (hϕ s).ne') (ku_norm ϕ f)
    (fun s => by rw [Real.norm_eq_abs]; exact le_ciSup (ku_bdd hϕ hf) s)

theorem ku_toBCF_apply (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : S → ℝ}
    (hf : ku_InC ϕ f) (s : S) : ku_toBCF hϕc hϕ hf s = f s / ϕ s := rfl

/-- `h ↦ hϕ` maps bounded continuous functions into `C_ϕ(S)`. -/
theorem ku_inC_mul (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    (h : BoundedContinuousFunction S ℝ) : ku_InC ϕ fun s => h s * ϕ s := by
  refine ⟨h.continuous.mul hϕc, ‖h‖, fun s => ?_⟩
  rw [abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using h.norm_coe_le_norm s)
    (hϕ s).le

/-- `‖hϕ − h'ϕ‖_ϕ ≤ dist h h'`. -/
theorem ku_norm_mul_sub_le (hϕ : ∀ s, 0 < ϕ s) (h h' : BoundedContinuousFunction S ℝ) :
    ku_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) ≤ dist h h' := by
  refine ku_norm_le hϕ dist_nonneg fun s => ?_
  have h1 : |h s - h' s| ≤ dist h h' := by
    rw [← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist s
  simp only [Pi.sub_apply]
  rw [← sub_mul, abs_mul, abs_of_pos (hϕ s)]
  exact mul_le_mul_of_nonneg_right h1 (hϕ s).le

/-- `dist (f/ϕ) (g/ϕ) ≤ ‖f − g‖_ϕ`. -/
theorem ku_dist_toBCF_le (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f g : S → ℝ}
    (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    dist (ku_toBCF hϕc hϕ hf) (ku_toBCF hϕc hϕ hg) ≤ ku_norm ϕ (f - g) := by
  refine (BoundedContinuousFunction.dist_le (ku_norm_nonneg _)).2 fun s => ?_
  rw [Real.dist_eq, ku_toBCF_apply, ku_toBCF_apply, ← sub_div]
  exact le_ciSup (ku_bdd hϕ (ku_inC_sub hf hg)) s

/-- **Exercise 7.1** (Miao, p. 228; completeness, p. 212). `C_ϕ(S)` with `‖·‖_ϕ` is complete: a
sequence in `C_ϕ(S)` that is Cauchy for `‖·‖_ϕ` converges in `‖·‖_ϕ` to some `g ∈ C_ϕ(S)`. -/
theorem ku_ex_7_1 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {f : ℕ → S → ℝ}
    (hf : ∀ n, ku_InC ϕ (f n))
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ku_norm ϕ (f m - f n) < ε) :
    ∃ g, ku_InC ϕ g ∧ Tendsto (fun n => ku_norm ϕ (f n - g)) atTop (𝓝 0) := by
  have hc : CauchySeq fun n => ku_toBCF hϕc hϕ (hf n) :=
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hcau ε hε
      exact ⟨N, fun m hm n hn => (ku_dist_toBCF_le hϕc hϕ (hf m) (hf n)).trans_lt
        (hN m hm n hn)⟩
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨fun s => H s * ϕ s, ku_inC_mul hϕc hϕ H, ?_⟩
  refine squeeze_zero (fun n => ku_norm_nonneg _) (fun n => ?_)
    (tendsto_iff_dist_tendsto_zero.1 hH)
  have he : f n = fun s => ku_toBCF hϕc hϕ (hf n) s * ϕ s := funext fun s => by
    rw [ku_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have h := ku_norm_mul_sub_le hϕ (ku_toBCF hϕc hϕ (hf n)) H
  rwa [← he] at h

/-- The Contraction Mapping Theorem on `(C_ϕ(S), ‖·‖_ϕ)` (Miao, p. 213, as used in the proof of
Theorem 7.3.6 and on p. 216): if `T` maps `C_ϕ(S)` into itself and
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` with `0 ≤ θ < 1`, then `T` has exactly one fixed point in
`C_ϕ(S)`. -/
theorem ku_exists_unique_fixedPoint (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcon : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) :
    ∃! V, ku_InC ϕ V ∧ T V = V := by
  -- the conjugate operator on bounded continuous functions
  let T' : BoundedContinuousFunction S ℝ → BoundedContinuousFunction S ℝ := fun h =>
    ku_toBCF hϕc hϕ (hT _ (ku_inC_mul hϕc hϕ h))
  have hT' : ContractingWith ⟨θ, hθ0⟩ T' := by
    refine ⟨by exact_mod_cast hθ1, LipschitzWith.of_dist_le_mul fun h h' => ?_⟩
    calc dist (T' h) (T' h')
        ≤ ku_norm ϕ (T (fun s => h s * ϕ s) - T fun s => h' s * ϕ s) :=
          ku_dist_toBCF_le hϕc hϕ _ _
      _ ≤ θ * ku_norm ϕ ((fun s => h s * ϕ s) - fun s => h' s * ϕ s) :=
          hcon _ _ (ku_inC_mul hϕc hϕ h) (ku_inC_mul hϕc hϕ h')
      _ ≤ θ * dist h h' := mul_le_mul_of_nonneg_left (ku_norm_mul_sub_le hϕ h h') hθ0
  set h0 := ContractingWith.fixedPoint T' hT' with hh0
  have hfix : T' h0 = h0 := ContractingWith.fixedPoint_isFixedPt (f := T') hT'
  have hfixV : T (fun s => h0 s * ϕ s) = fun s => h0 s * ϕ s := funext fun s => by
    have h1 := congrArg (fun h : BoundedContinuousFunction S ℝ => h s) hfix
    simp only [T', ku_toBCF_apply] at h1
    rw [← h1, div_mul_cancel₀ _ (hϕ s).ne']
  refine ⟨fun s => h0 s * ϕ s, ⟨ku_inC_mul hϕc hϕ h0, hfixV⟩, fun W ⟨hW, hWfix⟩ => ?_⟩
  have hWe : (fun s => ku_toBCF hϕc hϕ hW s * ϕ s) = W := funext fun s => by
    rw [ku_toBCF_apply, div_mul_cancel₀ _ (hϕ s).ne']
  have hWfix' : Function.IsFixedPt T' (ku_toBCF hϕc hϕ hW) := by
    refine BoundedContinuousFunction.ext fun s => ?_
    simp only [T', ku_toBCF_apply]
    have hWe' : (fun s => W s / ϕ s * ϕ s) = W := funext fun s => div_mul_cancel₀ _ (hϕ s).ne'
    rw [hWe', hWfix]
  have hWh : ku_toBCF hϕc hϕ hW = h0 := ContractingWith.fixedPoint_unique hT' hWfix'
  rw [← hWe, hWh]

/-- Comparable weights: if `0 ≤ ψ ≤ cϕ` then `C_ψ(S) ⊆ C_ϕ(S)`. -/
theorem ku_inC_of_le {ψ : S → ℝ} {c : ℝ} (hψ : ∀ s, 0 ≤ ψ s)
    (hle : ∀ s, ψ s ≤ c * ϕ s) {f : S → ℝ} (hf : ku_InC ψ f) : ku_InC ϕ f := by
  obtain ⟨B, hB⟩ := hf.2
  refine ⟨hf.1, max B 0 * c, fun s => ?_⟩
  calc |f s| ≤ B * ψ s := hB s
    _ ≤ max B 0 * ψ s := mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ s)
    _ ≤ max B 0 * (c * ϕ s) := mul_le_mul_of_nonneg_left (hle s) (le_max_right _ _)
    _ = max B 0 * c * ϕ s := by ring



/-- Miao, proof of Theorem 7.3.6, p. 213: from (a) and (b),
`Tf ≤ Tg + θ‖f − g‖_ϕ ϕ` for `f, g ∈ C_ϕ(S)`. -/
theorem ku_le_add_of_disc (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) (s : S) :
    T f s ≤ T g s + θ * ku_norm ϕ (f - g) * ϕ s := by
  have hfg := ku_abs_le hϕ (ku_inC_sub hf hg)
  rcases (ku_norm_nonneg (ϕ := ϕ) (f - g)).eq_or_lt with h0 | hpos
  · have hle : f ≤ g := fun t => by
      have h1 := hfg t
      rw [← h0, zero_mul] at h1
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      linarith
    rw [← h0, mul_zero, zero_mul, add_zero]
    exact hmono f g hf hg hle s
  · set a := ku_norm ϕ (f - g)
    have hle : f ≤ g + a • ϕ := fun t => by
      have h1 := hfg t
      have h2 := le_abs_self ((f - g) t)
      simp only [Pi.sub_apply] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have h1 := hmono f (g + a • ϕ) hf (ku_inC_add hg (ku_inC_smul (ku_inC_self hϕc hϕ) a)) hle s
    have h2 := hdisc g hg a hpos s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    linarith

/-- Miao, proof of Theorem 7.3.6, p. 213: (a) and (b) make `T` a contraction with modulus `θ`,
`‖Tf − Tg‖_ϕ ≤ θ‖f − g‖_ϕ` on `C_ϕ(S)`. -/
theorem ku_thm_7_3_6_contraction (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g) := by
  refine ku_norm_le hϕ (mul_nonneg hθ0.le (ku_norm_nonneg _)) fun s => ?_
  have h1 := ku_le_add_of_disc hϕc hϕ hmono hdisc hf hg s
  have h2 := ku_le_add_of_disc hϕc hϕ hmono hdisc hg hf s
  rw [ku_norm_sub_comm g f] at h2
  simp only [Pi.sub_apply]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Theorem 7.3.6** (Weighted Contraction Mapping Theorem, Miao, p. 212). Let
`T : C_ϕ(S) → C_ϕ(S)` be (a) monotone and (b) discounting, `T(f + aϕ) ≤ Tf + θaϕ` for some
`θ ∈ (0, 1)` and all `a > 0`. Then `T` is a contraction with modulus `θ` and has a unique fixed
point in `C_ϕ(S)`. Condition (c), `T0 ∈ C_ϕ(S)`, is part of `T : C_ϕ(S) → C_ϕ(S)`
(`ku_thm_7_3_6_c`). -/
theorem ku_thm_7_3_6 (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s) {T : (S → ℝ) → S → ℝ}
    (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ) :
    (∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) ∧
      ∃! V, ku_InC ϕ V ∧ T V = V := by
  have hcon : ∀ f g, ku_InC ϕ f → ku_InC ϕ g →
      ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g) := fun f g hf hg =>
    ku_thm_7_3_6_contraction hϕc hϕ hmono hθ0 hdisc hf hg
  exact ⟨hcon, ku_exists_unique_fixedPoint hϕc hϕ hT hθ0.le hθ1 hcon⟩

/-- **Theorem 7.3.6 (c)** (Miao, p. 213). For `T : C_ϕ(S) → C_ϕ(S)`, (c) `T0 ∈ C_ϕ(S)` holds. -/
theorem ku_thm_7_3_6_c {T : (S → ℝ) → S → ℝ} (hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) :
    ku_InC ϕ (T 0) :=
  hT 0 ku_inC_zero

/-- Miao, proof of Theorem 7.3.6, p. 213 ("Condition (c) ensures that `‖Tf‖_ϕ < ∞`"). If `T`
maps `C_ϕ(S)` into continuous functions and satisfies (a)–(c), then `T` maps `C_ϕ(S)` into
itself, with `‖Tf‖_ϕ ≤ ‖T0‖_ϕ + θ‖f‖_ϕ`. -/
theorem ku_thm_7_3_6_selfMap (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, ku_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ}
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : ku_InC ϕ (T 0)) {f : S → ℝ} (hf : ku_InC ϕ f) :
    ku_InC ϕ (T f) ∧ ∀ s, |T f s| ≤ (ku_norm ϕ (T 0) + θ * ku_norm ϕ f) * ϕ s := by
  have hb : ∀ s, |T f s| ≤ (ku_norm ϕ (T 0) + θ * ku_norm ϕ f) * ϕ s := fun s => by
    have h1 := ku_le_add_of_disc hϕc hϕ hmono hdisc hf ku_inC_zero s
    have h2 := ku_le_add_of_disc hϕc hϕ hmono hdisc ku_inC_zero hf s
    have h3 := ku_abs_le hϕ h0 s
    rw [sub_zero] at h1
    rw [ku_norm_sub_comm, sub_zero] at h2
    rw [abs_le] at h3 ⊢
    constructor <;> nlinarith
  exact ⟨⟨hTc f hf, _, hb⟩, hb⟩

/-- **Theorem 7.3.6** in the form its proof establishes (Miao, pp. 212–213): if `T` maps
`C_ϕ(S)` into continuous functions and satisfies (a) monotonicity, (b) discounting with
`θ ∈ (0, 1)`, and (c) `T0 ∈ C_ϕ(S)`, then `T` maps `C_ϕ(S)` into itself, is a contraction with
modulus `θ`, and has a unique fixed point in `C_ϕ(S)`. -/
theorem ku_thm_7_3_6_of_continuous (hϕc : Continuous ϕ) (hϕ : ∀ s, 0 < ϕ s)
    {T : (S → ℝ) → S → ℝ} (hTc : ∀ f, ku_InC ϕ f → Continuous (T f))
    (hmono : ∀ f g, ku_InC ϕ f → ku_InC ϕ g → f ≤ g → T f ≤ T g) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hdisc : ∀ f, ku_InC ϕ f → ∀ a : ℝ, 0 < a → T (f + a • ϕ) ≤ T f + (θ * a) • ϕ)
    (h0 : ku_InC ϕ (T 0)) :
    (∀ f, ku_InC ϕ f → ku_InC ϕ (T f)) ∧
      (∀ f g, ku_InC ϕ f → ku_InC ϕ g → ku_norm ϕ (T f - T g) ≤ θ * ku_norm ϕ (f - g)) ∧
      ∃! V, ku_InC ϕ V ∧ T V = V := by
  have hT : ∀ f, ku_InC ϕ f → ku_InC ϕ (T f) := fun f hf =>
    (ku_thm_7_3_6_selfMap hϕc hϕ hTc hmono hdisc h0 hf).1
  exact ⟨hT, ku_thm_7_3_6 hϕc hϕ hT hmono hθ0 hθ1 hdisc⟩

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The introduction to Chapter 20: limits of time-additive expected utility

Miao, Part IV introduction (p. 673) and the introduction to Chapter 20, pp. 675–677. The Part IV
introduction is a description of the topics of Chapters 20–22 and contains no mathematical
claim. The chapter introduction lists four shortcomings of time-additive expected utility; the
three that the text derives are formalised.

* `ku_intro_partial`, `ku_intro_mrs_const`: for `U(c) = ∑_{t<T} βᵗu(c_t)` the partial derivative
  in `c_s` is `βˢu'(c_s)`, so at constant consumption the marginal rate of substitution between
  consecutive dates is `1/β`, whatever the level of consumption (p. 675).
* `ku_intro_knife_edge`, `ku_intro_growth`: with a fixed gross interest rate `R` the Euler
  equation `u'(c_t) = βRu'(c_{t+1})` admits a constant path only if `βR = 1`; for `βR > 1` and
  strictly concave `u` consumption grows without bound being reached (p. 675).
* `ku_intro_rra`, `ku_intro_eis`: for power utility `u(c) = c^{1−γ}/(1 − γ)` the coefficient of
  relative risk aversion is `γ` and `log MRS_{0,1} = γ log(c₁/c₀) − log β`, so the elasticity of
  intertemporal substitution `d log(c₁/c₀)/d log MRS_{0,1}` is `1/γ` (p. 676).
* `ku_intro_timing`: in the two-period coin example (p. 676) early and late resolution give the
  same expected utility.
-/

namespace Miao.RecursiveUtility

open Filter Topology

/-- Miao, p. 675: for the time-additive utility `U(c) = ∑_{t<T} βᵗu(c_t)` the partial derivative
in `c_s`, `s < T`, is `βˢu'(c_s)`. -/
theorem ku_intro_partial {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (β : ℝ) (T : ℕ)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < T) :
    HasDerivAt (fun x => ∑ t ∈ Finset.range T, β ^ t * u (Function.update c s x t))
      (β ^ s * u' (c s)) (c s) := by
  have h : ∀ t ∈ Finset.range T, HasDerivAt (fun x => β ^ t * u (Function.update c s x t))
      (if t = s then β ^ s * u' (c s) else 0) (c s) := by
    intro t _
    by_cases hts : t = s
    · subst hts
      simp only [Function.update_self, ↓reduceIte]
      exact (hu (c t)).const_mul _
    · simp only [Function.update_of_ne hts, hts, ↓reduceIte]
      exact hasDerivAt_const _ _
  have h2 := HasDerivAt.fun_sum h
  rw [Finset.sum_ite_eq' (Finset.range T) s] at h2
  simpa [hs] using h2

/-- Miao, p. 675: at constant consumption `c_s = c_{s+1} = x` the marginal rate of substitution
`β^s u'(x)/(β^{s+1} u'(x))` between consecutive dates is `1/β`, independent of `x`. -/
theorem ku_intro_mrs_const {β ux : ℝ} (hβ : β ≠ 0) (hux : ux ≠ 0) (s : ℕ) :
    β ^ s * ux / (β ^ (s + 1) * ux) = 1 / β := by
  rw [pow_succ]
  field_simp

/-- Miao, p. 675: with a fixed gross interest rate `R`, a constant consumption path satisfies the
Euler equation `u'(c_t) = βRu'(c_{t+1})` iff `βR = 1` (the knife-edge case), when `u' > 0`. -/
theorem ku_intro_knife_edge {β R ux : ℝ} (hux : 0 < ux) : ux = β * R * ux ↔ β * R = 1 := by
  constructor
  · intro h
    have : (β * R - 1) * ux = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hux.ne'
  · intro h
    rw [h, one_mul]

/-- Miao, p. 675: if `βR > 1`, `u'` is positive and strictly decreasing, then the Euler equation
`u'(c_t) = βRu'(c_{t+1})` forces `c_{t+1} > c_t`: the consumer keeps saving. -/
theorem ku_intro_growth {u' : ℝ → ℝ} (hpos : ∀ x, 0 < u' x) (hanti : StrictAnti u') {β R : ℝ}
    (hβR : 1 < β * R) {c₀ c₁ : ℝ} (heu : u' c₀ = β * R * u' c₁) : c₀ < c₁ := by
  by_contra h
  have h1 : u' c₀ ≤ u' c₁ := hanti.antitone (not_lt.1 h)
  have h2 := hpos c₁
  nlinarith

/-- Miao, p. 676: for power utility `u(c) = c^{1−γ}/(1 − γ)`, `c > 0`, `γ ≠ 1`, the derivatives
are `u'(c) = c^{−γ}` and `u''(c) = −γc^{−γ−1}`, and the coefficient of relative risk aversion
`−cu''(c)/u'(c)` equals `γ`. -/
theorem ku_intro_rra {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c ∧
      HasDerivAt (fun x => x ^ (-γ)) (-γ * c ^ (-γ - 1)) c ∧
      -c * (-γ * c ^ (-γ - 1)) / c ^ (-γ) = γ := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine ⟨?_, ?_, ?_⟩
  · have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
    convert this using 1
    rw [show (1 : ℝ) - γ - 1 = -γ by ring]
    field_simp
  · exact Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  · have e : c ^ (-γ - 1) = c ^ (-γ) * c⁻¹ := by
      rw [Real.rpow_sub hc, Real.rpow_one, div_eq_mul_inv]
    have hcg : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc _
    rw [e]
    field_simp

/-- Miao, p. 676: for `U = u(c₀) + βu(c₁)` with power utility, the marginal rate of substitution
`MRS_{0,1} = u'(c₀)/(βu'(c₁)) = c₀^{−γ}/(βc₁^{−γ})` satisfies
`log MRS_{0,1} = γ log(c₁/c₀) − log β`; hence `log(c₁/c₀) = (log MRS_{0,1} + log β)/γ` and the
elasticity of intertemporal substitution is `1/γ`, the inverse of the coefficient of relative
risk aversion. -/
theorem ku_intro_eis {β γ c₀ c₁ : ℝ} (hβ : 0 < β) (hγ : γ ≠ 0) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) = γ * Real.log (c₁ / c₀) - Real.log β ∧
      HasDerivAt (fun m => (m + Real.log β) / γ) (1 / γ)
        (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ)))) ∧
      (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) + Real.log β) / γ = Real.log (c₁ / c₀) := by
  have h0 : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc₀ _
  have h1 : 0 < c₁ ^ (-γ) := Real.rpow_pos_of_pos hc₁ _
  have hlog : Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))) = γ * Real.log (c₁ / c₀) - Real.log β := by
    rw [Real.log_div h0.ne' (by positivity), Real.log_mul hβ.ne' h1.ne', Real.log_rpow hc₀,
      Real.log_rpow hc₁, Real.log_div hc₁.ne' hc₀.ne']
    ring
  refine ⟨hlog, ?_, ?_⟩
  · have := ((hasDerivAt_id (Real.log (c₀ ^ (-γ) / (β * c₁ ^ (-γ))))).add_const
      (Real.log β)).div_const γ
    simpa using this
  · rw [hlog]
    field_simp
    ring

/-- Miao, p. 676: the coin example. Flipping the coin at date 0 (consumption `(c₀, c₁¹)` or
`(c₀, c₁²)`) and flipping it at date 1 give the same time-additive expected utility
`u(c₀) + β(u(c₁¹) + u(c₁²))/2`. -/
theorem ku_intro_timing (u : ℝ → ℝ) (β c₀ c₁₁ c₁₂ : ℝ) :
    (1 / 2) * (u c₀ + β * u c₁₁) + (1 / 2) * (u c₀ + β * u c₁₂) =
      u c₀ + β * ((1 / 2) * u c₁₁ + (1 / 2) * u c₁₂) := by
  ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Koopmans's utility (§20.1.1)

Miao §20.1.1, pp. 677–679. Consumption streams are sequences `c : ℕ → X` of bundles; the book's
space `L` of bounded sequences in `ℝˡ₊` is `ku_bddSeq K` (with `K = ℝˡ₊`), closed under the shift
`₁c` (`ku_shift`), the tails `ₜc` (`ku_tail`) and prepending a bundle (`ku_cons`):
`ku_bddSeq_closed`. Results are stated for any set `L` of streams with these closure properties.

* `eq_20_1`: the recursive representation `U(c) = W(u(c₀), U(₁c))` (20.1);
  `eq_20_1_additive`: the time-additive utility is an example.
* `ku_K1`, `ku_K2`, `ku_K3`: Koopmans's axioms (K1)–(K3).
* `ku_K1_of_recursive`, `ku_K2_of_recursive`, `ku_K3_iff_of_recursive`: a recursive
  representation satisfies (K1)–(K2) when `W` is strictly increasing in each argument, and (K3)
  iff `u` is not constant. The book's "any preference order with a recursive representation
  satisfies Koopmans's Axioms" is false without these conditions (`ku_K1_counterexample`,
  `ku_K3_counterexample`).
* `ku_koopmans_1960`: (K1)–(K2) give a recursive representation (Koopmans (1960), p. 678; the
  regularity of `W` is not addressed); `ku_ordinal_unique`: representations are unique up to a
  strictly increasing transformation.
* `definition_20_1_1`: dynamic consistency, with `U_t(c) = U(ₜc)`; `ku_dynConsistent_of_K1`
  ("Axiom (K1) ensures dynamic consistency") and `ku_dynConsistent_of_recursive`.
* `ku_IsSubjDiscount`: the subjective discount factor `β(x) = ∂W/∂U` at `(x, x, …)`.
* `example_20_1_1`, `example_20_1_1_epstein_hynes`: Uzawa and Epstein–Hynes utilities, with
  discount factors `β(u(c₀))` and `β(c₀)`.
* `example_20_1_2_const`, `example_20_1_2_discount`, `example_20_1_2_mrs`, `example_20_1_2`,
  `example_20_1_2_misprint`: for the CES aggregator `U(x, x, …) = x`, the discount factor is `β`,
  `MRS_{0,1} = (c₁/c₀)^ρ/β`, and `d log(c₁/c₀)/d log MRS_{0,1} = 1/ρ`. The printed formula
  `EIS = d log(c_s/c_t)/d log MRS_{s,t}` has the wrong sign: it gives `−1/ρ`.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {X : Type*}

/-! ### Streams -/

/-- Miao, p. 677: the shifted stream `₁c = (c₁, c₂, …)`. -/
def ku_shift (c : ℕ → X) : ℕ → X := fun t => c (t + 1)

/-- Miao, p. 677: the tail `ₜc = (c_t, c_{t+1}, …)`. -/
def ku_tail (t : ℕ) (c : ℕ → X) : ℕ → X := fun s => c (s + t)

/-- The stream `(x, c₀, c₁, …)`, written `(x, ₁c)` in the book when `c` is a shifted stream. -/
def ku_cons (x : X) (c : ℕ → X) : ℕ → X := fun t => if t = 0 then x else c (t - 1)

theorem ku_cons_zero (x : X) (c : ℕ → X) : ku_cons x c 0 = x := rfl

theorem ku_shift_cons (x : X) (c : ℕ → X) : ku_shift (ku_cons x c) = c := by
  funext t
  simp [ku_shift, ku_cons]

theorem ku_cons_shift (c : ℕ → X) : ku_cons (c 0) (ku_shift c) = c := by
  funext t
  rcases t with _ | t
  · rfl
  · simp [ku_cons, ku_shift]

theorem ku_tail_zero (c : ℕ → X) : ku_tail 0 c = c := rfl

theorem ku_tail_succ (t : ℕ) (c : ℕ → X) : ku_tail (t + 1) c = ku_tail t (ku_shift c) := by
  funext s
  simp only [ku_tail, ku_shift]
  congr 1

/-- Miao, p. 677: the space `L` of streams in `K` bounded in `‖c‖_L = sup_t ‖c_t‖`. -/
def ku_bddSeq {E : Type*} [Norm E] (K : Set E) : Set (ℕ → E) :=
  {c | (∀ t, c t ∈ K) ∧ BddAbove (Set.range fun t => ‖c t‖)}

/-- `L` is closed under the shift, under prepending a bundle in `K`, and its streams start in
`K`. -/
theorem ku_bddSeq_closed {E : Type*} [Norm E] (K : Set E) :
    (∀ c ∈ ku_bddSeq K, ku_shift c ∈ ku_bddSeq K) ∧
      (∀ x ∈ K, ∀ c ∈ ku_bddSeq K, ku_cons x c ∈ ku_bddSeq K) ∧
      (∀ c ∈ ku_bddSeq K, c 0 ∈ K) := by
  refine ⟨fun c hc => ⟨fun t => hc.1 (t + 1), ?_⟩, fun x hx c hc => ⟨fun t => ?_, ?_⟩,
    fun c hc => hc.1 0⟩
  · obtain ⟨B, hB⟩ := hc.2
    exact ⟨B, by rintro _ ⟨t, rfl⟩; exact hB ⟨t + 1, rfl⟩⟩
  · rcases t with _ | t
    · exact hx
    · simpa [ku_cons] using hc.1 t
  · obtain ⟨B, hB⟩ := hc.2
    refine ⟨max B ‖x‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    rcases t with _ | t
    · exact le_max_right _ _
    · simpa [ku_cons] using le_max_of_le_left (hB ⟨t, rfl⟩)

/-! ### Recursive representations and Koopmans's axioms -/

/-- `U` represents the preference `pref` on `L`: `c ≽ c'` iff `U(c') ≤ U(c)`. -/
def ku_Represents (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) (U : (ℕ → X) → ℝ) :
    Prop :=
  ∀ c ∈ L, ∀ c' ∈ L, (pref c c' ↔ U c' ≤ U c)

/-- Miao, (20.1), p. 678: `U` is a recursive utility with time aggregator `W` and period utility
`u`: `U(c) = W(u(c₀), U(₁c))` for `c ∈ L`. -/
def eq_20_1 {Y : Type*} (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) (W : Y → ℝ → ℝ) (u : X → Y) :
    Prop :=
  ∀ c ∈ L, U c = W (u (c 0)) (U (ku_shift c))

/-- Miao, p. 678: the time-additive utility `U(c) = ∑ βᵗu(c_t)` satisfies (20.1) with
`W(a, y) = a + βy`, on any set of streams where the series converge. -/
theorem eq_20_1_additive (L : Set (ℕ → X)) (u : X → ℝ) (β : ℝ)
    (hsum : ∀ c ∈ L, Summable fun t => β ^ t * u (c t)) (hL : ∀ c ∈ L, ku_shift c ∈ L) :
    eq_20_1 L (fun c => ∑' t, β ^ t * u (c t)) (fun a y => a + β * y) u := by
  intro c hc
  have hs := hsum c hc
  have hs' := hsum _ (hL c hc)
  simp only
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, ku_shift, pow_succ]
  congr 1
  exact tsum_congr fun t => by ring

/-- Miao, p. 678, axiom (K1): stationarity, `(x, ₁c) ≽ (x, ₁c')` iff `₁c ≽ ₁c'`. -/
def ku_K1 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∀ x ∈ K, ∀ c ∈ L, ∀ c' ∈ L, (pref (ku_cons x c) (ku_cons x c') ↔ pref c c')

/-- Miao, p. 678, axiom (K2): limited independence,
`(x, ₁c) ≽ (x', ₁c)` iff `(x, ₁c') ≽ (x', ₁c')`. -/
def ku_K2 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∀ x ∈ K, ∀ x' ∈ K, ∀ c ∈ L, ∀ c' ∈ L,
    (pref (ku_cons x c) (ku_cons x' c) ↔ pref (ku_cons x c') (ku_cons x' c'))

/-- Miao, p. 678, axiom (K3): sensitivity, `(x, ₁c) ≻ (x', ₁c)` for some `₁c`, `x`, `x'`. -/
def ku_K3 (K : Set X) (L : Set (ℕ → X)) (pref : (ℕ → X) → (ℕ → X) → Prop) : Prop :=
  ∃ c ∈ L, ∃ x ∈ K, ∃ x' ∈ K, pref (ku_cons x c) (ku_cons x' c) ∧
    ¬ pref (ku_cons x' c) (ku_cons x c)

/-- Miao, p. 678 (corrected): a recursive representation with `W` strictly increasing in its
second argument satisfies (K1). -/
theorem ku_K1_of_recursive {Y : Type*} {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ a, StrictMono (W a)) : ku_K1 K L pref := by
  intro x hx c hc c' hc'
  rw [hrep _ (hcons x hx c hc) _ (hcons x hx c' hc'), hrep c hc c' hc',
    hrec _ (hcons x hx c hc), hrec _ (hcons x hx c' hc'), ku_shift_cons, ku_shift_cons,
    ku_cons_zero, ku_cons_zero]
  exact (hW (u x)).le_iff_le

/-- Miao, p. 678 (corrected): a recursive representation with `W` strictly increasing in its
first argument satisfies (K2). -/
theorem ku_K2_of_recursive {Y : Type*} [LinearOrder Y] {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ y, StrictMono fun a => W a y) : ku_K2 K L pref := by
  intro x hx x' hx' c hc c' hc'
  rw [hrep _ (hcons x hx c hc) _ (hcons x' hx' c hc),
    hrep _ (hcons x hx c' hc') _ (hcons x' hx' c' hc'), hrec _ (hcons x hx c hc),
    hrec _ (hcons x' hx' c hc), hrec _ (hcons x hx c' hc'), hrec _ (hcons x' hx' c' hc')]
  simp only [ku_shift_cons, ku_cons_zero]
  exact ((hW (U c)).le_iff_le).trans ((hW (U c')).le_iff_le).symm

/-- Miao, p. 678 (corrected): for a recursive representation with `W` strictly increasing in its
first argument, (K3) holds iff the period utility `u` is not constant on `K` (and `L ≠ ∅`). -/
theorem ku_K3_iff_of_recursive {Y : Type*} [LinearOrder Y] {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} {W : Y → ℝ → ℝ} {u : X → Y}
    (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L) (hrep : ku_Represents L pref U)
    (hrec : eq_20_1 L U W u) (hW : ∀ y, StrictMono fun a => W a y) (hL : L.Nonempty) :
    ku_K3 K L pref ↔ ∃ x ∈ K, ∃ x' ∈ K, u x ≠ u x' := by
  have key : ∀ x ∈ K, ∀ x' ∈ K, ∀ c ∈ L,
      (pref (ku_cons x c) (ku_cons x' c) ↔ u x' ≤ u x) := by
    intro x hx x' hx' c hc
    rw [hrep _ (hcons x hx c hc) _ (hcons x' hx' c hc), hrec _ (hcons x hx c hc),
      hrec _ (hcons x' hx' c hc)]
    simp only [ku_shift_cons, ku_cons_zero]
    exact (hW (U c)).le_iff_le
  constructor
  · rintro ⟨c, hc, x, hx, x', hx', h1, h2⟩
    rw [key x hx x' hx' c hc] at h1
    rw [key x' hx' x hx c hc] at h2
    exact ⟨x, hx, x', hx', fun h => h2 (le_of_eq h)⟩
  · rintro ⟨x, hx, x', hx', hne⟩
    obtain ⟨c, hc⟩ := hL
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨c, hc, x', hx', x, hx, (key x' hx' x hx c hc).2 hlt.le,
        fun h => absurd ((key x hx x' hx' c hc).1 h) (not_le.2 hlt)⟩
    · exact ⟨c, hc, x, hx, x', hx', (key x hx x' hx' c hc).2 hlt.le,
        fun h => absurd ((key x' hx' x hx c hc).1 h) (not_le.2 hlt)⟩

/-- A constant stream lies in the book's `L` (with `K = ℝ₊`). -/
theorem ku_const_mem_bddSeq {a : ℝ} (ha : 0 ≤ a) :
    (fun _ : ℕ => a) ∈ ku_bddSeq (Set.Ici (0 : ℝ)) :=
  ⟨fun _ => ha, ⟨‖a‖, by rintro _ ⟨t, rfl⟩; exact le_rfl⟩⟩

/-- Counterexample (Miao, p. 678): a recursive representation need not satisfy (K1).
`U(c) = c₀` satisfies (20.1) with `W(a, y) = a`, `u = id`, on the book's `L ⊆ ℝ₊^ℕ`, but the
preference it represents is not stationary. -/
theorem ku_K1_counterexample :
    eq_20_1 (ku_bddSeq (Set.Ici (0 : ℝ))) (fun c => c 0) (fun a _ => a) id ∧
      ¬ ku_K1 (Set.Ici (0 : ℝ)) (ku_bddSeq (Set.Ici (0 : ℝ))) fun c c' => c' 0 ≤ c 0 := by
  refine ⟨fun c _ => rfl, fun h => ?_⟩
  have h1 := h 0 (Set.mem_Ici.2 (le_refl (0 : ℝ))) (fun _ => 0) (ku_const_mem_bddSeq le_rfl)
    (fun _ => 1)
    (ku_const_mem_bddSeq zero_le_one)
  simp only [ku_cons_zero, le_refl, true_iff] at h1
  norm_num at h1

/-- Counterexample (Miao, p. 678): a recursive representation need not satisfy (K3): `U ≡ 0`
satisfies (20.1) with `W ≡ 0`. -/
theorem ku_K3_counterexample :
    eq_20_1 (ku_bddSeq (Set.Ici (0 : ℝ))) (fun _ => (0 : ℝ)) (fun (_ : ℝ) _ => 0) id ∧
      ¬ ku_K3 (Set.Ici (0 : ℝ)) (ku_bddSeq (Set.Ici (0 : ℝ))) fun _ _ => (0 : ℝ) ≤ 0 := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, h⟩
  exact h le_rfl

/-- Miao, p. 678 (Koopmans (1960)): if `U` represents a preference satisfying (K1) and (K2) on
`L`, then `U` has a recursive representation (20.1): `u(x) = U(x, d)` for a fixed `d ∈ L` and a
suitable `W`. (Axiom (K3) and the continuity of `W` are not needed for the algebra.) -/
theorem ku_koopmans_1960 {K : Set X} {L : Set (ℕ → X)} {pref : (ℕ → X) → (ℕ → X) → Prop}
    {U : (ℕ → X) → ℝ} (hcons : ∀ x ∈ K, ∀ c ∈ L, ku_cons x c ∈ L)
    (hshift : ∀ c ∈ L, ku_shift c ∈ L) (hhead : ∀ c ∈ L, c 0 ∈ K)
    (hrep : ku_Represents L pref U) (h1 : ku_K1 K L pref) (h2 : ku_K2 K L pref) {d : ℕ → X}
    (hd : d ∈ L) : ∃ (W : ℝ → ℝ → ℝ) (u : X → ℝ), eq_20_1 L U W u := by
  classical
  let u : X → ℝ := fun x => U (ku_cons x d)
  let W : ℝ → ℝ → ℝ := fun a b =>
    if h : ∃ p : X × (ℕ → X), p.1 ∈ K ∧ p.2 ∈ L ∧ u p.1 = a ∧ U p.2 = b then
      U (ku_cons h.choose.1 h.choose.2) else 0
  refine ⟨W, u, fun c hc => ?_⟩
  have hex : ∃ p : X × (ℕ → X), p.1 ∈ K ∧ p.2 ∈ L ∧ u p.1 = u (c 0) ∧
      U p.2 = U (ku_shift c) := ⟨(c 0, ku_shift c), hhead c hc, hshift c hc, rfl, rfl⟩
  have hW : W (u (c 0)) (U (ku_shift c)) = U (ku_cons hex.choose.1 hex.choose.2) := by
    simp only [W]
    split_ifs
    rfl
  rw [hW]
  obtain ⟨hxK, hcL, hux, hUc⟩ := hex.choose_spec
  set x := hex.choose.1
  set c' := hex.choose.2
  have hc0 := hhead c hc
  have hsc := hshift c hc
  -- `(x, d) ∼ (c₀, d)`, so by (K2) `(x, c') ∼ (c₀, c')`
  have e1 : U (ku_cons x c') = U (ku_cons (c 0) c') := by
    have ha := (hrep _ (hcons x hxK d hd) _ (hcons _ hc0 d hd)).2 (le_of_eq hux.symm)
    have hb := (hrep _ (hcons _ hc0 d hd) _ (hcons x hxK d hd)).2 (le_of_eq hux)
    have ha' := (h2 x hxK _ hc0 d hd c' hcL).1 ha
    have hb' := (h2 _ hc0 x hxK d hd c' hcL).1 hb
    exact le_antisymm ((hrep _ (hcons _ hc0 c' hcL) _ (hcons x hxK c' hcL)).1 hb')
      ((hrep _ (hcons x hxK c' hcL) _ (hcons _ hc0 c' hcL)).1 ha')
  -- `c' ∼ ₁c`, so by (K1) `(c₀, c') ∼ (c₀, ₁c)`
  have e2 : U (ku_cons (c 0) c') = U (ku_cons (c 0) (ku_shift c)) := by
    have ha := (hrep _ hcL _ hsc).2 (le_of_eq hUc.symm)
    have hb := (hrep _ hsc _ hcL).2 (le_of_eq hUc)
    have ha' := (h1 _ hc0 c' hcL _ hsc).2 ha
    have hb' := (h1 _ hc0 _ hsc c' hcL).2 hb
    exact le_antisymm ((hrep _ (hcons _ hc0 _ hsc) _ (hcons _ hc0 c' hcL)).1 hb')
      ((hrep _ (hcons _ hc0 c' hcL) _ (hcons _ hc0 _ hsc)).1 ha')
  rw [e1, e2, ku_cons_shift]

/-- Miao, p. 678: the representation is unique in the sense of ordinal utility: two utility
functions representing the same preference on `L` differ by a strictly increasing
transformation. -/
theorem ku_ordinal_unique {L : Set (ℕ → X)} {pref : (ℕ → X) → (ℕ → X) → Prop}
    {U U' : (ℕ → X) → ℝ} (hU : ku_Represents L pref U) (hU' : ku_Represents L pref U') :
    ∃ f : ℝ → ℝ, StrictMonoOn f (U '' L) ∧ ∀ c ∈ L, U' c = f (U c) := by
  classical
  let f : ℝ → ℝ := fun y => if h : ∃ c, c ∈ L ∧ U c = y then U' h.choose else 0
  have hf : ∀ c ∈ L, f (U c) = U' c := by
    intro c hc
    have hex : ∃ c', c' ∈ L ∧ U c' = U c := ⟨c, hc, rfl⟩
    simp only [f]
    split_ifs
    obtain ⟨h1, h2⟩ := hex.choose_spec
    have ha := (hU _ h1 _ hc).2 (le_of_eq h2.symm)
    have hb := (hU _ hc _ h1).2 (le_of_eq h2)
    exact le_antisymm ((hU' _ hc _ h1).1 hb) ((hU' _ h1 _ hc).1 ha)
  refine ⟨f, ?_, fun c hc => (hf c hc).symm⟩
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hlt
  rw [hf c₁ hc₁, hf c₂ hc₂]
  have h1 : ¬ pref c₁ c₂ := fun h => absurd ((hU _ hc₁ _ hc₂).1 h) (not_le.2 hlt)
  rw [hU' _ hc₁ _ hc₂] at h1
  exact not_le.1 h1

/-! ### Dynamic consistency -/

/-- **Definition 20.1.1** (Miao, p. 678). `U` is dynamically consistent on `L` if for all `t` and
streams `c, c'` with `c_s = c'_s` for `s < t`, `U_t(c) > U_t(c')` implies `U₀(c) > U₀(c')`, where
`U_t(c) = U(ₜc)`. -/
def definition_20_1_1 (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) : Prop :=
  ∀ t, ∀ c ∈ L, ∀ c' ∈ L, (∀ s < t, c s = c' s) → U (ku_tail t c') < U (ku_tail t c) →
    U c' < U c

/-- Miao, p. 678: a recursive utility (20.1) with `W` strictly increasing in its second argument
is dynamically consistent. -/
theorem ku_dynConsistent_of_recursive {Y : Type*} {L : Set (ℕ → X)} {U : (ℕ → X) → ℝ}
    {W : Y → ℝ → ℝ} {u : X → Y} (hshift : ∀ c ∈ L, ku_shift c ∈ L) (hrec : eq_20_1 L U W u)
    (hW : ∀ a, StrictMono (W a)) : definition_20_1_1 L U := by
  intro t
  induction t with
  | zero => exact fun c _ c' _ _ h => h
  | succ t ih =>
    intro c hc c' hc' heq hlt
    rw [ku_tail_succ, ku_tail_succ] at hlt
    have h1 := ih _ (hshift c hc) _ (hshift c' hc')
      (fun s hs => heq (s + 1) (by omega)) hlt
    rw [hrec c hc, hrec c' hc', ← heq 0 (by omega)]
    exact hW _ h1

/-- Miao, p. 678: "Axiom (K1) ensures dynamic consistency": if `U` represents a preference on `L`
that satisfies (K1), then `U` is dynamically consistent. -/
theorem ku_dynConsistent_of_K1 {K : Set X} {L : Set (ℕ → X)}
    {pref : (ℕ → X) → (ℕ → X) → Prop} {U : (ℕ → X) → ℝ} (hshift : ∀ c ∈ L, ku_shift c ∈ L)
    (hhead : ∀ c ∈ L, c 0 ∈ K) (hrep : ku_Represents L pref U) (h1 : ku_K1 K L pref) :
    definition_20_1_1 L U := by
  intro t
  induction t with
  | zero => exact fun c _ c' _ _ h => h
  | succ t ih =>
    intro c hc c' hc' heq hlt
    rw [ku_tail_succ, ku_tail_succ] at hlt
    have hs := ih _ (hshift c hc) _ (hshift c' hc')
      (fun s hs => heq (s + 1) (by omega)) hlt
    have hn : ¬ pref (ku_shift c') (ku_shift c) := fun h =>
      absurd ((hrep _ (hshift c' hc') _ (hshift c hc)).1 h) (not_le.2 hs)
    rw [← h1 (c 0) (hhead c hc) _ (hshift c' hc') _ (hshift c hc)] at hn
    have e : ku_cons (c 0) (ku_shift c') = c' := by
      rw [heq 0 (by omega)]
      exact ku_cons_shift c'
    rw [e, ku_cons_shift, hrep c' hc' c hc] at hn
    exact not_le.1 hn

/-! ### The subjective discount factor and Examples 20.1.1–20.1.2 -/

/-- Miao, p. 678: `b` is the subjective discount factor `β(x) = ∂W(u, U)/∂U` at the constant
stream `(x, x, …)`. -/
def ku_IsSubjDiscount (W : ℝ → ℝ → ℝ) (u : X → ℝ) (U : (ℕ → X) → ℝ) (x : X) (b : ℝ) : Prop :=
  HasDerivAt (W (u x)) b (U fun _ => x)

/-- **Example 20.1.1** (Miao, p. 679), Uzawa (1968): `U(c) = u(c₀) + β(u(c₀))U(₁c)` is (20.1)
with `W(a, y) = a + β(a)y`, and the subjective discount factor at `(x, x, …)` is `β(u(x))`. -/
theorem example_20_1_1 (L : Set (ℕ → X)) (U : (ℕ → X) → ℝ) (u : X → ℝ) (β : ℝ → ℝ) :
    (eq_20_1 L U (fun a y => a + β a * y) u ↔
      ∀ c ∈ L, U c = u (c 0) + β (u (c 0)) * U (ku_shift c)) ∧
      ∀ x, ku_IsSubjDiscount (fun a y => a + β a * y) u U x (β (u x)) := by
  refine ⟨Iff.rfl, fun x => ?_⟩
  have h := ((hasDerivAt_id (U fun _ => x)).const_mul (β (u x))).const_add (u x)
  simp only [id, mul_one] at h
  exact h

/-- **Example 20.1.1** (Miao, p. 679), Epstein and Hynes (1983): for `U(c) = u(c₀) + β(c₀)U(₁c)`
the derivative of the aggregator `y ↦ u(x) + β(x)y` is the discount factor `β(x)`. -/
theorem example_20_1_1_epstein_hynes (u β : X → ℝ) (x : X) (y : ℝ) :
    HasDerivAt (fun y => u x + β x * y) (β x) y := by
  simpa using ((hasDerivAt_id y).const_mul (β x)).const_add (u x)

/-- The CES time aggregator `W(x, y) = ((1 − β)x^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}` of Example 20.1.2. -/
noncomputable def ku_ces (β ρ x y : ℝ) : ℝ :=
  ((1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ)) ^ (1 - ρ)⁻¹

theorem ku_ces_pos {β ρ x y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx : 0 < x) (hy : 0 < y) :
    0 < ku_ces β ρ x y := by
  have h1 : 0 < 1 - β := by linarith
  have := Real.rpow_pos_of_pos hx (1 - ρ)
  have := Real.rpow_pos_of_pos hy (1 - ρ)
  exact Real.rpow_pos_of_pos (by positivity) _

/-- `W(x, y)^{1−ρ} = (1 − β)x^{1−ρ} + βy^{1−ρ}`. -/
theorem ku_ces_rpow {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : ku_ces β ρ x y ^ (1 - ρ) = (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) := by
  have h1 : 0 ≤ 1 - β := by linarith
  have h2 := Real.rpow_nonneg hx (1 - ρ)
  have h3 := Real.rpow_nonneg hy (1 - ρ)
  exact Real.rpow_inv_rpow (by positivity) (sub_ne_zero.2 (Ne.symm hρ))

/-- The partial derivative `W_x = (1 − β)x^{−ρ}W^ρ` of the CES aggregator. -/
theorem ku_ces_hasDerivAt_x {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' => ku_ces β ρ x' y) ((1 - β) * x ^ (-ρ) * ku_ces β ρ x y ^ ρ) x := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy (1 - ρ)
  set S := (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) with hS
  have hSpos : 0 < S := by positivity
  have hd : HasDerivAt (fun x' => (1 - β) * x' ^ (1 - ρ) + β * y ^ (1 - ρ))
      ((1 - β) * ((1 - ρ) * x ^ (1 - ρ - 1))) x :=
    ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul (1 - β)).add_const _
  have h2 := hd.rpow_const (p := (1 - ρ)⁻¹) (Or.inl hSpos.ne')
  refine HasDerivAt.congr_deriv h2 ?_
  have e1 : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have e2 : ku_ces β ρ x y ^ ρ = S ^ ((1 - ρ)⁻¹ - 1) := by
    rw [show ku_ces β ρ x y = S ^ (1 - ρ)⁻¹ from rfl, ← Real.rpow_mul hSpos.le]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  field_simp
  rfl

/-- The partial derivative `W_y = βy^{−ρ}W^ρ` of the CES aggregator. -/
theorem ku_ces_hasDerivAt_y {β ρ x y : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' => ku_ces β ρ x y') (β * y ^ (-ρ) * ku_ces β ρ x y ^ ρ) y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy (1 - ρ)
  set S := (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) with hS
  have hSpos : 0 < S := by positivity
  have hd : HasDerivAt (fun y' => (1 - β) * x ^ (1 - ρ) + β * y' ^ (1 - ρ))
      (β * ((1 - ρ) * y ^ (1 - ρ - 1))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul β).const_add _
  have h2 := hd.rpow_const (p := (1 - ρ)⁻¹) (Or.inl hSpos.ne')
  refine HasDerivAt.congr_deriv h2 ?_
  have e1 : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have e2 : ku_ces β ρ x y ^ ρ = S ^ ((1 - ρ)⁻¹ - 1) := by
    rw [show ku_ces β ρ x y = S ^ (1 - ρ)⁻¹ from rfl, ← Real.rpow_mul hSpos.le]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  field_simp
  rfl

/-- **Example 20.1.2** (Miao, p. 679): for the CES aggregator the only positive solution of
`u = W(x, u)` is `u = x`; so a positive recursive utility assigns `U(x, x, …) = x`. -/
theorem example_20_1_2_const {β ρ x u : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) (hu : 0 < u) (h : u = ku_ces β ρ x u) : u = x := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have e := congrArg (fun z => z ^ (1 - ρ)) h
  rw [ku_ces_rpow hρ hβ0.le hβ1.le hx.le hu.le] at e
  have e2 : u ^ (1 - ρ) = x ^ (1 - ρ) := by
    have : (1 - β) * u ^ (1 - ρ) = (1 - β) * x ^ (1 - ρ) := by linarith
    exact mul_left_cancel₀ (by linarith) this
  have := congrArg (fun z => z ^ (1 - ρ)⁻¹) e2
  rwa [Real.rpow_rpow_inv hu.le h1, Real.rpow_rpow_inv hx.le h1] at this

/-- **Example 20.1.2** (Miao, p. 679): the subjective discount factor of the CES aggregator is
`β`: `∂W/∂U` at `(x, U(x, x, …)) = (x, x)` equals `β`. -/
theorem example_20_1_2_discount {β ρ x : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx : 0 < x) : HasDerivAt (fun y => ku_ces β ρ x y) β x := by
  have h := ku_ces_hasDerivAt_y hρ hβ0 hβ1 hx hx
  have hxx : ku_ces β ρ x x = x := by
    have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
    rw [ku_ces, show (1 - β) * x ^ (1 - ρ) + β * x ^ (1 - ρ) = x ^ (1 - ρ) by ring,
      Real.rpow_rpow_inv hx.le h1]
  rw [hxx, mul_assoc, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one] at h
  exact h

theorem ku_shift_update_zero (c : ℕ → ℝ) (x : ℝ) :
    ku_shift (Function.update c 0 x) = ku_shift c := by
  funext t
  simp [ku_shift]

theorem ku_shift_update_succ (c : ℕ → ℝ) (s : ℕ) (x : ℝ) :
    ku_shift (Function.update c (s + 1) x) = Function.update (ku_shift c) s x := by
  funext t
  simp [ku_shift, Function.update_apply]

/-- **Example 20.1.2** (Miao, p. 679). Let `U` solve `U(c) = W(c₀, U(₁c))` with the CES aggregator
on a set `L` of positive streams closed under the shift and under changing one entry to a
positive number, with `U > 0` on `L`. Then the partial derivatives of `U` in `c₀` and `c₁` are
`∂U/∂c₀ = W_x(c₀, U(₁c))` and `∂U/∂c₁ = W_y(c₀, U(₁c))W_x(c₁, U(₂c))`, and
`MRS_{0,1} = (∂U/∂c₀)/(∂U/∂c₁) = c₀^{−ρ}/(βc₁^{−ρ})`. -/
theorem example_20_1_2_mrs {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {L : Set (ℕ → ℝ)} {U : (ℕ → ℝ) → ℝ} (hpos : ∀ c ∈ L, ∀ t, 0 < c t)
    (hUpos : ∀ c ∈ L, 0 < U c) (hshift : ∀ c ∈ L, ku_shift c ∈ L)
    (hupd : ∀ c ∈ L, ∀ s, ∀ x, 0 < x → Function.update c s x ∈ L)
    (hrec : ∀ c ∈ L, U c = ku_ces β ρ (c 0) (U (ku_shift c))) {c : ℕ → ℝ} (hc : c ∈ L) :
    ∃ D₀ D₁ : ℝ, HasDerivAt (fun x => U (Function.update c 0 x)) D₀ (c 0) ∧
      HasDerivAt (fun x => U (Function.update c 1 x)) D₁ (c 1) ∧ 0 < D₀ ∧ 0 < D₁ ∧
      D₀ / D₁ = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ)) := by
  have hc0 := hpos c hc 0
  have hc1 := hpos c hc 1
  have hs1 := hshift c hc
  have hs2 := hshift _ hs1
  have hU1 := hUpos _ hs1
  have hU2 := hUpos _ hs2
  set U₁ := U (ku_shift c)
  set U₂ := U (ku_shift (ku_shift c))
  have hU1rec : U₁ = ku_ces β ρ (c 1) U₂ := hrec _ hs1
  -- the date-0 partial
  have hev0 : (fun x => ku_ces β ρ x U₁) =ᶠ[𝓝 (c 0)] fun x => U (Function.update c 0 x) := by
    filter_upwards [lt_mem_nhds hc0] with x hx
    rw [hrec _ (hupd c hc 0 x hx), Function.update_self, ku_shift_update_zero]
  have hD0 := (ku_ces_hasDerivAt_x hρ hβ0 hβ1 hc0 hU1).congr_of_eventuallyEq hev0.symm
  -- the date-1 partial
  have hev1 : (fun x => ku_ces β ρ (c 0) (ku_ces β ρ x U₂)) =ᶠ[𝓝 (c 1)]
      fun x => U (Function.update c 1 x) := by
    filter_upwards [lt_mem_nhds hc1] with x hx
    have hm := hupd c hc 1 x hx
    have hm1 : Function.update (ku_shift c) 0 x ∈ L := hupd _ hs1 0 x hx
    rw [hrec _ hm, Function.update_of_ne zero_ne_one, show (1 : ℕ) = 0 + 1 from rfl,
      ku_shift_update_succ, hrec _ hm1, Function.update_self, ku_shift_update_zero]
  have hin := ku_ces_hasDerivAt_x hρ hβ0 hβ1 hc1 hU2
  rw [← hU1rec] at hin
  have hout := ku_ces_hasDerivAt_y hρ hβ0 hβ1 hc0 hU1
  have hout' : HasDerivAt (fun y' => ku_ces β ρ (c 0) y')
      (β * U₁ ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ) (ku_ces β ρ (c 1) U₂) := by
    rw [← hU1rec]
    exact hout
  have hD1 := (hout'.comp (c 1) hin).congr_of_eventuallyEq hev1.symm
  refine ⟨_, _, hD0, hD1, ?_, ?_, ?_⟩
  · have := Real.rpow_pos_of_pos hc0 (-ρ)
    have := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have : 0 < 1 - β := by linarith
    positivity
  · have := Real.rpow_pos_of_pos hc1 (-ρ)
    have := Real.rpow_pos_of_pos hU1 (-ρ)
    have := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have := Real.rpow_pos_of_pos hU1 ρ
    have : 0 < 1 - β := by linarith
    positivity
  · have hW := Real.rpow_pos_of_pos (ku_ces_pos (ρ := ρ) hβ0 hβ1 hc0 hU1) ρ
    have hU1r : U₁ ^ (-ρ) * U₁ ^ ρ = 1 := by
      rw [← Real.rpow_add hU1, neg_add_cancel, Real.rpow_zero]
    have h1 := Real.rpow_pos_of_pos hc1 (-ρ)
    have h0 := Real.rpow_pos_of_pos hc0 (-ρ)
    have hb : 0 < 1 - β := by linarith
    calc (1 - β) * c 0 ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ /
          (β * U₁ ^ (-ρ) * ku_ces β ρ (c 0) U₁ ^ ρ * ((1 - β) * c 1 ^ (-ρ) * U₁ ^ ρ))
        = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ) * (U₁ ^ (-ρ) * U₁ ^ ρ)) := by
          field_simp
      _ = c 0 ^ (-ρ) / (β * c 1 ^ (-ρ)) := by rw [hU1r, mul_one]

/-- **Example 20.1.2** (Miao, p. 679): "EIS is equal to `1/ρ`". With
`MRS_{0,1} = c₀^{−ρ}/(βc₁^{−ρ})` (`example_20_1_2_mrs`), `log MRS_{0,1} = ρ log(c₁/c₀) − log β`, so
`log(c₁/c₀) = (log MRS_{0,1} + log β)/ρ` and `d log(c₁/c₀)/d log MRS_{0,1} = 1/ρ`. -/
theorem example_20_1_2 {β ρ c₀ c₁ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) :
    Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) = ρ * Real.log (c₁ / c₀) - Real.log β ∧
      (Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) + Real.log β) / ρ = Real.log (c₁ / c₀) ∧
      ∀ m, HasDerivAt (fun m => (m + Real.log β) / ρ) (1 / ρ) m := by
  have h0 : 0 < c₀ ^ (-ρ) := Real.rpow_pos_of_pos hc₀ _
  have h1 : 0 < c₁ ^ (-ρ) := Real.rpow_pos_of_pos hc₁ _
  have hlog : Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) = ρ * Real.log (c₁ / c₀) - Real.log β := by
    rw [Real.log_div h0.ne' (by positivity), Real.log_mul hβ.ne' h1.ne', Real.log_rpow hc₀,
      Real.log_rpow hc₁, Real.log_div hc₁.ne' hc₀.ne']
    ring
  refine ⟨hlog, ?_, fun m => ?_⟩
  · rw [hlog]
    field_simp
    ring
  · simpa using ((hasDerivAt_id m).add_const (Real.log β)).div_const ρ

/-- Miao, p. 679 (sign misprint): with the printed definition `EIS = d log(c_s/c_t)/d log MRS_{s,t}`
the CES aggregator gives `log(c₀/c₁) = −(log MRS_{0,1} + log β)/ρ`, whose derivative is `−1/ρ`,
not `1/ρ`. -/
theorem example_20_1_2_misprint {β ρ c₀ c₁ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) :
    -(Real.log (c₀ ^ (-ρ) / (β * c₁ ^ (-ρ))) + Real.log β) / ρ = Real.log (c₀ / c₁) ∧
      ∀ m, HasDerivAt (fun m => -(m + Real.log β) / ρ) (-1 / ρ) m := by
  obtain ⟨_, h2, _⟩ := example_20_1_2 hβ hρ hc₀ hc₁
  refine ⟨?_, fun m => ?_⟩
  · rw [neg_div, h2, ← Real.log_inv, inv_div]
  · have h := (((hasDerivAt_id m).add_const (Real.log β)).div_const ρ).neg
    convert h using 1
    · funext m
      simp only [Pi.neg_apply, id]
      ring
    · ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Construction of recursive utility (§20.1.2): Theorems 20.1.1 and 20.1.2

Miao §20.1.2, pp. 679–682.

**The operator.** For a space of streams `S` with a continuous shift `σ` (the book's `c ↦ ₁c`) and
a continuous head `hd` (`c ↦ c₀`), `ku_TW hd σ W f (c) = W(c₀, f(₁c))` is the book's `T_W`.
For a weight `ϕ > 0` let `κ` bound `δϕ(₁c) ≤ κϕ(c)` with `κ < 1` (the book's
`δ sup_c ϕ(₁c)/ϕ(c) < 1`). Under (W5), `|W(x, y) − W(x, y')| ≤ δ|y − y'|`:

* `ku_TW_mapsTo`, `ku_TW_contraction`: `T_W` maps `C_ϕ(S)` into itself and contracts `‖·‖_ϕ`
  with modulus `κ` (no monotonicity of `W` is needed);
* `ku_TW_exists_unique`: `T_W` has a unique fixed point in `C_ϕ(S)`;
* `ku_TW_iterate_bound`, `ku_TW_tendsto`: `|U(c) − T_Wⁿ0(c)| ≤ κⁿ‖U‖_ϕϕ(c)`, so `T_Wⁿ0 → U`
  in `‖·‖_ϕ` (the display on p. 682);
* `ku_TW_unique_of_bound`: `U` is also the only fixed point among the `ϕ`-bounded functions,
  continuous or not;
* `ku_TW_monotone`: (W3) makes the fixed point increasing.

The book's own proof of Theorem 20.1.2 goes through the Weighted Contraction Mapping Theorem
7.3.6 (`ku_thm_7_3_6_of_continuous`, copied in `KUWeighted`): `theorem_20_1_2_T0` (`T_W0 ∈ C_ϕ`),
`theorem_20_1_2_disc` (`T_W(f + aϕ) ≤ T_Wf + aκϕ`), and `theorem_20_1_2_via_7_3_6`.

**The consumption spaces.** `ℓ^∞_θ` (streams in `K` with `|c|_θ = sup_t ‖c_t‖/θᵗ < ∞`) is encoded
isometrically by `b_t = c_t/θᵗ`: `ku_Lθ θ K` is the set of bounded sequences `b` with
`c_t = θᵗb_t ∈ K` (`ku_seqθ`), `|c|_θ = ‖b‖` (`ku_thetaNorm_seqθ`), and every stream of finite
`θ`-norm arises (`ku_Lθ_surj`). The shift is `b ↦ θ · (b_{t+1})` (`ku_σθ`, `ku_seqθ_σθ`). The
book's `L` (bounded streams, sup norm) is `θ = 1` (`ku_seqθ_one`).

* `theorem_20_1_1`, `theorem_20_1_1_mono`, `theorem_20_1_1_concave`: Theorem 20.1.1.
* `theorem_20_1_2`, `theorem_20_1_2_concave`, `theorem_20_1_2_strict`: Theorem 20.1.2.

Departures: Theorem 20.1.2 is stated with (W5) only for existence, uniqueness and convergence
(the printed "(W2) and (W5)" would make (W5) redundant; the book's proof also uses that `W` is
increasing in `y`, which `theorem_20_1_2_via_7_3_6` assumes); (W5) is stated with `≤` and for all
`y ∈ ℝ` (the printed strict `<` fails at `y = y₀`, `ku_W5_misprint`); `θ > 0` replaces `θ ≥ 1`.
The strict concavity claim is proved with `W` jointly concave and strictly concave in the
direction of `x` (`theorem_20_1_2_strict`).
-/

namespace Miao.RecursiveUtility

open Filter Topology
open scoped BoundedContinuousFunction

/-! ### The operator `T_W` on an abstract space of streams -/

variable {S X : Type*} [TopologicalSpace S]

/-- Miao, p. 680: the operator `T_W f(c) = W(c₀, f(₁c))`, with head `hd c = c₀` and shift
`σ c = ₁c`. -/
def ku_TW (hd : S → X) (σ : S → S) (W : X → ℝ → ℝ) (f : S → ℝ) : S → ℝ :=
  fun c => W (hd c) (f (σ c))

theorem ku_TW_continuous {hd : S → X} {σ : S → S} {W : X → ℝ → ℝ} (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) {f : S → ℝ} (hf : Continuous f) :
    Continuous (ku_TW hd σ W f) :=
  hWc.comp (continuous_id.prodMk (hf.comp hσ))

/-- Miao, (W5), p. 681 (corrected): as printed, with a strict inequality for all `y, y₀`, the
Lipschitz condition fails at `y = y₀` for every `W` and `δ`. -/
theorem ku_W5_misprint (W : ℝ → ℝ → ℝ) (δ : ℝ) :
    ¬ ∀ x y y₀ : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ y₀ → |W x y - W x y₀| < δ * |y - y₀| := by
  intro h
  have := h 0 0 0 le_rfl le_rfl le_rfl
  simp at this

variable {hd : S → X} {σ : S → S} {W : X → ℝ → ℝ} {ϕ : S → ℝ} {δ κ : ℝ}

/-- Miao, proof of Theorem 20.1.2, p. 681: under (W5) and `W(c₀, 0) ∈ C_ϕ`, `T_W` maps `C_ϕ(S)`
into itself, with `|T_Wf| ≤ (B + κ‖f‖_ϕ)ϕ`. -/
theorem ku_TW_mapsTo (hσ : Continuous σ) (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2)
    (hϕ : ∀ s, 0 < ϕ s) (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hδ : 0 ≤ δ) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) {f : S → ℝ} (hf : ku_InC ϕ f) :
    ku_InC ϕ (ku_TW hd σ W f) := by
  refine ⟨ku_TW_continuous hσ hWc hf.1, B + κ * ku_norm ϕ f, fun c => ?_⟩
  have h1 := hW5 c (f (σ c)) 0
  have h2 := ku_abs_le hϕ hf (σ c)
  have h3 := hκ c
  have hN := ku_norm_nonneg (ϕ := ϕ) f
  rw [sub_zero] at h1
  calc |ku_TW hd σ W f c| ≤ |W (hd c) 0| + δ * |f (σ c)| := by
        have := abs_sub_abs_le_abs_sub (W (hd c) (f (σ c))) (W (hd c) 0)
        simp only [ku_TW]
        linarith
    _ ≤ B * ϕ c + δ * (ku_norm ϕ f * ϕ (σ c)) :=
        add_le_add (hB c) (mul_le_mul_of_nonneg_left h2 hδ)
    _ = B * ϕ c + ku_norm ϕ f * (δ * ϕ (σ c)) := by ring
    _ ≤ B * ϕ c + ku_norm ϕ f * (κ * ϕ c) := by
        have := mul_le_mul_of_nonneg_left h3 hN
        linarith
    _ = (B + κ * ku_norm ϕ f) * ϕ c := by ring

/-- Miao, proof of Theorem 20.1.2, pp. 681–682: under (W5), `T_W` is a contraction of modulus `κ`
for `‖·‖_ϕ`. -/
theorem ku_TW_contraction (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {f g : S → ℝ} (hf : ku_InC ϕ f) (hg : ku_InC ϕ g) :
    ku_norm ϕ (ku_TW hd σ W f - ku_TW hd σ W g) ≤ κ * ku_norm ϕ (f - g) := by
  refine ku_norm_le hϕ (mul_nonneg hκ0 (ku_norm_nonneg _)) fun c => ?_
  have h1 := hW5 c (f (σ c)) (g (σ c))
  have h2 := ku_abs_le hϕ (ku_inC_sub hf hg) (σ c)
  have hN := ku_norm_nonneg (ϕ := ϕ) (f - g)
  simp only [Pi.sub_apply] at h2 ⊢
  calc |ku_TW hd σ W f c - ku_TW hd σ W g c| ≤ δ * |f (σ c) - g (σ c)| := h1
    _ ≤ δ * (ku_norm ϕ (f - g) * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
    _ = ku_norm ϕ (f - g) * (δ * ϕ (σ c)) := by ring
    _ ≤ ku_norm ϕ (f - g) * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
    _ = κ * ku_norm ϕ (f - g) * ϕ c := by ring

/-- Miao, Theorem 20.1.2 (abstract form): under (W5), `W(c₀, 0) ∈ C_ϕ` and `δϕ(₁c) ≤ κϕ(c)` with
`κ < 1`, `T_W` has a unique fixed point in `C_ϕ(S)`. -/
theorem ku_TW_exists_unique (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) (hϕc : Continuous ϕ)
    (hϕ : ∀ s, 0 < ϕ s) (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) :
    ∃! U, ku_InC ϕ U ∧ ku_TW hd σ W U = U :=
  ku_exists_unique_fixedPoint hϕc hϕ (fun _ hf => ku_TW_mapsTo hσ hWc hϕ hW5 hδ hκ hB hf) hκ0
    hκ1 fun _ _ hf hg => ku_TW_contraction hϕ hW5 hδ hκ0 hκ hf hg

/-- Miao, p. 682: for a fixed point `U ∈ C_ϕ(S)`, `|U(c) − T_Wⁿ0(c)| ≤ κⁿ‖U‖_ϕϕ(c)`. -/
theorem ku_TW_iterate_bound (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) (n : ℕ) (c : S) :
    |U c - (ku_TW hd σ W)^[n] 0 c| ≤ κ ^ n * ku_norm ϕ U * ϕ c := by
  induction n generalizing c with
  | zero =>
    simpa using ku_abs_le hϕ hU c
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← congrFun hfix c]
    have h1 := hW5 c (U (σ c)) ((ku_TW hd σ W)^[n] 0 (σ c))
    have h2 := ih (σ c)
    have hN : 0 ≤ κ ^ n * ku_norm ϕ U := mul_nonneg (pow_nonneg hκ0 n) (ku_norm_nonneg _)
    calc |ku_TW hd σ W U c - ku_TW hd σ W ((ku_TW hd σ W)^[n] 0) c|
        ≤ δ * |U (σ c) - (ku_TW hd σ W)^[n] 0 (σ c)| := h1
      _ ≤ δ * (κ ^ n * ku_norm ϕ U * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
      _ = κ ^ n * ku_norm ϕ U * (δ * ϕ (σ c)) := by ring
      _ ≤ κ ^ n * ku_norm ϕ U * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
      _ = κ ^ (n + 1) * ku_norm ϕ U * ϕ c := by ring

/-- Miao, Theorem 20.1.2 (p. 681) and its proof (p. 682): `T_Wⁿ0 → U` in `‖·‖_ϕ`, and so
pointwise. -/
theorem ku_TW_tendsto (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) :
    Tendsto (fun n => ku_norm ϕ (U - (ku_TW hd σ W)^[n] 0)) atTop (𝓝 0) ∧
      ∀ c, Tendsto (fun n => (ku_TW hd σ W)^[n] 0 c) atTop (𝓝 (U c)) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1
  have hb := ku_TW_iterate_bound hϕ hW5 hδ hκ0 hκ hU hfix
  refine ⟨?_, fun c => ?_⟩
  · have h0 : Tendsto (fun n => κ ^ n * ku_norm ϕ U) atTop (𝓝 0) := by
      simpa using hpow.mul_const (ku_norm ϕ U)
    refine squeeze_zero (fun n => ku_norm_nonneg _) (fun n => ?_) h0
    exact ku_norm_le hϕ (mul_nonneg (pow_nonneg hκ0 n) (ku_norm_nonneg _)) fun c => by
      simpa using hb n c
  · have h0 : Tendsto (fun n => κ ^ n * ku_norm ϕ U * ϕ c) atTop (𝓝 0) := by
      simpa using (hpow.mul_const (ku_norm ϕ U)).mul_const (ϕ c)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
    rw [Real.dist_eq, abs_sub_comm]
    exact hb n c

/-- `U` is the only fixed point of `T_W` among the `ϕ`-bounded functions, continuous or not. -/
theorem ku_TW_unique_of_bound (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) {V : S → ℝ} {B : ℝ} (hV : ∀ c, |V c| ≤ B * ϕ c)
    (hVfix : ku_TW hd σ W V = V) : V = U := by
  set M := |B| + ku_norm ϕ U
  have hM : 0 ≤ M := add_nonneg (abs_nonneg B) (ku_norm_nonneg _)
  have hb : ∀ n c, |V c - U c| ≤ κ ^ n * M * ϕ c := by
    intro n
    induction n with
    | zero =>
      intro c
      have h1 := hV c
      have h2 := ku_abs_le hϕ hU c
      have h3 : B * ϕ c ≤ |B| * ϕ c := mul_le_mul_of_nonneg_right (le_abs_self B) (hϕ c).le
      have h4 := abs_sub (V c) (U c)
      simp only [pow_zero, one_mul, M]
      nlinarith
    | succ n ih =>
      intro c
      rw [← congrFun hVfix c, ← congrFun hfix c]
      have h1 := hW5 c (V (σ c)) (U (σ c))
      have h2 := ih (σ c)
      have hN : 0 ≤ κ ^ n * M := mul_nonneg (pow_nonneg hκ0 n) hM
      calc |ku_TW hd σ W V c - ku_TW hd σ W U c| ≤ δ * |V (σ c) - U (σ c)| := h1
        _ ≤ δ * (κ ^ n * M * ϕ (σ c)) := mul_le_mul_of_nonneg_left h2 hδ
        _ = κ ^ n * M * (δ * ϕ (σ c)) := by ring
        _ ≤ κ ^ n * M * (κ * ϕ c) := mul_le_mul_of_nonneg_left (hκ c) hN
        _ = κ ^ (n + 1) * M * ϕ c := by ring
  funext c
  have h0 : Tendsto (fun n => κ ^ n * M * ϕ c) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const M).mul_const (ϕ c)
  have := ge_of_tendsto' h0 fun n => hb n c
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- Miao, Theorem 20.1.1 and §20.1.2 (abstract form of "if `W` satisfies (W3), then `U` is
increasing"): if `W` is increasing and the head and shift preserve a relation `R` on streams, the
fixed point is increasing along `R`. -/
theorem ku_TW_monotone (hϕ : ∀ s, 0 < ϕ s)
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hδ : 0 ≤ δ) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {U : S → ℝ} (hU : ku_InC ϕ U)
    (hfix : ku_TW hd σ W U = U) (R : S → S → Prop) (Rx : X → X → Prop)
    (hR : ∀ c c', R c c' → Rx (hd c) (hd c') ∧ R (σ c) (σ c'))
    (hW3 : ∀ c c', Rx (hd c) (hd c') → ∀ y y' : ℝ, y ≤ y' → W (hd c) y ≤ W (hd c') y')
    {c c' : S} (hcc : R c c') : U c ≤ U c' := by
  have hit : ∀ n, ∀ c c', R c c' → (ku_TW hd σ W)^[n] 0 c ≤ (ku_TW hd σ W)^[n] 0 c' := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => le_rfl
    | succ n ih =>
      intro c c' h
      simp only [Function.iterate_succ_apply']
      exact hW3 c c' (hR c c' h).1 _ _ (ih _ _ (hR c c' h).2)
  have ht := (ku_TW_tendsto hϕ hW5 hδ hκ0 hκ1 hκ hU hfix).2
  exact le_of_tendsto_of_tendsto' (ht c) (ht c') fun n => hit n c c' hcc

/-! ### The book's route: the Weighted Contraction Mapping Theorem 7.3.6 -/

/-- Miao, proof of Theorem 20.1.2, p. 681: `|T_W0(c)|/ϕ(c) = |W(c₀, 0)|/ϕ(c) < ∞`, so
`T_W0 ∈ C_ϕ`. -/
theorem theorem_20_1_2_T0 (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) {B : ℝ}
    (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) : ku_InC ϕ (ku_TW hd σ W 0) :=
  ⟨hWc.comp (continuous_id.prodMk continuous_const), B, hB⟩

omit [TopologicalSpace S] in
/-- Miao, proof of Theorem 20.1.2, p. 682: by (W5), for `a > 0`,
`T_W(f + aϕ)(c) ≤ T_Wf(c) + aδϕ(₁c) ≤ T_Wf(c) + aκϕ(c)`, condition (b) of Theorem 7.3.6. -/
theorem theorem_20_1_2_disc (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) (hϕ : ∀ s, 0 < ϕ s) (f : S → ℝ) {a : ℝ} (ha : 0 < a) :
    ku_TW hd σ W (f + a • ϕ) ≤ ku_TW hd σ W f + (κ * a) • ϕ := by
  intro c
  have h1 := hW5 c (f (σ c) + a * ϕ (σ c)) (f (σ c))
  have h2 := hκ c
  rw [add_sub_cancel_left, abs_of_pos (mul_pos ha (hϕ (σ c)))] at h1
  have h3 := le_abs_self (W (hd c) (f (σ c) + a * ϕ (σ c)) - W (hd c) (f (σ c)))
  simp only [ku_TW, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

/-- **Theorem 20.1.2** by the book's route (Miao, pp. 681–682): if in addition `W` is increasing in
`y`, `T_W` is monotone, satisfies (b) of Theorem 7.3.6 with `κ` (`theorem_20_1_2_disc`) and (c)
(`theorem_20_1_2_T0`), so the Weighted Contraction Mapping Theorem gives a unique fixed point in
`C_ϕ`. -/
theorem theorem_20_1_2_via_7_3_6 (hσ : Continuous σ)
    (hWc : Continuous fun p : S × ℝ => W (hd p.1) p.2) (hϕc : Continuous ϕ)
    (hϕ : ∀ s, 0 < ϕ s) (hW3 : ∀ c, Monotone (W (hd c)))
    (hW5 : ∀ c y y', |W (hd c) y - W (hd c) y'| ≤ δ * |y - y'|) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hκ : ∀ c, δ * ϕ (σ c) ≤ κ * ϕ c) {B : ℝ} (hB : ∀ c, |W (hd c) 0| ≤ B * ϕ c) :
    ∃! U, ku_InC ϕ U ∧ ku_TW hd σ W U = U :=
  (ku_thm_7_3_6_of_continuous hϕc hϕ (fun _ hf => ku_TW_continuous hσ hWc hf.1)
    (fun _ _ _ _ hfg c => hW3 c (hfg (σ c))) hκ0 hκ1
    (fun f _ _ ha => theorem_20_1_2_disc hW5 hκ hϕ f ha) (theorem_20_1_2_T0 hWc hB)).2.2

/-! ### Concavity on a convex set of streams -/

/-- Concavity of `f` on a convex set `A` of streams, with `f` defined on the subtype `A`. -/
def ku_ConcaveS {V : Type*} [AddCommMonoid V] [SMul ℝ V] {A : Set V} (hA : Convex ℝ A)
    (f : A → ℝ) : Prop :=
  ∀ x y : A, ∀ a b : ℝ, ∀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    a * f x + b * f y ≤ f ⟨a • x.1 + b • y.1, hA x.2 y.2 ha hb hab⟩

/-- A pointwise limit of concave functions is concave. -/
theorem ku_concaveS_of_tendsto {V : Type*} [AddCommMonoid V] [SMul ℝ V] {A : Set V}
    (hA : Convex ℝ A) {g : ℕ → A → ℝ} {U : A → ℝ} (hg : ∀ n, ku_ConcaveS hA (g n))
    (ht : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (U c))) : ku_ConcaveS hA U := by
  intro x y a b ha hb hab
  exact le_of_tendsto_of_tendsto' (((ht x).const_mul a).add ((ht y).const_mul b))
    (ht _) fun n => hg n x y a b ha hb hab

/-! ### The consumption spaces `L` and `ℓ^∞_θ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The shift `(b_t) ↦ (b_{t+1})` on bounded sequences. -/
def ku_bshift (b : ℕ →ᵇ E) : ℕ →ᵇ E :=
  b.compContinuous ⟨Nat.succ, continuous_of_discreteTopology⟩

omit [NormedSpace ℝ E] in
theorem ku_bshift_apply (b : ℕ →ᵇ E) (t : ℕ) : ku_bshift b t = b (t + 1) := rfl

/-- The stream `c_t = θᵗb_t` encoded by the bounded sequence `b`. -/
def ku_seqθ (θ : ℝ) (b : ℕ →ᵇ E) : ℕ → E := fun t => θ ^ t • b t

/-- Miao, p. 681: `ℓ^∞_θ`, encoded by `b_t = c_t/θᵗ`: bounded `b` with `c_t = θᵗb_t ∈ K`. -/
def ku_Lθ (θ : ℝ) (K : Set E) : Set (ℕ →ᵇ E) := {b | ∀ t, ku_seqθ θ b t ∈ K}

/-- Miao, p. 681: the `θ`-norm `|c|_θ = sup_t ‖c_t‖/θᵗ`. -/
noncomputable def ku_thetaNorm (θ : ℝ) (c : ℕ → E) : ℝ := ⨆ t, ‖c t‖ / θ ^ t

/-- Miao, p. 681: the encoding is isometric, `|c|_θ = ‖b‖`. -/
theorem ku_thetaNorm_seqθ {θ : ℝ} (hθ : 0 < θ) (b : ℕ →ᵇ E) :
    ku_thetaNorm θ (ku_seqθ θ b) = ‖b‖ := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm, ku_thetaNorm]
  congr 1
  funext t
  have h := pow_pos hθ t
  rw [ku_seqθ, norm_smul, Real.norm_eq_abs, abs_of_pos h, mul_div_cancel_left₀ _ h.ne']

/-- Miao, p. 681: every stream in `K` with finite `θ`-norm is encoded by some `b ∈ ℓ^∞_θ`. -/
theorem ku_Lθ_surj {θ : ℝ} (hθ : 0 < θ) {K : Set E} {c : ℕ → E} (hK : ∀ t, c t ∈ K)
    (hc : BddAbove (Set.range fun t => ‖c t‖ / θ ^ t)) :
    ∃ b ∈ ku_Lθ θ K, ku_seqθ θ b = c := by
  obtain ⟨B, hB⟩ := hc
  have hb : ∀ t, ‖(θ ^ t)⁻¹ • c t‖ ≤ B := fun t => by
    have h := pow_pos hθ t
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h, inv_mul_eq_div]
    exact hB ⟨t, rfl⟩
  let b : ℕ →ᵇ E := BoundedContinuousFunction.mkOfBound
    ⟨fun t => (θ ^ t)⁻¹ • c t, continuous_of_discreteTopology⟩ (B + B)
    fun s t => ((dist_eq_norm _ _).le.trans (norm_sub_le _ _)).trans (add_le_add (hb s) (hb t))
  have hbc : ku_seqθ θ b = c := by
    funext t
    have h := pow_pos hθ t
    change θ ^ t • (θ ^ t)⁻¹ • c t = c t
    rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
  exact ⟨b, fun t => by rw [hbc]; exact hK t, hbc⟩

/-- Miao, p. 681: `ℓ^∞_θ` is complete in the `θ`-norm when `K` is closed (the book's "Banach
space"; `K = ℝˡ₊` is not a vector space): it is a closed subset of the bounded sequences. -/
theorem ku_Lθ_complete [CompleteSpace E] (θ : ℝ) {K : Set E} (hK : IsClosed K) :
    CompleteSpace (ku_Lθ θ K) := by
  have hc : IsClosed (ku_Lθ θ K) := by
    have : ku_Lθ θ K = ⋂ t, (fun b : ℕ →ᵇ E => θ ^ t • b t) ⁻¹' K := by
      ext b
      simp [ku_Lθ, ku_seqθ]
    rw [this]
    exact isClosed_iInter fun t => hK.preimage
      ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.const_smul _)
  exact hc.completeSpace_coe

/-- For `θ = 1` the encoding is the identity: `ℓ^∞_1` is the book's space `L` of bounded streams
with the sup norm. -/
theorem ku_seqθ_one (b : ℕ →ᵇ E) : ku_seqθ 1 b = b := by
  funext t
  simp [ku_seqθ]

theorem ku_seqθ_zero (θ : ℝ) (b : ℕ →ᵇ E) : ku_seqθ θ b 0 = b 0 := by
  simp [ku_seqθ]

/-- The shift on `ℓ^∞_θ`: `b ↦ θ · (b_{t+1})`. -/
def ku_σθ {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) : ku_Lθ θ K :=
  ⟨θ • ku_bshift b.1, fun t => by
    have h := b.2 (t + 1)
    simp only [ku_seqθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply,
      smul_smul] at h ⊢
    rwa [← pow_succ]⟩

/-- Miao, p. 677: the shift on `ℓ^∞_θ` is the book's `c ↦ ₁c`: `(₁c)_t = c_{t+1}`. -/
theorem ku_seqθ_σθ {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) (t : ℕ) :
    ku_seqθ θ (ku_σθ b).1 t = ku_seqθ θ b.1 (t + 1) := by
  simp only [ku_σθ, ku_seqθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply,
    smul_smul, ← pow_succ]

theorem ku_continuous_σθ {θ : ℝ} {K : Set E} : Continuous (ku_σθ (θ := θ) (K := K)) :=
  Continuous.subtype_mk ((continuous_const_smul θ).comp
    ((BoundedContinuousFunction.continuous_compContinuous _).comp continuous_subtype_val)) _

theorem ku_continuous_head {θ : ℝ} {K : Set E} : Continuous fun b : ku_Lθ θ K => b.1 0 :=
  (BoundedContinuousFunction.lipschitz_eval_const 0).continuous.comp continuous_subtype_val

theorem ku_head_mem {θ : ℝ} {K : Set E} (b : ku_Lθ θ K) : b.1 0 ∈ K := by
  have h := b.2 0
  rwa [ku_seqθ_zero] at h

/-- `W ∘ (head, id)` is continuous on `ℓ^∞_θ × ℝ` when `W` is continuous on `K × ℝ`. -/
theorem ku_continuous_W {θ : ℝ} {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ)) :
    Continuous fun p : ku_Lθ θ K × ℝ => W (p.1.1 0) p.2 :=
  hWc.comp_continuous ((ku_continuous_head.comp continuous_fst).prodMk continuous_snd)
    fun p => ⟨ku_head_mem p.1, Set.mem_univ _⟩

theorem ku_convex_Lθ {θ : ℝ} {K : Set E} (hK : Convex ℝ K) : Convex ℝ (ku_Lθ θ K) := by
  intro x hx y hy a b ha hb hab t
  have := hK (hx t) (hy t) ha hb hab
  simp only [ku_seqθ, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    Pi.add_apply, smul_add] at this ⊢
  rwa [smul_comm (θ ^ t) a, smul_comm (θ ^ t) b]

theorem ku_σθ_mix {θ : ℝ} {K : Set E} (hK : Convex ℝ K) (x y : ku_Lθ θ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ku_σθ ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha hb hab⟩ =
      ⟨a • (ku_σθ x).1 + b • (ku_σθ y).1,
        ku_convex_Lθ hK (ku_σθ x).2 (ku_σθ y).2 ha hb hab⟩ := by
  apply Subtype.ext
  ext t
  simp only [ku_σθ, BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_add,
    Pi.add_apply, ku_bshift_apply, smul_add]
  rw [smul_comm θ a, smul_comm θ b]

/-- One step of concavity: for `W` concave on `K × ℝ` and increasing in `y`, `T_W` maps concave
functions on `ℓ^∞_θ` to concave functions. -/
theorem ku_TW_concave {θ : ℝ} {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ}
    (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (hW3 : ∀ x ∈ K, Monotone (W x)) {f : ku_Lθ θ K → ℝ} (hf : ku_ConcaveS (ku_convex_Lθ hK) f) :
    ku_ConcaveS (ku_convex_Lθ hK) (ku_TW (fun b => b.1 0) ku_σθ W f) := by
  intro x y a b ha hb hab
  simp only [ku_TW]
  rw [ku_σθ_mix hK x y ha hb hab]
  have hmix : (a • x.1 + b • y.1) 0 = a • x.1 0 + b • y.1 0 := rfl
  have hxK := ku_head_mem x
  have hyK := ku_head_mem y
  have h1 := hf (ku_σθ x) (ku_σθ y) a b ha hb hab
  have h2 := hW3 _ (hK hxK hyK ha hb hab) h1
  have h3 := hW4.2 (x := (x.1 0, f (ku_σθ x))) (y := (y.1 0, f (ku_σθ y)))
    ⟨hxK, Set.mem_univ _⟩ ⟨hyK, Set.mem_univ _⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h3
  rw [hmix]
  exact h3.trans h2

/-! ### Theorem 20.1.1 -/

/-- **Theorem 20.1.1** (Miao, p. 680), existence and uniqueness. Let `W : K × ℝ → ℝ` be continuous
with (W1) `W(·, z)` bounded on `K` for `z ≥ 0` and (W2) `|W(x, z) − W(x, z')| ≤ β|z − z'|` with
`0 ≤ β < 1`. Then on the book's space `L` (`ℓ^∞_1`) there is exactly one bounded continuous
`U : L → ℝ` with `U(c) = W(c₀, U(₁c))`: the fixed point of `T_W` on `C(L)`. -/
theorem theorem_20_1_1 {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ))
    (hW1 : ∀ z : ℝ, 0 ≤ z → ∃ B, ∀ x ∈ K, |W x z| ≤ B) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|) :
    ∃! U : ku_Lθ 1 K →ᵇ ℝ, ∀ c, U c = W (c.1 0) (U (ku_σθ c)) := by
  obtain ⟨B, hB⟩ := hW1 0 le_rfl
  have h := ku_TW_exists_unique (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) ku_continuous_σθ (ku_continuous_W hWc)
    continuous_const (fun _ => one_pos) (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1
    (fun _ => le_rfl) (B := B) (fun c => by rw [mul_one]; exact hB _ (ku_head_mem c))
  obtain ⟨U, ⟨hU, hfix⟩, huniq⟩ := h
  obtain ⟨C, hC⟩ := hU.2
  let U' : ku_Lθ 1 K →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup U hU.1 C
    fun c => by rw [Real.norm_eq_abs]; simpa using hC c
  refine ⟨U', fun c => (congrFun hfix c).symm, fun V hV => ?_⟩
  have hVin : ku_InC (fun _ => (1 : ℝ)) (fun c => V c) :=
    ⟨V.continuous, ‖V‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact V.norm_coe_le_norm c⟩
  have e := huniq (fun c => V c) ⟨hVin, funext fun c => (hV c).symm⟩
  ext c
  exact congrFun e c

/-- **Theorem 20.1.1** (Miao, p. 680): "if `W` satisfies (W3), then `U` is increasing": if `W` is
increasing in both arguments on `K × ℝ`, then `c ≤ c'` componentwise gives `U(c) ≤ U(c')`. -/
theorem theorem_20_1_1_mono [Preorder E] {K : Set E} {W : E → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|)
    (hW3 : ∀ x ∈ K, ∀ x' ∈ K, x ≤ x' → ∀ z z' : ℝ, z ≤ z' → W x z ≤ W x' z')
    (U : ku_Lθ 1 K →ᵇ ℝ) (hU : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) {c c' : ku_Lθ 1 K}
    (hcc : ∀ t, c.1 t ≤ c'.1 t) : U c ≤ U c' := by
  have hUin : ku_InC (fun _ => (1 : ℝ)) (fun c => U c) :=
    ⟨U.continuous, ‖U‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact U.norm_coe_le_norm c⟩
  exact ku_TW_monotone (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) (fun _ => one_pos)
    (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1 (fun _ => le_rfl) hUin
    (funext fun c => (hU c).symm) (fun c c' => ∀ t, c.1 t ≤ c'.1 t) (· ≤ ·)
    (fun c c' h => ⟨h 0, fun t => by
      simpa [ku_σθ, ku_bshift_apply] using h (t + 1)⟩)
    (fun c c' h y y' hy => hW3 _ (ku_head_mem c) _ (ku_head_mem c') h y y' hy) hcc

/-- **Theorem 20.1.1** (Miao, p. 680): "if (W3)–(W4) hold, then `U` is concave": for `K` convex
and `W` concave on `K × ℝ` and increasing in `z`, the solution `U` is concave on `L`. -/
theorem theorem_20_1_1_concave {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ}
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hW2 : ∀ x ∈ K, ∀ z z', |W x z - W x z'| ≤ β * |z - z'|)
    (hW3 : ∀ x ∈ K, Monotone (W x))
    (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (U : ku_Lθ 1 K →ᵇ ℝ) (hU : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) :
    ku_ConcaveS (ku_convex_Lθ hK) fun c => U c := by
  have hUin : ku_InC (fun _ => (1 : ℝ)) (fun c => U c) :=
    ⟨U.continuous, ‖U‖, fun c => by rw [mul_one, ← Real.norm_eq_abs]; exact U.norm_coe_le_norm c⟩
  have ht := (ku_TW_tendsto (S := ku_Lθ 1 K) (hd := fun b => b.1 0) (σ := ku_σθ) (W := W)
    (ϕ := fun _ => 1) (δ := β) (κ := β) (fun _ => one_pos)
    (fun c => hW2 _ (ku_head_mem c)) hβ0 hβ0 hβ1 (fun _ => le_rfl) hUin
    (funext fun c => (hU c).symm)).2
  refine ku_concaveS_of_tendsto (ku_convex_Lθ hK) (fun n => ?_) ht
  induction n with
  | zero => intro x y a b _ _ _; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ku_TW_concave hK hW4 hW3 ih

/-! ### Theorem 20.1.2 -/

/-- **Theorem 20.1.2** (Miao, p. 681), existence, uniqueness and convergence. On `ℓ^∞_θ`
(`θ > 0`), let `W` be continuous on `K × ℝ` with (W5) `|W(x, y) − W(x, y')| ≤ δ|y − y'|`, let
`ϕ > 0` be continuous, `W(c₀, 0)` bounded in the `ϕ`-norm, and `δ sup_c ϕ(₁c)/ϕ(c) < 1`. Then
there is a unique `U ∈ C_ϕ(ℓ^∞_θ)` with `W(c₀, U(₁c)) = U(c)`, and `T_Wⁿ0 → U` in `C_ϕ`. -/
theorem theorem_20_1_2 {θ : ℝ} {K : Set E} {W : E → ℝ → ℝ}
    (hWc : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (K ×ˢ Set.univ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hW5 : ∀ x ∈ K, ∀ y y', |W x y - W x y'| ≤ δ * |y - y'|) {ϕ : ku_Lθ θ K → ℝ}
    (hϕc : Continuous ϕ) (hϕ : ∀ c, 0 < ϕ c) (hW0 : ∃ B, ∀ c, |W (c.1 0) 0| ≤ B * ϕ c)
    (hsup : BddAbove (Set.range fun c => ϕ (ku_σθ c) / ϕ c))
    (hδsup : δ * ⨆ c, ϕ (ku_σθ c) / ϕ c < 1) :
    (∃! U, ku_InC ϕ U ∧ ∀ c, W (c.1 0) (U (ku_σθ c)) = U c) ∧
      ∀ U, ku_InC ϕ U → (∀ c, W (c.1 0) (U (ku_σθ c)) = U c) →
        Tendsto (fun n => ku_norm ϕ (U - (ku_TW (fun b => b.1 0) ku_σθ W)^[n] 0)) atTop
          (𝓝 0) := by
  obtain ⟨B, hB⟩ := hW0
  set κ := δ * ⨆ c, ϕ (ku_σθ c) / ϕ c
  have hκ0 : 0 ≤ κ :=
    mul_nonneg hδ (Real.iSup_nonneg fun c => (div_pos (hϕ _) (hϕ c)).le)
  have hκ : ∀ c, δ * ϕ (ku_σθ c) ≤ κ * ϕ c := fun c => by
    have h1 : ϕ (ku_σθ c) / ϕ c ≤ ⨆ c, ϕ (ku_σθ c) / ϕ c := le_ciSup hsup c
    rw [div_le_iff₀ (hϕ c)] at h1
    calc δ * ϕ (ku_σθ c) ≤ δ * ((⨆ c, ϕ (ku_σθ c) / ϕ c) * ϕ c) :=
          mul_le_mul_of_nonneg_left h1 hδ
      _ = κ * ϕ c := by ring
  have hW5' : ∀ (c : ku_Lθ θ K) y y', |W (c.1 0) y - W (c.1 0) y'| ≤ δ * |y - y'| :=
    fun c => hW5 _ (ku_head_mem c)
  refine ⟨?_, fun U hU hfix => (ku_TW_tendsto hϕ hW5' hδ hκ0 hδsup hκ hU
    (funext hfix)).1⟩
  obtain ⟨U, ⟨hU, hfix⟩, huniq⟩ := ku_TW_exists_unique ku_continuous_σθ (ku_continuous_W hWc)
    hϕc hϕ hW5' hδ hκ0 hδsup hκ hB
  exact ⟨U, ⟨hU, congrFun hfix⟩, fun V ⟨hV, hVf⟩ => huniq V ⟨hV, funext hVf⟩⟩

/-- **Theorem 20.1.2** (Miao, p. 681): "if (W6) holds, then `U` is concave". (W6): every
`T_Wⁿy` with `y` constant is concave on `ℓ^∞_θ`; the solution `U ∈ C_ϕ` is the pointwise limit of
`T_Wⁿ0` (`ku_TW_tendsto`), hence concave. -/
theorem theorem_20_1_2_concave {θ : ℝ} {K : Set E} (hK : Convex ℝ K) {W : E → ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hW5 : ∀ x ∈ K, ∀ y y', |W x y - W x y'| ≤ δ * |y - y'|)
    {ϕ : ku_Lθ θ K → ℝ} (hϕ : ∀ c, 0 < ϕ c) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hκ : ∀ c, δ * ϕ (ku_σθ c) ≤ κ * ϕ c)
    (hW6 : ∀ (n : ℕ) (y : ℝ),
      ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) ((ku_TW (fun b => b.1 0) ku_σθ W)^[n] fun _ => y))
    {U : ku_Lθ θ K → ℝ} (hU : ku_InC ϕ U) (hfix : ∀ c, W (c.1 0) (U (ku_σθ c)) = U c) :
    ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) U :=
  ku_concaveS_of_tendsto (ku_convex_Lθ (θ := θ) hK) (fun n => hW6 n 0)
    (ku_TW_tendsto hϕ (fun c => hW5 _ (ku_head_mem c)) hδ hκ0 hκ1 hκ hU (funext hfix)).2

/-- **Theorem 20.1.2** (Miao, p. 681), strict concavity (corrected hypotheses). If `W` is concave
on `K × ℝ`, strictly increasing in `y`, and strictly concave in the direction of `x`
(`aW(x, y) + bW(x', y') < W(ax + bx', ay + by')` for `x ≠ x'`), then a concave solution `U` of
`U(c) = W(c₀, U(₁c))` is strictly concave. (The printed "strictly [concave] in `x`" alone does
not drive the argument: the first date at which two streams differ may be any `t`.) -/
theorem theorem_20_1_2_strict {θ : ℝ} (hθ : 0 < θ) {K : Set E} (hK : Convex ℝ K)
    {W : E → ℝ → ℝ} (hW4 : ConcaveOn ℝ (K ×ˢ Set.univ) fun p : E × ℝ => W p.1 p.2)
    (hWs : ∀ x ∈ K, StrictMono (W x))
    (hWx : ∀ x ∈ K, ∀ x' ∈ K, x ≠ x' → ∀ y y' : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      a * W x y + b * W x' y' < W (a • x + b • x') (a * y + b * y'))
    {U : ku_Lθ θ K → ℝ} (hUc : ku_ConcaveS (ku_convex_Lθ (θ := θ) hK) U)
    (hfix : ∀ c, U c = W (c.1 0) (U (ku_σθ c))) {c c' : ku_Lθ θ K} (hne : c ≠ c') {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * U c + b * U c' < U ⟨a • c.1 + b • c'.1, ku_convex_Lθ hK c.2 c'.2 ha.le hb.le hab⟩ := by
  -- streams whose heads differ
  have head : ∀ x y : ku_Lθ θ K, x.1 0 ≠ y.1 0 →
      a * U x + b * U y < U ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩ := by
    intro x y hxy
    rw [hfix x, hfix y, hfix ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩,
      ku_σθ_mix hK x y ha.le hb.le hab]
    have hmix : (a • x.1 + b • y.1) 0 = a • x.1 0 + b • y.1 0 := rfl
    rw [hmix]
    have h1 := hUc (ku_σθ x) (ku_σθ y) a b ha.le hb.le hab
    have h2 := (hWs _ (hK (ku_head_mem x) (ku_head_mem y) ha.le hb.le hab)).monotone h1
    exact (hWx _ (ku_head_mem x) _ (ku_head_mem y) hxy _ _ a b ha hb hab).trans_le h2
  have key : ∀ k, ∀ x y : ku_Lθ θ K, x.1 k ≠ y.1 k →
      a * U x + b * U y < U ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩ := by
    intro k
    induction k with
    | zero => exact head
    | succ k ih =>
      intro x y hxy
      by_cases h0 : x.1 0 = y.1 0
      · have hs : (ku_σθ x).1 k ≠ (ku_σθ y).1 k := by
          simp only [ku_σθ, BoundedContinuousFunction.coe_smul, ku_bshift_apply]
          exact fun h => hxy (smul_right_injective E hθ.ne' h)
        have h1 := ih _ _ hs
        rw [hfix x, hfix y, hfix ⟨a • x.1 + b • y.1, ku_convex_Lθ hK x.2 y.2 ha.le hb.le hab⟩,
          ku_σθ_mix hK x y ha.le hb.le hab]
        have hmix : (a • x.1 + b • y.1) 0 = y.1 0 := by
          change a • x.1 0 + b • y.1 0 = y.1 0
          rw [h0, ← add_smul, hab, one_smul]
        rw [hmix, h0]
        have h2 := hW4.2 (x := (y.1 0, U (ku_σθ x))) (y := (y.1 0, U (ku_σθ y)))
          ⟨ku_head_mem y, Set.mem_univ _⟩ ⟨ku_head_mem y, Set.mem_univ _⟩ ha.le hb.le hab
        simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h2
        rw [← add_smul, hab, one_smul] at h2
        exact h2.trans_lt (hWs _ (ku_head_mem y) h1)
      · exact head x y h0
  have hk : ∃ k, c.1 k ≠ c'.1 k := by
    by_contra h
    push Not at h
    exact hne (Subtype.ext (BoundedContinuousFunction.ext h))
  obtain ⟨k, hk⟩ := hk
  exact key k c c' hk

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples for §20.1.2

Miao §20.1.2, pp. 680–683.

* `example_20_1_1_exists`: Uzawa's utility with bounded continuous `u` and `0 ≤ β(·) ≤ b < 1`
  satisfies (W1)–(W2), so Theorem 20.1.1 constructs it.
* `ku_additive_not_W1` (p. 680): `W(x, y) = x^{1−γ}/(1 − γ) + βy` violates (W1) on `ℝ₊`, so the
  time-additive power utility is outside Lucas and Stokey's framework.
* The weighted example on p. 682: `W(x, y) = x^{1−γ} + βy` with `0 < γ, β < 1`, `βθ^{1−γ} < 1`,
  `ϕ(c) = 1 + |c|_θ^{1−γ}` on `ℓ^∞_θ ⊆ ℝ₊^ℕ`:
  `ku_example_682_W0` (`W(c₀, 0) = c₀^{1−γ} ≤ |c|_θ^{1−γ} < ϕ(c)`; the printed strict first
  inequality fails at `c = 0`, `ku_example_682_misprint`), `ku_example_682_ratio`
  (`βϕ(₁c) ≤ max(β, βθ^{1−γ})ϕ(c)`), `ku_example_682_sup` (`β sup ϕ(₁c)/ϕ(c) < 1`),
  `ku_example_682` (Theorem 20.1.2 applies) and `ku_example_682_series` (the solution is
  `U(c) = ∑ βᵗc_t^{1−γ}`). The book derives the sup bound from the pointwise strict inequality
  `βϕ(₁c) < ϕ(c)`, which by itself does not bound the supremum (`ku_pointwise_not_sup`); the
  uniform constant `max(β, βθ^{1−γ})` does.
-/

namespace Miao.RecursiveUtility

open Filter Topology
open scoped BoundedContinuousFunction

/-- Uzawa's utility constructed by **Theorem 20.1.1** (Miao, Example 20.1.1, p. 679, and p. 680):
for `u` continuous and bounded on `K` and `β(·)` continuous with `0 ≤ β ≤ b < 1`,
`W(x, y) = u(x) + β(u(x))y` satisfies (W1)–(W2), so there is a unique bounded continuous `U` on
`L` with `U(c) = u(c₀) + β(u(c₀))U(₁c)`. -/
theorem example_20_1_1_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    {u : E → ℝ} (hu : ContinuousOn u K) {M : ℝ} (huM : ∀ x ∈ K, |u x| ≤ M) {β : ℝ → ℝ}
    (hβ : Continuous β) {b : ℝ} (hb0 : ∀ a, 0 ≤ β a) (hb : ∀ a, β a ≤ b) (hb1 : b < 1) :
    ∃! U : ku_Lθ 1 K →ᵇ ℝ, ∀ c, U c = u (c.1 0) + β (u (c.1 0)) * U (ku_σθ c) := by
  have hu' : ContinuousOn (fun p : E × ℝ => u p.1) (K ×ˢ Set.univ) :=
    hu.comp continuousOn_fst fun p hp => hp.1
  have hWc : ContinuousOn (fun p : E × ℝ => u p.1 + β (u p.1) * p.2) (K ×ˢ Set.univ) :=
    hu'.add ((hβ.comp_continuousOn hu').mul continuousOn_snd)
  refine theorem_20_1_1 (W := fun x y => u x + β (u x) * y) hWc
    (fun z _ => ⟨M + b * |z|, fun x hx => ?_⟩) ((hb0 0).trans (hb 0))
    hb1 fun x _ z z' => ?_
  · calc |u x + β (u x) * z| ≤ |u x| + |β (u x) * z| := abs_add_le _ _
      _ ≤ M + b * |z| := by
          rw [abs_mul, abs_of_nonneg (hb0 _)]
          exact add_le_add (huM x hx) (mul_le_mul_of_nonneg_right (hb _) (abs_nonneg z))
  · rw [show u x + β (u x) * z - (u x + β (u x) * z') = β (u x) * (z - z') by ring, abs_mul,
      abs_of_nonneg (hb0 _)]
    exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)

/-- Miao, p. 680: the aggregator `W(x, y) = x^{1−γ}/(1 − γ) + βy` (`γ ≠ 1`) violates (W1): `W(·, 0)`
is unbounded on `ℝ₊`. -/
theorem ku_additive_not_W1 {γ : ℝ} (hγ : γ ≠ 1) (β : ℝ) :
    ¬ ∃ B, ∀ x : ℝ, 0 ≤ x → |x ^ (1 - γ) / (1 - γ) + β * 0| ≤ B := by
  rintro ⟨B, hB⟩
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have ha : 0 < |1 - γ| := abs_pos.2 h1
  have hy : 0 ≤ (|B| + 1) * |1 - γ| := by positivity
  have hx := hB (((|B| + 1) * |1 - γ|) ^ (1 - γ)⁻¹) (Real.rpow_nonneg hy _)
  rw [Real.rpow_inv_rpow hy h1, mul_zero, add_zero, abs_div, abs_mul, abs_abs,
    abs_of_pos (by positivity : (0 : ℝ) < |B| + 1), mul_div_cancel_right₀ _ ha.ne'] at hx
  linarith [le_abs_self B]

/-- Miao, p. 682: a pointwise strict inequality `f < 1` does not bound the supremum away from
`1`: `f(n) = 1 − 1/(n + 1)`. -/
theorem ku_pointwise_not_sup :
    ∃ f : ℕ → ℝ, (∀ n, f n < 1) ∧ BddAbove (Set.range f) ∧ ¬ (⨆ n, f n) < 1 := by
  refine ⟨fun n => 1 - 1 / ((n : ℝ) + 1), fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith, ⟨1, ?_⟩, fun h => ?_⟩
  · rintro _ ⟨n, rfl⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    have hb : BddAbove (Set.range fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) := ⟨1, by
      rintro _ ⟨n, rfl⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
    have := le_ciSup hb n
    linarith

/-! ### The example on p. 682 -/

/-- The aggregator `W(x, y) = x^{1−γ} + βy` of the example on p. 682. -/
noncomputable def ku_exW (γ β : ℝ) (x y : ℝ) : ℝ := x ^ (1 - γ) + β * y

/-- The weight `ϕ(c) = 1 + |c|_θ^{1−γ}` of the example on p. 682 (`|c|_θ = ‖b‖`). -/
noncomputable def ku_exϕ {θ : ℝ} (γ : ℝ) (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : ℝ :=
  1 + ‖b.1‖ ^ (1 - γ)

theorem ku_exϕ_pos {θ γ : ℝ} (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : 0 < ku_exϕ γ b := by
  have := Real.rpow_nonneg (norm_nonneg b.1) (1 - γ)
  unfold ku_exϕ
  linarith

theorem ku_head_le_norm {θ : ℝ} (b : ku_Lθ θ (Set.Ici (0 : ℝ))) : b.1 0 ≤ ‖b.1‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact b.1.norm_coe_le_norm 0)

/-- Miao, p. 682 (corrected): `W(c₀, 0) = c₀^{1−γ} ≤ |c|_θ^{1−γ} < ϕ(c)`, so `W(c₀, 0)` is bounded
in the `ϕ`-norm. -/
theorem ku_example_682_W0 {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    b.1 0 ^ (1 - γ) ≤ ku_thetaNorm θ (ku_seqθ θ b.1) ^ (1 - γ) ∧
      |ku_exW γ β (b.1 0) 0| ≤ 1 * ku_exϕ γ b := by
  have h0 : (0 : ℝ) ≤ b.1 0 := ku_head_mem b
  have h1 : b.1 0 ^ (1 - γ) ≤ ‖b.1‖ ^ (1 - γ) :=
    Real.rpow_le_rpow h0 (ku_head_le_norm b) (by linarith)
  refine ⟨by rw [ku_thetaNorm_seqθ hθ]; exact h1, ?_⟩
  have h2 := Real.rpow_nonneg h0 (1 - γ)
  rw [ku_exW, mul_zero, add_zero, abs_of_nonneg h2, one_mul, ku_exϕ]
  linarith

/-- The zero stream lies in `ℓ^∞_θ`. -/
def ku_zeroθ (θ : ℝ) : ku_Lθ θ (Set.Ici (0 : ℝ)) :=
  ⟨0, fun t => by simp [ku_seqθ]⟩

/-- Miao, p. 682 (misprint): the printed strict inequality `c₀^{1−γ} < |c|_θ^{1−γ}` fails at
`c = 0`. -/
theorem ku_example_682_misprint {θ γ : ℝ} (hθ : 0 < θ) :
    ¬ ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      b.1 0 ^ (1 - γ) < ku_thetaNorm θ (ku_seqθ θ b.1) ^ (1 - γ) := by
  intro h
  have := h (ku_zeroθ θ)
  rw [ku_thetaNorm_seqθ hθ] at this
  simp [ku_zeroθ] at this

/-- Miao, p. 682: `|₁c|_θ ≤ θ|c|_θ`, in the encoding `‖θ · (b_{t+1})‖ ≤ θ‖b‖`. -/
theorem ku_norm_σθ_le {θ : ℝ} (hθ : 0 < θ) (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    ‖(ku_σθ b).1‖ ≤ θ * ‖b.1‖ := by
  have h : ‖ku_bshift b.1‖ ≤ ‖b.1‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun t => b.1.norm_coe_le_norm (t + 1)
  change ‖θ • ku_bshift b.1‖ ≤ θ * ‖b.1‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
  exact mul_le_mul_of_nonneg_left h hθ.le

/-- Miao, p. 682 (corrected): `βϕ(₁c) = β + β|₁c|_θ^{1−γ} ≤ β + βθ^{1−γ}|c|_θ^{1−γ}
≤ max(β, βθ^{1−γ})ϕ(c)`. -/
theorem ku_example_682_ratio {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ : 0 ≤ β)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    β * ku_exϕ γ (ku_σθ b) ≤ max β (β * θ ^ (1 - γ)) * ku_exϕ γ b := by
  have hg : 0 ≤ 1 - γ := by linarith
  have h1 : ‖(ku_σθ b).1‖ ^ (1 - γ) ≤ θ ^ (1 - γ) * ‖b.1‖ ^ (1 - γ) := by
    rw [← Real.mul_rpow hθ.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (ku_norm_σθ_le hθ b) hg
  have h2 := Real.rpow_nonneg (norm_nonneg b.1) (1 - γ)
  have h3 : β ≤ max β (β * θ ^ (1 - γ)) := le_max_left _ _
  have h4 : β * θ ^ (1 - γ) ≤ max β (β * θ ^ (1 - γ)) := le_max_right _ _
  unfold ku_exϕ
  calc β * (1 + ‖(ku_σθ b).1‖ ^ (1 - γ)) ≤ β + β * θ ^ (1 - γ) * ‖b.1‖ ^ (1 - γ) := by
        have := mul_le_mul_of_nonneg_left h1 hβ
        linarith
    _ ≤ max β (β * θ ^ (1 - γ)) + max β (β * θ ^ (1 - γ)) * ‖b.1‖ ^ (1 - γ) :=
        add_le_add h3 (mul_le_mul_of_nonneg_right h4 h2)
    _ = max β (β * θ ^ (1 - γ)) * (1 + ‖b.1‖ ^ (1 - γ)) := by ring

/-- Miao, p. 682: `β sup_c ϕ(₁c)/ϕ(c) ≤ max(β, βθ^{1−γ}) < 1`. -/
theorem ku_example_682_sup {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβθ : β * θ ^ (1 - γ) < 1) :
    BddAbove (Set.range fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) =>
        ku_exϕ γ (ku_σθ b) / ku_exϕ γ b) ∧
      β * ⨆ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exϕ γ (ku_σθ b) / ku_exϕ γ b < 1 := by
  have hr : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      ku_exϕ γ (ku_σθ b) / ku_exϕ γ b ≤ max β (β * θ ^ (1 - γ)) / β := fun b => by
    rw [div_le_div_iff₀ (ku_exϕ_pos b) hβ0]
    have := ku_example_682_ratio hθ hγ hβ0.le b
    linarith
  have hbdd : BddAbove (Set.range fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) =>
      ku_exϕ γ (ku_σθ b) / ku_exϕ γ b) := ⟨_, by rintro _ ⟨b, rfl⟩; exact hr b⟩
  refine ⟨hbdd, ?_⟩
  have : Nonempty (ku_Lθ θ (Set.Ici (0 : ℝ))) := ⟨ku_zeroθ θ⟩
  have h1 := ciSup_le hr
  have h2 : β * ⨆ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exϕ γ (ku_σθ b) / ku_exϕ γ b ≤
      max β (β * θ ^ (1 - γ)) := by
    have := mul_le_mul_of_nonneg_left h1 hβ0.le
    rwa [mul_div_cancel₀ _ hβ0.ne'] at this
  exact h2.trans_lt (max_lt hβ1 hβθ)

theorem ku_exW_continuousOn {γ β : ℝ} (hγ : γ < 1) :
    ContinuousOn (fun p : ℝ × ℝ => ku_exW γ β p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) :=
  (((Real.continuous_rpow_const (by linarith)).comp continuous_fst).add
    (continuous_const.mul continuous_snd)).continuousOn

theorem ku_exW_lipschitz (γ β : ℝ) (hβ : 0 ≤ β) (x y y' : ℝ) :
    |ku_exW γ β x y - ku_exW γ β x y'| ≤ β * |y - y'| := by
  rw [ku_exW, ku_exW, show x ^ (1 - γ) + β * y - (x ^ (1 - γ) + β * y') = β * (y - y') by ring,
    abs_mul, abs_of_nonneg hβ]

theorem ku_exϕ_continuous {θ γ : ℝ} (hγ : γ < 1) :
    Continuous (ku_exϕ (θ := θ) γ) :=
  continuous_const.add ((Real.continuous_rpow_const (by linarith)).comp
    (continuous_norm.comp continuous_subtype_val))

/-- Miao, p. 682: the example satisfies the hypotheses of **Theorem 20.1.2**, so
`W(x, y) = x^{1−γ} + βy` defines a unique recursive utility `U ∈ C_ϕ(ℓ^∞_θ)`. -/
theorem ku_example_682 {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβθ : β * θ ^ (1 - γ) < 1) :
    ∃! U, ku_InC (ku_exϕ γ) U ∧
      ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exW γ β (b.1 0) (U (ku_σθ b)) = U b :=
  (theorem_20_1_2 (ku_exW_continuousOn hγ) hβ0.le (fun x _ => ku_exW_lipschitz γ β hβ0.le x)
    (ku_exϕ_continuous hγ) ku_exϕ_pos ⟨1, fun b => (ku_example_682_W0 hθ hγ b).2⟩
    (ku_example_682_sup hθ hγ hβ0 hβ1 hβθ).1 (ku_example_682_sup hθ hγ hβ0 hβ1 hβθ).2).1

/-- Miao, p. 680 and p. 682: the solution of the example is the discounted sum
`U(c) = ∑ βᵗc_t^{1−γ}`. -/
theorem ku_example_682_series {θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβθ : β * θ ^ (1 - γ) < 1) {U : ku_Lθ θ (Set.Ici (0 : ℝ)) → ℝ}
    (hU : ku_InC (ku_exϕ γ) U)
    (hfix : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)), ku_exW γ β (b.1 0) (U (ku_σθ b)) = U b)
    (b : ku_Lθ θ (Set.Ici (0 : ℝ))) :
    U b = ∑' t, β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) := by
  have hg : 0 ≤ 1 - γ := by linarith
  set r := β * θ ^ (1 - γ)
  have hr0 : 0 ≤ r := mul_nonneg hβ0.le (Real.rpow_nonneg hθ.le _)
  -- the series and its bounds
  let V : ku_Lθ θ (Set.Ici (0 : ℝ)) → ℝ := fun b => ∑' t, β ^ t * ku_seqθ θ b.1 t ^ (1 - γ)
  have hterm : ∀ (b : ku_Lθ θ (Set.Ici (0 : ℝ))) t,
      0 ≤ β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ∧
        β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ≤ r ^ t * ‖b.1‖ ^ (1 - γ) := by
    intro b t
    have hc0 : (0 : ℝ) ≤ ku_seqθ θ b.1 t := b.2 t
    have hct : ku_seqθ θ b.1 t ≤ θ ^ t * ‖b.1‖ := by
      have h := le_abs_self (ku_seqθ θ b.1 t)
      have h2 : |ku_seqθ θ b.1 t| = θ ^ t * ‖b.1 t‖ := by
        rw [← Real.norm_eq_abs, ku_seqθ, norm_smul, Real.norm_eq_abs,
          abs_of_pos (pow_pos hθ t)]
      have h3 := mul_le_mul_of_nonneg_left (b.1.norm_coe_le_norm t) (pow_pos hθ t).le
      linarith
    have hpow : (θ ^ t * ‖b.1‖) ^ (1 - γ) = (θ ^ (1 - γ)) ^ t * ‖b.1‖ ^ (1 - γ) := by
      rw [Real.mul_rpow (pow_nonneg hθ.le t) (norm_nonneg _), Real.rpow_pow_comm hθ.le]
    refine ⟨mul_nonneg (pow_nonneg hβ0.le t) (Real.rpow_nonneg hc0 _), ?_⟩
    calc β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) ≤ β ^ t * (θ ^ t * ‖b.1‖) ^ (1 - γ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0 hct hg) (pow_nonneg hβ0.le t)
      _ = r ^ t * ‖b.1‖ ^ (1 - γ) := by rw [hpow, mul_pow]; ring
  have hsum : ∀ b : ku_Lθ θ (Set.Ici (0 : ℝ)),
      Summable fun t => β ^ t * ku_seqθ θ b.1 t ^ (1 - γ) := fun b =>
    Summable.of_nonneg_of_le (fun t => (hterm b t).1) (fun t => (hterm b t).2)
      ((summable_geometric_of_lt_one hr0 hβθ).mul_right _)
  have hVb : ∀ b, |V b| ≤ (1 - r)⁻¹ * ku_exϕ γ b := by
    intro b
    have h0 : 0 ≤ V b := tsum_nonneg fun t => (hterm b t).1
    have h1 : V b ≤ ∑' t, r ^ t * ‖b.1‖ ^ (1 - γ) :=
      Summable.tsum_le_tsum (fun t => (hterm b t).2) (hsum b)
        ((summable_geometric_of_lt_one hr0 hβθ).mul_right _)
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hβθ] at h1
    have h2 : ‖b.1‖ ^ (1 - γ) ≤ ku_exϕ γ b := by unfold ku_exϕ; linarith
    have h3 : 0 < (1 - r)⁻¹ := inv_pos.2 (by linarith)
    rw [abs_of_nonneg h0]
    calc V b ≤ (1 - r)⁻¹ * ‖b.1‖ ^ (1 - γ) := h1
      _ ≤ (1 - r)⁻¹ * ku_exϕ γ b := mul_le_mul_of_nonneg_left h2 h3.le
  have hVfix : ku_TW (fun b => b.1 0) ku_σθ (ku_exW γ β) V = V := by
    funext b
    simp only [ku_TW, ku_exW, V]
    rw [(hsum b).tsum_eq_zero_add, ← tsum_mul_left, ku_seqθ_zero, pow_zero, one_mul]
    congr 1
    refine tsum_congr fun t => ?_
    rw [ku_seqθ_σθ, pow_succ]
    ring
  have hκ := ku_example_682_ratio hθ hγ hβ0.le
  have e := ku_TW_unique_of_bound (hd := fun b : ku_Lθ θ (Set.Ici (0 : ℝ)) => b.1 0)
    (σ := ku_σθ) (W := ku_exW γ β) ku_exϕ_pos (fun c => ku_exW_lipschitz γ β hβ0.le _)
    hβ0.le (le_max_of_le_left hβ0.le) (max_lt hβ1 hβθ) hκ hU (funext hfix) hVb hVfix
  rw [← e]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive utility under uncertainty (§20.2, Definitions 20.2.1–20.2.3)

Miao §20.2 and §20.2.1, pp. 683–685. The probability space is generated by a Markov chain with
finite state space `S` and transition matrix `P` (as the book allows, p. 683): a sample path is
`ω : ℕ → S`, `F_t` is generated by `(ω₀, …, ω_t)`, and the initial state `s₀` is fixed, so `F₀` is
trivial on the paths that start at `s₀`.

* `ku_Meas t x`: `x` is `F_t`-measurable (depends on `ω₀, …, ω_t` only); `ku_Adapted`.
* `ku_E P t x`: the conditional expectation `E_t[x](ω) = ∑_{s'} P(ω_t, s') x(ω with ω_{t+1} = s')`;
  `ku_E_meas`: it maps `F_{t+1}`-measurable variables to `F_t`-measurable ones.
* `ku_Reach P s₀ t ω`: the history `(ω₀, …, ω_t)` starts at `s₀` and has positive probability.
* `definition_20_2_1` (dynamic utility, as printed: independence of past consumption),
  `definition_20_2_2` (dynamic consistency),
  `definition_20_2_3` (conditional certainty equivalent, on a set `D` of values),
  `ku_UncertaintyAgg` (the uncertainty aggregator `R`, without `R_t(α) = α`), `eq_20_2`.
* `ku_dynConsistent_of_eq_20_2`: a recursive utility (20.2) with `W` strictly increasing in its
  second argument and `M` (strictly) monotone on positive-probability successors is dynamically
  consistent.
* `ku_E_isCE`: `E_t` is a conditional certainty equivalent.
* Time-additive expected utility (pp. 685): `ku_timeAdditive_eu` (with
  `W(x, y) = u⁻¹(u(x) + βu(y))` and `M_t = u⁻¹E_t u`, `V_t = u(U_t)` satisfies
  `V_t = u(c_t) + βE_tV_{t+1}`), `ku_additive_sum` (the solution of that equation is
  `V_t = ∑_{k≥0} βᵏE_t[u(c_{t+k})]`, the book's `E_t[∑_{s ≥ t} β^{s−t}u(c_s)]`, with `E_t` of a
  date-`t + k` variable the iterated conditional expectation `ku_Eiter`), and
  `ku_timeAdditive_eu_sum`, `ku_timeAdditive_R` for the two specifications.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-- `x` is `F_t`-measurable: it depends on `ω₀, …, ω_t` only. -/
def ku_Meas (t : ℕ) (x : (ℕ → S) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → S, (∀ s ≤ t, ω s = ω' s) → x ω = x ω'

/-- An adapted process (Miao, p. 683: the set `L`). -/
def ku_Adapted (x : ℕ → (ℕ → S) → ℝ) : Prop := ∀ t, ku_Meas t (x t)

/-- Miao, p. 685: the conditional expectation `E_t`. -/
def ku_E (P : Matrix S S ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) : (ℕ → S) → ℝ :=
  fun ω => ∑ s', P (ω t) s' * x (Function.update ω (t + 1) s')

omit [Fintype S] in
theorem ku_update_agree {t : ℕ} {ω ω' : ℕ → S} (h : ∀ s ≤ t, ω s = ω' s) (s' : S) :
    ∀ s ≤ t + 1, Function.update ω (t + 1) s' s = Function.update ω' (t + 1) s' s := by
  intro s hs
  by_cases hst : s = t + 1
  · subst hst
    simp
  · rw [Function.update_of_ne hst, Function.update_of_ne hst]
    exact h s (by omega)

/-- `E_t` maps `F_{t+1}`-measurable variables to `F_t`-measurable ones. -/
theorem ku_E_meas (P : Matrix S S ℝ) {t : ℕ} {x : (ℕ → S) → ℝ} (hx : ku_Meas (t + 1) x) :
    ku_Meas t (ku_E P t x) := by
  intro ω ω' h
  simp only [ku_E, h t le_rfl]
  exact Finset.sum_congr rfl fun s' _ => by rw [hx _ _ (ku_update_agree h s')]

/-- The history `(ω₀, …, ω_t)` starts at `s₀` and has positive probability. -/
def ku_Reach (P : Matrix S S ℝ) (s₀ : S) (t : ℕ) (ω : ℕ → S) : Prop :=
  ω 0 = s₀ ∧ 0 < ∏ j ∈ Finset.range t, P (ω j) (ω (j + 1))

omit [Fintype S] in
theorem ku_reach_update {P : Matrix S S ℝ} {s₀ : S} {t : ℕ} {ω : ℕ → S}
    (h : ku_Reach P s₀ t ω) {s' : S} (hs : 0 < P (ω t) s') :
    ku_Reach P s₀ (t + 1) (Function.update ω (t + 1) s') := by
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h.1, ?_⟩
  rw [Finset.prod_range_succ, Function.update_self, Function.update_of_ne (by omega)]
  have e : ∏ j ∈ Finset.range t, P (Function.update ω (t + 1) s' j)
      (Function.update ω (t + 1) s' (j + 1)) = ∏ j ∈ Finset.range t, P (ω j) (ω (j + 1)) :=
    Finset.prod_congr rfl fun j hj => by
      have := Finset.mem_range.1 hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  rw [e]
  exact mul_pos h.2 hs

omit [Fintype S] in
theorem ku_reach_pred {P : Matrix S S ℝ} (hP : ∀ x x', 0 ≤ P x x') {s₀ : S} {t : ℕ}
    {ω : ℕ → S} (h : ku_Reach P s₀ (t + 1) ω) :
    ku_Reach P s₀ t ω ∧ 0 < P (ω t) (ω (t + 1)) := by
  have h2 := h.2
  rw [Finset.prod_range_succ] at h2
  have ha : 0 ≤ ∏ j ∈ Finset.range t, P (ω j) (ω (j + 1)) :=
    Finset.prod_nonneg fun j _ => hP _ _
  have hb := hP (ω t) (ω (t + 1))
  refine ⟨⟨h.1, ?_⟩, ?_⟩
  · by_contra hc
    have : ∏ j ∈ Finset.range t, P (ω j) (ω (j + 1)) = 0 := le_antisymm (not_lt.1 hc) ha
    rw [this, zero_mul] at h2
    exact lt_irrefl _ h2
  · by_contra hc
    have : P (ω t) (ω (t + 1)) = 0 := le_antisymm (not_lt.1 hc) hb
    rw [this, mul_zero] at h2
    exact lt_irrefl _ h2

/-! ### Definitions 20.2.1–20.2.3 and (20.2) -/

/-- **Definition 20.2.1** (Miao, p. 684). A dynamic utility on a set `C` of consumption plans maps
each plan to an adapted utility process such that `U_t(c)` does not depend on past consumption:
`c_s = c'_s` for `s ≥ t` implies `U_t(c) = U_t(c')`. -/
def definition_20_2_1 (C : Set (ℕ → (ℕ → S) → ℝ)) (U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ) :
    Prop :=
  (∀ c ∈ C, ku_Adapted (U c)) ∧
    ∀ c ∈ C, ∀ c' ∈ C, ∀ t, (∀ s ≥ t, c s = c' s) → U c t = U c' t

/-- **Definition 20.2.2** (Miao, p. 684). Dynamic consistency: if `c_s = c'_s` for `s < t`,
`U_t(c) ≥ U_t(c')` almost surely and `U_t(c) > U_t(c')` with positive probability, then
`U₀(c) > U₀(c')`. -/
def definition_20_2_2 (P : Matrix S S ℝ) (s₀ : S) (C : Set (ℕ → (ℕ → S) → ℝ))
    (U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, ∀ t, (∀ s < t, c s = c' s) →
    (∀ ω, ku_Reach P s₀ t ω → U c' t ω ≤ U c t ω) →
    (∃ ω, ku_Reach P s₀ t ω ∧ U c' t ω < U c t ω) → ∀ ω, ω 0 = s₀ → U c' 0 ω < U c 0 ω

/-- **Definition 20.2.3** (Miao, p. 684). A conditional certainty equivalent (for random
variables with values in `D`): each `M_t` maps `F_{t+1}`-measurable variables to `F_t`-measurable
ones, is continuous (in the topology of pointwise convergence), and `M_t(α) = α` for constants
`α ∈ D`, `α ≥ 0`. -/
def definition_20_2_3 (D : Set ℝ) (M : ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ) : Prop :=
  ∀ t, (∀ x, ku_Meas (t + 1) x → ku_Meas t (M t x)) ∧
    ContinuousOn (M t) {x | ku_Meas (t + 1) x ∧ ∀ ω, x ω ∈ D} ∧
    ∀ α ∈ D, 0 ≤ α → M t (fun _ => α) = fun _ => α

/-- Miao, p. 685: an uncertainty aggregator `R`, as in Definition 20.2.3 without `R_t(α) = α`. -/
def ku_UncertaintyAgg (D : Set ℝ) (M : ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ) : Prop :=
  ∀ t, (∀ x, ku_Meas (t + 1) x → ku_Meas t (M t x)) ∧
    ContinuousOn (M t) {x | ku_Meas (t + 1) x ∧ ∀ ω, x ω ∈ D}

/-- Miao, (20.2), p. 684: `U` is a recursive utility with time aggregator `W` and conditional
certainty equivalent (or uncertainty aggregator) `M`: `U_t(c) = W(c_t, M_t(U_{t+1}(c)))`. -/
def eq_20_2 (C : Set (ℕ → (ℕ → S) → ℝ)) (U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ)
    (W : ℝ → ℝ → ℝ) (M : ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ) : Prop :=
  ∀ c ∈ C, ∀ t ω, U c t ω = W (c t ω) (M t (U c (t + 1)) ω)

omit [Fintype S] in
theorem ku_definition_20_2_3_uncertaintyAgg {D : Set ℝ}
    {M : ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ} (h : definition_20_2_3 D M) :
    ku_UncertaintyAgg D M :=
  fun t => ⟨(h t).1, (h t).2.1⟩

/-- Miao, p. 685: `E_t` is a conditional certainty equivalent on all real random variables. -/
theorem ku_E_isCE {P : Matrix S S ℝ} (hP : SS.IsMarkov P) :
    definition_20_2_3 Set.univ fun t => ku_E P t := by
  intro t
  refine ⟨fun x hx => ku_E_meas P hx, ?_, fun α _ _ => ?_⟩
  · refine Continuous.continuousOn (continuous_pi fun ω => ?_)
    exact continuous_finsetSum _ fun s' _ => continuous_const.mul (continuous_apply _)
  · funext ω
    simp only [ku_E]
    rw [← Finset.sum_mul, hP.rowsum, one_mul]

omit [Fintype S] in
/-- Miao, p. 684 (dynamic consistency of (20.2)). If `U` satisfies (20.2) with `W` strictly
increasing in its second argument and `M_t` monotone, and strictly monotone, with respect to the
successors of positive probability (for random variables with values in a set `D` containing the
utilities, `W` strictly increasing on a set `E` containing the values of `M`), and `U₀(c)` is
`F₀`-measurable, then `U` is dynamically
consistent. -/
theorem ku_dynConsistent_of_eq_20_2 {P : Matrix S S ℝ} (hP : ∀ x x', 0 ≤ P x x') {s₀ : S}
    {C : Set (ℕ → (ℕ → S) → ℝ)} {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    {W : ℝ → ℝ → ℝ} {M : ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ} (hrec : eq_20_2 C U W M)
    (D E : Set ℝ) (hW : ∀ c ∈ C, ∀ t ω, StrictMonoOn (W (c t ω)) E)
    (hUD : ∀ c ∈ C, ∀ t ω, U c t ω ∈ D)
    (hME : ∀ t x ω, (∀ ω', x ω' ∈ D) → M t x ω ∈ E)
    (hM : ∀ t x y ω, (∀ ω', x ω' ∈ D) → (∀ ω', y ω' ∈ D) → (∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s')) → M t y ω ≤ M t x ω)
    (hMs : ∀ t x y ω, (∀ ω', x ω' ∈ D) → (∀ ω', y ω' ∈ D) → (∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s')) →
      (∃ s', 0 < P (ω t) s' ∧
        y (Function.update ω (t + 1) s') < x (Function.update ω (t + 1) s')) →
      M t y ω < M t x ω)
    (h0 : ∀ c ∈ C, ku_Meas 0 (U c 0)) : definition_20_2_2 P s₀ C U := by
  intro c hc c' hc' t heq hweak hstrict ω hω
  -- one backward step
  have step : ∀ k < t,
      ((∀ ω, ku_Reach P s₀ (k + 1) ω → U c' (k + 1) ω ≤ U c (k + 1) ω) ∧
        ∃ ω, ku_Reach P s₀ (k + 1) ω ∧ U c' (k + 1) ω < U c (k + 1) ω) →
      ((∀ ω, ku_Reach P s₀ k ω → U c' k ω ≤ U c k ω) ∧
        ∃ ω, ku_Reach P s₀ k ω ∧ U c' k ω < U c k ω) := by
    intro k hk ⟨hw, ω₁, hr₁, hs₁⟩
    have hck : c k = c' k := heq k hk
    have hsucc : ∀ ω, ku_Reach P s₀ k ω → ∀ s', 0 < P (ω k) s' →
        U c' (k + 1) (Function.update ω (k + 1) s') ≤ U c (k + 1) (Function.update ω (k + 1) s') :=
      fun ω hr s' hs => hw _ (ku_reach_update hr hs)
    refine ⟨fun ω hr => ?_, ?_⟩
    · rw [hrec c hc, hrec c' hc', hck]
      exact (hW c' hc' k ω).monotoneOn (hME _ _ _ (hUD c' hc' _)) (hME _ _ _ (hUD c hc _))
        (hM k _ _ ω (hUD c hc _) (hUD c' hc' _) (hsucc ω hr))
    · obtain ⟨hr₀, hp⟩ := ku_reach_pred hP hr₁
      refine ⟨ω₁, hr₀, ?_⟩
      rw [hrec c hc, hrec c' hc', hck]
      refine hW c' hc' k ω₁ (hME _ _ _ (hUD c' hc' _)) (hME _ _ _ (hUD c hc _))
        (hMs k _ _ ω₁ (hUD c hc _) (hUD c' hc' _) (hsucc ω₁ hr₀) ⟨ω₁ (k + 1), hp, ?_⟩)
      rw [Function.update_eq_self]
      exact hs₁
  have key : ∀ m ≤ t, (∀ ω, ku_Reach P s₀ (t - m) ω → U c' (t - m) ω ≤ U c (t - m) ω) ∧
      ∃ ω, ku_Reach P s₀ (t - m) ω ∧ U c' (t - m) ω < U c (t - m) ω := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨hweak, hstrict⟩
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      rw [show t - m = t - (m + 1) + 1 by omega] at h1
      exact step _ (by omega) h1
  obtain ⟨_, ω₁, hr, hs⟩ := key t le_rfl
  rw [Nat.sub_self] at hr hs
  have e1 := h0 c hc ω ω₁ fun s hs => by rw [Nat.le_zero.1 hs, hω, hr.1]
  have e2 := h0 c' hc' ω ω₁ fun s hs => by rw [Nat.le_zero.1 hs, hω, hr.1]
  rw [e1, e2]
  exact hs

/-! ### Time-additive expected utility (p. 685) -/

/-- The conditional expectation `E_t` of a date-`t + n` variable, by iterating one-step
expectations (the tower property in the Markov event tree). -/
def ku_Eiter (P : Matrix S S ℝ) : ℕ → ℕ → ((ℕ → S) → ℝ) → (ℕ → S) → ℝ
  | _, 0, x => x
  | t, n + 1, x => ku_E P t (ku_Eiter P (t + 1) n x)

theorem ku_Eiter_zero (P : Matrix S S ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) : ku_Eiter P t 0 x = x := rfl

theorem ku_Eiter_succ (P : Matrix S S ℝ) (t n : ℕ) (x : (ℕ → S) → ℝ) (ω : ℕ → S) :
    ku_Eiter P t (n + 1) x ω =
      ∑ s', P (ω t) s' * ku_Eiter P (t + 1) n x (Function.update ω (t + 1) s') := rfl

theorem ku_Eiter_abs_le {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {x : (ℕ → S) → ℝ} {B : ℝ}
    (hx : ∀ ω, |x ω| ≤ B) (n : ℕ) : ∀ t ω, |ku_Eiter P t n x ω| ≤ B := by
  induction n with
  | zero => exact fun _ ω => hx ω
  | succ n ih =>
    intro t ω
    rw [ku_Eiter_succ]
    calc |∑ s', P (ω t) s' * ku_Eiter P (t + 1) n x (Function.update ω (t + 1) s')|
        ≤ ∑ s', P (ω t) s' * B := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
          rw [abs_mul, abs_of_nonneg (hP.nonneg _ _)]
          exact mul_le_mul_of_nonneg_left (ih _ _) (hP.nonneg _ _)
      _ = B := by rw [← Finset.sum_mul, hP.rowsum, one_mul]

/-- Miao, p. 685: a bounded solution of `V_t = r_t + βE_t[V_{t+1}]` with `r` bounded and
`0 ≤ β < 1` is `V_t = ∑_{k≥0} βᵏE_t[r_{t+k}]`, the book's `E_t[∑_{s≥t} β^{s−t}r_s]`. -/
theorem ku_additive_sum {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {r V : ℕ → (ℕ → S) → ℝ} {B R : ℝ} (hr : ∀ t ω, |r t ω| ≤ R)
    (hVb : ∀ t ω, |V t ω| ≤ B) (hV : ∀ t ω, V t ω = r t ω + β * ku_E P t (V (t + 1)) ω)
    (t : ℕ) (ω : ℕ → S) :
    HasSum (fun k => β ^ k * ku_Eiter P t k (r (t + k)) ω) (V t ω) := by
  -- the finite-horizon identity
  have fin : ∀ n t ω, V t ω = ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P t k (r (t + k)) ω +
      β ^ n * ku_Eiter P t n (V (t + n)) ω := by
    intro n
    induction n with
    | zero => intro t ω; simp [ku_Eiter]
    | succ n ih =>
      intro t ω
      have hV1 : V (t + 1) = fun ω' =>
          ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P (t + 1) k (r (t + 1 + k)) ω' +
            β ^ n * ku_Eiter P (t + 1) n (V (t + 1 + n)) ω' := funext (ih (t + 1))
      have e1 : ∀ k, t + 1 + k = t + (k + 1) := fun k => by omega
      have hE : ku_E P t (V (t + 1)) ω =
          ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P t (k + 1) (r (t + (k + 1))) ω +
            β ^ n * ku_Eiter P t (n + 1) (V (t + (n + 1))) ω := by
        rw [hV1]
        simp only [ku_E, ku_Eiter_succ, mul_add, Finset.sum_add_distrib, Finset.mul_sum, e1]
        congr 1
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => by ring
      have hs : β * ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P t (k + 1) (r (t + (k + 1))) ω =
          ∑ k ∈ Finset.range n, β ^ (k + 1) * ku_Eiter P t (k + 1) (r (t + (k + 1))) ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hV t ω, hE, Finset.sum_range_succ', mul_add, hs, pow_zero, one_mul, Nat.add_zero,
        pow_succ, ku_Eiter_zero]
      simp only [add_zero]
      ring
  have hsum : Summable fun k => β ^ k * ku_Eiter P t k (r (t + k)) ω := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right R)
      fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (ku_Eiter_abs_le hP (hr _) k t ω) (pow_nonneg hβ0 k)
  have hlim : Tendsto (fun n => ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P t k (r (t + k)) ω)
      atTop (𝓝 (V t ω)) := by
    have htail : Tendsto (fun n => β ^ n * ku_Eiter P t n (V (t + n)) ω) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => β ^ n * B) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) h0
      change |β ^ n * ku_Eiter P t n (V (t + n)) ω| ≤ β ^ n * B
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
      exact mul_le_mul_of_nonneg_left (ku_Eiter_abs_le hP (hVb _) n t ω) (pow_nonneg hβ0 n)
    have e : (fun n => ∑ k ∈ Finset.range n, β ^ k * ku_Eiter P t k (r (t + k)) ω) =
        fun n => V t ω - β ^ n * ku_Eiter P t n (V (t + n)) ω := by
      funext n
      rw [fin n t ω]
      ring
    rw [e]
    simpa using htail.const_sub (V t ω)
  have h1 := hsum.hasSum
  rwa [tendsto_nhds_unique h1.tendsto_sum_nat hlim] at h1

/-- Miao, p. 685: with `W(x, y) = u⁻¹(u(x) + βu(y))` and `M_t(x) = u⁻¹E_t[u(x)]`, the recursive
utility (20.2) satisfies `U_t = u⁻¹(u(c_t) + βE_t[u(U_{t+1})])`, and `V_t = u(U_t)` satisfies
`V_t = u(c_t) + βE_t[V_{t+1}]`. -/
theorem ku_timeAdditive_eu {P : Matrix S S ℝ} {u ui : ℝ → ℝ} (hu : ∀ y, u (ui y) = y) {β : ℝ}
    {C : Set (ℕ → (ℕ → S) → ℝ)} {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (fun x y => ui (u x + β * u y))
      fun t x ω => ui (ku_E P t (fun ω' => u (x ω')) ω))
    {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C) (t : ℕ) (ω : ℕ → S) :
    U c t ω = ui (u (c t ω) + β * ku_E P t (fun ω' => u (U c (t + 1) ω')) ω) ∧
      u (U c t ω) = u (c t ω) + β * ku_E P t (fun ω' => u (U c (t + 1) ω')) ω := by
  have h := hrec c hc t ω
  simp only [hu] at h
  exact ⟨h, by rw [h, hu]⟩

/-- Miao, p. 685: for bounded `u ∘ c` and `u ∘ U`, the time-additive expected utility in the first
specification is `u(U_t(c)) = E_t[∑_{s≥t} β^{s−t}u(c_s)]`. -/
theorem ku_timeAdditive_eu_sum {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {u ui : ℝ → ℝ}
    (hu : ∀ y, u (ui y) = y) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {C : Set (ℕ → (ℕ → S) → ℝ)} {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (fun x y => ui (u x + β * u y))
      fun t x ω => ui (ku_E P t (fun ω' => u (x ω')) ω))
    {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C) {B R : ℝ} (hr : ∀ t ω, |u (c t ω)| ≤ R)
    (hVb : ∀ t ω, |u (U c t ω)| ≤ B) (t : ℕ) (ω : ℕ → S) :
    HasSum (fun k => β ^ k * ku_Eiter P t k (fun ω' => u (c (t + k) ω')) ω) (u (U c t ω)) :=
  ku_additive_sum hP hβ0 hβ1 (r := fun t ω => u (c t ω)) (V := fun t ω => u (U c t ω)) hr hVb
    (fun t ω => (ku_timeAdditive_eu hu hrec hc t ω).2) t ω

/-- Miao, p. 685: with `W(x, y) = u(x) + βy` and the uncertainty aggregator `R_t = E_t`, the
recursive utility is `U_t(c) = u(c_t) + βE_t[U_{t+1}(c)] = E_t[∑_{s≥t} β^{s−t}u(c_s)]`. -/
theorem ku_timeAdditive_R {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {u : ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (fun x y => u x + β * y) fun t => ku_E P t) {c : ℕ → (ℕ → S) → ℝ}
    (hc : c ∈ C) {B R : ℝ} (hr : ∀ t ω, |u (c t ω)| ≤ R) (hVb : ∀ t ω, |U c t ω| ≤ B)
    (t : ℕ) (ω : ℕ → S) :
    HasSum (fun k => β ^ k * ku_Eiter P t k (fun ω' => u (c (t + k) ω')) ω) (U c t ω) :=
  ku_additive_sum hP hβ0 hβ1 (r := fun t ω => u (c t ω)) (V := U c) hr hVb
    (fun t ω => hrec c hc t ω) t ω

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin preferences (§20.2.1, (20.3)–(20.5))

Miao §20.2.1, pp. 685–687.

* `ku_kpCE`: the Kreps–Porteus conditional certainty equivalent
  `M_t(x) = (E_t[x^{1−γ}])^{1/(1−γ)}`; `ku_kpCE_eq_kpR` identifies it at a node with the
  Sargent–Stachurski operator `SS.kpR`; `ku_kpCE_isCE`: it is a conditional certainty equivalent
  (Definition 20.2.3) on positive random variables; `ku_kpCE_mono`, `ku_kpCE_strictMono`.
* `eq_20_3`: with the CES aggregator, (20.2) is the Epstein–Zin recursion (20.3);
  `ku_ez_dynConsistent`: an Epstein–Zin utility with positive values is dynamically consistent.
* `ku_ez_rra`: the relative risk aversion of the certainty equivalent is `γ`; `ku_ez_eis`: the
  EIS of the aggregator is `1/ρ` (via `SS.ces_eis`).
* `ku_ez_expected_power`, `ku_ez_expected_power_sum`: for `γ = ρ`, `V_t = U_t^{1−ρ}` is the
  time-additive expected power utility.
* `ku_ez_markov`, `ku_ez_markov_homogeneous`: for stationary Markov consumption `c_t = c(s_t)`
  and irreducible `P`, (20.3) has a unique positive Markov solution `U_t = v(s_t)`, and it is
  homogeneous of degree one ("scale-invariant", p. 686).
* `ku_expCE`, `ku_expCE_isCE`, `ku_expCE_translation`, `eq_20_4`: Weil's exponential certainty
  equivalent, its translation invariance, and (20.4).
* `ku_ces_limit`, `eq_20_5`: as `ρ → 1` the CES aggregator tends to `x^{1−β}y^β`, and then
  `V_t = log U_t` satisfies (20.5).
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-- Miao, p. 686: the Kreps–Porteus conditional certainty equivalent
`M_t(x) = (E_t[x^{1−γ}])^{1/(1−γ)}`. -/
noncomputable def ku_kpCE (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) :
    (ℕ → S) → ℝ :=
  fun ω => ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω ^ (1 - γ)⁻¹

theorem ku_kpCE_eq_kpR (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) (ω : ℕ → S) :
    ku_kpCE P γ t x ω = SS.kpR (1 - γ) P (fun s' => x (Function.update ω (t + 1) s')) (ω t) := by
  simp [ku_kpCE, ku_E, SS.kpR, Matrix.mulVec, dotProduct]

theorem ku_E_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {x : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω)
    (t : ℕ) (ω : ℕ → S) : 0 < ku_E P t x ω := by
  have := hP.mulVec_pos (f := fun s' => x (Function.update ω (t + 1) s')) (fun _ => hx _) (ω t)
  simpa [ku_E, Matrix.mulVec, dotProduct] using this

theorem ku_kpCE_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) (γ : ℝ) {x : (ℕ → S) → ℝ}
    (hx : ∀ ω, 0 < x ω) (t : ℕ) (ω : ℕ → S) : 0 < ku_kpCE P γ t x ω :=
  Real.rpow_pos_of_pos (ku_E_pos hP (fun ω => Real.rpow_pos_of_pos (hx ω) _) t ω) _

/-- Miao, p. 686: the Kreps–Porteus certainty equivalent is a conditional certainty equivalent
(Definition 20.2.3) on positive random variables. -/
theorem ku_kpCE_isCE {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) :
    definition_20_2_3 (Set.Ioi 0) (ku_kpCE P γ) := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  intro t
  refine ⟨fun x hx => ?_, ?_, fun α hα _ => ?_⟩
  · have hm : ku_Meas (t + 1) fun ω => x ω ^ (1 - γ) := fun ω ω' h => by
      change x ω ^ (1 - γ) = x ω' ^ (1 - γ)
      rw [hx ω ω' h]
    intro ω ω' h
    simp only [ku_kpCE]
    rw [ku_E_meas P hm ω ω' h]
  · intro x hx
    refine ContinuousAt.continuousWithinAt (continuousAt_pi.2 fun ω => ?_)
    have hpos : ∀ s', 0 < x (Function.update ω (t + 1) s') := fun s' => hx.2 _
    have hin : ContinuousAt (fun y : (ℕ → S) → ℝ =>
        ∑ s', P (ω t) s' * y (Function.update ω (t + 1) s') ^ (1 - γ)) x :=
      tendsto_finsetSum _ fun s' _ => by
        have hc : ContinuousAt (fun y : (ℕ → S) → ℝ => y (Function.update ω (t + 1) s')) x :=
          (continuous_apply _).continuousAt
        exact (continuousAt_const.mul (hc.rpow_const (Or.inl (hpos s').ne'))).tendsto
    have hS : 0 < ∑ s', P (ω t) s' * x (Function.update ω (t + 1) s') ^ (1 - γ) :=
      ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx.2 ω') _) t ω
    exact hin.rpow_const (Or.inl hS.ne')
  · funext ω
    simp only [ku_kpCE, ku_E]
    rw [← Finset.sum_mul, hP.rowsum, one_mul]
    exact Real.rpow_rpow_inv (le_of_lt hα) h1

/-- The Kreps–Porteus certainty equivalent is monotone with respect to successors of positive
probability, on positive random variables. -/
theorem ku_kpCE_mono {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) (t : ℕ)
    {x y : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω) (ω : ℕ → S)
    (hxy : ∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s')) :
    ku_kpCE P γ t y ω ≤ ku_kpCE P γ t x ω := by
  have hSx := ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx ω') _)
    t ω
  have hSy := ku_E_pos hP (x := fun ω' => y ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hy ω') _)
    t ω
  simp only [ku_kpCE]
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hγ) : (1 : ℝ) - γ ≠ 0) with hneg | hpos
  · have h1 : ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω ≤ ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω :=
      Finset.sum_le_sum fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (hy _) (hxy s' h0) hneg.le) h0.le
    exact Real.rpow_le_rpow_of_nonpos hSx h1 (inv_lt_zero.2 hneg).le
  · have h1 : ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω ≤ ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω :=
      Finset.sum_le_sum fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hy _).le (hxy s' h0) hpos.le) h0.le
    exact Real.rpow_le_rpow hSy.le h1 (inv_pos.2 hpos).le

/-- The Kreps–Porteus certainty equivalent is strictly monotone with respect to successors of
positive probability, on positive random variables. -/
theorem ku_kpCE_strictMono {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1)
    (t : ℕ) {x y : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω) (ω : ℕ → S)
    (hxy : ∀ s', 0 < P (ω t) s' →
      y (Function.update ω (t + 1) s') ≤ x (Function.update ω (t + 1) s'))
    (hs : ∃ s', 0 < P (ω t) s' ∧
      y (Function.update ω (t + 1) s') < x (Function.update ω (t + 1) s')) :
    ku_kpCE P γ t y ω < ku_kpCE P γ t x ω := by
  obtain ⟨s₁, hp₁, hlt₁⟩ := hs
  have hSx := ku_E_pos hP (x := fun ω' => x ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hx ω') _)
    t ω
  have hSy := ku_E_pos hP (x := fun ω' => y ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hy ω') _)
    t ω
  simp only [ku_kpCE]
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hγ) : (1 : ℝ) - γ ≠ 0) with hneg | hpos
  · have h1 : ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω < ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω :=
      Finset.sum_lt_sum (fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (hy _) (hxy s' h0) hneg.le) h0.le)
        ⟨s₁, Finset.mem_univ _, mul_lt_mul_of_pos_left
          (Real.rpow_lt_rpow_of_neg (hy _) hlt₁ hneg) hp₁⟩
    exact Real.rpow_lt_rpow_of_neg hSx h1 (inv_lt_zero.2 hneg)
  · have h1 : ku_E P t (fun ω' => y ω' ^ (1 - γ)) ω < ku_E P t (fun ω' => x ω' ^ (1 - γ)) ω :=
      Finset.sum_lt_sum (fun s' _ => by
        rcases (hP.nonneg (ω t) s').eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hy _).le (hxy s' h0) hpos.le) h0.le)
        ⟨s₁, Finset.mem_univ _, mul_lt_mul_of_pos_left
          (Real.rpow_lt_rpow (hy _).le hlt₁ hpos) hp₁⟩
    exact Real.rpow_lt_rpow hSy.le h1 (inv_pos.2 hpos)

/-- `W(x, y) = ((1 − β)x^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}` is strictly increasing in `y > 0`. -/
theorem ku_ces_strictMonoOn {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ}
    (hx : 0 < x) : StrictMonoOn (ku_ces β ρ x) (Set.Ioi 0) := by
  intro y hy y' hy' hlt
  have hy0 : (0 : ℝ) < y := hy
  have hb : 0 < 1 - β := by linarith
  have hxa := Real.rpow_pos_of_pos hx (1 - ρ)
  have hya := Real.rpow_pos_of_pos hy0 (1 - ρ)
  have hya' := Real.rpow_pos_of_pos (hy0.trans hlt) (1 - ρ)
  unfold ku_ces
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hρ) : (1 : ℝ) - ρ ≠ 0) with hneg | hpos
  · have h1 : y' ^ (1 - ρ) < y ^ (1 - ρ) := Real.rpow_lt_rpow_of_neg hy0 hlt hneg
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by nlinarith) (inv_lt_zero.2 hneg)
  · have h1 : y ^ (1 - ρ) < y' ^ (1 - ρ) := Real.rpow_lt_rpow hy0.le hlt hpos
    exact Real.rpow_lt_rpow (by positivity) (by nlinarith) (inv_pos.2 hpos)

/-- Miao, (20.3), p. 686: with the CES aggregator `W` and the Kreps–Porteus certainty
equivalent,
`W(c_t, M_t(U_{t+1})) = [(1 − β)c_t^{1−ρ} + β(E_t[U_{t+1}^{1−γ}])^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}`
for positive `U_{t+1}`; so (20.2) is the Epstein–Zin recursion (20.3). -/
theorem eq_20_3 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) (β ρ γ : ℝ) {x : ℝ} {t : ℕ}
    {V : (ℕ → S) → ℝ} (hV : ∀ ω, 0 < V ω) (ω : ℕ → S) :
    ku_ces β ρ x (ku_kpCE P γ t V ω) =
      ((1 - β) * x ^ (1 - ρ) +
        β * ku_E P t (fun ω' => V ω' ^ (1 - γ)) ω ^ ((1 - ρ) / (1 - γ))) ^ (1 - ρ)⁻¹ := by
  have hE := ku_E_pos hP (x := fun ω' => V ω' ^ (1 - γ)) (fun ω' => Real.rpow_pos_of_pos (hV ω') _)
    t ω
  rw [ku_ces, ku_kpCE, ← Real.rpow_mul hE.le, div_eq_inv_mul]

/-- Miao, p. 684 and (20.3): an Epstein–Zin utility with positive values and `F₀`-measurable
`U₀` is dynamically consistent (Definition 20.2.2). -/
theorem ku_ez_dynConsistent {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {s₀ : S} {β ρ γ : ℝ}
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (hβ0 : 0 < β) (hβ1 : β < 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P γ)) (hC : ∀ c ∈ C, ∀ t ω, 0 < c t ω)
    (hU : ∀ c ∈ C, ∀ t ω, 0 < U c t ω) (h0 : ∀ c ∈ C, ku_Meas 0 (U c 0)) :
    definition_20_2_2 P s₀ C U :=
  ku_dynConsistent_of_eq_20_2 hP.nonneg hrec (Set.Ioi 0) (Set.Ioi 0)
    (fun c hc t ω => ku_ces_strictMonoOn hρ hβ0 hβ1 (hC c hc t ω)) (fun c hc t ω => hU c hc t ω)
    (fun t _ ω hx => ku_kpCE_pos hP γ hx t ω)
    (fun t _ _ ω hx hy h => ku_kpCE_mono hP hγ t hx hy ω h)
    (fun t _ _ ω hx hy h hs => ku_kpCE_strictMono hP hγ t hx hy ω h hs) h0

/-! ### Risk aversion, intertemporal substitution and the case `γ = ρ` -/

/-- Miao, p. 686: the relative risk aversion of the Kreps–Porteus certainty equivalent is `γ`: for
the vNM index `v(x) = x^{1−γ}`, `v'(x) = (1 − γ)x^{−γ}`, `v''(x) = −γ(1 − γ)x^{−γ−1}` and
`−xv''(x)/v'(x) = γ`. -/
theorem ku_ez_rra {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun x => x ^ (1 - γ)) ((1 - γ) * x ^ (-γ)) x ∧
      HasDerivAt (fun x => (1 - γ) * x ^ (-γ)) ((1 - γ) * (-γ * x ^ (-γ - 1))) x ∧
      -x * ((1 - γ) * (-γ * x ^ (-γ - 1))) / ((1 - γ) * x ^ (-γ)) = γ := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine ⟨?_, (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul _, ?_⟩
  · have := Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')
    rwa [show (1 : ℝ) - γ - 1 = -γ by ring] at this
  · have e : x ^ (-γ - 1) = x ^ (-γ) * x⁻¹ := by
      rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
    have hxg : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx _
    rw [e]
    field_simp

/-- Miao, p. 686: the EIS of the Epstein–Zin aggregator is `1/ρ`:
`log(W_x/W_y) = log((1 − β)/β) + ρ log(y/x)`, so `log(y/x) = (log(W_x/W_y) − log((1 − β)/β))/ρ`
has derivative `1/ρ` in `log(W_x/W_y)` (Sargent–Stachurski `SS.ces_eis` with `α = 1 − ρ`). -/
theorem ku_ez_eis {β ρ x y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hρ0 : ρ ≠ 0)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ Wx Wy : ℝ, HasDerivAt (fun x' => ku_ces β ρ x' y) Wx x ∧
      HasDerivAt (fun y' => ku_ces β ρ x y') Wy y ∧ 0 < Wx ∧ 0 < Wy ∧
      Real.log (Wx / Wy) = Real.log ((1 - β) / β) + ρ * Real.log (y / x) ∧
      (Real.log (Wx / Wy) - Real.log ((1 - β) / β)) / ρ = Real.log (y / x) ∧
      ∀ m, HasDerivAt (fun m => (m - Real.log ((1 - β) / β)) / ρ) (1 / ρ) m := by
  obtain ⟨Wx, Wy, h1, h2, h3, h4, h5⟩ :=
    SS.ces_eis (α := 1 - ρ) hβ0 hβ1 (sub_ne_zero.2 (Ne.symm hρ)) hx hy
  rw [show (1 : ℝ) - (1 - ρ) = ρ by ring] at h5
  refine ⟨Wx, Wy, h1, h2, h3, h4, h5, ?_, fun m => ?_⟩
  · rw [h5]
    field_simp
    ring
  · simpa using ((hasDerivAt_id m).sub_const (Real.log ((1 - β) / β))).div_const ρ

/-- Miao, p. 686: for `γ = ρ` the Epstein–Zin utility is the time-additive expected power
utility: `V_t = U_t^{1−ρ}` satisfies `V_t = (1 − β)c_t^{1−ρ} + βE_t[V_{t+1}]`. -/
theorem ku_ez_expected_power {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ : ℝ} (hρ : ρ ≠ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P ρ)) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C)
    (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω) (t : ℕ) (ω : ℕ → S) :
    U c t ω ^ (1 - ρ) =
      (1 - β) * c t ω ^ (1 - ρ) + β * ku_E P t (fun ω' => U c (t + 1) ω' ^ (1 - ρ)) ω := by
  have hE := ku_E_pos hP (x := fun ω' => U c (t + 1) ω' ^ (1 - ρ))
    (fun ω' => Real.rpow_pos_of_pos (hU _ ω') _) t ω
  rw [hrec c hc t ω, ku_ces_rpow hρ hβ0 hβ1 (hcpos t ω).le
    (ku_kpCE_pos hP ρ (hU (t + 1)) t ω).le, ku_kpCE,
    Real.rpow_inv_rpow hE.le (sub_ne_zero.2 (Ne.symm hρ))]

/-- Miao, p. 686: for `γ = ρ` and bounded `c^{1−ρ}`, `U^{1−ρ}`,
`U_t^{1−ρ} = E_t[∑_{s≥t} β^{s−t}(1 − β)c_s^{1−ρ}]`. -/
theorem ku_ez_expected_power_sum {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ : ℝ}
    (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set (ℕ → (ℕ → S) → ℝ)}
    {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (ku_ces β ρ) (ku_kpCE P ρ)) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C)
    (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω) {B R : ℝ}
    (hr : ∀ t ω, |(1 - β) * c t ω ^ (1 - ρ)| ≤ R) (hVb : ∀ t ω, |U c t ω ^ (1 - ρ)| ≤ B)
    (t : ℕ) (ω : ℕ → S) :
    HasSum (fun k => β ^ k * ku_Eiter P t k (fun ω' => (1 - β) * c (t + k) ω' ^ (1 - ρ)) ω)
      (U c t ω ^ (1 - ρ)) :=
  ku_additive_sum hP hβ0 hβ1 (r := fun t ω => (1 - β) * c t ω ^ (1 - ρ))
    (V := fun t ω => U c t ω ^ (1 - ρ)) hr hVb
    (fun t ω => ku_ez_expected_power hP hρ hβ0 hβ1.le hrec hc hcpos hU t ω) t ω

/-! ### Stationary Markov consumption: existence, uniqueness and homogeneity -/

/-- Miao, (20.3), p. 686: for stationary Markov consumption `c_t = c(s_t) > 0` and an irreducible
Markov chain, (20.3) has a unique positive Markov solution `U_t = v(s_t)`: `v` is the unique
positive fixed point of the Epstein–Zin Koopmans operator (Sargent–Stachurski Proposition 7.2.3,
`SS.globallyStableOn_ez`). -/
theorem ku_ez_markov [DecidableEq S] [Nonempty S] {P : Matrix S S ℝ} (hP : SS.IsMarkov P)
    (hirr : SS.Irreducible P) {c : S → ℝ} (hc : ∀ s, 0 < c s) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) :
    ∃ v : S → ℝ, (∀ s, 0 < v s) ∧ (∀ s, v s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P v s)) ∧
      (∀ w : S → ℝ, (∀ s, 0 < w s) →
        (∀ s, w s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P w s)) → w = v) ∧
      ∀ t ω, v (ω t) = ku_ces β ρ (c (ω t)) (ku_kpCE P γ t (fun ω' => v (ω' (t + 1))) ω) := by
  have hb : 0 < 1 - β := by linarith
  obtain ⟨v, hv, hfix, huniq, _⟩ := SS.globallyStableOn_ez hP hirr
    (h := fun s => (1 - β) * c s ^ (1 - ρ))
    (fun s => mul_pos hb (Real.rpow_pos_of_pos (hc s) _)) hβ0 hβ1
    (sub_ne_zero.2 (Ne.symm hρ)) (sub_ne_zero.2 (Ne.symm hγ))
  have hK : ∀ w : S → ℝ, ∀ s, SS.ezK (fun s => (1 - β) * c s ^ (1 - ρ)) (fun _ => β) (1 - ρ)
      (1 - γ) P w s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P w s) := fun _ _ => rfl
  refine ⟨v, hv, fun s => ?_, fun w hw hwfix => huniq w hw ?_, fun t ω => ?_⟩
  · rw [← hK]
    exact (congrFun hfix s).symm
  · funext s
    rw [hK]
    exact (hwfix s).symm
  · rw [ku_kpCE_eq_kpR]
    simp only [Function.update_self]
    rw [← hK]
    exact (congrFun hfix _).symm

/-- The CES aggregator is homogeneous of degree one. -/
theorem ku_ces_homog {β ρ : ℝ} (hρ : ρ ≠ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {l x y : ℝ}
    (hl : 0 < l) (hx : 0 ≤ x) (hy : 0 ≤ y) : ku_ces β ρ (l * x) (l * y) = l * ku_ces β ρ x y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 ≤ 1 - β := by linarith
  have h2 := Real.rpow_nonneg hx (1 - ρ)
  have h3 := Real.rpow_nonneg hy (1 - ρ)
  unfold ku_ces
  rw [Real.mul_rpow hl.le hx, Real.mul_rpow hl.le hy,
    show (1 - β) * (l ^ (1 - ρ) * x ^ (1 - ρ)) + β * (l ^ (1 - ρ) * y ^ (1 - ρ)) =
      l ^ (1 - ρ) * ((1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ)) by ring,
    Real.mul_rpow (Real.rpow_nonneg hl.le _) (by positivity), Real.rpow_rpow_inv hl.le h1]

/-- Miao, p. 686: Epstein–Zin utility is scale-invariant (homothetic): for stationary Markov
consumption the solution for `λc` is `λ` times the solution for `c`. -/
theorem ku_ez_markov_homogeneous [DecidableEq S] [Nonempty S] {P : Matrix S S ℝ}
    (hP : SS.IsMarkov P) (hirr : SS.Irreducible P) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {v : S → ℝ}
    (hv : ∀ s, 0 < v s) (hvfix : ∀ s, v s = ku_ces β ρ (c s) (SS.kpR (1 - γ) P v s)) {l : ℝ}
    (hl : 0 < l) {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (hwfix : ∀ s, w s = ku_ces β ρ (l * c s) (SS.kpR (1 - γ) P w s)) : w = l • v := by
  obtain ⟨u, _, _, huniq, _⟩ := ku_ez_markov hP hirr (c := fun s => l * c s)
    (fun s => mul_pos hl (hc s)) hβ0 hβ1 hρ hγ
  have hlv : ∀ s, 0 < (l • v) s := fun s => by simpa using mul_pos hl (hv s)
  have hK : SS.kpR (1 - γ) P (l • v) = l • SS.kpR (1 - γ) P v :=
    SS.posHomogeneous_kpR (sub_ne_zero.2 (Ne.symm hγ)) hP v hv l hl.le hlv
  have hfix' : ∀ s, (l • v) s = ku_ces β ρ (l * c s) (SS.kpR (1 - γ) P (l • v) s) := by
    intro s
    rw [hK, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      ku_ces_homog hρ hβ0.le hβ1.le hl (hc s).le (SS.kpR_pos hP hv s).le, ← hvfix s]
  rw [huniq w hw hwfix, huniq _ hlv hfix']

/-! ### Weil's exponential certainty equivalent and (20.4) -/

/-- Miao, p. 686: Weil's exponential certainty equivalent `M_t(x) = −(1/γ) log E_t[exp(−γx)]`. -/
noncomputable def ku_expCE (P : Matrix S S ℝ) (γ : ℝ) (t : ℕ) (x : (ℕ → S) → ℝ) :
    (ℕ → S) → ℝ :=
  fun ω => -(1 / γ) * Real.log (ku_E P t (fun ω' => Real.exp (-γ * x ω')) ω)

/-- Miao, p. 686: the exponential certainty equivalent is a conditional certainty equivalent on
all real random variables. -/
theorem ku_expCE_isCE {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 0) :
    definition_20_2_3 Set.univ (ku_expCE P γ) := by
  intro t
  refine ⟨fun x hx => ?_, ?_, fun α _ _ => ?_⟩
  · have hm : ku_Meas (t + 1) fun ω => Real.exp (-γ * x ω) := fun ω ω' h => by
      change Real.exp (-γ * x ω) = Real.exp (-γ * x ω')
      rw [hx ω ω' h]
    intro ω ω' h
    simp only [ku_expCE]
    rw [ku_E_meas P hm ω ω' h]
  · refine Continuous.continuousOn (continuous_pi fun ω => ?_)
    refine continuous_const.mul (Continuous.log ?_ fun x => ?_)
    · exact continuous_finsetSum _ fun s' _ => continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _)))
    · exact (ku_E_pos hP (x := fun ω' => Real.exp (-γ * x ω')) (fun _ => Real.exp_pos _)
        t ω).ne'
  · funext ω
    simp only [ku_expCE, ku_E]
    rw [← Finset.sum_mul, hP.rowsum, one_mul, Real.log_exp]
    field_simp

/-- Miao, p. 686: the exponential certainty equivalent is translation invariant:
`M_t(x + a) = M_t(x) + a` for `F_t`-measurable `a`. -/
theorem ku_expCE_translation {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 0)
    (t : ℕ) (x : (ℕ → S) → ℝ) {a : (ℕ → S) → ℝ} (ha : ku_Meas t a) (ω : ℕ → S) :
    ku_expCE P γ t (x + a) ω = ku_expCE P γ t x ω + a ω := by
  have hE := ku_E_pos hP (x := fun ω' => Real.exp (-γ * x ω')) (fun _ => Real.exp_pos _) t ω
  have e : ku_E P t (fun ω' => Real.exp (-γ * (x + a) ω')) ω =
      Real.exp (-γ * a ω) * ku_E P t (fun ω' => Real.exp (-γ * x ω')) ω := by
    simp only [ku_E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    have h1 : a (Function.update ω (t + 1) s') = a ω :=
      ha _ _ fun s hs => by rw [Function.update_of_ne (by omega)]
    rw [Pi.add_apply, h1, mul_add, Real.exp_add]
    ring
  simp only [ku_expCE]
  rw [e, Real.log_mul (Real.exp_pos _).ne' hE.ne', Real.log_exp]
  field_simp
  ring

/-- Miao, (20.4), p. 686: with the CES aggregator and Weil's certainty equivalent, (20.2) reads
`U_t = [(1 − β)c_t^{1−ρ} + β(−(1/γ) log E_t exp(−γU_{t+1}))^{1−ρ}]^{1/(1−ρ)}`. -/
theorem eq_20_4 (P : Matrix S S ℝ) (β ρ γ : ℝ) (C : Set (ℕ → (ℕ → S) → ℝ))
    (U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ) :
    eq_20_2 C U (ku_ces β ρ) (ku_expCE P γ) ↔
      ∀ c ∈ C, ∀ t ω, U c t ω = ((1 - β) * c t ω ^ (1 - ρ) +
        β * (-(1 / γ) * Real.log (ku_E P t (fun ω' => Real.exp (-γ * U c (t + 1) ω')) ω)) ^
          (1 - ρ)) ^ (1 - ρ)⁻¹ :=
  Iff.rfl

/-! ### The limit `ρ → 1` and (20.5) -/

/-- Miao, p. 686: as `ρ → 1` the CES aggregator tends to the Cobb–Douglas aggregator
`x^{1−β}y^β`. -/
theorem ku_ces_limit {β x y : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun ρ => ku_ces β ρ x y) (𝓝[≠] 1) (𝓝 (x ^ (1 - β) * y ^ β)) := by
  have hh : HasDerivAt (fun r : ℝ => (1 - β) * x ^ r + β * y ^ r)
      ((1 - β) * (x ^ (0 : ℝ) * Real.log x) + β * (y ^ (0 : ℝ) * Real.log y)) (0 : ℝ) :=
    ((Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt.const_mul _).add
      ((Real.hasStrictDerivAt_const_rpow hy 0).hasDerivAt.const_mul _)
  have h0 : (1 - β) * x ^ (0 : ℝ) + β * y ^ (0 : ℝ) = 1 := by simp
  have hg := hh.log (by rw [h0]; exact one_ne_zero)
  rw [h0, div_one, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul] at hg
  have hslope := hg.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at hslope
  rw [h0, Real.log_one] at hslope
  simp only [sub_zero] at hslope
  have hr : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ρ hρ => ?_⟩
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact sub_ne_zero.2 (Ne.symm hρ)
  have hlim := (Real.continuous_exp.tendsto _).comp (hslope.comp hr)
  have hval : Real.exp ((1 - β) * Real.log x + β * Real.log y) = x ^ (1 - β) * y ^ β := by
    rw [Real.exp_add, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, mul_comm (1 - β),
      mul_comm β]
  rw [← hval]
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ρ hρ => ?_)
  have hpos : 0 < (1 - β) * x ^ (1 - ρ) + β * y ^ (1 - ρ) := by
    have h1 := Real.rpow_pos_of_pos hx (1 - ρ)
    have h2 := Real.rpow_pos_of_pos hy (1 - ρ)
    rcases lt_or_eq_of_le hβ1 with h | h
    · have : 0 < 1 - β := by linarith
      positivity
    · rw [h]
      linarith
  simp only [Function.comp_def]
  rw [ku_ces, Real.rpow_def_of_pos hpos, mul_comm]

/-- Miao, (20.5), p. 686: with the limiting aggregator `W(x, y) = x^{1−β}y^β` and the
Kreps–Porteus certainty equivalent, `V_t = log U_t` satisfies
`V_t = (1 − β) log c_t + β/(1 − γ) log E_t exp((1 − γ)V_{t+1})`. -/
theorem eq_20_5 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β γ : ℝ}
    {C : Set (ℕ → (ℕ → S) → ℝ)} {U : (ℕ → (ℕ → S) → ℝ) → ℕ → (ℕ → S) → ℝ}
    (hrec : eq_20_2 C U (fun x y => x ^ (1 - β) * y ^ β) (ku_kpCE P γ))
    {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ C) (hcpos : ∀ t ω, 0 < c t ω) (hU : ∀ t ω, 0 < U c t ω)
    (t : ℕ) (ω : ℕ → S) :
    Real.log (U c t ω) = (1 - β) * Real.log (c t ω) + β / (1 - γ) *
      Real.log (ku_E P t (fun ω' => Real.exp ((1 - γ) * Real.log (U c (t + 1) ω'))) ω) := by
  have hE := ku_E_pos hP (x := fun ω' => U c (t + 1) ω' ^ (1 - γ))
    (fun ω' => Real.rpow_pos_of_pos (hU _ ω') _) t ω
  have e : (fun ω' => Real.exp ((1 - γ) * Real.log (U c (t + 1) ω'))) =
      fun ω' => U c (t + 1) ω' ^ (1 - γ) := funext fun ω' => by
    rw [Real.rpow_def_of_pos (hU _ ω'), mul_comm]
  rw [hrec c hc t ω, e, Real.log_mul (Real.rpow_pos_of_pos (hcpos t ω) _).ne'
    (Real.rpow_pos_of_pos (ku_kpCE_pos hP γ (hU (t + 1)) t ω) _).ne',
    Real.log_rpow (hcpos t ω), Real.log_rpow (ku_kpCE_pos hP γ (hU (t + 1)) t ω), ku_kpCE,
    Real.log_rpow hE]
  ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Chew–Dekel risk aggregator (§20.2.1, (20.6))

Miao §20.2.1, pp. 687–691: static preferences over consumption `c : S → ℝ₊` on a finite state
space with probabilities `p`, their certainty equivalents, the Allais paradox, the Chew–Dekel
class (20.6) and its members, and their recursive versions.

* `ku_ce_unique`, `ku_ce_exists`, `ku_ce_counterexample`: if `U` is strictly increasing along
  constants the certainty equivalent `μ` with `U(μ, …, μ) = U(c)` is unique; it exists when in
  addition `U` is monotone and continuous along constants; without continuity it may not exist,
  although the book's "If `U` is strictly increasing, then there is a unique `μ`" says it does.
* `ku_allais`, `ku_allais_u0`, `ku_allais_paradox`: under expected utility `a₁ ≽ a₂` iff
  `a₃ ≽ a₄` (the printed display, with `u(0) = 0`, lacks the `≥`); hence `a₁ ≻ a₂` and `a₄ ≻ a₃`
  cannot both hold.
* `eq_20_6`: the Chew–Dekel equation `μ = ∑ p(s)M(c(s), μ)`.
* Expected utility `M(c, m) = c^αm^{1−α}/α + m(1 − 1/α)`: properties (i)–(iv)
  (`ku_euM_i`, `ku_euM_ii`, `ku_euM_iii`, `ku_euM_iv`) and `μ = (∑ p c^α)^{1/α}`
  (`ku_euM_ce`). Property (iv) holds as `M(kc, km) = kM(c, m)`; as printed, `M(kc, m) = kM(c, m)`,
  it fails (`ku_euM_iv_misprint`).
* Weighted utility: `ku_wM_i`, `ku_wM_ce` (`μ = (∑ p c^{γ+α}/∑ p c^γ)^{1/α} = (∑ p̂ c^α)^{1/α}`),
  `ku_wM_params` (the parameter implications), `ku_wM_local` (`∂M/∂c = 1` and
  `∂²M/∂c² = (α + 2γ − 1)/m` at `c = m`, so (i) or (ii) gives local concavity), and
  `ku_wM_params_not_necessary` (`γ = 0`, `α = 1/2` is increasing and concave though neither (i)
  nor (ii) holds: the conditions are sufficient, not necessary).
* Disappointment aversion: `ku_gulM_i`, `ku_gulM_zero` (`δ = 0` is expected utility),
  `ku_gulM_ce` (`μ^α = ∑ p c^α − δ ∑ p 1(c < μ)(μ^α − c^α)`), `ku_gulM_ce_hat` (`= ∑ p̂ c^α` with
  `p̂(s) = p(s)(1 + δ1(c(s) < μ))/(1 + δ∑ p 1(c < μ))`; the printed `p̂` omits the factor `p(s)`,
  `ku_gulM_hat_misprint`).
* `ku_recWeighted_ce`, `ku_recWeighted`, `ku_recGul`: the recursive weighted and disappointment
  aversion utilities use the static certainty equivalents at each node, with `p = π(·|s_t)`.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-! ### Certainty equivalents and the Allais paradox -/

omit [Fintype S] in
/-- Miao, p. 688: if `m ↦ U(m, …, m)` is strictly increasing, the certainty equivalent is unique. -/
theorem ku_ce_unique {U : (S → ℝ) → ℝ} (hU : StrictMono fun m : ℝ => U fun _ => m)
    {c : S → ℝ} {μ μ' : ℝ} (h : U (fun _ => μ) = U c) (h' : U (fun _ => μ') = U c) : μ = μ' :=
  hU.injective (h.trans h'.symm)

omit [Fintype S] in
/-- Miao, p. 688: if `U` is monotone and continuous along constants, the certainty equivalent
`μ` with `U(μ, …, μ) = U(c)` exists, between `min c` and `max c`. -/
theorem ku_ce_exists [Finite S] [Nonempty S] {U : (S → ℝ) → ℝ} (hmono : Monotone U)
    (hcont : Continuous fun m : ℝ => U fun _ => m) (c : S → ℝ) :
    ∃ μ, U (fun _ => μ) = U c := by
  have := Fintype.ofFinite S
  set m₀ := Finset.univ.inf' Finset.univ_nonempty c
  set m₁ := Finset.univ.sup' Finset.univ_nonempty c
  have h0 : (fun _ : S => m₀) ≤ c := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  have h1 : c ≤ fun _ : S => m₁ := fun s => Finset.le_sup' c (Finset.mem_univ s)
  have h01 : m₀ ≤ m₁ := (h0 (Classical.arbitrary S)).trans (h1 (Classical.arbitrary S))
  obtain ⟨μ, _, hμ⟩ := intermediate_value_Icc h01 hcont.continuousOn ⟨hmono h0, hmono h1⟩
  exact ⟨μ, hμ⟩

/-- Counterexample (Miao, p. 688): a utility strictly increasing in each state need not have a
certainty equivalent. With two states and `f(x) = x + 1` for `x > 0`, `f(x) = x` otherwise,
`U(c) = f(c₁) + f(c₂)` is strictly increasing, but `U(1, 0) = 2 ≠ 2f(μ)` for every `μ`. -/
theorem ku_ce_counterexample :
    let f : ℝ → ℝ := fun x => if 0 < x then x + 1 else x
    let U : (Bool → ℝ) → ℝ := fun c => ∑ b, f (c b)
    (∀ c c' : Bool → ℝ, c ≤ c' → c ≠ c' → U c < U c') ∧
      ¬ ∃ μ, U (fun _ => μ) = U fun b => if b then 1 else 0 := by
  intro f U
  have hf : StrictMono f := by
    intro x y hxy
    simp only [f]
    split_ifs <;> linarith
  refine ⟨fun c c' hle hne => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, c b ≠ c' b := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact Finset.sum_lt_sum (fun i _ => hf.monotone (hle i))
      ⟨b, Finset.mem_univ _, hf (lt_of_le_of_ne (hle b) hb)⟩
  · rintro ⟨μ, hμ⟩
    simp only [U, f, Fintype.univ_bool] at hμ
    norm_num at hμ
    split_ifs at hμ with h <;> linarith

/-- Miao, p. 687: the Allais choices under expected utility. With `u₁ = u(1M)`, `u₅ = u(5M)`,
`u₀ = u(0)`: `a₁ ≽ a₂` iff `a₃ ≽ a₄`. -/
theorem ku_allais (u₁ u₅ u₀ : ℝ) :
    (0.1 * u₅ + 0.89 * u₁ + 0.01 * u₀ ≤ u₁) ↔ (0.1 * u₅ + 0.9 * u₀ ≤ 0.11 * u₁ + 0.89 * u₀) := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 687 (corrected display): with `u(0) = 0`,
`u(1M) ≥ 0.1u(5M) + 0.89u(1M)` iff `0.11u(1M) ≥ 0.1u(5M)`. -/
theorem ku_allais_u0 (u₁ u₅ : ℝ) : (0.1 * u₅ + 0.89 * u₁ ≤ u₁) ↔ (0.1 * u₅ ≤ 0.11 * u₁) := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 688: the Allais paradox: no expected utility gives `a₁ ≻ a₂` and `a₄ ≻ a₃`. -/
theorem ku_allais_paradox (u₁ u₅ u₀ : ℝ) :
    ¬ ((0.1 * u₅ + 0.89 * u₁ + 0.01 * u₀ < u₁) ∧
      (0.11 * u₁ + 0.89 * u₀ < 0.1 * u₅ + 0.9 * u₀)) := by
  rintro ⟨h1, h2⟩
  linarith

/-! ### The Chew–Dekel class -/

/-- A probability-weighted sum of positive numbers is positive. -/
theorem ku_wsum_pos {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {f : S → ℝ}
    (hf : ∀ s, 0 < f s) : 0 < ∑ s, p s * f s := by
  obtain ⟨s, hs⟩ : ∃ s, 0 < p s := by
    by_contra h
    push Not at h
    have : ∑ s, p s = 0 := Finset.sum_eq_zero fun s _ => le_antisymm (h s) (hp s)
    linarith
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hp i) (hf i).le)
    ⟨s, Finset.mem_univ _, mul_pos hs (hf s)⟩

/-- Miao, (20.6), p. 688: `μ` is the Chew–Dekel certainty equivalent of `c` for the risk aggregator
`M`: `μ = ∑ p(s)M(c(s), μ)`. -/
def eq_20_6 (p : S → ℝ) (M : ℝ → ℝ → ℝ) (c : S → ℝ) (μ : ℝ) : Prop :=
  μ = ∑ s, p s * M (c s) μ

/-- The expected-utility risk aggregator `M(c, m) = c^αm^{1−α}/α + m(1 − 1/α)` (p. 689). -/
noncomputable def ku_euM (α c m : ℝ) : ℝ := c ^ α * m ^ (1 - α) / α + m * (1 - 1 / α)

/-- Miao, p. 689, property (i): `M(m, m) = m`. -/
theorem ku_euM_i {α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_euM α m m = m := by
  unfold ku_euM
  rw [← Real.rpow_add hm, add_sub_cancel, Real.rpow_one]
  field_simp
  ring

/-- Miao, p. 689, property (ii): `M` is (strictly) increasing in `c`. -/
theorem ku_euM_ii {α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) :
    StrictMonoOn (fun c => ku_euM α c m) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hmα := Real.rpow_pos_of_pos hm (1 - α)
  simp only [ku_euM]
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have h1 : y ^ α < x ^ α := Real.rpow_lt_rpow_of_neg hx0 hxy hneg
    have h2 : x ^ α * m ^ (1 - α) / α < y ^ α * m ^ (1 - α) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_neg_right (mul_lt_mul_of_pos_right h1 hmα) (inv_lt_zero.2 hneg)
    linarith
  · have h1 : x ^ α < y ^ α := Real.rpow_lt_rpow hx0.le hxy hpos
    have h2 : x ^ α * m ^ (1 - α) / α < y ^ α * m ^ (1 - α) / α :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h1 hmα) hpos
    linarith

/-- Miao, p. 689, property (iii): for `α ≤ 1`, `M` is concave in `c`. -/
theorem ku_euM_iii {α m : ℝ} (hα : α ≠ 0) (hα1 : α ≤ 1) (hm : 0 < m) :
    ConcaveOn ℝ (Set.Ioi 0) (fun c => ku_euM α c m) := by
  have hmα := Real.rpow_pos_of_pos hm (1 - α)
  have e : (fun c => ku_euM α c m) = fun c => (m ^ (1 - α) / α) • c ^ α + m * (1 - 1 / α) := by
    funext c
    simp only [ku_euM, smul_eq_mul]
    ring
  rw [e]
  refine ConcaveOn.add_const ?_ _
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have hK : 0 ≤ -(m ^ (1 - α) / α) := by
      have : m ^ (1 - α) / α < 0 := div_neg_of_pos_of_neg hmα hneg
      linarith
    have h1 := (SS.convexOn_rpow_of_neg hneg).smul hK
    have h2 := neg_concaveOn_iff.2 h1
    convert h2 using 1
    funext c
    simp
  · exact ((Real.concaveOn_rpow hpos.le hα1).subset Set.Ioi_subset_Ici_self
      (convex_Ioi 0)).smul (div_pos hmα hpos).le

/-- Miao, p. 689, property (iv) (corrected): linear homogeneity `M(kc, km) = kM(c, m)`. -/
theorem ku_euM_iv {α k c m : ℝ} (hk : 0 < k) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    ku_euM α (k * c) (k * m) = k * ku_euM α c m := by
  unfold ku_euM
  rw [Real.mul_rpow hk.le hc, Real.mul_rpow hk.le hm,
    show k ^ α * c ^ α * (k ^ (1 - α) * m ^ (1 - α)) =
      (k ^ α * k ^ (1 - α)) * (c ^ α * m ^ (1 - α)) by ring,
    ← Real.rpow_add hk, add_sub_cancel, Real.rpow_one]
  ring

/-- Miao, p. 689 (misprint): property (iv) as printed, `M(kc, m) = kM(c, m)`, fails for the
expected-utility aggregator (`α = −1`, `k = 2`, `c = m = 1`). -/
theorem ku_euM_iv_misprint : ku_euM (-1) (2 * 1) 1 ≠ 2 * ku_euM (-1) 1 1 := by
  unfold ku_euM
  rw [mul_one, Real.rpow_neg_one, Real.one_rpow, Real.one_rpow]
  norm_num

/-- Miao, p. 689: for the expected-utility aggregator, (20.6) holds iff
`μ = (∑ p(s)c(s)^α)^{1/α}`. -/
theorem ku_euM_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {α : ℝ} (hα : α ≠ 0)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_euM α) c μ ↔ μ = (∑ s, p s * c s ^ α) ^ α⁻¹ := by
  set A := ∑ s, p s * c s ^ α
  have hA : 0 < A :=
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hc s) _
  have hb := Real.rpow_pos_of_pos hμ α
  have e1 : μ ^ (1 - α) = μ / μ ^ α := by rw [Real.rpow_sub hμ, Real.rpow_one]
  have hsum : ∑ s, p s * ku_euM α (c s) μ = μ / μ ^ α * A / α + μ * (1 - 1 / α) := by
    have : ∀ s, p s * ku_euM α (c s) μ =
        μ / μ ^ α / α * (p s * c s ^ α) + μ * (1 - 1 / α) * p s := fun s => by
      simp only [ku_euM, e1]
      ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, A]
    ring
  unfold eq_20_6
  rw [hsum]
  constructor
  · intro h
    have h2 : μ ^ α = A := by
      have h4 : μ * (1 - 1 / α) = μ - μ / α := by ring
      have h3 : μ / α = μ / μ ^ α * A / α := by linarith
      field_simp at h3
      linarith
    rw [← h2, Real.rpow_rpow_inv hμ.le hα]
  · intro h
    have h2 : μ ^ α = A := by rw [h, Real.rpow_inv_rpow hA.le hα]
    rw [h2]
    field_simp
    ring

/-! ### Weighted utility -/

/-- Chew's weighted-utility risk aggregator
`M(c, m) = (c/m)^γ c^αm^{1−α}/α + m(1 − (c/m)^γ/α)` (p. 689). -/
noncomputable def ku_wM (γ α c m : ℝ) : ℝ :=
  (c / m) ^ γ * c ^ α * m ^ (1 - α) / α + m * (1 - (c / m) ^ γ / α)

/-- Miao, p. 689: property (i) for weighted utility, `M(m, m) = m`. -/
theorem ku_wM_i {γ α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_wM γ α m m = m := by
  unfold ku_wM
  rw [div_self hm.ne', Real.one_rpow, one_mul, ← Real.rpow_add hm, add_sub_cancel,
    Real.rpow_one]
  field_simp
  ring

/-- With `γ = 0` weighted utility is expected utility. -/
theorem ku_wM_zero (α c m : ℝ) : ku_wM 0 α c m = ku_euM α c m := by
  simp [ku_wM, ku_euM]

/-- Miao, p. 689: for weighted utility, (20.6) holds iff
`μ = (∑ p c^{γ+α}/∑ p c^γ)^{1/α}`, and this equals `(∑ p̂ c^α)^{1/α}` with
`p̂(s) = p(s)c(s)^γ/∑ p c^γ`. -/
theorem ku_wM_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {γ α : ℝ} (hα : α ≠ 0)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) {μ : ℝ} (hμ : 0 < μ) :
    (eq_20_6 p (ku_wM γ α) c μ ↔
      μ = ((∑ s, p s * c s ^ (γ + α)) / ∑ s, p s * c s ^ γ) ^ α⁻¹) ∧
      (∑ s, p s * c s ^ (γ + α)) / (∑ s, p s * c s ^ γ) =
        ∑ s, (p s * c s ^ γ / ∑ s', p s' * c s' ^ γ) * c s ^ α := by
  have hpos : ∀ e : ℝ, 0 < ∑ s, p s * c s ^ e := fun e =>
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hc s) _
  set A := ∑ s, p s * c s ^ (γ + α)
  set B := ∑ s, p s * c s ^ γ
  have hA := hpos (γ + α)
  have hB : 0 < B := hpos γ
  have ha := Real.rpow_pos_of_pos hμ (-γ)
  have hb := Real.rpow_pos_of_pos hμ (-α)
  have e1 : ∀ s, (c s / μ) ^ γ = c s ^ γ * μ ^ (-γ) := fun s => by
    rw [Real.div_rpow (hc s).le hμ.le, Real.rpow_neg hμ.le, div_eq_mul_inv]
  have e2 : μ ^ (1 - α) = μ * μ ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hμ, Real.rpow_one]
  have e3 : ∀ s, c s ^ γ * c s ^ α = c s ^ (γ + α) := fun s => (Real.rpow_add (hc s) _ _).symm
  have hsum : ∑ s, p s * ku_wM γ α (c s) μ =
      μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α := by
    simp only [ku_wM, e1, e2]
    have : ∀ s, p s * (c s ^ γ * μ ^ (-γ) * c s ^ α * (μ * μ ^ (-α)) / α +
        μ * (1 - c s ^ γ * μ ^ (-γ) / α)) =
        μ ^ (-γ) * μ * μ ^ (-α) / α * (p s * (c s ^ γ * c s ^ α)) + μ * p s -
          μ * μ ^ (-γ) / α * (p s * c s ^ γ) := fun s => by ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e3,
      hp1, A, B]
    ring
  refine ⟨?_, ?_⟩
  · unfold eq_20_6
    rw [hsum]
    have key : μ = μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α ↔
        μ ^ (-α) * A = B := by
      constructor
      · intro h
        have h1 : μ ^ (-γ) * μ * (μ ^ (-α) * A - B) / α =
            (μ ^ (-γ) * μ * μ ^ (-α) * A / α + μ - μ * μ ^ (-γ) * B / α) - μ := by ring
        rw [← h, sub_self] at h1
        rcases div_eq_zero_iff.1 h1 with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · rcases mul_eq_zero.1 h3 with h4 | h4
            · exact absurd h4 ha.ne'
            · exact absurd h4 hμ.ne'
          · linarith
        · exact absurd h2 hα
      · intro h
        have : μ ^ (-γ) * μ * μ ^ (-α) * A = μ * μ ^ (-γ) * B := by rw [← h]; ring
        rw [this]
        ring
    rw [key]
    have hma : μ ^ (-α) = (μ ^ α)⁻¹ := Real.rpow_neg hμ.le α
    have hmα := Real.rpow_pos_of_pos hμ α
    constructor
    · intro h
      have h2 : μ ^ α = A / B := by
        rw [hma] at h
        field_simp at h
        rw [eq_div_iff hB.ne']
        linarith
      rw [← h2, Real.rpow_rpow_inv hμ.le hα]
    · intro h
      have h2 : μ ^ α = A / B := by rw [h, Real.rpow_inv_rpow (div_pos hA hB).le hα]
      rw [hma, h2]
      field_simp
      exact div_self hA.ne'
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← e3 s]
    ring

/-- Miao, p. 689: the parameter conditions for weighted utility: (i) `0 < γ < 1`, `α + γ < 0`
implies `α < 0`; (ii) `γ < 0`, `0 < α + γ < 1` implies `α > 0`; both imply `α + 2γ < 1`. -/
theorem ku_wM_params {γ α : ℝ} :
    ((0 < γ ∧ γ < 1 ∧ α + γ < 0) → α < 0 ∧ α + 2 * γ < 1) ∧
      ((γ < 0 ∧ 0 < α + γ ∧ α + γ < 1) → 0 < α ∧ α + 2 * γ < 1) := by
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨by linarith, by linarith⟩,
    fun ⟨h1, h2, h3⟩ => ⟨by linarith, by linarith⟩⟩

/-- The weighted aggregator in power form, `M(c, m) = c^{γ+α}m^{1−α−γ}/α + m − c^γm^{1−γ}/α`. -/
theorem ku_wM_eq {γ α c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ku_wM γ α c m = c ^ (γ + α) * m ^ (1 - α - γ) / α + m - c ^ γ * m ^ (1 - γ) / α := by
  unfold ku_wM
  have e1 : (c / m) ^ γ = c ^ γ * m ^ (-γ) := by
    rw [Real.div_rpow hc.le hm.le, Real.rpow_neg hm.le, div_eq_mul_inv]
  have e2 : c ^ (γ + α) = c ^ γ * c ^ α := Real.rpow_add hc _ _
  have e3 : m ^ (1 - α - γ) = m ^ (-γ) * m ^ (1 - α) := by
    rw [← Real.rpow_add hm]; ring_nf
  have e4 : m ^ (1 - γ) = m * m ^ (-γ) := by
    rw [sub_eq_add_neg, Real.rpow_add hm, Real.rpow_one]
  rw [e1, e2, e3, e4]
  ring

/-- Miao, p. 689: near `c = m` the weighted aggregator has slope `1` and curvature
`(α + 2γ − 1)/m`; so (i) or (ii) (which give `α + 2γ < 1`, `ku_wM_params`) makes `M` increasing
and strictly concave in `c` near `m`. -/
theorem ku_wM_local {γ α m : ℝ} (hα : α ≠ 0) (hm : 0 < m) :
    ∃ D : ℝ → ℝ, (∀ c, 0 < c → HasDerivAt (fun c => ku_wM γ α c m) (D c) c) ∧ D m = 1 ∧
      HasDerivAt D ((α + 2 * γ - 1) / m) m := by
  let D : ℝ → ℝ := fun c => ((γ + α) * c ^ (γ + α - 1) * m ^ (1 - α - γ) -
    γ * c ^ (γ - 1) * m ^ (1 - γ)) / α
  refine ⟨D, fun c hc => ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun c => c ^ (γ + α) * m ^ (1 - α - γ) / α + m -
        c ^ γ * m ^ (1 - γ) / α) (D c) c := by
      have ha := ((Real.hasDerivAt_rpow_const (p := γ + α) (Or.inl hc.ne')).mul_const
        (m ^ (1 - α - γ))).div_const α
      have hb := ((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hc.ne')).mul_const
        (m ^ (1 - γ))).div_const α
      convert (ha.add_const m).sub hb using 1
      simp only [D]
      ring
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hc] with x hx
    exact ku_wM_eq hx hm
  · have e1 : m ^ (γ + α - 1) * m ^ (1 - α - γ) = 1 := by
      rw [← Real.rpow_add hm, show γ + α - 1 + (1 - α - γ) = 0 by ring, Real.rpow_zero]
    have e2 : m ^ (γ - 1) * m ^ (1 - γ) = 1 := by
      rw [← Real.rpow_add hm, show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero]
    simp only [D]
    rw [mul_assoc (γ + α), e1, mul_assoc γ, e2]
    field_simp
    ring
  · have ha := ((Real.hasDerivAt_rpow_const (p := γ + α - 1) (Or.inl hm.ne')).const_mul
      (γ + α)).mul_const (m ^ (1 - α - γ))
    have hb := ((Real.hasDerivAt_rpow_const (p := γ - 1) (Or.inl hm.ne')).const_mul γ).mul_const
      (m ^ (1 - γ))
    convert (ha.sub hb).div_const α using 1
    have e1 : m ^ (γ + α - 1 - 1) * m ^ (1 - α - γ) = m⁻¹ := by
      rw [← Real.rpow_add hm, show γ + α - 1 - 1 + (1 - α - γ) = -1 by ring, Real.rpow_neg_one]
    have e2 : m ^ (γ - 1 - 1) * m ^ (1 - γ) = m⁻¹ := by
      rw [← Real.rpow_add hm, show γ - 1 - 1 + (1 - γ) = -1 by ring, Real.rpow_neg_one]
    calc (α + 2 * γ - 1) / m
        = ((γ + α) * (γ + α - 1) * (m ^ (γ + α - 1 - 1) * m ^ (1 - α - γ)) -
            γ * (γ - 1) * (m ^ (γ - 1 - 1) * m ^ (1 - γ))) / α := by
          rw [e1, e2]
          field_simp
          ring
      _ = _ := by ring

/-- Miao, p. 689: the conditions (i)–(ii) are not necessary for `M` to be increasing and concave
near `m`: `γ = 0`, `α = 1/2` satisfies neither, yet `M(·, m)` is increasing and concave on
`(0, ∞)`. -/
theorem ku_wM_params_not_necessary {m : ℝ} (hm : 0 < m) :
    ¬ ((0 < (0 : ℝ) ∧ (0 : ℝ) < 1 ∧ (1 / 2 : ℝ) + 0 < 0) ∨
        ((0 : ℝ) < 0 ∧ 0 < (1 / 2 : ℝ) + 0 ∧ (1 / 2 : ℝ) + 0 < 1)) ∧
      StrictMonoOn (fun c => ku_wM 0 (1 / 2) c m) (Set.Ioi 0) ∧
      ConcaveOn ℝ (Set.Ioi 0) (fun c => ku_wM 0 (1 / 2) c m) := by
  have e : (fun c => ku_wM 0 (1 / 2) c m) = fun c => ku_euM (1 / 2) c m :=
    funext fun c => ku_wM_zero _ c m
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [e]; exact ku_euM_ii (by norm_num) hm
  · rw [e]; exact ku_euM_iii (by norm_num) (by norm_num) hm

/-! ### Disappointment aversion -/

/-- Gul's disappointment-aversion risk aggregator (p. 690). -/
noncomputable def ku_gulM (α δ c m : ℝ) : ℝ :=
  if m ≤ c then ku_euM α c m else ku_euM α c m + δ * ((c ^ α * m ^ (1 - α) - m) / α)

/-- Miao, p. 690: property (i), `M(m, m) = m`. -/
theorem ku_gulM_i {α δ m : ℝ} (hα : α ≠ 0) (hm : 0 < m) : ku_gulM α δ m m = m := by
  simp only [ku_gulM, le_refl, ↓reduceIte]
  exact ku_euM_i hα hm

/-- Miao, p. 690: with `δ = 0` disappointment aversion is expected utility. -/
theorem ku_gulM_zero (α c m : ℝ) : ku_gulM α 0 c m = ku_euM α c m := by
  simp [ku_gulM]

/-- Miao, p. 690: for disappointment aversion, (20.6) holds iff
`μ^α = ∑ p c^α − δ ∑ p 1(c < μ)(μ^α − c^α)`. -/
theorem ku_gulM_ce {p : S → ℝ} (hp1 : ∑ s, p s = 1) {α δ : ℝ} (hα : α ≠ 0) (c : S → ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_gulM α δ) c μ ↔
      μ ^ α = ∑ s, p s * c s ^ α -
        δ * ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) := by
  have hb := Real.rpow_pos_of_pos hμ (-α)
  have hmα := Real.rpow_pos_of_pos hμ α
  have hma : μ ^ (-α) * μ ^ α = 1 := by
    rw [← Real.rpow_add hμ, neg_add_cancel, Real.rpow_zero]
  have e2 : μ ^ (1 - α) = μ * μ ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hμ, Real.rpow_one]
  have hterm : ∀ s, p s * ku_gulM α δ (c s) μ =
      μ * μ ^ (-α) / α * (p s * c s ^ α) + μ * (1 - 1 / α) * p s +
        δ * μ / α * (μ ^ (-α) * (p s * (if c s < μ then 1 else 0) * c s ^ α) -
          p s * (if c s < μ then 1 else 0)) := fun s => by
    simp only [ku_gulM, ku_euM, e2]
    by_cases h : μ ≤ c s
    · simp only [h, ↓reduceIte, not_lt.2 h]
      ring
    · simp only [h, ↓reduceIte, not_le.1 h]
      ring
  unfold eq_20_6
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1]
  set A := ∑ s, p s * c s ^ α
  set I := ∑ s, p s * (if c s < μ then 1 else 0)
  set J := ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α
  have hJ : ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) = μ ^ α * I - J := by
    simp only [I, J, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hJ, Real.rpow_neg hμ.le]
  set q := μ ^ α
  have key : μ * q⁻¹ / α * A + μ * (1 - 1 / α) * 1 + δ * μ / α * (q⁻¹ * J - I) - μ =
      μ / (α * q) * (A - q + δ * (J - q * I)) := by
    field_simp
    ring
  have hne : μ / (α * q) ≠ 0 := div_ne_zero hμ.ne' (mul_ne_zero hα hmα.ne')
  constructor
  · intro h
    have h1 : μ / (α * q) * (A - q + δ * (J - q * I)) = 0 := by rw [← key]; linarith
    have h2 := (mul_eq_zero.1 h1).resolve_left hne
    linarith
  · intro h
    have h1 : A - q + δ * (J - q * I) = 0 := by linarith
    have h2 := key
    rw [h1, mul_zero] at h2
    linarith

/-- Miao, p. 690 (corrected): the disappointment-aversion certainty equivalent is
`μ^α = ∑ p̂(s)c(s)^α` with `p̂(s) = p(s)(1 + δ1(c(s) < μ))/(1 + δ∑ p 1(c < μ))`, for `δ ≥ 0`. -/
theorem ku_gulM_ce_hat {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {α δ : ℝ}
    (hα : α ≠ 0) (hδ : 0 ≤ δ) (c : S → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    eq_20_6 p (ku_gulM α δ) c μ ↔
      μ ^ α = ∑ s, p s * (1 + δ * (if c s < μ then 1 else 0)) /
        (1 + δ * ∑ s', p s' * (if c s' < μ then 1 else 0)) * c s ^ α := by
  rw [ku_gulM_ce hp1 hα c hμ]
  set I := ∑ s', p s' * (if c s' < μ then (1 : ℝ) else 0)
  have hI : 0 ≤ I := Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (by split_ifs <;> norm_num)
  have hD : 0 < 1 + δ * I := by nlinarith
  have e : ∑ s, p s * (1 + δ * (if c s < μ then 1 else 0)) / (1 + δ * I) * c s ^ α =
      (∑ s, p s * c s ^ α + δ * ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α) /
        (1 + δ * I) := by
    have h1 : ∀ s, p s * (1 + δ * (if c s < μ then 1 else 0)) / (1 + δ * I) * c s ^ α =
        (p s * c s ^ α + δ * (p s * (if c s < μ then 1 else 0) * c s ^ α)) / (1 + δ * I) :=
      fun s => by ring
    simp only [h1]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e2 : ∑ s, p s * (if c s < μ then 1 else 0) * (μ ^ α - c s ^ α) =
      μ ^ α * I - ∑ s, p s * (if c s < μ then 1 else 0) * c s ^ α := by
    simp only [I, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, e2, eq_div_iff hD.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 690 (misprint): with the printed weights `p̂(s) = (1 + δ1)/(1 + δ∑ p1)` (no factor
`p(s)`), the formula `μ^α = ∑ p̂ c^α` fails: for two equally likely states, `δ = 0` and `c ≡ 1`,
`μ = 1` solves (20.6) but `∑ p̂ c^α = 2`. -/
theorem ku_gulM_hat_misprint {α : ℝ} (hα : α ≠ 0) :
    eq_20_6 (fun _ : Bool => (1 / 2 : ℝ)) (ku_gulM α 0) (fun _ => 1) 1 ∧
      (1 : ℝ) ^ α ≠ ∑ s : Bool, (1 + 0 * (if (1 : ℝ) < 1 then 1 else 0)) /
        (1 + 0 * ∑ _s : Bool, (1 / 2 : ℝ) * (if (1 : ℝ) < 1 then 1 else 0)) *
          (fun _ => (1 : ℝ)) s ^ α := by
  refine ⟨?_, ?_⟩
  · unfold eq_20_6
    simp only [ku_gulM_i hα one_pos, Fintype.univ_bool, Finset.mem_singleton,
      Finset.sum_insert, Finset.sum_singleton, Bool.true_eq_false, not_false_eq_true]
    norm_num
  · simp

/-! ### Recursive weighted and disappointment-aversion utility -/

/-- Miao, p. 690: the conditional certainty equivalent of recursive weighted utility at a node,
`(M_t[U^α])^{1/α}` with `M_t(x) = ∑ (π U^γ/∑ π U^γ) x`, is the static weighted-utility
certainty equivalent for `p = π(·|s_t)`: it solves (20.6). -/
theorem ku_recWeighted_ce {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {γ α : ℝ}
    (hα : α ≠ 0) {u : S → ℝ} (hu : ∀ s, 0 < u s) :
    eq_20_6 p (ku_wM γ α) u
      ((∑ s, (p s * u s ^ γ / ∑ s', p s' * u s' ^ γ) * u s ^ α) ^ α⁻¹) := by
  have hpos : ∀ e : ℝ, 0 < ∑ s, p s * u s ^ e := fun e =>
    ku_wsum_pos hp hp1 fun s => Real.rpow_pos_of_pos (hu s) _
  have h := ku_wM_ce hp hp1 (γ := γ) hα hu (μ := ((∑ s, p s * u s ^ (γ + α)) /
    ∑ s, p s * u s ^ γ) ^ α⁻¹) (Real.rpow_pos_of_pos (div_pos (hpos _) (hpos _)) _)
  rw [← h.2]
  exact h.1.2 rfl

/-- Miao, p. 690: recursive weighted utility
`U_t = [(1 − β)c_t^{1−ρ} + β(M_t[U_{t+1}^α])^{(1−ρ)/α}]^{1/(1−ρ)}` is the CES aggregator applied to
the certainty equivalent `(M_t[U_{t+1}^α])^{1/α}`. -/
theorem ku_recWeighted {β ρ α x m : ℝ} (hm : 0 ≤ m) :
    ku_ces β ρ x (m ^ α⁻¹) = ((1 - β) * x ^ (1 - ρ) + β * m ^ ((1 - ρ) / α)) ^ (1 - ρ)⁻¹ := by
  rw [ku_ces, ← Real.rpow_mul hm, div_eq_inv_mul]

/-- Miao, p. 691: in recursive disappointment-aversion utility, `μ_t` solves
`μ_t^α = ∑ π U_{t+1}^α − δ∑_{Δ_{t+1}} π(μ_t^α − U_{t+1}^α)`, `Δ_{t+1} = {μ_t > U_{t+1}}`, iff it is
the static Gul certainty equivalent (20.6) at the node with `p = π(·|s_t)`. -/
theorem ku_recGul {p : S → ℝ} (hp1 : ∑ s, p s = 1) {α δ : ℝ} (hα : α ≠ 0) (u : S → ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    (μ ^ α = ∑ s, p s * u s ^ α -
        δ * ∑ s ∈ Finset.univ.filter (fun s => u s < μ), p s * (μ ^ α - u s ^ α)) ↔
      eq_20_6 p (ku_gulM α δ) u μ := by
  rw [ku_gulM_ce hp1 hα u hμ, Finset.sum_filter]
  have e : ∀ s, (if u s < μ then p s * (μ ^ α - u s ^ α) else 0) =
      p s * (if u s < μ then 1 else 0) * (μ ^ α - u s ^ α) := fun s => by
    split_ifs <;> ring
  simp only [e]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 20.1: Epstein–Zin utility with a finite horizon

Miao, Exercise 20.1, p. 735 (item 1 of §20.6): the Epstein–Zin utility (20.3) with horizon `T`,
`U_T(c) = c_T`, `U_t(c) = [(1 − β)c_t^{1−ρ} + β(E_t[U_{t+1}^{1−γ}])^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}`.
The exercise asks to prove that `U_t` is strictly concave for `t < T` when `ρ > 0` and `γ > 0`.

* `ku_ezFin`, `ku_ezFin_T`, `ku_ezFin_succ`: the backward recursion; `ku_ezFin_pos`.
* `ku_ezFin_dynUtility`, `ku_ezFin_meas`: `U` is a dynamic utility (Definition 20.2.1) on the
  dates `t ≤ T`.
* `ku_ezFin_homog`: `U_t(λc) = λU_t(c)` (homotheticity).
* `ex_20_1`: `U_t` is concave on positive plans, for `0 ≤ ρ`, `0 ≤ γ` (`ρ, γ ≠ 1`), `0 < β < 1`.
* `ex_20_1_not_strict`: `U_t` is never strictly concave: by homogeneity it is linear along rays
  (`U_t(2c) = (U_t(c) + U_t(3c))/2`). The exercise's claim is false as printed; concavity is
  what holds.
-/

namespace Miao.RecursiveUtility

open Filter Topology

variable {S : Type*} [Fintype S]

/-- The backward recursion of Exercise 20.1, indexed by the number `k` of periods to go. -/
noncomputable def ku_ezAux (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ) :
    ℕ → (ℕ → S) → ℝ
  | 0 => c T
  | k + 1 => fun ω =>
      ku_ces β ρ (c (T - (k + 1)) ω) (ku_kpCE P γ (T - (k + 1)) (ku_ezAux P β ρ γ T c k) ω)

/-- Miao, Exercise 20.1: the finite-horizon Epstein–Zin utility `U_t(c)`. -/
noncomputable def ku_ezFin (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ)
    (t : ℕ) : (ℕ → S) → ℝ :=
  ku_ezAux P β ρ γ T c (T - t)

theorem ku_ezFin_T (P : Matrix S S ℝ) (β ρ γ : ℝ) (T : ℕ) (c : ℕ → (ℕ → S) → ℝ) :
    ku_ezFin P β ρ γ T c T = c T := by
  simp [ku_ezFin, ku_ezAux]

/-- Miao, Exercise 20.1: `U_t = W(c_t, M_t(U_{t+1}))` for `t < T`. -/
theorem ku_ezFin_succ (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (c : ℕ → (ℕ → S) → ℝ)
    (ht : t < T) (ω : ℕ → S) :
    ku_ezFin P β ρ γ T c t ω =
      ku_ces β ρ (c t ω) (ku_kpCE P γ t (ku_ezFin P β ρ γ T c (t + 1)) ω) := by
  obtain ⟨k, hk⟩ : ∃ k, T - t = k + 1 := ⟨T - t - 1, by omega⟩
  have hk' : T - (t + 1) = k := by omega
  have ht' : T - (k + 1) = t := by omega
  simp only [ku_ezFin, hk, hk', ku_ezAux, ht']

/-- The set of positive consumption plans. -/
def ku_PosPlan (S : Type*) : Set (ℕ → (ℕ → S) → ℝ) := {c | ∀ t ω, 0 < c t ω}

omit [Fintype S] in
theorem ku_convex_PosPlan : Convex ℝ (ku_PosPlan S) := by
  intro x hx y hy a b ha hb hab t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with h | h
  · subst h
    rw [zero_add] at hab
    subst hab
    simpa using hy t ω
  · exact add_pos_of_pos_of_nonneg (mul_pos h (hx t ω)) (mul_nonneg hb (hy t ω).le)

theorem ku_ezAux_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ ku_PosPlan S) (k : ℕ) :
    ∀ ω, 0 < ku_ezAux P β ρ γ T c k ω := by
  induction k with
  | zero => exact hc T
  | succ k ih => exact fun ω => ku_ces_pos hβ0 hβ1 (hc _ ω) (ku_kpCE_pos hP γ ih _ ω)

theorem ku_ezFin_pos {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ} (hc : c ∈ ku_PosPlan S) (t : ℕ) (ω : ℕ → S) :
    0 < ku_ezFin P β ρ γ T c t ω :=
  ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc _ ω

/-- Miao, Definition 20.2.1 for Exercise 20.1: `U_t(c)` depends only on `c_s`, `s ≥ t`, for
`t ≤ T`. -/
theorem ku_ezFin_dynUtility (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (ht : t ≤ T)
    {c c' : ℕ → (ℕ → S) → ℝ} (h : ∀ s ≥ t, c s = c' s) :
    ku_ezFin P β ρ γ T c t = ku_ezFin P β ρ γ T c' t := by
  have key : ∀ k, k ≤ T - t → ku_ezAux P β ρ γ T c k = ku_ezAux P β ρ γ T c' k := by
    intro k
    induction k with
    | zero => exact fun _ => h T ht
    | succ k ih =>
      intro hk
      funext ω
      simp only [ku_ezAux, ih (by omega), h (T - (k + 1)) (by omega)]
  exact key _ le_rfl

/-- Miao, Definition 20.2.1 for Exercise 20.1: for an adapted plan, `U_t(c)` is
`F_t`-measurable (`t ≤ T`). -/
theorem ku_ezFin_meas (P : Matrix S S ℝ) (β ρ γ : ℝ) {T t : ℕ} (ht : t ≤ T)
    {c : ℕ → (ℕ → S) → ℝ} (hc : ku_Adapted c) : ku_Meas t (ku_ezFin P β ρ γ T c t) := by
  have key : ∀ k, k ≤ T → ku_Meas (T - k) (ku_ezAux P β ρ γ T c k) := by
    intro k
    induction k with
    | zero =>
      intro _
      change ku_Meas (T - 0) (c T)
      simpa using hc T
    | succ k ih =>
      intro hk ω ω' hωω
      have hm := ih (by omega)
      rw [show T - k = T - (k + 1) + 1 by omega] at hm
      have hm' : ku_Meas (T - (k + 1) + 1) fun ω => ku_ezAux P β ρ γ T c k ω ^ (1 - γ) :=
        fun ω ω' h => by
          change ku_ezAux P β ρ γ T c k ω ^ (1 - γ) = ku_ezAux P β ρ γ T c k ω' ^ (1 - γ)
          rw [hm ω ω' h]
      simp only [ku_ezAux, ku_kpCE]
      rw [hc _ ω ω' hωω, ku_E_meas P hm' ω ω' hωω]
  have := key (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- `M_t(λx) = λM_t(x)` for the Kreps–Porteus certainty equivalent. -/
theorem ku_kpCE_homog {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {γ : ℝ} (hγ : γ ≠ 1) (t : ℕ)
    {x : (ℕ → S) → ℝ} (hx : ∀ ω, 0 < x ω) {l : ℝ} (hl : 0 < l) (ω : ℕ → S) :
    ku_kpCE P γ t (fun ω' => l * x ω') ω = l * ku_kpCE P γ t x ω := by
  rw [ku_kpCE_eq_kpR, ku_kpCE_eq_kpR]
  have h := SS.posHomogeneous_kpR (sub_ne_zero.2 (Ne.symm hγ)) hP
    (fun s' => x (Function.update ω (t + 1) s')) (fun _ => hx _) l hl.le
    (fun s' => by simpa using mul_pos hl (hx _))
  have := congrFun h (ω t)
  convert this using 2

/-- Miao, p. 686 and Exercise 20.1: the finite-horizon Epstein–Zin utility is homogeneous of
degree one, `U_t(λc) = λU_t(c)`. -/
theorem ku_ezFin_homog {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (T : ℕ) {c : ℕ → (ℕ → S) → ℝ}
    (hc : c ∈ ku_PosPlan S) {l : ℝ} (hl : 0 < l) (t : ℕ) (ω : ℕ → S) :
    ku_ezFin P β ρ γ T (l • c) t ω = l * ku_ezFin P β ρ γ T c t ω := by
  have key : ∀ k ω, ku_ezAux P β ρ γ T (l • c) k ω = l * ku_ezAux P β ρ γ T c k ω := by
    intro k
    induction k with
    | zero => intro ω; rfl
    | succ k ih =>
      intro ω
      have hf : ku_ezAux P β ρ γ T (l • c) k = fun ω' => l * ku_ezAux P β ρ γ T c k ω' :=
        funext ih
      simp only [ku_ezAux, hf]
      rw [ku_kpCE_homog hP hγ _ (ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k) hl,
        Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ku_ces_homog hρ hβ0.le hβ1.le hl (hc _ ω).le
          (ku_kpCE_pos hP γ (ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k) _ ω).le]
  exact key _ ω

/-- The two-state "distribution" `(1 − β, β)`, under which `SS.kpR` is the CES aggregator. -/
def ku_Q (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun _ j => if j = 0 then 1 - β else β

theorem ku_Q_markov {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : SS.IsMarkov (ku_Q β) :=
  ⟨fun _ j => by unfold ku_Q; split_ifs <;> linarith,
    fun _ => by simp [ku_Q, Fin.sum_univ_two]⟩

theorem ku_ces_eq_kpR (β ρ x y : ℝ) :
    ku_ces β ρ x y = SS.kpR (1 - ρ) (ku_Q β) ![x, y] 0 := by
  simp [ku_ces, SS.kpR, ku_Q, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The CES aggregator is jointly concave on `(0, ∞)²` for `ρ ≥ 0`, `ρ ≠ 1`. -/
theorem ku_ces_concave {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : ρ ≠ 1) (hρ0 : 0 ≤ ρ)
    {x x' y y' a b : ℝ} (hx : 0 < x) (hx' : 0 < x') (hy : 0 < y) (hy' : 0 < y') (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * ku_ces β ρ x y + b * ku_ces β ρ x' y' ≤ ku_ces β ρ (a * x + b * x') (a * y + b * y') := by
  have h := (SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hρ)) (by linarith)
    (ku_Q_markov hβ0 hβ1)).2 (x := ![x, y]) (y := ![x', y'])
    (fun i => by fin_cases i <;> simp [hx, hy]) (fun i => by fin_cases i <;> simp [hx', hy'])
    ha hb hab
  have h0 := h 0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  rw [ku_ces_eq_kpR, ku_ces_eq_kpR, ku_ces_eq_kpR]
  convert h0 using 3
  ext i
  fin_cases i <;> simp

/-- **Exercise 20.1** (Miao, p. 735), corrected: for `0 < β < 1`, `ρ ≥ 0`, `γ ≥ 0`
(`ρ, γ ≠ 1`), the finite-horizon Epstein–Zin utility `U_t` is concave on positive plans, at every
node. -/
theorem ex_20_1 {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hρ0 : 0 ≤ ρ) (hγ : γ ≠ 1) (hγ0 : 0 ≤ γ) (T t : ℕ) (ω : ℕ → S) :
    ConcaveOn ℝ (ku_PosPlan S) fun c => ku_ezFin P β ρ γ T c t ω := by
  have key : ∀ k, ∀ c ∈ ku_PosPlan S, ∀ c' ∈ ku_PosPlan S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → ∀ ω, a * ku_ezAux P β ρ γ T c k ω + b * ku_ezAux P β ρ γ T c' k ω ≤
        ku_ezAux P β ρ γ T (a • c + b • c') k ω := by
    intro k
    induction k with
    | zero => intro c _ c' _ a b _ _ _ ω; simp [ku_ezAux]
    | succ k ih =>
      intro c hc c' hc' a b ha hb hab ω
      set t' := T - (k + 1)
      have hmix := ku_convex_PosPlan hc hc' ha hb hab
      set X := ku_ezAux P β ρ γ T c k
      set X' := ku_ezAux P β ρ γ T c' k
      set Y := ku_ezAux P β ρ γ T (a • c + b • c') k
      have hX := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc k
      have hX' := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hc' k
      have hY := ku_ezAux_pos (ρ := ρ) (γ := γ) hP hβ0 hβ1 T hmix k
      have hZ : ∀ ω, 0 < a * X ω + b * X' ω := fun ω => by
        have := ku_convex_PosPlan (S := S) (x := fun _ => X) (y := fun _ => X')
          (fun _ => hX) (fun _ => hX') ha hb hab 0 ω
        simpa using this
      -- monotonicity of `M` and the induction hypothesis
      have h1 : ku_kpCE P γ t' (fun ω => a * X ω + b * X' ω) ω ≤ ku_kpCE P γ t' Y ω :=
        ku_kpCE_mono hP hγ t' hY hZ ω fun s' _ => ih c hc c' hc' a b ha hb hab _
      -- concavity of `M`
      have h2 : a * ku_kpCE P γ t' X ω + b * ku_kpCE P γ t' X' ω ≤
          ku_kpCE P γ t' (fun ω => a * X ω + b * X' ω) ω := by
        rw [ku_kpCE_eq_kpR, ku_kpCE_eq_kpR, ku_kpCE_eq_kpR]
        have h := (SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hγ)) (by linarith) hP).2
          (x := fun s' => X (Function.update ω (t' + 1) s'))
          (y := fun s' => X' (Function.update ω (t' + 1) s')) (fun _ => hX _) (fun _ => hX' _)
          ha hb hab (ω t')
        exact h
      have hMX := ku_kpCE_pos hP γ hX t' ω
      have hMX' := ku_kpCE_pos hP γ hX' t' ω
      have hMZ : 0 < a * ku_kpCE P γ t' X ω + b * ku_kpCE P γ t' X' ω := by
        have := ku_convex_PosPlan (S := S) (x := fun _ _ => ku_kpCE P γ t' X ω)
          (y := fun _ _ => ku_kpCE P γ t' X' ω) (fun _ _ => hMX) (fun _ _ => hMX') ha hb hab
          0 ω
        simpa using this
      have hc0 : 0 < (a • c + b • c') t' ω := hmix t' ω
      have hmono := (ku_ces_strictMonoOn hρ hβ0 hβ1 hc0).monotoneOn
      have h3 := hmono hMZ (ku_kpCE_pos hP γ hY t' ω) (h2.trans h1)
      have h4 := ku_ces_concave hβ0.le hβ1.le hρ hρ0 (hc t' ω) (hc' t' ω) hMX hMX' ha hb hab
      simp only [ku_ezAux]
      have e : (a • c + b • c') t' ω = a * c t' ω + b * c' t' ω := by simp
      rw [e] at h3 ⊢
      exact h4.trans h3
  refine ⟨ku_convex_PosPlan, fun c hc c' hc' a b ha hb hab => ?_⟩
  simpa [ku_ezFin] using key _ c hc c' hc' a b ha hb hab ω

/-- **Exercise 20.1** (Miao, p. 735): the claim is false. `U_t` is homogeneous of degree one
(`ku_ezFin_homog`), so it is linear along rays: for the constant plan `c ≡ 1`,
`U_t((c + 3c)/2) = (U_t(c) + U_t(3c))/2`, and `U_t` is not strictly concave, for any `t`, `ρ`,
`γ`. -/
theorem ex_20_1_not_strict [Nonempty S] {P : Matrix S S ℝ} (hP : SS.IsMarkov P) {β ρ γ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (T t : ℕ) (ω : ℕ → S) :
    ¬ StrictConcaveOn ℝ (ku_PosPlan S) fun c => ku_ezFin P β ρ γ T c t ω := by
  intro h
  set c : ℕ → (ℕ → S) → ℝ := fun _ _ => 1
  have hc : c ∈ ku_PosPlan S := fun _ _ => one_pos
  have h3c : (3 : ℝ) • c ∈ ku_PosPlan S := fun _ _ => by simp [c]
  have hne : c ≠ (3 : ℝ) • c := by
    intro he
    have := congrFun (congrFun he 0) ω
    simp [c] at this
  have hs := h.2 hc h3c hne (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num)
  have e : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • ((3 : ℝ) • c) = (2 : ℝ) • c := by
    rw [smul_smul, ← add_smul]
    norm_num
  rw [e] at hs
  simp only [smul_eq_mul] at hs
  rw [ku_ezFin_homog hP hβ0 hβ1 hρ hγ T hc (by norm_num : (0 : ℝ) < 3),
    ku_ezFin_homog hP hβ0 hβ1 hρ hγ T hc (by norm_num : (0 : ℝ) < 2)] at hs
  linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite-state setting for §20.2.2–§20.3

Miao, §20.2 (pp. 683–704) and §20.3 (pp. 704–710). The common objects used by the `AA` modules.

* `aa_E p x = ∑ₛ p(s)x(s)`: the expectation of `x : S → ℝ` under the distribution `p` on the finite
  state space `S` (the conditional expectation `E_t` of a one-step-ahead random variable).
* `aa_W β ρ c y = ((1 − β)c^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}`: the CES time aggregator of (20.3) and
  (20.11).
* `aa_KP γ p x = (E_p x^{1−γ})^{1/(1−γ)}`: the Kreps–Porteus conditional certainty equivalent of
  (20.3).
* The event tree. Histories are lists `h : List S`, newest shock first (`s :: h` is the successor
  of `h` after the shock `s`); `p h` is the one-step-ahead distribution at the node `h`, a
  consumption plan is `c : List S → ℝ`, and `aa_ezU β ρ γ p c n h` is the finite-horizon
  Epstein–Zin utility (20.3) at the node `h` with `n` periods remaining and terminal utility
  `U_T = c_T` (the setting of §20.3.1). The book works on a filtered probability space generated by
  a Markov chain with finitely many states; the event tree with finitely many shocks per period is
  that setting, with `p h s = π(s | head h)` in the Markov case.

The Epstein–Zin recursion (20.3) itself is defined in §20.2.1 (another part of this formalisation);
it is restated here for the finite horizon.
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- The expectation `E_p x = ∑ₛ p(s) x(s)` on a finite state space. -/
def aa_E (p x : S → ℝ) : ℝ := ∑ s, p s * x s

/-- The expectation of a constant is the constant. -/
theorem aa_E_const {p : S → ℝ} (hp : SS.IsDistribution p) (k : ℝ) : aa_E p (fun _ => k) = k := by
  simp only [aa_E, ← Finset.sum_mul, hp.sum_eq_one, one_mul]

/-- Monotonicity of the expectation. -/
theorem aa_E_mono {p : S → ℝ} (hp : SS.IsDistribution p) {x y : S → ℝ} (hxy : ∀ s, x s ≤ y s) :
    aa_E p x ≤ aa_E p y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hxy s) (hp.nonneg s)

/-- Linearity of the expectation. -/
theorem aa_E_add (p x y : S → ℝ) : aa_E p (fun s => x s + y s) = aa_E p x + aa_E p y := by
  simp only [aa_E, mul_add, Finset.sum_add_distrib]

/-- Homogeneity of the expectation. -/
theorem aa_E_smul (p x : S → ℝ) (a : ℝ) : aa_E p (fun s => a * x s) = a * aa_E p x := by
  simp only [aa_E, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of a positive random variable is positive. -/
theorem aa_E_pos [Nonempty S] {p : S → ℝ} (hp : SS.IsDistribution p) {x : S → ℝ}
    (hx : ∀ s, 0 < x s) : 0 < aa_E p x := by
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < p s := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ s, p s = 0 := Finset.sum_eq_zero fun s _ => le_antisymm (h s) (hp.nonneg s)
    rw [hp.sum_eq_one] at this
    exact one_ne_zero this
  have h1 : p s₀ * x s₀ ≤ ∑ s, p s * x s :=
    Finset.single_le_sum (f := fun s => p s * x s)
      (fun s _ => mul_nonneg (hp.nonneg s) (hx s).le) (Finset.mem_univ s₀)
  exact lt_of_lt_of_le (mul_pos hs₀ (hx s₀)) h1

/-- The CES time aggregator `W(c, y) = ((1 − β)c^{1−ρ} + βy^{1−ρ})^{1/(1−ρ)}` of (20.3), (20.11). -/
noncomputable def aa_W (β ρ c y : ℝ) : ℝ := ((1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ)) ^ (1 - ρ)⁻¹

/-- The Kreps–Porteus certainty equivalent `M(x) = (E x^{1−γ})^{1/(1−γ)}` of (20.3). -/
noncomputable def aa_KP (γ : ℝ) (p x : S → ℝ) : ℝ := (aa_E p fun s => x s ^ (1 - γ)) ^ (1 - γ)⁻¹

/-- The finite-horizon Epstein–Zin utility (20.3) on the event tree, `U_T(c) = c_T`. -/
noncomputable def aa_ezU (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => c h
  | n + 1, h => aa_W β ρ (c h) (aa_KP γ (p h) fun s => aa_ezU β ρ γ p c n (s :: h))

/-- The aggregator is positive at positive arguments. -/
theorem aa_W_pos {β ρ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (hy : 0 < y) :
    0 < aa_W β ρ c y := by
  unfold aa_W
  have h1 : 0 < 1 - β := by linarith
  positivity

/-- The certainty equivalent of a positive random variable is positive. -/
theorem aa_KP_pos [Nonempty S] (γ : ℝ) {p : S → ℝ} (hp : SS.IsDistribution p) {x : S → ℝ}
    (hx : ∀ s, 0 < x s) : 0 < aa_KP γ p x :=
  Real.rpow_pos_of_pos (aa_E_pos hp fun s => Real.rpow_pos_of_pos (hx s) _) _

/-- The certainty-equivalent property `M(k) = k` for constants `k > 0`. -/
theorem aa_KP_const {γ : ℝ} (hγ : γ ≠ 1) {p : S → ℝ} (hp : SS.IsDistribution p) {k : ℝ}
    (hk : 0 < k) : aa_KP γ p (fun _ => k) = k := by
  unfold aa_KP
  rw [aa_E_const hp]
  exact Real.rpow_rpow_inv hk.le (sub_ne_zero.2 (Ne.symm hγ))

/-- The aggregator at equal arguments: `W(k, k) = k`. -/
theorem aa_W_diag {β ρ : ℝ} (hρ : ρ ≠ 1) {k : ℝ} (hk : 0 < k) : aa_W β ρ k k = k := by
  unfold aa_W
  rw [show (1 - β) * k ^ (1 - ρ) + β * k ^ (1 - ρ) = k ^ (1 - ρ) by ring]
  exact Real.rpow_rpow_inv hk.le (sub_ne_zero.2 (Ne.symm hρ))

/-- The aggregator is strictly increasing in the continuation value `y > 0` (`β > 0`, `ρ ≠ 1`). -/
theorem aa_W_strictMonoOn {β ρ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hc : 0 < c) :
    StrictMonoOn (aa_W β ρ c) (Set.Ioi 0) := by
  intro y hy y' hy' hyy'
  have hy0 : (0 : ℝ) < y := hy
  have hy0' : (0 : ℝ) < y' := hy'
  have h1 : 0 < 1 - β := by linarith
  unfold aa_W
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hρ)) with hneg | hpos
  · have h2 : y' ^ (1 - ρ) < y ^ (1 - ρ) := Real.rpow_lt_rpow_of_neg hy0 hyy' hneg
    have h3 : (1 - β) * c ^ (1 - ρ) + β * y' ^ (1 - ρ) < (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) :=
      by nlinarith
    exact Real.rpow_lt_rpow_of_neg (by positivity) h3 (inv_lt_zero.2 hneg)
  · have h2 : y ^ (1 - ρ) < y' ^ (1 - ρ) := Real.rpow_lt_rpow hy0.le hyy' hpos
    have h3 : (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) < (1 - β) * c ^ (1 - ρ) + β * y' ^ (1 - ρ) :=
      by nlinarith
    exact Real.rpow_lt_rpow (by positivity) h3 (inv_pos.2 hpos)

/-- The certainty equivalent is monotone on positive random variables (`γ ≠ 1`). -/
theorem aa_KP_mono {γ : ℝ} (hγ : γ ≠ 1) [Nonempty S] {p : S → ℝ} (hp : SS.IsDistribution p)
    {x y : S → ℝ} (hx : ∀ s, 0 < x s) (hxy : ∀ s, x s ≤ y s) : aa_KP γ p x ≤ aa_KP γ p y := by
  have hy : ∀ s, 0 < y s := fun s => (hx s).trans_le (hxy s)
  have hEx := aa_E_pos hp fun s => Real.rpow_pos_of_pos (hx s) (1 - γ)
  have hEy := aa_E_pos hp fun s => Real.rpow_pos_of_pos (hy s) (1 - γ)
  unfold aa_KP
  rcases lt_or_gt_of_ne (sub_ne_zero.2 (Ne.symm hγ)) with hneg | hpos
  · have h1 : (aa_E p fun s => y s ^ (1 - γ)) ≤ aa_E p fun s => x s ^ (1 - γ) :=
      aa_E_mono hp fun s => Real.rpow_le_rpow_of_nonpos (hx s) (hxy s) hneg.le
    exact Real.rpow_le_rpow_of_nonpos hEy h1 (inv_lt_zero.2 hneg).le
  · have h1 : (aa_E p fun s => x s ^ (1 - γ)) ≤ aa_E p fun s => y s ^ (1 - γ) :=
      aa_E_mono hp fun s => Real.rpow_le_rpow (hx s).le (hxy s) hpos.le
    exact Real.rpow_le_rpow hEx.le h1 (inv_pos.2 hpos).le

/-- The finite-horizon Epstein–Zin utility of a positive plan is positive. -/
theorem aa_ezU_pos [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : List S → S → ℝ}
    (hp : ∀ h, SS.IsDistribution (p h)) {c : List S → ℝ} (hc : ∀ h, 0 < c h) :
    ∀ n h, 0 < aa_ezU β ρ γ p c n h
  | 0, h => hc h
  | n + 1, h =>
    aa_W_pos hβ0 hβ1 (hc h) (aa_KP_pos γ (hp h) fun s => aa_ezU_pos hβ0 hβ1 hp hc n (s :: h))

/-- The `t`-step-ahead expectation on the event tree: `aa_Ex q t f h = E_h[f(h_{t})]` when the
one-step-ahead distribution at the node `h'` is `q h'`. -/
def aa_Ex (q : List S → S → ℝ) : ℕ → (List S → ℝ) → List S → ℝ
  | 0, f, h => f h
  | t + 1, f, h => ∑ s, q h s * aa_Ex q t f (s :: h)

/-- Unrolling a linear recursion `V_{n+1}(h) = g(h) + β E_h V_n`, `V_0 = g_T`: the law of iterated
expectations gives `V_n(h) = ∑_{t<n} β^t E_h g(h_t) + β^n E_h g_T(h_n)`. -/
theorem aa_linear_unroll (q : List S → S → ℝ) (β : ℝ) (g gT : List S → ℝ)
    (V : ℕ → List S → ℝ) (h0 : ∀ h, V 0 h = gT h)
    (hs : ∀ n h, V (n + 1) h = g h + β * ∑ s, q h s * V n (s :: h)) :
    ∀ n h, V n h = ∑ t ∈ Finset.range n, β ^ t * aa_Ex q t g h + β ^ n * aa_Ex q n gT h := by
  intro n
  induction n with
  | zero => intro h; simp [h0, aa_Ex]
  | succ n ih =>
    intro h
    rw [hs, Finset.sum_range_succ', pow_succ']
    simp only [ih, pow_zero, one_mul, aa_Ex]
    have e1 : ∑ s, q h s * (∑ t ∈ Finset.range n, β ^ t * aa_Ex q t g (s :: h) +
        β ^ n * aa_Ex q n gT (s :: h)) =
        ∑ t ∈ Finset.range n, β ^ t * ∑ s, q h s * aa_Ex q t g (s :: h) +
          β ^ n * ∑ s, q h s * aa_Ex q n gT (s :: h) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
      · exact Finset.sum_congr rfl fun s _ => by ring
    rw [e1, mul_add, Finset.mul_sum]
    have e2 : ∀ t ∈ Finset.range n, β * (β ^ t * ∑ s, q h s * aa_Ex q t g (s :: h)) =
        β ^ (t + 1) * ∑ s, q h s * aa_Ex q t g (s :: h) := fun t _ => by ring
    rw [Finset.sum_congr rfl e2]
    ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Limits of log-exponential certainty equivalents

Miao, §20.2.2, pp. 694–700. The limits that the text takes in passing from one specification to
another all reduce to two facts about the cumulant generating function
`Λ(t) = ln E_p exp(t v)` on a finite state space.

* `Λ(0) = 0` and `Λ'(0) = E_p v` (`aa_logmgf_hasDerivAt`), hence
  `t⁻¹ ln E_p exp(t v) → E_p v` as `t → 0` (`aa_tendsto_logmgf`).
* The soft minimum: if every state has positive probability,
  `−k⁻¹ ln E_p exp(−k v) → min v` as `k → ∞` (`aa_tendsto_softmin`), with the two-sided bound
  `min v ≤ −k⁻¹ ln E_p exp(−k v) ≤ min v − k⁻¹ ln p(s*)` (`aa_softmin_bounds`).

They are applied in `AAVariational` (`θ → ∞`), and in `AASmoothAmbiguity` (`ρ → 1`, `γ → 1`,
`η → ∞`, equations (20.16)–(20.18)).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- The cumulant generating function `Λ(t) = ln ∑ₛ p(s) exp(t v(s))` has `Λ'(0) = E_p v`. -/
theorem aa_logmgf_hasDerivAt {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) :
    HasDerivAt (fun t => Real.log (∑ s, p s * Real.exp (t * v s))) (aa_E p v) 0 := by
  have hsum : HasDerivAt (fun t => ∑ s, p s * Real.exp (t * v s))
      (∑ s, p s * (Real.exp (0 * v s) * (1 * v s))) 0 := by
    apply HasDerivAt.fun_sum
    intro s _
    exact (((hasDerivAt_id (0 : ℝ)).mul_const (v s)).exp).const_mul (p s)
  have h1 : (∑ s, p s * Real.exp (0 * v s)) = 1 := by
    simp [hp.sum_eq_one]
  have := hsum.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  simpa [aa_E] using this

/-- `t⁻¹ ln E_p exp(t v) → E_p v` as `t → 0`, `t ≠ 0`. -/
theorem aa_tendsto_logmgf {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) :
    Tendsto (fun t => t⁻¹ * Real.log (∑ s, p s * Real.exp (t * v s))) (𝓝[≠] 0)
      (𝓝 (aa_E p v)) := by
  have := (hasDerivAt_iff_tendsto_slope_zero.1 (aa_logmgf_hasDerivAt hp v))
  simpa [hp.sum_eq_one] using this

/-- The soft-minimum bounds: for `k > 0` and a state `s*` minimising `v`,
`v(s*) ≤ −k⁻¹ ln E_p exp(−k v) ≤ v(s*) − k⁻¹ ln p(s*)`, provided `p(s*) > 0`. -/
theorem aa_softmin_bounds {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) {s₀ : S}
    (hmin : ∀ s, v s₀ ≤ v s) (hps : 0 < p s₀) {k : ℝ} (hk : 0 < k) :
    v s₀ ≤ -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ∧
      -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ≤ v s₀ - k⁻¹ * Real.log (p s₀) := by
  have hlow : p s₀ * Real.exp (-k * v s₀) ≤ ∑ s, p s * Real.exp (-k * v s) :=
    Finset.single_le_sum (f := fun s => p s * Real.exp (-k * v s))
      (fun s _ => mul_nonneg (hp.nonneg s) (Real.exp_pos _).le) (Finset.mem_univ s₀)
  have hup : ∑ s, p s * Real.exp (-k * v s) ≤ Real.exp (-k * v s₀) := by
    calc ∑ s, p s * Real.exp (-k * v s) ≤ ∑ s, p s * Real.exp (-k * v s₀) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by nlinarith [hmin s])) (hp.nonneg s)
      _ = Real.exp (-k * v s₀) := by rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
  have hpos0 : 0 < p s₀ * Real.exp (-k * v s₀) := mul_pos hps (Real.exp_pos _)
  have hpos : 0 < ∑ s, p s * Real.exp (-k * v s) := hpos0.trans_le hlow
  have hk' : 0 < k⁻¹ := inv_pos.2 hk
  constructor
  · have h1 := Real.log_le_log hpos hup
    rw [Real.log_exp] at h1
    have h2 : k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) ≤ k⁻¹ * (-k * v s₀) :=
      mul_le_mul_of_nonneg_left h1 hk'.le
    have h3 : k⁻¹ * (-k * v s₀) = -v s₀ := by field_simp
    linarith
  · have h1 := Real.log_le_log hpos0 hlow
    rw [Real.log_mul hps.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 : k⁻¹ * (Real.log (p s₀) + -k * v s₀) ≤
        k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s)) := mul_le_mul_of_nonneg_left h1 hk'.le
    have h3 : k⁻¹ * (Real.log (p s₀) + -k * v s₀) = k⁻¹ * Real.log (p s₀) - v s₀ := by
      field_simp
      ring
    linarith

/-- **The soft minimum** (used for (20.18)): if `p(s*) > 0` at a minimiser `s*` of `v`, then
`−k⁻¹ ln E_p exp(−k v) → min v` as `k → ∞`. -/
theorem aa_tendsto_softmin {p : S → ℝ} (hp : SS.IsDistribution p) (v : S → ℝ) {s₀ : S}
    (hmin : ∀ s, v s₀ ≤ v s) (hps : 0 < p s₀) :
    Tendsto (fun k => -k⁻¹ * Real.log (∑ s, p s * Real.exp (-k * v s))) atTop (𝓝 (v s₀)) := by
  have hup : Tendsto (fun k : ℝ => v s₀ - k⁻¹ * Real.log (p s₀)) atTop (𝓝 (v s₀)) := by
    have := (tendsto_inv_atTop_zero.mul_const (Real.log (p s₀))).const_sub (v s₀)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (aa_softmin_bounds hp v hmin hps hk).1
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (aa_softmin_bounds hp v hmin hps hk).2

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maxmin expected utility and recursive multiple priors

Miao, §20.2.2, pp. 691–693: the Ellsberg paradox, Gilboa–Schmeidler maxmin expected utility,
the recursive multiple-priors utility (20.7) of Epstein–Wang, Epstein–Schneider rectangularity
and Hayashi's generalisation.

* `aa_maxmin Q u = inf_{q ∈ Q} E_q u`, with `aa_maxmin_le`, `aa_le_maxmin`, attainment on finite
  sets of priors (`aa_maxmin_isLeast`) and the special case of one prior (`aa_maxmin_singleton`).
* The Ellsberg paradox (p. 692): no single prior strictly prefers urn 1 for both bets
  (`aa_ellsberg_no_prior`), while maxmin utility with an interval of priors for urn 2 does
  (`aa_ellsberg_maxmin`).
* The uncertainty aggregator `R_t` of (20.7) is monotone, translation invariant, positively
  homogeneous and superadditive (`aa_maxmin_mono`, `aa_maxmin_add_const`, `aa_maxmin_smul`,
  `aa_maxmin_superadditive`).
* (20.7) on the event tree with a finite horizon (`aa_rmpU`); Hayashi's form `W(c, R(U'))`
  (`aa_hayashiU`) contains it (`aa_hayashiU_additive`).
* Rectangularity (p. 693): with rectangular priors (one-step-ahead priors chosen node by node), the
  time-zero utility `min_P E^P[∑ βᵗ u(c_t)]` satisfies the recursion (20.7)
  (`aa_rmpU_isLeast_selection`, `aa_rectangular_recursion`); for a non-rectangular set it can fail
  (`aa_nonrectangular_counterexample`).

Departures: the book's (20.7) is on an infinite horizon with a Markov correspondence `P(·|s)`; here
it
is on a finite event tree, with sets of priors that are finite where a minimum must be attained.
The Choquet expected utility of footnote 1 is not formalised (cited, no derivation).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- The maxmin (Gilboa–Schmeidler) utility `U = inf_{q ∈ Q} ∫ u dq` over a set `Q` of priors. -/
noncomputable def aa_maxmin (Q : Set (S → ℝ)) (u : S → ℝ) : ℝ := sInf ((fun q => aa_E q u) '' Q)

/-- Expected utility under a distribution is bounded below by `−∑ |u|`. -/
theorem aa_E_ge_neg {q : S → ℝ} (hq : SS.IsDistribution q) (u : S → ℝ) :
    -∑ s, |u s| ≤ aa_E q u := by
  unfold aa_E
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have hq1 : q s ≤ 1 := by
    rw [← hq.sum_eq_one]
    exact Finset.single_le_sum (fun s _ => hq.nonneg s) (Finset.mem_univ s)
  have h1 : |q s * u s| ≤ |u s| := by
    rw [abs_mul, abs_of_nonneg (hq.nonneg s)]
    exact mul_le_of_le_one_left (abs_nonneg _) hq1
  linarith [neg_abs_le (q s * u s)]

theorem aa_maxmin_bdd {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ) :
    BddBelow ((fun q => aa_E q u) '' Q) :=
  ⟨-∑ s, |u s|, by rintro _ ⟨q, hq, rfl⟩; exact aa_E_ge_neg (hQ q hq) u⟩

/-- Maxmin utility is at most the expected utility under every prior in `Q`. -/
theorem aa_maxmin_le {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ)
    {q : S → ℝ} (hq : q ∈ Q) : aa_maxmin Q u ≤ aa_E q u :=
  csInf_le (aa_maxmin_bdd hQ u) ⟨q, hq, rfl⟩

/-- A lower bound for every prior is a lower bound for maxmin utility. -/
theorem aa_le_maxmin {Q : Set (S → ℝ)} (hne : Q.Nonempty) (u : S → ℝ) {k : ℝ}
    (hk : ∀ q ∈ Q, k ≤ aa_E q u) : k ≤ aa_maxmin Q u :=
  le_csInf (hne.image _) (by rintro _ ⟨q, hq, rfl⟩; exact hk q hq)

/-- On a finite nonempty set of priors the minimum is attained. -/
theorem aa_maxmin_attained {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hfin : Q.Finite) (hne : Q.Nonempty) (u : S → ℝ) :
    ∃ q ∈ Q, aa_maxmin Q u = aa_E q u := by
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image Q (fun q => aa_E q u) hfin hne
  exact ⟨q, hq, le_antisymm (aa_maxmin_le hQ u hq) (aa_le_maxmin hne u hmin)⟩

/-- Miao, p. 692: with one prior `Q = {p}`, maxmin utility is expected utility. -/
theorem aa_maxmin_singleton (p u : S → ℝ) : aa_maxmin {p} u = aa_E p u := by
  simp [aa_maxmin]

/-- Monotonicity of the uncertainty aggregator `R_t` of (20.7). -/
theorem aa_maxmin_mono {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hne : Q.Nonempty)
    {x y : S → ℝ} (hxy : ∀ s, x s ≤ y s) : aa_maxmin Q x ≤ aa_maxmin Q y :=
  aa_le_maxmin hne y fun q hq => (aa_maxmin_le hQ x hq).trans (aa_E_mono (hQ q hq) hxy)

/-- Translation invariance `R(x + k) = R(x) + k`; in particular `R(k) = k`. -/
theorem aa_maxmin_add_const {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x : S → ℝ) (k : ℝ) :
    aa_maxmin Q (fun s => x s + k) = aa_maxmin Q x + k := by
  have e : ∀ q ∈ Q, aa_E q (fun s => x s + k) = aa_E q x + k := fun q hq => by
    rw [aa_E_add, aa_E_const (hQ q hq)]
  apply le_antisymm
  · have : aa_maxmin Q (fun s => x s + k) - k ≤ aa_maxmin Q x :=
      aa_le_maxmin hne x fun q hq => by
        have := aa_maxmin_le hQ (fun s => x s + k) hq
        rw [e q hq] at this
        linarith
    linarith
  · exact aa_le_maxmin hne _ fun q hq => by
      rw [e q hq]
      linarith [aa_maxmin_le hQ x hq]

/-- The certainty-equivalent property `R(k) = k` of the maxmin aggregator. -/
theorem aa_maxmin_const {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (k : ℝ) : aa_maxmin Q (fun _ => k) = k := by
  have := aa_maxmin_add_const hQ hne (fun _ => 0) k
  have h0 : aa_maxmin Q (fun _ => (0 : ℝ)) = 0 := by
    apply le_antisymm
    · obtain ⟨q, hq⟩ := hne
      have := aa_maxmin_le hQ (fun _ => (0 : ℝ)) hq
      rwa [aa_E_const (hQ q hq)] at this
    · exact aa_le_maxmin hne _ fun q hq => by rw [aa_E_const (hQ q hq)]
  simpa [h0] using this

/-- Positive homogeneity `R(a x) = a R(x)` for `a ≥ 0`. -/
theorem aa_maxmin_smul {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x : S → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    aa_maxmin Q (fun s => a * x s) = a * aa_maxmin Q x := by
  rcases ha.lt_or_eq with ha | ha
  · apply le_antisymm
    · have : aa_maxmin Q (fun s => a * x s) / a ≤ aa_maxmin Q x :=
        aa_le_maxmin hne x fun q hq => by
          rw [div_le_iff₀ ha, mul_comm, ← aa_E_smul]
          exact aa_maxmin_le hQ _ hq
      rwa [div_le_iff₀ ha, mul_comm] at this
    · exact aa_le_maxmin hne _ fun q hq => by
        rw [aa_E_smul]
        exact mul_le_mul_of_nonneg_left (aa_maxmin_le hQ x hq) ha.le
  · subst ha
    simp only [zero_mul]
    exact aa_maxmin_const hQ hne 0

/-- Superadditivity `R(x + y) ≥ R(x) + R(y)`, so with positive homogeneity `R` is concave. -/
theorem aa_maxmin_superadditive {Q : Set (S → ℝ)} (hQ : ∀ q ∈ Q, SS.IsDistribution q)
    (hne : Q.Nonempty) (x y : S → ℝ) :
    aa_maxmin Q x + aa_maxmin Q y ≤ aa_maxmin Q (fun s => x s + y s) :=
  aa_le_maxmin hne _ fun q hq => by
    rw [aa_E_add]
    exact add_le_add (aa_maxmin_le hQ x hq) (aa_maxmin_le hQ y hq)

/-! ### The Ellsberg paradox (p. 692) -/

/-- **The Ellsberg paradox** (Miao, p. 692): no subjective probability `(q_B, q_W)` on the colour of
the ball drawn from urn 2 makes an expected-utility maximiser strictly prefer urn 1 (known
composition `50/50`) both for the bet on black and for the bet on white. Here `a = u(100)`,
`b = u(0)`. -/
theorem aa_ellsberg_no_prior (a b qB qW : ℝ) (hq : qB + qW = 1) :
    ¬ (qB * a + qW * b < a / 2 + b / 2 ∧ qW * a + qB * b < a / 2 + b / 2) := by
  rintro ⟨h1, h2⟩
  have : (qB + qW) * (a + b) < a + b := by nlinarith
  rw [hq, one_mul] at this
  exact lt_irrefl _ this

/-- The priors on urn 2 (state `true` = black): all distributions with `q(black) ∈ [l, h]`. -/
def aa_ellsbergPriors (l h : ℝ) : Set (Bool → ℝ) :=
  {q | SS.IsDistribution q ∧ l ≤ q true ∧ q true ≤ h}

/-- The prior with `q(black) = r`. -/
def aa_ellsbergPrior (r : ℝ) : Bool → ℝ := fun b => if b then r else 1 - r

theorem aa_ellsbergPrior_isDistribution {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    SS.IsDistribution (aa_ellsbergPrior r) :=
  ⟨fun b => by cases b <;> simp [aa_ellsbergPrior] <;> linarith, by simp [aa_ellsbergPrior]⟩

theorem aa_E_bool (q u : Bool → ℝ) : aa_E q u = q true * u true + q false * u false := by
  simp [aa_E, add_comm]

/-- Maxmin utility of the bet on black from urn 2: `l u(100) + (1 − l) u(0)` (`u(100) ≥ u(0)`). -/
theorem aa_ellsberg_black {l h a b : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hh : h ≤ 1) (hab : b ≤ a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then a else b) = l * a + (1 - l) * b := by
  have hD : ∀ q ∈ aa_ellsbergPriors l h, SS.IsDistribution q := fun q hq => hq.1
  have hmem : aa_ellsbergPrior l ∈ aa_ellsbergPriors l h :=
    ⟨aa_ellsbergPrior_isDistribution hl (hlh.trans hh), by simp [aa_ellsbergPrior],
      by simp [aa_ellsbergPrior, hlh]⟩
  apply le_antisymm
  · have := aa_maxmin_le hD (fun c => if c then a else b) hmem
    simpa [aa_E_bool, aa_ellsbergPrior] using this
  · refine aa_le_maxmin ⟨_, hmem⟩ _ fun q hq => ?_
    have hs := hq.1.sum_eq_one
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton] at hs
    rw [aa_E_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [show q false = 1 - q true by linarith]
    nlinarith [mul_nonneg (sub_nonneg.2 hq.2.1) (sub_nonneg.2 hab)]

/-- Maxmin utility of the bet on white from urn 2: `(1 − h) u(100) + h u(0)` (`u(100) ≥ u(0)`). -/
theorem aa_ellsberg_white {l h a b : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hh : h ≤ 1) (hab : b ≤ a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then b else a) = (1 - h) * a + h * b := by
  have hD : ∀ q ∈ aa_ellsbergPriors l h, SS.IsDistribution q := fun q hq => hq.1
  have hmem : aa_ellsbergPrior h ∈ aa_ellsbergPriors l h :=
    ⟨aa_ellsbergPrior_isDistribution (hl.trans hlh) hh, by simp [aa_ellsbergPrior, hlh],
      by simp [aa_ellsbergPrior]⟩
  apply le_antisymm
  · have := aa_maxmin_le hD (fun c => if c then b else a) hmem
    simp only [aa_E_bool, aa_ellsbergPrior, ↓reduceIte, Bool.false_eq_true] at this
    linarith
  · refine aa_le_maxmin ⟨_, hmem⟩ _ fun q hq => ?_
    have hs := hq.1.sum_eq_one
    simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
      Finset.sum_insert, Finset.sum_singleton] at hs
    rw [aa_E_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [show q false = 1 - q true by linarith]
    nlinarith [mul_nonneg (sub_nonneg.2 hq.2.2) (sub_nonneg.2 hab)]

/-- **The Ellsberg paradox resolved by maxmin utility** (Miao, pp. 692–693). With the known urn 1
(`50/50`, one prior) and priors `q(black) ∈ [l, h]` for urn 2, `l < 1/2 < h`, and
`u(100) > u(0)`, the maxmin decision maker strictly prefers urn 1 for the bet on black and for the
bet on white. -/
theorem aa_ellsberg_maxmin {l h a b : ℝ} (hl : 0 ≤ l) (hl2 : l < 1 / 2) (hh2 : 1 / 2 < h)
    (hh : h ≤ 1) (hab : b < a) :
    aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then a else b) <
        aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun c => if c then a else b) ∧
      aa_maxmin (aa_ellsbergPriors l h) (fun c => if c then b else a) <
        aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun c => if c then b else a) := by
  have hlh : l ≤ h := by linarith
  rw [aa_ellsberg_black hl hlh hh hab.le, aa_ellsberg_white hl hlh hh hab.le,
    aa_maxmin_singleton, aa_maxmin_singleton, aa_E_bool, aa_E_bool]
  simp only [aa_ellsbergPrior, ↓reduceIte, Bool.false_eq_true]
  constructor <;> nlinarith

/-! ### Recursive multiple priors (20.7) and Hayashi's form -/

/-- **(20.7)** (Miao, p. 693) on a finite event tree:
`U_t = u(c_t) + β min_{π ∈ P(·|h)} E_π U_{t+1}`,
`U_T = u(c_T)`; `P h` is the set of one-step-ahead priors at the node `h`. -/
noncomputable def aa_rmpU (u : ℝ → ℝ) (β : ℝ) (P : List S → Set (S → ℝ)) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * aa_maxmin (P h) fun s => aa_rmpU u β P c n (s :: h)

/-- Hayashi's (2005) form `U_t = W(c_t, R_t(U_{t+1}))` (Miao, p. 693), terminal utility
`U_T = ψ(c_T)`. -/
noncomputable def aa_hayashiU (W : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ) (P : List S → Set (S → ℝ))
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => ψ (c h)
  | n + 1, h => W (c h) (aa_maxmin (P h) fun s => aa_hayashiU W ψ P c n (s :: h))

/-- Miao, p. 693: Hayashi's form with the additive aggregator `W(c, y) = u(c) + βy` is (20.7). -/
theorem aa_hayashiU_additive (u : ℝ → ℝ) (β : ℝ) (P : List S → Set (S → ℝ)) (c : List S → ℝ) :
    ∀ n h, aa_hayashiU (fun x y => u x + β * y) u P c n h = aa_rmpU u β P c n h
  | 0, h => rfl
  | n + 1, h => by
    simp only [aa_hayashiU, aa_rmpU]
    rw [show (fun s => aa_hayashiU (fun x y => u x + β * y) u P c n (s :: h)) =
      (fun s => aa_rmpU u β P c n (s :: h)) from
        funext fun s => aa_hayashiU_additive u β P c n (s :: h)]

/-- Expected discounted utility under a selection `q` of one-step-ahead priors (one at every node):
`V_t = u(c_t) + β E_{q(h)} V_{t+1}`. -/
noncomputable def aa_selU (u : ℝ → ℝ) (β : ℝ) (q : List S → S → ℝ) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * ∑ s, q h s * aa_selU u β q c n (s :: h)

/-- Under a selection `q` the recursion computes `E^q[∑_{t ≤ n} βᵗ u(c_t)]`, the expected discounted
utility under the probability measure on the tree that `q` generates. -/
theorem aa_selU_eq_sum (u : ℝ → ℝ) (β : ℝ) (q : List S → S → ℝ) (c : List S → ℝ) (n : ℕ)
    (h : List S) : aa_selU u β q c n h =
      ∑ t ∈ Finset.range (n + 1), β ^ t * aa_Ex q t (fun h' => u (c h')) h := by
  rw [aa_linear_unroll q β (fun h' => u (c h')) (fun h' => u (c h')) (aa_selU u β q c)
    (fun _ => rfl) (fun _ _ => rfl) n h, Finset.sum_range_succ]

/-- **Rectangularity** (Miao, p. 693; Epstein and Schneider 2003). With finitely many priors at
every
node, the recursive multiple-priors utility (20.7) is the minimum, over all rectangular selections
of priors (`q h ∈ P h` at every node), of the expected discounted utility: the time-zero utility
`min_P E^P[∑ βᵗ u(c_t)]` over the rectangular set satisfies the recursion. -/
theorem aa_rmpU_isLeast_selection (u : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)}
    (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q) (hfin : ∀ h, (P h).Finite)
    (hne : ∀ h, (P h).Nonempty) (c : List S → ℝ) (n : ℕ) (h : List S) :
    IsLeast {y | ∃ q : List S → S → ℝ, (∀ h', q h' ∈ P h') ∧ y = aa_selU u β q c n h}
      (aa_rmpU u β P c n h) := by
  classical
  -- the minimising selection
  let qstar : ℕ → List S → S → ℝ := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h') fun s => aa_rmpU u β P c m (s :: h')).choose
  have hq_mem : ∀ m h', qstar m h' ∈ P h' := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h')
      fun s => aa_rmpU u β P c m (s :: h')).choose_spec.1
  have hq_eq : ∀ m h', aa_maxmin (P h') (fun s => aa_rmpU u β P c m (s :: h')) =
      aa_E (qstar m h') fun s => aa_rmpU u β P c m (s :: h') := fun m h' =>
    (aa_maxmin_attained (hP h') (hfin h') (hne h')
      fun s => aa_rmpU u β P c m (s :: h')).choose_spec.2
  -- lower bound for every selection
  have hlow : ∀ (q : List S → S → ℝ), (∀ h', q h' ∈ P h') →
      ∀ m h', aa_rmpU u β P c m h' ≤ aa_selU u β q c m h' := by
    intro q hq m
    induction m with
    | zero => intro h'; exact le_rfl
    | succ m ih =>
      intro h'
      simp only [aa_rmpU, aa_selU]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ)
      exact (aa_maxmin_le (hP h') _ (hq h')).trans (aa_E_mono (hP h' _ (hq h')) fun s => ih _)
  -- the selection attaining the bound, along the remaining horizon from `h`
  let qsel : List S → S → ℝ := fun h' => qstar (n + h.length - h'.length - 1) h'
  have hattain : ∀ m h', h'.length + m = n + h.length →
      aa_rmpU u β P c m h' = aa_selU u β qsel c m h' := by
    intro m
    induction m with
    | zero => intro h' _; rfl
    | succ m ih =>
      intro h' hlen
      have hidx : n + h.length - h'.length - 1 = m := by omega
      simp only [aa_rmpU, aa_selU]
      rw [hq_eq m h']
      congr 2
      simp only [aa_E, qsel, hidx]
      exact Finset.sum_congr rfl fun s _ => by
        rw [ih (s :: h') (by simp only [List.length_cons]; omega)]
  exact ⟨⟨qsel, fun h' => hq_mem _ h', hattain n h (by omega)⟩,
    by rintro y ⟨q, hq, rfl⟩; exact hlow q hq n h⟩

/-- **Rectangularity, two periods** (Miao, p. 693). For priors `q₀ ∈ P₀` over the first shock and
`q₁(s) ∈ P₁(s)` over the second, the minimum of `E^Q x` over the rectangular set of products
`Q(s, s') = q₀(s)q₁(s)(s')` equals the recursive value
`min_{q₀} E_{q₀}[min_{q₁(s)} E_{q₁(s)} x(s, ·)]`. -/
theorem aa_rectangular_recursion {S' : Type*} [Fintype S'] {P₀ : Set (S → ℝ)}
    {P₁ : S → Set (S' → ℝ)} (hP₀ : ∀ q ∈ P₀, SS.IsDistribution q)
    (hP₁ : ∀ s, ∀ q ∈ P₁ s, SS.IsDistribution q) (hfin₀ : P₀.Finite) (hfin₁ : ∀ s, (P₁ s).Finite)
    (hne₀ : P₀.Nonempty) (hne₁ : ∀ s, (P₁ s).Nonempty) (x : S × S' → ℝ) :
    IsLeast {y | ∃ q₀ ∈ P₀, ∃ q₁ : S → S' → ℝ, (∀ s, q₁ s ∈ P₁ s) ∧
        y = aa_E (fun ω => q₀ ω.1 * q₁ ω.1 ω.2) x}
      (aa_maxmin P₀ fun s => aa_maxmin (P₁ s) fun s' => x (s, s')) := by
  classical
  have hprod : ∀ (q₀ : S → ℝ) (q₁ : S → S' → ℝ), aa_E (fun ω => q₀ ω.1 * q₁ ω.1 ω.2) x =
      aa_E q₀ fun s => aa_E (q₁ s) fun s' => x (s, s') := fun q₀ q₁ => by
    simp only [aa_E, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  let q₁ : S → S' → ℝ := fun s =>
    (aa_maxmin_attained (hP₁ s) (hfin₁ s) (hne₁ s) fun s' => x (s, s')).choose
  have hq₁ : ∀ s, q₁ s ∈ P₁ s ∧ aa_maxmin (P₁ s) (fun s' => x (s, s')) =
      aa_E (q₁ s) fun s' => x (s, s') := fun s =>
    (aa_maxmin_attained (hP₁ s) (hfin₁ s) (hne₁ s) fun s' => x (s, s')).choose_spec
  obtain ⟨q₀, hq₀, hq₀e⟩ := aa_maxmin_attained hP₀ hfin₀ hne₀
    fun s => aa_maxmin (P₁ s) fun s' => x (s, s')
  refine ⟨⟨q₀, hq₀, q₁, fun s => (hq₁ s).1, ?_⟩, ?_⟩
  · rw [hprod, hq₀e]
    congr 1
    funext s
    exact (hq₁ s).2
  · rintro y ⟨r₀, hr₀, r₁, hr₁, rfl⟩
    rw [hprod]
    exact (aa_maxmin_le hP₀ _ hr₀).trans
      (aa_E_mono (hP₀ r₀ hr₀) fun s => aa_maxmin_le (hP₁ s) _ (hr₁ s))

/-- The two full-state priors of the counterexample: the first shock is a fair coin, and the second
is `true` (resp. `false`) for sure. -/
noncomputable def aa_nrPrior (b : Bool) : Bool × Bool → ℝ := fun ω => if ω.2 = b then 1 / 2 else 0

/-- **Without rectangularity the recursion fails** (Miao, p. 693). For the set `{Q_true, Q_false}`
of
priors on `Bool × Bool` (`aa_nrPrior`) and the payoff `x(s, s') = 1{s = s'}`,
`min_Q E^Q x = 1/2`, while the recursion built from the same marginal (a fair coin) and the same
conditionals (`δ_true`, `δ_false` at either first shock) gives `0`. -/
theorem aa_nonrectangular_counterexample :
    aa_maxmin {aa_nrPrior true, aa_nrPrior false} (fun ω => if ω.1 = ω.2 then 1 else 0) = 1 / 2 ∧
      aa_maxmin {aa_ellsbergPrior (1 / 2)} (fun s =>
        aa_maxmin {aa_ellsbergPrior 1, aa_ellsbergPrior 0}
          fun s' => if s = s' then (1 : ℝ) else 0) = 0 := by
  have hE : ∀ b, aa_E (aa_nrPrior b) (fun ω => if ω.1 = ω.2 then (1 : ℝ) else 0) = 1 / 2 := by
    intro b
    cases b <;> simp [aa_E, aa_nrPrior, Fintype.sum_prod_type]
  have hD : ∀ q ∈ ({aa_nrPrior true, aa_nrPrior false} : Set (Bool × Bool → ℝ)),
      SS.IsDistribution q := by
    intro q hq
    rcases hq with rfl | rfl <;>
      exact ⟨fun ω => by unfold aa_nrPrior; positivity,
        by simp [aa_nrPrior, Fintype.sum_prod_type]⟩
  have hD' : ∀ q ∈ ({aa_ellsbergPrior 1, aa_ellsbergPrior 0} : Set (Bool → ℝ)),
      SS.IsDistribution q := by
    intro q hq
    rcases hq with rfl | rfl
    · exact aa_ellsbergPrior_isDistribution zero_le_one le_rfl
    · exact aa_ellsbergPrior_isDistribution le_rfl zero_le_one
  have hin : ∀ s : Bool, aa_maxmin {aa_ellsbergPrior 1, aa_ellsbergPrior 0}
      (fun s' => if s = s' then (1 : ℝ) else 0) = 0 := by
    intro s
    apply le_antisymm
    · cases s
      · have := aa_maxmin_le hD' (fun s' => if false = s' then (1 : ℝ) else 0)
          (Set.mem_insert _ _)
        simpa [aa_E_bool, aa_ellsbergPrior] using this
      · have := aa_maxmin_le hD' (fun s' => if true = s' then (1 : ℝ) else 0)
          (Set.mem_insert_of_mem _ rfl)
        simpa [aa_E_bool, aa_ellsbergPrior] using this
    · refine aa_le_maxmin ⟨_, Set.mem_insert _ _⟩ _ fun q hq => ?_
      unfold aa_E
      exact Finset.sum_nonneg fun s' _ => mul_nonneg ((hD' q hq).nonneg s') (by positivity)
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · have := aa_maxmin_le hD (fun ω => if ω.1 = ω.2 then (1 : ℝ) else 0) (Set.mem_insert _ _)
      rwa [hE] at this
    · refine aa_le_maxmin ⟨_, Set.mem_insert _ _⟩ _ fun q hq => ?_
      rcases hq with rfl | rfl <;> rw [hE]
  · simp only [hin, aa_maxmin_singleton]
    exact aa_E_const (aa_ellsbergPrior_isDistribution (by norm_num) (by norm_num)) 0

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Variational, divergence and multiplier utility

Miao, §20.2.2, pp. 693–696 (static models), on a finite state space `S` with reference
distribution `p`.

* Variational utility `U(c) = min_q {∫ u dq + c(q)}` (`aa_variational`); with zero cost it is
  maxmin utility (`aa_variational_zero`).
* The `w`-weighted `φ`-divergence `D_φʷ(q‖p) = ∫ w φ(dq/dp) dp` (`aa_phiDiv`), with
  `D(p‖p) = 0` and `D ≥ 0` (`aa_phiDiv_self`, `aa_phiDiv_nonneg`), and divergence utility
  `min_q {∫ u dq + θD(q‖p)}` (`aa_divU`). It is at most expected utility under `p` and
  increasing in `θ`: a smaller `θ` is more ambiguity averse (`aa_divU_le_E`, `aa_divU_mono`).
* Relative entropy `φ(x) = x ln x − x + 1` (`aa_klPhi`; `φ ≥ 0`, `φ(1) = 0`, `φ(t)/t → ∞`):
  `D_φ¹(q‖p) = ∫ ln(dq/dp) dq` (`aa_phiDiv_kl`), so divergence utility is the multiplier utility
  of Hansen and Sargent, and solving the minimisation gives the risk-sensitive utility
  `−θ ln ∫ exp(−u/θ) dp` (`aa_multiplier_isLeast`, `aa_divU_kl`). As `θ → ∞` it tends to expected
  utility (`aa_riskSensitive_tendsto`). It is the certainty equivalent of the exponential utility
  `−exp(−x/θ)`, whose absolute risk aversion is `1/θ` (`aa_riskSensitive_eq_ce`,
  `aa_expU_arrowPratt`): "concern for robustness enhances risk aversion by `1/θ`".
* The relative Gini index `φ(x) = (x − 1)²/2` (`aa_chiPhi`): on the domain `c − Ec ≤ θ`, divergence
  utility with `u(c) = c` is the monotone mean–variance utility `E c − Var(c)/(2θ)`, attained by the
  density `1 − (c − Ec)/θ` (`aa_chi2_mmv`).

Not formalised: the probabilistic sophistication of divergence preferences with `w = 1` and their
failure to explain the Ellsberg paradox (results of Maccheroni, Marinacci and Rustichini (2006a)
that the text cites without derivation).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- The set `Δ(S)` of all distributions on `S`. -/
def aa_Δ (S : Type*) [Fintype S] : Set (S → ℝ) := {q | SS.IsDistribution q}

/-- Variational utility `U(c) = inf_{q ∈ Q} {∫ u dq + c(q)}` (Miao, p. 693). -/
noncomputable def aa_variational (Q : Set (S → ℝ)) (cost : (S → ℝ) → ℝ) (u : S → ℝ) : ℝ :=
  sInf ((fun q => aa_E q u + cost q) '' Q)

/-- Miao, p. 694: with zero cost, variational utility is maxmin expected utility. -/
theorem aa_variational_zero (Q : Set (S → ℝ)) (u : S → ℝ) :
    aa_variational Q (fun _ => 0) u = aa_maxmin Q u := by
  simp [aa_variational, aa_maxmin]

/-- The `w`-weighted `φ`-divergence `D_φʷ(q‖p) = ∫ w φ(dq/dp) dp` (Miao, p. 694), with
`dq/dp = q/p`. -/
noncomputable def aa_phiDiv (φ : ℝ → ℝ) (w p q : S → ℝ) : ℝ := ∑ s, w s * φ (q s / p s) * p s

/-- Divergence utility `U(c) = inf_{q ∈ Q} {∫ u dq + θD_φʷ(q‖p)}` (Miao, p. 694). -/
noncomputable def aa_divU (φ : ℝ → ℝ) (w p : S → ℝ) (θ : ℝ) (Q : Set (S → ℝ)) (u : S → ℝ) : ℝ :=
  aa_variational Q (fun q => θ * aa_phiDiv φ w p q) u

/-- `D(p‖p) = 0` when `φ(1) = 0`. -/
theorem aa_phiDiv_self {φ : ℝ → ℝ} (hφ : φ 1 = 0) (w p : S → ℝ) : aa_phiDiv φ w p p = 0 := by
  unfold aa_phiDiv
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases h : p s = 0
  · simp [h]
  · simp [div_self h, hφ]

/-- `D ≥ 0` when `φ ≥ 0`, `w ≥ 0`. -/
theorem aa_phiDiv_nonneg {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) (q : S → ℝ) : 0 ≤ aa_phiDiv φ w p q :=
  Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hw s) (hφ _)) (hp.nonneg s)

theorem aa_divU_bdd {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) {θ : ℝ} (hθ : 0 ≤ θ) {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (u : S → ℝ) :
    BddBelow ((fun q => aa_E q u + θ * aa_phiDiv φ w p q) '' Q) :=
  ⟨-∑ s, |u s|, by
    rintro _ ⟨q, hq, rfl⟩
    have := aa_E_ge_neg (hQ q hq) u
    have := mul_nonneg hθ (aa_phiDiv_nonneg hφ hw hp q)
    dsimp only
    linarith⟩

/-- Divergence utility is at most expected utility under the reference model `p` (Miao, p. 694:
the decision maker takes `p` into account among the nearby models). -/
theorem aa_divU_le_E {φ : ℝ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : φ 1 = 0) {w p : S → ℝ}
    (hw : ∀ s, 0 ≤ w s) (hp : SS.IsDistribution p) {θ : ℝ} (hθ : 0 ≤ θ) {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hpQ : p ∈ Q) (u : S → ℝ) :
    aa_divU φ w p θ Q u ≤ aa_E p u := by
  have := csInf_le (aa_divU_bdd hφ0 hw hp hθ hQ u) ⟨p, hpQ, rfl⟩
  simpa [aa_divU, aa_variational, aa_phiDiv_self hφ1] using this

/-- Miao, p. 694: a smaller `θ` means a larger degree of ambiguity aversion: divergence utility is
increasing in `θ`. -/
theorem aa_divU_mono {φ : ℝ → ℝ} (hφ0 : ∀ x, 0 ≤ φ x) {w p : S → ℝ} (hw : ∀ s, 0 ≤ w s)
    (hp : SS.IsDistribution p) {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ' : θ ≤ θ') {Q : Set (S → ℝ)}
    (hQ : ∀ q ∈ Q, SS.IsDistribution q) (hne : Q.Nonempty) (u : S → ℝ) :
    aa_divU φ w p θ Q u ≤ aa_divU φ w p θ' Q u := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨q, hq, rfl⟩
  refine (csInf_le (aa_divU_bdd hφ0 hw hp hθ hQ u) ⟨q, hq, rfl⟩).trans ?_
  have := mul_le_mul_of_nonneg_right hθθ' (aa_phiDiv_nonneg hφ0 hw hp q)
  dsimp only
  linarith

/-! ### Relative entropy and multiplier utility -/

/-- The relative-entropy index `φ(x) = x ln x − x + 1` (Miao, p. 695). -/
noncomputable def aa_klPhi (x : ℝ) : ℝ := x * Real.log x - x + 1

theorem aa_klPhi_one : aa_klPhi 1 = 0 := by simp [aa_klPhi]

/-- `φ(x) = x ln x − x + 1 ≥ 0` on `ℝ₊`, as the book requires of a divergence index. -/
theorem aa_klPhi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ aa_klPhi x := by
  unfold aa_klPhi
  rcases hx.lt_or_eq with hx | hx
  · have h := Real.one_sub_inv_le_log_of_pos hx
    have : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left h hx.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at this
    linarith
  · subst hx
    simp

/-- `φ(t)/t → ∞` for the relative-entropy index. -/
theorem aa_klPhi_superlinear : Tendsto (fun t => aa_klPhi t / t) atTop atTop := by
  have h : Tendsto (fun t : ℝ => Real.log t - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) Real.tendsto_log_atTop |>.congr fun t => by ring
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [aa_klPhi, le_div_iff₀ ht]
  nlinarith

/-- Miao, p. 695: for `φ(x) = x ln x − x + 1`, `w = 1` and a reference model `p` with full support,
`D_φ¹(q‖p) = ∫ ln(dq/dp) dq`, the relative entropy (Kullback–Leibler divergence). -/
theorem aa_phiDiv_kl {p q : S → ℝ} (hp : SS.IsDistribution p) (hpos : ∀ s, 0 < p s)
    (hq : SS.IsDistribution q) : aa_phiDiv aa_klPhi (fun _ => 1) p q = SS.klDiv q p := by
  unfold aa_phiDiv aa_klPhi SS.klDiv
  have e : ∀ s, 1 * (q s / p s * Real.log (q s / p s) - q s / p s + 1) * p s =
      q s * Real.log (q s / p s) - q s + p s := fun s => by
    field_simp [(hpos s).ne']
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one]
  ring

/-- **Multiplier utility solves to risk-sensitive utility** (Miao, p. 695; Hansen and Sargent):
for `θ > 0`, `min_{q ≪ p} {∫ u dq + θ ∫ ln(dq/dp) dq} = −θ ln ∫ exp(−u/θ) dp`, the minimum being
attained. -/
theorem aa_multiplier_isLeast {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (u : S → ℝ) :
    IsLeast {y | ∃ q, SS.IsDistribution q ∧ SS.AbsCont q p ∧ y = aa_E q u + θ * SS.klDiv q p}
      (-θ * Real.log (∑ s, p s * Real.exp (-u s / θ))) := by
  have key := SS.entropic_isLeast (θ := -θ⁻¹) (by simpa using hθ) hp u
  have e1 : (-θ⁻¹)⁻¹ = -θ := by rw [inv_neg, inv_inv]
  rw [e1] at key
  have e2 : (∑ x, Real.exp (-θ⁻¹ * u x) * p x) = ∑ s, p s * Real.exp (-u s / θ) :=
    Finset.sum_congr rfl fun s _ => by rw [mul_comm]; congr 2; field_simp
  rw [e2] at key
  convert key using 2
  ext y
  simp only [aa_E]
  constructor
  · rintro ⟨q, hq, hac, rfl⟩
    exact ⟨q, hq, hac, by rw [Finset.sum_congr rfl fun s _ => mul_comm (q s) (u s)]; ring⟩
  · rintro ⟨q, hq, hac, rfl⟩
    exact ⟨q, hq, hac, by rw [Finset.sum_congr rfl fun s _ => mul_comm (q s) (u s)]; ring⟩

/-- Miao, p. 695: with a full-support reference model, divergence utility with relative entropy
and `w = 1` over all of `Δ(S)` equals the risk-sensitive utility `−θ ln ∫ exp(−u/θ) dp`. -/
theorem aa_divU_kl {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (u : S → ℝ) :
    aa_divU aa_klPhi (fun _ => 1) p θ (aa_Δ S) u =
      -θ * Real.log (∑ s, p s * Real.exp (-u s / θ)) := by
  refine IsLeast.csInf_eq ?_
  have h := aa_multiplier_isLeast hθ hp u
  have hset : ((fun q => aa_E q u + θ * aa_phiDiv aa_klPhi (fun _ => 1) p q) '' aa_Δ S) =
      {y | ∃ q, SS.IsDistribution q ∧ SS.AbsCont q p ∧ y = aa_E q u + θ * SS.klDiv q p} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, fun s hs => absurd hs (hpos s).ne', by dsimp only; rw [aa_phiDiv_kl hp hpos hq]⟩
    · rintro ⟨q, hq, -, rfl⟩
      exact ⟨q, hq, by dsimp only; rw [aa_phiDiv_kl hp hpos hq]⟩
  rwa [hset]

/-- Miao, p. 694: "when `θ` goes to infinity, the model reduces to expected utility":
`−θ ln ∫ exp(−u/θ) dp → ∫ u dp` as `θ → ∞`. -/
theorem aa_riskSensitive_tendsto {p : S → ℝ} (hp : SS.IsDistribution p) (u : S → ℝ) :
    Tendsto (fun θ => -θ * Real.log (∑ s, p s * Real.exp (-u s / θ))) atTop (𝓝 (aa_E p u)) := by
  have h1 := aa_tendsto_logmgf hp (fun s => -u s)
  have h2 : Tendsto (fun θ : ℝ => θ⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_mono_right (fun x hx => ne_of_gt hx) tendsto_inv_atTop_nhdsGT_zero
  have h3 := (h1.comp h2).neg
  have hE : -aa_E p (fun s => -u s) = aa_E p u := by
    simp [aa_E, Finset.sum_neg_distrib]
  rw [hE] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  have e : ∀ s, θ⁻¹ * -u s = -u s / θ := fun s => by ring
  simp only [Function.comp_apply, inv_inv, e]
  ring

/-- The exponential utility `u(x) = −exp(−x/θ)`. -/
noncomputable def aa_expU (θ x : ℝ) : ℝ := -Real.exp (-x / θ)

/-- Miao, p. 695: risk-sensitive utility is the certainty equivalent of the exponential utility,
`u(−θ ln E exp(−x/θ)) = E u(x)`. -/
theorem aa_riskSensitive_eq_ce {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    [Nonempty S] (x : S → ℝ) :
    aa_expU θ (-θ * Real.log (∑ s, p s * Real.exp (-x s / θ))) =
      aa_E p fun s => aa_expU θ (x s) := by
  have hpos : 0 < ∑ s, p s * Real.exp (-x s / θ) := aa_E_pos hp fun s => Real.exp_pos _
  unfold aa_expU
  rw [show -(-θ * Real.log (∑ s, p s * Real.exp (-x s / θ))) / θ =
    Real.log (∑ s, p s * Real.exp (-x s / θ)) by field_simp, Real.exp_log hpos]
  simp [aa_E, Finset.sum_neg_distrib]

/-- Miao, p. 695: "concern for robustness enhances risk aversion by `1/θ`": the exponential
utility has `u'(x) = θ⁻¹e^{−x/θ}`, `u''(x) = −θ⁻²e^{−x/θ}`, so absolute risk aversion
`−u''/u' = 1/θ`. -/
theorem aa_expU_arrowPratt {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (aa_expU θ) (θ⁻¹ * Real.exp (-x / θ)) x ∧
      HasDerivAt (fun y => θ⁻¹ * Real.exp (-y / θ)) (-θ⁻¹ * (θ⁻¹ * Real.exp (-x / θ))) x ∧
      -(-θ⁻¹ * (θ⁻¹ * Real.exp (-x / θ))) / (θ⁻¹ * Real.exp (-x / θ)) = θ⁻¹ := by
  have hd : HasDerivAt (fun y : ℝ => -y / θ) (-1 / θ) x := by
    simpa using ((hasDerivAt_id x).neg.div_const θ)
  refine ⟨?_, ?_, ?_⟩
  · have e : aa_expU θ = fun y => -Real.exp (-y / θ) := rfl
    rw [e]
    convert hd.exp.neg using 1
    field_simp
  · have := hd.exp.const_mul θ⁻¹
    convert this using 1
    field_simp
  · have : Real.exp (-x / θ) ≠ 0 := (Real.exp_pos _).ne'
    field_simp

/-! ### The relative Gini concentration index and monotone mean–variance utility -/

/-- The relative Gini concentration index (`χ²` divergence) `φ(x) = (x − 1)²/2` (Miao, p. 695). -/
noncomputable def aa_chiPhi (x : ℝ) : ℝ := (x - 1) ^ 2 / 2

theorem aa_chiPhi_one : aa_chiPhi 1 = 0 := by simp [aa_chiPhi]

theorem aa_chiPhi_nonneg (x : ℝ) : 0 ≤ aa_chiPhi x := by unfold aa_chiPhi; positivity

/-- `φ(t)/t → ∞` for the Gini index. -/
theorem aa_chiPhi_superlinear : Tendsto (fun t => aa_chiPhi t / t) atTop atTop := by
  have h0 : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have h : Tendsto (fun t : ℝ => t / 2 + -1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) h0
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [aa_chiPhi, le_div_iff₀ ht]
  nlinarith

/-- The variance `Var_p(x) = E_p (x − E_p x)²`. -/
noncomputable def aa_Var (p x : S → ℝ) : ℝ := aa_E p fun s => (x s - aa_E p x) ^ 2

/-- The completed square behind the monotone mean–variance formula: for every distribution `q`,
`E_q x + θD_χ²(q‖p) = E_p x − Var_p(x)/(2θ) + ∑ p (θ/2)(q/p − 1 + (x − E_p x)/θ)²`. -/
theorem aa_chi2_identity {θ : ℝ} (hθ : 0 < θ) {p q : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (hq : SS.IsDistribution q) (x : S → ℝ) :
    aa_E q x + θ * aa_phiDiv aa_chiPhi (fun _ => 1) p q =
      aa_E p x - aa_Var p x / (2 * θ) +
        ∑ s, p s * (θ / 2 * (q s / p s - 1 + (x s - aa_E p x) / θ) ^ 2) := by
  set m := aa_E p x with hm
  have hterm : ∀ s, q s * x s + θ * (1 * aa_chiPhi (q s / p s) * p s) =
      p s * x s - p s * (x s - m) ^ 2 / (2 * θ) +
        p s * (θ / 2 * (q s / p s - 1 + (x s - m) / θ) ^ 2) + m * (q s - p s) := fun s => by
    unfold aa_chiPhi
    field_simp [(hpos s).ne']
    ring
  have hsum : ∑ s, m * (q s - p s) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one, sub_self, mul_zero]
  unfold aa_E aa_phiDiv aa_Var
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun s _ => hterm s,
    Finset.sum_add_distrib, hsum, add_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div]
  rfl

/-- **Monotone mean–variance utility** (Miao, pp. 695–696; Maccheroni, Marinacci and Rustichini
(2006a)). For `φ(x) = (x − 1)²/2`, `w = 1`, `θ > 0` and a full-support reference model `p`, on the
domain `c − E c ≤ θ` divergence utility with `u(c) = c` is `E c − Var(c)/(2θ)`, attained at the
density `dq*/dp = 1 − (c − E c)/θ`. -/
theorem aa_chi2_mmv {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (c : S → ℝ) (hdom : ∀ s, c s - aa_E p c ≤ θ) :
    IsLeast ((fun q => aa_E q c + θ * aa_phiDiv aa_chiPhi (fun _ => 1) p q) '' aa_Δ S)
      (aa_E p c - aa_Var p c / (2 * θ)) := by
  set qs : S → ℝ := fun s => p s * (1 - (c s - aa_E p c) / θ) with hqs
  have hqsD : SS.IsDistribution qs := by
    refine ⟨fun s => mul_nonneg (hp.nonneg s) ?_, ?_⟩
    · rw [sub_nonneg, div_le_one hθ]
      exact hdom s
    · have h1 : ∑ s, p s * (c s - aa_E p c) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_eq_one, one_mul]
        unfold aa_E
        ring
      have h2 : ∑ s, qs s = ∑ s, p s - (∑ s, p s * (c s - aa_E p c)) / θ := by
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by simp only [hqs]; ring
      rw [h2, h1, hp.sum_eq_one]
      simp
  refine ⟨⟨qs, hqsD, ?_⟩, ?_⟩
  · dsimp only
    rw [aa_chi2_identity hθ hp hpos hqsD c]
    have h0 : ∀ s, p s * (θ / 2 * (qs s / p s - 1 + (c s - aa_E p c) / θ) ^ 2) = 0 := fun s => by
      simp only [hqs]
      rw [mul_div_cancel_left₀ _ (hpos s).ne']
      ring
    simp [h0]
  · rintro _ ⟨q, hq, rfl⟩
    dsimp only
    rw [aa_chi2_identity hθ hp hpos hq c]
    have : 0 ≤ ∑ s, p s * (θ / 2 * (q s / p s - 1 + (c s - aa_E p c) / θ) ^ 2) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (hp.nonneg s) (by positivity)
    linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive divergence utility

Miao, §20.2.2, pp. 696–697: belief distortions as a martingale (20.8) and the recursive divergence
utility, on a finite event tree with one-step-ahead reference distributions `p h` and a finite
horizon (`U_T = u(c_T)`).

* A one-step density `m_{t+1} = π̂(s_{t+1}|s_t)/π(s_{t+1}|s_t)` at the node `h` is a nonnegative
  `m : S → ℝ` with `E_t m = 1` (`aa_Admissible`); the distortion `M_{t+1} = m_{t+1}M_t`, `M₀ = 1`
  (20.8) (`aa_M`) is a martingale (`aa_M_martingale`).
* `R_t(x) = min_m E_t[m x + θ w φ(m)]` (`aa_divR`) and the recursive divergence utility
  `U_t = u(c_t) + βR_t(U_{t+1})` (`aa_rdU`); with a fixed distortion, `aa_rdUm`.
* The time-zero formula: for fixed distortions,
  `U₀ = E ∑_t βᵗ M_t {u(c_t) + βθE_t[w_{t+1}φ(m_{t+1})]}` (with no penalty in the last period)
  (`aa_rdUm_eq_sum`), by unrolling under the distorted measure (`aa_rdUm_unroll`) and changing
  measure with the martingale `M` (`aa_Ex_change`).
* Dynamic consistency: the recursive utility is the infimum over all adapted distortion processes of
  the time-zero formula (`aa_rdU_isGLB`), so the recursion and the time-zero minimisation agree.
* With relative entropy and `w = 1`, `R_t` is the risk-sensitive operator
  `−θ ln E_t exp(−x/θ)` (`aa_divR_kl`): the recursive multiplier utility.

Departure: the book's horizon is infinite; here it is finite, and the infimum over distortions is an
infimum (it is attained, e.g., for relative entropy, `aa_divR_kl`).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- An admissible one-step-ahead density at a node with reference distribution `p`:
`m ≥ 0`, `E[m] = 1`. -/
def aa_Admissible (p m : S → ℝ) : Prop := (∀ s, 0 ≤ m s) ∧ ∑ s, p s * m s = 1

/-- The constant density `m = 1` (no distortion) is admissible. -/
theorem aa_admissible_one {p : S → ℝ} (hp : SS.IsDistribution p) : aa_Admissible p fun _ => 1 :=
  ⟨fun _ => zero_le_one, by simp [hp.sum_eq_one]⟩

/-- The distorted one-step distribution `π̂ = m π` is a distribution. -/
theorem aa_admissible_isDistribution {p m : S → ℝ} (hp : SS.IsDistribution p)
    (hm : aa_Admissible p m) : SS.IsDistribution fun s => p s * m s :=
  ⟨fun s => mul_nonneg (hp.nonneg s) (hm.1 s), hm.2⟩

/-- The martingale `M_{t+1} = m_{t+1}M_t`, `M₀ = 1`, of (20.8). -/
def aa_M (m : List S → S → ℝ) : List S → ℝ
  | [] => 1
  | s :: h => m h s * aa_M m h

/-- Miao, (20.8), p. 696: `M` is a martingale under the reference measure, `E_t M_{t+1} = M_t`. -/
theorem aa_M_martingale {p : List S → S → ℝ} {m : List S → S → ℝ}
    (hm : ∀ h, aa_Admissible (p h) (m h)) (h : List S) :
    ∑ s, p h s * aa_M m (s :: h) = aa_M m h := by
  simp only [aa_M, ← mul_assoc, ← Finset.sum_mul, (hm h).2, one_mul]

/-- The objective `E_t[m x + θ w φ(m)]` at a node. -/
def aa_divObj (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x m : S → ℝ) : ℝ :=
  ∑ s, p s * (m s * x s + θ * w s * φ (m s))

/-- The divergence uncertainty aggregator `R_t(x) = inf_m E_t[m x + θwφ(m)]`, `E_t m = 1`. -/
noncomputable def aa_divR (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x : S → ℝ) : ℝ :=
  sInf ((aa_divObj p w θ φ x) '' {m | aa_Admissible p m})

/-- The recursive divergence utility `U_t = u(c_t) + βR_t(U_{t+1})`, `U_T = u(c_T)`
(Miao, p. 696). -/
noncomputable def aa_rdU (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w : List S → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h => u (c h) + β * aa_divR (p h) (w h) θ φ fun s => aa_rdU u β θ φ p w c n (s :: h)

/-- The same recursion for a fixed adapted distortion process `m`. -/
def aa_rdUm (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => u (c h)
  | n + 1, h =>
    u (c h) + β * aa_divObj (p h) (w h) θ φ (fun s => aa_rdUm u β θ φ p w m c n (s :: h)) (m h)

/-- The objective is bounded below on admissible densities (`θ, w, φ ≥ 0`). -/
theorem aa_divObj_ge {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s) {θ : ℝ}
    (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (x : S → ℝ) {m : S → ℝ}
    (hm : aa_Admissible p m) : -∑ s, |x s| ≤ aa_divObj p w θ φ x m := by
  have h1 := aa_E_ge_neg (aa_admissible_isDistribution hp hm) x
  have h2 : aa_E (fun s => p s * m s) x ≤ aa_divObj p w θ φ x m := by
    unfold aa_E aa_divObj
    refine Finset.sum_le_sum fun s _ => ?_
    have := mul_nonneg (mul_nonneg (mul_nonneg hθ (hw s)) (hφ (m s))) (hp.nonneg s)
    nlinarith
  linarith

theorem aa_divR_le {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s) {θ : ℝ}
    (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (x : S → ℝ) {m : S → ℝ}
    (hm : aa_Admissible p m) : aa_divR p w θ φ x ≤ aa_divObj p w θ φ x m :=
  csInf_le ⟨-∑ s, |x s|, by rintro _ ⟨m', hm', rfl⟩; exact aa_divObj_ge hp hw hθ hφ x hm'⟩
    ⟨m, hm, rfl⟩

/-- The objective changes by `E_t[m(x − y)]` when the continuation changes from `y` to `x`. -/
theorem aa_divObj_sub (p w : S → ℝ) (θ : ℝ) (φ : ℝ → ℝ) (x y m : S → ℝ) :
    aa_divObj p w θ φ x m - aa_divObj p w θ φ y m = ∑ s, p s * m s * (x s - y s) := by
  unfold aa_divObj
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `t`-step expectations under the distorted measure `π̂ = mπ`. -/
def aa_distort (p m : List S → S → ℝ) : List S → S → ℝ := fun h s => p h s * m h s

/-- Unrolling the recursion for a fixed distortion: under the distorted measure,
`U_n(h) = ∑_{t<n} βᵗ Ê_h[g(h_t)] + βⁿ Ê_h[u(c_{h_n})]` with the flow
`g = u(c_t) + βθE_t[wφ(m)]`. -/
theorem aa_rdUm_unroll (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) (n : ℕ) (h : List S) :
    aa_rdUm u β θ φ p w m c n h =
      ∑ t ∈ Finset.range n, β ^ t * aa_Ex (aa_distort p m) t
          (fun h' => u (c h') + β * θ * ∑ s, p h' s * w h' s * φ (m h' s)) h +
        β ^ n * aa_Ex (aa_distort p m) n (fun h' => u (c h')) h := by
  refine aa_linear_unroll _ β _ _ (aa_rdUm u β θ φ p w m c) (fun _ => rfl) (fun n h => ?_) n h
  simp only [aa_rdUm, aa_divObj, aa_distort]
  rw [add_assoc]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Change of measure with the martingale `M`: `M(h) Ê_h[f(h_t)] = E_h[M(h_t) f(h_t)]`. -/
theorem aa_Ex_change (p m : List S → S → ℝ) (f : List S → ℝ) :
    ∀ t h, aa_M m h * aa_Ex (aa_distort p m) t f h =
      aa_Ex p t (fun h' => aa_M m h' * f h') h
  | 0, h => rfl
  | t + 1, h => by
    simp only [aa_Ex, aa_distort, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← aa_Ex_change p m f t (s :: h), aa_M]
    ring

/-- **The time-zero divergence utility** (Miao, p. 696): for a fixed adapted distortion process,
`U₀(c) = E ∑_{t<T} βᵗ M_t{u(c_t) + βθE_t[w_{t+1}φ(m_{t+1})]} + βᵀE[M_T u(c_T)]`; the penalty
terms form the discounted divergence `β ∑_t βᵗ E[M_t w_{t+1}φ(m_{t+1})]`. -/
theorem aa_rdUm_eq_sum (u : ℝ → ℝ) (β θ : ℝ) (φ : ℝ → ℝ) (p w m : List S → S → ℝ)
    (c : List S → ℝ) (n : ℕ) :
    aa_rdUm u β θ φ p w m c n [] =
      ∑ t ∈ Finset.range n, β ^ t * aa_Ex p t
          (fun h' => aa_M m h' * (u (c h') + β * θ * ∑ s, p h' s * w h' s * φ (m h' s))) [] +
        β ^ n * aa_Ex p n (fun h' => aa_M m h' * u (c h')) [] := by
  rw [aa_rdUm_unroll]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [← aa_Ex_change, aa_M, one_mul]
  · rw [← aa_Ex_change, aa_M, one_mul]

/-- The recursive utility is a lower bound for every distortion process (`θ, w, φ ≥ 0`, `β ≥ 0`). -/
theorem aa_rdU_le_rdUm (u : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hθ : 0 ≤ θ) {φ : ℝ → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) {p w m : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (hw : ∀ h s, 0 ≤ w h s) (hm : ∀ h, aa_Admissible (p h) (m h)) (c : List S → ℝ) :
    ∀ n h, aa_rdU u β θ φ p w c n h ≤ aa_rdUm u β θ φ p w m c n h
  | 0, h => le_rfl
  | n + 1, h => by
    simp only [aa_rdU, aa_rdUm]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hβ)
    refine (aa_divR_le (hp h) (hw h) hθ hφ _ (hm h)).trans ?_
    have := aa_divObj_sub (p h) (w h) θ φ (fun s => aa_rdUm u β θ φ p w m c n (s :: h))
      (fun s => aa_rdU u β θ φ p w c n (s :: h)) (m h)
    have h2 : 0 ≤ ∑ s, p h s * m h s *
        (aa_rdUm u β θ φ p w m c n (s :: h) - aa_rdU u β θ φ p w c n (s :: h)) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg ((hp h).nonneg s) ((hm h).1 s))
        (sub_nonneg.2 (aa_rdU_le_rdUm u hβ hθ hφ hp hw hm c n (s :: h)))
    linarith

/-- **Dynamic consistency of recursive divergence utility** (Miao, p. 696). For `0 ≤ β ≤ 1`,
`θ ≥ 0`, `w ≥ 0`, `φ ≥ 0`, the recursive utility at every node is the infimum, over all adapted
distortion processes, of the utility under a fixed distortion, which is the time-zero formula
`aa_rdUm_eq_sum`. -/
theorem aa_rdU_isGLB (u : ℝ → ℝ) {β θ : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ)
    {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {p w : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (hw : ∀ h s, 0 ≤ w h s) (c : List S → ℝ) (n : ℕ) (h : List S) :
    IsGLB {y | ∃ m : List S → S → ℝ, (∀ h', aa_Admissible (p h') (m h')) ∧
        y = aa_rdUm u β θ φ p w m c n h} (aa_rdU u β θ φ p w c n h) := by
  classical
  refine ⟨by rintro y ⟨m, hm, rfl⟩; exact aa_rdU_le_rdUm u hβ hθ hφ hp hw hm c n h, ?_⟩
  intro b hb
  by_contra hlt
  push Not at hlt
  set ε := b - aa_rdU u β θ φ p w c n h with hε
  have hε0 : 0 < ε := by linarith
  set δ := ε / (n + 1 : ℝ) with hδ
  have hδ0 : 0 < δ := by positivity
  set N := n + h.length with hN
  -- near-minimising densities at every node
  have hnear : ∀ h' : List S, ∃ m' : S → ℝ, aa_Admissible (p h') m' ∧
      aa_divObj (p h') (w h') θ φ
          (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h')) m' <
        aa_divR (p h') (w h') θ φ
          (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h')) + δ := by
    intro h'
    have hne : ((aa_divObj (p h') (w h') θ φ
        (fun s => aa_rdU u β θ φ p w c (N - h'.length - 1) (s :: h'))) ''
          {m | aa_Admissible (p h') m}).Nonempty :=
      ⟨_, _, aa_admissible_one (hp h'), rfl⟩
    obtain ⟨_, ⟨m', hm', rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hδ0)
    exact ⟨m', hm', hlt'⟩
  choose m hm hmlt using hnear
  have key : ∀ k h', h'.length + k = N →
      aa_rdUm u β θ φ p w m c k h' ≤ aa_rdU u β θ φ p w c k h' + k * δ := by
    intro k
    induction k with
    | zero => intro h' _; simp [aa_rdUm, aa_rdU]
    | succ k ih =>
      intro h' hlen
      have hidx : N - h'.length - 1 = k := by omega
      have hm' := hmlt h'
      rw [hidx] at hm'
      simp only [aa_rdU, aa_rdUm]
      have hsub := aa_divObj_sub (p h') (w h') θ φ
        (fun s => aa_rdUm u β θ φ p w m c k (s :: h'))
        (fun s => aa_rdU u β θ φ p w c k (s :: h')) (m h')
      have hbound : ∑ s, p h' s * m h' s *
          (aa_rdUm u β θ φ p w m c k (s :: h') - aa_rdU u β θ φ p w c k (s :: h')) ≤ k * δ := by
        calc ∑ s, p h' s * m h' s *
              (aa_rdUm u β θ φ p w m c k (s :: h') - aa_rdU u β θ φ p w c k (s :: h'))
            ≤ ∑ s, p h' s * m h' s * (k * δ) :=
              Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
                (by linarith [ih (s :: h') (by simp only [List.length_cons]; omega)])
                (mul_nonneg ((hp h').nonneg s) ((hm h').1 s))
          _ = k * δ := by rw [← Finset.sum_mul, (hm h').2, one_mul]
      have h3 : aa_divObj (p h') (w h') θ φ (fun s => aa_rdUm u β θ φ p w m c k (s :: h')) (m h')
          ≤ aa_divR (p h') (w h') θ φ (fun s => aa_rdU u β θ φ p w c k (s :: h')) +
            (k * δ + δ) := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hβ
      have h5 : β * (k * δ + δ) ≤ (k + 1 : ℕ) * δ := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hδ0.le]
      nlinarith
  have := key n h (by omega)
  have hnδ : (n : ℝ) * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hb' := hb ⟨m, hm, rfl⟩
  linarith

/-- Miao, pp. 695–696: with relative entropy, `w = 1` and a full-support reference distribution,
`R_t(x) = min_m E_t[m x + θ m ln m − θ m + θ] = −θ ln E_t exp(−x/θ)`: recursive divergence utility
is the recursive multiplier (risk-sensitive) utility. -/
theorem aa_divR_kl {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ} (hp : SS.IsDistribution p)
    (hpos : ∀ s, 0 < p s) (x : S → ℝ) :
    aa_divR p (fun _ => 1) θ aa_klPhi x = -θ * Real.log (∑ s, p s * Real.exp (-x s / θ)) := by
  rw [← aa_divU_kl hθ hp hpos x]
  unfold aa_divR aa_divU aa_variational
  congr 1
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨fun s => p s * m s, aa_admissible_isDistribution hp hm, ?_⟩
    simp only [aa_E, aa_phiDiv, aa_divObj, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [mul_div_cancel_left₀ _ (hpos s).ne']
      ring
  · rintro ⟨q, hq, rfl⟩
    refine ⟨fun s => q s / p s, ⟨fun s => div_nonneg (hq.nonneg s) (hpos s).le, ?_⟩, ?_⟩
    · rw [← hq.sum_eq_one]
      exact Finset.sum_congr rfl fun s _ => by field_simp [(hpos s).ne']
    · simp only [aa_E, aa_phiDiv, aa_divObj, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by
        field_simp [(hpos s).ne']

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Smooth ambiguity utility

Miao, §20.2.2, pp. 697–701: the static smooth ambiguity model (20.9) of Klibanoff, Marinacci and
Mukerji, the generalized recursive smooth ambiguity model (20.10) of Hayashi–Miao and Ju–Miao,
the homothetic specification (20.11)–(20.15) and its limits (20.16)–(20.18), and the nested models
(Hansen–Sargent multiplier with hidden states; (20.19)).

The hidden state `z` ranges over a finite type `Z`, with prior (posterior) `μ` and likelihoods
`π z` on the finite state space `S`.

* (20.9) and its Bayesian reduction: with affine `v` the model is subjective expected utility
  under the predictive distribution `∑ μ(z)π_z` (`aa_kmm_affine`); with concave `v` the smooth
  ambiguity index is below the Bayesian one (`aa_kmm_concave_le`).
* (20.10): the certainty equivalent `M(x) = v⁻¹(E_μ v(u⁻¹(E_{π_z} u(x))))` (`aa_smoothM`); when
  `v ∘ u⁻¹` is affine, `M(x) = u⁻¹(E u(x))` under the predictive distribution, Epstein–Zin with
  hidden states (`aa_smoothM_linear`). Bayes' rule (`aa_posterior`, `aa_posterior_isDistribution`,
  `aa_posterior_martingale`).
* (20.12)–(20.15): with power `u` and `v`, `M` is (20.15) (`aa_smoothM_power`); the recursion
  (20.14) on the tree (`aa_juU`). For `η = γ` it is Epstein–Zin under the predictive distribution
  (`aa_ju_neutral`, `aa_juU_neutral`); `M` (hence `U`) is decreasing in `η`
  (`aa_ju_antitone`, `aa_W_ju_antitone`), and `η ≥ γ` (`η ≤ γ`) puts it below (above) the
  Epstein–Zin value (`aa_ju_le_KP`, `aa_KP_le_ju`). The power-mean inequality behind these is
  `aa_powMean_mono`.
* (20.16): the limit `ρ → 1` of the CES aggregator is Cobb–Douglas (`aa_W_tendsto_rho_one`), and
  `V = ln U` then satisfies (20.16) (`eq_20_16`). (20.17): the limit `γ → 1` (`eq_20_17`).
  (20.18): the limit `η → ∞` (`eq_20_18`).
* Hansen–Sargent multiplier preferences with hidden states (`aa_smoothM_exp`), which are
  Kreps–Porteus–Epstein–Zin when `θ₁ = θ₂` (`aa_smoothM_exp_equal`, footnote 2).
* (20.19) of Klibanoff et al. (2009) is the case `u = id` of (20.10) (`eq_20_19`); with power
  utility and `γ > 1` it is not well defined since `E u(c) < 0` lies outside the domain of
  `φ(x) = x^{1−α}/(1−α)` (`aa_juMiao_illDefined`); with `γ = ρ ∈ (0, 1)` and
  `α = 1 − (1 − η)/(1 − γ)`, (20.14)–(20.15) is ordinally equivalent to (20.19)
  (`aa_juMiao_ordinal`); the exponential `φ` is always well defined (`aa_smoothM_expPhi`).

Not formalised: the remark that the exponential specification lacks homogeneity (no statement).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S Z : Type*} [Fintype S] [Fintype Z]

/-! ### Power means -/

/-- Jensen's inequality for `t ↦ tᵏ` convex on `(0, ∞)`. -/
theorem aa_jensen_rpow {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {k : ℝ}
    (hk : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k) {y : Z → ℝ} (hy : ∀ z, 0 < y z) :
    (∑ z, μ z * y z) ^ k ≤ ∑ z, μ z * y z ^ k := by
  have := hk.map_sum_le (t := Finset.univ) (w := μ) (p := y) (fun z _ => hμ.nonneg z)
    hμ.sum_eq_one (fun z _ => hy z)
  simpa [smul_eq_mul] using this

/-- The power mean `(∑ μ yʳ)^{1/r}`. -/
noncomputable def aa_powMean (r : ℝ) (μ y : Z → ℝ) : ℝ := (∑ z, μ z * y z ^ r) ^ r⁻¹

/-- **The power-mean inequality**: for `r ≤ r'`, both nonzero, `M_r(y) ≤ M_{r'}(y)`. -/
theorem aa_powMean_mono [Nonempty Z] {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {y : Z → ℝ}
    (hy : ∀ z, 0 < y z) {r r' : ℝ} (hr : r ≠ 0) (hr' : r' ≠ 0) (hrr : r ≤ r') :
    aa_powMean r μ y ≤ aa_powMean r' μ y := by
  have hpos : ∀ t : ℝ, 0 < ∑ z, μ z * y z ^ t := fun t =>
    aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hy z) t
  have hpow : ∀ z (a b : ℝ), (y z ^ a) ^ b = y z ^ (a * b) := fun z a b =>
    (Real.rpow_mul (hy z).le a b).symm
  unfold aa_powMean
  rcases lt_or_gt_of_ne hr with hneg | hpos'
  · -- `r < 0`: Jensen for `t ↦ t^{r/r'}` applied to `y^{r'}`
    set k := r / r' with hk
    have hconv : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k := by
      rcases lt_or_gt_of_ne hr' with hneg' | hpos''
      · have hk1 : 1 ≤ k := by rw [hk, le_div_iff_of_neg hneg']; linarith
        exact (convexOn_rpow hk1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
      · exact SS.convexOn_rpow_of_neg (div_neg_of_neg_of_pos hneg hpos'')
    have hJ := aa_jensen_rpow hμ hconv fun z => Real.rpow_pos_of_pos (hy z) r'
    have e1 : ∀ z, (y z ^ r') ^ k = y z ^ r := fun z => by
      rw [hpow, hk, mul_div_cancel₀ _ hr']
    simp only [e1] at hJ
    have h2 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (hpos r') k) hJ
      (inv_lt_zero.2 hneg).le
    rwa [← Real.rpow_mul (hpos r').le, hk, div_mul_eq_mul_div, mul_inv_cancel₀ hr,
      one_div] at h2
  · -- `r > 0`: Jensen for `t ↦ t^{r'/r}` applied to `y^r`
    set k := r' / r with hk
    have hk1 : 1 ≤ k := by rw [hk, le_div_iff₀ hpos']; linarith
    have hconv : ConvexOn ℝ (Set.Ioi 0) fun t : ℝ => t ^ k :=
      (convexOn_rpow hk1).subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
    have hJ := aa_jensen_rpow hμ hconv fun z => Real.rpow_pos_of_pos (hy z) r
    have e1 : ∀ z, (y z ^ r) ^ k = y z ^ r' := fun z => by
      rw [hpow, hk, mul_div_cancel₀ _ hr]
    simp only [e1] at hJ
    have hr'0 : 0 < r' := hpos'.trans_le hrr
    have h2 := Real.rpow_le_rpow (Real.rpow_pos_of_pos (hpos r) k).le hJ (inv_pos.2 hr'0).le
    rwa [← Real.rpow_mul (hpos r).le, hk, div_mul_eq_mul_div, mul_inv_cancel₀ hr'.symm.symm,
      one_div] at h2

/-! ### The static model (20.9) -/

/-- The predictive distribution `p(s) = ∑_z μ(z)π_z(s)`. -/
def aa_predictive (μ : Z → ℝ) (π : Z → S → ℝ) : S → ℝ := fun s => ∑ z, μ z * π z s

theorem aa_predictive_isDistribution {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) : SS.IsDistribution (aa_predictive μ π) := by
  refine ⟨fun s => Finset.sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) ((hπ z).nonneg s), ?_⟩
  unfold aa_predictive
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, (hπ _).sum_eq_one, hμ.sum_eq_one]

/-- Expectation under the predictive distribution is the average of the model expectations. -/
theorem aa_E_predictive (μ : Z → ℝ) (π : Z → S → ℝ) (f : S → ℝ) :
    aa_E (aa_predictive μ π) f = ∑ z, μ z * aa_E (π z) f := by
  simp only [aa_E, aa_predictive, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => by ring

/-- The smooth ambiguity utility (20.9): `U(c) = v⁻¹(∫ v(∫ u(c) dq) dμ(q))`, with the inverse
`vinv` of `v` supplied. -/
noncomputable def aa_kmmU (u v vinv : ℝ → ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (c : S → ℝ) : ℝ :=
  vinv (∑ z, μ z * v (aa_E (π z) fun s => u (c s)))

/-- Miao, p. 697: with an affine `v` (ambiguity neutrality) the smooth ambiguity model (20.9) is
subjective expected utility under the predictive distribution. -/
theorem aa_kmm_affine {u v vinv : ℝ → ℝ} {a b : ℝ} (hv : ∀ y, v y = a * y + b)
    (hinv : ∀ y, vinv (v y) = y) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (π : Z → S → ℝ)
    (c : S → ℝ) : aa_kmmU u v vinv μ π c = aa_E (aa_predictive μ π) fun s => u (c s) := by
  unfold aa_kmmU
  have : ∑ z, μ z * v (aa_E (π z) fun s => u (c s)) =
      v (aa_E (aa_predictive μ π) fun s => u (c s)) := by
    simp only [hv, aa_E_predictive, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      hμ.sum_eq_one, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [this, hinv]

/-- Miao, p. 697: an ambiguity-averse decision maker (concave `v`) values a plan below the Bayesian
(expected-utility under the predictive distribution) decision maker:
`∫ v(∫ u dq) dμ ≤ v(∫ u d p̄)`. -/
theorem aa_kmm_concave_le {u v : ℝ → ℝ} {I : Set ℝ} (hv : ConcaveOn ℝ I v) {μ : Z → ℝ}
    (hμ : SS.IsDistribution μ) (π : Z → S → ℝ) (c : S → ℝ)
    (hI : ∀ z, (aa_E (π z) fun s => u (c s)) ∈ I) :
    ∑ z, μ z * v (aa_E (π z) fun s => u (c s)) ≤
      v (aa_E (aa_predictive μ π) fun s => u (c s)) := by
  have := hv.le_map_sum (t := Finset.univ) (w := μ) (fun z _ => hμ.nonneg z) hμ.sum_eq_one
    (fun z _ => hI z)
  simpa [smul_eq_mul, aa_E_predictive] using this

/-! ### The generalized recursive model (20.10) -/

/-- The certainty equivalent of (20.10): `M(x) = v⁻¹(E_μ v(u⁻¹(E_{π_z} u(x))))`. -/
noncomputable def aa_smoothM (u uinv v vinv : ℝ → ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) :
    ℝ :=
  vinv (∑ z, μ z * v (uinv (aa_E (π z) fun s => u (x s))))

/-- Miao, p. 698: when `v ∘ u⁻¹` is affine, (20.10) reduces to Epstein–Zin with hidden states:
`M(x) = u⁻¹(E u(x))` under the predictive distribution. -/
theorem aa_smoothM_linear {u uinv v vinv : ℝ → ℝ} {a b : ℝ}
    (hvu : ∀ y, v (uinv y) = a * y + b) (hinv : ∀ y, vinv (v (uinv y)) = uinv y)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (π : Z → S → ℝ) (x : S → ℝ) :
    aa_smoothM u uinv v vinv μ π x = uinv (aa_E (aa_predictive μ π) fun s => u (x s)) := by
  unfold aa_smoothM
  have : ∑ z, μ z * v (uinv (aa_E (π z) fun s => u (x s))) =
      v (uinv (aa_E (aa_predictive μ π) fun s => u (x s))) := by
    simp only [hvu, aa_E_predictive, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      hμ.sum_eq_one, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [this, hinv]

/-- Bayes' rule: the posterior over hidden states after observing `s`. -/
noncomputable def aa_posterior (μ : Z → ℝ) (π : Z → S → ℝ) (s : S) : Z → ℝ :=
  fun z => μ z * π z s / aa_predictive μ π s

/-- Miao, p. 698: the posterior obtained by Bayes' rule is a distribution when the observation has
positive predictive probability. -/
theorem aa_posterior_isDistribution {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {s : S} (hs : 0 < aa_predictive μ π s) :
    SS.IsDistribution (aa_posterior μ π s) :=
  ⟨fun z => div_nonneg (mul_nonneg (hμ.nonneg z) ((hπ z).nonneg s)) hs.le, by
    simp only [aa_posterior, ← Finset.sum_div]
    exact div_self hs.ne'⟩

/-- The posterior is a martingale: its predictive expectation is the prior. -/
theorem aa_posterior_martingale {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) (z : Z) :
    ∑ s, aa_predictive μ π s * aa_posterior μ π s z = μ z := by
  have e : ∀ s, aa_predictive μ π s * aa_posterior μ π s z = μ z * π z s := fun s => by
    by_cases h : aa_predictive μ π s = 0
    · have h0 : ∀ z' ∈ Finset.univ, 0 ≤ μ z' * π z' s := fun z' _ =>
        mul_nonneg (hμ.nonneg z') ((hπ z').nonneg s)
      have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 h z (Finset.mem_univ z)
      simp [aa_posterior, h, this]
    · simp only [aa_posterior]
      field_simp
  simp [e, ← Finset.mul_sum, (hπ z).sum_eq_one]

/-! ### The homothetic specification (20.11)–(20.15) -/

/-- The power utility `u(x) = x^{1−γ}/(1−γ)` of (20.12) (and `v` of (20.13) with `η`). -/
noncomputable def aa_powU (γ x : ℝ) : ℝ := x ^ (1 - γ) / (1 - γ)

/-- Its inverse `u⁻¹(y) = ((1 − γ)y)^{1/(1−γ)}`. -/
noncomputable def aa_powUinv (γ y : ℝ) : ℝ := ((1 - γ) * y) ^ (1 - γ)⁻¹

theorem aa_powUinv_powU {γ : ℝ} (hγ : γ ≠ 1) {x : ℝ} (hx : 0 < x) :
    aa_powUinv γ (aa_powU γ x) = x := by
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_powUinv aa_powU
  rw [mul_div_cancel₀ _ h1, Real.rpow_rpow_inv hx.le h1]

/-- The certainty equivalent (20.15):
`M(x) = (E_μ (E_{π_z} x^{1−γ})^{(1−η)/(1−γ)})^{1/(1−η)}`. -/
noncomputable def aa_ju (γ η : ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) : ℝ :=
  (∑ z, μ z * (aa_E (π z) fun s => x s ^ (1 - γ)) ^ ((1 - η) / (1 - γ))) ^ (1 - η)⁻¹

/-- **(20.15)** (Miao, p. 699): with the power utilities (20.12)–(20.13), the certainty equivalent
of (20.10) is (20.15). -/
theorem aa_smoothM_power [Nonempty S] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) {μ : Z → ℝ}
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_smoothM (aa_powU γ) (aa_powUinv γ) (aa_powU η) (aa_powUinv η) μ π x = aa_ju γ η μ π x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have he : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  have hE : ∀ z, 0 < aa_E (π z) fun s => x s ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  have inner : ∀ z, aa_powU η (aa_powUinv γ (aa_E (π z) fun s => aa_powU γ (x s))) =
      (aa_E (π z) fun s => x s ^ (1 - γ)) ^ ((1 - η) / (1 - γ)) / (1 - η) := fun z => by
    unfold aa_powU aa_powUinv
    have : (1 - γ) * aa_E (π z) (fun s => x s ^ (1 - γ) / (1 - γ)) =
        aa_E (π z) fun s => x s ^ (1 - γ) := by
      rw [← aa_E_smul]
      congr 1
      funext s
      field_simp
    rw [this, ← Real.rpow_mul (hE z).le, inv_mul_eq_div]
  unfold aa_smoothM aa_ju
  simp only [inner]
  unfold aa_powUinv
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by field_simp

/-- The generalized recursive smooth ambiguity utility (20.14) on the event tree: at the node `h`
the posterior is `μ h` and the likelihoods are `π h`; `U_T = c_T`. -/
noncomputable def aa_juU (β ρ γ η : ℝ) (μ : List S → Z → ℝ) (π : List S → Z → S → ℝ)
    (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => c h
  | n + 1, h => aa_W β ρ (c h) (aa_ju γ η (μ h) (π h) fun s => aa_juU β ρ γ η μ π c n (s :: h))

/-- (20.15) as a power mean of the model-wise certainty equivalents
`Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}`. -/
theorem aa_ju_eq_powMean [Nonempty S] {γ : ℝ} (hγ : γ ≠ 1) (η : ℝ) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_ju γ η μ π x = aa_powMean (1 - η) μ fun z => aa_KP γ (π z) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ju aa_powMean aa_KP
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  have hE : 0 < aa_E (π z) fun s => x s ^ (1 - γ) :=
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  rw [← Real.rpow_mul hE.le, inv_mul_eq_div]

/-- Miao, p. 699: with `η = γ` the decision maker is ambiguity neutral and (20.15) is the
Kreps–Porteus certainty equivalent of Epstein–Zin under the predictive distribution. -/
theorem aa_ju_neutral {γ : ℝ} (hγ : γ ≠ 1) (μ : Z → ℝ) (π : Z → S → ℝ) (x : S → ℝ) :
    aa_ju γ γ μ π x = aa_KP γ (aa_predictive μ π) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ju aa_KP
  rw [div_self hg, aa_E_predictive]
  simp

/-- Miao, p. 699: with `η = γ`, the recursion (20.14) is the Epstein–Zin recursion (20.3) under
the predictive one-step-ahead distributions. -/
theorem aa_juU_neutral {β ρ γ : ℝ} (hγ : γ ≠ 1) (μ : List S → Z → ℝ) (π : List S → Z → S → ℝ)
    (c : List S → ℝ) :
    ∀ n h, aa_juU β ρ γ γ μ π c n h =
      aa_ezU β ρ γ (fun h' => aa_predictive (μ h') (π h')) c n h
  | 0, h => rfl
  | n + 1, h => by
    simp only [aa_juU, aa_ezU, aa_ju_neutral hγ]
    rw [show (fun s => aa_juU β ρ γ γ μ π c n (s :: h)) =
      (fun s => aa_ezU β ρ γ (fun h' => aa_predictive (μ h') (π h')) c n (s :: h)) from
        funext fun s => aa_juU_neutral hγ μ π c n (s :: h)]

/-- Miao, p. 699: "a more ambiguity-averse agent with a higher value of `η` has a lower utility
level": the certainty equivalent (20.15) is decreasing in `η` (`η, η' ≠ 1`). -/
theorem aa_ju_antitone [Nonempty S] [Nonempty Z] {γ : ℝ} (hγ : γ ≠ 1) {μ : Z → ℝ}
    (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) {η η' : ℝ} (hη : η ≠ 1) (hη' : η' ≠ 1) (hηη' : η ≤ η') :
    aa_ju γ η' μ π x ≤ aa_ju γ η μ π x := by
  rw [aa_ju_eq_powMean hγ _ _ hπ hx, aa_ju_eq_powMean hγ _ _ hπ hx]
  exact aa_powMean_mono hμ (fun z => aa_KP_pos γ (hπ z) hx) (sub_ne_zero.2 (Ne.symm hη'))
    (sub_ne_zero.2 (Ne.symm hη)) (by linarith)

/-- Miao, p. 699: ambiguity aversion `η ≥ γ` lowers the certainty equivalent below the Epstein–Zin
(ambiguity-neutral) value. -/
theorem aa_ju_le_KP [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) (hγη : γ ≤ η)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) : aa_ju γ η μ π x ≤ aa_KP γ (aa_predictive μ π) x := by
  rw [← aa_ju_neutral hγ]
  exact aa_ju_antitone hγ hμ hπ hx hγ hη hγη

/-- `η ≤ γ` (ambiguity loving) raises the certainty equivalent above the Epstein–Zin value. -/
theorem aa_KP_le_ju [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1) (hηγ : η ≤ γ)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) : aa_KP γ (aa_predictive μ π) x ≤ aa_ju γ η μ π x := by
  rw [← aa_ju_neutral hγ]
  exact aa_ju_antitone hγ hμ hπ hx hη hγ hηγ

/-- Miao, p. 699: the utility (20.14) is decreasing in `η` (one step, any positive continuation). -/
theorem aa_W_ju_antitone [Nonempty S] [Nonempty Z] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) {x : S → ℝ} (hx : ∀ s, 0 < x s)
    {η η' : ℝ} (hη : η ≠ 1) (hη' : η' ≠ 1) (hηη' : η ≤ η') :
    aa_W β ρ c (aa_ju γ η' μ π x) ≤ aa_W β ρ c (aa_ju γ η μ π x) := by
  have hpos : ∀ e, 0 < aa_ju γ e μ π x := fun e => by
    rw [aa_ju_eq_powMean hγ _ _ hπ hx]
    exact Real.rpow_pos_of_pos (aa_E_pos hμ fun z => Real.rpow_pos_of_pos
      (aa_KP_pos γ (hπ z) hx) _) _
  exact (aa_W_strictMonoOn hβ0 hβ1 hρ hc).monotoneOn (hpos η') (hpos η)
    (aa_ju_antitone hγ hμ hπ hx hη hη' hηη')

/-! ### The limits (20.16)–(20.18) -/

/-- Miao, p. 699: as `ρ → 1` the CES aggregator (20.11) tends to the Cobb–Douglas aggregator
`c^{1−β}y^β`. -/
theorem aa_W_tendsto_rho_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {c y : ℝ} (hc : 0 < c)
    (hy : 0 < y) :
    Tendsto (fun ρ => aa_W β ρ c y) (𝓝[≠] 1) (𝓝 (c ^ (1 - β) * y ^ β)) := by
  set p : Bool → ℝ := fun b => if b then β else 1 - β with hp
  set v : Bool → ℝ := fun b => if b then Real.log y else Real.log c with hv
  have hpD : SS.IsDistribution p :=
    ⟨fun b => by cases b <;> simp [hp] <;> linarith, by simp [hp]⟩
  have hL := aa_tendsto_logmgf hpD v
  have hsub : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_ne_zero.2 (Ne.symm hρ)
  have h2 := (Real.continuous_exp.tendsto _).comp (hL.comp hsub)
  have hlim : Real.exp (aa_E p v) = c ^ (1 - β) * y ^ β := by
    simp only [aa_E, Fintype.sum_bool, hp, hv, ↓reduceIte, Bool.false_eq_true]
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hy, ← Real.exp_add]
    ring_nf
  rw [hlim] at h2
  refine h2.congr fun ρ => ?_
  simp only [Function.comp_apply, aa_W, Fintype.sum_bool, hp, hv, ↓reduceIte,
    Bool.false_eq_true]
  have hb : 0 < (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) ∨
      (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) = 0 := by
    rcases (show (0 : ℝ) ≤ (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) by
      have := Real.rpow_pos_of_pos hc (1 - ρ)
      have := Real.rpow_pos_of_pos hy (1 - ρ)
      nlinarith).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have e1 : β * Real.exp ((1 - ρ) * Real.log y) + (1 - β) * Real.exp ((1 - ρ) * Real.log c) =
      (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hy]
    ring_nf
  rw [e1]
  rcases hb with hb | hb
  · rw [Real.rpow_def_of_pos hb]
    ring_nf
  · have hβ' : β = 0 ∧ 1 - β = 0 := by
      have := Real.rpow_pos_of_pos hc (1 - ρ)
      have := Real.rpow_pos_of_pos hy (1 - ρ)
      constructor <;> nlinarith
    exact absurd (hβ'.1 ▸ hβ'.2) (by norm_num)

/-- **(20.16)** (Miao, p. 699): at `ρ = 1` the aggregator is `U = c^{1−β}M^β`, and with
`U_{t+1} = exp V_{t+1}` the log utility `V = ln U` satisfies
`V_t = (1 − β) ln c_t + (β/(1 − η)) ln E_μ exp(((1 − η)/(1 − γ)) ln E_{π_z} exp((1 − γ)V_{t+1}))`.
-/
theorem eq_20_16 [Nonempty S] {β γ η : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) [Nonempty Z]
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) (V : S → ℝ) :
    Real.log (c ^ (1 - β) * aa_ju γ η μ π (fun s => Real.exp (V s)) ^ β) =
      (1 - β) * Real.log c + β / (1 - η) * Real.log (∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
        Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))) := by
  have hE : ∀ z, 0 < aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (Real.exp_pos _) _
  have e1 : ∀ z, (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) =
      ∑ s, π z s * Real.exp ((1 - γ) * V s) := fun z => by
    unfold aa_E
    exact Finset.sum_congr rfl fun s _ => by
      dsimp only
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (V s)]
  have hS : 0 < ∑ z, μ z * (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) ^
      ((1 - η) / (1 - γ)) := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hE z) _
  have hM : 0 < aa_ju γ η μ π (fun s => Real.exp (V s)) := Real.rpow_pos_of_pos hS _
  rw [Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.rpow_pos_of_pos hM _).ne',
    Real.log_rpow hc, Real.log_rpow hM]
  unfold aa_ju
  rw [Real.log_rpow hS]
  have e2 : ∑ z, μ z * (aa_E (π z) fun s => Real.exp (V s) ^ (1 - γ)) ^ ((1 - η) / (1 - γ)) =
      ∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
        Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s))) :=
    Finset.sum_congr rfl fun z _ => by
      rw [Real.rpow_def_of_pos (hE z), e1, mul_comm (Real.log _)]
  rw [e2]
  ring

/-- **(20.17)** (Miao, p. 700): as `γ → 1`, the right side of (20.16) tends to
`(1 − β) ln c_t + (β/(1 − η)) ln E_μ exp((1 − η)E_{π_z}[V_{t+1}])`. -/
theorem eq_20_17 {β η : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) [Nonempty Z]
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (c : ℝ) (V : S → ℝ) :
    Tendsto (fun γ => (1 - β) * Real.log c + β / (1 - η) * Real.log (∑ z, μ z *
        Real.exp ((1 - η) / (1 - γ) * Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))))
      (𝓝[≠] 1)
      (𝓝 ((1 - β) * Real.log c + β / (1 - η) *
        Real.log (∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V)))) := by
  have hsub : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γ hγ
      exact sub_ne_zero.2 (Ne.symm hγ)
  have hz : ∀ z, Tendsto (fun γ => (1 - η) / (1 - γ) *
      Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s))) (𝓝[≠] 1)
        (𝓝 ((1 - η) * aa_E (π z) V)) := fun z => by
    have := ((aa_tendsto_logmgf (hπ z) V).comp hsub).const_mul (1 - η)
    refine this.congr fun γ => ?_
    simp only [Function.comp_apply]
    ring
  have hsum : Tendsto (fun γ => ∑ z, μ z * Real.exp ((1 - η) / (1 - γ) *
      Real.log (∑ s, π z s * Real.exp ((1 - γ) * V s)))) (𝓝[≠] 1)
        (𝓝 (∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V))) :=
    tendsto_finsetSum _ fun z _ => ((Real.continuous_exp.tendsto _).comp (hz z)).const_mul (μ z)
  have hpos : 0 < ∑ z, μ z * Real.exp ((1 - η) * aa_E (π z) V) :=
    aa_E_pos hμ fun z => Real.exp_pos _
  exact tendsto_const_nhds.add ((hsum.log hpos.ne').const_mul _)

/-- **(20.18)** (Miao, p. 700): as `η → ∞` the log-exponential specification (20.17) tends to the
recursive multiple-priors form `V_t = (1 − β) ln c_t + β min_z E_{π_z}[V_{t+1}]`, provided the
minimising model has positive posterior probability. Here `X z = E_{π_z}[V_{t+1}]`. -/
theorem eq_20_18 {β : ℝ} {μ : Z → ℝ} (hμ : SS.IsDistribution μ) (c : ℝ) (X : Z → ℝ) {z₀ : Z}
    (hmin : ∀ z, X z₀ ≤ X z) (hμz : 0 < μ z₀) :
    Tendsto (fun η => (1 - β) * Real.log c + β / (1 - η) *
        Real.log (∑ z, μ z * Real.exp ((1 - η) * X z))) atTop
      (𝓝 ((1 - β) * Real.log c + β * X z₀)) := by
  have hk : Tendsto (fun η : ℝ => η + -1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h := ((aa_tendsto_softmin hμ X hmin hμz).comp hk).const_mul β
  refine (tendsto_const_nhds.add h).congr fun η => ?_
  simp only [Function.comp_apply]
  have e1 : ∀ z, -(η + -1) * X z = (1 - η) * X z := fun z => by ring
  simp only [e1]
  have e2 : (1 - η) = -(η + -1) := by ring
  rw [e2, div_neg, div_eq_mul_inv]
  ring

/-! ### Exponential specifications and the nested models -/

/-- The inverse `u⁻¹(y) = −θ ln(−y)` of the exponential utility. -/
noncomputable def aa_expUinv (θ y : ℝ) : ℝ := -θ * Real.log (-y)

/-- Miao, p. 699: with `u(x) = −exp(−x/θ₁)` and `v(x) = −exp(−x/θ₂)`, the certainty equivalent of
(20.10) is the recursive multiplier with hidden states of Hansen and Sargent (2007),
`M(x) = −θ₂ ln E_μ (E_{π_z} exp(−x/θ₁))^{θ₁/θ₂}`. -/
theorem aa_smoothM_exp [Nonempty S] {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (x : S → ℝ) :
    aa_smoothM (aa_expU θ₁) (aa_expUinv θ₁) (aa_expU θ₂) (aa_expUinv θ₂) μ π x =
      -θ₂ * Real.log (∑ z, μ z * (∑ s, π z s * Real.exp (-x s / θ₁)) ^ (θ₁ / θ₂)) := by
  have hA : ∀ z, 0 < ∑ s, π z s * Real.exp (-x s / θ₁) := fun z =>
    aa_E_pos (hπ z) fun s => Real.exp_pos _
  have inner : ∀ z, aa_expU θ₂ (aa_expUinv θ₁ (aa_E (π z) fun s => aa_expU θ₁ (x s))) =
      -(∑ s, π z s * Real.exp (-x s / θ₁)) ^ (θ₁ / θ₂) := fun z => by
    have e : (aa_E (π z) fun s => aa_expU θ₁ (x s)) = -∑ s, π z s * Real.exp (-x s / θ₁) := by
      simp [aa_E, aa_expU, Finset.sum_neg_distrib]
    rw [e]
    unfold aa_expU aa_expUinv
    rw [neg_neg, Real.rpow_def_of_pos (hA z)]
    congr 2
    field_simp
  unfold aa_smoothM
  simp only [inner, mul_neg, Finset.sum_neg_distrib]
  unfold aa_expUinv
  rw [neg_neg]

/-- Miao, p. 699, footnote 2: with `θ₁ = θ₂ = θ` the multiplier model with hidden states is the
risk-sensitive (Kreps–Porteus–Epstein–Zin) certainty equivalent under the predictive
distribution. -/
theorem aa_smoothM_exp_equal [Nonempty S] {θ : ℝ} (hθ : 0 < θ) (μ : Z → ℝ)
    {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z)) (x : S → ℝ) :
    aa_smoothM (aa_expU θ) (aa_expUinv θ) (aa_expU θ) (aa_expUinv θ) μ π x =
      -θ * Real.log (∑ s, aa_predictive μ π s * Real.exp (-x s / θ)) := by
  rw [aa_smoothM_exp hθ hθ μ hπ x, div_self hθ.ne']
  simp only [Real.rpow_one]
  have := aa_E_predictive μ π fun s => Real.exp (-x s / θ)
  simp only [aa_E] at this
  rw [this]

/-- Miao, p. 700: the exponential `φ(x) = −exp(−x/θ)` makes `φ⁻¹(E_μ φ(y)) = −θ ln E_μ exp(−y/θ)`
well defined for every real `y`. -/
theorem aa_smoothM_expPhi (θ : ℝ) (μ y : Z → ℝ) :
    aa_expUinv θ (∑ z, μ z * aa_expU θ (y z)) = -θ * Real.log (∑ z, μ z * Real.exp (-y z / θ)) := by
  unfold aa_expUinv aa_expU
  simp [Finset.sum_neg_distrib]

/-- **(20.19)** (Miao, p. 700): with `W(c, y) = u(c) + βy` and the identity in place of the inner
utility, (20.10) is the model of Klibanoff et al. (2009):
`V_t = u(c_t) + βφ⁻¹(E_μ φ(E_{π_z}[V_{t+1}]))`. -/
theorem eq_20_19 (u φ φinv : ℝ → ℝ) (β : ℝ) (μ : Z → ℝ) (π : Z → S → ℝ) (c : ℝ) (V : S → ℝ) :
    u c + β * aa_smoothM id id φ φinv μ π V = u c + β * φinv (∑ z, μ z * φ (aa_E (π z) V)) := by
  rfl

/-- Miao, p. 700: with the power utility (20.12) and `γ > 1`, every expected utility is negative,
so it lies outside the domain `x > 0` of `φ(x) = x^{1−α}/(1−α)`: (20.19) is not well defined. -/
theorem aa_juMiao_illDefined [Nonempty S] {γ : ℝ} (hγ : 1 < γ) {p : S → ℝ}
    (hp : SS.IsDistribution p) {c : S → ℝ} (hc : ∀ s, 0 < c s) :
    aa_E p (fun s => aa_powU γ (c s)) < 0 := by
  have h : 0 < aa_E p fun s => -aa_powU γ (c s) := aa_E_pos hp fun s => by
    unfold aa_powU
    rw [neg_pos]
    exact div_neg_of_pos_of_neg (Real.rpow_pos_of_pos (hc s) _) (by linarith)
  have e : (aa_E p fun s => -aa_powU γ (c s)) = -aa_E p fun s => aa_powU γ (c s) := by
    simp [aa_E, Finset.sum_neg_distrib]
  linarith

/-- The recursion (20.19) on the event tree, with terminal utility `V_T = ψ(c_T)`. -/
noncomputable def aa_kmm09U (u φ φinv ψ : ℝ → ℝ) (β : ℝ) (μ : List S → Z → ℝ)
    (π : List S → Z → S → ℝ) (c : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => ψ (c h)
  | n + 1, h => u (c h) + β * φinv (∑ z, μ h z * φ (aa_E (π h z)
      fun s => aa_kmm09U u φ φinv ψ β μ π c n (s :: h)))

/-- The utility (20.14) is positive. -/
theorem aa_juU_pos [Nonempty S] [Nonempty Z] {β ρ γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≠ 1) {μ : List S → Z → ℝ} (hμ : ∀ h, SS.IsDistribution (μ h))
    {π : List S → Z → S → ℝ} (hπ : ∀ h z, SS.IsDistribution (π h z)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) : ∀ n h, 0 < aa_juU β ρ γ η μ π c n h
  | 0, h => hc h
  | n + 1, h => by
    refine aa_W_pos hβ0 hβ1 (hc h) ?_
    rw [aa_ju_eq_powMean hγ _ _ (hπ h) fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)]
    exact Real.rpow_pos_of_pos (aa_E_pos (hμ h) fun z => Real.rpow_pos_of_pos
      (aa_KP_pos γ (hπ h z) fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)) _) _

/-- The one-step ordinal equivalence behind `aa_juMiao_ordinal`. With `ρ = γ ∈ (0, 1)`,
`k = (1 − γ)(1 − β)` and `1 − α = (1 − η)/(1 − γ)`, the transform `V = U^{1−γ}/k` of (20.14)
satisfies
`V = u(c) + βφ⁻¹(E_μ φ(E_{π_z} V'))`, `u(c) = c^{1−γ}/(1−γ)`, `φ(x) = x^{1−α}/(1−α)`. -/
theorem aa_juMiao_step [Nonempty S] [Nonempty Z] {β γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ1 : γ < 1)
    (hη : η ≠ 1) {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ}
    (hπ : ∀ z, SS.IsDistribution (π z)) {c : ℝ} (hc : 0 < c) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_W β γ c (aa_ju γ η μ π x) ^ (1 - γ) / ((1 - γ) * (1 - β)) =
      aa_powU γ c + β * aa_powUinv (1 - (1 - η) / (1 - γ)) (∑ z, μ z *
        aa_powU (1 - (1 - η) / (1 - γ))
          (aa_E (π z) fun s => x s ^ (1 - γ) / ((1 - γ) * (1 - β)))) := by
  set k := (1 - γ) * (1 - β) with hk
  set a := (1 - η) / (1 - γ) with ha
  have hg : 0 < 1 - γ := by linarith
  have hb : 0 < 1 - β := by linarith
  have hk0 : 0 < k := mul_pos hg hb
  have ha0 : a ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm hη)) hg.ne'
  have e1 : 1 - (1 - a) = a := by ring
  have hE : ∀ z, 0 < aa_E (π z) fun s => x s ^ (1 - γ) := fun z =>
    aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  set T := ∑ z, μ z * (aa_E (π z) fun s => x s ^ (1 - γ)) ^ a with hT
  have hT0 : 0 < T := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hE z) _
  have hM : aa_ju γ η μ π x = T ^ (1 - η)⁻¹ := rfl
  have hM0 : 0 < aa_ju γ η μ π x := by rw [hM]; exact Real.rpow_pos_of_pos hT0 _
  -- the left side
  have hL : aa_W β γ c (aa_ju γ η μ π x) ^ (1 - γ) =
      (1 - β) * c ^ (1 - γ) + β * T ^ a⁻¹ := by
    unfold aa_W
    have hA : 0 ≤ (1 - β) * c ^ (1 - γ) + β * aa_ju γ η μ π x ^ (1 - γ) :=
      add_nonneg (mul_nonneg hb.le (Real.rpow_pos_of_pos hc _).le)
        (mul_nonneg hβ0.le (Real.rpow_pos_of_pos hM0 _).le)
    rw [Real.rpow_inv_rpow hA hg.ne', hM, ← Real.rpow_mul hT0.le]
    congr 3
    rw [ha]
    field_simp
  -- the right side
  have hR : aa_powUinv (1 - a) (∑ z, μ z * aa_powU (1 - a)
      (aa_E (π z) fun s => x s ^ (1 - γ) / k)) = T ^ a⁻¹ / k := by
    have hEk : ∀ z, (aa_E (π z) fun s => x s ^ (1 - γ) / k) =
        (aa_E (π z) fun s => x s ^ (1 - γ)) / k := fun z => by
      rw [div_eq_inv_mul, ← aa_E_smul]
      congr 1
      funext s
      ring
    unfold aa_powUinv aa_powU
    simp only [e1, hEk]
    have hsum : a * ∑ z, μ z * (((aa_E (π z) fun s => x s ^ (1 - γ)) / k) ^ a / a) =
        T / k ^ a := by
      rw [hT, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Real.div_rpow (hE z).le hk0.le]
      field_simp
    rw [hsum, Real.div_rpow hT0.le (Real.rpow_pos_of_pos hk0 _).le,
      ← Real.rpow_mul hk0.le, mul_inv_cancel₀ ha0, Real.rpow_one]
  rw [hL, hR, aa_powU]
  field_simp
  ring

/-- Miao, p. 700: with `ρ = γ ∈ (0, 1)` and `α = 1 − (1 − η)/(1 − γ)`, the generalized smooth
ambiguity utility (20.14)–(20.15) is ordinally equivalent to the model (20.19) of Klibanoff et al.
(2009): `V = U^{1−γ}/((1 − γ)(1 − β))` (a strictly increasing transform of `U`) satisfies (20.19)
at every node, with the terminal utility `V_T = c_T^{1−γ}/((1 − γ)(1 − β))`. -/
theorem aa_juMiao_ordinal [Nonempty S] [Nonempty Z] {β γ η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ1 : γ < 1) (hη : η ≠ 1) {μ : List S → Z → ℝ} (hμ : ∀ h, SS.IsDistribution (μ h))
    {π : List S → Z → S → ℝ} (hπ : ∀ h z, SS.IsDistribution (π h z)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) :
    ∀ n h, aa_kmm09U (aa_powU γ) (aa_powU (1 - (1 - η) / (1 - γ)))
        (aa_powUinv (1 - (1 - η) / (1 - γ))) (fun y => y ^ (1 - γ) / ((1 - γ) * (1 - β))) β μ π c
        n h = aa_juU β γ γ η μ π c n h ^ (1 - γ) / ((1 - γ) * (1 - β))
  | 0, h => rfl
  | n + 1, h => by
    have hγ : γ ≠ 1 := hγ1.ne
    simp only [aa_kmm09U, aa_juU]
    rw [aa_juMiao_step hβ0 hβ1 hγ1 hη (hμ h) (hπ h) (hc h)
      fun s => aa_juU_pos hβ0 hβ1 hγ hμ hπ hc n (s :: h)]
    congr 3
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 3
    funext s
    exact aa_juMiao_ordinal hβ0 hβ1 hγ1 hη hμ hπ hc n (s :: h)

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Temporal resolution of uncertainty

Miao, §20.2.3, pp. 701–704, and Exercise 20.3 (p. 735): Kreps and Porteus (1978).

Consumption in each period lies in a measurable space `X` (the book: a bounded interval of
`ℝ₊`); period-1 lotteries are probability measures on `X` (`aa_Lott`), and the intertemporal
consumption lotteries used in the definition are finite mixtures of programs `δ[c₀, m]`, valued
by `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` (`aa_U0`).

* The four choices of p. 701: a time-additive expected-utility maximiser is indifferent between
  choices 1 and 2 (`aa_timeAdditive_indifferent`) and between choices 3 and 4
  (`aa_timeAdditive_indifferent_34`).
* **Definition 20.2.4** (`aa_PrefersEarly`, `aa_PrefersLate`, `definition_20_2_4`).
* **Theorem 20.2.1**: earlier (later) resolution is preferred iff `W(x, ·)` is convex (concave) on
  the set `Y` of expected utilities `E_m U₁` (`theorem_20_2_1`, `theorem_20_2_1_late`), for
  bounded measurable `U₁`. The book says "convex in `y`": only the values `y ∈ Y` matter.
* **Exercise 20.3** and p. 704: for Epstein–Zin utility (20.3), written in the Kreps–Porteus form
  `W̃(c, y) = u(W(c, u⁻¹(y)))`, `u(x) = x^{1−γ}/(1−γ)` (`aa_ezKP`, `aa_ezKP_eq`), on
  `X = [a, b] ⊆ (0, ∞)` with `a < b`: earlier resolution is (weakly) preferred iff `γ ≥ ρ`
  (`ex_20_3`), strictly preferred for every nondegenerate pair of lotteries when `γ > ρ`
  (`aa_ez_strictEarly`), and at `γ = ρ` the agent is indifferent (`aa_ez_indifferent`). The book's
  "iff `γ > ρ`" is the strict version; with the weak preference of Definition 20.2.4 the condition
  is `γ ≥ ρ`.
-/

namespace Miao.RecursiveUtility

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- The period-1 consumption lotteries `M(X)`: Borel probability measures on `X`. -/
def aa_Lott (X : Type*) [MeasurableSpace X] : Set (Measure X) := {m | IsProbabilityMeasure m}

/-- The mixture `αm + (1 − α)m'` of two lotteries. -/
noncomputable def aa_mix (α : ℝ) (m m' : Measure X) : Measure X :=
  ENNReal.ofReal α • m + ENNReal.ofReal (1 - α) • m'

theorem aa_mix_mem {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {m m' : Measure X} (hm : m ∈ aa_Lott X)
    (hm' : m' ∈ aa_Lott X) : aa_mix α m m' ∈ aa_Lott X := by
  have h1 : m Set.univ = 1 := (hm : IsProbabilityMeasure m).measure_univ
  have h2 : m' Set.univ = 1 := (hm' : IsProbabilityMeasure m').measure_univ
  refine ⟨?_⟩
  simp only [aa_mix, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h1, h2, mul_one]
  rw [← ENNReal.ofReal_add hα0 (by linarith)]
  simp

theorem aa_integrable {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C)
    {m : Measure X} (hm : m ∈ aa_Lott X) : Integrable U₁ m := by
  have : IsProbabilityMeasure m := hm
  exact Integrable.of_bound hU.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC x)

/-- `E_{αm + (1−α)m'} U₁ = αE_m U₁ + (1 − α)E_{m'} U₁` for bounded measurable `U₁`. -/
theorem aa_integral_mix {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {m m' : Measure X} (hm : m ∈ aa_Lott X)
    (hm' : m' ∈ aa_Lott X) :
    ∫ x, U₁ x ∂(aa_mix α m m') = α * ∫ x, U₁ x ∂m + (1 - α) * ∫ x, U₁ x ∂m' := by
  unfold aa_mix
  rw [integral_add_measure ((aa_integrable hU hC hm).smul_measure ENNReal.ofReal_ne_top)
    ((aa_integrable hU hC hm').smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hα0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- The utility `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` of a finite intertemporal consumption lottery
`d = ∑ᵢ wᵢ δ[cᵢ, mᵢ]`. -/
noncomputable def aa_U0 (W : X → ℝ → ℝ) (U₁ : X → ℝ) {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (c : ι → X) (m : ι → Measure X) : ℝ :=
  ∑ i, w i * W (c i) (∫ x, U₁ x ∂(m i))

/-- **Definition 20.2.4** (Miao, p. 703): the decision maker prefers earlier resolution of
uncertainty if `αδ[c₀, m] + (1 − α)δ[c₀, m'] ≿ δ[c₀, αm + (1 − α)m']` for all `c₀, m, m', α`. -/
def aa_PrefersEarly (W : X → ℝ → ℝ) (U₁ : X → ℝ) : Prop :=
  ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    W c₀ (∫ x, U₁ x ∂(aa_mix α m m')) ≤
      α * W c₀ (∫ x, U₁ x ∂m) + (1 - α) * W c₀ (∫ x, U₁ x ∂m')

/-- Preference for later resolution: the reverse ranking. -/
def aa_PrefersLate (W : X → ℝ → ℝ) (U₁ : X → ℝ) : Prop :=
  ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    α * W c₀ (∫ x, U₁ x ∂m) + (1 - α) * W c₀ (∫ x, U₁ x ∂m') ≤
      W c₀ (∫ x, U₁ x ∂(aa_mix α m m'))

/-- **Definition 20.2.4** (Miao, p. 703) in terms of the recursive utility `U₀` of the two
programs: the early-resolution lottery `αδ[c₀, m] + (1 − α)δ[c₀, m']` (indexed by `Bool`) is
weakly preferred to the late-resolution lottery `δ[c₀, αm + (1 − α)m']` (indexed by `Unit`). -/
theorem definition_20_2_4 (W : X → ℝ → ℝ) (U₁ : X → ℝ) :
    aa_PrefersEarly W U₁ ↔ ∀ c₀ : X, ∀ m ∈ aa_Lott X, ∀ m' ∈ aa_Lott X, ∀ α : ℝ, 0 ≤ α →
      α ≤ 1 → aa_U0 W U₁ (fun _ : Unit => 1) (fun _ => c₀) (fun _ => aa_mix α m m') ≤
        aa_U0 W U₁ (fun b : Bool => if b then α else 1 - α) (fun _ => c₀)
          (fun b => if b then m else m') := by
  simp [aa_U0, aa_PrefersEarly]

/-- The set `Y = {E_m U₁ : m ∈ M(X)}` of expected period-1 utilities. -/
def aa_Y (U₁ : X → ℝ) : Set ℝ := {y | ∃ m ∈ aa_Lott X, y = ∫ x, U₁ x ∂m}

theorem aa_Y_convex {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C) :
    Convex ℝ (aa_Y U₁) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  exact ⟨aa_mix a m m', aa_mix_mem ha (by linarith) hm hm',
    by rw [aa_integral_mix hU hC ha (by linarith) hm hm', smul_eq_mul, smul_eq_mul]⟩

/-- **Theorem 20.2.1** (Miao, p. 704; Kreps and Porteus 1978). For bounded measurable `U₁`, the
decision maker with `U₀(d) = E_d[W(c₀, E_m U₁(c₁))]` prefers earlier resolution of uncertainty iff
`W(x, ·)` is convex on the set `Y` of expected utilities, for every `x`. -/
theorem theorem_20_2_1 (W : X → ℝ → ℝ) {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ}
    (hC : ∀ x, |U₁ x| ≤ C) : aa_PrefersEarly W U₁ ↔ ∀ x, ConvexOn ℝ (aa_Y U₁) (W x) := by
  constructor
  · intro h x
    refine ⟨aa_Y_convex hU hC, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x m hm m' hm' a ha (by linarith)
    rw [aa_integral_mix hU hC ha (by linarith) hm hm'] at this
    simpa [smul_eq_mul] using this
  · intro h c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    have := (h c₀).2 ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩ hα0 (by linarith : 0 ≤ 1 - α) (by ring)
    simpa [smul_eq_mul] using this

/-- **Theorem 20.2.1, later resolution** (Miao, p. 704): later resolution is preferred iff `W(x, ·)`
is concave on `Y` for every `x`. -/
theorem theorem_20_2_1_late (W : X → ℝ → ℝ) {U₁ : X → ℝ} (hU : Measurable U₁) {C : ℝ}
    (hC : ∀ x, |U₁ x| ≤ C) : aa_PrefersLate W U₁ ↔ ∀ x, ConcaveOn ℝ (aa_Y U₁) (W x) := by
  constructor
  · intro h x
    refine ⟨aa_Y_convex hU hC, ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x m hm m' hm' a ha (by linarith)
    rw [aa_integral_mix hU hC ha (by linarith) hm hm'] at this
    simpa [smul_eq_mul] using this
  · intro h c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    have := (h c₀).2 ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩ hα0 (by linarith : 0 ≤ 1 - α) (by ring)
    simpa [smul_eq_mul] using this

/-- Miao, p. 701: a decision maker with time-additive expected utility, `W(x, y) = u(x) + βy`, is
indifferent between choices 1 and 2 (it both prefers earlier and prefers later resolution). -/
theorem aa_timeAdditive_indifferent (u : X → ℝ) (β : ℝ) {U₁ : X → ℝ} (hU : Measurable U₁)
    {C : ℝ} (hC : ∀ x, |U₁ x| ≤ C) :
    aa_PrefersEarly (fun x y => u x + β * y) U₁ ∧ aa_PrefersLate (fun x y => u x + β * y) U₁ := by
  constructor <;>
  · intro c₀ m hm m' hm' α hα0 hα1
    rw [aa_integral_mix hU hC hα0 hα1 hm hm']
    linarith

/-- Miao, p. 701: choices 3 and 4. With time-additive expected utility `u(c₀) + βu(c₁)`,
independent fair coins in both periods (choice 3) and one coin for both periods (choice 4) give the
same utility. -/
theorem aa_timeAdditive_indifferent_34 (u : ℝ → ℝ) (β c c' : ℝ) :
    (1 / 4 : ℝ) * ((u c + β * u c) + (u c + β * u c') + (u c' + β * u c) + (u c' + β * u c')) =
      (1 / 2 : ℝ) * (u c + β * u c) + (1 / 2 : ℝ) * (u c' + β * u c') := by
  ring

/-! ### Epstein–Zin utility (Exercise 20.3) -/

/-- Epstein–Zin utility (20.3) over two periods in the Kreps–Porteus form
`U₀ = W̃(c₀, E_m u(c₁))`, `W̃(c, y) = u(W(c, u⁻¹(y)))` with `u(x) = x^{1−γ}/(1−γ)` and the CES
aggregator `W`. -/
noncomputable def aa_ezKP (β ρ γ c y : ℝ) : ℝ := aa_powU γ (aa_W β ρ c (aa_powUinv γ y))

/-- The Kreps–Porteus form is the Epstein–Zin recursion: `u⁻¹(E u(c₁))` is the certainty equivalent
`M(c₁) = (E c₁^{1−γ})^{1/(1−γ)}`, so `W̃(c₀, E u(c₁)) = u(W(c₀, M(c₁)))`. -/
theorem aa_ezKP_eq {S : Type*} [Fintype S] (β ρ : ℝ) {γ : ℝ} (hγ : γ ≠ 1) (c : ℝ) (p x : S → ℝ) :
    aa_ezKP β ρ γ c (aa_E p fun s => aa_powU γ (x s)) = aa_powU γ (aa_W β ρ c (aa_KP γ p x)) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  unfold aa_ezKP aa_KP
  congr 2
  unfold aa_powUinv aa_powU
  rw [← aa_E_smul]
  congr 2
  funext s
  field_simp

/-- `F(t) = (h + t^{1/θ})^θ` is strictly convex on `(0, ∞)` for `h > 0`, `θ ∈ (0, 1)`. -/
theorem aa_powF_strictConvexOn {h θ : ℝ} (hh : 0 < h) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (SS.continuousOn_powF hh.le hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(SS.hasDerivAt_powF hh.le hθ0.ne' hs').deriv, (SS.hasDerivAt_powF hh.le hθ0.ne' ht').deriv]
  have h1 : t ^ (-θ⁻¹) < s ^ (-θ⁻¹) :=
    Real.rpow_lt_rpow_of_neg hs' hst (by have := inv_pos.2 hθ0; linarith)
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  exact Real.rpow_lt_rpow_of_neg hBt (by nlinarith) (by linarith)

/-- `F(t) = (h + t^{1/θ})^θ` is strictly concave on `(0, ∞)` for `h > 0` and `θ > 1` or `θ < 0`. -/
theorem aa_powF_strictConcaveOn {h θ : ℝ} (hh : 0 < h) (hθ : θ < 0 ∨ 1 < θ) :
    StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
  have hθ0 : θ ≠ 0 := by rcases hθ with h | h <;> [exact h.ne; exact (by linarith : (0:ℝ) < θ).ne']
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (SS.continuousOn_powF hh.le hθ0) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [(SS.hasDerivAt_powF hh.le hθ0 hs').deriv, (SS.hasDerivAt_powF hh.le hθ0 ht').deriv]
  have hBs : 0 < 1 + h * s ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos hs' (-θ⁻¹); positivity
  have hBt : 0 < 1 + h * t ^ (-θ⁻¹) := by have := Real.rpow_pos_of_pos ht' (-θ⁻¹); positivity
  rcases hθ with hneg | hpos
  · have h1 : s ^ (-θ⁻¹) < t ^ (-θ⁻¹) :=
      Real.rpow_lt_rpow hs'.le hst (by have := inv_lt_zero.2 hneg; linarith)
    exact Real.rpow_lt_rpow_of_neg hBs (by nlinarith) (by linarith)
  · have h1 : t ^ (-θ⁻¹) < s ^ (-θ⁻¹) :=
      Real.rpow_lt_rpow_of_neg hs' hst (by have := inv_pos.2 (by linarith : (0:ℝ) < θ); linarith)
    exact Real.rpow_lt_rpow hBt.le (by nlinarith) (by linarith)

/-- `W̃(c, y) = β^{θ}(1 − γ)⁻¹ F((1 − γ)y)` with `F(t) = (h + t^{1/θ})^θ`, `θ = (1 − γ)/(1 − ρ)`,
`h = (1 − β)c^{1−ρ}/β`, on the domain `(1 − γ)y > 0`. -/
theorem aa_ezKP_eq_powF {β ρ γ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hc : 0 < c) (hy : 0 < (1 - γ) * y) :
    aa_ezKP β ρ γ c y = β ^ ((1 - γ) / (1 - ρ)) / (1 - γ) *
      SS.powF ((1 - β) * c ^ (1 - ρ) / β) ((1 - γ) / (1 - ρ)) ((1 - γ) * y) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  set t := (1 - γ) * y with htdef
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hθ0 : θ ≠ 0 := div_ne_zero hg hr
  have hA : 0 < (1 - β) * c ^ (1 - ρ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hc _)
  have hbase : 0 < (1 - β) * c ^ (1 - ρ) + β * t ^ θ⁻¹ :=
    add_pos hA (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))
  unfold aa_ezKP aa_powU aa_W aa_powUinv SS.powF
  rw [← htdef, ← Real.rpow_mul hy.le]
  have e1 : (1 - γ)⁻¹ * (1 - ρ) = θ⁻¹ := by rw [hθ, inv_div]; ring
  rw [e1, ← Real.rpow_mul hbase.le]
  have e2 : (1 - ρ)⁻¹ * (1 - γ) = θ := by rw [hθ]; ring
  rw [e2]
  have e3 : (1 - β) * c ^ (1 - ρ) + β * t ^ θ⁻¹ = β * ((1 - β) * c ^ (1 - ρ) / β + t ^ θ⁻¹) := by
    field_simp
  rw [e3, Real.mul_rpow hβ0.le (by positivity)]
  ring

/-- Strict convexity transfers through `y ↦ k F(l y)` with `k > 0`, `l ≠ 0`. -/
theorem aa_strictConvexOn_comp {F : ℝ → ℝ} (hF : StrictConvexOn ℝ (Ioi 0) F) {k l : ℝ}
    (hk : 0 < k) (hl : l ≠ 0) : StrictConvexOn ℝ {y | 0 < l * y} fun y => k * F (l * y) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [show l * (a * x + b * y) = a * (l * x) + b * (l * y) by ring]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx, mul_nonneg hb hy.le]
    · subst ha'
      rw [zero_add] at hab
      subst hab
      simpa using hy
  · intro x hx y hy hxy a b ha hb hab
    have hx' : l * x ∈ Ioi (0 : ℝ) := hx
    have hy' : l * y ∈ Ioi (0 : ℝ) := hy
    have hne : l * x ≠ l * y := fun h => hxy (mul_left_cancel₀ hl h)
    have := hF.2 hx' hy' hne ha hb hab
    simp only [smul_eq_mul] at this ⊢
    rw [show l * (a * x + b * y) = a * (l * x) + b * (l * y) by ring]
    nlinarith

/-- Strict concavity transfers through `y ↦ k F(l y)` with `k > 0`, `l ≠ 0`. -/
theorem aa_strictConcaveOn_comp {F : ℝ → ℝ} (hF : StrictConcaveOn ℝ (Ioi 0) F) {k l : ℝ}
    (hk : 0 < k) (hl : l ≠ 0) : StrictConcaveOn ℝ {y | 0 < l * y} fun y => k * F (l * y) := by
  have := (aa_strictConvexOn_comp hF.neg hk hl).neg
  convert this using 1
  funext y
  simp

/-- The domain `{y : (1 − γ)y > 0}` of the Kreps–Porteus form. -/
theorem aa_ezKP_strict {β ρ γ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hc : 0 < c) :
    (ρ < γ → StrictConvexOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c)) ∧
      (γ < ρ → StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c)) := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  set h := (1 - β) * c ^ (1 - ρ) / β with hh
  have hh0 : 0 < h := div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hc _)) hβ0
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hβθ : 0 < β ^ θ := Real.rpow_pos_of_pos hβ0 _
  have heq : ∀ y ∈ {y : ℝ | 0 < (1 - γ) * y},
      aa_ezKP β ρ γ c y = β ^ θ / (1 - γ) * SS.powF h θ ((1 - γ) * y) := fun y hy =>
    aa_ezKP_eq_powF hβ0 hβ1 hρ hγ hc hy
  -- a function equal on the domain to a strictly convex/concave one
  have transfer_cvx : ∀ g : ℝ → ℝ, StrictConvexOn ℝ {y | 0 < (1 - γ) * y} g →
      (∀ y ∈ {y : ℝ | 0 < (1 - γ) * y}, aa_ezKP β ρ γ c y = g y) →
      StrictConvexOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c) := by
    intro g hg' he
    refine ⟨hg'.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [he x hx, he y hy, he _ (hg'.1 hx hy ha.le hb.le hab)]
    exact hg'.2 hx hy hxy ha hb hab
  have transfer_ccv : ∀ g : ℝ → ℝ, StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} g →
      (∀ y ∈ {y : ℝ | 0 < (1 - γ) * y}, aa_ezKP β ρ γ c y = g y) →
      StrictConcaveOn ℝ {y | 0 < (1 - γ) * y} (aa_ezKP β ρ γ c) := by
    intro g hg' he
    refine ⟨hg'.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [he x hx, he y hy, he _ (hg'.1 hx hy ha.le hb.le hab)]
    exact hg'.2 hx hy hxy ha hb hab
  constructor
  · intro hργ
    rcases lt_or_gt_of_ne hg with hgn | hgp
    · -- `γ > 1`: `k < 0`, need `F` strictly concave: `θ < 0` (ρ < 1) or `θ > 1` (ρ > 1)
      have hk : 0 < -(β ^ θ / (1 - γ)) := by
        rw [neg_pos]; exact div_neg_of_pos_of_neg hβθ hgn
      have hF : StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
        refine aa_powF_strictConcaveOn hh0 ?_
        rcases lt_or_gt_of_ne hr with hrn | hrp
        · right; rw [hθ, lt_div_iff_of_neg hrn]; linarith
        · left; exact div_neg_of_neg_of_pos hgn hrp
      refine transfer_cvx _ ((aa_strictConcaveOn_comp hF.neg.neg hk hg).neg) fun y hy => ?_
      · rw [heq y hy]
        simp
    · -- `γ < 1`: `k > 0`, need `F` strictly convex: `θ ∈ (0, 1)`
      have hk : 0 < β ^ θ / (1 - γ) := div_pos hβθ hgp
      have hrp : 0 < 1 - ρ := by linarith
      have hF : StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) :=
        aa_powF_strictConvexOn hh0 (div_pos hgp hrp) (by rw [hθ, div_lt_one hrp]; linarith)
      exact transfer_cvx _ (aa_strictConvexOn_comp hF hk hg) heq
  · intro hγρ
    rcases lt_or_gt_of_ne hg with hgn | hgp
    · -- `γ > 1`, so `ρ > γ > 1`: `θ ∈ (0, 1)`, `F` strictly convex, `k < 0`
      have hk : 0 < -(β ^ θ / (1 - γ)) := by
        rw [neg_pos]; exact div_neg_of_pos_of_neg hβθ hgn
      have hrn : 1 - ρ < 0 := by linarith
      have hF : StrictConvexOn ℝ (Ioi 0) (SS.powF h θ) :=
        aa_powF_strictConvexOn hh0 (div_pos_of_neg_of_neg hgn hrn)
          (by rw [hθ, div_lt_one_of_neg hrn]; linarith)
      refine transfer_ccv _ ((aa_strictConvexOn_comp hF hk hg).neg) fun y hy => ?_
      rw [heq y hy]
      simp
    · -- `γ < 1`: `k > 0`, `F` strictly concave: `θ > 1` (ρ < 1) or `θ < 0` (ρ > 1)
      have hk : 0 < β ^ θ / (1 - γ) := div_pos hβθ hgp
      have hF : StrictConcaveOn ℝ (Ioi 0) (SS.powF h θ) := by
        refine aa_powF_strictConcaveOn hh0 ?_
        rcases lt_or_gt_of_ne hr with hrn | hrp
        · left; exact div_neg_of_pos_of_neg hgp hrn
        · right; rw [hθ, lt_div_iff₀ hrp]; linarith
      exact transfer_ccv _ (aa_strictConcaveOn_comp hF hk hg) heq

/-- At `γ = ρ` the Kreps–Porteus form is affine in `y`: `W̃(c, y) = (1 − β)u(c) + βy`. -/
theorem aa_ezKP_diag {β γ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hc : 0 < c)
    (hy : 0 < (1 - γ) * y) : aa_ezKP β γ γ c y = (1 - β) * aa_powU γ c + β * y := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hbase : 0 ≤ (1 - β) * c ^ (1 - γ) + β * (((1 - γ) * y) ^ (1 - γ)⁻¹) ^ (1 - γ) := by
    have := Real.rpow_pos_of_pos hc (1 - γ)
    have := Real.rpow_nonneg (Real.rpow_nonneg hy.le (1 - γ)⁻¹) (1 - γ)
    have : 0 < 1 - β := by linarith
    positivity
  unfold aa_ezKP aa_powU aa_W aa_powUinv
  rw [Real.rpow_inv_rpow hbase hg, Real.rpow_inv_rpow hy.le hg]
  field_simp

/-- Consumption on `[a, b]`, `0 < a`: the vNM index `u(x) = x^{1−γ}/(1−γ)` is bounded. -/
theorem aa_powU_bound {a b γ : ℝ} (ha : 0 < a) (x : Icc a b) :
    |aa_powU γ x| ≤ (a ^ (1 - γ) + b ^ (1 - γ)) / |1 - γ| := by
  have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
  unfold aa_powU
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := Real.rpow_pos_of_pos ha (1 - γ)
  have h2 := Real.rpow_pos_of_pos (ha.trans_le (x.2.1.trans x.2.2)) (1 - γ)
  rcases le_or_gt 0 (1 - γ) with hp | hn
  · have := Real.rpow_le_rpow hx.le x.2.2 hp
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha x.2.1 hn.le
    linarith

theorem aa_powU_measurable (a b γ : ℝ) : Measurable fun x : Icc a b => aa_powU γ x := by
  unfold aa_powU
  fun_prop

/-- Expected utilities of lotteries on `[a, b]`, `0 < a`, lie in the domain `(1 − γ)y > 0`. -/
theorem aa_Y_subset {a b γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hγ : γ ≠ 1) :
    aa_Y (fun x : Icc a b => aa_powU γ x) ⊆ {y | 0 < (1 - γ) * y} := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  rintro _ ⟨m, hm, rfl⟩
  have : IsProbabilityMeasure m := hm
  set k := min (a ^ (1 - γ)) (b ^ (1 - γ)) with hk
  have hk0 : 0 < k := lt_min (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos (ha.trans_le hab) _)
  have hlow : ∀ x : Icc a b, k ≤ (1 - γ) * aa_powU γ x := fun x => by
    have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
    unfold aa_powU
    rw [mul_div_cancel₀ _ hg]
    rcases le_or_gt 0 (1 - γ) with hp | hn
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow ha.le x.2.1 hp)
    · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hx x.2.2 hn.le)
  have hint := aa_integrable (aa_powU_measurable a b γ) (aa_powU_bound ha) hm
  have h1 : k ≤ ∫ x, (1 - γ) * aa_powU γ x ∂m := by
    have := integral_mono (integrable_const k) (hint.const_mul (1 - γ)) hlow
    simpa using this
  rw [integral_const_mul] at h1
  exact hk0.trans_le h1

/-- **Exercise 20.3** (Miao, p. 735; p. 704). An agent with Epstein–Zin utility (20.3) over two
periods, consumption in `[a, b]` with `0 < a < b`, `β ∈ (0, 1)`, `ρ, γ ≠ 1`, prefers earlier
resolution of uncertainty (Definition 20.2.4) iff `γ ≥ ρ`. The book's "iff `γ > ρ`" is the strict
preference (`aa_ez_strictEarly`); at `γ = ρ` the agent is indifferent (`aa_ez_indifferent`). -/
theorem ex_20_3 {a b β ρ γ : ℝ} (ha : 0 < a) (hab : a < b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) :
    aa_PrefersEarly (fun c : Icc a b => aa_ezKP β ρ γ c) (fun x : Icc a b => aa_powU γ x) ↔
      ρ ≤ γ := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab.le hγ
  have hYc := aa_Y_convex hU hC
  rw [theorem_20_2_1 _ hU hC]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- strict concavity on two Dirac lotteries contradicts convexity
    have hcc := (aa_ezKP_strict hβ0 hβ1 hρ hγ (c := a) ha).2 hlt
    let xa : Icc a b := ⟨a, le_rfl, hab.le⟩
    let xb : Icc a b := ⟨b, hab.le, le_rfl⟩
    have hda : Measure.dirac xa ∈ aa_Lott (Icc a b) := (inferInstance : IsProbabilityMeasure _)
    have hdb : Measure.dirac xb ∈ aa_Lott (Icc a b) := (inferInstance : IsProbabilityMeasure _)
    have hya : aa_powU γ a ∈ aa_Y (fun x : Icc a b => aa_powU γ x) :=
      ⟨_, hda, by rw [integral_dirac]⟩
    have hyb : aa_powU γ b ∈ aa_Y (fun x : Icc a b => aa_powU γ x) :=
      ⟨_, hdb, by rw [integral_dirac]⟩
    have hne : aa_powU γ a ≠ aa_powU γ b := by
      unfold aa_powU
      intro heq
      have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
      have h2 : a ^ (1 - γ) = b ^ (1 - γ) := by
        have := congrArg (· * (1 - γ)) heq
        simpa [div_mul_cancel₀ _ hg] using this
      have h3 := congrArg (· ^ (1 - γ)⁻¹) h2
      simp only [Real.rpow_rpow_inv ha.le hg, Real.rpow_rpow_inv (ha.trans hab).le hg] at h3
      exact hab.ne h3
    have h1 := (h xa).2 hya hyb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have h2 := hcc.2 (hY hya) (hY hyb) hne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    exact absurd h1 (not_le.2 h2)
  · intro hle x
    have hx : 0 < (x : ℝ) := ha.trans_le x.2.1
    rcases hle.lt_or_eq with hlt | heq
    · exact ((aa_ezKP_strict hβ0 hβ1 hρ hγ hx).1 hlt).convexOn.subset hY hYc
    · subst heq
      refine ⟨hYc, fun y₁ hy₁ y₂ hy₂ s t hs ht hst => ?_⟩
      have hm := hYc hy₁ hy₂ hs ht hst
      rw [aa_ezKP_diag hβ0 hβ1 hγ hx (hY hm), aa_ezKP_diag hβ0 hβ1 hγ hx (hY hy₁),
        aa_ezKP_diag hβ0 hβ1 hγ hx (hY hy₂)]
      simp only [smul_eq_mul]
      have : s * ((1 - β) * aa_powU ρ x) + t * ((1 - β) * aa_powU ρ x) =
          (1 - β) * aa_powU ρ x := by rw [← add_mul, hst, one_mul]
      nlinarith

/-- Miao, p. 704: for `γ > ρ` the Epstein–Zin agent strictly prefers earlier resolution whenever
the two lotteries have different expected utilities and `α ∈ (0, 1)`. -/
theorem aa_ez_strictEarly {a b β ρ γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1) (hργ : ρ < γ) (c₀ : Icc a b) {m m' : Measure (Icc a b)}
    (hm : m ∈ aa_Lott (Icc a b)) (hm' : m' ∈ aa_Lott (Icc a b))
    (hne : ∫ x, aa_powU γ x ∂m ≠ ∫ x, aa_powU γ x ∂m') {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂(aa_mix α m m')) <
      α * aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂m) +
        (1 - α) * aa_ezKP β ρ γ c₀ (∫ x, aa_powU γ x ∂m') := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab hγ
  have hc : 0 < (c₀ : ℝ) := ha.trans_le c₀.2.1
  have hcv := (aa_ezKP_strict hβ0 hβ1 hρ hγ hc).1 hργ
  rw [aa_integral_mix hU hC hα0.le hα1.le hm hm']
  have := hcv.2 (hY ⟨m, hm, rfl⟩) (hY ⟨m', hm', rfl⟩) hne hα0 (by linarith : 0 < 1 - α)
    (by ring)
  simpa [smul_eq_mul] using this

/-- Miao, p. 686: at `γ = ρ` (time-additive expected power utility) the Epstein–Zin agent is
indifferent to the timing of resolution. -/
theorem aa_ez_indifferent {a b β γ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≠ 1) (c₀ : Icc a b) {m m' : Measure (Icc a b)} (hm : m ∈ aa_Lott (Icc a b))
    (hm' : m' ∈ aa_Lott (Icc a b)) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂(aa_mix α m m')) =
      α * aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂m) +
        (1 - α) * aa_ezKP β γ γ c₀ (∫ x, aa_powU γ x ∂m') := by
  have hU := aa_powU_measurable a b γ
  have hC := aa_powU_bound (γ := γ) (b := b) ha
  have hY := aa_Y_subset ha hab hγ
  have hc : 0 < (c₀ : ℝ) := ha.trans_le c₀.2.1
  have hmix := hY ⟨_, aa_mix_mem hα0 hα1 hm hm', rfl⟩
  rw [aa_ezKP_diag hβ0 hβ1 hγ hc hmix, aa_ezKP_diag hβ0 hβ1 hγ hc (hY ⟨m, hm, rfl⟩),
    aa_ezKP_diag hβ0 hβ1 hγ hc (hY ⟨m', hm', rfl⟩), aa_integral_mix hU hC hα0 hα1 hm hm']
  ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concavity of recursive utility

Miao, §20.3.1, pp. 704–705.

* Backward induction (p. 705): on a finite event tree, if the time aggregator `W` is jointly
  concave and increasing in its second argument and every conditional certainty equivalent `M_t` is
  concave and monotone, the recursive utility `U_t(c) = W(c_t, M_t(U_{t+1}(c)))`, `U_T = c_T`, is
  concave in the plan (`aa_recU_concaveOn`).
* The strict version asserted in the text (`W` strictly increasing and concave, `M` strictly
  concave ⇒ `U` strictly concave) is false: with `W(c, y) = c + βy`, perturbing consumption at a
  single node moves `U` affinely, whatever `M` is (`aa_recU_not_strictConcave`).
* The Epstein–Zin claim (p. 705): for `ρ > 0`, `γ > 0` (`ρ, γ ≠ 1`) and `U_T(c) = c_T`, `U_t` is
  concave (`aa_ezU_concaveOn`) and homogeneous of degree one (`aa_ezU_smul`), hence never strictly
  concave (`aa_ezU_not_strictConcave`): the book's "strictly concave" is false; it holds only
  across non-proportional plans.
* **Lemma 20.3.1** (Skiadas 2009). For `f : ℝ^l_{++} → ℝ` homogeneous of degree one, (i) concavity
  and (iii) superadditivity are equivalent (`lemma_20_3_1_i_iff_iii`), and imply (ii) the
  level-set condition `f(x) = f(y), x ≠ y ⇒ f(λx + (1 − λ)y) ≥ f(x)` (`lemma_20_3_1_i_ii`; the book
  prints `f(λx + (1 − λ))`). (ii) implies (i) and (iii) when `f > 0` (`lemma_20_3_1`), but not in
  general: `f(x) = φ(x₁ − x₂)` with `φ(s) = s + max(s, 0)` satisfies (ii) but neither (i) nor (iii)
  (`lemma_20_3_1_counterexample`).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- Recursive utility `U_t(c) = W(c_t, M_t(U_{t+1}(c)))` on the event tree, `U_T(c) = c_T`; `M h` is
the conditional certainty equivalent at the node `h`. -/
noncomputable def aa_recU (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) (c : List S → ℝ) :
    ℕ → List S → ℝ
  | 0, h => c h
  | n + 1, h => W (c h) (M h fun s => aa_recU W M c n (s :: h))

/-- The positive plans. -/
def aa_posPlans (S : Type*) : Set (List S → ℝ) := {c | ∀ h, 0 < c h}

omit [Fintype S] in
theorem aa_posPlans_convex : Convex ℝ (aa_posPlans S) := by
  intro c hc c' hc' a b ha hb hab h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · nlinarith [mul_pos ha' (hc h), mul_nonneg hb (hc' h).le]
  · subst ha'
    rw [zero_add] at hab
    subst hab
    simpa using hc' h

omit [Fintype S] in
/-- **Concavity by backward induction** (Miao, p. 705). Suppose `W` is jointly concave on
`(0, ∞)²`, monotone in `y`, and positive; every `M_h` is concave and monotone on `(0, ∞)^S` and
positive. Then `U_n(·, h)` is positive and concave on positive plans, for every horizon `n` and
node `h`. -/
theorem aa_recU_concaveOn {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ}
    (hWc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) fun z : ℝ × ℝ => W z.1 z.2)
    (hWm : ∀ c, 0 < c → MonotoneOn (W c) (Set.Ioi 0))
    (hWp : ∀ c y, 0 < c → 0 < y → 0 < W c y)
    (hMc : ∀ h, ConcaveOn ℝ (SS.posCone S) (M h)) (hMm : ∀ h, MonotoneOn (M h) (SS.posCone S))
    (hMp : ∀ h x, x ∈ SS.posCone S → 0 < M h x) :
    ∀ n h, (∀ c ∈ aa_posPlans S, 0 < aa_recU W M c n h) ∧
      ConcaveOn ℝ (aa_posPlans S) fun c => aa_recU W M c n h := by
  intro n
  induction n with
  | zero =>
    intro h
    refine ⟨fun c hc => hc h, aa_posPlans_convex, fun c _ c' _ a b _ _ _ => ?_⟩
    simp [aa_recU]
  | succ n ih =>
    intro h
    have hpos : ∀ c ∈ aa_posPlans S, (fun s => aa_recU W M c n (s :: h)) ∈ SS.posCone S :=
      fun c hc s => (ih (s :: h)).1 c hc
    refine ⟨fun c hc => hWp _ _ (hc h) (hMp h _ (hpos c hc)), aa_posPlans_convex, ?_⟩
    intro c hc c' hc' a b ha hb hab
    simp only [aa_recU, smul_eq_mul]
    have hmix := aa_posPlans_convex hc hc' ha hb hab
    -- children: concavity of `U_n`
    have hchild : ∀ s, a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h) ≤
        aa_recU W M (a • c + b • c') n (s :: h) := fun s => by
      have := (ih (s :: h)).2.2 hc hc' ha hb hab
      simpa [smul_eq_mul] using this
    have hcomb : (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) ∈
        SS.posCone S := SS.convex_posCone (hpos c hc) (hpos c' hc') ha hb hab
    have hM1 : a * M h (fun s => aa_recU W M c n (s :: h)) +
        b * M h (fun s => aa_recU W M c' n (s :: h)) ≤
          M h (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) := by
      have := (hMc h).2 (hpos c hc) (hpos c' hc') ha hb hab
      simp only [smul_eq_mul] at this
      convert this using 2
    have hM2 : M h (fun s => a * aa_recU W M c n (s :: h) + b * aa_recU W M c' n (s :: h)) ≤
        M h (fun s => aa_recU W M (a • c + b • c') n (s :: h)) :=
      hMm h hcomb (hpos _ hmix) hchild
    have hy1 := hMp h _ (hpos c hc)
    have hy2 := hMp h _ (hpos c' hc')
    have hy3 : 0 < a * M h (fun s => aa_recU W M c n (s :: h)) +
        b * M h (fun s => aa_recU W M c' n (s :: h)) := by
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_pos ha' hy1, mul_nonneg hb hy2.le]
      · subst ha'
        rw [zero_add] at hab
        subst hab
        simpa using hy2
    have hW1 : a * W (c h) (M h fun s => aa_recU W M c n (s :: h)) +
        b * W (c' h) (M h fun s => aa_recU W M c' n (s :: h)) ≤
          W (a * c h + b * c' h) (a * M h (fun s => aa_recU W M c n (s :: h)) +
            b * M h (fun s => aa_recU W M c' n (s :: h))) := by
      have := hWc.2 (x := (c h, M h fun s => aa_recU W M c n (s :: h)))
        (y := (c' h, M h fun s => aa_recU W M c' n (s :: h))) ⟨hc h, hy1⟩ ⟨hc' h, hy2⟩ ha hb hab
      simpa [smul_eq_mul] using this
    have hch : (a • c + b • c') h = a * c h + b * c' h := by simp
    rw [hch]
    exact hW1.trans (hWm _ (by rw [← hch]; exact hmix h) hy3 (hMp h _ (hpos _ hmix))
      (hM1.trans hM2))

omit [Fintype S] in
/-- `U_n(c, g)` depends only on consumption at nodes of length at least `|g|`. -/
theorem aa_recU_congr (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) {c c' : List S → ℝ} :
    ∀ n g, (∀ g', g.length ≤ g'.length → c g' = c' g') → aa_recU W M c n g = aa_recU W M c' n g
  | 0, g, hg => hg g le_rfl
  | n + 1, g, hg => by
    simp only [aa_recU]
    rw [hg g le_rfl]
    congr 2
    funext s
    exact aa_recU_congr W M n (s :: g) fun g' hg' => hg g' (by simp at hg'; omega)

omit [Fintype S] in
/-- **The strict version is false** (Miao, p. 705): with `W(c, y) = c + βy`, for any conditional
certainty equivalents `M`, `U_{n+1}(·, h)` is affine along perturbations of consumption at the node
`h`, so it is not strictly concave on the positive plans. -/
theorem aa_recU_not_strictConcave [Nonempty S] (β : ℝ) (M : List S → (S → ℝ) → ℝ) (n : ℕ)
    (h : List S) :
    ¬ StrictConcaveOn ℝ (aa_posPlans S) fun c => aa_recU (fun x y => x + β * y) M c (n + 1) h := by
  classical
  intro hsc
  set c : List S → ℝ := fun _ => 1 with hcdef
  set c' : List S → ℝ := Function.update c h 3 with hc'def
  have hc : c ∈ aa_posPlans S := fun _ => one_pos
  have hc' : c' ∈ aa_posPlans S := fun g => by
    simp only [hc'def, Function.update_apply]
    split_ifs <;> norm_num [hcdef]
  have hne : c ≠ c' := fun he => by
    have := congrFun he h
    simp [hc'def, hcdef] at this
  have key := hsc.2 hc hc' hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hagree : ∀ d : List S → ℝ, (∀ g, g ≠ h → d g = 1) → ∀ s,
      aa_recU (fun x y => x + β * y) M d n (s :: h) =
        aa_recU (fun x y => x + β * y) M c n (s :: h) := fun d hd s =>
    aa_recU_congr _ M n (s :: h) fun g' hg' => by
      rw [hd g' (fun he => by subst he; simp at hg')]
  have hmix : ∀ g, g ≠ h → ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • c') g = 1 := fun g hg => by
    simp [hc'def, hcdef, hg]
    norm_num
  have hc'1 : ∀ g, g ≠ h → c' g = 1 := fun g hg => by simp [hc'def, hcdef, hg]
  simp only [aa_recU, smul_eq_mul] at key
  rw [show (fun s => aa_recU (fun x y => x + β * y) M ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • c') n
      (s :: h)) = fun s => aa_recU (fun x y => x + β * y) M c n (s :: h) from
        funext (hagree _ hmix),
    show (fun s => aa_recU (fun x y => x + β * y) M c' n (s :: h)) =
      fun s => aa_recU (fun x y => x + β * y) M c n (s :: h) from funext (hagree _ hc'1)] at key
  simp [hc'def, hcdef] at key
  linarith

/-! ### Epstein–Zin -/

/-- The Epstein–Zin finite-horizon utility is the recursive utility with `W` the CES aggregator
and `M_h` the Kreps–Porteus certainty equivalent. -/
theorem aa_ezU_eq_recU (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) :
    ∀ n h, aa_ezU β ρ γ p c n h = aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n h
  | 0, _ => rfl
  | n + 1, h => by
    simp only [aa_ezU, aa_recU]
    rw [show (fun s => aa_ezU β ρ γ p c n (s :: h)) =
      (fun s => aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n (s :: h)) from
        funext fun s => aa_ezU_eq_recU β ρ γ p c n (s :: h)]

/-- The Kreps–Porteus certainty equivalent is concave on `(0, ∞)^S` for `γ ≥ 0`, `γ ≠ 1`. -/
theorem aa_KP_concaveOn [Nonempty S] {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≠ 1) {p : S → ℝ}
    (hp : SS.IsDistribution p) : ConcaveOn ℝ (SS.posCone S) (aa_KP γ p) := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have hP : SS.IsMarkov (fun (_ : S) (s : S) => p s : Matrix S S ℝ) :=
    ⟨fun _ s => hp.nonneg s, fun _ => hp.sum_eq_one⟩
  have h := SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hγ1)) (by linarith) hP
  have e : ∀ x, aa_KP γ p x = SS.kpR (1 - γ) (fun (_ : S) (s : S) => p s : Matrix S S ℝ) x s₀ :=
    fun x => by
      simp [aa_KP, SS.kpR, aa_E, Matrix.mulVec, dotProduct]
  refine ⟨SS.convex_posCone, fun x hx y hy a b ha hb hab => ?_⟩
  rw [e, e, e]
  exact h.2 hx hy ha hb hab s₀

/-- The CES aggregator is jointly concave on `(0, ∞)²` for `ρ ≥ 0`, `ρ ≠ 1`, `β ∈ [0, 1]`. -/
theorem aa_W_concaveOn {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) fun z : ℝ × ℝ => aa_W β ρ z.1 z.2 := by
  set P : Matrix Bool Bool ℝ := fun _ b => if b then β else 1 - β with hPdef
  have hP : SS.IsMarkov P :=
    ⟨fun _ b => by cases b <;> simp [hPdef] <;> linarith, fun _ => by simp [hPdef]⟩
  have h := SS.concaveOn_kpR (sub_ne_zero.2 (Ne.symm hρ1)) (by linarith) hP
  let v : ℝ × ℝ → Bool → ℝ := fun z b => if b then z.2 else z.1
  have e : ∀ z : ℝ × ℝ, aa_W β ρ z.1 z.2 = SS.kpR (1 - ρ) P (v z) true := fun z => by
    simp [aa_W, SS.kpR, Matrix.mulVec, dotProduct, hPdef, v, add_comm]
  have hv : ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0, v z ∈ SS.posCone Bool := fun z hz b => by
    cases b
    · exact hz.1
    · exact hz.2
  have hlin : ∀ (z w : ℝ × ℝ) (a b : ℝ), v (a • z + b • w) = a • v z + b • v w := fun z w a b => by
    funext t
    cases t <;> simp [v]
  refine ⟨(convex_Ioi 0).prod (convex_Ioi 0), fun z hz w hw a b ha hb hab => ?_⟩
  dsimp only
  rw [e, e, e, hlin]
  exact h.2 (hv z hz) (hv w hw) ha hb hab true

/-- Miao, p. 705 (the corrected claim): for the Epstein–Zin utility (20.3) with a finite horizon,
`U_T(c) = c_T`, `ρ > 0` and `γ > 0` (`ρ, γ ≠ 1`, `β ∈ (0, 1)`), every `U_t` is concave on positive
plans. -/
theorem aa_ezU_concaveOn [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≠ 1) (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) {p : List S → S → ℝ}
    (hp : ∀ h, SS.IsDistribution (p h)) (n : ℕ) (h : List S) :
    ConcaveOn ℝ (aa_posPlans S) fun c => aa_ezU β ρ γ p c n h := by
  have := (aa_recU_concaveOn (aa_W_concaveOn hβ0.le hβ1.le hρ0.le hρ1)
    (fun c hc => (aa_W_strictMonoOn hβ0 hβ1 hρ1 hc).monotoneOn)
    (fun c y hc hy => aa_W_pos hβ0 hβ1 hc hy) (fun h => aa_KP_concaveOn hγ0.le hγ1 (hp h))
    (fun h x hx y _ hxy => aa_KP_mono hγ1 (hp h) hx hxy)
    (fun h x hx => aa_KP_pos γ (hp h) hx) n h).2
  simpa only [aa_ezU_eq_recU] using this

/-- Homogeneity of degree one of the Epstein–Zin utility: `U_t(λc) = λU_t(c)` for `λ > 0`. -/
theorem aa_ezU_smul [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1)
    (hγ : γ ≠ 1) {p : List S → S → ℝ}
    (hp : ∀ h, SS.IsDistribution (p h)) {c : List S → ℝ} (hc : ∀ h, 0 < c h) {t : ℝ}
    (ht : 0 < t) : ∀ n h, aa_ezU β ρ γ p (t • c) n h = t * aa_ezU β ρ γ p c n h
  | 0, h => by simp [aa_ezU]
  | n + 1, h => by
    simp only [aa_ezU]
    rw [show (fun s => aa_ezU β ρ γ p (t • c) n (s :: h)) =
      (fun s => t * aa_ezU β ρ γ p c n (s :: h)) from
        funext fun s => aa_ezU_smul hβ0 hβ1 hρ hγ hp hc ht n (s :: h)]
    have hx : ∀ s, 0 < aa_ezU β ρ γ p c n (s :: h) := fun s => aa_ezU_pos hβ0 hβ1 hp hc n _
    have hE := aa_E_pos (hp h) fun s => Real.rpow_pos_of_pos (hx s) (1 - γ)
    have hK : aa_KP γ (p h) (fun s => t * aa_ezU β ρ γ p c n (s :: h)) =
        t * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) := by
      unfold aa_KP
      rw [show (fun s => (t * aa_ezU β ρ γ p c n (s :: h)) ^ (1 - γ)) =
        (fun s => t ^ (1 - γ) * aa_ezU β ρ γ p c n (s :: h) ^ (1 - γ)) from
          funext fun s => Real.mul_rpow ht.le (hx s).le, aa_E_smul,
        Real.mul_rpow (Real.rpow_nonneg ht.le _) hE.le]
      rw [Real.rpow_rpow_inv ht.le (sub_ne_zero.2 (Ne.symm hγ))]
    rw [hK]
    have hKp := aa_KP_pos γ (hp h) hx
    unfold aa_W
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.mul_rpow ht.le (hc h).le, Real.mul_rpow ht.le hKp.le]
    have hb : 0 ≤ (1 - β) * c h ^ (1 - ρ) +
        β * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ) :=
      add_nonneg (mul_nonneg (by linarith) (Real.rpow_pos_of_pos (hc h) _).le)
        (mul_nonneg hβ0.le (Real.rpow_pos_of_pos hKp _).le)
    rw [show (1 - β) * (t ^ (1 - ρ) * c h ^ (1 - ρ)) +
        β * (t ^ (1 - ρ) * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ)) =
      t ^ (1 - ρ) * ((1 - β) * c h ^ (1 - ρ) +
        β * aa_KP γ (p h) (fun s => aa_ezU β ρ γ p c n (s :: h)) ^ (1 - ρ)) by ring,
      Real.mul_rpow (Real.rpow_nonneg ht.le _) hb]
    rw [Real.rpow_rpow_inv ht.le (sub_ne_zero.2 (Ne.symm hρ))]

/-- **The Epstein–Zin utility is not strictly concave** (correction to Miao, p. 705): being
homogeneous of degree one, `U_t` is affine along every ray, so the claim "`U_t` is strictly
concave" fails for every horizon. -/
theorem aa_ezU_not_strictConcave [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) (n : ℕ) (h : List S) :
    ¬ StrictConcaveOn ℝ (aa_posPlans S) fun c => aa_ezU β ρ γ p c n h := by
  intro hsc
  set c : List S → ℝ := fun _ => 1 with hcdef
  have hc : c ∈ aa_posPlans S := fun _ => one_pos
  have h3 : (3 : ℝ) • c ∈ aa_posPlans S := fun g => by simp [hcdef]
  have hne : c ≠ (3 : ℝ) • c := fun he => by
    have := congrFun he []
    simp [hcdef] at this
  have key := hsc.2 hc h3 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hmix : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • ((3 : ℝ) • c) = (2 : ℝ) • c := by
    funext g; simp [hcdef]; norm_num
  simp only [smul_eq_mul] at key
  rw [hmix, aa_ezU_smul hβ0 hβ1 hρ hγ hp hc (by norm_num) n h,
    aa_ezU_smul hβ0 hβ1 hρ hγ hp hc (by norm_num) n h] at key
  linarith

/-! ### Lemma 20.3.1 -/

variable {ι : Type*}

/-- Homogeneity of degree one on `ℝ^l_{++}`. -/
def aa_Homogeneous1 (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ t : ℝ, 0 < t → f (t • x) = t * f x

/-- Condition (ii) of Lemma 20.3.1 (with the book's misprint `f(λx + (1 − λ))` read as
`f(λx + (1 − λ)y)`). -/
def aa_LevelCond (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ y ∈ SS.posCone ι, f x = f y → x ≠ y → ∀ l : ℝ, 0 < l → l < 1 →
    f x ≤ f (l • x + (1 - l) • y)

/-- Condition (iii) of Lemma 20.3.1: superadditivity. -/
def aa_Superadd (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ SS.posCone ι, ∀ y ∈ SS.posCone ι, f x + f y ≤ f (x + y)

/-- **Lemma 20.3.1**, (i) ⇔ (iii) (Miao, p. 705): a function homogeneous of degree one on
`ℝ^l_{++}` is concave iff it is superadditive. -/
theorem lemma_20_3_1_i_iff_iii {f : (ι → ℝ) → ℝ} (hf : aa_Homogeneous1 f) :
    ConcaveOn ℝ (SS.posCone ι) f ↔ aa_Superadd f := by
  constructor
  · intro hc x hx y hy
    have h := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have hxy : x + y ∈ SS.posCone ι := fun i => add_pos (hx i) (hy i)
    have e : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by
      rw [smul_add]
    rw [e, hf _ hxy _ (by norm_num), smul_eq_mul, smul_eq_mul] at h
    linarith
  · intro hs
    refine ⟨SS.convex_posCone, fun x hx y hy a b ha hb hab => ?_⟩
    rcases ha.lt_or_eq with ha' | ha'
    · rcases hb.lt_or_eq with hb' | hb'
      · have hax := SS.smul_mem_posCone hx ha'
        have hby := SS.smul_mem_posCone hy hb'
        have := hs _ hax _ hby
        rwa [hf x hx a ha', hf y hy b hb'] at this
      · subst hb'
        rw [add_zero] at hab
        subst hab
        simp
    · subst ha'
      rw [zero_add] at hab
      subst hab
      simp

/-- **Lemma 20.3.1**, (i) ⇒ (ii) (Miao, p. 705). -/
theorem lemma_20_3_1_i_ii {f : (ι → ℝ) → ℝ} (hc : ConcaveOn ℝ (SS.posCone ι) f) :
    aa_LevelCond f := by
  intro x hx y hy hxy _ l hl0 hl1
  have := hc.2 hx hy hl0.le (by linarith : 0 ≤ 1 - l) (by ring)
  rw [smul_eq_mul, smul_eq_mul, ← hxy] at this
  linarith

/-- **Lemma 20.3.1** (Miao, p. 705; Skiadas 2009), for positive `f`: for `f : ℝ^l_{++} → (0, ∞)`
homogeneous of degree one, (i) concavity, (ii) the level-set condition and (iii) superadditivity
are equivalent. -/
theorem lemma_20_3_1 {f : (ι → ℝ) → ℝ} (hf : aa_Homogeneous1 f)
    (hpos : ∀ x ∈ SS.posCone ι, 0 < f x) :
    (ConcaveOn ℝ (SS.posCone ι) f ↔ aa_LevelCond f) ∧
      (ConcaveOn ℝ (SS.posCone ι) f ↔ aa_Superadd f) := by
  have hiii := lemma_20_3_1_i_iff_iii hf
  refine ⟨⟨lemma_20_3_1_i_ii, fun hii => hiii.2 ?_⟩, hiii⟩
  intro x hx y hy
  have hfx := hpos x hx
  have hfy := hpos y hy
  set x' := (f x)⁻¹ • x with hx'
  set y' := (f y)⁻¹ • y with hy'
  have hx'p : x' ∈ SS.posCone ι := SS.smul_mem_posCone hx (inv_pos.2 hfx)
  have hy'p : y' ∈ SS.posCone ι := SS.smul_mem_posCone hy (inv_pos.2 hfy)
  have hfx' : f x' = 1 := by rw [hf x hx _ (inv_pos.2 hfx), inv_mul_cancel₀ hfx.ne']
  have hfy' : f y' = 1 := by rw [hf y hy _ (inv_pos.2 hfy), inv_mul_cancel₀ hfy.ne']
  set l := f x / (f x + f y) with hl
  have hl0 : 0 < l := div_pos hfx (add_pos hfx hfy)
  have hl1 : l < 1 := by rw [hl, div_lt_one (add_pos hfx hfy)]; linarith
  have hsum : x + y = (f x + f y) • (l • x' + (1 - l) • y') := by
    rw [hx', hy', hl, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    have e1 : (f x + f y) * (f x / (f x + f y)) * (f x)⁻¹ = 1 := by field_simp
    have e2 : (f x + f y) * (1 - f x / (f x + f y)) * (f y)⁻¹ = 1 := by field_simp; ring
    rw [e1, e2, one_smul, one_smul]
  have hmixp : l • x' + (1 - l) • y' ∈ SS.posCone ι :=
    SS.convex_posCone hx'p hy'p hl0.le (by linarith) (by ring)
  have hmix1 : 1 ≤ f (l • x' + (1 - l) • y') := by
    by_cases hxy : x' = y'
    · rw [hxy, ← add_smul, show l + (1 - l) = 1 by ring, one_smul, hfy']
    · have := hii x' hx'p y' hy'p (by rw [hfx', hfy']) hxy l hl0 hl1
      rwa [hfx'] at this
  rw [hsum, hf _ hmixp _ (add_pos hfx hfy)]
  nlinarith

/-- The counterexample to Lemma 20.3.1 without positivity: `f(x) = φ(x₀ − x₁)` with
`φ(s) = s + max(s, 0)` on `ℝ²_{++}`. -/
noncomputable def aa_skiadasCex (x : Fin 2 → ℝ) : ℝ := (x 0 - x 1) + max (x 0 - x 1) 0

/-- **Lemma 20.3.1 fails without positivity** (Miao, p. 705): `f(x) = φ(x₀ − x₁)`,
`φ(s) = s + max(s, 0)`, is homogeneous of degree one and satisfies (ii) on `ℝ²_{++}`, but it is
neither superadditive (iii) nor concave (i): `f(2, 1) + f(1, 2) = 1 > 0 = f(3, 3)`. -/
theorem lemma_20_3_1_counterexample :
    aa_Homogeneous1 aa_skiadasCex ∧ aa_LevelCond aa_skiadasCex ∧ ¬ aa_Superadd aa_skiadasCex ∧
      ¬ ConcaveOn ℝ (SS.posCone (Fin 2)) aa_skiadasCex := by
  have hhom : aa_Homogeneous1 aa_skiadasCex := fun x _ t ht => by
    simp only [aa_skiadasCex, Pi.smul_apply, smul_eq_mul]
    have e : max (t * (x 0 - x 1)) 0 = t * max (x 0 - x 1) 0 := by
      rw [mul_max_of_nonneg _ _ ht.le, mul_zero]
    rw [← mul_sub, e]
    ring
  have hinj : ∀ d e : ℝ, d + max d 0 = e + max e 0 → d = e := fun d e h => by
    rcases le_total d 0 with hd | hd <;> rcases le_total e 0 with he | he <;>
      simp only [max_eq_right, max_eq_left, hd, he] at h <;> linarith
  have hsup : ¬ aa_Superadd aa_skiadasCex := fun h => by
    have := h ![2, 1] (fun i => by fin_cases i <;> norm_num) ![1, 2]
      (fun i => by fin_cases i <;> norm_num)
    simp [aa_skiadasCex] at this
    norm_num at this
  refine ⟨hhom, ?_, hsup, fun hc => hsup ((lemma_20_3_1_i_iff_iii hhom).1 hc)⟩
  intro x _ y _ hxy _ l _ _
  have hd := hinj _ _ hxy
  have : aa_skiadasCex (l • x + (1 - l) • y) = aa_skiadasCex x := by
    simp only [aa_skiadasCex, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : l * x 0 + (1 - l) * y 0 - (l * x 1 + (1 - l) * y 1) = x 0 - x 1 := by
      have : y 0 - y 1 = x 0 - x 1 := hd.symm
      nlinarith
    rw [this]
  rw [this]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Comparative risk aversion

Miao, §20.3.2, pp. 705–706: comparative risk aversion of recursive utilities on the event tree
(finite horizon, `U_T = c_T`; `aa_recU` of `AAConcavity`).

* A plan is deterministic if consumption depends only on the date (`aa_Deterministic`); `U¹` is
  more risk averse than `U²` if `U²_t(b) > U²_t(c) ⇒ U¹_t(b) > U¹_t(c)` for deterministic `b`, at
  every node and horizon (`aa_MoreRiskAverse`); `U¹` is risk averse relative to a family of
  benchmarks (`aa_RiskAverse`, the book's definition).
* With a common aggregator, both utilities agree on deterministic plans
  (`aa_recU_deterministic`).
* **Proposition 20.3.1**, first part: for a common aggregator `W` strictly increasing in its second
  argument and conditional certainty equivalents with `M(k) = k`, `U¹` is more risk averse than
  `U²` iff `M¹_t ≤ M²_t` for all `t` (`proposition_20_3_1`).
* **Proposition 20.3.1**, second part ("standard risk theory", Pratt): for the expected-utility
  certainty equivalents `u_i⁻¹E u_i` on an interval `D`, `M¹ ≤ M²` for all lotteries iff
  `u₁ = φ ∘ u₂` with `φ` increasing and concave (`aa_pratt_of_concave`, `aa_concave_of_pratt`,
  `proposition_20_3_1_pratt`), so with `u_i` order isomorphisms of `ℝ` a concave `φ` makes `U¹` more
  risk averse (`proposition_20_3_1_ez`). Departure: the converse needs the certainty-equivalent
  comparison for all two-point lotteries; on a tree with given conditional probabilities the first
  part only yields it for those probabilities.
* The book's definition of risk aversion is never satisfied, since `c = b` is allowed
  (`aa_riskAverse_never`); and even for random `c` (`aa_RiskAverse'`), being more risk averse than a
  risk-neutral `U²` does not imply it (`aa_moreRiskAverse_not_riskAverse`).

Not formalised: comparative ambiguity aversion (the text only discusses the approaches of
Ghirardato–Marinacci and Epstein, without statements).
-/

namespace Miao.RecursiveUtility

open Finset

variable {S : Type*} [Fintype S]

/-- A deterministic plan: consumption depends only on the date. -/
def aa_Deterministic (b : List S → ℝ) : Prop := ∀ h h' : List S, h.length = h'.length → b h = b h'

/-- `U¹` (certainty equivalents `M₁`) is more risk averse than `U²` (`M₂`), with common aggregator
`W`: whenever `U²` prefers a deterministic plan `b` to a plan `c`, so does `U¹`. -/
def aa_MoreRiskAverse (W : ℝ → ℝ → ℝ) (M₁ M₂ : List S → (S → ℝ) → ℝ) : Prop :=
  ∀ n h (b c : List S → ℝ), aa_Deterministic b →
    aa_recU W M₂ c n h < aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The book's risk aversion: `U²_t(b) = U²_t(c) ⇒ U¹_t(b) > U¹_t(c)` for deterministic `b`, for
every benchmark `M₂` in the family `B`. -/
def aa_RiskAverse (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    (B : Set (List S → (S → ℝ) → ℝ)) : Prop :=
  ∀ M₂ ∈ B, ∀ n h (b c : List S → ℝ), aa_Deterministic b →
    aa_recU W M₂ c n h = aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The certainty-equivalent property `M(k) = k`. -/
def aa_IsCE (M : List S → (S → ℝ) → ℝ) : Prop := ∀ h k, M h (fun _ => k) = k

omit [Fintype S] in
/-- A deterministic plan has the same utility at every node of a given date, and all utilities with
the aggregator `W` and certainty equivalents agree on it. -/
theorem aa_recU_deterministic [Nonempty S] (W : ℝ → ℝ → ℝ) {M₁ M₂ : List S → (S → ℝ) → ℝ}
    (h₁ : aa_IsCE M₁) (h₂ : aa_IsCE M₂) {b : List S → ℝ} (hb : aa_Deterministic b) :
    ∀ n (g g' : List S), g.length = g'.length → aa_recU W M₁ b n g = aa_recU W M₂ b n g' := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  intro n
  induction n with
  | zero => intro g g' hg; exact hb g g' hg
  | succ n ih =>
    intro g g' hg
    simp only [aa_recU]
    have e1 : (fun s => aa_recU W M₁ b n (s :: g)) = fun _ => aa_recU W M₁ b n (s₀ :: g) :=
      funext fun s => (ih (s :: g) (s₀ :: g) rfl).trans (ih (s₀ :: g) (s₀ :: g) rfl).symm |>.trans
        (by rw [ih (s₀ :: g) (s₀ :: g) rfl])
    have e2 : (fun s => aa_recU W M₂ b n (s :: g')) = fun _ => aa_recU W M₂ b n (s₀ :: g') :=
      funext fun s => ((ih (s₀ :: g') (s :: g') rfl).symm.trans (ih (s₀ :: g') (s₀ :: g') rfl))
    rw [e1, e2, h₁, h₂, hb g g' hg, ih (s₀ :: g) (s₀ :: g') (by simp [hg])]

omit [Fintype S] in
/-- With `M₁ ≤ M₂`, `M₁` monotone and `W` monotone in `y`, `U¹ ≤ U²` for every plan. -/
theorem aa_recU_le {W : ℝ → ℝ → ℝ} (hW : ∀ c, Monotone (W c)) {M₁ M₂ : List S → (S → ℝ) → ℝ}
    (hM₁ : ∀ h, Monotone (M₁ h)) (hle : ∀ h x, M₁ h x ≤ M₂ h x) (c : List S → ℝ) :
    ∀ n h, aa_recU W M₁ c n h ≤ aa_recU W M₂ c n h
  | 0, _ => le_rfl
  | n + 1, h => by
    simp only [aa_recU]
    exact hW _ ((hM₁ h fun s => aa_recU_le hW hM₁ hle c n (s :: h)).trans (hle h _))

omit [Fintype S] in
/-- **Proposition 20.3.1** (Miao, p. 706), first part. Let `U¹, U²` be recursive utilities with a
common aggregator `W`, strictly increasing in its second argument, and conditional certainty
equivalents `M₁, M₂` (`M(k) = k`), `M₁` monotone. Then `U¹` is more risk averse than `U²` iff
`M₁_t ≤ M₂_t` for all `t`. -/
theorem proposition_20_3_1 [Nonempty S] {W : ℝ → ℝ → ℝ} (hW : ∀ c, StrictMono (W c))
    {M₁ M₂ : List S → (S → ℝ) → ℝ} (h₁ : aa_IsCE M₁) (h₂ : aa_IsCE M₂)
    (hM₁ : ∀ h, Monotone (M₁ h)) :
    aa_MoreRiskAverse W M₁ M₂ ↔ ∀ h x, M₁ h x ≤ M₂ h x := by
  classical
  constructor
  · intro hra h x
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy2, hy1⟩ := exists_between hlt
    -- the plan with consumption `0` at the date of `h` and the continuation `x` after `h`
    let c : List S → ℝ := fun g => match g with
      | [] => 0
      | s :: g' => if g' = h then x s else 0
    let b : List S → ℝ := fun g => if g.length = h.length then 0 else y
    have hb : aa_Deterministic b := fun g g' hg => by simp only [b, hg]
    have hch : c h = 0 := by
      rcases h with _ | ⟨s, g'⟩
      · rfl
      · simp only [c]
        split_ifs with he
        · exact absurd (congrArg List.length he) (by simp)
        · rfl
    have hcc : (fun s => c (s :: h)) = x := funext fun s => by simp [c]
    have hbb : (fun s => b (s :: h)) = fun _ => y := funext fun s => by simp [b]
    have hbh : b h = 0 := by simp [b]
    have hU2 : aa_recU W M₂ c 1 h < aa_recU W M₂ b 1 h := by
      simp only [aa_recU]
      rw [hcc, hbb, h₂, hch, hbh]
      exact hW 0 hy2
    have hU1 := hra 1 h b c hb hU2
    simp only [aa_recU] at hU1
    rw [hcc, hbb, h₁, hch, hbh] at hU1
    exact absurd (hW 0 hy1) (not_lt.2 hU1.le)
  · intro hle n h b c hb hlt
    have hdet := aa_recU_deterministic W h₂ h₁ hb n h h rfl
    calc aa_recU W M₁ c n h ≤ aa_recU W M₂ c n h :=
          aa_recU_le (fun c => (hW c).monotone) hM₁ hle c n h
      _ < aa_recU W M₂ b n h := hlt
      _ = aa_recU W M₁ b n h := hdet

omit [Fintype S] in
/-- Miao, p. 706: risk aversion as printed is never satisfied: taking `c = b` gives
`U²_t(b) = U²_t(b)` but not `U¹_t(b) > U¹_t(b)`. -/
theorem aa_riskAverse_never (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    {B : Set (List S → (S → ℝ) → ℝ)} (hB : B.Nonempty) : ¬ aa_RiskAverse W M₁ B := by
  intro h
  obtain ⟨M₂, hM₂⟩ := hB
  have := h M₂ hM₂ 0 [] (fun _ => 0) (fun _ => 0) (fun _ _ _ => rfl) rfl
  exact lt_irrefl _ this

/-- Risk aversion with the comparison restricted to random plans `c`. -/
def aa_RiskAverse' (W : ℝ → ℝ → ℝ) (M₁ : List S → (S → ℝ) → ℝ)
    (B : Set (List S → (S → ℝ) → ℝ)) : Prop :=
  ∀ M₂ ∈ B, ∀ n h (b c : List S → ℝ), aa_Deterministic b → ¬ aa_Deterministic c →
    aa_recU W M₂ c n h = aa_recU W M₂ b n h → aa_recU W M₁ c n h < aa_recU W M₁ b n h

/-- The risk-neutral certainty equivalent: the expectation under a fair coin. -/
noncomputable def aa_coinE : List Bool → (Bool → ℝ) → ℝ := fun _ x => aa_E (fun _ => 1 / 2) x

/-- **"More risk averse than a risk-neutral `U²`" does not imply risk aversion** (Miao, p. 706),
even with the comparison restricted to random plans: the risk-neutral utility itself
(`W(c, y) = c + y`, `M = E` under a fair coin) is more risk averse than itself, but it is
indifferent between the deterministic plan `0` and the random plan paying `±1` at date 1. -/
theorem aa_moreRiskAverse_not_riskAverse :
    aa_MoreRiskAverse (fun x y => x + y) aa_coinE aa_coinE ∧
      ¬ aa_RiskAverse' (fun x y => x + y) aa_coinE {aa_coinE} := by
  have hD : SS.IsDistribution (fun _ : Bool => (1 / 2 : ℝ)) := ⟨fun _ => by norm_num, by simp⟩
  have hCE : aa_IsCE aa_coinE := fun _ k => aa_E_const hD k
  refine ⟨(proposition_20_3_1 (fun c => fun y y' hy => by simpa using hy) hCE hCE
    (fun _ _ _ hxy => aa_E_mono hD hxy)).2 fun _ _ => le_rfl, fun h => ?_⟩
  let c : List Bool → ℝ := fun g => match g with
    | [s] => if s then 1 else -1
    | _ => 0
  have hc : ¬ aa_Deterministic c := fun hd => by
    have := hd [true] [false] rfl
    simp [c] at this
    norm_num at this
  have heq : aa_recU (fun x y => x + y) aa_coinE c 1 [] =
      aa_recU (fun x y => x + y) aa_coinE (fun _ => 0) 1 [] := by
    simp [aa_recU, aa_coinE, aa_E, c]
  have := h aa_coinE rfl 1 [] (fun _ => 0) c (fun _ _ _ => rfl) hc heq
  rw [heq] at this
  exact lt_irrefl _ this

/-! ### Expected-utility certainty equivalents: Pratt's theorem -/

/-- The certainty-equivalent comparison `u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` for all lotteries on a finite state
space `T` with outcomes in `D`, written without inverses: if `u₁(m₁) = E u₁(x)` and
`u₂(m₂) = E u₂(x)` with `m₁, m₂ ∈ D` then `m₁ ≤ m₂`. -/
def aa_CELe (T : Type*) [Fintype T] (D : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ (p : T → ℝ), SS.IsDistribution p → ∀ x : T → ℝ, (∀ t, x t ∈ D) → ∀ m₁ ∈ D, ∀ m₂ ∈ D,
    u₁ m₁ = aa_E p (fun t => u₁ (x t)) → u₂ m₂ = aa_E p (fun t => u₂ (x t)) → m₁ ≤ m₂

/-- Pratt, the easy direction: if `u₁ = φ ∘ u₂` on `D` with `φ` strictly increasing and concave on
`u₂(D)`, then `u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` (Jensen). -/
theorem aa_pratt_of_concave (T : Type*) [Fintype T] {D : Set ℝ} {u₁ u₂ : ℝ → ℝ}
    (hu₂ : StrictMonoOn u₂ D) {φ : ℝ → ℝ} (hφc : ConcaveOn ℝ (u₂ '' D) φ)
    (hφm : StrictMonoOn φ (u₂ '' D)) (hφ : ∀ x ∈ D, u₁ x = φ (u₂ x)) : aa_CELe T D u₁ u₂ := by
  intro p hp x hx m₁ hm₁ m₂ hm₂ h1 h2
  have hJ := hφc.le_map_sum (t := Finset.univ) (w := p) (p := fun t => u₂ (x t))
    (fun t _ => hp.nonneg t) hp.sum_eq_one (fun t _ => ⟨x t, hx t, rfl⟩)
  simp only [smul_eq_mul] at hJ
  have e1 : aa_E p (fun t => u₁ (x t)) = ∑ t, p t * φ (u₂ (x t)) := by
    unfold aa_E
    exact Finset.sum_congr rfl fun t _ => by dsimp only; rw [hφ _ (hx t)]
  rw [e1, hφ m₁ hm₁] at h1
  have h3 : φ (u₂ m₁) ≤ φ (u₂ m₂) := by
    rw [h1, h2]
    exact hJ
  exact (hu₂.le_iff_le hm₁ hm₂).1 ((hφm.le_iff_le ⟨_, hm₁, rfl⟩ ⟨_, hm₂, rfl⟩).1 h3)

/-- Pratt, the converse: on an interval `D`, with `u₁, u₂` continuous and strictly increasing, if
`u₁⁻¹E u₁ ≤ u₂⁻¹E u₂` for all two-point lotteries, then `u₁ = φ ∘ u₂` with `φ = u₁ ∘ u₂⁻¹`
strictly increasing and concave on `u₂(D)`. -/
theorem aa_concave_of_pratt {D : Set ℝ} (hD : Convex ℝ D) {u₁ u₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn u₁ D) (hc₂ : ContinuousOn u₂ D) (hu₁ : StrictMonoOn u₁ D)
    (hu₂ : StrictMonoOn u₂ D) (hCE : aa_CELe Bool D u₁ u₂) :
    ∃ φ : ℝ → ℝ, ConcaveOn ℝ (u₂ '' D) φ ∧ StrictMonoOn φ (u₂ '' D) ∧ ∀ x ∈ D, u₁ x = φ (u₂ x) := by
  classical
  set φ : ℝ → ℝ := fun t => u₁ (Function.invFunOn u₂ D t) with hφdef
  have hinj := hu₂.injOn
  have hleft : ∀ x ∈ D, Function.invFunOn u₂ D (u₂ x) = x := fun x hx =>
    hinj.leftInvOn_invFunOn hx
  have hφ : ∀ x ∈ D, u₁ x = φ (u₂ x) := fun x hx => by rw [hφdef]; dsimp only; rw [hleft x hx]
  have hconv : ∀ {u : ℝ → ℝ}, ContinuousOn u D → Convex ℝ (u '' D) := fun hc =>
    ((hD.isPreconnected.image _ hc).ordConnected).convex
  refine ⟨φ, ⟨hconv hc₂, ?_⟩, ?_, hφ⟩
  · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ a b ha hb hab
    obtain ⟨m, hm, hme⟩ := hconv hc₂ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ ha hb hab
    obtain ⟨m₁, hm₁, hme₁⟩ := hconv hc₁ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, rfl⟩ ha hb hab
    set p : Bool → ℝ := fun t => if t then a else b with hp
    set x : Bool → ℝ := fun t => if t then x₁ else x₂ with hx
    have hpD : SS.IsDistribution p :=
      ⟨fun t => by cases t <;> simp [hp, ha, hb], by simp [hp, hab]⟩
    have hle := hCE p hpD x (fun t => by cases t <;> simp [hx, hx₁, hx₂]) m₁ hm₁ m hm
      (by rw [hme₁]; simp [aa_E, hp, hx, smul_eq_mul])
      (by rw [hme]; simp [aa_E, hp, hx, smul_eq_mul])
    rw [← hme, ← hφ m hm, ← hφ x₁ hx₁, ← hφ x₂ hx₂]
    have := hu₁.monotoneOn hm₁ hm hle
    rw [hme₁] at this
    exact this
  · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hlt
    rw [← hφ x₁ hx₁, ← hφ x₂ hx₂]
    exact hu₁ hx₁ hx₂ ((hu₂.lt_iff_lt hx₁ hx₂).1 hlt)

/-- **Proposition 20.3.1** (Miao, p. 706), second part, for the certainty equivalents `u_i⁻¹E u_i`
on an interval `D` with continuous strictly increasing `u_i`: the comparison `M¹ ≤ M²` holds for all
lotteries iff `u₁ = φ ∘ u₂` with `φ` increasing and concave. -/
theorem proposition_20_3_1_pratt {D : Set ℝ} (hD : Convex ℝ D) {u₁ u₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn u₁ D) (hc₂ : ContinuousOn u₂ D) (hu₁ : StrictMonoOn u₁ D)
    (hu₂ : StrictMonoOn u₂ D) :
    (∀ (T : Type) [Fintype T], aa_CELe T D u₁ u₂) ↔
      ∃ φ : ℝ → ℝ, ConcaveOn ℝ (u₂ '' D) φ ∧ StrictMonoOn φ (u₂ '' D) ∧
        ∀ x ∈ D, u₁ x = φ (u₂ x) :=
  ⟨fun h => aa_concave_of_pratt hD hc₁ hc₂ hu₁ hu₂ (h Bool),
    fun ⟨_, hφc, hφm, hφ⟩ T _ => aa_pratt_of_concave T hu₂ hφc hφm hφ⟩

/-- The expected-utility conditional certainty equivalent `M_h(x) = u⁻¹(E_{p h} u(x))` for an order
isomorphism `u` of `ℝ`. -/
noncomputable def aa_euCE (u : ℝ ≃o ℝ) (p : List S → S → ℝ) : List S → (S → ℝ) → ℝ :=
  fun h x => u.symm (aa_E (p h) fun s => u (x s))

theorem aa_euCE_isCE (u : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) :
    aa_IsCE (aa_euCE u p) := fun h k => by
  simp [aa_euCE, aa_E_const (hp h)]

theorem aa_euCE_mono (u : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h))
    (h : List S) : Monotone (aa_euCE u p h) := fun _ _ hxy =>
  u.symm.monotone (aa_E_mono (hp h) fun s => u.monotone (hxy s))

/-- **Proposition 20.3.1** (Miao, p. 706), the Epstein–Zin case: with a common aggregator strictly
increasing in `y` and expected-utility certainty equivalents `u_i⁻¹E_t u_i` (`u_i` order
isomorphisms of `ℝ`), if `u₁ = φ ∘ u₂` with `φ` increasing and concave then `U¹` is more risk averse
than `U²`. -/
theorem proposition_20_3_1_ez [Nonempty S] {W : ℝ → ℝ → ℝ} (hW : ∀ c, StrictMono (W c))
    (u₁ u₂ : ℝ ≃o ℝ) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) {φ : ℝ → ℝ}
    (hφc : ConcaveOn ℝ Set.univ φ) (hφm : StrictMono φ) (hφ : ∀ x, u₁ x = φ (u₂ x)) :
    aa_MoreRiskAverse W (aa_euCE u₁ p) (aa_euCE u₂ p) := by
  rw [proposition_20_3_1 hW (aa_euCE_isCE u₁ hp) (aa_euCE_isCE u₂ hp) (aa_euCE_mono u₁ hp)]
  intro h x
  have himg : (u₂ : ℝ → ℝ) '' Set.univ = Set.univ := Set.image_univ_of_surjective u₂.surjective
  refine aa_pratt_of_concave S (D := Set.univ) (u₂.strictMono.strictMonoOn _)
    (by rw [himg]; exact hφc) (by rw [himg]; exact hφm.strictMonoOn _) (fun x _ => hφ x)
    (p h) (hp h) x (fun _ => trivial) _ trivial _ trivial ?_ ?_
  · simp [aa_euCE]
  · simp [aa_euCE]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Utility gradients and pricing kernels

Miao, §20.3.3, pp. 706–709, on the finite event tree with horizon `N` (`aa_recU`, `U_N = c_N`).
Plans are `c : List S → ℝ`, `p h` is the one-step-ahead distribution at the node `h`, and
`E[∑_t π_t x_t] = ∑_{t ≤ N} E_t-step[π x]` is computed with `aa_Ex`.

* **Definition 20.3.1**: gradient densities (`aa_IsGradientDensity`).
* **Definition 20.3.2**: the derivative `κ` of a conditional certainty equivalent. As printed
  (`aa_CEDerivPrinted`) the condition `E h² < δ ⇒ |M(z + h) − M(z) − E[κh]| < ε` only says that `M`
  is continuous: for `M = E` both `κ = 1` and `κ = 0` satisfy it (`aa_CEDerivPrinted_not_unique`).
  The intended notion is Fréchet differentiability, `|M(z + h) − M(z) − E[κh]| = o(‖h‖)`
  (`aa_HasCEDeriv`), for which `κ = 1` is the derivative of `E` and `κ = 0` is not
  (`aa_HasCEDeriv_expectation`, `aa_not_HasCEDeriv_expectation_zero`). For `M = u⁻¹E u`,
  `κ(x) = u'(x)/u'(M(x))` (`aa_euCE_hasCEDeriv`; the book's `u'(v_t(x_{t+1}))` is
`u'(M_t(x_{t+1}))`).
* **Proposition 20.3.2**: the recursion `φ'_t(0) = W₁(t)x_t + W₂(t)E_t[κ_{t+1}φ'_{t+1}(0)]`
  (`aa_gradV_hasDerivAt`) and the gradient density `π = ℰλ`,
  `ℰ_t = ∏_{s ≤ t} W₂(s − 1)κ_s`, `λ_t = W₁(t)` (`proposition_20_3_2`,
  `proposition_20_3_2_gradient`). With a finite horizon the transversality condition
  `E[π_t x_t] → 0` is not needed; `λ_N = 1` since `U_N = c_N`.
* The pricing kernel `π_{t+1}/π_t = (λ_{t+1}/λ_t)W₂(t)κ_{t+1}` (`aa_pricingKernel`).
* The marginal value of wealth (p. 708): the envelope argument `J'(w₀) = μ` with
  `W₁(c₀, M₀) = λ₀ = μ` (`aa_marginal_value_wealth`, `aa_lambda0_eq_mu`).
* Utility supergradients (p. 709) (`aa_IsSupergradient`).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-- **Definition 20.3.1** (Miao, p. 707): `π` is a gradient density of `U₀` at `c` if
`lim_{α↓0} (U₀(c + αx) − U₀(c))/α = E[∑_{t ≤ N} π_t x_t]` for every direction `x`. -/
def aa_IsGradientDensity (U₀ : (List S → ℝ) → ℝ) (p : List S → S → ℝ) (N : ℕ)
    (c π : List S → ℝ) : Prop :=
  ∀ x : List S → ℝ, Tendsto (fun α => (U₀ (c + α • x) - U₀ c) / α) (𝓝[>] 0)
    (𝓝 (∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => π h * x h) []))

/-- Utility supergradients (Miao, p. 709): `U₀(c') ≤ U₀(c) + E[∑_t π_t(c'_t − c_t)]` for all `c'`.
-/
def aa_IsSupergradient (U₀ : (List S → ℝ) → ℝ) (p : List S → S → ℝ) (N : ℕ)
    (c π : List S → ℝ) : Prop :=
  ∀ c' : List S → ℝ,
    U₀ c' ≤ U₀ c + ∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => π h * (c' h - c h)) []

/-- **Definition 20.3.2** as printed (Miao, p. 707): for every `ε > 0` there is `δ > 0` with
`E[h²] < δ ⇒ |M(z + h) − M(z) − E[κh]| < ε`. -/
def aa_CEDerivPrinted (M : (S → ℝ) → ℝ) (p κ z : S → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ v : S → ℝ, aa_E p (fun s => v s ^ 2) < δ →
    |M (z + v) - M z - aa_E p (fun s => κ s * v s)| < ε

/-- **Definition 20.3.2**, corrected: `κ` is the derivative of the certainty equivalent `M` at `z`
if `M` is Fréchet differentiable at `z` with derivative `h ↦ E[κh]`. -/
def aa_HasCEDeriv (M : (S → ℝ) → ℝ) (p κ z : S → ℝ) : Prop :=
  HasFDerivAt M (∑ s, (p s * κ s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) z

theorem aa_cePrinted_apply (p κ v : S → ℝ) :
    (∑ s, (p s * κ s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) v =
      aa_E p (fun s => κ s * v s) := by
  simp [aa_E, mul_assoc]

/-- The printed Definition 20.3.2 does not determine `κ`: for the expectation `M = E_p`, both
`κ = 1` (the true derivative) and `κ = 0` satisfy it. -/
theorem aa_CEDerivPrinted_not_unique {p : S → ℝ} (hp : SS.IsDistribution p) (z : S → ℝ) :
    aa_CEDerivPrinted (aa_E p) p (fun _ => 1) z ∧ aa_CEDerivPrinted (aa_E p) p (fun _ => 0) z := by
  constructor
  · intro ε hε
    refine ⟨1, one_pos, fun v _ => ?_⟩
    have : aa_E p (z + v) - aa_E p z - aa_E p (fun s => 1 * v s) = 0 := by
      simp only [one_mul]
      rw [show aa_E p (z + v) = aa_E p (fun s => z s + v s) from rfl, aa_E_add]
      ring
    rw [this, abs_zero]
    exact hε
  · intro ε hε
    refine ⟨ε ^ 2, by positivity, fun v hv => ?_⟩
    have hvar : aa_E p v ^ 2 ≤ aa_E p (fun s => v s ^ 2) := by
      have h0 : 0 ≤ aa_E p (fun s => (v s - aa_E p v) ^ 2) :=
        Finset.sum_nonneg fun s _ => mul_nonneg (hp.nonneg s) (sq_nonneg _)
      have e : aa_E p (fun s => (v s - aa_E p v) ^ 2) =
          aa_E p (fun s => v s ^ 2) - aa_E p v ^ 2 := by
        simp only [aa_E, sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h1 : ∑ s, p s * (2 * v s * ∑ s', p s' * v s') = 2 * (∑ s, p s * v s) ^ 2 := by
          calc ∑ s, p s * (2 * v s * ∑ s', p s' * v s') =
              ∑ s, (2 * ∑ s', p s' * v s') * (p s * v s) :=
                Finset.sum_congr rfl fun s _ => by ring
            _ = 2 * (∑ s, p s * v s) ^ 2 := by rw [← Finset.mul_sum]; ring
        have h2 : ∑ s, p s * (∑ s', p s' * v s') ^ 2 = (∑ s, p s * v s) ^ 2 := by
          rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
        rw [h1, h2]
        ring
      linarith
    have : aa_E p (z + v) - aa_E p z - aa_E p (fun s => 0 * v s) = aa_E p v := by
      simp only [zero_mul]
      rw [show aa_E p (z + v) = aa_E p (fun s => z s + v s) from rfl, aa_E_add,
        aa_E_const hp]
      ring
    rw [this]
    exact abs_lt_of_sq_lt_sq' (by linarith) hε.le |>.elim (fun h1 h2 => abs_lt.2 ⟨h1, h2⟩)

/-- The expectation has the corrected derivative `κ = 1`. -/
theorem aa_HasCEDeriv_expectation (p z : S → ℝ) : aa_HasCEDeriv (aa_E p) p (fun _ => 1) z := by
  unfold aa_HasCEDeriv
  have h : HasFDerivAt (fun x : S → ℝ => ∑ s, p s * x s)
      (∑ s, p s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) z :=
    HasFDerivAt.fun_sum fun s _ => (hasFDerivAt_apply s z).const_mul (p s)
  have e : aa_E p = fun x : S → ℝ => ∑ s, p s * x s := rfl
  rw [e]
  simpa using h

/-- With the corrected Definition 20.3.2, `κ = 0` is not the derivative of `E_p`. -/
theorem aa_not_HasCEDeriv_expectation_zero {p : S → ℝ} (hp : SS.IsDistribution p) (z : S → ℝ) :
    ¬ aa_HasCEDeriv (aa_E p) p (fun _ => 0) z := by
  intro h
  have h1 := (aa_HasCEDeriv_expectation p z).unique h
  have := congrArg (fun L : (S → ℝ) →L[ℝ] ℝ => L fun _ => 1) h1
  simp only [aa_cePrinted_apply] at this
  rw [aa_E_const hp, aa_E_const hp] at this
  norm_num at this

/-- Miao, p. 707: for `M(x) = u⁻¹(E u(x))` with `u` an order isomorphism of `ℝ` differentiable with
`u' ≠ 0` at `M(x)`, the derivative of the certainty equivalent is `κ(x) = u'(x)/u'(M(x))`. -/
theorem aa_euCE_hasCEDeriv (u : ℝ ≃o ℝ) (u' : ℝ → ℝ) (hu : ∀ y, HasDerivAt u (u' y) y)
    (p x : S → ℝ) (hM : u' (u.symm (aa_E p fun s => u (x s))) ≠ 0) :
    aa_HasCEDeriv (fun y => u.symm (aa_E p fun s => u (y s))) p
      (fun s => u' (x s) / u' (u.symm (aa_E p fun s => u (x s)))) x := by
  set a := aa_E p fun s => u (x s) with ha
  have hinv : HasDerivAt u.symm (u' (u.symm a))⁻¹ a :=
    HasDerivAt.of_local_left_inverse u.symm.continuous.continuousAt (hu _) hM
      (Eventually.of_forall fun y => u.apply_symm_apply y)
  have hin : HasFDerivAt (fun y : S → ℝ => aa_E p fun s => u (y s))
      (∑ s, p s • (u' (x s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x :=
    HasFDerivAt.fun_sum fun s _ =>
      ((hu (x s)).hasFDerivAt.comp x (hasFDerivAt_apply s x)).const_mul (p s) |>.congr_fderiv
        (by ext v; simp [mul_comm])
  have hcomp := hinv.hasFDerivAt.comp x hin
  have hL : (ContinuousLinearMap.toSpanSingleton ℝ (u' (u.symm a))⁻¹).comp
      (∑ s, p s • (u' (x s) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) =
      ∑ s, (p s * (u' (x s) / u' (u.symm a))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, map_sum,
      ContinuousLinearMap.toSpanSingleton_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
  exact hcomp.congr_fderiv hL

/-! ### Proposition 20.3.2 -/

/-- The derivative recursion of Proposition 20.3.2:
`V_{n+1}(h) = W₁(h)x(h) + W₂(h)E_h[κ_h V_n]`, `V_0(h) = x(h)`. -/
def aa_gradV (W₁ W₂ : List S → ℝ) (p κ : List S → S → ℝ) (x : List S → ℝ) : ℕ → List S → ℝ
  | 0, h => x h
  | n + 1, h => W₁ h * x h + W₂ h * ∑ s, p h s * κ h s * aa_gradV W₁ W₂ p κ x n (s :: h)

/-- The differentiability hypotheses of Proposition 20.3.2 along the plan `c`, horizon `N`: at
every non-terminal node `h`, `W` has partial derivatives `W₁(h), W₂(h)` at
`(c_h, M_h(U_{h+1}))` and `M_h` has derivative `κ_h` at `U_{h+1}`. -/
def aa_GradHyp (W : ℝ → ℝ → ℝ) (M : List S → (S → ℝ) → ℝ) (p : List S → S → ℝ) (c : List S → ℝ)
    (N : ℕ) (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) : Prop :=
  ∀ h : List S, h.length < N →
    HasFDerivAt (fun z : ℝ × ℝ => W z.1 z.2)
      (W₁ h • ContinuousLinearMap.fst ℝ ℝ ℝ + W₂ h • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c h, M h fun s => aa_recU W M c (N - h.length - 1) (s :: h)) ∧
    aa_HasCEDeriv (M h) (p h) (κ h) fun s => aa_recU W M c (N - h.length - 1) (s :: h)

/-- **Proposition 20.3.2, the recursion** (Miao, p. 708): with `φ_t(α) = U_t(c + αx)`,
`φ'_t(0) = W₁(t)x_t + W₂(t)E_t[κ_{t+1}φ'_{t+1}(0)]`, at every node `h` with `|h| + k = N`. -/
theorem aa_gradV_hasDerivAt {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ} {p : List S → S → ℝ}
    {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) (x : List S → ℝ) :
    ∀ k h, h.length + k = N →
      HasDerivAt (fun α : ℝ => aa_recU W M (c + α • x) k h) (aa_gradV W₁ W₂ p κ x k h) 0 := by
  intro k
  induction k with
  | zero =>
    intro h _
    simp only [aa_recU, aa_gradV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x h)).const_add (c h)
  | succ k ih =>
    intro h hlen
    have hlt : h.length < N := by omega
    have hidx : N - h.length - 1 = k := by omega
    obtain ⟨hW, hM⟩ := hyp h hlt
    rw [hidx] at hW hM
    have hchild : HasDerivAt (fun α : ℝ => fun s => aa_recU W M (c + α • x) k (s :: h))
        (fun s => aa_gradV W₁ W₂ p κ x k (s :: h)) 0 :=
      hasDerivAt_pi.2 fun s => ih (s :: h) (by simp only [List.length_cons]; omega)
    have h0 : (fun s => aa_recU W M (c + (0 : ℝ) • x) k (s :: h)) =
        fun s => aa_recU W M c k (s :: h) := by simp
    have hMc := HasFDerivAt.comp_hasDerivAt_of_eq 0 hM hchild h0.symm
    have hc0 : HasDerivAt (fun α : ℝ => (c + α • x) h) (x h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x h)).const_add (c h)
    have hpair := hc0.prodMk hMc
    have hpt : ((c + (0 : ℝ) • x) h,
        (M h ∘ fun α : ℝ => fun s => aa_recU W M (c + α • x) k (s :: h)) 0) =
        (c h, M h fun s => aa_recU W M c k (s :: h)) := by simp
    have hall := HasFDerivAt.comp_hasDerivAt_of_eq 0 hW hpair hpt.symm
    simp only [aa_recU, aa_gradV]
    convert hall using 1
    · rfl
    · simp [mul_assoc]

/-- `t`-step expectations from `h` only see nodes of length `|h| + t`. -/
theorem aa_Ex_congr (q : List S → S → ℝ) {f g : List S → ℝ} :
    ∀ t h, (∀ h', h'.length = h.length + t → f h' = g h') → aa_Ex q t f h = aa_Ex q t g h
  | 0, h, hfg => hfg h (by simp)
  | t + 1, h, hfg => by
    simp only [aa_Ex]
    exact Finset.sum_congr rfl fun s _ => by
      rw [aa_Ex_congr q t (s :: h) fun h' hh' => hfg h' (by simp at hh'; omega)]

/-- The gradient density `π = ℰλ` of Proposition 20.3.2: `ℰ_t = ∏ W₂κ` along the path and
`λ_t = W₁(t)` (`λ_N = 1`, since `U_N = c_N`). -/
def aa_gradπ (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) (N : ℕ) (h : List S) : ℝ :=
  aa_M (fun h' s => W₂ h' * κ h' s) h * if h.length < N then W₁ h else 1

/-- **Proposition 20.3.2** (Miao, p. 708). Under the differentiability hypotheses, the derivative of
`α ↦ U₀(c + αx)` at `0` is `E[∑_{t ≤ N} π_t x_t]` with `π = ℰλ` (`aa_gradπ`). -/
theorem proposition_20_3_2 {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ} {p : List S → S → ℝ}
    {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) (x : List S → ℝ) :
    HasDerivAt (fun α : ℝ => aa_recU W M (c + α • x) N [])
      (∑ t ∈ Finset.range (N + 1), aa_Ex p t (fun h => aa_gradπ W₁ W₂ κ N h * x h) []) 0 := by
  have hd := aa_gradV_hasDerivAt hyp x N [] (by simp)
  convert hd using 1
  set m : List S → S → ℝ := fun h' s => W₂ h' * κ h' s with hm
  have hun := aa_linear_unroll (aa_distort p m) 1 (fun h => W₁ h * x h) x
    (aa_gradV W₁ W₂ p κ x) (fun _ => rfl) (fun n h => by
      simp only [aa_gradV, aa_distort, hm, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring) N []
  rw [hun, Finset.sum_range_succ]
  simp only [one_pow, one_mul]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have := aa_Ex_change p m (fun h => W₁ h * x h) t []
    rw [aa_M, one_mul] at this
    rw [this]
    refine aa_Ex_congr p t [] fun h' hh' => ?_
    have : h'.length < N := by simp at hh' ht; omega
    simp only [aa_gradπ, this, ↓reduceIte, hm]
    ring
  · have := aa_Ex_change p m x N []
    rw [aa_M, one_mul] at this
    rw [this]
    refine aa_Ex_congr p N [] fun h' hh' => ?_
    have : ¬ h'.length < N := by simp at hh'; omega
    simp only [aa_gradπ, this, ↓reduceIte, hm, mul_one]

/-- **Proposition 20.3.2** in the form of Definition 20.3.1: `π = ℰλ` is the utility gradient
density of `U₀` at `c`. -/
theorem proposition_20_3_2_gradient {W : ℝ → ℝ → ℝ} {M : List S → (S → ℝ) → ℝ}
    {p : List S → S → ℝ} {c : List S → ℝ} {N : ℕ} {W₁ W₂ : List S → ℝ} {κ : List S → S → ℝ}
    (hyp : aa_GradHyp W M p c N W₁ W₂ κ) :
    aa_IsGradientDensity (fun c' => aa_recU W M c' N []) p N c (aa_gradπ W₁ W₂ κ N) := by
  intro x
  have h := hasDerivAt_iff_tendsto_slope_zero.1 (proposition_20_3_2 hyp x)
  have h2 := h.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
  refine h2.congr fun α => ?_
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  ring

omit [Fintype S] in
/-- The pricing kernel (Miao, p. 709): `π_{t+1}/π_t = (λ_{t+1}/λ_t)W₂(t)κ_{t+1}`. -/
theorem aa_pricingKernel (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) (N : ℕ) (h : List S) (s : S)
    (hlen : h.length + 1 < N) (hM : aa_M (fun h' s => W₂ h' * κ h' s) h ≠ 0) (hlam : W₁ h ≠ 0) :
    aa_gradπ W₁ W₂ κ N (s :: h) / aa_gradπ W₁ W₂ κ N h =
      W₁ (s :: h) / W₁ h * W₂ h * κ h s := by
  have h1 : h.length < N := by omega
  have h2 : (s :: h).length < N := by simpa using hlen
  simp only [aa_gradπ, h1, h2, ↓reduceIte, aa_M]
  field_simp

/-- The marginal value of wealth (Miao, p. 708). If `c*(w)` solves
`max U₀(c)` s.t. `E[∑ p_t c_t] ≤ w` near `w₀` with a binding budget, `U₀` has derivative `L` at
`c*(w₀)` with the first-order condition `L = μB` (`B` the budget functional), and `c*` is
differentiable at `w₀`, then `J(w) = U₀(c*(w))` has `J'(w₀) = μ`. -/
theorem aa_marginal_value_wealth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → ℝ} {L B : E →L[ℝ] ℝ} {cstar : ℝ → E} {v : E} {w₀ μ : ℝ}
    (hU : HasFDerivAt U L (cstar w₀)) (hc : HasDerivAt cstar v w₀)
    (hbud : ∀ᶠ w in 𝓝 w₀, B (cstar w) = w) (hfoc : L = μ • B) :
    HasDerivAt (fun w => U (cstar w)) μ w₀ := by
  have h1 : HasDerivAt (fun w => B (cstar w)) (B v) w₀ := B.hasFDerivAt.comp_hasDerivAt w₀ hc
  have h2 : HasDerivAt (fun w => B (cstar w)) 1 w₀ :=
    (hasDerivAt_id w₀).congr_of_eventuallyEq hbud
  have hBv : B v = 1 := h1.unique h2
  have := hU.comp_hasDerivAt w₀ hc
  rw [hfoc] at this
  simpa [hBv, Function.comp_def] using this

omit [Fintype S] in
/-- Miao, p. 709: `λ₀ = W₁(c₀, M₀(U₁(c)))`: the gradient density at the root is `λ₀`, so the
first-order condition `π = μ p` with state-price density `p₀ = 1` gives `λ₀ = μ = J'(w₀)`. -/
theorem aa_lambda0_eq_mu (W₁ W₂ : List S → ℝ) (κ : List S → S → ℝ) {N : ℕ} (hN : 0 < N)
    (price : List S → ℝ) (μ : ℝ) (hfoc : ∀ h, aa_gradπ W₁ W₂ κ N h = μ * price h)
    (hp0 : price [] = 1) : W₁ [] = μ := by
  have := hfoc []
  simp only [aa_gradπ, aa_M, List.length_nil, hN, ↓reduceIte, one_mul, hp0, mul_one] at this
  exact this

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pricing kernels: Examples 20.3.1–20.3.3 and Exercise 20.2

Miao, §20.3.3, pp. 709–710, and Exercise 20.2 (p. 735).

* **Example 20.3.1** (Epstein–Zin): the partial derivatives of the CES aggregator
  `W₁ = (1 − β)c^{−ρ}W^ρ`, `W₂ = βy^{−ρ}W^ρ` (`aa_W_hasFDerivAt`), the derivative of the
  Kreps–Porteus certainty equivalent `κ_s = (x_s/M)^{−γ}` (`aa_KP_hasCEDeriv`), the algebra of
  (20.20) (`eq_20_20`), and on the event tree: the hypotheses of Proposition 20.3.2 hold and the
  pricing kernel is `β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M_t(U_{t+1}))^{ρ−γ}` (`example_20_3_1`); for
  `γ > ρ` it is decreasing in the continuation value (`aa_ez_kernel_antitone`).
* **Example 20.3.2** (generalized smooth ambiguity): the derivative of (20.15) with respect to the
  joint measure `μ(z)π_z(s)`, `κ_{z,s} = (x_s/M)^{−γ}(Y_z/M)^{−(η−γ)}`,
  `Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}` (`aa_ju_hasFDerivAt`), and the kernel
  `M_{z,t+1} = β(c'/c)^{−ρ}(U'/M)^{ρ−γ}(Y_z/M)^{−(η−γ)}` (`example_20_3_2`), decreasing in `Y_z`
  for `η > γ` (`aa_smooth_kernel_antitone`).
* **Example 20.3.3** (recursive multiple priors): for concave `u` with supergradient `u'` and any
  selection of minimising priors `q*`, `π_t = β^t u'(c_t)M*_t` with `M*` the product of the
  densities `m* = dq*/dp` is a utility supergradient (`example_20_3_3`); such a selection exists for
  finite sets of priors (`example_20_3_3_exists`). The book prints `π_t = u'(c_t)m*_t`: the
  discount factor and the cumulated density are implicit. Not formalised: the reverse inclusion
  (every supergradient is of this form), which the text cites from Epstein and Wang (1994).
* **Exercise 20.2**: Epstein–Zin (`example_20_3_1`), divergence utility — in the multiplier
  (relative entropy) case the aggregator `R = −θ ln E exp(−x/θ)` has derivative `κ = m*`, the
  minimising density (`aa_riskSensitive_hasCEDeriv`, `aa_klDensity_attains`), so the kernel is
  `βu'(c_{t+1})/u'(c_t) · m*_{t+1}` (`ex_20_2_divergence`); for a general divergence the
  minimising density is a supergradient of `R` (`aa_divR_supergradient`) — and generalized smooth
  ambiguity (`example_20_3_2`).
-/

namespace Miao.RecursiveUtility

open Finset Filter Topology

variable {S Z : Type*} [Fintype S] [Fintype Z]

/-! ### Example 20.3.1: Epstein–Zin -/

/-- The partial derivatives of the CES aggregator at `(c, y) ∈ (0, ∞)²`:
`W₁ = (1 − β)c^{−ρ}W^ρ`, `W₂ = βy^{−ρ}W^ρ`. -/
theorem aa_W_hasFDerivAt {β ρ c y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hc : 0 < c)
    (hy : 0 < y) :
    HasFDerivAt (fun z : ℝ × ℝ => aa_W β ρ z.1 z.2)
      (((1 - β) * c ^ (-ρ) * aa_W β ρ c y ^ ρ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (β * y ^ (-ρ) * aa_W β ρ c y ^ ρ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, y) := by
  have hr : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : 0 < 1 - β := by linarith
  set A := (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) with hA
  have hA0 : 0 < A := add_pos (mul_pos hb (Real.rpow_pos_of_pos hc _))
    (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => z.1 ^ (1 - ρ))
      (((1 - ρ) * c ^ (1 - ρ - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (c, y) :=
    (hasFDerivAt_fst (p := (c, y))).rpow_const (Or.inl hc.ne')
  have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.2 ^ (1 - ρ))
      (((1 - ρ) * y ^ (1 - ρ - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, y) :=
    (hasFDerivAt_snd (p := (c, y))).rpow_const (Or.inl hy.ne')
  have hW := ((h1.const_mul (1 - β)).add (h2.const_mul β)).rpow_const (p := (1 - ρ)⁻¹)
    (Or.inl hA0.ne')
  have e1 : A ^ ((1 - ρ)⁻¹ - 1) = aa_W β ρ c y ^ ρ := by
    rw [aa_W, ← hA, ← Real.rpow_mul hA0.le]
    congr 1
    field_simp
    ring
  have e2 : ∀ t : ℝ, 0 < t → t ^ (1 - ρ - 1) = t ^ (-ρ) := fun t _ => by congr 1; ring
  refine hW.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Pi.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [← hA, e1, e2 c hc, e2 y hy]
  field_simp

/-- **Example 20.3.1**, the certainty equivalent: the Kreps–Porteus `M(x) = (E x^{1−γ})^{1/(1−γ)}`
has derivative `κ_s = (x_s/M(x))^{−γ}` at a positive `x`. -/
theorem aa_KP_hasCEDeriv [Nonempty S] {γ : ℝ} (hγ : γ ≠ 1) {p : S → ℝ}
    (hp : SS.IsDistribution p) {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    aa_HasCEDeriv (aa_KP γ p) p (fun s => (x s / aa_KP γ p x) ^ (-γ)) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  set B := aa_E p fun s => x s ^ (1 - γ) with hB
  have hB0 : 0 < B := aa_E_pos hp fun s => Real.rpow_pos_of_pos (hx s) _
  have hin : HasFDerivAt (fun y : S → ℝ => aa_E p fun s => y s ^ (1 - γ))
      (∑ s, p s • (((1 - γ) * x s ^ (1 - γ - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x :=
    HasFDerivAt.fun_sum fun s _ =>
      ((hasFDerivAt_apply s x).rpow_const (Or.inl (hx s).ne')).const_mul (p s)
  have hW := hin.rpow_const (p := (1 - γ)⁻¹) (Or.inl hB0.ne')
  have hK : aa_KP γ p x = B ^ (1 - γ)⁻¹ := rfl
  have hK0 : 0 < aa_KP γ p x := aa_KP_pos γ hp hx
  unfold aa_HasCEDeriv
  refine hW.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.div_rpow (hx s).le hK0.le, Real.rpow_neg hK0.le, hK, ← Real.rpow_mul hB0.le,
    show 1 - γ - 1 = -γ by ring]
  have e : B ^ ((1 - γ)⁻¹ - 1) = B ^ ((1 - γ)⁻¹ * γ) := by congr 1; field_simp; ring
  rw [e]
  have h1 := Real.rpow_pos_of_pos hB0 ((1 - γ)⁻¹ * γ)
  field_simp

/-- **(20.20)** (Miao, p. 709), the algebra: with `λ_t = (1 − β)c_t^{−ρ}U_t^ρ`,
`W₂ = βM^{−ρ}U_t^ρ` and `κ = (U_{t+1}/M)^{−γ}`,
`(λ_{t+1}/λ_t)W₂κ = β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M)^{ρ−γ}`. -/
theorem eq_20_20 {β ρ γ c c' U U' M : ℝ} (hβ1 : β < 1) (hc : 0 < c) (hc' : 0 < c') (hU : 0 < U)
    (hU' : 0 < U') (hM : 0 < M) :
    (1 - β) * c' ^ (-ρ) * U' ^ ρ / ((1 - β) * c ^ (-ρ) * U ^ ρ) * (β * M ^ (-ρ) * U ^ ρ) *
        (U' / M) ^ (-γ) = β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ) := by
  have hb : 1 - β ≠ 0 := by linarith
  rw [Real.rpow_sub (div_pos hU' hM)]
  simp only [Real.div_rpow hc'.le hc.le, Real.div_rpow hU'.le hM.le, Real.rpow_neg hM.le,
    Real.rpow_neg hU'.le, Real.rpow_neg hc.le, Real.rpow_neg hc'.le]
  have h1 := Real.rpow_pos_of_pos hc ρ
  have h1' := Real.rpow_pos_of_pos hc' ρ
  have h2 := Real.rpow_pos_of_pos hU ρ
  have h3 := Real.rpow_pos_of_pos hM ρ
  have h4 := Real.rpow_pos_of_pos hM γ
  have h5 := Real.rpow_pos_of_pos hU' γ
  have h6 := Real.rpow_pos_of_pos hU' ρ
  field_simp

/-- The Epstein–Zin certainty equivalent at the node `h` of the horizon-`N` tree. -/
noncomputable def aa_ezMh (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  aa_KP γ (p h) fun s => aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h)

/-- `λ_t = W₁(c_t, M_t)` for Epstein–Zin. -/
noncomputable def aa_ezW₁ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  (1 - β) * c h ^ (-ρ) * aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) ^ ρ

/-- `W₂(c_t, M_t)` for Epstein–Zin. -/
noncomputable def aa_ezW₂ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) : ℝ :=
  β * aa_ezMh β ρ γ p c N h ^ (-ρ) * aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) ^ ρ

/-- `κ_{t+1} = (U_{t+1}/M_t)^{−γ}` for Epstein–Zin. -/
noncomputable def aa_ezκ (β ρ γ : ℝ) (p : List S → S → ℝ) (c : List S → ℝ) (N : ℕ)
    (h : List S) (s : S) : ℝ :=
  (aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) /
    aa_ezMh β ρ γ p c N h) ^ (-γ)

omit [Fintype S] in
theorem aa_M_pos {m : List S → S → ℝ} (hm : ∀ h s, 0 < m h s) : ∀ h, 0 < aa_M m h
  | [] => one_pos
  | s :: h => mul_pos (hm h s) (aa_M_pos hm h)

/-- **Example 20.3.1** (Miao, p. 709). For the finite-horizon Epstein–Zin utility (20.3) and a
positive plan, the hypotheses of Proposition 20.3.2 hold with `W₁, W₂, κ` as above, so
`π = ℰλ` is the utility gradient, and the pricing kernel is (20.20):
`π_{t+1}/π_t = β(c_{t+1}/c_t)^{−ρ}(U_{t+1}/M_t(U_{t+1}))^{ρ−γ}`. -/
theorem example_20_3_1 [Nonempty S] {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1)
    (hγ : γ ≠ 1) {p : List S → S → ℝ} (hp : ∀ h, SS.IsDistribution (p h)) {c : List S → ℝ}
    (hc : ∀ h, 0 < c h) (N : ℕ) :
    aa_GradHyp (aa_W β ρ) (fun h => aa_KP γ (p h)) p c N (aa_ezW₁ β ρ γ p c N)
        (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) ∧
      ∀ (h : List S) (s : S), h.length + 1 < N →
        aa_gradπ (aa_ezW₁ β ρ γ p c N) (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) N (s :: h) /
            aa_gradπ (aa_ezW₁ β ρ γ p c N) (aa_ezW₂ β ρ γ p c N) (aa_ezκ β ρ γ p c N) N h =
          β * (c (s :: h) / c h) ^ (-ρ) *
            (aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) /
              aa_ezMh β ρ γ p c N h) ^ (ρ - γ) := by
  have hU : ∀ n h, 0 < aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c n h := fun n h => by
    rw [← aa_ezU_eq_recU]; exact aa_ezU_pos hβ0 hβ1 hp hc n h
  have hMh : ∀ h, 0 < aa_ezMh β ρ γ p c N h := fun h => aa_KP_pos γ (hp h) fun s => hU _ _
  have hWp : ∀ h, 0 < aa_W β ρ (c h) (aa_ezMh β ρ γ p c N h) := fun h =>
    aa_W_pos hβ0 hβ1 (hc h) (hMh h)
  refine ⟨fun h _ => ⟨aa_W_hasFDerivAt hβ0 hβ1 hρ (hc h) (hMh h),
    aa_KP_hasCEDeriv hγ (hp h) fun s => hU _ _⟩, fun h s hlen => ?_⟩
  have hW₁ : ∀ h, 0 < aa_ezW₁ β ρ γ p c N h := fun h =>
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (hc h) _))
      (Real.rpow_pos_of_pos (hWp h) _)
  have hm : ∀ h s, 0 < aa_ezW₂ β ρ γ p c N h * aa_ezκ β ρ γ p c N h s := fun h s =>
    mul_pos (mul_pos (mul_pos hβ0 (Real.rpow_pos_of_pos (hMh h) _))
      (Real.rpow_pos_of_pos (hWp h) _)) (Real.rpow_pos_of_pos (div_pos (hU _ _) (hMh h)) _)
  rw [aa_pricingKernel _ _ _ N h s hlen (aa_M_pos hm h).ne' (hW₁ h).ne']
  -- the child's utility is `W(c', M(s :: h))`
  have hchild : aa_recU (aa_W β ρ) (fun h => aa_KP γ (p h)) c (N - h.length - 1) (s :: h) =
      aa_W β ρ (c (s :: h)) (aa_ezMh β ρ γ p c N (s :: h)) := by
    obtain ⟨k, hk⟩ : ∃ k, N - h.length - 1 = k + 1 := ⟨N - h.length - 2, by omega⟩
    have hk2 : N - (s :: h).length - 1 = k := by simp only [List.length_cons]; omega
    rw [hk, aa_recU, aa_ezMh, hk2]
  unfold aa_ezW₁ aa_ezW₂ aa_ezκ
  rw [hchild, eq_20_20 hβ1 (hc h) (hc _) (hWp h) (hWp _) (hMh h)]

/-- Miao, pp. 709–710: when `γ > ρ` (preference for earlier resolution) the Epstein–Zin pricing
kernel puts more weight on low continuation values: it is strictly decreasing in `U_{t+1}`. -/
theorem aa_ez_kernel_antitone {β ρ γ c c' M : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc' : 0 < c')
    (hM : 0 < M) (hργ : ρ < γ) :
    StrictAntiOn (fun U' => β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have h1 : (y / M) ^ (ρ - γ) < (x / M) ^ (ρ - γ) :=
    Real.rpow_lt_rpow_of_neg (div_pos hx' hM) (div_lt_div_of_pos_right hxy hM) (by linarith)
  have h2 : 0 < β * (c' / c) ^ (-ρ) := mul_pos hβ (Real.rpow_pos_of_pos (div_pos hc' hc) _)
  exact mul_lt_mul_of_pos_left h1 h2

/-! ### Example 20.3.2: generalized smooth ambiguity -/

/-- **Example 20.3.2**, the certainty equivalent (Miao, p. 710): the derivative of (20.15) at a
positive `x` is `h ↦ ∑_{z,s} μ(z)π_z(s)κ_{z,s}h_s` with
`κ_{z,s} = (x_s/M)^{−γ}(Y_z/M)^{−(η−γ)}`, `Y_z = (E_{π_z} x^{1−γ})^{1/(1−γ)}`. -/
theorem aa_ju_hasFDerivAt [Nonempty S] [Nonempty Z] {γ η : ℝ} (hγ : γ ≠ 1) (hη : η ≠ 1)
    {μ : Z → ℝ} (hμ : SS.IsDistribution μ) {π : Z → S → ℝ} (hπ : ∀ z, SS.IsDistribution (π z))
    {x : S → ℝ} (hx : ∀ s, 0 < x s) :
    HasFDerivAt (aa_ju γ η μ π)
      (∑ s, (∑ z, μ z * π z s * ((x s / aa_ju γ η μ π x) ^ (-γ) *
          (aa_KP γ (π z) x / aa_ju γ η μ π x) ^ (-(η - γ)))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) x := by
  have hg : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have he : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  set a := (1 - η) / (1 - γ) with ha
  set A : Z → ℝ := fun z => aa_E (π z) fun s => x s ^ (1 - γ) with hA
  have hA0 : ∀ z, 0 < A z := fun z => aa_E_pos (hπ z) fun s => Real.rpow_pos_of_pos (hx s) _
  set T := ∑ z, μ z * A z ^ a with hT
  have hT0 : 0 < T := aa_E_pos hμ fun z => Real.rpow_pos_of_pos (hA0 z) _
  have hAd : ∀ z, HasFDerivAt (fun y : S → ℝ => aa_E (π z) fun s => y s ^ (1 - γ))
      (∑ s, π z s • (((1 - γ) * x s ^ (1 - γ - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s)) x := fun z =>
    HasFDerivAt.fun_sum fun s _ =>
      ((hasFDerivAt_apply s x).rpow_const (Or.inl (hx s).ne')).const_mul (π z s)
  have hTd := HasFDerivAt.fun_sum (u := Finset.univ) fun z _ =>
    (((hAd z).rpow_const (p := a) (Or.inl (hA0 z).ne')).const_mul (μ z))
  have hMd := hTd.rpow_const (p := (1 - η)⁻¹) (Or.inl hT0.ne')
  have hMx : aa_ju γ η μ π x = T ^ (1 - η)⁻¹ := rfl
  have hM0 : 0 < aa_ju γ η μ π x := by rw [hMx]; exact Real.rpow_pos_of_pos hT0 _
  have hY : ∀ z, aa_KP γ (π z) x = A z ^ (1 - γ)⁻¹ := fun z => rfl
  refine hMd.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  -- the exponent algebra
  have e1 : (x s / aa_ju γ η μ π x) ^ (-γ) = x s ^ (-γ) * aa_ju γ η μ π x ^ γ := by
    rw [Real.div_rpow (hx s).le hM0.le, Real.rpow_neg hM0.le]
    field_simp
  have e2 : (aa_KP γ (π z) x / aa_ju γ η μ π x) ^ (-(η - γ)) =
      A z ^ (a - 1) * aa_ju γ η μ π x ^ (η - γ) := by
    have hY0 : 0 < aa_KP γ (π z) x := aa_KP_pos γ (hπ z) hx
    have hk : (1 - γ)⁻¹ * (η - γ) = -(a - 1) := by rw [ha]; field_simp; ring
    rw [Real.div_rpow hY0.le hM0.le, Real.rpow_neg hY0.le, Real.rpow_neg hM0.le, hY,
      ← Real.rpow_mul (hA0 z).le, hk, Real.rpow_neg (hA0 z).le, inv_inv]
    have := Real.rpow_pos_of_pos hM0 (η - γ)
    field_simp
  have e3 : aa_ju γ η μ π x ^ γ * aa_ju γ η μ π x ^ (η - γ) = T ^ ((1 - η)⁻¹ - 1) := by
    rw [← Real.rpow_add hM0, hMx, ← Real.rpow_mul hT0.le]
    congr 1
    field_simp
    ring
  rw [e1, e2, show 1 - γ - 1 = -γ by ring]
  have hone : (1 - η)⁻¹ * a * (1 - γ) = 1 := by rw [ha]; field_simp
  calc (1 - η)⁻¹ * T ^ ((1 - η)⁻¹ - 1) *
        (μ z * (a * A z ^ (a - 1) * (π z s * ((1 - γ) * x s ^ (-γ) * v s))))
      = ((1 - η)⁻¹ * a * (1 - γ)) * T ^ ((1 - η)⁻¹ - 1) * μ z * π z s * x s ^ (-γ) *
          A z ^ (a - 1) * v s := by ring
    _ = μ z * π z s * (x s ^ (-γ) * aa_ju γ η μ π x ^ γ *
          (A z ^ (a - 1) * aa_ju γ η μ π x ^ (η - γ))) * v s := by
        rw [hone, ← e3]; ring

/-- **Example 20.3.2** (Miao, p. 710), the pricing kernel: with `λ_t = (1 − β)c_t^{−ρ}U_t^ρ`,
`W₂ = βM^{−ρ}U_t^ρ` and `κ_{z,s} = (U'/M)^{−γ}(Y_z/M)^{−(η−γ)}`,
`M_{z,t+1} = β(c'/c)^{−ρ}(U'/M)^{ρ−γ}(Y_z/M)^{−(η−γ)}`. -/
theorem example_20_3_2 {β ρ γ η c c' U U' M Y : ℝ} (hβ1 : β < 1) (hc : 0 < c) (hc' : 0 < c')
    (hU : 0 < U) (hU' : 0 < U') (hM : 0 < M) :
    (1 - β) * c' ^ (-ρ) * U' ^ ρ / ((1 - β) * c ^ (-ρ) * U ^ ρ) * (β * M ^ (-ρ) * U ^ ρ) *
        ((U' / M) ^ (-γ) * (Y / M) ^ (-(η - γ))) =
      β * (c' / c) ^ (-ρ) * (U' / M) ^ (ρ - γ) * (Y / M) ^ (-(η - γ)) := by
  rw [← mul_assoc, eq_20_20 hβ1 hc hc' hU hU' hM]

/-- Miao, p. 710: for `η > γ` (ambiguity aversion) the kernel puts more weight on models `z` with
low certainty-equivalent continuation value `Y_z`. -/
theorem aa_smooth_kernel_antitone {k M γ η : ℝ} (hk : 0 < k) (hM : 0 < M) (hγη : γ < η) :
    StrictAntiOn (fun Y => k * (Y / M) ^ (-(η - γ))) (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hx' : (0 : ℝ) < x := hx
  exact mul_lt_mul_of_pos_left
    (Real.rpow_lt_rpow_of_neg (div_pos hx' hM) (div_lt_div_of_pos_right hxy hM) (by linarith)) hk

/-! ### Example 20.3.3: recursive multiple priors -/

/-- Linearity of `t`-step expectations. -/
theorem aa_Ex_smul (q : List S → S → ℝ) (a : ℝ) (f : List S → ℝ) :
    ∀ t h, aa_Ex q t (fun h' => a * f h') h = a * aa_Ex q t f h
  | 0, _ => rfl
  | t + 1, h => by
    simp only [aa_Ex, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [aa_Ex_smul q a f t (s :: h)]; ring

/-- **Example 20.3.3** (Miao, p. 710; Epstein and Wang 1994). For the recursive multiple-priors
utility (20.7) with `u` concave (`u'` a supergradient of `u`), `β ≥ 0`, a full-support reference
`p`, and a selection `q*` of priors attaining the minimum at every node, the process
`π_t = β^t u'(c_t) M*_t`, `M*_t = ∏ dq*/dp`, is a utility supergradient at `c`. -/
theorem example_20_3_3 {u u' : ℝ → ℝ} (hu : ∀ x y, u y ≤ u x + u' x * (y - x)) {β : ℝ}
    (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)} (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q)
    {p : List S → S → ℝ} (hpos : ∀ h s, 0 < p h s) (c : List S → ℝ) (N : ℕ)
    (qs : List S → S → ℝ) (hqs : ∀ h, qs h ∈ P h)
    (hmin : ∀ h : List S, h.length < N →
      aa_E (qs h) (fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)) =
        aa_maxmin (P h) (fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h))) :
    aa_IsSupergradient (fun c' => aa_rmpU u β P c' N []) p N c
      (fun h => β ^ h.length * aa_M (fun h s => qs h s / p h s) h * u' (c h)) := by
  intro c'
  let g : List S → ℝ := fun h => u' (c h) * (c' h - c h)
  have key : ∀ k h, h.length + k = N →
      aa_rmpU u β P c' k h ≤ aa_rmpU u β P c k h +
        ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g h := by
    intro k
    induction k with
    | zero =>
      intro h _
      simp only [aa_rmpU, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
        aa_Ex, g]
      exact hu _ _
    | succ k ih =>
      intro h hlen
      have hidx : N - h.length - 1 = k := by omega
      have hm := hmin h (by omega)
      rw [hidx] at hm
      simp only [aa_rmpU]
      have hD := hP h _ (hqs h)
      have h1 : aa_maxmin (P h) (fun s => aa_rmpU u β P c' k (s :: h)) ≤
          aa_E (qs h) fun s => aa_rmpU u β P c k (s :: h) +
            ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g (s :: h) :=
        (aa_maxmin_le (hP h) _ (hqs h)).trans (aa_E_mono hD fun s =>
          ih (s :: h) (by simp only [List.length_cons]; omega))
      rw [aa_E_add, hm] at h1
      have h2 : (aa_E (qs h) fun s => ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs t g (s :: h)) =
          ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs (t + 1) g h := by
        simp only [aa_E, aa_Ex, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left h1 hβ
      have h4 := hu (c h) (c' h)
      rw [Finset.sum_range_succ' _ (k + 1)]
      rw [show aa_Ex qs 0 g h = g h from rfl]
      simp only [pow_zero, one_mul, pow_succ, g]
      have h5 : β * ∑ t ∈ Finset.range (k + 1), β ^ t * aa_Ex qs (t + 1) g h =
          ∑ t ∈ Finset.range (k + 1), β ^ t * β * aa_Ex qs (t + 1) g h := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      simp only [g] at h5 h3
      linarith
  have hk := key N [] (by simp)
  refine hk.trans (add_le_add le_rfl (le_of_eq ?_))
  refine Finset.sum_congr rfl fun t ht => ?_
  have hdist : aa_distort p (fun h s => qs h s / p h s) = qs := by
    funext h s
    simp only [aa_distort]
    field_simp [(hpos h s).ne']
  have hch := aa_Ex_change p (fun h s => qs h s / p h s) g t []
  rw [hdist, aa_M, one_mul] at hch
  rw [hch, ← aa_Ex_smul]
  refine aa_Ex_congr p t [] fun h' hh' => ?_
  simp only [List.length_nil, zero_add] at hh'
  simp only [hh', g]
  ring

/-- For finite nonempty sets of priors a minimising selection exists, so the recursive
multiple-priors utility has the supergradient of Example 20.3.3. -/
theorem example_20_3_3_exists {u u' : ℝ → ℝ} (hu : ∀ x y, u y ≤ u x + u' x * (y - x)) {β : ℝ}
    (hβ : 0 ≤ β) {P : List S → Set (S → ℝ)} (hP : ∀ h, ∀ q ∈ P h, SS.IsDistribution q)
    (hfin : ∀ h, (P h).Finite) (hne : ∀ h, (P h).Nonempty) {p : List S → S → ℝ}
    (hpos : ∀ h s, 0 < p h s) (c : List S → ℝ) (N : ℕ) :
    ∃ π, aa_IsSupergradient (fun c' => aa_rmpU u β P c' N []) p N c π := by
  classical
  let qs : List S → S → ℝ := fun h =>
    (aa_maxmin_attained (hP h) (hfin h) (hne h)
      fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)).choose
  have hspec := fun h => (aa_maxmin_attained (hP h) (hfin h) (hne h)
      fun s => aa_rmpU u β P c (N - h.length - 1) (s :: h)).choose_spec
  exact ⟨_, example_20_3_3 hu hβ hP hpos c N qs (fun h => (hspec h).1)
    fun h _ => ((hspec h).2).symm⟩

/-! ### Exercise 20.2: divergence utility -/

/-- The minimising density of the multiplier problem, `m*_s = e^{−x_s/θ}/E e^{−x/θ}`. -/
noncomputable def aa_klDensity (θ : ℝ) (p x : S → ℝ) : S → ℝ :=
  fun s => Real.exp (-x s / θ) / ∑ s', p s' * Real.exp (-x s' / θ)

/-- `m*` is admissible and attains `R(x) = −θ ln E e^{−x/θ}` (relative entropy, `w = 1`). -/
theorem aa_klDensity_attains [Nonempty S] {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ}
    (hp : SS.IsDistribution p) (x : S → ℝ) :
    aa_Admissible p (aa_klDensity θ p x) ∧
      aa_divObj p (fun _ => 1) θ aa_klPhi x (aa_klDensity θ p x) =
        -θ * Real.log (∑ s, p s * Real.exp (-x s / θ)) := by
  set Zs := ∑ s, p s * Real.exp (-x s / θ) with hZ
  have hZ0 : 0 < Zs := aa_E_pos hp fun s => Real.exp_pos _
  refine ⟨⟨fun s => div_nonneg (Real.exp_pos _).le hZ0.le, ?_⟩, ?_⟩
  · simp only [aa_klDensity, ← hZ, mul_div_assoc', ← Finset.sum_div]
    exact div_self hZ0.ne'
  · have hlog : ∀ s, Real.log (aa_klDensity θ p x s) = -x s / θ - Real.log Zs := fun s => by
      rw [aa_klDensity, ← hZ, Real.log_div (Real.exp_pos _).ne' hZ0.ne', Real.log_exp]
    have hsum : ∑ s, p s * aa_klDensity θ p x s = 1 := by
      simp only [aa_klDensity, ← hZ, mul_div_assoc', ← Finset.sum_div]
      exact div_self hZ0.ne'
    unfold aa_divObj aa_klPhi
    simp only [hlog, mul_one]
    have e : ∀ s, p s * (aa_klDensity θ p x s * x s + θ * (aa_klDensity θ p x s *
        (-x s / θ - Real.log Zs) - aa_klDensity θ p x s + 1)) =
        p s * aa_klDensity θ p x s * (-θ * Real.log Zs - θ) + θ * p s := fun s => by
      field_simp
      ring
    rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
      ← Finset.mul_sum, hp.sum_eq_one]
    ring

/-- Exercise 20.2, divergence utility, the certainty equivalent: the multiplier aggregator
`R(x) = −θ ln E e^{−x/θ}` has derivative `κ = m*`, the minimising density. -/
theorem aa_riskSensitive_hasCEDeriv [Nonempty S] {θ : ℝ} (hθ : 0 < θ) {p : S → ℝ}
    (hp : SS.IsDistribution p) (x : S → ℝ) :
    aa_HasCEDeriv (fun y => -θ * Real.log (∑ s, p s * Real.exp (-y s / θ))) p
      (aa_klDensity θ p x) x := by
  set Zs := ∑ s, p s * Real.exp (-x s / θ) with hZ
  have hZ0 : 0 < Zs := aa_E_pos hp fun s => Real.exp_pos _
  have hf : (fun y : S → ℝ => ∑ s, p s * Real.exp (-y s / θ)) =
      fun y => ∑ s, p s * Real.exp ((-1 / θ) * y s) := by
    funext y
    exact Finset.sum_congr rfl fun s _ => by ring_nf
  have hin : HasFDerivAt (fun y : S → ℝ => ∑ s, p s * Real.exp (-y s / θ))
      (∑ s, p s • (Real.exp ((-1 / θ) * x s) • ((-1 / θ) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s))) x := by
    rw [hf]
    exact HasFDerivAt.fun_sum fun s _ =>
      (((hasFDerivAt_apply s x).const_mul (-1 / θ)).exp.const_mul (p s))
  have hR := (hin.log hZ0.ne').const_mul (-θ)
  unfold aa_HasCEDeriv
  refine hR.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, Finset.mul_sum, aa_klDensity]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← hZ]
  field_simp

omit [Fintype S] in
/-- **Exercise 20.2**, divergence utility (Miao, p. 735). With `W(c, y) = u(c) + βy`
(`W₁ = u'(c)`, `W₂ = β`) and the multiplier aggregator, whose derivative is the minimising density
`m*` (`aa_riskSensitive_hasCEDeriv`), the pricing kernel of Proposition 20.3.2 is
`M_{t+1} = βu'(c_{t+1})/u'(c_t) · m*_{t+1}`. -/
theorem ex_20_2_divergence (u' : ℝ → ℝ) (c : List S → ℝ) (β : ℝ) (m : List S → S → ℝ) (N : ℕ)
    (h : List S) (s : S) (hlen : h.length + 1 < N) (hβ : 0 < β) (hm : ∀ h s, 0 < m h s)
    (hu : u' (c h) ≠ 0) :
    aa_gradπ (fun h => u' (c h)) (fun _ => β) m N (s :: h) /
        aa_gradπ (fun h => u' (c h)) (fun _ => β) m N h =
      β * (u' (c (s :: h)) / u' (c h)) * m h s := by
  rw [aa_pricingKernel _ _ _ N h s hlen (aa_M_pos (fun h s => mul_pos hβ (hm h s)) h).ne' hu]
  ring

/-- Exercise 20.2, divergence utility with a general divergence (Miao, p. 696): a density `m*`
attaining `R_t(x)` is a supergradient of `R_t` at `x`:
`R_t(y) ≤ R_t(x) + E_t[m*(y − x)]` (envelope inequality). -/
theorem aa_divR_supergradient {p w : S → ℝ} (hp : SS.IsDistribution p) (hw : ∀ s, 0 ≤ w s)
    {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {x : S → ℝ} {m : S → ℝ}
    (hm : aa_Admissible p m) (hatt : aa_divObj p w θ φ x m = aa_divR p w θ φ x) (y : S → ℝ) :
    aa_divR p w θ φ y ≤ aa_divR p w θ φ x + ∑ s, p s * m s * (y s - x s) := by
  have h1 := aa_divR_le hp hw hθ hφ y hm
  have h2 := aa_divObj_sub p w θ φ y x m
  linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Epstein–Zin recursion on one node of an event tree

Miao, *Economic Dynamics in Discrete Time*, §20.4 (pp. 711–714), using the Epstein–Zin utility
(20.3) of §20.2.1 and its pricing kernel (20.20) of §20.3.3, which are restated here under the
prefix `pa_` (the §20.2–20.3 formalisations live in other projects).

The setting is one node of an event tree: the next-period shock takes finitely many values
`s : S` with probabilities `p s` (`p ≥ 0`, `∑ p = 1`), and the conditional expectation is
`pa_E p f = ∑ s, p s * f s`.

* `pa_W β ρ c y = ((1 − β) c^{1−ρ} + β y^{1−ρ})^{1/(1−ρ)}`, the CES time aggregator of (20.3);
* `pa_CE γ p v = (E v^{1−γ})^{1/(1−γ)}`, the certainty equivalent of (20.3), which is the
  Kreps–Porteus certainty equivalent `kpR (1 − γ)` of the copied `SSCertaintyEquivalents`
  (`pa_CE_eq_kpR`);
* both are positively homogeneous of degree one (`pa_W_homog`, `pa_CE_homog`), the property
  "scale invariance" used for the conjecture `J_t(X) = A_t X_t` of §20.4.1;
* `pa_M` is the pricing kernel (20.20), `M = β (C'/C)^{−ρ} (U'/M_t(U'))^{ρ−γ}`.

The lemmas `pa_E_*` are the linearity of the conditional expectation, and `pa_log_*` are the
logarithmic identities used to verify identities between positive powers.
-/

namespace Miao.RecursiveUtility

open Real

/-- The conditional expectation `E_t f = ∑ s, p s f(s)` at one node of the event tree. -/
def pa_E {S : Type*} [Fintype S] (p : S → ℝ) (f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- Miao, (20.3), p. 686: the CES time aggregator
`W(c, y) = ((1 − β) c^{1−ρ} + β y^{1−ρ})^{1/(1−ρ)}` of the Epstein–Zin utility. -/
noncomputable def pa_W (β ρ c y : ℝ) : ℝ :=
  ((1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ)) ^ (1 / (1 - ρ))

/-- Miao, (20.3), p. 686: the certainty equivalent `M_t(x) = (E_t x^{1−γ})^{1/(1−γ)}`. -/
noncomputable def pa_CE {S : Type*} [Fintype S] (γ : ℝ) (p : S → ℝ) (v : S → ℝ) : ℝ :=
  (pa_E p fun s => v s ^ (1 - γ)) ^ (1 / (1 - γ))

/-- Miao, (20.20), p. 710: the Epstein–Zin pricing kernel
`M_{t+1} = β (C_{t+1}/C_t)^{−ρ} (U_{t+1}/M_t(U_{t+1}))^{ρ−γ}`. -/
noncomputable def pa_M {S : Type*} [Fintype S] (β ρ γ : ℝ) (p : S → ℝ) (C : ℝ) (C' U' : S → ℝ)
    (s : S) : ℝ :=
  β * (C' s / C) ^ (-ρ) * (U' s / pa_CE γ p U') ^ (ρ - γ)

theorem pa_E_add {S : Type*} [Fintype S] (p f g : S → ℝ) :
    pa_E p (fun s => f s + g s) = pa_E p f + pa_E p g := by
  simp only [pa_E, mul_add, Finset.sum_add_distrib]

theorem pa_E_sub {S : Type*} [Fintype S] (p f g : S → ℝ) :
    pa_E p (fun s => f s - g s) = pa_E p f - pa_E p g := by
  simp only [pa_E, mul_sub, Finset.sum_sub_distrib]

theorem pa_E_const_mul {S : Type*} [Fintype S] (p f : S → ℝ) (k : ℝ) :
    pa_E p (fun s => k * f s) = k * pa_E p f := by
  simp only [pa_E, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem pa_E_mul_const {S : Type*} [Fintype S] (p f : S → ℝ) (k : ℝ) :
    pa_E p (fun s => f s * k) = pa_E p f * k := by
  simp only [pa_E, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem pa_E_const {S : Type*} [Fintype S] {p : S → ℝ} (hp1 : ∑ s, p s = 1) (k : ℝ) :
    pa_E p (fun _ => k) = k := by
  simp only [pa_E, ← Finset.sum_mul, hp1, one_mul]

theorem pa_E_congr {S : Type*} [Fintype S] (p : S → ℝ) {f g : S → ℝ} (h : ∀ s, f s = g s) :
    pa_E p f = pa_E p g := by
  simp only [pa_E, h]

theorem pa_E_pos {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    {f : S → ℝ} (hf : ∀ s, 0 < f s) : 0 < pa_E p f := by
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < p s := by
    by_contra h
    push Not at h
    have : ∑ s, p s ≤ 0 := Finset.sum_nonpos fun s _ => h s
    linarith
  calc 0 < p s₀ * f s₀ := mul_pos hs₀ (hf s₀)
    _ ≤ ∑ s, p s * f s :=
        Finset.single_le_sum (f := fun s => p s * f s)
          (fun s _ => mul_nonneg (hp s) (hf s).le) (Finset.mem_univ s₀)

/-- Two positive reals with equal logarithms are equal. -/
theorem pa_eq_of_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a = Real.log b) :
    a = b := Real.log_injOn_pos ha hb h

theorem pa_CE_pos {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (γ : ℝ) {v : S → ℝ} (hv : ∀ s, 0 < v s) : 0 < pa_CE γ p v :=
  Real.rpow_pos_of_pos (pa_E_pos hp hp1 fun s => Real.rpow_pos_of_pos (hv s) _) _

/-- The certainty equivalent (20.3) is the Kreps–Porteus certainty equivalent `kpR (1 − γ)`
(Sargent–Stachurski (7.16)) of the copied `SSCertaintyEquivalents`, at a state `x` whose
transition row is `p`. -/
theorem pa_CE_eq_kpR {S : Type*} [Fintype S] (γ : ℝ) (P : Matrix S S ℝ) (x : S) (v : S → ℝ) :
    pa_CE γ (P x) v = SS.kpR (1 - γ) P v x := by
  simp only [pa_CE, SS.kpR, pa_E, Matrix.mulVec, dotProduct, one_div]

/-- Miao, p. 686: the certainty equivalent of (20.3) is homogeneous of degree one,
`M_t(λ v) = λ M_t(v)` for `λ > 0`. -/
theorem pa_CE_homog {S : Type*} [Fintype S] {γ : ℝ} (hγ : γ ≠ 1) {p : S → ℝ}
    (hp : ∀ s, 0 ≤ p s) {lam : ℝ} (hlam : 0 < lam) {v : S → ℝ} (hv : ∀ s, 0 ≤ v s) :
    pa_CE γ p (fun s => lam * v s) = lam * pa_CE γ p v := by
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hE : (pa_E p fun s => (lam * v s) ^ (1 - γ))
      = lam ^ (1 - γ) * pa_E p fun s => v s ^ (1 - γ) := by
    rw [← pa_E_const_mul]
    exact pa_E_congr p fun s => Real.mul_rpow hlam.le (hv s)
  have hE0 : 0 ≤ pa_E p fun s => v s ^ (1 - γ) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (Real.rpow_nonneg (hv s) _)
  simp only [pa_CE]
  rw [hE, Real.mul_rpow (Real.rpow_nonneg hlam.le _) hE0, ← Real.rpow_mul hlam.le,
    mul_one_div_cancel h1, Real.rpow_one]

/-- Miao, p. 686: the time aggregator of (20.3) is homogeneous of degree one,
`W(λ c, λ y) = λ W(c, y)` for `λ > 0` ("scale invariance"). -/
theorem pa_W_homog {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hρ : ρ ≠ 1) {lam c y : ℝ}
    (hlam : 0 < lam) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    pa_W β ρ (lam * c) (lam * y) = lam * pa_W β ρ c y := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hin : 0 ≤ (1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ) :=
    add_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hc _))
      (mul_nonneg hβ0 (Real.rpow_nonneg hy _))
  simp only [pa_W]
  rw [Real.mul_rpow hlam.le hc, Real.mul_rpow hlam.le hy]
  have : (1 - β) * (lam ^ (1 - ρ) * c ^ (1 - ρ)) + β * (lam ^ (1 - ρ) * y ^ (1 - ρ))
      = lam ^ (1 - ρ) * ((1 - β) * c ^ (1 - ρ) + β * y ^ (1 - ρ)) := by ring
  rw [this, Real.mul_rpow (Real.rpow_nonneg hlam.le _) hin, ← Real.rpow_mul hlam.le,
    mul_one_div_cancel h1, Real.rpow_one]

theorem pa_W_pos {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    0 < pa_W β ρ c y :=
  Real.rpow_pos_of_pos (add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hc _))
    (mul_pos hβ0 (Real.rpow_pos_of_pos hy _))) _

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Portfolio choice with Epstein–Zin utility: optimality and equilibrium

Miao, *Economic Dynamics in Discrete Time*, §20.4 and §20.4.1 (pp. 711–714).

One node of the event tree (`PAEpsteinZin`): next-period states `s : S` with probabilities `p`.
Wealth `X`, consumption `C = a X`, portfolio return `R_w(s)`, next-period consumption `C'(s)`
and wealth `X'(s) = R_w(s)(X − C)` (20.21).

* (20.21) and the wealth return: `pa_wealthReturn`, `pa_wealthReturn_eq` (with a riskless
  asset, `R_w = R_f + ∑ ψ_i (R_i − R_f)`).
* The Bellman equation under the conjecture `J_{t+1}(X) = A_{t+1} X`: the objective is
  homogeneous of degree one in wealth (`pa_bellman_conjecture`) and so is its supremum
  (`pa_value_homogeneous`), which is the conjecture `J_t(X) = A_t X_t`.
* (20.22): the first-order condition for the consumption–wealth ratio `a`
  (`pa_bellman_hasDerivAt`, `eq_20_22`).
* (20.23)–(20.26): `eq_20_23`, `eq_20_24`, `eq_20_25`, `eq_20_26`.
* The portfolio first-order condition and (20.27)–(20.30): `pa_portfolio_foc`,
  `pa_portfolio_foc_X`, `eq_20_27`, `pa_sum_portfolio_foc`, `eq_20_28`, `eq_20_29`, with the
  kernel `M̄` of (20.30) (`pa_Mbar`).
* (20.31) and `M = M̄` (`eq_20_31`, `pa_M_eq_Mbar`).
* The riskfree rate `R_f = 1/E_t M` and the conditional equity premium
  `E_t R_e − R_f = −Cov_t(R_e, M)/E_t M` (`pa_riskfree_rate`, `pa_equity_premium`).

Departures: none in substance. The first-order conditions are proved as necessary conditions
at a local maximum (the text derives them without discussing sufficiency).
-/

namespace Miao.RecursiveUtility

open Real

/-- Miao, (20.21), p. 711: the portfolio (wealth, market) return `R_w = ∑_i ψ_i R_i`. -/
def pa_wealthReturn {S ι : Type*} [Fintype ι] (ψ : ι → ℝ) (R : ι → S → ℝ) (s : S) : ℝ :=
  ∑ i, ψ i * R i s

/-- Miao, p. 711: with `∑_i ψ_i = 1` and a riskless asset `i₀` (`R_{i₀} ≡ R_f`), the wealth
return is `R_w = R_f + ∑_{i} ψ_i (R_i − R_f)`. -/
theorem pa_wealthReturn_eq {S ι : Type*} [Fintype ι] {ψ : ι → ℝ} (hψ : ∑ i, ψ i = 1)
    (R : ι → S → ℝ) (Rf : ℝ) (s : S) :
    pa_wealthReturn ψ R s = Rf + ∑ i, ψ i * (R i s - Rf) := by
  simp only [pa_wealthReturn, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hψ, one_mul]
  ring

/-- Miao, (20.21), p. 711: the budget constraint `X_{t+1} = R_{w,t+1}(X_t − C_t)`. -/
def pa_nextWealth {S : Type*} (Rw : S → ℝ) (X C : ℝ) (s : S) : ℝ := Rw s * (X - C)

/-- The objective of the Bellman equation of §20.4.1 after substituting the conjecture,
`(1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β Q^{1−ρ}` with `Q = M_t(A_{t+1} R_{w,t+1})`. -/
noncomputable def pa_bellmanInner (β ρ Q a : ℝ) : ℝ :=
  (1 - β) * a ^ (1 - ρ) + (1 - a) ^ (1 - ρ) * (β * Q ^ (1 - ρ))

theorem pa_bellmanInner_pos {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q) (ha0 : 0 < a)
    (ha1 : a < 1) : 0 < pa_bellmanInner β ρ Q a :=
  add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos ha0 _))
    (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (mul_pos hβ0 (Real.rpow_pos_of_pos hQ _)))

/-- Miao, §20.4.1, p. 711: substituting the budget constraint (20.21), `C = a X` and the
conjecture `J_{t+1}(X') = A_{t+1} X'` into the Bellman equation, the objective equals
`X ((1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β (M_t(A_{t+1} R_{w,t+1}))^{1−ρ})^{1/(1−ρ)}`. -/
theorem pa_bellman_conjecture {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {A' Rw : S → ℝ}
    (hA : ∀ s, 0 < A' s) (hR : ∀ s, 0 < Rw s) {X a : ℝ} (hX : 0 < X) (ha0 : 0 < a)
    (ha1 : a < 1) :
    pa_W β ρ (a * X) (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)
      = X * pa_bellmanInner β ρ (pa_CE γ p fun s => A' s * Rw s) a ^ (1 / (1 - ρ)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hQ : 0 ≤ pa_CE γ p fun s => A' s * Rw s :=
    Real.rpow_nonneg (Finset.sum_nonneg fun s _ => mul_nonneg (hp s)
      (Real.rpow_nonneg (mul_pos (hA s) (hR s)).le _)) _
  have hCE : (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)
      = X * ((1 - a) * pa_CE γ p fun s => A' s * Rw s) := by
    rw [← mul_assoc, ← pa_CE_homog hγ hp (by nlinarith) fun s => (mul_pos (hA s) (hR s)).le]
    congr 1
    funext s
    simp only [pa_nextWealth]
    ring
  rw [hCE, mul_comm a X, pa_W_homog hβ0.le hβ1.le hρ hX ha0.le (mul_nonneg (by linarith) hQ)]
  congr 1
  simp only [pa_W, pa_bellmanInner]
  rw [Real.mul_rpow (by linarith) hQ]
  ring_nf

/-- Miao, §20.4.1, p. 711: if `J_{t+1}(X') = A_{t+1} X'`, the value
`J_t(X) = sup_{a, R_w} W(a X, M_t(A_{t+1} R_w (X − a X)))` is linear in wealth,
`J_t(X) = A_t X` with `A_t = J_t(1)`: the conjecture `J_t(X_t) = A_t X_t`. Here `Rset` is
the set of attainable portfolio returns. -/
theorem pa_value_homogeneous {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    {β ρ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {A' : S → ℝ}
    (hA : ∀ s, 0 < A' s) (Rset : Set (S → ℝ)) (hR : ∀ Rw ∈ Rset, ∀ s, 0 < Rw s) {X : ℝ}
    (hX : 0 < X) :
    sSup {v | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ Rw ∈ Rset,
        v = pa_W β ρ (a * X) (pa_CE γ p fun s => A' s * pa_nextWealth Rw X (a * X) s)}
      = X * sSup {v | ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∃ Rw ∈ Rset,
        v = pa_W β ρ (a * 1) (pa_CE γ p fun s => A' s * pa_nextWealth Rw 1 (a * 1) s)} := by
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hX.le]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨a, ha, Rw, hRw, rfl⟩
    refine ⟨_, ⟨a, ha, Rw, hRw, rfl⟩, ?_⟩
    rw [pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) hX ha.1 ha.2,
      pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) one_pos ha.1 ha.2, one_mul]
  · rintro ⟨w, ⟨a, ha, Rw, hRw, rfl⟩, rfl⟩
    refine ⟨a, ha, Rw, hRw, ?_⟩
    rw [pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) hX ha.1 ha.2,
      pa_bellman_conjecture hp hβ0 hβ1 hρ hγ hA (hR Rw hRw) one_pos ha.1 ha.2, one_mul]

/-- Miao, §20.4.1, p. 712: the derivative of the inner objective with respect to `a`,
`(1 − ρ)((1 − β) a^{−ρ} − β Q^{1−ρ} (1 − a)^{−ρ})`. -/
theorem pa_bellmanInner_hasDerivAt {β ρ Q a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (pa_bellmanInner β ρ Q)
      ((1 - ρ) * ((1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ))) a := by
  have e : (1 : ℝ) - ρ - 1 = -ρ := by ring
  have h1 : HasDerivAt (fun a : ℝ => a ^ (1 - ρ)) ((1 - ρ) * a ^ (-ρ)) a := by
    have := Real.hasDerivAt_rpow_const (x := a) (p := 1 - ρ) (Or.inl ha0.ne')
    rwa [e] at this
  have h2 : HasDerivAt (fun a : ℝ => (1 - a) ^ (1 - ρ)) (-1 * (1 - ρ) * (1 - a) ^ (-ρ)) a := by
    have := ((hasDerivAt_id a).const_sub 1).rpow_const (p := 1 - ρ)
      (Or.inl (by simp only [id]; linarith))
    simp only [id] at this
    rwa [e] at this
  have := (h1.const_mul (1 - β)).add (h2.mul_const (β * Q ^ (1 - ρ)))
  convert this using 1
  · funext y
    simp only [pa_bellmanInner, Pi.add_apply]
  · ring

/-- Miao, §20.4.1, p. 712: the derivative of the Bellman objective
`a ↦ ((1 − β) a^{1−ρ} + (1 − a)^{1−ρ} β Q^{1−ρ})^{1/(1−ρ)}`. -/
theorem pa_bellman_hasDerivAt {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hQ : 0 < Q)
    (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun a => pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ)))
      ((1 - ρ) * ((1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ)) * (1 / (1 - ρ))
        * pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ) - 1)) a :=
  (pa_bellmanInner_hasDerivAt ha0 ha1).rpow_const
    (Or.inl (pa_bellmanInner_pos hβ0 hβ1 hQ ha0 ha1).ne')

/-- Miao, (20.22), p. 712: the first-order condition for the consumption–wealth ratio,
`(a/(1 − a))^{−ρ} = β/(1 − β) (M_t(A_{t+1} R_{w,t+1}))^{1−ρ}`, at any interior local maximum
`a ∈ (0, 1)` of the Bellman objective. -/
theorem eq_20_22 {β ρ Q a : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hQ : 0 < Q)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hmax : IsLocalMax (fun a => pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ))) a) :
    (a / (1 - a)) ^ (-ρ) = β / (1 - β) * Q ^ (1 - ρ) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hd := hmax.hasDerivAt_eq_zero (pa_bellman_hasDerivAt hβ0 hβ1 hQ ha0 ha1)
  have hpos := Real.rpow_pos_of_pos (pa_bellmanInner_pos (ρ := ρ) hβ0 hβ1 hQ ha0 ha1)
    (1 / (1 - ρ) - 1)
  have hk : (1 - β) * a ^ (-ρ) - β * Q ^ (1 - ρ) * (1 - a) ^ (-ρ) = 0 := by
    rcases mul_eq_zero.1 hd with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h h1
        · exact h
      · simp only [one_div, inv_eq_zero] at h
        exact absurd h h1
    · exact absurd h hpos.ne'
  have hb : (0 : ℝ) < 1 - a := by linarith
  rw [Real.div_rpow ha0.le hb.le]
  have hpa := Real.rpow_pos_of_pos hb (-ρ)
  have hβ' : (1 : ℝ) - β ≠ 0 := by linarith
  rw [div_eq_iff hpa.ne', div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hβ']
  linear_combination hk

/-- Miao, (20.23), p. 712: eliminating the expectation between the Bellman equation and
(20.22), `A_t = (1 − β)^{1/(1−ρ)} a_t^{−ρ/(1−ρ)} = (1 − β)^{1/(1−ρ)} (C_t/X_t)^{−ρ/(1−ρ)}`. -/
theorem eq_20_23 {β ρ Q a : ℝ} (hβ1 : β < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (h22 : (a / (1 - a)) ^ (-ρ) = β / (1 - β) * Q ^ (1 - ρ)) :
    pa_bellmanInner β ρ Q a ^ (1 / (1 - ρ)) = (1 - β) ^ (1 / (1 - ρ)) * a ^ (-ρ / (1 - ρ)) := by
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hQ' : β * Q ^ (1 - ρ) = (1 - β) * (a ^ (-ρ) / (1 - a) ^ (-ρ)) := by
    rw [← Real.div_rpow ha0.le hb.le, h22]
    field_simp
  have hin : pa_bellmanInner β ρ Q a = (1 - β) * a ^ (-ρ) := by
    simp only [pa_bellmanInner]
    rw [hQ', show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add ha0, Real.rpow_add hb,
      Real.rpow_one, Real.rpow_one]
    have := (Real.rpow_pos_of_pos hb (-ρ)).ne'
    field_simp
    ring
  rw [hin, Real.mul_rpow hβ'.le (Real.rpow_nonneg ha0.le _), ← Real.rpow_mul ha0.le]
  ring_nf

/-- Miao, (20.25), p. 712: with `X_t = C_t/a_t`, `X_{t+1} = (X_t − C_t)R_{w,t+1}
= R_{w,t+1} C_t (1 − a_t)/a_t`. -/
theorem eq_20_25 {S : Type*} (Rw : S → ℝ) {X C : ℝ} (hX : 0 < X) (hC : 0 < C) (s : S) :
    pa_nextWealth Rw X C s = Rw s * C * ((1 - C / X) / (C / X)) := by
  simp only [pa_nextWealth]
  field_simp

/-- Miao, (20.23) one period ahead: `A_{t+1} = (1 − β)^{1/(1−ρ)} (C_{t+1}/X_{t+1})^{−ρ/(1−ρ)}`. -/
noncomputable def pa_Anext {S : Type*} (β ρ : ℝ) (C' X' : S → ℝ) (s : S) : ℝ :=
  (1 - β) ^ (1 / (1 - ρ)) * (C' s / X' s) ^ (-ρ / (1 - ρ))

/-- Miao, (20.24), p. 712: substituting (20.23) at `t + 1` into (20.22),
`(a_t/(1 − a_t))^{−ρ}
= β (E_t[(C_{t+1}/X_{t+1})^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{1−γ}])^{(1−ρ)/(1−γ)}`. -/
theorem eq_20_24 {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) {β ρ γ a : ℝ}
    (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1) {C' X' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hX' : ∀ s, 0 < X' s) (hR : ∀ s, 0 < Rw s)
    (h22 : (a / (1 - a)) ^ (-ρ)
      = β / (1 - β) * (pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s) ^ (1 - ρ)) :
    (a / (1 - a)) ^ (-ρ) = β * (pa_E p fun s =>
      (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) ^ ((1 - ρ) / (1 - γ)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hterm : ∀ s, (pa_Anext β ρ C' X' s * Rw s) ^ (1 - γ) = (1 - β) ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) := by
    intro s
    have hc := hC' s
    have hx := hX' s
    have hr := hR s
    simp only [pa_Anext]
    rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hβ'.le, ← Real.rpow_mul (by positivity),
      show 1 / (1 - ρ) * (1 - γ) = (1 - γ) / (1 - ρ) by ring,
      show -ρ / (1 - ρ) * (1 - γ) = -ρ * (1 - γ) / (1 - ρ) by ring]
    ring
  have hG : 0 ≤ pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (mul_nonneg
      (Real.rpow_nonneg (div_pos (hC' s) (hX' s)).le _) (Real.rpow_nonneg (hR s).le _))
  rw [h22]
  simp only [pa_CE]
  rw [pa_E_congr p hterm, pa_E_const_mul, ← Real.rpow_mul (mul_nonneg
    (Real.rpow_nonneg hβ'.le _) hG), Real.mul_rpow (Real.rpow_nonneg hβ'.le _) hG,
    ← Real.rpow_mul hβ'.le, show (1 - γ) / (1 - ρ) * (1 / (1 - γ) * (1 - ρ)) = 1 by field_simp,
    Real.rpow_one, show 1 / (1 - γ) * (1 - ρ) = (1 - ρ) / (1 - γ) by ring]
  field_simp

/-- Miao, (20.26), p. 712: substituting (20.25) into (20.24),
`β^{(1−γ)/(1−ρ)} E_t[(C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ)}] = 1`. -/
theorem eq_20_26 {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {β ρ γ a C : ℝ} (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (h24 : (a / (1 - a)) ^ (-ρ) = β * (pa_E p fun s =>
      (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (1 - γ)) ^ ((1 - ρ) / (1 - γ))) :
    β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ ((1 - γ) / (1 - ρ))) = 1 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hb : (0 : ℝ) < 1 - a := by linarith
  set b := a / (1 - a) with hb_def
  have hbpos : 0 < b := div_pos ha0 hb
  set k := -ρ * (1 - γ) / (1 - ρ) with hk
  have hterm : ∀ s, (C' s / X' s) ^ k * Rw s ^ (1 - γ)
      = b ^ k * ((C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ))) := by
    intro s
    have hc := hC' s
    have hr := hR s
    rw [h25 s]
    apply pa_eq_of_log_eq (by positivity) (by positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, hb_def]
    rw [hk]
    field_simp
    ring
  have hE' : 0 < pa_E p fun s => (C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ)) :=
    pa_E_pos hp hp1 fun s => mul_pos (Real.rpow_pos_of_pos (div_pos (hC' s) hC) _)
      (Real.rpow_pos_of_pos (hR s) _)
  set E' := pa_E p fun s => (C' s / C) ^ k * Rw s ^ ((1 - γ) / (1 - ρ)) with hE'_def
  rw [pa_E_congr p hterm, pa_E_const_mul, Real.mul_rpow (Real.rpow_nonneg hbpos.le _) hE'.le,
    ← Real.rpow_mul hbpos.le, show k * ((1 - ρ) / (1 - γ)) = -ρ by rw [hk]; field_simp] at h24
  have hβE : β * E' ^ ((1 - ρ) / (1 - γ)) = 1 := by
    have hbρ := Real.rpow_pos_of_pos hbpos (-ρ)
    field_simp at h24
    nlinarith [h24]
  have := congrArg (fun x : ℝ => x ^ ((1 - γ) / (1 - ρ))) hβE
  simp only [Real.one_rpow] at this
  rw [Real.mul_rpow hβ0.le (Real.rpow_nonneg hE'.le _), ← Real.rpow_mul hE'.le,
    show (1 - ρ) / (1 - γ) * ((1 - γ) / (1 - ρ)) = 1 by field_simp, Real.rpow_one] at this
  exact this

/-- The wealth return in excess-return form, `R_w = R_f + ∑_i ψ_i (R_i − R_f)`, where `ψ` are
the weights on the risky assets (the riskless asset has weight `1 − ∑ ψ_i`). -/
def pa_Rw {S ι : Type*} [Fintype ι] (Rf : ℝ) (ψ : ι → ℝ) (R : ι → S → ℝ) (s : S) : ℝ :=
  Rf + ∑ i, ψ i * (R i s - Rf)

/-- Raising the weight on risky asset `i` by `t` (financed by the riskless asset) moves the
wealth return by `t (R_i − R_f)`. -/
theorem pa_Rw_update {S ι : Type*} [Fintype ι] [DecidableEq ι] (Rf : ℝ) (ψ : ι → ℝ)
    (R : ι → S → ℝ) (i : ι) (t : ℝ) (s : S) :
    pa_Rw Rf (ψ + t • Pi.single i 1) R s = pa_Rw Rf ψ R s + t * (R i s - Rf) := by
  simp only [pa_Rw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  ring

/-- Miao, §20.4.1, p. 712: the portfolio first-order condition. If the weight `t = 0` on the
direction `d` (for asset `i`, `d = R_i − R_f`) locally maximises the certainty equivalent
`M_t(A_{t+1}(R_w + t d))`, then `E_t[A_{t+1}^{1−γ} R_w^{−γ} d] = 0`. -/
theorem pa_portfolio_foc {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {γ : ℝ} (hγ : γ ≠ 1) {A' Rw d : S → ℝ} (hA : ∀ s, 0 < A' s)
    (hR : ∀ s, 0 < Rw s)
    (hmax : IsLocalMax (fun t : ℝ => pa_CE γ p fun s => A' s * (Rw s + t * d s)) 0) :
    (pa_E p fun s => A' s ^ (1 - γ) * Rw s ^ (-γ) * d s) = 0 := by
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hterm : ∀ s, HasDerivAt (fun t : ℝ => p s * (A' s * (Rw s + t * d s)) ^ (1 - γ))
      (p s * ((1 - γ) * (A' s ^ (1 - γ) * Rw s ^ (-γ) * d s))) 0 := by
    intro s
    have hin : HasDerivAt (fun t : ℝ => A' s * (Rw s + t * d s)) (A' s * (1 * d s)) 0 :=
      (((hasDerivAt_id (0 : ℝ)).mul_const (d s)).const_add (Rw s)).const_mul (A' s)
    have hpos : 0 < A' s * (Rw s + 0 * d s) := by
      rw [zero_mul, add_zero]; exact mul_pos (hA s) (hR s)
    have := (hin.rpow_const (p := 1 - γ) (Or.inl hpos.ne')).const_mul (p s)
    convert this using 2
    rw [zero_mul, add_zero, Real.mul_rpow (hA s).le (hR s).le,
      show (1 : ℝ) - γ - 1 = -γ by ring, Real.rpow_sub (hA s), Real.rpow_one]
    have := (hA s).ne'
    simp only [Real.rpow_neg (hA s).le]
    field_simp
  have hg := HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hterm s
  have hg0 : 0 < ∑ s, p s * (A' s * (Rw s + 0 * d s)) ^ (1 - γ) := by
    simp only [zero_mul, add_zero]
    exact pa_E_pos hp hp1 fun s => Real.rpow_pos_of_pos (mul_pos (hA s) (hR s)) _
  have hce := hg.rpow_const (p := 1 / (1 - γ)) (Or.inl hg0.ne')
  have hd := hmax.hasDerivAt_eq_zero hce
  have hpos := Real.rpow_pos_of_pos hg0 (1 / (1 - γ) - 1)
  rcases mul_eq_zero.1 hd with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have hsum : ∑ s, p s * ((1 - γ) * (A' s ^ (1 - γ) * Rw s ^ (-γ) * d s))
          = (1 - γ) * pa_E p fun s => A' s ^ (1 - γ) * Rw s ^ (-γ) * d s := by
        simp only [pa_E, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hsum] at h
      exact (mul_eq_zero.1 h).resolve_left h2
    · simp only [one_div, inv_eq_zero] at h
      exact absurd h h2
  · exact absurd h hpos.ne'

/-- Miao, p. 712: substituting (20.23) at `t + 1` into the portfolio first-order condition,
`E_t[(C_{t+1}/X_{t+1})^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{−γ} (R_{i,t+1} − R_{f,t+1})] = 0`. -/
theorem pa_portfolio_foc_X {S : Type*} [Fintype S] {p : S → ℝ} {β ρ γ : ℝ} (hβ1 : β < 1)
    {C' X' Rw d : S → ℝ} (hC' : ∀ s, 0 < C' s) (hX' : ∀ s, 0 < X' s)
    (hfoc : (pa_E p fun s => pa_Anext β ρ C' X' s ^ (1 - γ) * Rw s ^ (-γ) * d s) = 0) :
    (pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) = 0 := by
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hterm : ∀ s, pa_Anext β ρ C' X' s ^ (1 - γ) * Rw s ^ (-γ) * d s
      = (1 - β) ^ ((1 - γ) / (1 - ρ)) *
        ((C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) := by
    intro s
    have hc := hC' s
    have hx := hX' s
    simp only [pa_Anext]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hβ'.le,
      ← Real.rpow_mul (by positivity), show 1 / (1 - ρ) * (1 - γ) = (1 - γ) / (1 - ρ) by ring,
      show -ρ / (1 - ρ) * (1 - γ) = -ρ * (1 - γ) / (1 - ρ) by ring]
    ring
  rw [pa_E_congr p hterm, pa_E_const_mul] at hfoc
  exact (mul_eq_zero.1 hfoc).resolve_left (Real.rpow_pos_of_pos hβ' _).ne'

/-- Miao, (20.27), p. 712: substituting (20.25),
`E_t[(C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ) − 1} (R_{i,t+1} − R_{f,t+1})] = 0`. -/
theorem eq_20_27 {S : Type*} [Fintype S] {p : S → ℝ} {ρ γ a C : ℝ} (hρ : ρ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw d : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (hfoc : (pa_E p fun s => (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s) = 0) :
    (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      Rw s ^ ((1 - γ) / (1 - ρ) - 1) * d s) = 0 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hbpos : 0 < a / (1 - a) := div_pos ha0 hb
  have hterm : ∀ s, (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ) * d s
      = (a / (1 - a)) ^ (-ρ * (1 - γ) / (1 - ρ)) * ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
        Rw s ^ ((1 - γ) / (1 - ρ) - 1) * d s) := by
    intro s
    have hc := hC' s
    have hr := hR s
    have key : (C' s / X' s) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ (-γ)
        = (a / (1 - a)) ^ (-ρ * (1 - γ) / (1 - ρ)) * ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
          Rw s ^ ((1 - γ) / (1 - ρ) - 1)) := by
      rw [h25 s]
      apply pa_eq_of_log_eq (by positivity) (by positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
      field_simp
      ring
    rw [key]
    ring
  rw [pa_E_congr p hterm, pa_E_const_mul] at hfoc
  exact (mul_eq_zero.1 hfoc).resolve_left (Real.rpow_pos_of_pos hbpos _).ne'

/-- Miao, p. 713: multiplying (20.27) by `ψ_{i,t+1}` and summing over the risky assets,
`E_t[K R_w^{(1−γ)/(1−ρ)−1} R_f] = E_t[K R_w^{(1−γ)/(1−ρ)}]`, `K = (C_{t+1}/C_t)^{−ρ(1−γ)/(1−ρ)}`. -/
theorem pa_sum_portfolio_foc {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {ρ γ C Rf : ℝ}
    {C' : S → ℝ} {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) :
    (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf)
      = pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
        pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ)) := by
  set K := fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
    pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) with hK
  have hsum : ∑ i, ψ i * (pa_E p fun s => K s * (R i s - Rf)) = 0 := by
    simp only [hK, h27, mul_zero, Finset.sum_const_zero]
  have hpt : ∀ s, (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))
      = K s * Rf + K s * ∑ i, ψ i * (R i s - Rf) := by
    intro s
    rw [← mul_add, show Rf + ∑ i, ψ i * (R i s - Rf) = pa_Rw Rf ψ R s from rfl, hK]
    simp only
    rw [mul_assoc, ← Real.rpow_add_one (hR s).ne', sub_add_cancel]
  have hswap : (pa_E p fun s => K s * ∑ i, ψ i * (R i s - Rf))
      = ∑ i, ψ i * (pa_E p fun s => K s * (R i s - Rf)) := by
    simp only [pa_E, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  rw [pa_E_congr p hpt, pa_E_add, hswap, hsum, add_zero]

/-- Miao, (20.30), p. 713: the kernel
`M̄_{t+1} = (β (C_{t+1}/C_t)^{−ρ})^{(1−γ)/(1−ρ)} R_{w,t+1}^{(ρ−γ)/(1−ρ)}`. -/
noncomputable def pa_Mbar {S : Type*} (β ρ γ C : ℝ) (C' Rw : S → ℝ) (s : S) : ℝ :=
  (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) * Rw s ^ ((ρ - γ) / (1 - ρ))

theorem pa_Mbar_eq {S : Type*} {β ρ γ C : ℝ} (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C)
    {C' Rw : S → ℝ} (hC' : ∀ s, 0 < C' s) (s : S) :
    pa_Mbar β ρ γ C C' Rw s = β ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * Rw s ^ ((1 - γ) / (1 - ρ) - 1)) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hc := hC' s
  simp only [pa_Mbar]
  rw [Real.mul_rpow hβ0.le (by positivity), ← Real.rpow_mul (by positivity),
    show -ρ * ((1 - γ) / (1 - ρ)) = -ρ * (1 - γ) / (1 - ρ) by ring,
    show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by field_simp; ring]
  ring

/-- Miao, (20.28), p. 713: using (20.26) in `pa_sum_portfolio_foc`,
`E_t[(β (C_{t+1}/C_t)^{−ρ})^{(1−γ)/(1−ρ)} R_{w,t+1}^{(1−γ)/(1−ρ) − 1} R_{f,t+1}] = 1`. -/
theorem eq_20_28 {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {β ρ γ C Rf : ℝ}
    (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C) {C' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h26 : β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))) = 1)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) :
    (pa_E p fun s => (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf) = 1 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hpt : ∀ s, (β * (C' s / C) ^ (-ρ)) ^ ((1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf = β ^ ((1 - γ) / (1 - ρ)) *
      ((C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * Rf) := by
    intro s
    have h := pa_Mbar_eq (γ := γ) (Rw := pa_Rw Rf ψ R) hβ0 hρ hC hC' s
    simp only [pa_Mbar] at h
    rw [show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by field_simp; ring] at h
    rw [h]
    ring
  rw [pa_E_congr p hpt, pa_E_const_mul, pa_sum_portfolio_foc hR h27, h26]

/-- Miao, (20.29)–(20.30), p. 713: the Euler equation `E_t[M̄_{t+1} R_{i,t+1}] = 1` for every
asset `i`, where `M̄` is the kernel (20.30). -/
theorem eq_20_29 {S ι : Type*} [Fintype S] [Fintype ι] {p : S → ℝ} {β ρ γ C Rf : ℝ}
    (hβ0 : 0 < β) (hρ : ρ ≠ 1) (hC : 0 < C) {C' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    {ψ : ι → ℝ} {R : ι → S → ℝ} (hR : ∀ s, 0 < pa_Rw Rf ψ R s)
    (h26 : β ^ ((1 - γ) / (1 - ρ)) * (pa_E p fun s =>
      (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) * pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ))) = 1)
    (h27 : ∀ i, (pa_E p fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
      pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) * (R i s - Rf)) = 0) (i : ι) :
    (pa_E p fun s => pa_Mbar β ρ γ C C' (pa_Rw Rf ψ R) s * R i s) = 1 := by
  have h28 := eq_20_28 hβ0 hρ hC hC' hR h26 h27
  set K := fun s => (C' s / C) ^ (-ρ * (1 - γ) / (1 - ρ)) *
    pa_Rw Rf ψ R s ^ ((1 - γ) / (1 - ρ) - 1) with hK
  have hMK : ∀ s, pa_Mbar β ρ γ C C' (pa_Rw Rf ψ R) s * R i s
      = β ^ ((1 - γ) / (1 - ρ)) * (K s * Rf) + β ^ ((1 - γ) / (1 - ρ)) * (K s * (R i s - Rf)) := by
    intro s
    rw [pa_Mbar_eq hβ0 hρ hC hC' s]
    ring
  have h28' : (pa_E p fun s => β ^ ((1 - γ) / (1 - ρ)) * (K s * Rf)) = 1 := by
    refine Eq.trans (pa_E_congr p fun s => ?_) h28
    have h := pa_Mbar_eq (γ := γ) (Rw := pa_Rw Rf ψ R) hβ0 hρ hC hC' s
    simp only [pa_Mbar] at h
    rw [show (ρ - γ) / (1 - ρ) = (1 - γ) / (1 - ρ) - 1 by
      have : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
      field_simp; ring] at h
    rw [h, hK]
    ring
  rw [pa_E_congr p hMK, pa_E_add, h28', pa_E_const_mul, h27 i, mul_zero, add_zero]

/-- Miao, (20.31), p. 713: substituting (20.23) into `U_t = J_t(X_t) = A_t X_t`,
`X_t/C_t = (1/(1 − β)) (U_t/C_t)^{1−ρ}`. -/
theorem eq_20_31 {β ρ X C U : ℝ} (hβ1 : β < 1) (hρ : ρ ≠ 1) (hX : 0 < X) (hC : 0 < C)
    (hU : U = (1 - β) ^ (1 / (1 - ρ)) * (C / X) ^ (-ρ / (1 - ρ)) * X) :
    X / C = 1 / (1 - β) * (U / C) ^ (1 - ρ) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  subst hU
  apply pa_eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
  field_simp
  ring

/-- Miao, pp. 713–714: the pricing kernel (20.20) equals the kernel (20.30), `M_{t+1} = M̄_{t+1}`.
Here `U_{t+1} = A_{t+1} X_{t+1}` is the utility value, `A_{t+1}` is given by (20.23),
`X_{t+1}` by (20.25), and the consumption–wealth ratio `a_t` satisfies (20.22). -/
theorem pa_M_eq_Mbar {S : Type*} [Fintype S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {β ρ γ a C : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 0 < C) {C' X' Rw U' : S → ℝ} (hC' : ∀ s, 0 < C' s)
    (hR : ∀ s, 0 < Rw s) (h25 : ∀ s, X' s = Rw s * C * ((1 - a) / a))
    (hU : ∀ s, U' s = pa_Anext β ρ C' X' s * X' s)
    (h22 : (a / (1 - a)) ^ (-ρ)
      = β / (1 - β) * (pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s) ^ (1 - ρ)) (s : S) :
    pa_M β ρ γ p C C' U' s = pa_Mbar β ρ γ C C' Rw s := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have hβ' : (0 : ℝ) < 1 - β := by linarith
  have hb : (0 : ℝ) < 1 - a := by linarith
  have hX' : ∀ s, 0 < X' s := fun s => by
    rw [h25 s]; exact mul_pos (mul_pos (hR s) hC) (div_pos hb ha0)
  have hA : ∀ s, 0 < pa_Anext β ρ C' X' s := fun s =>
    mul_pos (Real.rpow_pos_of_pos hβ' _) (Real.rpow_pos_of_pos (div_pos (hC' s) (hX' s)) _)
  set Q := pa_CE γ p fun s => pa_Anext β ρ C' X' s * Rw s with hQ_def
  have hQ : 0 < Q := pa_CE_pos hp hp1 γ fun s => mul_pos (hA s) (hR s)
  have hCE : pa_CE γ p U' = C * ((1 - a) / a) * Q := by
    rw [hQ_def, ← pa_CE_homog hγ hp (mul_pos hC (div_pos hb ha0))
      fun s => (mul_pos (hA s) (hR s)).le]
    congr 1
    funext s
    rw [hU s, h25 s]
    ring
  have hlQ : Real.log Q = (-ρ * Real.log (a / (1 - a)) - Real.log (β / (1 - β))) / (1 - ρ) := by
    have := congrArg Real.log h22
    rw [Real.log_rpow (div_pos ha0 hb), Real.log_mul (div_pos hβ0 hβ').ne'
      (Real.rpow_pos_of_pos hQ _).ne', Real.log_rpow hQ] at this
    field_simp
    linarith
  have hc := hC' s
  have hr := hR s
  have hx := hX' s
  have hu : U' s = pa_Anext β ρ C' X' s * X' s := hU s
  simp only [pa_M, pa_Mbar]
  rw [hCE, hu]
  have ha' := hA s
  have hab : 0 < (1 - a) / a := div_pos hb ha0
  apply pa_eq_of_log_eq (by positivity) (by positivity)
  simp only [pa_Anext]
  rw [h25 s]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  rw [hlQ]
  simp (disch := positivity) only [Real.log_div]
  field_simp
  ring

/-- Miao, p. 714: the Euler equation (20.29) for the riskless asset gives
`R_{f,t+1} = 1/E_t[M_{t+1}]`. -/
theorem pa_riskfree_rate {S : Type*} [Fintype S] {p M : S → ℝ} {Rf : ℝ}
    (h : (pa_E p fun s => M s * Rf) = 1) : Rf = 1 / pa_E p M := by
  rw [pa_E_mul_const] at h
  have hM : pa_E p M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  field_simp
  linarith

/-- The conditional covariance `Cov_t(f, g) = E_t[f g] − E_t f E_t g`. -/
def pa_Cov {S : Type*} [Fintype S] (p f g : S → ℝ) : ℝ :=
  pa_E p (fun s => f s * g s) - pa_E p f * pa_E p g

/-- Miao, p. 714: the conditional equity premium
`E_t[R_{e,t+1}] − R_{f,t+1} = −Cov_t(R_{e,t+1}, M_{t+1})/E_t[M_{t+1}]`, from the Euler
equations for equity and the riskless asset. -/
theorem pa_equity_premium {S : Type*} [Fintype S] {p M Re : S → ℝ} {Rf : ℝ}
    (he : (pa_E p fun s => M s * Re s) = 1) (hf : (pa_E p fun s => M s * Rf) = 1) :
    pa_E p Re - Rf = -pa_Cov p Re M / pa_E p M := by
  have hRf := pa_riskfree_rate hf
  rw [pa_E_mul_const] at hf
  have hM : pa_E p M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hf
    exact zero_ne_one hf
  have he' : (pa_E p fun s => Re s * M s) = 1 := by
    rw [← he]; exact pa_E_congr p fun s => mul_comm _ _
  simp only [pa_Cov, he']
  rw [hRf]
  field_simp
  ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log-linear (lognormal) approximation of Campbell

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 715–716), equations (20.32)–(20.35).

The time-`t` conditional distribution is a probability measure `P` on a sample space `Ω`. The
log consumption growth, log wealth return and log return on asset `i` are the random variables
`X 0 = Δc_{t+1}`, `X 1 = r_{w,t+1}`, `X 2 = r_{i,t+1}`; "conditionally lognormal and
homoskedastic" means they are jointly Gaussian with mean vector `μ` and covariance matrix `V`
(`pa_JointGaussian`: every linear combination `∑ a_k X_k` has law `N(a·μ, aᵀVa)`; a concrete
instance is `pa_jointGaussian_rank_one`). The book's notation is
`σ_c² = V 0 0`, `σ_w² = V 1 1`, `σ_cw = V 0 1`, `σ_i² = V 2 2`, `σ_ic = V 2 0`, `σ_iw = V 2 1`.

* Campbell's formula `ln E X = E ln X + ½ Var ln X` for lognormal `X`:
  `pa_log_integral_exp_gaussian`, and for linear combinations `pa_integral_exp_lin`,
  `pa_lognormal_euler`.
* The log form of (20.26): `pa_eq_20_26_log`; (20.32): `eq_20_32`; (20.33): `eq_20_33`;
  (20.34): `eq_20_34`; (20.35): `eq_20_35`; and the expected log return on equity
  `E_t r_{e,t+1} = μ_e + ρ E_t Δc_{t+1}` (p. 718): `pa_expected_equity_return`.

Departure: in (20.32) the last variance term is `½((ρ−γ)/(1−ρ))² σ_w²` (the square is lost
in the printed text; (20.34) prints it). See `docs/PA-corrections.md`.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The linear form `a · μ = ∑_k a_k μ_k`. -/
def pa_lin {n : ℕ} (μ a : Fin n → ℝ) : ℝ := ∑ k, a k * μ k

/-- The quadratic form `aᵀ V a = ∑_k ∑_l a_k a_l V_{kl}`. -/
def pa_quad {n : ℕ} (V : Fin n → Fin n → ℝ) (a : Fin n → ℝ) : ℝ := ∑ k, ∑ l, a k * a l * V k l

/-- Miao, p. 715: the random vector `X` is (conditionally) jointly Gaussian with mean `μ` and
covariance matrix `V`: every linear combination `∑ a_k X_k` has law `N(a · μ, aᵀ V a)`. -/
def pa_JointGaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (μ : Fin n → ℝ) (V : Fin n → Fin n → ℝ) : Prop :=
  ∀ a : Fin n → ℝ, HasLaw (fun ω => ∑ k, a k * X k ω)
    (gaussianReal (pa_lin μ a) (pa_quad V a).toNNReal) P

/-- A concrete instance of `pa_JointGaussian`: on `(ℝ, N(0, 1))`, the vector `X_k(ω) = b_k ω`
is jointly Gaussian with mean `0` and covariance `V_{kl} = b_k b_l`. -/
theorem pa_jointGaussian_rank_one {n : ℕ} (b : Fin n → ℝ) :
    pa_JointGaussian (gaussianReal 0 1) (fun k ω => b k * ω) (fun _ => 0)
      (fun k l => b k * b l) := by
  intro a
  have hfun : (fun ω : ℝ => ∑ k, a k * (b k * ω)) = fun ω => (∑ k, a k * b k) * ω := by
    funext ω
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hq : pa_quad (fun k l => b k * b l) a = (∑ k, a k * b k) ^ 2 := by
    simp only [pa_quad, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨by fun_prop, ?_⟩
  rw [hfun, gaussianReal_map_const_mul, hq]
  simp only [pa_lin, mul_zero, Finset.sum_const_zero, mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg _)]

/-- Miao, p. 715: Campbell's formula `ln E X = E ln X + ½ Var ln X` for a lognormal `X = e^Y`,
`Y ∼ N(m, v)`: `ln E e^Y = m + v/2 = E Y + ½ Var Y`. -/
theorem pa_log_integral_exp_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : NNReal} (hY : HasLaw Y (gaussianReal m v) P) :
    Real.log (∫ ω, Real.exp (Y ω) ∂P) = m + v / 2 ∧ m + v / 2 = P[Y] + Var[Y; P] / 2 := by
  have h := mgf_gaussianReal hY 1
  simp only [mgf, one_mul, mul_one, one_pow] at h
  refine ⟨by rw [h, Real.log_exp], ?_⟩
  rw [hY.integral_eq, integral_id_gaussianReal, hY.variance_eq, variance_id_gaussianReal]

/-- The expectation of `exp(c + ∑ a_k X_k)` for a jointly Gaussian `X`:
`E exp(c + a · X) = exp(c + a · μ + ½ aᵀ V a)`. -/
theorem pa_integral_exp_lin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} {μ : Fin n → ℝ} {V : Fin n → Fin n → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * X k ω) ∂P = Real.exp (c + pa_lin μ a + pa_quad V a / 2) := by
  have h := mgf_gaussianReal (hG a) 1
  simp only [mgf, one_mul, mul_one, one_pow, Real.coe_toNNReal _ (hV a)] at h
  simp only [Real.exp_add, integral_const_mul]
  rw [h, Real.exp_add, mul_assoc]

/-- Miao, p. 715: an Euler equation `E_t exp(c + a · X) = 1` with jointly Gaussian log
variables holds iff `c + a · μ + ½ aᵀ V a = 0`. -/
theorem pa_lognormal_euler {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} {μ : Fin n → ℝ} {V : Fin n → Fin n → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * X k ω) ∂P = 1 ↔ c + pa_lin μ a + pa_quad V a / 2 = 0 := by
  rw [pa_integral_exp_lin hG hV, Real.exp_eq_one_iff]

theorem pa_lin_three (μ : Fin 3 → ℝ) (a0 a1 a2 : ℝ) :
    pa_lin μ ![a0, a1, a2] = a0 * μ 0 + a1 * μ 1 + a2 * μ 2 := by
  simp only [pa_lin, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem pa_quad_three {V : Fin 3 → Fin 3 → ℝ} (hV : ∀ k l, V k l = V l k) (a0 a1 a2 : ℝ) :
    pa_quad V ![a0, a1, a2] = a0 ^ 2 * V 0 0 + a1 ^ 2 * V 1 1 + a2 ^ 2 * V 2 2
      + 2 * a0 * a1 * V 0 1 + 2 * a2 * a0 * V 2 0 + 2 * a2 * a1 * V 2 1 := by
  simp only [pa_quad, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [hV 1 0, hV 0 2, hV 1 2]
  ring

theorem pa_sum_three (X : Fin 3 → ℝ) (a0 a1 a2 : ℝ) :
    ∑ k, ![a0, a1, a2] k * X k = a0 * X 0 + a1 * X 1 + a2 * X 2 := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- In levels, `β^θ (C'/C)^{−ρθ} R_w^{θ'} R_i^{θ''} = exp(θ ln β − ρθ Δc + θ' r_w + θ'' r_i)`. -/
theorem pa_levels_eq_exp {β : ℝ} (hβ : 0 < β) (θ e0 e1 e2 x0 x1 x2 : ℝ) :
    β ^ θ * Real.exp x0 ^ e0 * Real.exp x1 ^ e1 * Real.exp x2 ^ e2
      = Real.exp (θ * Real.log β + ∑ k, ![e0, e1, e2] k * ![x0, x1, x2] k) := by
  rw [Real.rpow_def_of_pos hβ, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, pa_sum_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring_nf

/-- Miao, p. 715: the log form of (20.26). With `θ = (1 − γ)/(1 − ρ)`, `C'/C = e^{Δc}`,
`R_w = e^{r_w}` and `(Δc, r_w, r_i)` jointly Gaussian,
`0 = θ ln β − ρθ E_t Δc + θ E_t r_w + ½(ρθ)² σ_c² − ρθ·θ σ_cw + ½ θ² σ_w²`. -/
theorem pa_eq_20_26_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ : ℝ} (hβ : 0 < β)
    (h26 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ)) ∂P = 1) :
    0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + (1 - γ) / (1 - ρ) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * V 1 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ θ
      = Real.exp (θ * Real.log β + ∑ k, ![-ρ * θ, θ, 0] k * X k ω) := by
    intro ω
    have := pa_levels_eq_exp hβ θ (-ρ * θ) θ 0 (X 0 ω) (X 1 ω) (X 2 ω)
    rw [Real.rpow_zero, mul_one] at this
    rw [this, pa_sum_three, pa_sum_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  simp only [hpt] at h26
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h26
  linear_combination -h26

/-- Miao, (20.32), p. 715: the log form of (20.28) (riskless asset, `R_f = e^{r_f}` known at
`t`), `0 = r_f + θ ln β − ρθ E_t Δc + (θ − 1) E_t r_w + ½(ρθ)² σ_c² − ρθ(θ − 1) σ_cw
+ ½(θ − 1)² σ_w²`, with `θ − 1 = (ρ − γ)/(1 − ρ)`. -/
theorem eq_20_32 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ rf : ℝ} (hβ : 0 < β)
    (h28 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ) - 1) * Real.exp rf ∂P = 1) :
    0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + ((1 - γ) / (1 - ρ) - 1) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * V 1 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ (θ - 1)
      * Real.exp rf = Real.exp ((rf + θ * Real.log β) + ∑ k, ![-ρ * θ, θ - 1, 0] k * X k ω) := by
    intro ω
    have := pa_levels_eq_exp hβ θ (-ρ * θ) (θ - 1) 0 (X 0 ω) (X 1 ω) (X 2 ω)
    rw [Real.rpow_zero, mul_one] at this
    rw [this, pa_sum_three, pa_sum_three, ← Real.exp_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    ring_nf
  simp only [hpt] at h28
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h28
  linear_combination -h28

/-- Miao, (20.33), p. 716: eliminating `σ_cw` between the log form of (20.26) and (20.32),
`r_f = −ln β + ρ E_t Δc − ½ (γ − ρ)/(1 − ρ) σ_w² − ρ²(1 − γ)/(2(1 − ρ)) σ_c²`. -/
theorem eq_20_33 {β ρ γ rf m0 m1 v00 v01 v11 : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + (1 - γ) / (1 - ρ) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11) :
    rf = -Real.log β + ρ * m0 - 1 / 2 * ((γ - ρ) / (1 - ρ)) * v11
      - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * v00 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  set θ := (1 - γ) / (1 - ρ) with hθ
  have hθ0 : θ ≠ 0 := div_ne_zero h2 h1
  have key : θ * (rf - (-Real.log β + ρ * m0 + 1 / 2 * (θ - 1) * v11
      - ρ ^ 2 * θ / 2 * v00)) = 0 := by
    linear_combination (θ - 1) * hA - θ * hB
  have := (mul_eq_zero.1 key).resolve_left hθ0
  have e1 : θ - 1 = -((γ - ρ) / (1 - ρ)) := by rw [hθ]; field_simp; ring
  have e2 : ρ ^ 2 * θ / 2 = ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) := by rw [hθ]; field_simp
  rw [e1, e2] at this
  linarith

/-- Miao, (20.34), p. 716: the log form of the Euler equation (20.29) for asset `i`,
`0 = E_t r_i + θ ln β − ρθ E_t Δc + (θ − 1) E_t r_w + ½(ρθ)² σ_c² − ρθ(θ − 1)σ_cw
+ ½(θ − 1)² σ_w² + ½ σ_i² − ρθ σ_ic + (θ − 1) σ_iw`. -/
theorem eq_20_34 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin 3 → Ω → ℝ} {μ : Fin 3 → ℝ} {V : Fin 3 → Fin 3 → ℝ}
    (hG : pa_JointGaussian P X μ V) (hV : ∀ a, 0 ≤ pa_quad V a) (hVs : ∀ k l, V k l = V l k)
    {β ρ γ : ℝ} (hβ : 0 < β)
    (h29 : ∫ ω, β ^ ((1 - γ) / (1 - ρ)) * Real.exp (X 0 ω) ^ (-ρ * ((1 - γ) / (1 - ρ)))
      * Real.exp (X 1 ω) ^ ((1 - γ) / (1 - ρ) - 1) * Real.exp (X 2 ω) ^ (1 : ℝ) ∂P = 1) :
    0 = μ 2 + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * μ 0
      + ((1 - γ) / (1 - ρ) - 1) * μ 1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * V 0 0
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * V 0 1
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * V 1 1
      + 1 / 2 * V 2 2 - ρ * ((1 - γ) / (1 - ρ)) * V 2 0
      + ((1 - γ) / (1 - ρ) - 1) * V 2 1 := by
  set θ := (1 - γ) / (1 - ρ)
  have hpt : ∀ ω, β ^ θ * Real.exp (X 0 ω) ^ (-ρ * θ) * Real.exp (X 1 ω) ^ (θ - 1)
      * Real.exp (X 2 ω) ^ (1 : ℝ)
      = Real.exp (θ * Real.log β + ∑ k, ![-ρ * θ, θ - 1, 1] k * X k ω) := by
    intro ω
    rw [pa_levels_eq_exp hβ θ (-ρ * θ) (θ - 1) 1 (X 0 ω) (X 1 ω) (X 2 ω), pa_sum_three,
      pa_sum_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  simp only [hpt] at h29
  rw [pa_lognormal_euler hG hV, pa_lin_three, pa_quad_three hVs] at h29
  linear_combination -h29

/-- Miao, (20.35), p. 716: combining (20.32) and (20.34), the risk premium on asset `i`,
`E_t r_i − r_f + ½ σ_i² = ρ(1 − γ)/(1 − ρ) σ_ic + (γ − ρ)/(1 − ρ) σ_iw`. -/
theorem eq_20_35 {β ρ γ rf m0 m1 m2 v00 v01 v11 v22 v20 v21 : ℝ} (hρ : ρ ≠ 1)
    (h32 : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11)
    (h34 : 0 = m2 + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11
      + 1 / 2 * v22 - ρ * ((1 - γ) / (1 - ρ)) * v20 + ((1 - γ) / (1 - ρ) - 1) * v21) :
    m2 - rf + 1 / 2 * v22 = ρ * (1 - γ) / (1 - ρ) * v20 + (γ - ρ) / (1 - ρ) * v21 := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have e1 : (1 - γ) / (1 - ρ) - 1 = -((γ - ρ) / (1 - ρ)) := by field_simp; ring
  have e2 : ρ * ((1 - γ) / (1 - ρ)) = ρ * (1 - γ) / (1 - ρ) := by ring
  rw [e1, e2] at h32 h34
  linarith

/-- Miao, p. 718: equations (20.33) and (20.35) imply `E_t r_{e,t+1} = μ_e + ρ E_t Δc_{t+1}`
with the asset-specific constant
`μ_e = −ln β − ½(γ−ρ)/(1−ρ) σ_w² − ρ²(1−γ)/(2(1−ρ)) σ_c² − ½σ_e² + ρ(1−γ)/(1−ρ) σ_ec
+ (γ−ρ)/(1−ρ) σ_ew`. -/
theorem pa_expected_equity_return {β ρ γ rf m0 me ve vc vw vec vew : ℝ}
    (h33 : rf = -Real.log β + ρ * m0 - 1 / 2 * ((γ - ρ) / (1 - ρ)) * vw
      - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * vc)
    (h35 : me - rf + 1 / 2 * ve = ρ * (1 - γ) / (1 - ρ) * vec + (γ - ρ) / (1 - ρ) * vew) :
    me = (-Real.log β - 1 / 2 * ((γ - ρ) / (1 - ρ)) * vw - ρ ^ 2 * (1 - γ) / (2 * (1 - ρ)) * vc
      - 1 / 2 * ve + ρ * (1 - γ) / (1 - ρ) * vec + (γ - ρ) / (1 - ρ) * vew) + ρ * m0 := by
  linarith

/-- Miao, p. 716: the weights in (20.35). When `0 < ρ < 1` (EIS above one) and `γ > 1` (so
`γ > ρ`), the weight `ρ(1 − γ)/(1 − ρ)` on `σ_ic` is negative and the weight
`(γ − ρ)/(1 − ρ)` on `σ_iw` is positive. -/
theorem pa_eq_20_35_weights {ρ γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 < γ) :
    ρ * (1 - γ) / (1 - ρ) < 0 ∧ 0 < (γ - ρ) / (1 - ρ) :=
  ⟨div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hρ0 (by linarith)) (by linarith),
    div_pos (by linarith) (by linarith)⟩

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Campbell–Shiller approximation and the return decomposition

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 717–719), equations (20.36)–(20.41).

* (20.36): the exact log return is `r_{t+1} = d_{t+1} − p_t + ln(1 + e^{p_{t+1} − d_{t+1}})`
  (`pa_cs_exact`); `x ↦ ln(1 + eˣ)` has derivative `ϱ = 1/(1 + exp(d̄ − p̄))` at the mean
  `p̄ − d̄` (`pa_cs_hasDerivAt`), its tangent there is `κ + ϱ x` with
  `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)` (`pa_cs_kappa`), and so (20.36) is the first-order Taylor
  expansion, with an error that is `o(p_{t+1} − d_{t+1} − (p̄ − d̄))` (`eq_20_36`).
* (20.38): `eq_20_38` (a rearrangement of (20.36)).
* (20.37): solving forward with the terminal condition `ϱⁿ(p_{t+n} − d_{t+n}) → 0`, path by
  path (`pa_cs_iterate`, `eq_20_37`), and its conditional expectation (`eq_20_37_cond`).
* (20.39): `eq_20_39`, with `E_t`, `E_{t+1}` linear operators on random variables.
* (20.40)–(20.41), the equity volatility accounting with dividends `d_e = λ c` and
  `E_t r_{e,t+1+k} = μ_e + ρ E_t Δc_{t+1+k}`: `eq_20_40`, `eq_20_41` (finite sample space, so
  that conditional expectations commute with the limits of the discounted sums).

Departure: the terminal condition is imposed on the log price–dividend ratio
`ϱⁿ(p_{t+n} − d_{t+n}) → 0` (the text writes `ϱⁱ p_{t+i} → 0`); this is the condition the
forward solution uses.
-/

namespace Miao.RecursiveUtility

open Real Filter Topology Asymptotics

/-- Miao, p. 717: the linearisation coefficient `ϱ = 1/(1 + exp(d̄ − p̄))`, as a function of the
mean log dividend–price ratio `d̄ − p̄`. -/
noncomputable def pa_varrho (dp : ℝ) : ℝ := 1 / (1 + Real.exp dp)

/-- Miao, p. 717: the constant `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)`. -/
noncomputable def pa_kappa (ϱ : ℝ) : ℝ := -Real.log ϱ - (1 - ϱ) * Real.log (1 / ϱ - 1)

theorem pa_varrho_pos (dp : ℝ) : 0 < pa_varrho dp := by
  unfold pa_varrho; positivity

theorem pa_varrho_lt_one (dp : ℝ) : pa_varrho dp < 1 := by
  unfold pa_varrho
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos dp]

/-- Miao, p. 717: the exact identity behind (20.36). With `p = ln P`, `d = ln D`,
`r_{t+1} = ln((P_{t+1} + D_{t+1})/P_t) = d_{t+1} − p_t + ln(1 + exp(p_{t+1} − d_{t+1}))`. -/
theorem pa_cs_exact {P P' D' : ℝ} (hP : 0 < P) (hP' : 0 < P') (hD' : 0 < D') :
    Real.log ((P' + D') / P)
      = Real.log D' - Real.log P + Real.log (1 + Real.exp (Real.log P' - Real.log D')) := by
  rw [Real.exp_sub, Real.exp_log hP', Real.exp_log hD']
  have h1 : (P' + D') / P = D' / P * (1 + P' / D') := by field_simp; ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_div hD'.ne' hP.ne']

/-- Miao, p. 717: the derivative of `x ↦ ln(1 + eˣ)` at `x̄ = p̄ − d̄` is
`ϱ = 1/(1 + exp(d̄ − p̄))`. -/
theorem pa_cs_hasDerivAt (xbar : ℝ) :
    HasDerivAt (fun x => Real.log (1 + Real.exp x)) (pa_varrho (-xbar)) xbar := by
  have h := ((Real.hasDerivAt_exp xbar).const_add 1).log (by positivity)
  convert h using 1
  simp only [pa_varrho, Real.exp_neg]
  have := Real.exp_pos xbar
  field_simp
  ring

/-- Miao, p. 717: the tangent of `x ↦ ln(1 + eˣ)` at `x̄` is `κ + ϱ x`, i.e.
`ln(1 + e^{x̄}) − ϱ x̄ = κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)` with `ϱ = 1/(1 + e^{−x̄})`. -/
theorem pa_cs_kappa (xbar : ℝ) :
    Real.log (1 + Real.exp xbar) - pa_varrho (-xbar) * xbar = pa_kappa (pa_varrho (-xbar)) := by
  have h1 : 1 / pa_varrho (-xbar) - 1 = Real.exp (-xbar) := by
    simp only [pa_varrho]; field_simp; ring
  have h2 : Real.log (1 + Real.exp xbar) = xbar + Real.log (1 + Real.exp (-xbar)) := by
    rw [← Real.log_exp xbar, ← Real.log_mul (by positivity) (by positivity), Real.log_exp]
    congr 1
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  simp only [pa_kappa, h1, Real.log_exp]
  rw [h2]
  simp only [pa_varrho, one_div, Real.log_inv]
  ring

/-- Miao, (20.36), p. 717: the Campbell–Shiller approximation. With `x̄ = p̄ − d̄`,
`ϱ = 1/(1 + exp(d̄ − p̄))` and `κ = −ln ϱ − (1 − ϱ) ln(1/ϱ − 1)`, the exact log return is
`r_{t+1} = κ + ϱ p_{t+1} + (1 − ϱ) d_{t+1} − p_t + e(p_{t+1} − d_{t+1})`, where the error
`e(x) = ln(1 + eˣ) − κ − ϱx` is `o(x − x̄)` as `x → x̄`. -/
theorem eq_20_36 (xbar : ℝ) :
    (∀ p d' p' : ℝ, Real.log ((Real.exp p' + Real.exp d') / Real.exp p)
      = pa_kappa (pa_varrho (-xbar)) + pa_varrho (-xbar) * p' + (1 - pa_varrho (-xbar)) * d' - p
        + (Real.log (1 + Real.exp (p' - d')) - pa_kappa (pa_varrho (-xbar))
          - pa_varrho (-xbar) * (p' - d'))) ∧
    (fun x => Real.log (1 + Real.exp x) - pa_kappa (pa_varrho (-xbar))
      - pa_varrho (-xbar) * x) =o[𝓝 xbar] fun x => x - xbar := by
  refine ⟨fun p d' p' => ?_, ?_⟩
  · rw [pa_cs_exact (Real.exp_pos p) (Real.exp_pos p') (Real.exp_pos d'), Real.log_exp,
      Real.log_exp, Real.log_exp]
    ring
  · have h := (hasDerivAt_iff_isLittleO.1 (pa_cs_hasDerivAt xbar))
    refine h.congr_left fun x => ?_
    rw [← pa_cs_kappa xbar, smul_eq_mul]
    ring

/-- Miao, (20.38), p. 717: (20.36) rewritten as
`r_{t+1} = κ + ϱ(p_{t+1} − d_{t+1}) + Δd_{t+1} + (d_t − p_t)`. -/
theorem eq_20_38 (κ ϱ p d p' d' : ℝ) :
    κ + ϱ * p' + (1 - ϱ) * d' - p = κ + ϱ * (p' - d') + (d' - d) + (d - p) := by ring

/-- Iterating (20.38) forward `n` periods:
`pd_t = ∑_{k<n} ϱᵏ (κ + Δd_{t+1+k} − r_{t+1+k}) + ϱⁿ pd_{t+n}`, `pd = p − d`. -/
theorem pa_cs_iterate {κ ϱ : ℝ} {pd dd r : ℕ → ℝ}
    (h38 : ∀ t, r (t + 1) = κ + ϱ * pd (t + 1) + dd (t + 1) - pd t) (t n : ℕ) :
    pd t = ∑ k ∈ Finset.range n, ϱ ^ k * (κ + dd (t + 1 + k) - r (t + 1 + k))
      + ϱ ^ n * pd (t + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := h38 (t + n)
    rw [show t + n + 1 = t + 1 + n by ring] at h
    rw [ih, Finset.sum_range_succ, show t + (n + 1) = t + 1 + n by ring, h, pow_succ]
    ring

/-- Miao, (20.37), p. 717: solving (20.38) forward under the terminal condition
`ϱⁿ pd_{t+n} → 0`, `pd_t = κ/(1 − ϱ) + ∑_{k≥0} ϱᵏ (Δd_{t+1+k} − r_{t+1+k})` (the partial sums
converge to `pd_t − κ/(1 − ϱ)`), path by path. -/
theorem eq_20_37 {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) {pd dd r : ℕ → ℝ}
    (h38 : ∀ t, r (t + 1) = κ + ϱ * pd (t + 1) + dd (t + 1) - pd t) (t : ℕ)
    (hterm : Tendsto (fun n => ϱ ^ n * pd (t + n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * (dd (t + 1 + k) - r (t + 1 + k))) atTop
      (𝓝 (pd t - κ / (1 - ϱ))) := by
  have hgeom := (hasSum_geometric_of_lt_one hϱ0 hϱ1).tendsto_sum_nat
  have heq : ∀ n, ∑ k ∈ Finset.range n, ϱ ^ k * (dd (t + 1 + k) - r (t + 1 + k))
      = pd t - ϱ ^ n * pd (t + n) - κ * ∑ k ∈ Finset.range n, ϱ ^ k := by
    intro n
    rw [pa_cs_iterate h38 t n, Finset.mul_sum]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have : ∑ k ∈ Finset.range n, ϱ ^ k * κ = ∑ k ∈ Finset.range n, κ * ϱ ^ k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    ring
  simp only [heq]
  have := ((tendsto_const_nhds (x := pd t)).sub hterm).sub (hgeom.const_mul κ)
  convert this using 2
  rw [sub_zero, div_eq_mul_inv]

/-- Miao, (20.37), p. 717, conditional form: for any linear conditional expectation `E_t` that
fixes constants and the time-`t` variable `pd_t`, if the partial sums converge to `Y` on every
path, then `pd_t = κ/(1 − ϱ) + E_t Y`. -/
theorem eq_20_37_cond {Ω : Type*} {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r : ℕ → Ω → ℝ} (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (t : ℕ) (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + n) ω) atTop (𝓝 0))
    (E : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (hE1 : E (fun _ => 1) = fun _ => 1) (hEpd : E (pd t) = pd t)
    {Y : Ω → ℝ} (hY : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n,
      ϱ ^ k * (dd (t + 1 + k) ω - r (t + 1 + k) ω)) atTop (𝓝 (Y ω))) :
    pd t = (fun _ => κ / (1 - ϱ)) + E Y := by
  have hYeq : Y = pd t - (κ / (1 - ϱ)) • fun _ => (1 : ℝ) := by
    funext ω
    have h := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) t (hterm ω)
    rw [tendsto_nhds_unique (hY ω) h]
    simp
  rw [hYeq, map_sub, map_smul, hE1, hEpd]
  funext ω
  simp

/-- Miao, (20.39), p. 717: unexpected returns are revisions in expected dividend growth less
revisions in expected future returns,
`r_{t+1} − E_t r_{t+1}
= (E_{t+1} − E_t) ∑_{k≥0} ϱᵏ Δd_{t+1+k} − (E_{t+1} − E_t) ∑_{k≥1} ϱᵏ r_{t+1+k}`.
`E_t`, `E_{t+1}` are linear, fix constants, `E_{t+1}` fixes the time-`t+1` variables and both
fix `pd_t`; `D` and `Rs` are the path-by-path sums. -/
theorem eq_20_39 {Ω : Type*} {κ ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r : ℕ → Ω → ℝ} (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (t : ℕ) (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + 1 + n) ω) atTop (𝓝 0))
    (E0 E1 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (h11 : E1 (fun _ => 1) = fun _ => 1) (hE0pd : E0 (pd t) = pd t) (hE1pd : E1 (pd t) = pd t)
    (hE1r : E1 (r (t + 1)) = r (t + 1)) {D Rs : Ω → ℝ}
    (hD : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dd (t + 1 + k) ω) atTop
      (𝓝 (D ω)))
    (hRs : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
      (𝓝 (Rs ω))) :
    r (t + 1) - E0 (r (t + 1)) = (E1 D - E0 D) - (E1 Rs - E0 Rs) := by
  -- path by path, `r_{t+1} = κ/(1 − ϱ) + D − Rs − pd_t`
  have hpath : r (t + 1) = (κ / (1 - ϱ)) • (fun _ => (1 : ℝ)) + D - Rs - pd t := by
    funext ω
    have h37 := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) (t + 1) (hterm ω)
    have hshift : Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * dd (t + 2 + k) ω)
        atTop (𝓝 (D ω - dd (t + 1) ω)) := by
      have h := ((hD ω).comp (tendsto_add_atTop_nat 1)).sub_const (dd (t + 1) ω)
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, add_zero, add_sub_cancel_right]
      exact Finset.sum_congr rfl fun k _ => by rw [show t + 1 + (k + 1) = t + 2 + k by ring]
    have hR2 : Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
        (𝓝 ((D ω - dd (t + 1) ω) - ϱ * (pd (t + 1) ω - κ / (1 - ϱ)))) := by
      refine (hshift.sub (h37.const_mul ϱ)).congr fun n => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        rw [show t + 1 + 1 + k = t + 2 + k by ring, pow_succ]; ring
    have hRs' := tendsto_nhds_unique (hRs ω) hR2
    have h1 : (1 : ℝ) - ϱ ≠ 0 := by linarith
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [hRs', h38 ω t]
    field_simp
    ring
  have hlhs : r (t + 1) - E0 (r (t + 1)) = E1 (r (t + 1)) - E0 (r (t + 1)) := by rw [hE1r]
  rw [hlhs, ← LinearMap.sub_apply, hpath]
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, h01, h11, hE0pd, hE1pd]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Miao, (20.40), p. 719: with dividends `d_e = λ c` and expected returns
`E_t r_{e,t+1+k} = μ_e + ρ E_t Δc_{t+1+k}` (from (20.33) and (20.35)), (20.37) becomes
`pd_{e,t} = k_e/(1 − ϱ) + (λ − ρ) E_t ∑_{i≥0} ϱⁱ Δc_{t+1+i}`, `k_e = κ − μ_e`.
The sample space is finite, so `E_t` is continuous. -/
theorem eq_20_40 {Ω : Type*} [Finite Ω] {κ ϱ lam ρ μe : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r dc : ℕ → Ω → ℝ}
    (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (hdd : ∀ t, dd t = lam • dc t) (t : ℕ)
    (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + n) ω) atTop (𝓝 0))
    (E0 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (hE0pd : E0 (pd t) = pd t)
    (hr : ∀ k, E0 (r (t + 1 + k)) = μe • (fun _ => 1) + ρ • E0 (dc (t + 1 + k)))
    {G : Ω → ℝ} (hG : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dc (t + 1 + k) ω)
      atTop (𝓝 (G ω))) :
    pd t = (fun _ => (κ - μe) / (1 - ϱ)) + (lam - ρ) • E0 G := by
  have hc : Continuous E0 := LinearMap.continuous_of_finiteDimensional E0
  set S : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ k • (dd (t + 1 + k) - r (t + 1 + k))
    with hS
  set Gn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ k • dc (t + 1 + k) with hGn
  have hSlim : Tendsto S atTop (𝓝 (pd t - (κ / (1 - ϱ)) • fun _ => (1 : ℝ))) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    have h := eq_20_37 hϱ0 hϱ1 (pd := fun t => pd t ω) (dd := fun t => dd t ω)
      (r := fun t => r t ω) (fun t => h38 ω t) t (hterm ω)
    simp only [hS, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_one]
    exact h
  have hGlim : Tendsto Gn atTop (𝓝 G) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hGn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hG ω
  have hES : ∀ n, E0 (S n) = (lam - ρ) • E0 (Gn n)
      - (μe * ∑ k ∈ Finset.range n, ϱ ^ k) • fun _ => (1 : ℝ) := by
    intro n
    simp only [hS, hGn, map_sum, map_smul, map_sub, hdd, hr]
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
      mul_one, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlim1 := (hc.tendsto _).comp hSlim
  have hgeom := (hasSum_geometric_of_lt_one hϱ0 hϱ1).tendsto_sum_nat
  have hlim2 : Tendsto (fun n => E0 (S n)) atTop
      (𝓝 ((lam - ρ) • E0 G - (μe * (1 - ϱ)⁻¹) • fun _ => (1 : ℝ))) := by
    simp only [hES]
    exact (((hc.tendsto _).comp hGlim).const_smul (lam - ρ)).sub
      ((hgeom.const_mul μe).smul_const _)
  have huniq := tendsto_nhds_unique hlim1 hlim2
  rw [map_sub, map_smul, h01, hE0pd] at huniq
  funext ω
  have := congrFun huniq ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 : ℝ) - ϱ ≠ 0 := by linarith
  field_simp at this ⊢
  linarith

/-- Miao, (20.41), p. 719: with `d_e = λ c` and `E r_{e,t+1+k} = μ_e + ρ E Δc_{t+1+k}` under
both `E_t` and `E_{t+1}` (`k ≥ 1`),
`r_{e,t+1} − E_t r_{e,t+1}
= λ(Δc_{t+1} − E_t Δc_{t+1}) + (λ − ρ)(E_{t+1} − E_t) ∑_{i≥1} ϱⁱ Δc_{t+1+i}`.
-/
theorem eq_20_41 {Ω : Type*} [Finite Ω] {κ ϱ lam ρ μe : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    {pd dd r dc : ℕ → Ω → ℝ}
    (h38 : ∀ ω t, r (t + 1) ω = κ + ϱ * pd (t + 1) ω + dd (t + 1) ω - pd t ω)
    (hdd : ∀ t, dd t = lam • dc t) (t : ℕ)
    (hterm : ∀ ω, Tendsto (fun n => ϱ ^ n * pd (t + 1 + n) ω) atTop (𝓝 0))
    (E0 E1 : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (h01 : E0 (fun _ => 1) = fun _ => 1)
    (h11 : E1 (fun _ => 1) = fun _ => 1) (hE0pd : E0 (pd t) = pd t) (hE1pd : E1 (pd t) = pd t)
    (hE1r : E1 (r (t + 1)) = r (t + 1)) (hE1c : E1 (dc (t + 1)) = dc (t + 1))
    (hr0 : ∀ k, E0 (r (t + 2 + k)) = μe • (fun _ => 1) + ρ • E0 (dc (t + 2 + k)))
    (hr1 : ∀ k, E1 (r (t + 2 + k)) = μe • (fun _ => 1) + ρ • E1 (dc (t + 2 + k)))
    {G1 Rs : Ω → ℝ}
    (hG1 : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * dc (t + 2 + k) ω) atTop
      (𝓝 (G1 ω)))
    (hRs : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) * r (t + 2 + k) ω) atTop
      (𝓝 (Rs ω))) :
    r (t + 1) - E0 (r (t + 1))
      = lam • (dc (t + 1) - E0 (dc (t + 1))) + (lam - ρ) • (E1 G1 - E0 G1) := by
  have hc0 : Continuous E0 := LinearMap.continuous_of_finiteDimensional E0
  have hc1 : Continuous E1 := LinearMap.continuous_of_finiteDimensional E1
  set D : Ω → ℝ := lam • (dc (t + 1) + G1) with hDdef
  have hD : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, ϱ ^ k * dd (t + 1 + k) ω) atTop
      (𝓝 (D ω)) := by
    intro ω
    have h := (((hG1 ω).const_add (dc (t + 1) ω)).const_mul lam).comp
      (tendsto_sub_atTop_nat 1)
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Function.comp_apply, Nat.add_sub_cancel, hdd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, add_zero, mul_add, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by
      rw [show t + 1 + (k + 1) = t + 2 + k by ring]; ring
  have h39 := eq_20_39 hϱ0 hϱ1 h38 t hterm E0 E1 h01 h11 hE0pd hE1pd hE1r hD hRs
  -- revisions of the return sum are `ρ` times revisions of the consumption-growth sum
  set Rn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) • r (t + 2 + k) with hRn
  set Gn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, ϱ ^ (k + 1) • dc (t + 2 + k) with hGn
  have hRlim : Tendsto Rn atTop (𝓝 Rs) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hRn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hRs ω
  have hGlim : Tendsto Gn atTop (𝓝 G1) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    simp only [hGn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hG1 ω
  have hrev : ∀ n, E1 (Rn n) - E0 (Rn n) = ρ • (E1 (Gn n) - E0 (Gn n)) := by
    intro n
    simp only [hRn, hGn, map_sum, map_smul, hr0, hr1, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hl1 : Tendsto (fun n => E1 (Rn n) - E0 (Rn n)) atTop (𝓝 (E1 Rs - E0 Rs)) :=
    ((hc1.tendsto _).comp hRlim).sub ((hc0.tendsto _).comp hRlim)
  have hl2 : Tendsto (fun n => E1 (Rn n) - E0 (Rn n)) atTop (𝓝 (ρ • (E1 G1 - E0 G1))) := by
    simp only [hrev]
    exact (((hc1.tendsto _).comp hGlim).sub ((hc0.tendsto _).comp hGlim)).const_smul ρ
  rw [h39, tendsto_nhds_unique hl1 hl2, hDdef, map_smul, map_smul, map_add, map_add, hE1c]
  funext ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equity volatility and equity premium puzzles with a simple long-run risk process

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 719–722), equations (20.42)–(20.45).

Consumption growth is `Δc_{t+1} = z_t + ε_{c,t+1}`, `z_{t+1} = (1 − φ)g + φ z_t + ε_{z,t+1}`.

* Forecasts: `E_t Δc_{t+1+j} = E_t z_{t+j} = g + φʲ(z_t − g)` (`pa_forecast`, built by iterating
  the conditional mean `pa_forecast_succ`), and the revisions
  `(E_{t+1} − E_t)Δc_{t+1+j} = φ^{j−1} ε_{z,t+1}`, `j ≥ 1` (`pa_forecast_revision`).
* The discounted sums `∑ ϱⁱ E_t Δc_{t+1+i} = g/(1 − ϱ) + (z_t − g)/(1 − ϱφ)`
  (`pa_sum_forecast`) and `∑_{j≥1} ϱʲ φ^{j−1} ε_z = ϱ/(1 − ϱφ) ε_z` (`pa_sum_revision`).
* (20.42)–(20.43): `eq_20_42`, `eq_20_43`; the price–dividend ratio is procyclical when
  `λ > ρ` (`pa_pd_procyclical`); the real consol (`λ = 0`): `pa_consol_yield`,
  `pa_consol_news`, and the printed `λ = 1` is wrong (`pa_consol_lambda_one_counterexample`).
* The equity premium: `σ_iw = σ_ic + (1 − ρ) σ_ig` (`pa_sigma_iw`), the premium
  `E_t r_i − r_f + ½σ_i² = γ σ_ic + (γ − ρ) σ_ig` (`pa_premium_gamma`), the long-run-risk
  covariances (`pa_lrr_cov`), the equity premium (`pa_lrr_equity_premium`), (20.44)
  (`eq_20_44`) and (20.45) (`eq_20_45`). Covariances are Mathlib's `cov[X, Y; P]`.

Departures (see `docs/PA-corrections.md`): the consol bond is `λ = 0` (the text says "setting
`λ = 1`" for the bond formulas, which hold for `λ = 0` only); in the wealth-return news and in
`σ_ig` the revision sum starts at `j = 1` and is discounted by `ϱʲ` (the text writes `∑_{j≥0}`
and `ρⁱ`), as the derivation of the premium formula requires.
-/

namespace Miao.RecursiveUtility

open Real Filter Topology MeasureTheory ProbabilityTheory

/-- Miao, p. 719: the forecast `E_t Δc_{t+1+j} = E_t z_{t+j} = g + φʲ (z_t − g)`. -/
noncomputable def pa_forecast (g φ z : ℝ) (j : ℕ) : ℝ := g + φ ^ j * (z - g)

theorem pa_forecast_zero (g φ z : ℝ) : pa_forecast g φ z 0 = z := by
  simp [pa_forecast]

/-- The forecasts are obtained by iterating the conditional mean of the AR(1) process,
`E_t z_{t+j+1} = (1 − φ) g + φ E_t z_{t+j}` (the law of iterated expectations). -/
theorem pa_forecast_succ (g φ z : ℝ) (j : ℕ) :
    pa_forecast g φ z (j + 1) = (1 - φ) * g + φ * pa_forecast g φ z j := by
  simp only [pa_forecast, pow_succ]
  ring

/-- Miao, p. 721: the revision of the forecast of `Δc_{t+2+j}` between `t` and `t + 1`,
`E_{t+1} Δc_{t+2+j} − E_t Δc_{t+2+j} = φʲ ε_{z,t+1}`, `ε_{z,t+1} = z_{t+1} − (1 − φ)g − φ z_t`. -/
theorem pa_forecast_revision (g φ z z' : ℝ) (j : ℕ) :
    pa_forecast g φ z' j - pa_forecast g φ z (j + 1) = φ ^ j * (z' - (1 - φ) * g - φ * z) := by
  simp only [pa_forecast, pow_succ]
  ring

/-- Miao, p. 719: `∑_{i≥0} ϱⁱ E_t Δc_{t+1+i} = g/(1 − ϱ) + (z_t − g)/(1 − ϱφ)`. -/
theorem pa_sum_forecast {ϱ φ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1) (g z : ℝ) :
    HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  have hab : |ϱ * φ| < 1 := by
    rw [abs_mul, abs_of_nonneg hϱ0]
    calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hφ
  have h1 := (hasSum_geometric_of_lt_one hϱ0 hϱ1).mul_left g
  have h2 := (hasSum_geometric_of_abs_lt_one hab).mul_left (z - g)
  convert h1.add h2 using 1
  · funext i
    simp only [pa_forecast, mul_pow]
    ring
  · simp only [div_eq_mul_inv]

/-- Miao, p. 721: `(E_{t+1} − E_t) ∑_{j≥1} ϱʲ Δc_{t+1+j} = ∑_{j≥0} ϱ^{j+1} φʲ ε_z
= ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem pa_sum_revision {ϱ φ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1) (εz : ℝ) :
    HasSum (fun j : ℕ => ϱ ^ (j + 1) * (φ ^ j * εz)) (ϱ / (1 - ϱ * φ) * εz) := by
  have hab : |ϱ * φ| < 1 := by
    rw [abs_mul, abs_of_nonneg hϱ0]
    calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hφ
  convert (hasSum_geometric_of_abs_lt_one hab).mul_left (ϱ * εz) using 1
  · funext j
    rw [mul_pow, pow_succ]
    ring
  · rw [div_eq_mul_inv]
    ring

/-- Miao, (20.42), p. 719: substituting the long-run risk forecasts into (20.40),
`pe_t − de_t = k_e/(1 − ϱ) + (λ − ρ)(g/(1 − ϱ) + (z_t − g)/(1 − ϱφ))`. -/
theorem eq_20_42 {ϱ φ g z ke lam ρ pd Gbar : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (h40 : pd = ke / (1 - ϱ) + (lam - ρ) * Gbar)
    (hG : HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) Gbar) :
    pd = ke / (1 - ϱ) + (lam - ρ) * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  rw [h40, hG.unique (pa_sum_forecast hϱ0 hϱ1 hφ g z)]

/-- Miao, (20.43), p. 719: substituting the forecast revisions into (20.41),
`r_{e,t+1} − E_t r_{e,t+1} = λ ε_{c,t+1} + (λ − ρ) ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem eq_20_43 {ϱ φ g z z' lam ρ news εc εz Rev : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    (hφ : |φ| < 1) (h41 : news = lam * εc + (lam - ρ) * Rev)
    (hRev : HasSum (fun j : ℕ => ϱ ^ (j + 1) *
      (pa_forecast g φ z' j - pa_forecast g φ z (j + 1))) Rev)
    (hεz : εz = z' - (1 - φ) * g - φ * z) :
    news = lam * εc + (lam - ρ) * (ϱ / (1 - ϱ * φ)) * εz := by
  have h := pa_sum_revision hϱ0 hϱ1 hφ εz
  simp only [pa_forecast_revision, ← hεz] at hRev
  rw [h41, hRev.unique h]
  ring

/-- Miao, p. 719: by (20.42) the price–dividend ratio is procyclical (increasing in `z_t`) when
`λ > ρ`. -/
theorem pa_pd_procyclical {ϱ φ g ke lam ρ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (hlam : ρ < lam) :
    StrictMono fun z : ℝ => ke / (1 - ϱ) + (lam - ρ) * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  have hpos : 0 < 1 - ϱ * φ := by
    have : ϱ * φ ≤ ϱ * |φ| := mul_le_mul_of_nonneg_left (le_abs_self φ) hϱ0
    have : ϱ * |φ| < 1 := by
      calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
        _ < 1 := by rw [one_mul]; exact hφ
    linarith
  intro z₁ z₂ h
  have : (z₁ - g) / (1 - ϱ * φ) < (z₂ - g) / (1 - ϱ * φ) :=
    div_lt_div_of_pos_right (by linarith) hpos
  have := mul_lt_mul_of_pos_left this (sub_pos.2 hlam)
  simp only
  nlinarith

/-- Miao, p. 720: the real consol bond is the claim with `λ = 0`; its log yield is
`y_{bt} = d_{bt} − p_{bt} = −k_b/(1 − ϱ) + ρ(g/(1 − ϱ) + (z_t − g)/(1 − ϱφ))`. -/
theorem pa_consol_yield {ϱ φ g z kb ρ pd Gbar : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (h40 : pd = kb / (1 - ϱ) + (0 - ρ) * Gbar)
    (hG : HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) Gbar) :
    -pd = -(kb / (1 - ϱ)) + ρ * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  rw [eq_20_42 hϱ0 hϱ1 hφ h40 hG]
  ring

/-- Miao, p. 720: the unexpected return on the real consol (`λ = 0`),
`r_{b,t+1} − E_t r_{b,t+1} = −ρ ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem pa_consol_news {ϱ φ g z z' ρ news εc εz Rev : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    (hφ : |φ| < 1) (h41 : news = 0 * εc + (0 - ρ) * Rev)
    (hRev : HasSum (fun j : ℕ => ϱ ^ (j + 1) *
      (pa_forecast g φ z' j - pa_forecast g φ z (j + 1))) Rev)
    (hεz : εz = z' - (1 - φ) * g - φ * z) :
    news = -ρ * (ϱ / (1 - ϱ * φ)) * εz := by
  rw [eq_20_43 hϱ0 hϱ1 hφ h41 hRev hεz]
  ring

/-- Miao, p. 720 (correction): "setting `λ = 1`" in (20.43) does not give the consol news
`−ρ ϱ/(1 − ϱφ) ε_z`: with `ε_c = 1`, `ε_z = 0` the `λ = 1` formula gives `1`. -/
theorem pa_consol_lambda_one_counterexample (ρ K : ℝ) :
    ¬ ∀ εc εz : ℝ, 1 * εc + (1 - ρ) * K * εz = -ρ * K * εz := by
  intro h
  have := h 1 0
  norm_num at this

/-- Miao, p. 720: the wealth portfolio is the case `λ = 1` of (20.41),
`r_w − E_t r_w = (Δc − E_t Δc) + (1 − ρ) G` with `G` the revision of
`∑_{j≥1} ϱʲ Δc_{t+1+j}`; hence for any asset `i`, `σ_iw = σ_ic + (1 − ρ) σ_ig`. -/
theorem pa_sigma_iw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ni εc G : Ω → ℝ} (hni : MemLp ni 2 P) (hεc : MemLp εc 2 P) (hG : MemLp G 2 P) (ρ : ℝ) :
    cov[ni, fun ω => εc ω + (1 - ρ) * G ω; P] = cov[ni, εc; P] + (1 - ρ) * cov[ni, G; P] := by
  rw [show (fun ω => εc ω + (1 - ρ) * G ω) = εc + fun ω => (1 - ρ) * G ω from rfl,
    covariance_add_right hni hεc (hG.const_mul _), covariance_const_mul_right]

/-- Miao, p. 721: substituting `σ_iw = σ_ic + (1 − ρ)σ_ig` into (20.35),
`E_t r_i − r_f + ½σ_i² = γ σ_ic + (γ − ρ) σ_ig`. -/
theorem pa_premium_gamma {ρ γ m rf vi σic σiw σig : ℝ} (hρ : ρ ≠ 1)
    (h35 : m - rf + 1 / 2 * vi = ρ * (1 - γ) / (1 - ρ) * σic + (γ - ρ) / (1 - ρ) * σiw)
    (hσ : σiw = σic + (1 - ρ) * σig) :
    m - rf + 1 / 2 * vi = γ * σic + (γ - ρ) * σig := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  rw [h35, hσ]
  field_simp
  ring

/-- Miao, p. 721: with the long-run risk news `n_e = λ ε_c + (λ − ρ) K ε_z` (20.43),
`K = ϱ/(1 − ϱφ)`, and revision `G = K ε_z`,
`σ_ec = λ σ_c² + (λ − ρ) K σ_cz` and `σ_eg = λ K σ_cz + (λ − ρ) K² σ_z²`. -/
theorem pa_lrr_cov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {εc εz : Ω → ℝ} (hc : MemLp εc 2 P) (hz : MemLp εz 2 P) (lam ρ K : ℝ) :
    cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, εc; P]
        = lam * cov[εc, εc; P] + (lam - ρ) * K * cov[εc, εz; P] ∧
      cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, fun ω => K * εz ω; P]
        = lam * K * cov[εc, εz; P] + (lam - ρ) * K ^ 2 * cov[εz, εz; P] := by
  have hsplit : (fun ω => lam * εc ω + (lam - ρ) * K * εz ω)
      = (fun ω => lam * εc ω) + fun ω => (lam - ρ) * K * εz ω := rfl
  rw [hsplit, covariance_add_left (hc.const_mul _) (hz.const_mul _) hc,
    covariance_add_left (hc.const_mul _) (hz.const_mul _) (hz.const_mul _),
    covariance_const_mul_left, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_right,
    covariance_comm εz εc]
  constructor <;> ring

/-- Miao, p. 721: the equity premium in the long-run risk model,
`E_t r_e − r_f + σ_e²/2 = γ(λσ_c² + (λ − ρ)Kσ_cz) + (γ − ρ)(λKσ_cz + (λ − ρ)K²σ_z²)`. -/
theorem pa_lrr_equity_premium {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {εc εz : Ω → ℝ} (hc : MemLp εc 2 P) (hz : MemLp εz 2 P)
    {lam ρ γ K m rf ve : ℝ}
    (hprem : m - rf + 1 / 2 * ve = γ * cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, εc; P]
      + (γ - ρ) * cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, fun ω => K * εz ω; P]) :
    m - rf + ve / 2 = γ * (lam * cov[εc, εc; P] + (lam - ρ) * K * cov[εc, εz; P])
      + (γ - ρ) * (lam * K * cov[εc, εz; P] + (lam - ρ) * K ^ 2 * cov[εz, εz; P]) := by
  obtain ⟨h1, h2⟩ := pa_lrr_cov hc hz lam ρ K
  rw [h1, h2] at hprem
  linarith

/-- Miao, (20.44), p. 721: the real bond premium (`λ = 0`),
`E_t r_b − r_f + σ_b²/2 = −ργ K σ_cz − (γ − ρ) ρ K² σ_z²`, `K = ϱ/(1 − ϱφ)`. -/
theorem eq_20_44 {ρ γ K mb rf vb vc vcz vz : ℝ}
    (h : mb - rf + vb / 2 = γ * (0 * vc + (0 - ρ) * K * vcz)
      + (γ - ρ) * (0 * K * vcz + (0 - ρ) * K ^ 2 * vz)) :
    mb - rf + vb / 2 = -ρ * γ * K * vcz - (γ - ρ) * ρ * K ^ 2 * vz := by
  linarith

/-- Miao, (20.45), p. 721: the premium of equities over real bonds,
`E_t[r_e − r_b] + σ_e²/2 − σ_b²/2 = γλ(σ_c² + Kσ_cz) + (γ − ρ)λ(Kσ_cz + K²σ_z²)`. -/
theorem eq_20_45 {ρ γ K lam me mb rf ve vb vc vcz vz : ℝ}
    (he : me - rf + ve / 2 = γ * (lam * vc + (lam - ρ) * K * vcz)
      + (γ - ρ) * (lam * K * vcz + (lam - ρ) * K ^ 2 * vz))
    (hb : mb - rf + vb / 2 = γ * (0 * vc + (0 - ρ) * K * vcz)
      + (γ - ρ) * (0 * K * vcz + (0 - ρ) * K ^ 2 * vz)) :
    (me - mb) + ve / 2 - vb / 2
      = γ * lam * (vc + K * vcz) + (γ - ρ) * lam * (K * vcz + K ^ 2 * vz) := by
  linear_combination he - hb

/-- Miao, p. 722: in (20.44) the power-utility term `−ργKσ_cz` is negative when `σ_cz > 0`
(real bonds hedge), and the Epstein–Zin term `−(γ − ρ)ρK²σ_z²` is negative when `γ > ρ`
(a negative term premium). -/
theorem pa_term_premium_signs {ρ γ K vcz vz : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hK : K ≠ 0)
    (hγρ : ρ < γ) (hvz : 0 < vz) :
    (0 < K * vcz → -ρ * γ * K * vcz < 0) ∧ -(γ - ρ) * ρ * K ^ 2 * vz < 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have : 0 < ρ * γ * (K * vcz) := by positivity
    linarith
  · have : 0 < (γ - ρ) * ρ * K ^ 2 * vz := by
      have := sub_pos.2 hγρ
      positivity
    linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lognormal Euler equations with IID standard normal shocks

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 723–729): the Bansal–Yaron shocks
`η_{t+1}, u_{t+1}, e_{t+1}, w_{t+1}` are IID `N(0, 1)`. Here they are `ξ : Fin n → Ω → ℝ`,
independent (`iIndepFun`) with law `N(0, 1)` under the time-`t` conditional probability `P`; a
concrete instance on `ℝⁿ` with the product Gaussian measure is `pa_stdNormal_pi`.

* `E exp(c + ∑ a_k ξ_k) = exp(c + ½ ∑ a_k²)` (`pa_integral_exp_shocks`), hence an Euler
  equation `E_t exp(·) = 1` is `c + ½ ∑ a_k² = 0` (`pa_euler_shocks_iff`).
* `Cov(∑ a_k ξ_k, ∑ b_k ξ_k) = ∑ a_k b_k` (`pa_cov_shocks`).
* The lognormal risk premium: if `m = c_m + a·ξ`, `r = c_r + b·ξ`, `E_t e^{m + r} = 1` and
  `E_t e^{m + r_f} = 1`, then `E_t r − r_f = −Cov_t(m, r) − ½ Var_t(r)`
  (`pa_lognormal_premium`), the step behind (20.53), (20.54) and (20.56).
* The variance of a sum of uncorrelated terms (`pa_cov_sum_uncorrelated`), used for the
  unconditional variances of §20.4.3.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The coordinates of `ℝⁿ` under the product of standard normal laws are IID `N(0, 1)`: a
concrete instance of the hypotheses used in this module. -/
theorem pa_stdNormal_pi (n : ℕ) :
    iIndepFun (fun (k : Fin n) (ω : Fin n → ℝ) => ω k)
        (Measure.pi fun _ => gaussianReal 0 1) ∧
      ∀ k, HasLaw (fun ω : Fin n → ℝ => ω k) (gaussianReal 0 1)
        (Measure.pi fun _ => gaussianReal 0 1) := by
  refine ⟨iIndepFun_pi (X := fun _ x => x) fun _ => aemeasurable_id, fun k => ?_⟩
  exact ⟨(measurable_pi_apply k).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => gaussianReal (0 : ℝ) 1) k).map_eq⟩

/-- `E exp(c + ∑ a_k ξ_k) = exp(c + ½ ∑ a_k²)` for IID standard normal `ξ`. -/
theorem pa_integral_exp_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * ξ k ω) ∂P = Real.exp (c + (∑ k, a k ^ 2) / 2) := by
  have hind' : iIndepFun (fun k ω => a k * ξ k ω) P :=
    hind.comp (fun k x => a k * x) fun k => measurable_const_mul (a k)
  have hmeas : ∀ k, AEMeasurable (fun ω => a k * ξ k ω) P :=
    fun k => (hlaw k).aemeasurable.const_mul (a k)
  have hmgf := hind'.mgf_sum₀ hmeas Finset.univ (t := 1)
  have hsumfun : (∑ k, fun ω => a k * ξ k ω) = fun ω => ∑ k, a k * ξ k ω := by
    funext ω; simp [Finset.sum_apply]
  rw [hsumfun] at hmgf
  have hk : ∀ k, mgf (fun ω => a k * ξ k ω) P 1 = Real.exp (a k ^ 2 / 2) := by
    intro k
    rw [mgf_const_mul, mgf_gaussianReal (hlaw k)]
    simp
  simp only [hk] at hmgf
  simp only [mgf, one_mul] at hmgf
  simp only [Real.exp_add, integral_const_mul]
  rw [hmgf, ← Real.exp_sum, Finset.sum_div]

/-- An Euler equation `E_t exp(c + ∑ a_k ξ_k) = 1` with IID standard normal shocks holds iff
`c + ½ ∑ a_k² = 0`. -/
theorem pa_euler_shocks_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, Real.exp (c + ∑ k, a k * ξ k ω) ∂P = 1 ↔ c + (∑ k, a k ^ 2) / 2 = 0 := by
  rw [pa_integral_exp_shocks hind hlaw, Real.exp_eq_one_iff]

/-- `Cov(∑ a_k ξ_k, ∑ b_k ξ_k) = ∑ a_k b_k` for IID standard normal `ξ`; in particular
`Var(∑ a_k ξ_k) = ∑ a_k²`. -/
theorem pa_cov_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P)
    (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P) (a b : Fin n → ℝ) :
    cov[fun ω => ∑ k, a k * ξ k ω, fun ω => ∑ k, b k * ξ k ω; P] = ∑ k, a k * b k := by
  have hL : ∀ k, MemLp (ξ k) 2 P := fun k => (hlaw k).memLp (memLp_id_gaussianReal 2)
  rw [covariance_fun_sum_fun_sum (fun k => (hL k).const_mul (a k))
    (fun k => (hL k).const_mul (b k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw k).aemeasurable, (hlaw k).variance_eq, variance_id_gaussianReal]
    simp
  · intro l _ hlk
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun (Ne.symm hlk)).covariance_eq_zero (hL k) (hL l)]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The lognormal risk premium (Miao, pp. 726–727): with `m = c_m + a·ξ` (log pricing kernel),
`r = c_r + b·ξ`, the Euler equations `E_t e^{m+r} = 1` and `E_t e^{m+r_f} = 1` give
`E_t r − r_f = −Cov_t(m, r) − ½ Var_t r`, i.e. `c_r − r_f = −∑ a_k b_k − ½ ∑ b_k²`. -/
theorem pa_lognormal_premium {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    {cm cr rf : ℝ} {a b : Fin n → ℝ}
    (hr : ∫ ω, Real.exp ((cm + ∑ k, a k * ξ k ω) + (cr + ∑ k, b k * ξ k ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp ((cm + ∑ k, a k * ξ k ω) + rf) ∂P = 1) :
    cr - rf = -(∑ k, a k * b k) - (∑ k, b k ^ 2) / 2 := by
  have hr' : ∫ ω, Real.exp ((cm + cr) + ∑ k, (a k + b k) * ξ k ω) ∂P = 1 := by
    rw [← hr]
    congr 1
    funext ω
    congr 1
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  have hf' : ∫ ω, Real.exp ((cm + rf) + ∑ k, a k * ξ k ω) ∂P = 1 := by
    rw [← hf]
    congr 1
    funext ω
    congr 1
    ring
  rw [pa_euler_shocks_iff hind hlaw] at hr' hf'
  have : ∑ k, (a k + b k) ^ 2 = ∑ k, a k ^ 2 + 2 * ∑ k, a k * b k + ∑ k, b k ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    exact congrArg₂ _ (congrArg₂ _ rfl (Finset.sum_congr rfl fun k _ => by ring)) rfl
  rw [this] at hr'
  linarith

/-- The variance of a sum of pairwise uncorrelated square-integrable terms is the sum of their
variances: `Cov(∑ Y_k, ∑ Y_k) = ∑ Cov(Y_k, Y_k)`. -/
theorem pa_cov_sum_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    {Y : Fin n → Ω → ℝ} (hY : ∀ k, MemLp (Y k) 2 P)
    (hunc : ∀ k l, k ≠ l → cov[Y k, Y l; P] = 0) :
    cov[fun ω => ∑ k, Y k ω, fun ω => ∑ k, Y k ω; P] = ∑ k, cov[Y k, Y k; P] := by
  rw [covariance_fun_sum_fun_sum hY hY]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hlk => hunc k l (Ne.symm hlk))
    (fun h => absurd (Finset.mem_univ k) h)]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Bansal–Yaron long-run risk model

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 723–729), equations (20.46)–(20.57).

The model: `g_{t+1} = μ + x_t + σ_t η_{t+1}`, `gd_{t+1} = μ_d + φ x_t + φ_d σ_t u_{t+1}`,
`x_{t+1} = ρ_x x_t + φ_e σ_t e_{t+1}`, `σ²_{t+1} = σ̄² + ν₁(σ_t² − σ̄²) + σ_w w_{t+1}`, with
`η, u, e, w` IID `N(0, 1)`. The state is `(x_t, σ_t)` with `σ_t = s > 0`; the shocks are
`ξ 0 = η`, `ξ 1 = e`, `ξ 2 = w`, `ξ 3 = u` (`PAGaussianShocks`). The parameters are bundled
in the data structure `PABansalYaron` (`ρ` is the inverse EIS, `κ₀, κ₁` and `κ₀ₑ, κ₁ₑ` the
Campbell–Shiller constants of the consumption claim and of equity).

* (20.46): `eq_20_46` (exact identity and linearisation, `κ₁ < 1`); the log-linear wealth
  return `pa_by_rw`.
* (20.47)–(20.49): `eq_20_47`, `eq_20_48`; the log kernel `pa_by_m`.
* Price–consumption ratio `z_t = A₀ + A₁ x_t + A₂ σ_t²`: matching coefficients in (20.49)
  (`pa_by_matching_wealth`), `A₁ = (1 − ρ)/(1 − κ₁ρ_x)` (`pa_by_A1`, `pa_by_A1_pos`),
  `A₂` (`pa_by_A2`, `pa_by_A2_neg`, `pa_by_A2_magnified`).
* (20.50): `eq_20_50`, `pa_by_var_rw`. (20.51): `pa_by_Em`, `eq_20_51`, the prices of risk
  and their signs (`pa_by_lam_eta_neg`, `pa_by_lam_e_pos`, `pa_by_lam_w_neg`,
  `pa_by_lam_w_not_pos`, `pa_by_power_utility`). (20.52): `eq_20_52`. (20.53): `eq_20_53`.
* Equity: (20.54) `eq_20_54`, (20.55) `eq_20_55`, the equity news and variance
  (`pa_by_re_news`, `pa_by_var_re`), (20.56) `eq_20_56`, (20.57) and the coefficients
  (`pa_by_matching_equity`, `pa_by_A1e`, `pa_by_A1e_pos`, `pa_by_A2e`), the unconditional
  decomposition and variances (`pa_by_re_decomp`, `pa_by_uncond_var`).
* The riskfree rate (`pa_by_riskfree`, `pa_by_riskfree_final`, `pa_by_riskfree_state`) and its
  volatility (`pa_by_var_riskfree`).

Departures (see `docs/PA-corrections.md`): the market price of volatility risk
`λ_{m,w} = (γ − ρ)/(1 − ρ) A₂ κ₁` is negative, not positive, when `γ > 1 > ρ`
(`pa_by_lam_w_neg`, `pa_by_lam_w_not_pos`); the `x_t` coefficient of `r_{e,t+1} − E r_{e,t+1}`
is `+ρ`, not `−ρ` (`pa_by_re_decomp`); the riskfree-rate equation has `(γ − ρ)/(1 − ρ) E_t r_w`,
not `(ρ − γ)/(1 − ρ) E_t r_w` (`pa_by_riskfree`), and in `Q₁` the term is `+(γ − ρ)/(1 − ρ) B²`
(`pa_by_riskfree_state`); the equity Campbell–Shiller constant is `κ₁ₑ` throughout (the text
mixes `κ₁` and `κ₁ₑ` in (20.55)); `λ_{e,·}` in (20.56) and `Q₁, Q₂` are `λ_{m,·}`; "an
increase in `ν₁` raises `A₂`" means it raises `|A₂|` (`pa_by_A2_magnified`).
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real Filter Topology

/-- The parameters of the Bansal–Yaron model (Miao, p. 723) and the Campbell–Shiller
constants of the consumption claim (`κ₀, κ₁`) and of equity (`κ₀ₑ, κ₁ₑ`). -/
structure PABansalYaron where
  β : ℝ
  ρ : ℝ
  γ : ℝ
  μ : ℝ
  μd : ℝ
  ρx : ℝ
  φe : ℝ
  σbar2 : ℝ
  ν1 : ℝ
  σw : ℝ
  φ : ℝ
  φd : ℝ
  κ0 : ℝ
  κ1 : ℝ
  κ0e : ℝ
  κ1e : ℝ

/-- `θ = (1 − γ)/(1 − ρ)`. -/
noncomputable def pa_by_θ (M : PABansalYaron) : ℝ := (1 - M.γ) / (1 - M.ρ)

/-- Consumption growth `g_{t+1} = μ + x_t + σ_t η_{t+1}`. -/
def pa_by_g (M : PABansalYaron) (x s η : ℝ) : ℝ := M.μ + x + s * η

/-- `x_{t+1} = ρ_x x_t + φ_e σ_t e_{t+1}`. -/
def pa_by_x' (M : PABansalYaron) (x s e : ℝ) : ℝ := M.ρx * x + M.φe * s * e

/-- `σ²_{t+1} = σ̄² + ν₁(σ_t² − σ̄²) + σ_w w_{t+1}`. -/
def pa_by_v' (M : PABansalYaron) (s w : ℝ) : ℝ := M.σbar2 + M.ν1 * (s ^ 2 - M.σbar2) + M.σw * w

/-- Dividend growth `gd_{t+1} = μ_d + φ x_t + φ_d σ_t u_{t+1}`. -/
def pa_by_gd (M : PABansalYaron) (x s u : ℝ) : ℝ := M.μd + M.φ * x + M.φd * s * u

/-- Miao, (20.46), p. 723: the log return on the consumption claim
`r_{w,t+1} = κ₀ + κ₁ z_{t+1} − z_t + g_{t+1}` with `z_t = A₀ + A₁ x_t + A₂ σ_t²`. -/
def pa_by_rw (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) : ℝ :=
  M.κ0 + M.κ1 * (A0 + A1 * pa_by_x' M x s e + A2 * pa_by_v' M s w) - (A0 + A1 * x + A2 * s ^ 2)
    + pa_by_g M x s η

/-- Miao, (20.47), p. 723: the log pricing kernel
`m_{t+1} = θ ln β − ρθ g_{t+1} + (θ − 1) r_{w,t+1}`. -/
noncomputable def pa_by_m (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) : ℝ :=
  pa_by_θ M * Real.log M.β - M.ρ * pa_by_θ M * pa_by_g M x s η
    + (pa_by_θ M - 1) * pa_by_rw M A0 A1 A2 x s η e w

/-- Miao, (20.55), p. 727: the log equity return `r_{e,t+1} = κ₀ₑ + κ₁ₑ z_{e,t+1} − z_{e,t} +
gd_{t+1}` with `z_{e,t} = A₀ₑ + A₁ₑ x_t + A₂ₑ σ_t²`. -/
def pa_by_re (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) : ℝ :=
  M.κ0e + M.κ1e * (A0e + A1e * pa_by_x' M x s e + A2e * pa_by_v' M s w)
    - (A0e + A1e * x + A2e * s ^ 2) + pa_by_gd M x s u

theorem pa_sum_four (a0 a1 a2 a3 : ℝ) (y : Fin 4 → ℝ) :
    ∑ k, ![a0, a1, a2, a3] k * y k = a0 * y 0 + a1 * y 1 + a2 * y 2 + a3 * y 3 := by
  simp [Fin.sum_univ_four]

/-- Matching coefficients: an identity `K₀ + K₁ x + K₂ s² = 0` for all `x` and all `s > 0`
forces `K₀ = K₁ = K₂ = 0`. -/
theorem pa_match_coeffs {K0 K1 K2 : ℝ}
    (h : ∀ x : ℝ, ∀ s : ℝ, 0 < s → K0 + K1 * x + K2 * s ^ 2 = 0) :
    K0 = 0 ∧ K1 = 0 ∧ K2 = 0 := by
  have h1 := h 0 1 one_pos
  have h2 := h 1 1 one_pos
  have h3 := h 0 2 two_pos
  refine ⟨by linarith, by linarith, by linarith⟩

theorem pa_by_θ_sub_one (M : PABansalYaron) (hρ : M.ρ ≠ 1) :
    pa_by_θ M - 1 = (M.ρ - M.γ) / (1 - M.ρ) := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp
  ring

theorem pa_by_θ_mul (M : PABansalYaron) (hρ : M.ρ ≠ 1) : pa_by_θ M * (1 - M.ρ) = 1 - M.γ := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp

/-- The mean of an affine function of the shocks: `E (c + ∑ a_k ξ_k) = c`. -/
theorem pa_integral_affine_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ}
    (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, (c + ∑ k, a k * ξ k ω) ∂P = c := by
  have hI : ∀ k, Integrable (ξ k) P := fun k =>
    memLp_one_iff_integrable.1 ((hlaw k).memLp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top))
  rw [integral_add (integrable_const c) (integrable_finsetSum _ fun k _ => (hI k).const_mul _),
    integral_finsetSum _ fun k _ => (hI k).const_mul _]
  simp only [integral_const_mul, (hlaw _).integral_eq, integral_id_gaussianReal, mul_zero,
    Finset.sum_const_zero, add_zero, integral_const, probReal_univ, one_smul]

/-! ### (20.46)–(20.49) -/

/-- Miao, (20.46), p. 723: with `z = ln(P/C)`, the exact log return on the consumption claim is
`r_{w,t+1} = ln(e^{z_{t+1}} + 1) − z_t + g_{t+1}`; its linearisation at `z̄` has slope
`κ₁ = e^{z̄}/(e^{z̄} + 1) < 1` and intercept `κ₀ = ln(e^{z̄} + 1) − z̄ κ₁`, with an error that is
`o(z_{t+1} − z̄)`. -/
theorem eq_20_46 (zbar : ℝ) :
    (∀ {P P' C C' : ℝ}, 0 < P → 0 < P' → 0 < C → 0 < C' →
      Real.log ((P' + C') / P) = Real.log (Real.exp (Real.log (P' / C')) + 1)
        - Real.log (P / C) + Real.log (C' / C)) ∧
    pa_varrho (-zbar) = Real.exp zbar / (Real.exp zbar + 1) ∧ pa_varrho (-zbar) < 1 ∧
    Real.log (Real.exp zbar + 1) - zbar * pa_varrho (-zbar) = pa_kappa (pa_varrho (-zbar)) ∧
    (fun z => Real.log (Real.exp z + 1) - pa_kappa (pa_varrho (-zbar))
      - pa_varrho (-zbar) * z) =o[𝓝 zbar] fun z => z - zbar := by
  refine ⟨fun {P P' C C'} hP hP' hC hC' => ?_, ?_, pa_varrho_lt_one _, ?_, ?_⟩
  · rw [Real.exp_log (div_pos hP' hC'), Real.log_div hP.ne' hC.ne', Real.log_div hC'.ne' hC.ne',
      Real.log_div (by positivity) hP.ne']
    have : P' / C' + 1 = (P' + C') / C' := by field_simp
    rw [this, Real.log_div (by positivity) hC'.ne']
    ring
  · simp only [pa_varrho, Real.exp_neg]
    have := Real.exp_pos zbar
    field_simp
  · rw [← pa_cs_kappa zbar, add_comm]
    ring
  · have h := (eq_20_36 zbar).2
    refine h.congr_left fun z => ?_
    rw [add_comm]

/-- Miao, (20.47), p. 723: the log of the kernel (20.30) with `C'/C = e^g`, `R_w = e^{r_w}` is
`ln M = (1 − γ)/(1 − ρ) ln β − (1 − γ)ρ/(1 − ρ) g + (ρ − γ)/(1 − ρ) r_w`. -/
theorem eq_20_47 {β ρ γ : ℝ} (hβ : 0 < β) (g r : ℝ) :
    Real.log (pa_Mbar β ρ γ 1 (fun _ : Unit => Real.exp g) (fun _ => Real.exp r) ())
      = (1 - γ) / (1 - ρ) * Real.log β - (1 - γ) * ρ / (1 - ρ) * g
        + (ρ - γ) / (1 - ρ) * r := by
  simp only [pa_Mbar, div_one]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_mul hβ.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_exp, Real.log_exp]
  ring

/-- Miao, (20.48), p. 724: `M_{t+1} R_{i,t+1} = exp(ln M_{t+1} + r_{i,t+1})`, so the Euler
equation `E_t[M R_i] = 1` is `E_t exp(θ ln β − ρθ g + (θ − 1) r_w + r_i) = 1`; for `r_i = r_w`
this is (20.49), `E_t exp(θ ln β − ρθ g + θ r_w) = 1`. -/
theorem eq_20_48 {β ρ γ : ℝ} (hβ : 0 < β) (g r ri : ℝ) :
    pa_Mbar β ρ γ 1 (fun _ : Unit => Real.exp g) (fun _ => Real.exp r) () * Real.exp ri
      = Real.exp ((1 - γ) / (1 - ρ) * Real.log β - (1 - γ) * ρ / (1 - ρ) * g
        + (ρ - γ) / (1 - ρ) * r + ri) := by
  rw [Real.exp_add, ← eq_20_47 hβ g r, Real.exp_log]
  simp only [pa_Mbar, div_one]
  positivity

/-! ### The price–consumption ratio -/

/-- Miao, p. 724: substituting the conjecture `z_t = A₀ + A₁ x_t + A₂ σ_t²` into (20.46) and
(20.49) and matching the coefficients of `x_t` and `σ_t²`:
`−(1 − γ)ρ/(1 − ρ) + (1 − γ)/(1 − ρ)(κ₁A₁ρ_x − A₁ + 1) = 0` and
`0 = (1 − γ)/(1 − ρ)(κ₁ν₁A₂ − A₂) + ½((1 − γ)² + ((1 − γ)/(1 − ρ) A₁κ₁φ_e)²)`. -/
theorem pa_by_matching_wealth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 : ℝ}
    (h49 : ∀ x s : ℝ, 0 < s → ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)) ∂P = 1) :
    -(1 - M.γ) * M.ρ / (1 - M.ρ) + (1 - M.γ) / (1 - M.ρ) * (M.κ1 * A1 * M.ρx - A1 + 1) = 0 ∧
    0 = (1 - M.γ) / (1 - M.ρ) * (M.κ1 * M.ν1 * A2 - A2)
      + 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2) := by
  set θ := pa_by_θ M with hθ
  have hθ1 := pa_by_θ_mul M hρ
  rw [← hθ] at hθ1
  have hpt : ∀ x s : ℝ, 0 < s →
      (θ * Real.log M.β - M.ρ * θ * (M.μ + x) + θ * (M.κ0 + M.κ1 * (A0 + A1 * (M.ρx * x)
        + A2 * (M.σbar2 + M.ν1 * (s ^ 2 - M.σbar2))) - (A0 + A1 * x + A2 * s ^ 2) + M.μ + x))
        + (∑ k, ![θ * (1 - M.ρ) * s, θ * M.κ1 * A1 * M.φe * s, θ * M.κ1 * A2 * M.σw, 0] k ^ 2)
          / 2 = 0 := by
    intro x s hs
    rw [← pa_euler_shocks_iff hind hlaw]
    refine Eq.trans ?_ (h49 x s hs)
    congr 1
    funext ω
    congr 1
    rw [pa_sum_four]
    simp only [pa_by_m, pa_by_rw, pa_by_g, pa_by_x', pa_by_v', ← hθ]
    ring
  have hK := pa_match_coeffs (K0 := θ * Real.log M.β - M.ρ * θ * M.μ + θ * (M.κ0 + M.κ1 * (A0
      + A2 * M.σbar2 * (1 - M.ν1)) - A0 + M.μ) + (θ * M.κ1 * A2 * M.σw) ^ 2 / 2)
    (K1 := -M.ρ * θ + θ * (M.κ1 * A1 * M.ρx - A1 + 1))
    (K2 := θ * (M.κ1 * M.ν1 * A2 - A2) + ((θ * (1 - M.ρ)) ^ 2 + (θ * M.κ1 * A1 * M.φe) ^ 2) / 2)
    (fun x s hs => by
      have := hpt x s hs
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
      linear_combination this)
  obtain ⟨-, hK1, hK2⟩ := hK
  have e1 : -(1 - M.γ) * M.ρ / (1 - M.ρ) = -M.ρ * θ := by rw [hθ, pa_by_θ]; ring
  have e2 : (1 - M.γ) / (1 - M.ρ) = θ := by rw [hθ, pa_by_θ]
  rw [e1, e2, ← hθ1]
  constructor
  · linear_combination hK1
  · linear_combination -hK2

/-- Miao, p. 724: solving the `x_t` equation, `A₁ = (1 − ρ)/(1 − κ₁ρ_x)`. -/
theorem pa_by_A1 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (hγ : M.γ ≠ 1) (hk : M.κ1 * M.ρx ≠ 1)
    {A1 : ℝ}
    (h : -(1 - M.γ) * M.ρ / (1 - M.ρ) + (1 - M.γ) / (1 - M.ρ) * (M.κ1 * A1 * M.ρx - A1 + 1) = 0) :
    A1 = (1 - M.ρ) / (1 - M.κ1 * M.ρx) := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - M.γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h3 : (1 : ℝ) - M.κ1 * M.ρx ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  field_simp at h
  have : (1 - M.γ) * ((1 - M.ρ) - A1 * (1 - M.κ1 * M.ρx)) = 0 := by linear_combination h
  have := (mul_eq_zero.1 this).resolve_left h2
  linarith

/-- Miao, p. 724: `A₁ > 0` when the EIS exceeds one (`ρ < 1`) and `κ₁ρ_x < 1`. -/
theorem pa_by_A1_pos (M : PABansalYaron) (hρ : M.ρ < 1) (hk : M.κ1 * M.ρx < 1) :
    0 < (1 - M.ρ) / (1 - M.κ1 * M.ρx) :=
  div_pos (by linarith) (by linarith)

/-- Miao, p. 724: with CRRA utility and `γ = ρ > 1`, `A₁ < 0`: the price–consumption ratio is
countercyclical. -/
theorem pa_by_A1_neg (M : PABansalYaron) (hρ : 1 < M.ρ) (hk : M.κ1 * M.ρx < 1) :
    (1 - M.ρ) / (1 - M.κ1 * M.ρx) < 0 :=
  div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The closed form `A₂ = ½((1 − γ)² + (θA₁κ₁φ_e)²)/(θ(1 − κ₁ν₁))`, `θ = (1 − γ)/(1 − ρ)`. -/
noncomputable def pa_by_A2formula (M : PABansalYaron) (A1 ν1 : ℝ) : ℝ :=
  1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2)
    / ((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1))

/-- Miao, pp. 724–725: solving the `σ_t²` equation for `A₂`. -/
theorem pa_by_A2 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (hγ : M.γ ≠ 1) (hk : M.κ1 * M.ν1 ≠ 1)
    {A1 A2 : ℝ}
    (h : 0 = (1 - M.γ) / (1 - M.ρ) * (M.κ1 * M.ν1 * A2 - A2)
      + 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2)) :
    A2 = pa_by_A2formula M A1 M.ν1 := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - M.γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h3 : (1 : ℝ) - M.κ1 * M.ν1 ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have hθ : (1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * M.ν1) ≠ 0 :=
    mul_ne_zero (div_ne_zero h2 h1) h3
  simp only [pa_by_A2formula]
  rw [eq_div_iff hθ]
  linear_combination h

/-- Miao, p. 725: if `γ > 1` and `ρ < 1` (and `κ₁ν₁ < 1`), then `A₂ < 0`: a rise in volatility
lowers the price–consumption ratio. -/
theorem pa_by_A2_neg (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hk : M.κ1 * M.ν1 < 1)
    (A1 : ℝ) : pa_by_A2formula M A1 M.ν1 < 0 := by
  simp only [pa_by_A2formula]
  have hθ : (1 - M.γ) / (1 - M.ρ) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  apply div_neg_of_pos_of_neg
  · have : 0 < (1 - M.γ) ^ 2 := by nlinarith
    positivity
  · exact mul_neg_of_neg_of_pos hθ (by linarith)

/-- Miao, p. 725: an increase in `ν₁` magnifies the (negative) effect of volatility on the
price–consumption ratio: for `ν₁ < ν₁'` with `κ₁ν₁' < 1` and `κ₁ > 0`, `A₂(ν₁') < A₂(ν₁) < 0`
(the text's "raises `A₂`" is "raises `|A₂|`"). -/
theorem pa_by_A2_magnified (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hκ : 0 < M.κ1)
    {ν1 ν1' : ℝ} (hν : ν1 < ν1') (hk : M.κ1 * ν1' < 1) (A1 : ℝ) :
    pa_by_A2formula M A1 ν1' < pa_by_A2formula M A1 ν1 := by
  simp only [pa_by_A2formula]
  have hθ : (1 - M.γ) / (1 - M.ρ) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hN : 0 < 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2) := by
    have : 0 < (1 - M.γ) ^ 2 := by nlinarith
    positivity
  have hk' : M.κ1 * ν1 < M.κ1 * ν1' := mul_lt_mul_of_pos_left hν hκ
  have hd1 : 0 < 1 - M.κ1 * ν1' := by linarith
  have hd2 : 1 - M.κ1 * ν1' < 1 - M.κ1 * ν1 := by linarith
  have hD1 : 0 < -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1')) := by
    have := mul_neg_of_neg_of_pos hθ hd1; linarith
  have hD12 : -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1'))
      < -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1)) := by
    have := mul_lt_mul_of_neg_left hd2 hθ; linarith
  have := div_lt_div_of_pos_left hN hD1 hD12
  rw [div_neg, div_neg] at this
  linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Bansal–Yaron model: pricing kernel, risk premia and the riskfree rate

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 725–729), equations (20.50)–(20.57)
and the riskfree rate. The setting and the notation are those of `PALongRunRisk`; the
shocks are `ξ 0 = η`, `ξ 1 = e`, `ξ 2 = w`, `ξ 3 = u`, IID `N(0, 1)` under `P`.

The conditional mean of a variable that is affine in the shocks is its value at zero shocks
(`pa_by_Erw`, `pa_by_Em_integral`, `pa_by_Ere`), and its news is the difference.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- `B = κ₁A₁φ_e` (Miao, (20.50), p. 725). -/
def pa_by_B (M : PABansalYaron) (A1 : ℝ) : ℝ := M.κ1 * A1 * M.φe

/-- The market price of short-run risk `λ_{m,η} = −γ` (Miao, p. 725). -/
def pa_by_lam_eta (M : PABansalYaron) : ℝ := -M.γ

/-- The market price of long-run risk `λ_{m,e} = (γ − ρ)/(1 − ρ) A₁κ₁φ_e` (Miao, p. 725). -/
noncomputable def pa_by_lam_e (M : PABansalYaron) (A1 : ℝ) : ℝ :=
  (M.γ - M.ρ) / (1 - M.ρ) * (A1 * M.κ1 * M.φe)

/-- The market price of volatility risk `λ_{m,w} = (γ − ρ)/(1 − ρ) A₂κ₁` (Miao, p. 725). -/
noncomputable def pa_by_lam_w (M : PABansalYaron) (A2 : ℝ) : ℝ :=
  (M.γ - M.ρ) / (1 - M.ρ) * A2 * M.κ1

/-- `β_{e,e} = κ₁ₑA₁ₑφ_e` (Miao, p. 727). -/
def pa_by_bee (M : PABansalYaron) (A1e : ℝ) : ℝ := M.κ1e * A1e * M.φe

/-- `β_{e,w} = κ₁ₑA₂ₑ` (Miao, p. 727). -/
def pa_by_bew (M : PABansalYaron) (A2e : ℝ) : ℝ := M.κ1e * A2e

theorem pa_by_gamma_rho (M : PABansalYaron) (hρ : M.ρ ≠ 1) :
    (M.γ - M.ρ) / (1 - M.ρ) = 1 - pa_by_θ M := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp
  ring

/-! ### The wealth return (20.50) -/

/-- Miao, (20.50), p. 725: `r_{w,t+1} − E_t r_{w,t+1} = σ_t η + Bσ_t e + A₂κ₁σ_w w`. -/
theorem eq_20_50 (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) :
    pa_by_rw M A0 A1 A2 x s η e w - pa_by_rw M A0 A1 A2 x s 0 0 0
      = s * η + pa_by_B M A1 * s * e + A2 * M.κ1 * M.σw * w := by
  simp only [pa_by_rw, pa_by_x', pa_by_v', pa_by_g, pa_by_B]
  ring

theorem pa_by_rw_affine (M : PABansalYaron) (A0 A1 A2 x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) = pa_by_rw M A0 A1 A2 x s 0 0 0
      + ∑ k, ![s, pa_by_B M A1 * s, A2 * M.κ1 * M.σw, 0] k * ξ k ω := by
  rw [pa_sum_four, ← eq_20_50]
  ring

/-- `E_t r_{w,t+1}` is `r_w` at zero shocks. -/
theorem pa_by_Erw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0 A1 A2 x s : ℝ) :
    ∫ ω, pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) ∂P = pa_by_rw M A0 A1 A2 x s 0 0 0 := by
  simp only [pa_by_rw_affine M A0 A1 A2 x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 725: `Var_t(r_{w,t+1}) = (1 + B²)σ_t² + (A₂κ₁)²σ_w²`. -/
theorem pa_by_var_rw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0 A1 A2 x s : ℝ) :
    cov[fun ω => pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_rw M A0 A1 A2 x s 0 0 0,
      fun ω => pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_rw M A0 A1 A2 x s 0 0 0;
      P] = (1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_rw_affine M A0 A1 A2 x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-! ### The pricing kernel (20.51)–(20.52) -/

/-- Miao, p. 725: `E_t m_{t+1} = m₀ − ρ x_t + A₂(κ₁ν₁ − 1)(ρ − γ)/(1 − ρ) σ_t²`, where
`m₀` is the value at `x_t = σ_t = 0` and `A₁` solves its matching equation. -/
theorem pa_by_Em (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 : ℝ}
    (hA1 : A1 * (1 - M.κ1 * M.ρx) = 1 - M.ρ) (x s : ℝ) :
    pa_by_m M A0 A1 A2 x s 0 0 0 = pa_by_m M A0 A1 A2 0 0 0 0 0 - M.ρ * x
      + A2 * (M.κ1 * M.ν1 - 1) * ((M.ρ - M.γ) / (1 - M.ρ)) * s ^ 2 := by
  rw [← pa_by_θ_sub_one M hρ]
  simp only [pa_by_m, pa_by_rw, pa_by_x', pa_by_v', pa_by_g]
  linear_combination -(pa_by_θ M - 1) * x * hA1

/-- Miao, (20.51), p. 725: the innovation of the log kernel,
`m_{t+1} − E_t m_{t+1} = λ_{m,η}σ_t η − λ_{m,e}σ_t e − λ_{m,w}σ_w w`. -/
theorem eq_20_51 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s η e w : ℝ) :
    pa_by_m M A0 A1 A2 x s η e w - pa_by_m M A0 A1 A2 x s 0 0 0
      = pa_by_lam_eta M * s * η - pa_by_lam_e M A1 * s * e - pa_by_lam_w M A2 * M.σw * w := by
  have hθ1 := pa_by_θ_mul M hρ
  simp only [pa_by_lam_eta, pa_by_lam_e, pa_by_lam_w, pa_by_gamma_rho M hρ]
  simp only [pa_by_m, pa_by_rw, pa_by_x', pa_by_v', pa_by_g]
  linear_combination (s * η) * hθ1

theorem pa_by_m_affine (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) = pa_by_m M A0 A1 A2 x s 0 0 0
      + ∑ k, ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s), -(pa_by_lam_w M A2 * M.σw), 0] k
        * ξ k ω := by
  rw [pa_sum_four, ← sub_eq_iff_eq_add', eq_20_51 M hρ]
  ring

/-- `E_t m_{t+1}` is `m` at zero shocks. -/
theorem pa_by_Em_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) :
    ∫ ω, pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) ∂P = pa_by_m M A0 A1 A2 x s 0 0 0 := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 725: `λ_{m,η} = −γ < 0`. -/
theorem pa_by_lam_eta_neg (M : PABansalYaron) (hγ : 0 < M.γ) : pa_by_lam_eta M < 0 := by
  simp only [pa_by_lam_eta]; linarith

/-- Miao, p. 726: `λ_{m,e} > 0` when the agent prefers early resolution (`γ > ρ`), the EIS
exceeds one (`ρ < 1`) and `A₁κ₁φ_e > 0`. -/
theorem pa_by_lam_e_pos (M : PABansalYaron) (hγρ : M.ρ < M.γ) (hρ : M.ρ < 1) {A1 : ℝ}
    (hA : 0 < A1 * M.κ1 * M.φe) : 0 < pa_by_lam_e M A1 :=
  mul_pos (div_pos (by linarith) (by linarith)) hA

/-- Miao, p. 726 (correction): the market price of volatility risk is negative,
`λ_{m,w} = (γ − ρ)/(1 − ρ) A₂κ₁ < 0`, when `γ > ρ`, `ρ < 1`, `κ₁ > 0` and `A₂ < 0`. -/
theorem pa_by_lam_w_neg (M : PABansalYaron) (hγρ : M.ρ < M.γ) (hρ : M.ρ < 1) (hκ : 0 < M.κ1)
    {A2 : ℝ} (hA2 : A2 < 0) : pa_by_lam_w M A2 < 0 := by
  simp only [pa_by_lam_w]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (div_pos (by linarith) (by linarith)) hA2)
    hκ

/-- Miao, p. 726 (counterexample to "the last two terms are positive"): with `γ > 1 > ρ`,
`κ₁ > 0`, `κ₁ν₁ < 1` and `A₂` from its matching equation, `λ_{m,w}` is not positive. -/
theorem pa_by_lam_w_not_pos (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hκ : 0 < M.κ1)
    (hk : M.κ1 * M.ν1 < 1) (A1 : ℝ) : ¬ 0 < pa_by_lam_w M (pa_by_A2formula M A1 M.ν1) :=
  not_lt.2 (pa_by_lam_w_neg M (by linarith) hρ hκ (pa_by_A2_neg M hρ hγ hk A1)).le

/-- Miao, p. 726: for power utility (`γ = ρ`) `λ_{m,e} = λ_{m,w} = 0`. -/
theorem pa_by_power_utility (M : PABansalYaron) (h : M.γ = M.ρ) (A1 A2 : ℝ) :
    pa_by_lam_e M A1 = 0 ∧ pa_by_lam_w M A2 = 0 := by
  simp [pa_by_lam_e, pa_by_lam_w, h]

/-- Miao, (20.52), p. 726: `Var_t(m_{t+1}) = (λ_{m,η}² + λ_{m,e}²)σ_t² + λ_{m,w}²σ_w²`. -/
theorem eq_20_52 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) :
    cov[fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_m M A0 A1 A2 x s 0 0 0,
      fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_m M A0 A1 A2 x s 0 0 0; P]
      = (pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.53), p. 726: the risk premium on the wealth portfolio. From the Euler equations
for `R_w` and `R_f` under lognormality,
`E_t(r_w − r_f) = −λ_{m,η}σ_t² + λ_{m,e}Bσ_t² + κ₁A₂λ_{m,w}σ_w² − ½Var_t(r_w)`. -/
theorem eq_20_53 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 x s rf : ℝ}
    (hw : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_rw M A0 A1 A2 x s 0 0 0 - rf
      = -pa_by_lam_eta M * s ^ 2 + pa_by_lam_e M A1 * pa_by_B M A1 * s ^ 2
        + M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_rw_affine M A0 A1 A2 x s ξ] at hw hf
  rw [pa_lognormal_premium hind hlaw hw hf]
  simp [Fin.sum_univ_four]
  ring

/-! ### Equity (20.54)–(20.57) -/

/-- Miao, (20.55), p. 727: the Campbell–Shiller form of the equity return,
`r_{e,t+1} = gd_{t+1} + κ₁ₑA₁ₑx_{t+1} − A₁ₑx_t + κ₁ₑA₂ₑσ²_{t+1} − A₂ₑσ_t² + constant`. -/
theorem eq_20_55 (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u = pa_by_gd M x s u + M.κ1e * A1e * pa_by_x' M x s e
      - A1e * x + M.κ1e * A2e * pa_by_v' M s w - A2e * s ^ 2
      + (M.κ0e + M.κ1e * A0e - A0e) := by
  simp only [pa_by_re]
  ring

/-- Miao, p. 727: `r_{e,t+1} − E_t r_{e,t+1} = φ_dσ_t u + β_{e,e}σ_t e + β_{e,w}σ_w w`. -/
theorem pa_by_re_news (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u - pa_by_re M A0e A1e A2e x s 0 0 0
      = M.φd * s * u + pa_by_bee M A1e * s * e + pa_by_bew M A2e * M.σw * w := by
  simp only [pa_by_re, pa_by_x', pa_by_v', pa_by_gd, pa_by_bee, pa_by_bew]
  ring

theorem pa_by_re_affine (M : PABansalYaron) (A0e A1e A2e x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω) = pa_by_re M A0e A1e A2e x s 0 0 0
      + ∑ k, ![0, pa_by_bee M A1e * s, pa_by_bew M A2e * M.σw, M.φd * s] k * ξ k ω := by
  rw [pa_sum_four, ← sub_eq_iff_eq_add', pa_by_re_news]
  ring

/-- `E_t r_{e,t+1}` is `r_e` at zero shocks. -/
theorem pa_by_Ere {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0e A1e A2e x s : ℝ) :
    ∫ ω, pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω) ∂P
      = pa_by_re M A0e A1e A2e x s 0 0 0 := by
  simp only [pa_by_re_affine M A0e A1e A2e x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 727: `Var_t(r_{e,t+1}) = (φ_d² + β_{e,e}²)σ_t² + β_{e,w}²σ_w²`. -/
theorem pa_by_var_re {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0e A1e A2e x s : ℝ) :
    cov[fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
        - pa_by_re M A0e A1e A2e x s 0 0 0,
      fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
        - pa_by_re M A0e A1e A2e x s 0 0 0; P]
      = (M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2 + pa_by_bew M A2e ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_re_affine M A0e A1e A2e x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.54), p. 726: from `E_t[M(R_e − R_f)] = 0` under lognormality,
`E_t(r_e − r_f) + ½Var_t(r_e) = −Cov_t(m − E_t m, r_e − E_t r_e)`. -/
theorem eq_20_54 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e x s rf : ℝ}
    (he : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_re M A0e A1e A2e x s 0 0 0 - rf
      + 1 / 2 * ((M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2 + pa_by_bew M A2e ^ 2 * M.σw ^ 2)
      = -cov[fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
            - pa_by_m M A0 A1 A2 x s 0 0 0,
          fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
            - pa_by_re M A0e A1e A2e x s 0 0 0; P] := by
  have : IsProbabilityMeasure P := inferInstance
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_re_affine M A0e A1e A2e x s ξ, add_sub_cancel_left] at he hf ⊢
  rw [pa_cov_shocks hind hlaw, pa_lognormal_premium hind hlaw he hf]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.56), p. 727: the conditional equity premium,
`E_t(r_e − r_f) = β_{e,e}λ_{m,e}σ_t² + β_{e,w}λ_{m,w}σ_w² − ½Var_t(r_e)` (the text's
`λ_{e,e}, λ_{e,w}` are `λ_{m,e}, λ_{m,w}`). -/
theorem eq_20_56 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e x s rf : ℝ}
    (he : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_re M A0e A1e A2e x s 0 0 0 - rf
      = pa_by_bee M A1e * pa_by_lam_e M A1 * s ^ 2 + pa_by_bew M A2e * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2
          + pa_by_bew M A2e ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_re_affine M A0e A1e A2e x s ξ] at he hf
  rw [pa_lognormal_premium hind hlaw he hf]
  simp [Fin.sum_univ_four]
  ring

/-- `H_e = λ_{m,η}² + (−λ_{m,e} + β_{e,e})² + φ_d²` (Miao, p. 728). -/
noncomputable def pa_by_He (M : PABansalYaron) (A1 A1e : ℝ) : ℝ :=
  pa_by_lam_eta M ^ 2 + (-pa_by_lam_e M A1 + pa_by_bee M A1e) ^ 2 + M.φd ^ 2

/-- Miao, (20.57), p. 728: substituting (20.46) and (20.55) into the Euler equation for equity
and matching the coefficients of `x_t` and `σ_t²`:
`−ρ + κ₁ₑA₁ₑρ_x − A₁ₑ + φ = 0` and
`(ρ − γ)/(1 − ρ) A₂(κ₁ν₁ − 1) + A₂ₑ(κ₁ₑν₁ − 1) + H_e/2 = 0`. -/
theorem pa_by_matching_equity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e : ℝ}
    (hA1 : A1 * (1 - M.κ1 * M.ρx) = 1 - M.ρ)
    (h57 : ∀ x s : ℝ, 0 < s → ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1) :
    -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0 ∧
    (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2 = 0 := by
  have hpt : ∀ x s : ℝ, 0 < s →
      (pa_by_m M A0 A1 A2 x s 0 0 0 + pa_by_re M A0e A1e A2e x s 0 0 0)
        + (∑ k, ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s) + pa_by_bee M A1e * s,
          -(pa_by_lam_w M A2 * M.σw) + pa_by_bew M A2e * M.σw, M.φd * s] k ^ 2) / 2 = 0 := by
    intro x s hs
    rw [← pa_euler_shocks_iff hind hlaw]
    refine Eq.trans ?_ (h57 x s hs)
    congr 1
    funext ω
    congr 1
    rw [pa_by_m_affine M hρ A0 A1 A2 x s ξ ω, pa_by_re_affine M A0e A1e A2e x s ξ ω,
      pa_sum_four, pa_sum_four, pa_sum_four]
    ring
  set m0 := pa_by_m M A0 A1 A2 0 0 0 0 0
  have hK := pa_match_coeffs (K0 := m0 + (M.κ0e + M.κ1e * (A0e + A2e * M.σbar2 * (1 - M.ν1))
      - A0e + M.μd) + ((-(pa_by_lam_w M A2) + pa_by_bew M A2e) * M.σw) ^ 2 / 2)
    (K1 := -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ)
    (K2 := (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2)
    (fun x s hs => by
      have := hpt x s hs
      rw [pa_by_Em M hρ hA1 x s] at this
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
        pa_by_re, pa_by_x', pa_by_v', pa_by_gd] at this
      simp only [pa_by_He]
      linear_combination this)
  exact ⟨hK.2.1, hK.2.2⟩

/-- Miao, p. 728: `A₁ₑ = (φ − ρ)/(1 − κ₁ₑρ_x)`. -/
theorem pa_by_A1e (M : PABansalYaron) (hk : M.κ1e * M.ρx ≠ 1) {A1e : ℝ}
    (h : -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0) :
    A1e = (M.φ - M.ρ) / (1 - M.κ1e * M.ρx) := by
  have h3 : (1 : ℝ) - M.κ1e * M.ρx ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  linarith

/-- Miao, p. 728: the price–dividend ratio is procyclical, `A₁ₑ > 0`, when `φ > ρ` (with
`κ₁ₑρ_x < 1`); e.g. when the EIS exceeds one and `φ ≥ 1`. -/
theorem pa_by_A1e_pos (M : PABansalYaron) (hφ : M.ρ < M.φ) (hk : M.κ1e * M.ρx < 1) :
    0 < (M.φ - M.ρ) / (1 - M.κ1e * M.ρx) :=
  div_pos (by linarith) (by linarith)

/-- Miao, p. 728: `A₂ₑ = ((γ − ρ)/(1 − ρ) A₂(1 − κ₁ν₁) + ½H_e)/(1 − κ₁ₑν₁)`. -/
theorem pa_by_A2e (M : PABansalYaron) (hk : M.κ1e * M.ν1 ≠ 1) {A1 A2 A1e A2e : ℝ}
    (h : (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2 = 0) :
    A2e = ((M.γ - M.ρ) / (1 - M.ρ) * A2 * (1 - M.κ1 * M.ν1) + 1 / 2 * pa_by_He M A1 A1e)
      / (1 - M.κ1e * M.ν1) := by
  have h3 : (1 : ℝ) - M.κ1e * M.ν1 ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  have e : (M.ρ - M.γ) / (1 - M.ρ) = -((M.γ - M.ρ) / (1 - M.ρ)) := by ring
  rw [e] at h
  linarith

/-! ### Unconditional moments -/

/-- Miao, p. 728: with `A₁ₑ` from (20.57), the equity return is
`r_{e,t+1} = c + ρ x_t + A₂ₑ(ν₁κ₁ₑ − 1)σ_t² + β_{e,e}σ_t e + φ_dσ_t u + β_{e,w}σ_w w`;
the coefficient of `x_t` is `+ρ` (the text prints `−ρ`). -/
theorem pa_by_re_decomp (M : PABansalYaron) {A0e A1e A2e : ℝ}
    (hA1e : -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0) (x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u = pa_by_re M A0e A1e A2e 0 0 0 0 0 + M.ρ * x
      + A2e * (M.ν1 * M.κ1e - 1) * s ^ 2 + pa_by_bee M A1e * s * e + M.φd * s * u
      + pa_by_bew M A2e * M.σw * w := by
  simp only [pa_by_re, pa_by_x', pa_by_v', pa_by_gd, pa_by_bee, pa_by_bew]
  linear_combination x * hA1e

/-- The variance of a linear combination of pairwise uncorrelated variables,
`Var(∑ a_k Z_k) = ∑ a_k² Var Z_k`. -/
theorem pa_cov_lin_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {Z : Fin n → Ω → ℝ} (hZ : ∀ k, MemLp (Z k) 2 P)
    (hunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0) (a : Fin n → ℝ) :
    cov[fun ω => ∑ k, a k * Z k ω, fun ω => ∑ k, a k * Z k ω; P]
      = ∑ k, a k ^ 2 * cov[Z k, Z k; P] := by
  rw [pa_cov_sum_uncorrelated (Y := fun k ω => a k * Z k ω) (fun k => (hZ k).const_mul _)
    (fun k l hkl => by
      rw [covariance_const_mul_left, covariance_const_mul_right, hunc k l hkl, mul_zero,
        mul_zero])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Miao, p. 728: the unconditional variances of the equity return and of the price–dividend
ratio. With `Z = (x_t, σ_t e, σ_t u, σ_t² − Eσ_t², w)` pairwise uncorrelated,
`Var(σ_t e) = Var(σ_t u) = σ̄²`, `Var w = 1`:
`Var(r_e) = ρ²Var(x) + (β_{e,e}² + φ_d²)σ̄² + (A₂ₑ(ν₁κ₁ₑ − 1))²Var(σ²) + β_{e,w}²σ_w²`, and,
with `x_t, σ_t²` uncorrelated, `Var(z_e) = A₁ₑ²Var(x) + A₂ₑ²Var(σ²)`. -/
theorem pa_by_uncond_var {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : PABansalYaron) (A1e A2e : ℝ) {Z : Fin 5 → Ω → ℝ}
    (hZ : ∀ k, MemLp (Z k) 2 P) (hunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0)
    (h1 : cov[Z 1, Z 1; P] = M.σbar2) (h2 : cov[Z 2, Z 2; P] = M.σbar2)
    (h4 : cov[Z 4, Z 4; P] = 1) :
    cov[fun ω => M.ρ * Z 0 ω + pa_by_bee M A1e * Z 1 ω + M.φd * Z 2 ω
        + A2e * (M.ν1 * M.κ1e - 1) * Z 3 ω + pa_by_bew M A2e * M.σw * Z 4 ω,
      fun ω => M.ρ * Z 0 ω + pa_by_bee M A1e * Z 1 ω + M.φd * Z 2 ω
        + A2e * (M.ν1 * M.κ1e - 1) * Z 3 ω + pa_by_bew M A2e * M.σw * Z 4 ω; P]
      = M.ρ ^ 2 * cov[Z 0, Z 0; P] + (pa_by_bee M A1e ^ 2 + M.φd ^ 2) * M.σbar2
        + (A2e * (M.ν1 * M.κ1e - 1)) ^ 2 * cov[Z 3, Z 3; P]
        + pa_by_bew M A2e ^ 2 * M.σw ^ 2 ∧
    cov[fun ω => A1e * Z 0 ω + A2e * Z 3 ω, fun ω => A1e * Z 0 ω + A2e * Z 3 ω; P]
      = A1e ^ 2 * cov[Z 0, Z 0; P] + A2e ^ 2 * cov[Z 3, Z 3; P] := by
  constructor
  · have h := pa_cov_lin_uncorrelated hZ hunc
      ![M.ρ, pa_by_bee M A1e, M.φd, A2e * (M.ν1 * M.κ1e - 1), pa_by_bew M A2e * M.σw]
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons] at h
    rw [h, h1, h2, h4]
    ring
  · have h := pa_cov_lin_uncorrelated hZ hunc ![A1e, 0, 0, A2e, 0]
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h
    exact h

/-! ### The riskfree rate -/

/-- Miao, p. 729: from `E_t[M R_f] = 1`,
`r_f = −(1 − γ)/(1 − ρ) ln β + (1 − γ)ρ/(1 − ρ) E_t g + (γ − ρ)/(1 − ρ) E_t r_w − ½Var_t(m)`
(the text prints `(ρ − γ)/(1 − ρ) E_t r_w`). -/
theorem pa_by_riskfree {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 x s rf : ℝ}
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    rf = -((1 - M.γ) / (1 - M.ρ)) * Real.log M.β + (1 - M.γ) * M.ρ / (1 - M.ρ) * (M.μ + x)
      + (M.γ - M.ρ) / (1 - M.ρ) * pa_by_rw M A0 A1 A2 x s 0 0 0
      - 1 / 2 * ((pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ] at hf
  have hf' : ∫ ω, Real.exp ((pa_by_m M A0 A1 A2 x s 0 0 0 + rf) + ∑ k,
      ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s), -(pa_by_lam_w M A2 * M.σw), 0] k
        * ξ k ω) ∂P = 1 := by
    refine Eq.trans ?_ hf
    congr 1
    funext ω
    congr 1
    ring
  rw [pa_euler_shocks_iff hind hlaw] at hf'
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hf'
  rw [pa_by_gamma_rho M hρ]
  simp only [pa_by_m, pa_by_g, pa_by_θ] at hf' ⊢
  linear_combination hf'

/-- Miao, p. 729: subtracting `(1 − θ) r_f` from both sides,
`r_f = −ln β + ρE_t g + (γ − ρ)/(1 − γ) E_t[r_w − r_f] − (1 − ρ)/(2(1 − γ)) Var_t(m)`. -/
theorem pa_by_riskfree_final {β ρ γ rf Eg Erw Vm : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (h : rf = -((1 - γ) / (1 - ρ)) * Real.log β + (1 - γ) * ρ / (1 - ρ) * Eg
      + (γ - ρ) / (1 - ρ) * Erw - 1 / 2 * Vm) :
    rf = -Real.log β + ρ * Eg + (γ - ρ) / (1 - γ) * (Erw - rf)
      - (1 - ρ) / (2 * (1 - γ)) * Vm := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  field_simp at h ⊢
  linear_combination h

/-- Miao, p. 729: `λ_{m,e} B = (γ − ρ)/(1 − ρ) B²`. -/
theorem pa_by_lam_e_B (M : PABansalYaron) (A1 : ℝ) :
    pa_by_lam_e M A1 * pa_by_B M A1 = (M.γ - M.ρ) / (1 - M.ρ) * pa_by_B M A1 ^ 2 := by
  simp only [pa_by_lam_e, pa_by_B]
  ring

/-- Miao, p. 729: the riskfree rate as a function of the state,
`r_f = R₀ + ρ x_t + ((γ − ρ)/(1 − γ) Q₁ − (1 − ρ)/(2(1 − γ)) Q₂) σ_t²` with
`Q₁ = −λ_{m,η} + (γ − ρ)/(1 − ρ) B² − ½(1 + B²)` (the time-varying part of the wealth premium
(20.53); the text prints `(ρ − γ)/(1 − ρ) B²`) and `Q₂ = λ_{m,η}² + λ_{m,e}²`. -/
theorem pa_by_riskfree_state (M : PABansalYaron) {A1 A2 rf x s Erw : ℝ}
    (hfin : rf = -Real.log M.β + M.ρ * (M.μ + x) + (M.γ - M.ρ) / (1 - M.γ) * (Erw - rf)
      - (1 - M.ρ) / (2 * (1 - M.γ)) * ((pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2))
    (h53 : Erw - rf = -pa_by_lam_eta M * s ^ 2 + pa_by_lam_e M A1 * pa_by_B M A1 * s ^ 2
        + M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2)) :
    rf = (-Real.log M.β + M.ρ * M.μ
        + (M.γ - M.ρ) / (1 - M.γ) * (M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
          - 1 / 2 * (A2 * M.κ1) ^ 2 * M.σw ^ 2)
        - (1 - M.ρ) / (2 * (1 - M.γ)) * (pa_by_lam_w M A2 ^ 2 * M.σw ^ 2))
      + M.ρ * x
      + ((M.γ - M.ρ) / (1 - M.γ) * (-pa_by_lam_eta M + (M.γ - M.ρ) / (1 - M.ρ) * pa_by_B M A1 ^ 2
          - 1 / 2 * (1 + pa_by_B M A1 ^ 2))
        - (1 - M.ρ) / (2 * (1 - M.γ)) * (pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2)) * s ^ 2 := by
  rw [pa_by_lam_e_B] at h53
  rw [hfin, h53]
  ring

/-- Miao, p. 729: the volatility of the riskfree rate. If `r_f = R₀ + ρ x_t + c σ_t²` with
`x_t` and `σ_t²` uncorrelated, `Var(r_f) = ρ²Var(x) + c²Var(σ²)`. -/
theorem pa_by_var_riskfree {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X V : Ω → ℝ} (hX : MemLp X 2 P) (hV : MemLp V 2 P)
    (hXV : cov[X, V; P] = 0) (ρ c : ℝ) :
    cov[fun ω => ρ * X ω + c * V ω, fun ω => ρ * X ω + c * V ω; P]
      = ρ ^ 2 * cov[X, X; P] + c ^ 2 * cov[V, V; P] := by
  have h := pa_cov_lin_uncorrelated (Z := ![X, V]) (fun k => by fin_cases k <;> assumption)
    (fun k l hkl => by
      fin_cases k <;> fin_cases l
      · exact absurd rfl hkl
      · exact hXV
      · rw [covariance_comm]; exact hXV
      · exact absurd rfl hkl) ![ρ, c]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pareto optimality with recursive utility: the utility possibility set

Miao, *Economic Dynamics in Discrete Time*, §20.5 (pp. 729–731), Lemma 20.5.1, Definition 20.5.1,
the Negishi problem (20.58)–(20.59) and Lemma 20.5.2.

The economy: `n` agents, consumption plans in `ι → ℝ` (`ι` finite: the dates and states of a
finite event tree, or the continuation plans from date 1 on), consumption set `C = {c ≥ 0}`,
aggregate endowment `e ≥ 0`, utilities `U i : (ι → ℝ) → ℝ`. The feasible allocations are
`pa_feasible e` (`C(e)`), the plain utility possibility set is `pa_U0 U e`
(`U₀(e) = {(U¹(c¹), …, Uⁿ(cⁿ)) : c ∈ C(e)}`), and its comprehensive hull is `pa_U0bar U e`
(`{u : u ≤ U(c) for some c ∈ C(e)}`). The simplex `Δⁿ` is `pa_simplex n`, and the value of the
Negishi problem (20.58) is `pa_Vhat`.

* Definition 20.5.1: `definition_20_5_1` (Pareto optimality, `pa_ParetoOptimal`).
* Lemma 20.5.1: the hull is convex, closed and satisfies free disposal when the utilities are
  concave and continuous (`lemma_20_5_1`); the plain set is closed (compact) but does not
  satisfy free disposal in general (`lemma_20_5_1_plain_closed`,
  `lemma_20_5_1_counterexample`).
* Lemma 20.5.2: for a convex, closed, comprehensive, nonempty set with bounded support values,
  `v ∈ U ↔ ∀ θ ∈ Δⁿ, θ · v ≤ V̂(θ)` (`pa_mem_iff_support`, proved by the separation theorem as
  in the text), and so `v ∈ Ū₀(e) ↔ min_θ (V̂(e, θ) − θ · v) ≥ 0` (`lemma_20_5_2`); with the
  plain set `U₀(e)` the "if" direction fails (`lemma_20_5_2_counterexample`).

Departure (see `docs/PA-corrections.md`): Lemma 20.5.1's free disposal, and hence Lemma 20.5.2,
hold for the comprehensive set `Ū₀(e) = U₀(e) − ℝⁿ₊`, not for `U₀(e)` itself; Lemma 20.5.1 also
needs concave, continuous utilities (convexity, closedness), which the text leaves implicit.
-/

namespace Miao.RecursiveUtility

open Set
open scoped Pointwise

/-- The simplex of Pareto weights `Δⁿ = {θ ∈ ℝⁿ₊ : ∑ θᵢ = 1}` (Miao, p. 730). -/
def pa_simplex (n : ℕ) : Set (Fin n → ℝ) := {θ | (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1}

/-- The weighted sum `θ · v = ∑ θᵢ vᵢ`. -/
def pa_dot {n : ℕ} (θ v : Fin n → ℝ) : ℝ := ∑ i, θ i * v i

/-- The support value `V̂(θ) = sup_{z ∈ U} θ · z` of a utility possibility set. -/
noncomputable def pa_Vhat {n : ℕ} (U : Set (Fin n → ℝ)) (θ : Fin n → ℝ) : ℝ :=
  sSup ((pa_dot θ) '' U)

/-- Free disposal: `u ≤ u' ∈ U ⟹ u ∈ U` (Miao, Lemma 20.5.1). -/
def pa_FreeDisposal {n : ℕ} (U : Set (Fin n → ℝ)) : Prop := ∀ u u', u ≤ u' → u' ∈ U → u ∈ U

/-- The feasible allocations `C(e) = {(c¹, …, cⁿ) : cⁱ ≥ 0, ∑ cⁱ ≤ e}` (Miao, p. 730). -/
def pa_feasible {n : ℕ} {ι : Type*} (e : ι → ℝ) : Set (Fin n → ι → ℝ) :=
  {c | (∀ i, 0 ≤ c i) ∧ ∑ i, c i ≤ e}

/-- The utility profile `(U¹(c¹), …, Uⁿ(cⁿ))`. -/
def pa_uvec {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (c : Fin n → ι → ℝ) : Fin n → ℝ :=
  fun i => U i (c i)

/-- The utility possibility set `U₀(e)` (Miao, p. 730). -/
def pa_U0 {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ) : Set (Fin n → ℝ) :=
  pa_uvec U '' pa_feasible e

/-- The comprehensive utility possibility set `Ū₀(e) = {u : ∃ c ∈ C(e), u ≤ U(c)}`. -/
def pa_U0bar {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ c ∈ pa_feasible e, u ≤ pa_uvec U c}

/-- Pareto optimality for an abstract set of feasible allocations and utility functions. -/
def pa_ParetoOptimal {α : Type*} {n : ℕ} (F : Set α) (U : Fin n → α → ℝ) (c : α) : Prop :=
  c ∈ F ∧ ¬ ∃ c' ∈ F, (∀ i, U i c ≤ U i c') ∧ ∃ j, U j c < U j c'

/-- **Definition 20.5.1** (Miao, p. 730). An allocation `c ∈ C(e)` is Pareto optimal iff there
is no feasible `ĉ` with `Uⁱ(ĉⁱ) ≥ Uⁱ(cⁱ)` for all `i` and `Uʲ(ĉʲ) > Uʲ(cʲ)` for some `j`. -/
theorem definition_20_5_1 {n : ℕ} {ι : Type*} (U : Fin n → (ι → ℝ) → ℝ) (e : ι → ℝ)
    (c : Fin n → ι → ℝ) :
    pa_ParetoOptimal (pa_feasible e) (fun i c => U i (c i)) c ↔ c ∈ pa_feasible e ∧
      ¬ ∃ ĉ ∈ pa_feasible e, (∀ i, U i (c i) ≤ U i (ĉ i)) ∧ ∃ j, U j (c j) < U j (ĉ j) :=
  Iff.rfl

/-- Miao, (20.58)–(20.59), p. 730: a solution of the Negishi problem with strictly positive
weights is Pareto optimal. -/
theorem pa_negishi_pareto {α : Type*} {n : ℕ} {F : Set α} {U : Fin n → α → ℝ} {θ : Fin n → ℝ}
    (hθ : ∀ i, 0 < θ i) {c : α} (hc : c ∈ F)
    (hmax : ∀ c' ∈ F, ∑ i, θ i * U i c' ≤ ∑ i, θ i * U i c) : pa_ParetoOptimal F U c := by
  refine ⟨hc, ?_⟩
  rintro ⟨c', hc', hle, j, hj⟩
  have : ∑ i, θ i * U i c < ∑ i, θ i * U i c' :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hθ i).le)
      ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hθ j)⟩
  linarith [hmax c' hc']

theorem pa_feasible_isCompact {n : ℕ} {ι : Type*} [Finite ι] (e : ι → ℝ) :
    IsCompact (pa_feasible (n := n) e) := by
  have := Fintype.ofFinite ι
  have hclosed : IsClosed (pa_feasible (n := n) e) := by
    have h1 : IsClosed {c : Fin n → ι → ℝ | ∀ i, 0 ≤ c i} := by
      have : {c : Fin n → ι → ℝ | ∀ i, 0 ≤ c i} = ⋂ i, {c | 0 ≤ c i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {c : Fin n → ι → ℝ | ∑ i, c i ≤ e} :=
      isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_Icc (0 : Fin n → ι → ℝ) (fun _ => e)).subset ?_
  rintro c ⟨h0, hs⟩
  refine ⟨fun i => h0 i, fun i => ?_⟩
  calc c i ≤ ∑ j, c j := Finset.single_le_sum (f := c) (fun j _ => h0 j) (Finset.mem_univ i)
    _ ≤ e := hs

theorem pa_feasible_convex {n : ℕ} {ι : Type*} (e : ι → ℝ) :
    Convex ℝ (pa_feasible (n := n) e) := by
  rintro c ⟨hc0, hcs⟩ d ⟨hd0, hds⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply]
    exact add_nonneg (smul_nonneg ha (hc0 i)) (smul_nonneg hb (hd0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum]
    calc a • ∑ i, c i + b • ∑ i, d i ≤ a • e + b • e :=
          add_le_add (smul_le_smul_of_nonneg_left hcs ha) (smul_le_smul_of_nonneg_left hds hb)
      _ = e := by rw [← add_smul, hab, one_smul]

theorem pa_zero_feasible {n : ℕ} {ι : Type*} {e : ι → ℝ} (he : 0 ≤ e) :
    (0 : Fin n → ι → ℝ) ∈ pa_feasible e :=
  ⟨fun _ => le_rfl, by simpa using he⟩

/-- Miao, Lemma 20.5.1, p. 730: the plain utility possibility set `U₀(e)` is closed (indeed
compact) when the utilities are continuous. -/
theorem lemma_20_5_1_plain_closed {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) (e : ι → ℝ) : IsCompact (pa_U0 U e) :=
  (pa_feasible_isCompact e).image (continuous_pi fun i => (hU i).comp (continuous_apply i))

/-- For `θ ≥ 0` and continuous utilities the support values of `Ū₀(e)` are bounded above. -/
theorem pa_U0bar_bdd {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) (e : ι → ℝ) {θ : Fin n → ℝ} (hθ : ∀ i, 0 ≤ θ i) :
    BddAbove ((pa_dot θ) '' pa_U0bar U e) := by
  obtain ⟨M, hM⟩ := ((pa_feasible_isCompact (n := n) e).image
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hU i).comp (continuous_apply i)) :
      Continuous fun c : Fin n → ι → ℝ => ∑ i, θ i * U i (c i))).isBounded.bddAbove
  refine ⟨M, ?_⟩
  rintro _ ⟨u, ⟨c, hc, hu⟩, rfl⟩
  calc pa_dot θ u ≤ ∑ i, θ i * U i (c i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (hθ i)
    _ ≤ M := hM ⟨c, hc, rfl⟩

/-- **Lemma 20.5.1** (Miao, p. 730), corrected. If each `Uⁱ` is concave on `C` and continuous and
`e ≥ 0`, the comprehensive utility possibility set `Ū₀(e)` is convex, closed, satisfies free
disposal and is nonempty, and each `θ ≥ 0` has bounded support values on it. -/
theorem lemma_20_5_1 {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (U i)) (hU : ∀ i, Continuous (U i)) {e : ι → ℝ}
    (he : 0 ≤ e) :
    Convex ℝ (pa_U0bar U e) ∧ IsClosed (pa_U0bar U e) ∧ pa_FreeDisposal (pa_U0bar U e) ∧
      (pa_U0bar U e).Nonempty ∧
      ∀ θ : Fin n → ℝ, (∀ i, 0 ≤ θ i) → BddAbove ((pa_dot θ) '' pa_U0bar U e) := by
  refine ⟨?_, ?_, ?_, ⟨_, 0, pa_zero_feasible he, le_rfl⟩, ?_⟩
  · rintro u ⟨c, hc, hu⟩ v ⟨d, hd, hv⟩ a b ha hb hab
    refine ⟨a • c + b • d, pa_feasible_convex e hc hd ha hb hab, fun i => ?_⟩
    have hci : c i ∈ Set.Ici (0 : ι → ℝ) := hc.1 i
    have hdi : d i ∈ Set.Ici (0 : ι → ℝ) := hd.1 i
    have := (hconc i).2 hci hdi ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pa_uvec] at this ⊢
    calc a * u i + b * v i ≤ a * U i (c i) + b * U i (d i) :=
          add_le_add (mul_le_mul_of_nonneg_left (hu i) ha) (mul_le_mul_of_nonneg_left (hv i) hb)
      _ ≤ U i (a • c i + b • d i) := this
  · have hK := (pa_feasible_isCompact (n := n) e).image
      (continuous_pi fun i => (hU i).comp (continuous_apply i) : Continuous (pa_uvec U))
    have hN : IsClosed {d : Fin n → ℝ | d ≤ 0} := isClosed_le continuous_id continuous_const
    have heq : pa_U0bar U e = pa_uvec U '' pa_feasible e + {d : Fin n → ℝ | d ≤ 0} := by
      ext u
      simp only [pa_U0bar, Set.mem_ofPred_eq, Set.mem_add, Set.mem_image]
      constructor
      · rintro ⟨c, hc, hu⟩
        exact ⟨pa_uvec U c, ⟨c, hc, rfl⟩, u - pa_uvec U c, fun i => by
          simp only [Pi.sub_apply, Pi.zero_apply]; linarith [hu i], by abel⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, d, hd, rfl⟩
        exact ⟨c, hc, fun i => by
          have := hd i
          simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
          linarith⟩
    rw [heq]
    exact hN.add_left_of_isCompact hK
  · rintro u u' huu' ⟨c, hc, hu'⟩
    exact ⟨c, hc, huu'.trans hu'⟩
  · exact fun θ hθ => pa_U0bar_bdd hU e hθ

/-- Miao, Lemma 20.5.1 (counterexample to the printed statement): the plain set `U₀(e)` need
not satisfy free disposal. One agent, one good, `U(c) = c`, `e = 1`: `U₀(e) = [0, 1]` and
`−1 ≤ 0 ∈ U₀(e)` but `−1 ∉ U₀(e)`. -/
theorem lemma_20_5_1_counterexample :
    ¬ pa_FreeDisposal (pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) := by
  intro h
  have h0 : (0 : Fin 1 → ℝ) ∈ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) :=
    ⟨0, ⟨fun _ => le_rfl, fun _ => by simp⟩, rfl⟩
  obtain ⟨c, hc, hcu⟩ := h (fun _ => -1) 0 (fun _ => by norm_num) h0
  have h1 := congrFun hcu 0
  have h2 := hc.1 0 ()
  simp only [pa_uvec, Pi.zero_apply] at h1 h2
  linarith

/-- The linear functional of a continuous linear map on `ℝⁿ` in coordinates. -/
theorem pa_clm_apply {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (z : Fin n → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have := f.toLinearMap.pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- Miao, Lemma 20.5.2 (p. 731), abstract form, proved by the separation theorem as in the text:
for a convex, closed, nonempty set `U ⊆ ℝⁿ` with free disposal whose support values are
bounded, `v ∈ U` iff `θ · v ≤ V̂(θ)` for every `θ ∈ Δⁿ`. -/
theorem pa_mem_iff_support {n : ℕ} {U : Set (Fin n → ℝ)} (hconv : Convex ℝ U)
    (hclosed : IsClosed U) (hfd : pa_FreeDisposal U) (hne : U.Nonempty)
    (hbdd : ∀ θ ∈ pa_simplex n, BddAbove ((pa_dot θ) '' U)) (v : Fin n → ℝ) :
    v ∈ U ↔ ∀ θ ∈ pa_simplex n, pa_dot θ v ≤ pa_Vhat U θ := by
  constructor
  · intro hv θ hθ
    exact le_csSup (hbdd θ hθ) ⟨v, hv, rfl⟩
  · intro hsupp
    by_contra hv
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hconv hclosed hv
    set w : Fin n → ℝ := fun i => f (Pi.single i 1) with hw
    have hf : ∀ z, f z = pa_dot w z := fun z => by rw [pa_clm_apply]; rfl
    obtain ⟨a, ha⟩ := hne
    -- free disposal forces `w ≥ 0`
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i
      by_contra hi
      push Not at hi
      have hmem : ∀ t : ℝ, 0 ≤ t → a - t • Pi.single i 1 ∈ U := fun t ht =>
        hfd _ a (fun j => by
          by_cases hj : j = i
          · subst hj; simp [ht]
          · simp [hj]) ha
      have key := hfu _ (hmem ((u - f a) / (-w i) + 1) (by
        have : 0 < u - f a := by linarith [hfu a ha]
        have : 0 < -w i := by linarith
        positivity))
      rw [map_sub, map_smul, smul_eq_mul] at key
      have hpos : 0 < -w i := by linarith
      have : ((u - f a) / -w i + 1) * f (Pi.single i 1) = -(u - f a) + w i := by
        rw [show f (Pi.single i 1) = w i from rfl]
        have hwne : w i ≠ 0 := by linarith
        field_simp
      linarith
    have hW : 0 < ∑ i, w i := by
      rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw0 i).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ i, w i = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).1 h.symm i (Finset.mem_univ i)
        have h1 := hfu a ha
        rw [hf, pa_dot] at h1 hux
        simp only [hz, zero_mul, Finset.sum_const_zero] at h1 hux
        linarith
    set θ : Fin n → ℝ := fun i => w i / ∑ j, w j with hθdef
    have hθ : θ ∈ pa_simplex n := ⟨fun i => div_nonneg (hw0 i) hW.le, by
      simp only [hθdef, ← Finset.sum_div, div_self hW.ne']⟩
    have hdot : ∀ z, pa_dot θ z = f z / ∑ j, w j := fun z => by
      rw [hf, pa_dot, pa_dot, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hθdef]; ring
    have hsup : pa_Vhat U θ ≤ u / ∑ j, w j := by
      unfold pa_Vhat
      refine csSup_le ⟨_, a, ha, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [hdot]
      exact (div_le_div_iff_of_pos_right hW).2 (hfu z hz).le
    have := hsupp θ hθ
    rw [hdot] at this
    have : f v / ∑ j, w j ≤ u / ∑ j, w j := this.trans hsup
    rw [div_le_div_iff_of_pos_right hW] at this
    linarith

/-- **Lemma 20.5.2** (Miao, p. 731), corrected to the comprehensive set: with concave, continuous
utilities and `e ≥ 0`, `v ∈ Ū₀(e)` iff `min_{θ ∈ Δⁿ} (V̂(e, θ) − θ · v) ≥ 0`, i.e.
`θ · v ≤ V̂(e, θ)` for all `θ ∈ Δⁿ`, where `V̂(e, θ)` is the value of (20.58). -/
theorem lemma_20_5_2 {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (U i)) (hU : ∀ i, Continuous (U i)) {e : ι → ℝ}
    (he : 0 ≤ e) (v : Fin n → ℝ) :
    v ∈ pa_U0bar U e ↔ ∀ θ ∈ pa_simplex n, 0 ≤ pa_Vhat (pa_U0bar U e) θ - pa_dot θ v := by
  obtain ⟨hc, hcl, hfd, hne, hb⟩ := lemma_20_5_1 hconc hU he
  rw [pa_mem_iff_support hc hcl hfd hne (fun θ hθ => hb θ hθ.1)]
  exact forall₂_congr fun θ _ => sub_nonneg.symm

/-- The support value of the comprehensive set is the Negishi value (20.58):
`V̂(θ) = sup_{c ∈ C(e)} ∑ θᵢ Uⁱ(cⁱ)` for `θ ≥ 0`. -/
theorem pa_Vhat_U0bar {n : ℕ} {ι : Type*} [Finite ι] {U : Fin n → (ι → ℝ) → ℝ}
    (hU : ∀ i, Continuous (U i)) {e : ι → ℝ} (he : 0 ≤ e) {θ : Fin n → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) :
    pa_Vhat (pa_U0bar U e) θ = sSup ((fun c => ∑ i, θ i * U i (c i)) '' pa_feasible e) := by
  have hcpt := (pa_feasible_isCompact (n := n) e).image
    (continuous_finsetSum _ fun i _ => continuous_const.mul ((hU i).comp (continuous_apply i)) :
      Continuous fun c : Fin n → ι → ℝ => ∑ i, θ i * U i (c i))
  have hbdd := hcpt.isBounded.bddAbove
  unfold pa_Vhat
  apply le_antisymm
  · refine csSup_le ⟨_, pa_uvec U 0, ⟨0, pa_zero_feasible he, le_rfl⟩, rfl⟩ ?_
    rintro _ ⟨u, ⟨c, hc, hu⟩, rfl⟩
    exact (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hu i) (hθ i)).trans
      (le_csSup hbdd ⟨c, hc, rfl⟩)
  · refine csSup_le ⟨_, 0, pa_zero_feasible he, rfl⟩ ?_
    rintro _ ⟨c, hc, rfl⟩
    exact le_csSup (pa_U0bar_bdd hU e hθ) ⟨pa_uvec U c, ⟨c, hc, le_rfl⟩, rfl⟩

/-- Miao, Lemma 20.5.2 (counterexample to the printed statement with the plain set `U₀(e)`):
one agent, `U(c) = c`, `e = 1`; `v = −1` satisfies (20.62) but `v ∉ U₀(e)`. -/
theorem lemma_20_5_2_counterexample :
    (∀ θ ∈ pa_simplex 1, pa_dot θ (fun _ => -1) ≤
        pa_Vhat (pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) θ) ∧
      (fun _ => -1) ∉ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) := by
  have h0 : (0 : Fin 1 → ℝ) ∈ pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1) :=
    ⟨0, ⟨fun _ => le_rfl, fun _ => by simp⟩, rfl⟩
  have hbdd : ∀ θ : Fin 1 → ℝ, BddAbove ((pa_dot θ) ''
      pa_U0 (n := 1) (ι := Unit) (fun _ c => c ()) (fun _ => 1)) := fun θ =>
    ((lemma_20_5_1_plain_closed (fun _ => continuous_apply ()) _).image
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).isBounded
      |>.bddAbove
  refine ⟨fun θ hθ => ?_, ?_⟩
  · have hθ0 := hθ.1 0
    refine le_trans ?_ (le_csSup (hbdd θ) ⟨0, h0, rfl⟩)
    simp only [pa_dot, Fin.sum_univ_one, Pi.zero_apply, mul_zero]
    linarith
  · rintro ⟨c, hc, hcu⟩
    have h1 := congrFun hcu 0
    have h2 := hc.1 0 ()
    simp only [pa_uvec, Pi.zero_apply] at h1 h2
    linarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive Pareto problems: the Lucas–Stokey and Dumas–Wang–Uppal approaches

Miao, *Economic Dynamics in Discrete Time*, §20.5.1–§20.5.2 (pp. 731–734): the Bellman
equation (20.60)–(20.61), Propositions 20.5.1 and 20.5.2, and the variational (dual) form of
Kreps–Porteus utility.

The economy (`PARecEconomy`) is one step of the event tree: date-0 consumption `c₀ ∈ ℝⁿ₊` with
`∑ c₀ⁱ ≤ e₀`, next-period states `s : S` with continuation economies (consumption plans in
`ι → ℝ`, endowment `e₁(s)`, continuation utilities `U₁(s)ⁱ`), and recursive utilities
`Uⁱ(c) = Wⁱ(c₀ⁱ, Rⁱ(s ↦ U₁(s)ⁱ(c₁(s)ⁱ)))` with `Wⁱ` increasing in its second argument and
`Rⁱ` monotone. The Negishi values are `pa_rec_values` (whose supremum is `V̂(e₀, θ)`), and the
values of the Bellman problem (20.60) subject to (20.61) are `pa_bellman_values`.

* **Proposition 20.5.1**: the two problems have the same upper bounds and the same value,
  `V̂(e₀, θ) = sup {∑ θᵢ Wⁱ(c₀ⁱ, Rⁱ(v₁ⁱ)) : (20.59), (20.61)}` (`proposition_20_5_1`).
* **Proposition 20.5.2**: an allocation generated by the dynamic program solves the Negishi
  problem (20.58), and is Pareto optimal when all weights are positive
  (`proposition_20_5_2`); with a zero weight it need not be Pareto optimal
  (`proposition_20_5_2_counterexample`).
* §20.5.2: `F(c, ν) = max_u W(c, u) − (1 − ν)u` and the duality
  `W(c, u) = min_ν F(c, ν) + (1 − ν)u` (`pa_dwu_duality`), the variational utility
  `U_t = min_ν F(c_t, ν) + (1 − ν) E_t U_{t+1}` (`pa_dwu_variational`), and the one-step
  planner identity behind the recursion with `λ_{t+1}ⁱ = (1 − ν_tⁱ)λ_tⁱ` (`pa_dwu_planner`).

The numerical algorithm (Steps 1–3, p. 733) is not formalised (computational; the text claims
no convergence result).

Departures (see `docs/PA-corrections.md`): Proposition 20.5.2 needs positive Pareto weights (or
strictly increasing utilities) for Pareto optimality, and "generated" includes that the
continuation allocation delivers the promised utilities `v₁`; the duality of §20.5.2 is proved
at points where `W(c, ·)` has a supergradient (e.g. concave differentiable `W`), the minimum
being over the `ν` for which the maximum defining `F` is finite.
-/

namespace Miao.RecursiveUtility

open Set

/-- One step of the recursive exchange economy of §20.5.1 (Miao, pp. 729–731). -/
structure PARecEconomy (n : ℕ) (S ι : Type*) where
  e0 : ℝ
  e1 : S → ι → ℝ
  W : Fin n → ℝ → ℝ → ℝ
  R : Fin n → (S → ℝ) → ℝ
  U1 : S → Fin n → (ι → ℝ) → ℝ

variable {n : ℕ} {S ι : Type*}

/-- Feasible allocations: `c₀ ≥ 0`, `∑ c₀ⁱ ≤ e₀` (20.59) and `c₁(s) ∈ C(e₁(s))`. -/
def pa_rec_feasible (E : PARecEconomy n S ι) : Set ((Fin n → ℝ) × (S → Fin n → ι → ℝ)) :=
  {c | (∀ i, 0 ≤ c.1 i) ∧ ∑ i, c.1 i ≤ E.e0 ∧ ∀ s, c.2 s ∈ pa_feasible (E.e1 s)}

/-- Recursive utility `Uⁱ(c) = Wⁱ(c₀ⁱ, Rⁱ(s ↦ U₁(s)ⁱ(c₁(s)ⁱ)))`. -/
def pa_rec_U (E : PARecEconomy n S ι) (i : Fin n) (c : (Fin n → ℝ) × (S → Fin n → ι → ℝ)) : ℝ :=
  E.W i (c.1 i) (E.R i fun s => E.U1 s i (c.2 s i))

/-- The values `∑ θᵢ Uⁱ(c)` of the Negishi problem (20.58); `V̂(e₀, θ)` is their supremum. -/
def pa_rec_values (E : PARecEconomy n S ι) (θ : Fin n → ℝ) : Set ℝ :=
  (fun c => ∑ i, θ i * pa_rec_U E i c) '' pa_rec_feasible E

/-- The constraint (20.61): `min_{θ₁ ∈ Δⁿ} V̂(e₁, θ₁) − θ₁ · v₁ ≥ 0` in every state. -/
def pa_promise_ok (E : PARecEconomy n S ι) (v : S → Fin n → ℝ) : Prop :=
  ∀ s, ∀ θ1 ∈ pa_simplex n, 0 ≤ pa_Vhat (pa_U0bar (E.U1 s) (E.e1 s)) θ1 - pa_dot θ1 (v s)

/-- The values of the Bellman problem (20.60): `∑ θᵢ Wⁱ(c₀ⁱ, Rⁱ(v₁ⁱ))` over `c₀` satisfying
(20.59) and promised utilities `v₁` satisfying (20.61). -/
def pa_bellman_values (E : PARecEconomy n S ι) (θ : Fin n → ℝ) : Set ℝ :=
  {b | ∃ c0 : Fin n → ℝ, ∃ v : S → Fin n → ℝ, (∀ i, 0 ≤ c0 i) ∧ ∑ i, c0 i ≤ E.e0 ∧
    pa_promise_ok E v ∧ b = ∑ i, θ i * E.W i (c0 i) (E.R i fun s => v s i)}

/-- Every Bellman value is dominated by a Negishi value (through Lemma 20.5.2). -/
theorem pa_bellman_le_rec [Finite ι] {E : PARecEconomy n S ι}
    (hconc : ∀ s i, ConcaveOn ℝ (Set.Ici 0) (E.U1 s i)) (hcont : ∀ s i, Continuous (E.U1 s i))
    (he1 : ∀ s, 0 ≤ E.e1 s) (hW : ∀ i c, Monotone (E.W i c)) (hR : ∀ i, Monotone (E.R i))
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 ≤ θ i) {c0 : Fin n → ℝ} {v : S → Fin n → ℝ}
    (hv : pa_promise_ok E v) :
    ∃ c1 : S → Fin n → ι → ℝ, (∀ s, c1 s ∈ pa_feasible (E.e1 s)) ∧
      (∀ s i, v s i ≤ E.U1 s i (c1 s i))
      ∧ ∑ i, θ i * E.W i (c0 i) (E.R i fun s => v s i)
        ≤ ∑ i, θ i * E.W i (c0 i) (E.R i fun s => E.U1 s i (c1 s i)) := by
  have hmem : ∀ s, v s ∈ pa_U0bar (E.U1 s) (E.e1 s) := fun s =>
    (lemma_20_5_2 (hconc s) (hcont s) (he1 s) (v s)).2 (hv s)
  choose c1 hc1 hle using hmem
  refine ⟨c1, hc1, fun s i => hle s i, Finset.sum_le_sum fun i _ => ?_⟩
  exact mul_le_mul_of_nonneg_left (hW i (c0 i) (hR i fun s => hle s i)) (hθ i)

/-- **Proposition 20.5.1** (Miao, p. 732). With concave, continuous continuation utilities,
`e₁ ≥ 0`, `Wⁱ` increasing in the continuation value, `Rⁱ` monotone and weights `θ ≥ 0`, the
Negishi problem (20.58) and the Bellman problem (20.60)–(20.61) have the same upper bounds;
hence (when the Negishi values are bounded above and `e₀ ≥ 0`) `V̂(e₀, θ)` satisfies the
Bellman equation (20.60). -/
theorem proposition_20_5_1 [Finite ι] {E : PARecEconomy n S ι}
    (hconc : ∀ s i, ConcaveOn ℝ (Set.Ici 0) (E.U1 s i)) (hcont : ∀ s i, Continuous (E.U1 s i))
    (he1 : ∀ s, 0 ≤ E.e1 s) (hW : ∀ i c, Monotone (E.W i c)) (hR : ∀ i, Monotone (E.R i))
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 ≤ θ i) :
    upperBounds (pa_rec_values E θ) = upperBounds (pa_bellman_values E θ) ∧
      (0 ≤ E.e0 → BddAbove (pa_rec_values E θ) →
        sSup (pa_rec_values E θ) = sSup (pa_bellman_values E θ)) := by
  have hsub : pa_rec_values E θ ⊆ pa_bellman_values E θ := by
    rintro _ ⟨c, ⟨hc0, hcs, hc1⟩, rfl⟩
    refine ⟨c.1, fun s => pa_uvec (E.U1 s) (c.2 s), hc0, hcs, fun s => ?_, rfl⟩
    exact (lemma_20_5_2 (hconc s) (hcont s) (he1 s) _).1 ⟨c.2 s, hc1 s, le_rfl⟩
  have hub : upperBounds (pa_rec_values E θ) = upperBounds (pa_bellman_values E θ) := by
    apply le_antisymm
    · intro x hx
      rintro _ ⟨c0, v, hc0, hcs, hv, rfl⟩
      obtain ⟨c1, hc1, -, hle⟩ := pa_bellman_le_rec hconc hcont he1 hW hR hθ (c0 := c0) hv
      exact hle.trans (hx ⟨(c0, c1), ⟨hc0, hcs, hc1⟩, rfl⟩)
    · exact upperBounds_mono_set hsub
  refine ⟨hub, fun he0 hbdd => ?_⟩
  have hne : (pa_rec_values E θ).Nonempty :=
    ⟨_, (0, fun _ => 0), ⟨fun _ => le_rfl, by simpa using he0, fun s => pa_zero_feasible (he1 s)⟩,
      rfl⟩
  have hlub : IsLUB (pa_bellman_values E θ) (sSup (pa_rec_values E θ)) := by
    have := isLUB_csSup hne hbdd
    unfold IsLUB at this ⊢
    rwa [← hub]
  exact (hlub.csSup_eq (hne.mono hsub)).symm

/-- **Proposition 20.5.2** (Miao, p. 733). Let `(c₀, v₁)` solve the Bellman problem (20.60)
(its value is the supremum of the Bellman values) and let the continuation allocation `c₁`
deliver the promised utilities, `v₁(s) ≤ U₁(s)(c₁(s))`. Then `(c₀, c₁)` solves the Negishi
problem (20.58), and it is Pareto optimal when all weights are positive. -/
theorem proposition_20_5_2 [Finite ι] {E : PARecEconomy n S ι}
    (hconc : ∀ s i, ConcaveOn ℝ (Set.Ici 0) (E.U1 s i)) (hcont : ∀ s i, Continuous (E.U1 s i))
    (he1 : ∀ s, 0 ≤ E.e1 s) (hW : ∀ i c, Monotone (E.W i c)) (hR : ∀ i, Monotone (E.R i))
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 ≤ θ i) (he0 : 0 ≤ E.e0) (hbdd : BddAbove (pa_rec_values E θ))
    {c0 : Fin n → ℝ} {v : S → Fin n → ℝ} (hc0 : ∀ i, 0 ≤ c0 i) (hcs : ∑ i, c0 i ≤ E.e0)
    (hopt : ∑ i, θ i * E.W i (c0 i) (E.R i fun s => v s i) = sSup (pa_bellman_values E θ))
    {c1 : S → Fin n → ι → ℝ} (hc1 : ∀ s, c1 s ∈ pa_feasible (E.e1 s))
    (hdel : ∀ s i, v s i ≤ E.U1 s i (c1 s i)) :
    (∀ c ∈ pa_rec_feasible E, ∑ i, θ i * pa_rec_U E i c ≤ ∑ i, θ i * pa_rec_U E i (c0, c1)) ∧
      ((∀ i, 0 < θ i) → pa_ParetoOptimal (pa_rec_feasible E) (pa_rec_U E) (c0, c1)) := by
  have hfeas : (c0, c1) ∈ pa_rec_feasible E := ⟨hc0, hcs, hc1⟩
  have hge : sSup (pa_bellman_values E θ) ≤ ∑ i, θ i * pa_rec_U E i (c0, c1) := by
    rw [← hopt]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hW i (c0 i) (hR i fun s => hdel s i)) (hθ i)
  have heq := (proposition_20_5_1 hconc hcont he1 hW hR hθ).2 he0 hbdd
  have hmax : ∀ c ∈ pa_rec_feasible E, ∑ i, θ i * pa_rec_U E i c
      ≤ ∑ i, θ i * pa_rec_U E i (c0, c1) := fun c hc =>
    (le_csSup hbdd ⟨c, hc, rfl⟩).trans (heq ▸ hge)
  exact ⟨hmax, fun hpos => pa_negishi_pareto hpos hfeas hmax⟩

/-- Miao, Proposition 20.5.2 (counterexample with a zero weight). Two agents, one state and one
good tomorrow; agent 0 has `W⁰ ≡ 0`, agent 1 has `W¹(c₀, r) = c₀`, `e₀ = 1`; weights
`θ = (1, 0)`. The allocation `c₀ = 0` solves the Bellman problem but is not Pareto optimal. -/
theorem proposition_20_5_2_counterexample :
    let E : PARecEconomy 2 Unit Unit :=
      { e0 := 1, e1 := fun _ _ => 0, W := ![fun _ _ => 0, fun c0 _ => c0],
        R := fun _ f => f (), U1 := fun _ _ _ => 0 }
    (∑ i, ![1, 0] i * E.W i ((0 : Fin 2 → ℝ) i) (E.R i fun s => (fun _ _ => 0 : Unit → Fin 2 → ℝ)
        s i) = sSup (pa_bellman_values E ![1, 0])) ∧
      ¬ pa_ParetoOptimal (pa_rec_feasible E) (pa_rec_U E) (0, fun _ _ _ => 0) := by
  intro E
  have hB : pa_bellman_values E ![1, 0] = {0} := by
    ext b
    simp only [pa_bellman_values, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c0, v, -, -, -, rfl⟩
      simp [E, Fin.sum_univ_two]
    · rintro rfl
      refine ⟨0, fun _ _ => 0, fun _ => le_rfl, by simp [E], fun s θ1 hθ1 => ?_, ?_⟩
      · have h0 : (pa_uvec (E.U1 s) 0) ∈ pa_U0bar (E.U1 s) (E.e1 s) :=
          ⟨0, pa_zero_feasible le_rfl, le_rfl⟩
        have hb := pa_U0bar_bdd (U := E.U1 s) (fun i => continuous_const) (E.e1 s) hθ1.1
        have := le_csSup hb ⟨_, h0, rfl⟩
        simp only [pa_dot, E, pa_uvec, mul_zero, Finset.sum_const_zero] at this ⊢
        unfold pa_Vhat
        linarith
      · simp [E, Fin.sum_univ_two]
  refine ⟨by rw [hB, csSup_singleton]; simp [E, Fin.sum_univ_two], ?_⟩
  rintro ⟨-, hno⟩
  apply hno
  refine ⟨(![0, 1], fun _ _ _ => 0), ⟨fun i => by fin_cases i <;> simp, by simp [E], fun s =>
    pa_zero_feasible le_rfl⟩, fun i => ?_, 1, ?_⟩
  · fin_cases i <;> simp [pa_rec_U, E]
  · simp [pa_rec_U, E]

/-! ### §20.5.2 The Dumas–Wang–Uppal approach -/

/-- Miao, p. 734: `F(c, ν) = max_u W(c, u) − (1 − ν)u`. -/
noncomputable def pa_dwu_F (W : ℝ → ℝ → ℝ) (c ν : ℝ) : ℝ :=
  sSup (Set.range fun u => W c u - (1 - ν) * u)

/-- Miao, p. 734, duality: if `W(c, ·)` has the supergradient `g` at `u`, then
`W(c, u) = min_ν F(c, ν) + (1 − ν)u`, the minimum over the `ν` with `F(c, ν) < ∞` being
attained at `ν = 1 − g`. -/
theorem pa_dwu_duality (W : ℝ → ℝ → ℝ) (c u g : ℝ)
    (hsg : ∀ u', W c u' ≤ W c u + g * (u' - u)) :
    IsLeast {y | ∃ ν, BddAbove (Set.range fun u' => W c u' - (1 - ν) * u') ∧
      y = pa_dwu_F W c ν + (1 - ν) * u} (W c u) := by
  constructor
  · refine ⟨1 - g, ⟨W c u - g * u, ?_⟩, ?_⟩
    · rintro _ ⟨u', rfl⟩
      have := hsg u'
      simp only
      linarith
    · have hmax : IsGreatest (Set.range fun u' => W c u' - (1 - (1 - g)) * u') (W c u - g * u) := by
        refine ⟨⟨u, by ring⟩, ?_⟩
        rintro _ ⟨u', rfl⟩
        have := hsg u'
        simp only
        linarith
      simp only [pa_dwu_F, hmax.csSup_eq]
      ring
  · rintro _ ⟨ν, hb, rfl⟩
    have := le_csSup hb ⟨u, rfl⟩
    simp only [pa_dwu_F] at this ⊢
    linarith

/-- Miao, p. 734 (Geoffard's variational utility): if `W(c_t, ·)` has a supergradient at
`E_t U_{t+1}`, then `U_t = W(c_t, E_t U_{t+1}) = min_ν F(c_t, ν) + (1 − ν) E_t U_{t+1}`. -/
theorem pa_dwu_variational {S' : Type*} [Fintype S'] (W : ℝ → ℝ → ℝ) (p U' : S' → ℝ) (c g : ℝ)
    (hsg : ∀ u', W c u' ≤ W c (pa_E p U') + g * (u' - pa_E p U')) :
    IsLeast {y | ∃ ν, BddAbove (Set.range fun u' => W c u' - (1 - ν) * u') ∧
      y = pa_dwu_F W c ν + (1 - ν) * pa_E p U'} (W c (pa_E p U')) :=
  pa_dwu_duality W c (pa_E p U') g hsg

/-- Miao, p. 734: the one-step planner identity behind the Dumas–Wang–Uppal recursion. For
weights `λ ≥ 0` and supergradients `gᵢ` of `Wⁱ(cⁱ, ·)` at `uⁱ = E_t U_{t+1}ⁱ`,
`∑ λⁱ Wⁱ(cⁱ, uⁱ) = min_ν ∑ λⁱ Fⁱ(cⁱ, νⁱ) + ∑ λ_{t+1}ⁱ uⁱ` with `λ_{t+1}ⁱ = (1 − νⁱ)λⁱ`. -/
theorem pa_dwu_planner {m : ℕ} (W : Fin m → ℝ → ℝ → ℝ) (lam c u g : Fin m → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsg : ∀ i u', W i (c i) u' ≤ W i (c i) (u i) + g i * (u' - u i)) :
    IsLeast {y | ∃ ν : Fin m → ℝ,
      (∀ i, BddAbove (Set.range fun u' => W i (c i) u' - (1 - ν i) * u'))
      ∧ y = ∑ i, lam i * pa_dwu_F (W i) (c i) (ν i) + ∑ i, ((1 - ν i) * lam i) * u i}
      (∑ i, lam i * W i (c i) (u i)) := by
  have hd := fun i => pa_dwu_duality (W i) (c i) (u i) (g i) (hsg i)
  constructor
  · refine ⟨fun i => 1 - g i, fun i => ?_, ?_⟩
    · obtain ⟨⟨ν, hb, hν⟩, -⟩ := hd i
      refine ⟨W i (c i) (u i) - g i * u i, ?_⟩
      rintro _ ⟨u', rfl⟩
      have := hsg i u'
      simp only
      linarith
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmax : IsGreatest (Set.range fun u' => W i (c i) u' - (1 - (1 - g i)) * u')
          (W i (c i) (u i) - g i * u i) := by
        refine ⟨⟨u i, by ring⟩, ?_⟩
        rintro _ ⟨u', rfl⟩
        have := hsg i u'
        simp only
        linarith
      simp only [pa_dwu_F, hmax.csSup_eq]
      ring
  · rintro _ ⟨ν, hb, rfl⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := (hd i).2 ⟨ν i, hb i, rfl⟩
    nlinarith [hlam i]

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 20.5: precautionary saving with Weil (1993) preferences

Miao, *Economic Dynamics in Discrete Time*, Exercise 20.5 (p. 735). Utility (20.4),
`U_t = ((1 − β)c_t^{1−ρ} + β(R_t U_{t+1})^{1−ρ})^{1/(1−ρ)}` with the exponential certainty
equivalent `R_t(X) = −(1/γ) ln E_t exp(−γX)`; budget `a_{t+1} = R(a_t − c_t) + y_{t+1}`;
labour income `y_{t+1} = ρ_y y_t + (1 − ρ_y)ȳ + σ_y ε_{t+1}`, `ε` IID `N(0, 1)` (the text
prints `y_t = ρ_y y_t + …`; the lag is meant).

Guess and verify `V(a, y) = A(a + By + D)`:

* the certainty equivalent of a Gaussian, `R(m + sε) = m − γs²/2` (`pa_expCE_gaussian`), gives
  `R_t V(a_{t+1}, y_{t+1}) = A(R(a − c) + K(y))` (`ex_20_5_ce`), with
  `K(y)/R = By + D` for `B = ρ_y/(R − ρ_y)` and the `D` below (`ex_20_5_K`);
* with `1 + x = (βR^{1−ρ})^{−1/ρ}` and `A` solving `ARk = x`, `k = (βAR/(1 − β))^{−1/ρ}`
  (such an `A` exists: `ex_20_5_A`), the consumption rule
  `c = x/(1 + x) (a + By + D)` satisfies the first-order condition of the Bellman problem and
  reproduces the guess, `V(a, y) = A(a + By + D)` (`ex_20_5`);
* effects of the parameters: the marginal propensity to consume out of total wealth is
  `1 − (βR^{1−ρ})^{1/ρ}`, which depends on the EIS `1/ρ` but not on `γ` (`ex_20_5_mpc`); risk
  aversion enters only through the precautionary term
  `D = ((1 + B)(1 − ρ_y)ȳ − γA(1 + B)²σ_y²/2)/(R − 1)`, which falls as `γ` rises
  (`ex_20_5_precautionary`).

The first-order condition is verified (stationarity); its sufficiency (concavity of the
objective) is not formalised.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- The exponential certainty equivalent `R(X) = −(1/γ) ln E exp(−γX)` of (20.4). -/
noncomputable def pa_expCE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (X : Ω → ℝ) : ℝ :=
  -(1 / γ) * Real.log (∫ ω, Real.exp (-γ * X ω) ∂P)

/-- The exponential certainty equivalent of a Gaussian: `R(m + sε) = m − γs²/2` for
`ε ∼ N(0, 1)`. -/
theorem pa_expCE_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε : Ω → ℝ}
    (hε : HasLaw ε (gaussianReal 0 1) P) {γ : ℝ} (hγ : γ ≠ 0) (m s : ℝ) :
    pa_expCE P γ (fun ω => m + s * ε ω) = m - γ * s ^ 2 / 2 := by
  have h := mgf_gaussianReal hε (-γ * s)
  simp only [mgf] at h
  have hint : (∫ ω, Real.exp (-γ * (m + s * ε ω)) ∂P)
      = Real.exp (-γ * m) * ∫ ω, Real.exp (-γ * s * ε ω) ∂P := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [← Real.exp_add]
    ring_nf
  simp only [pa_expCE]
  rw [hint, h, ← Real.exp_add, Real.log_exp]
  field_simp
  push_cast
  ring

/-- `K(y) = (1 + B)(ρ_y y + (1 − ρ_y)ȳ) + D − γA(1 + B)²σ_y²/2`. -/
noncomputable def pa_weilK (A B D γ ρy ybar σy y : ℝ) : ℝ :=
  (1 + B) * (ρy * y + (1 - ρy) * ybar) + D - γ * A * (1 + B) ^ 2 * σy ^ 2 / 2

/-- Exercise 20.5 (Miao, p. 735), the certainty-equivalent step: with
`V(a', y') = A(a' + By' + D)`, `a' = R(a − c) + y'` and
`y' = ρ_y y + (1 − ρ_y)ȳ + σ_y ε`, `R_t V(a', y') = A(R(a − c) + K(y))`. -/
theorem ex_20_5_ce {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε : Ω → ℝ}
    (hε : HasLaw ε (gaussianReal 0 1) P) {γ : ℝ} (hγ : γ ≠ 0) (A B D R ρy ybar σy a c y : ℝ) :
    pa_expCE P γ (fun ω => A * ((R * (a - c) + (ρy * y + (1 - ρy) * ybar + σy * ε ω))
        + B * (ρy * y + (1 - ρy) * ybar + σy * ε ω) + D))
      = A * (R * (a - c) + pa_weilK A B D γ ρy ybar σy y) := by
  have := pa_expCE_gaussian hε hγ (A * (R * (a - c) + (1 + B) * (ρy * y + (1 - ρy) * ybar) + D))
    (A * (1 + B) * σy)
  rw [show (fun ω => A * ((R * (a - c) + (ρy * y + (1 - ρy) * ybar + σy * ε ω))
      + B * (ρy * y + (1 - ρy) * ybar + σy * ε ω) + D))
      = fun ω => A * (R * (a - c) + (1 + B) * (ρy * y + (1 - ρy) * ybar) + D)
        + A * (1 + B) * σy * ε ω by funext ω; ring, this]
  simp only [pa_weilK]
  ring

/-- Exercise 20.5: with `B = ρ_y/(R − ρ_y)` and
`D = ((1 + B)(1 − ρ_y)ȳ − γA(1 + B)²σ_y²/2)/(R − 1)`, `K(y)/R = By + D`. -/
theorem ex_20_5_K {A γ R ρy ybar σy : ℝ} (hR1 : R ≠ 1) (hR0 : R ≠ 0) (hRy : R ≠ ρy) (y : ℝ) :
    pa_weilK A (ρy / (R - ρy))
        (((1 + ρy / (R - ρy)) * (1 - ρy) * ybar
          - γ * A * (1 + ρy / (R - ρy)) ^ 2 * σy ^ 2 / 2) / (R - 1)) γ ρy ybar σy y / R
      = ρy / (R - ρy) * y + ((1 + ρy / (R - ρy)) * (1 - ρy) * ybar
          - γ * A * (1 + ρy / (R - ρy)) ^ 2 * σy ^ 2 / 2) / (R - 1) := by
  have h1 : R - 1 ≠ 0 := sub_ne_zero.2 hR1
  have h2 : R - ρy ≠ 0 := sub_ne_zero.2 hRy
  simp only [pa_weilK]
  field_simp
  ring

/-- Exercise 20.5: an `A > 0` solving `A R k = x`, `k = (βAR/(1 − β))^{−1/ρ}`, exists for
`x > 0`, `ρ ≠ 1`: `A = (x(β/(1 − β))^{1/ρ})^{ρ/(ρ−1)}/R`. -/
theorem ex_20_5_A {β ρ R x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hR : 0 < R) (hx : 0 < x) :
    let A := (x * (β / (1 - β)) ^ (1 / ρ)) ^ (ρ / (ρ - 1)) / R
    0 < A ∧ A * R * (β * A * R / (1 - β)) ^ (-1 / ρ) = x := by
  intro A
  have hβ' : 0 < 1 - β := by linarith
  have hq : 0 < (β / (1 - β)) ^ (1 / ρ) := Real.rpow_pos_of_pos (div_pos hβ0 hβ') _
  have hA : 0 < A := div_pos (Real.rpow_pos_of_pos (mul_pos hx hq) _) hR
  refine ⟨hA, ?_⟩
  have hρ' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  apply pa_eq_of_log_eq (by positivity) hx
  have hAR : A * R = (x * (β / (1 - β)) ^ (1 / ρ)) ^ (ρ / (ρ - 1)) := by
    simp only [A]; field_simp
  rw [show β * A * R / (1 - β) = (β / (1 - β)) * (A * R) by ring]
  rw [hAR]
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div]
  field_simp
  ring

/-- The objective of the Bellman equation of Exercise 20.5 after the certainty-equivalent
step: `f(c) = ((1 − β)c^{1−ρ} + β(AR(w − c))^{1−ρ})^{1/(1−ρ)}`, where `w = a + By + D` is total
wealth (so that `A(R(a − c) + K(y)) = AR(w − c)` by `ex_20_5_K`). -/
noncomputable def pa_weilObj (β ρ A R w c : ℝ) : ℝ := pa_W β ρ c (A * R * (w - c))

/-- **Exercise 20.5** (Miao, p. 735): guess and verify. With `1 + x = (βR^{1−ρ})^{−1/ρ}`,
`x > 0`, and `A > 0` solving `ARk = x` with `k = (βAR/(1 − β))^{−1/ρ}`, the consumption
`c = x/(1 + x) w` out of total wealth `w = a + By + D > 0` is interior, satisfies the
first-order condition `f'(c) = 0`, and attains `f(c) = A w`, reproducing
`V(a, y) = A(a + By + D)`. -/
theorem ex_20_5 {β ρ R A x w : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hR : 0 < R) (hA : 0 < A) (hx1 : 1 + x = (β * R ^ (1 - ρ)) ^ (-1 / ρ)) (hx : 0 < x)
    (hk : A * R * (β * A * R / (1 - β)) ^ (-1 / ρ) = x) (hw : 0 < w) :
    0 < x / (1 + x) * w ∧ x / (1 + x) * w < w ∧
      HasDerivAt (pa_weilObj β ρ A R w) 0 (x / (1 + x) * w) ∧
      pa_weilObj β ρ A R w (x / (1 + x) * w) = A * w := by
  have hβ' : 0 < 1 - β := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ1)
  set c := x / (1 + x) * w with hc
  set k := (β * A * R / (1 - β)) ^ (-1 / ρ) with hkdef
  have hkpos : 0 < k := Real.rpow_pos_of_pos (by positivity) _
  have hcpos : 0 < c := by positivity
  have hcw : c < w := by
    rw [hc, div_mul_eq_mul_div, div_lt_iff₀ h1x]; nlinarith
  have hQ : A * R * (w - c) = A * R * w / (1 + x) := by
    rw [hc]; field_simp; ring
  have hQpos : 0 < A * R * (w - c) := mul_pos (mul_pos hA hR) (by linarith)
  -- `c = k Q` at the candidate
  have hcQ : c = k * (A * R * (w - c)) := by
    rw [hQ, hc]
    have : k = x / (A * R) := by rw [← hk]; field_simp
    rw [this]
    field_simp
  -- `k^{−ρ} = βAR/(1 − β)`
  have hkρ : k ^ (-ρ) = β * A * R / (1 - β) := by
    rw [hkdef, ← Real.rpow_mul (by positivity), show -1 / ρ * -ρ = 1 by field_simp,
      Real.rpow_one]
  refine ⟨hcpos, hcw, ?_, ?_⟩
  · -- the first-order condition
    have e : (1 : ℝ) - ρ - 1 = -ρ := by ring
    have hd1 : HasDerivAt (fun c : ℝ => c ^ (1 - ρ)) ((1 - ρ) * c ^ (-ρ)) c := by
      have := Real.hasDerivAt_rpow_const (x := c) (p := 1 - ρ) (Or.inl hcpos.ne')
      rwa [e] at this
    have hd2 : HasDerivAt (fun c : ℝ => (A * R * (w - c)) ^ (1 - ρ))
        (A * R * -1 * (1 - ρ) * (A * R * (w - c)) ^ (-ρ)) c := by
      have := (((hasDerivAt_id c).const_sub w).const_mul (A * R)).rpow_const (p := 1 - ρ)
        (Or.inl hQpos.ne')
      simp only [id] at this
      rw [e] at this
      exact this
    have hin := (hd1.const_mul (1 - β)).add (hd2.const_mul β)
    have hinpos : 0 < (1 - β) * c ^ (1 - ρ) + β * (A * R * (w - c)) ^ (1 - ρ) := by positivity
    have hout := hin.rpow_const (p := 1 / (1 - ρ)) (Or.inl hinpos.ne')
    have hzero : (1 - β) * ((1 - ρ) * c ^ (-ρ))
        + β * (A * R * -1 * (1 - ρ) * (A * R * (w - c)) ^ (-ρ)) = 0 := by
      have hc' : c ^ (-ρ) = k ^ (-ρ) * (A * R * (w - c)) ^ (-ρ) := by
        conv_lhs => rw [hcQ]
        rw [Real.mul_rpow hkpos.le hQpos.le]
      rw [hc', hkρ]
      field_simp
      ring
    rw [hzero, zero_mul, zero_mul] at hout
    exact hout
  · -- the value
    simp only [pa_weilObj, pa_W]
    have hk1 : (1 - β) * c ^ (1 - ρ) + β * (A * R * (w - c)) ^ (1 - ρ)
        = (A * R * (w - c)) ^ (1 - ρ) * (β * (1 + x)) := by
      have hcr : c ^ (1 - ρ) = k ^ (1 - ρ) * (A * R * (w - c)) ^ (1 - ρ) := by
        conv_lhs => rw [hcQ]
        rw [Real.mul_rpow hkpos.le hQpos.le]
      have hk1ρ : (1 - β) * k ^ (1 - ρ) = β * x := by
        rw [show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add hkpos, Real.rpow_one, hkρ, ← hk]
        field_simp
      rw [hcr, ← mul_assoc, hk1ρ]
      ring
    rw [hk1, Real.mul_rpow (Real.rpow_nonneg hQpos.le _) (by positivity), ← Real.rpow_mul
      hQpos.le, mul_one_div_cancel h1, Real.rpow_one]
    -- `(β(1 + x))^{1/(1−ρ)} = (1 + x)/R`
    have hb : (β * (1 + x)) ^ (1 / (1 - ρ)) = (1 + x) / R := by
      apply pa_eq_of_log_eq (by positivity) (by positivity)
      have hl := congrArg Real.log hx1
      rw [Real.log_rpow (by positivity), Real.log_mul hβ0.ne' (by positivity),
        Real.log_rpow hR] at hl
      rw [Real.log_rpow (by positivity), Real.log_mul hβ0.ne' h1x.ne',
        Real.log_div h1x.ne' hR.ne']
      field_simp at hl ⊢
      linear_combination hl
    rw [hb, hQ]
    field_simp

/-- Exercise 20.5: the marginal propensity to consume out of total wealth,
`x/(1 + x) = 1 − (βR^{1−ρ})^{1/ρ}`, depends on the EIS `1/ρ` (and `β`, `R`) but not on the
risk aversion `γ`. -/
theorem ex_20_5_mpc {β ρ R x : ℝ} (hβ0 : 0 < β) (hR : 0 < R)
    (hx1 : 1 + x = (β * R ^ (1 - ρ)) ^ (-1 / ρ)) :
    x / (1 + x) = 1 - (β * R ^ (1 - ρ)) ^ (1 / ρ) := by
  have hb : 0 < β * R ^ (1 - ρ) := mul_pos hβ0 (Real.rpow_pos_of_pos hR _)
  have h1x : 0 < 1 + x := by rw [hx1]; exact Real.rpow_pos_of_pos hb _
  have : 1 / (1 + x) = (β * R ^ (1 - ρ)) ^ (1 / ρ) := by
    rw [hx1, one_div, ← Real.rpow_neg hb.le]
    ring_nf
  rw [← this]
  field_simp
  ring

/-- Exercise 20.5: precautionary saving. The constant `D` of total wealth falls strictly as risk
aversion `γ` rises (for `R > 1`, `A > 0`, `1 + B ≠ 0`, `σ_y ≠ 0`), lowering consumption. -/
theorem ex_20_5_precautionary {A B R ρy ybar σy γ γ' : ℝ} (hR : 1 < R) (hA : 0 < A)
    (hB : 1 + B ≠ 0) (hσ : σy ≠ 0) (hγ : γ < γ') :
    ((1 + B) * (1 - ρy) * ybar - γ' * A * (1 + B) ^ 2 * σy ^ 2 / 2) / (R - 1)
      < ((1 + B) * (1 - ρy) * ybar - γ * A * (1 + B) ^ 2 * σy ^ 2 / 2) / (R - 1) := by
  apply div_lt_div_of_pos_right _ (by linarith)
  have : 0 < A * (1 + B) ^ 2 * σy ^ 2 := by positivity
  nlinarith

end Miao.RecursiveUtility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 20.6 and 20.7: first-order conditions for recursive Pareto problems

Miao, *Economic Dynamics in Discrete Time*, Exercises 20.6–20.7 (pp. 735–736).

**Exercise 20.6** (production). Agents `i` with recursive utility
`Uⁱ = Wⁱ(c₀ⁱ, Rⁱ(s ↦ uⁱ(c₁ⁱ(s))))`, resource constraints `∑ c₀ⁱ + k₁ = z₀F(k₀)` and
`∑ c₁ⁱ(s) = z₁(s)F(k₁)`, Pareto weights `θ`. At an optimum of the planner's problem, with
`Wⁱ`, `Rⁱ`, `uⁱ`, `F` differentiable (`W₁ⁱ, W₂ⁱ` the partials of `Wⁱ`, `Rₛⁱ` the partial of `Rⁱ`
in state `s`):
* date-0 risk sharing `θᵢW₁ⁱ = θⱼW₁ʲ` (`ex_20_6_sharing0`);
* date-1 risk sharing `θᵢW₂ⁱRₛⁱuⁱ'(c₁ⁱ(s)) = θⱼW₂ʲRₛʲuʲ'(c₁ʲ(s))` (`ex_20_6_sharing1`);
* the Euler equation `W₁ⁱ = W₂ⁱ ∑ₛ Rₛⁱ uⁱ'(c₁ⁱ(s)) z₁(s)F'(k₁)` (`ex_20_6_euler`).
The general directional derivative of the planner's objective is `pa_planner_hasDerivAt`.
For Epstein–Zin utility `W₂/W₁` and `Rₛ` are explicit (`pa_W`, `pa_CE`), which this
general statement covers.

**Exercise 20.7** (multiplier preferences). `Uⁱ = uⁱ(c₀ⁱ) − βϑᵢ ln E exp(−U₁ⁱ/ϑᵢ)` with
`U₁ⁱ(s) = uⁱ(c₁ⁱ(s))`, pure exchange. The certainty equivalent has the partial derivative
`p(s) m(s)` with the worst-case distortion `m(s) = e^{−U₁(s)/ϑ}/E e^{−U₁/ϑ}`
(`pa_multiplier_hasDerivAt`), and an optimum satisfies `λᵢ uⁱ'(c₀ⁱ) = λⱼ uʲ'(c₀ʲ)` and
`λᵢ mᵢ(s) uⁱ'(c₁ⁱ(s)) = λⱼ mⱼ(s) uʲ'(c₁ʲ(s))` (`ex_20_7`). Part (b) is computational (Matlab) and
is not formalised.

Exercise 20.4 (Matlab replication of Bansal–Yaron) is computational; its formulas are the
theorems of `PALongRunRisk` and `PALongRunRiskPricing`.

The first-order conditions are necessary conditions at an interior optimum (the
perturbations used are feasible for all `t`).
-/

namespace Miao.RecursiveUtility

open Real Filter Topology

theorem pa_clm_pi_apply {S : Type*} [Fintype S] [DecidableEq S] (L : (S → ℝ) →L[ℝ] ℝ)
    (z : S → ℝ) : L z = ∑ s, L (Pi.single s 1) * z s := by
  have := L.toLinearMap.pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem pa_clm_prod_apply (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) := by simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

variable {n : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The planner's objective `∑ θᵢ Wⁱ(c₀ⁱ, Rⁱ(s ↦ uⁱ(c₁(s)ⁱ)))`. -/
def pa_planner (θ : Fin n → ℝ) (W : Fin n → ℝ × ℝ → ℝ) (R : Fin n → (S → ℝ) → ℝ)
    (u : Fin n → ℝ → ℝ) (c0 : Fin n → ℝ) (c1 : S → Fin n → ℝ) : ℝ :=
  ∑ i, θ i * W i (c0 i, R i fun s => u i (c1 s i))

/-- The derivative of the planner's objective along differentiable paths `p₀`, `p₁` through the
allocation `(c₀, c₁)`. -/
theorem pa_planner_hasDerivAt (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {c0 : Fin n → ℝ} {c1 : S → Fin n → ℝ}
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i))
    {p0 : Fin n → ℝ → ℝ} {p1 : S → Fin n → ℝ → ℝ} {d0 : Fin n → ℝ} {d1 : S → Fin n → ℝ}
    (hp0 : ∀ i, HasDerivAt (p0 i) (d0 i) 0) (hp1 : ∀ s i, HasDerivAt (p1 s i) (d1 s i) 0)
    (h00 : ∀ i, p0 i 0 = c0 i) (h10 : ∀ s i, p1 s i 0 = c1 s i) :
    HasDerivAt (fun t => pa_planner θ W R u (fun i => p0 i t) fun s i => p1 s i t)
      (∑ i, θ i * (d0 i * DW i (1, 0)
        + DW i (0, 1) * ∑ s, DR i (Pi.single s 1) * (du i s * d1 s i))) 0 := by
  unfold pa_planner
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul (θ i) ?_
  have hv : HasDerivAt (fun t => fun s => u i (p1 s i t)) (fun s => du i s * d1 s i) 0 := by
    refine hasDerivAt_pi.2 fun s => ?_
    exact (hu i s).comp_of_eq 0 (hp1 s i) (h10 s i).symm
  have hr := (hR i).comp_hasDerivAt_of_eq 0 hv (by funext s; rw [h10])
  have hpair := (hp0 i).prodMk hr
  have := (hW i).comp_hasDerivAt_of_eq 0 hpair (by simp [Function.comp_apply, h00, h10])
  refine this.congr_deriv ?_
  rw [pa_clm_prod_apply (DW i) (d0 i) (DR i fun s => du i s * d1 s i),
    pa_clm_pi_apply (DR i) (fun s => du i s * d1 s i)]
  ring

omit [Fintype S] [DecidableEq S] in
/-- **Exercise 20.6** (Miao, p. 735), date-0 risk sharing: at an optimum of the planner's
problem with production, `θᵢ W₁ⁱ = θⱼ W₁ʲ`. -/
theorem ex_20_6_sharing0 [Finite S] (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) {i j : Fin n} :
    θ i * DW i (1, 0) = θ j * DW j (1, 0) := by
  have := Fintype.ofFinite S
  classical
  set d : Fin n → ℝ := fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0) with hd
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l t => c0 l + t * d l)
    (p1 := fun s l _ => c1 s l) (d0 := d) (d1 := fun _ _ => 0)
    (fun l => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c0 l))
    (fun s l => hasDerivAt_const _ _) (fun l => by simp) (fun s l => rfl)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l + t * d l)
      fun s l => c1 s l) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, add_zero]
    refine hopt _ k1 c1 ?_ hf1
    rw [← hf0, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hd, Finset.sum_sub_distrib]
  have h0 := hmax.hasDerivAt_eq_zero hD
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at h0
  simp only [hd, sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
  linarith

omit [Fintype S] in
/-- **Exercise 20.6** (Miao, p. 735), date-1 risk sharing in state `s`:
`θᵢ W₂ⁱ Rₛⁱ uⁱ'(c₁ⁱ(s)) = θⱼ W₂ʲ Rₛʲ uʲ'(c₁ʲ(s))`. -/
theorem ex_20_6_sharing1 [Finite S] (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) {i j : Fin n} (s : S) :
    θ i * DW i (0, 1) * DR i (Pi.single s 1) * du i s
      = θ j * DW j (0, 1) * DR j (Pi.single s 1) * du j s := by
  have := Fintype.ofFinite S
  set d : S → Fin n → ℝ := fun s' l => if s' = s then
    (if l = i then 1 else 0) - (if l = j then 1 else 0) else 0 with hd
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l _ => c0 l)
    (p1 := fun s' l t => c1 s' l + t * d s' l) (d0 := fun _ => 0) (d1 := d)
    (fun l => hasDerivAt_const _ _)
    (fun s' l => by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d s' l)).const_add (c1 s' l))
    (fun l => rfl) (fun s' l => by simp)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l)
      fun s' l => c1 s' l + t * d s' l) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, add_zero]
    refine hopt _ k1 _ hf0 fun s' => ?_
    rw [← hf1 s', Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases hs : s' = s
    · simp [hd, hs, Finset.sum_sub_distrib]
    · simp [hd, hs]
  have h0 := hmax.hasDerivAt_eq_zero hD
  simp only [zero_mul, zero_add] at h0
  simp only [hd, mul_ite, mul_zero, mul_sub, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.sum_sub_distrib] at h0
  linear_combination h0

/-- **Exercise 20.6** (Miao, p. 735), the Euler equation for capital: for an agent with
`θᵢ > 0`, `W₁ⁱ = W₂ⁱ ∑ₛ Rₛⁱ uⁱ'(c₁ⁱ(s)) z₁(s) F'(k₁)`. -/
theorem ex_20_6_euler (θ : Fin n → ℝ) {W : Fin n → ℝ × ℝ → ℝ}
    {R : Fin n → (S → ℝ) → ℝ} {u : Fin n → ℝ → ℝ} {F : ℝ → ℝ} {z0 k0 : ℝ} {z1 : S → ℝ}
    {c0 : Fin n → ℝ} {k1 : ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' k1' c1', ∑ i, c0' i + k1' = z0 * F k0 → (∀ s, ∑ i, c1' s i = z1 s * F k1') →
      pa_planner θ W R u c0' c1' ≤ pa_planner θ W R u c0 c1)
    (hf0 : ∑ i, c0 i + k1 = z0 * F k0) (hf1 : ∀ s, ∑ i, c1 s i = z1 s * F k1)
    {DW : Fin n → ℝ × ℝ →L[ℝ] ℝ} {DR : Fin n → (S → ℝ) →L[ℝ] ℝ} {du : Fin n → S → ℝ}
    {dF : ℝ} (hW : ∀ i, HasFDerivAt (W i) (DW i) (c0 i, R i fun s => u i (c1 s i)))
    (hR : ∀ i, HasFDerivAt (R i) (DR i) fun s => u i (c1 s i))
    (hu : ∀ i s, HasDerivAt (u i) (du i s) (c1 s i)) (hF : HasDerivAt F dF k1) {i : Fin n}
    (hθ : 0 < θ i) :
    DW i (1, 0) = DW i (0, 1) * ∑ s, DR i (Pi.single s 1) * du i s * z1 s * dF := by
  set δ : Fin n → ℝ := fun l => if l = i then 1 else 0 with hδ
  have hFt : HasDerivAt (fun t => F (k1 + t)) dF 0 := by
    have := HasDerivAt.comp_add_const 0 k1 (by rwa [zero_add])
    simpa [add_comm] using this
  have hD := pa_planner_hasDerivAt θ hW hR hu (p0 := fun l t => c0 l - t * δ l)
    (p1 := fun s l t => c1 s l + δ l * z1 s * (F (k1 + t) - F k1))
    (d0 := fun l => -δ l) (d1 := fun s l => δ l * z1 s * dF)
    (fun l => by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (δ l)).const_sub (c0 l)
      simpa using this)
    (fun s l => by
      have := ((hFt.sub_const (F k1)).const_mul (δ l * z1 s)).const_add (c1 s l)
      simpa using this)
    (fun l => by simp) (fun s l => by simp)
  have hmax : IsLocalMax (fun t => pa_planner θ W R u (fun l => c0 l - t * δ l)
      fun s l => c1 s l + δ l * z1 s * (F (k1 + t) - F k1)) 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [zero_mul, sub_zero, add_zero, sub_self, mul_zero]
    refine hopt _ (k1 + t) _ ?_ fun s => ?_
    · rw [← hf0, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [hδ]
    · rw [Finset.sum_add_distrib, hf1 s, ← Finset.sum_mul, ← Finset.sum_mul]
      simp [hδ]
      ring
  have h0 := hmax.hasDerivAt_eq_zero hD
  rw [Finset.sum_eq_single i (fun l _ hl => by simp [hδ, hl]) (by simp)] at h0
  simp only [hδ, ↓reduceIte, neg_mul, one_mul] at h0
  have hsum : ∑ s, DR i (Pi.single s 1) * (du i s * (z1 s * dF))
      = ∑ s, DR i (Pi.single s 1) * du i s * z1 s * dF :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [hsum] at h0
  have := (mul_eq_zero.1 h0).resolve_left hθ.ne'
  linarith

/-! ### Exercise 20.7 -/

/-- The multiplier certainty equivalent `−ϑ ln ∑ₛ p(s) exp(−v(s)/ϑ)`. -/
noncomputable def pa_multCE (ϑ : ℝ) (p v : S → ℝ) : ℝ :=
  -ϑ * Real.log (∑ s, p s * Real.exp (-v s / ϑ))

/-- The worst-case distortion `m(s) = e^{−v(s)/ϑ}/∑ p e^{−v/ϑ}`. -/
noncomputable def pa_distortion (ϑ : ℝ) (p v : S → ℝ) (s : S) : ℝ :=
  Real.exp (-v s / ϑ) / ∑ s', p s' * Real.exp (-v s' / ϑ)

/-- Exercise 20.7: perturbing the continuation value in state `s` by `t·d`, the multiplier
certainty equivalent has derivative `p(s) m(s) d`. -/
theorem pa_multiplier_hasDerivAt {ϑ : ℝ} (hϑ : ϑ ≠ 0) {p v : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (s : S) (d : ℝ) :
    HasDerivAt (fun t => pa_multCE ϑ p (fun s' => v s' + if s' = s then t * d else 0))
      (p s * pa_distortion ϑ p v s * d) 0 := by
  have hpos : 0 < ∑ s', p s' * Real.exp (-v s' / ϑ) :=
    pa_E_pos hp hp1 fun s' => Real.exp_pos _
  have hterm : ∀ s', HasDerivAt
      (fun t => p s' * Real.exp (-(v s' + if s' = s then t * d else 0) / ϑ))
      (if s' = s then p s' * (Real.exp (-v s' / ϑ) * (-d / ϑ)) else 0) 0 := by
    intro s'
    by_cases hs : s' = s
    · subst hs
      simp only [↓reduceIte]
      have h := ((((hasDerivAt_id (0 : ℝ)).mul_const d).const_add (v s')).neg.div_const ϑ).exp
      have := h.const_mul (p s')
      simpa using this
    · simp only [hs, ↓reduceIte, add_zero]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => hterm s'
  have h0 : (∑ s', p s' * Real.exp (-(v s' + if s' = s then (0 : ℝ) * d else 0) / ϑ))
      = ∑ s', p s' * Real.exp (-v s' / ϑ) := by simp
  have hlog := (hsum.log (by rw [h0]; exact hpos.ne')).const_mul (-ϑ)
  unfold pa_multCE
  convert hlog using 1
  rw [h0]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, pa_distortion]
  field_simp

/-- Multiplier preferences `Uⁱ = uⁱ(c₀ⁱ) − βϑᵢ ln E exp(−uⁱ(c₁ⁱ)/ϑᵢ)` and the planner's
objective `∑ λᵢ Uⁱ`. -/
noncomputable def pa_multPlanner (lam ϑ : Fin n → ℝ) (β : ℝ) (p : S → ℝ) (u : Fin n → ℝ → ℝ)
    (c0 : Fin n → ℝ) (c1 : S → Fin n → ℝ) : ℝ :=
  ∑ i, lam i * (u i (c0 i) + β * pa_multCE (ϑ i) p fun s => u i (c1 s i))

omit [DecidableEq S] in
/-- **Exercise 20.7(a)** (Miao, p. 736): first-order conditions for a Pareto optimum with
multiplier preferences in the pure exchange economy (`∑ᵢ c₀ⁱ = e₀`, `∑ᵢ c₁ⁱ(s) = e₁(s)`):
`λᵢ uⁱ'(c₀ⁱ) = λⱼ uʲ'(c₀ʲ)` and, in each state with `p(s) > 0`,
`λᵢ mᵢ(s) uⁱ'(c₁ⁱ(s)) = λⱼ mⱼ(s) uʲ'(c₁ʲ(s))`. -/
theorem ex_20_7 {lam ϑ : Fin n → ℝ} {β : ℝ} (hβ : 0 < β) {p : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) (hϑ : ∀ i, ϑ i ≠ 0) {u du0 : Fin n → ℝ → ℝ} {du1 : Fin n → S → ℝ}
    {e0 : ℝ} {e1 : S → ℝ} {c0 : Fin n → ℝ} {c1 : S → Fin n → ℝ}
    (hopt : ∀ c0' c1', ∑ i, c0' i = e0 → (∀ s, ∑ i, c1' s i = e1 s) →
      pa_multPlanner lam ϑ β p u c0' c1' ≤ pa_multPlanner lam ϑ β p u c0 c1)
    (hf0 : ∑ i, c0 i = e0) (hf1 : ∀ s, ∑ i, c1 s i = e1 s)
    (hu0 : ∀ i, HasDerivAt (u i) (du0 i (c0 i)) (c0 i))
    (hu1 : ∀ i s, HasDerivAt (u i) (du1 i s) (c1 s i)) {i j : Fin n} :
    lam i * du0 i (c0 i) = lam j * du0 j (c0 j) ∧
    ∀ s, 0 < p s → lam i * pa_distortion (ϑ i) p (fun s => u i (c1 s i)) s * du1 i s
      = lam j * pa_distortion (ϑ j) p (fun s => u j (c1 s j)) s * du1 j s := by
  classical
  set d : Fin n → ℝ := fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0) with hd
  have hdsum : ∑ l, d l = 0 := by simp [hd, Finset.sum_sub_distrib]
  constructor
  · have hD : HasDerivAt (fun t => pa_multPlanner lam ϑ β p u (fun l => c0 l + t * d l) c1)
        (∑ l, lam l * (du0 l (c0 l) * d l)) 0 := by
      unfold pa_multPlanner
      refine HasDerivAt.fun_sum fun l _ => HasDerivAt.const_mul (lam l) ?_
      have := ((hu0 l).comp_of_eq 0 (((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c0 l))
        (by simp)).add_const (β * pa_multCE (ϑ l) p fun s => u l (c1 s l))
      simpa using this
    have hmax : IsLocalMax (fun t => pa_multPlanner lam ϑ β p u (fun l => c0 l + t * d l) c1)
        0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [zero_mul, add_zero]
      refine hopt _ c1 ?_ hf1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdsum, mul_zero, add_zero, hf0]
    have h0 := hmax.hasDerivAt_eq_zero hD
    simp only [hd, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
    linarith
  · intro s hs
    have hD : HasDerivAt (fun t => pa_multPlanner lam ϑ β p u c0
          fun s' l => c1 s' l + if s' = s then t * d l else 0)
        (∑ l, lam l * (β * (p s * pa_distortion (ϑ l) p (fun s => u l (c1 s l)) s
          * (du1 l s * d l)))) 0 := by
      unfold pa_multPlanner
      refine HasDerivAt.fun_sum fun l _ => HasDerivAt.const_mul (lam l) ?_
      refine HasDerivAt.const_add _ (HasDerivAt.const_mul β ?_)
      -- the continuation value moves only in state `s`, to first order by `t u'(c₁(s)) d`
      have hcomp : HasDerivAt (fun t => pa_multCE (ϑ l) p
          fun s' => u l (c1 s' l + if s' = s then t * d l else 0))
          (p s * pa_distortion (ϑ l) p (fun s => u l (c1 s l)) s * (du1 l s * d l)) 0 := by
        have hus : HasDerivAt (fun t => u l (c1 s l + t * d l)) (du1 l s * d l) 0 := by
          have := (hu1 l s).comp_of_eq 0
            (((hasDerivAt_id (0 : ℝ)).mul_const (d l)).const_add (c1 s l)) (by simp)
          rw [one_mul] at this
          exact this
        have hpos : 0 < ∑ s', p s' * Real.exp (-u l (c1 s' l) / ϑ l) :=
          pa_E_pos hp hp1 fun s' => Real.exp_pos _
        have hterm : ∀ s', HasDerivAt (fun t => p s' *
            Real.exp (-u l (c1 s' l + if s' = s then t * d l else 0) / ϑ l))
            (if s' = s then p s' * (Real.exp (-u l (c1 s' l) / ϑ l) *
              (-(du1 l s * d l) / ϑ l)) else 0) 0 := by
          intro s'
          by_cases h : s' = s
          · subst h
            simp only [↓reduceIte]
            have := (((hus.neg).div_const (ϑ l)).exp).const_mul (p s')
            simpa using this
          · simp only [h, ↓reduceIte, add_zero]
            exact hasDerivAt_const _ _
        have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ => hterm s'
        have h0 : (∑ s', p s' * Real.exp (-u l (c1 s' l + if s' = s then (0 : ℝ) * d l else 0)
            / ϑ l)) = ∑ s', p s' * Real.exp (-u l (c1 s' l) / ϑ l) := by simp
        have hlog := (hsum.log (by rw [h0]; exact hpos.ne')).const_mul (-ϑ l)
        unfold pa_multCE
        convert hlog using 1
        rw [h0]
        have := hϑ l
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, pa_distortion]
        field_simp
      exact hcomp
    have hmax : IsLocalMax (fun t => pa_multPlanner lam ϑ β p u c0
        fun s' l => c1 s' l + if s' = s then t * d l else 0) 0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [zero_mul, ite_self, add_zero]
      refine hopt _ _ hf0 fun s' => ?_
      rw [Finset.sum_add_distrib, hf1 s']
      by_cases h : s' = s
      · simp only [h, ↓reduceIte, ← Finset.mul_sum, hdsum, mul_zero, add_zero]
      · simp [h]
    have h0 := hmax.hasDerivAt_eq_zero hD
    simp only [hd, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
    have hk : 0 < β * p s := mul_pos hβ hs
    have : β * p s * (lam i * pa_distortion (ϑ i) p (fun s => u i (c1 s i)) s * du1 i s
        - lam j * pa_distortion (ϑ j) p (fun s => u j (c1 s j)) s * du1 j s) = 0 := by
      rw [← h0]; ring
    have := (mul_eq_zero.1 this).resolve_left hk.ne'
    linarith

end Miao.RecursiveUtility

set_option linter.style.longLine false
#print axioms Miao.RecursiveUtility.SS.IsMarkov
#print axioms Miao.RecursiveUtility.SS.IsMarkov.mk
#print axioms Miao.RecursiveUtility.SS.IsMarkov.nonneg
#print axioms Miao.RecursiveUtility.SS.IsMarkov.rowsum
#print axioms Miao.RecursiveUtility.SS.IsDistribution
#print axioms Miao.RecursiveUtility.SS.IsDistribution.mk
#print axioms Miao.RecursiveUtility.SS.IsDistribution.nonneg
#print axioms Miao.RecursiveUtility.SS.IsDistribution.sum_eq_one
#print axioms Miao.RecursiveUtility.SS.mulVec_apply_eq
#print axioms Miao.RecursiveUtility.SS.IsMarkov.mul
#print axioms Miao.RecursiveUtility.SS.IsMarkov.pow
#print axioms Miao.RecursiveUtility.SS.IsMarkov.mulVec_le_mulVec
#print axioms Miao.RecursiveUtility.SS.IsMarkov.mulVec_const
#print axioms Miao.RecursiveUtility.SS.IsMarkov.abs_mulVec_le
#print axioms Miao.RecursiveUtility.SS.IsMarkov.norm_mulVec_le
#print axioms Miao.RecursiveUtility.SS.IsMarkov.abs_mulVec_sub_le
#print axioms Miao.RecursiveUtility.SS.GloballyStable
#print axioms Miao.RecursiveUtility.SS.IsContractionOn
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.mk
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.mapsTo
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.nonneg
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.lt_one
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.norm_sub_le
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.fixedPt_unique
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.iterate_mem
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.tendsto_iterate_fixedPt
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.exists_fixedPt
#print axioms Miao.RecursiveUtility.SS.IsContractionOn.globallyStable_univ
#print axioms Miao.RecursiveUtility.SS.fixedPt_le_of_le
#print axioms Miao.RecursiveUtility.SS.le_fixedPt_of_le_apply
#print axioms Miao.RecursiveUtility.SS.isContractionOn_of_blackwell
#print axioms Miao.RecursiveUtility.SS.abs_sup'_sub_sup'_le
#print axioms Miao.RecursiveUtility.SS.pow_nonneg_entries
#print axioms Miao.RecursiveUtility.SS.pow_le_pow_entries
#print axioms Miao.RecursiveUtility.SS.complexify
#print axioms Miao.RecursiveUtility.SS.complexify_apply
#print axioms Miao.RecursiveUtility.SS.complexify_pow
#print axioms Miao.RecursiveUtility.SS.complexify_transpose
#print axioms Miao.RecursiveUtility.SS.nnnorm_complexify
#print axioms Miao.RecursiveUtility.SS.norm_complexify
#print axioms Miao.RecursiveUtility.SS.specRad
#print axioms Miao.RecursiveUtility.SS.spectralRadius_complexify_ne_top
#print axioms Miao.RecursiveUtility.SS.specRad_nonneg
#print axioms Miao.RecursiveUtility.SS.mem_spectrum_iff_eigenpair
#print axioms Miao.RecursiveUtility.SS.tendsto_norm_pow_rpow
#print axioms Miao.RecursiveUtility.SS.eventually_norm_pow_le
#print axioms Miao.RecursiveUtility.SS.tendsto_norm_pow_zero
#print axioms Miao.RecursiveUtility.SS.summable_pow
#print axioms Miao.RecursiveUtility.SS.one_sub_mul_tsum
#print axioms Miao.RecursiveUtility.SS.tsum_mul_one_sub
#print axioms Miao.RecursiveUtility.SS.neumann_series
#print axioms Miao.RecursiveUtility.SS.specRad_transpose
#print axioms Miao.RecursiveUtility.SS.norm_le_norm_of_abs_le
#print axioms Miao.RecursiveUtility.SS.specRad_le_of_le
#print axioms Miao.RecursiveUtility.SS.rowsum_abs_le_norm
#print axioms Miao.RecursiveUtility.SS.norm_le_of_rowsum_abs_le
#print axioms Miao.RecursiveUtility.SS.abs_entry_le_norm
#print axioms Miao.RecursiveUtility.SS.norm_eq_of_rowsum_eq
#print axioms Miao.RecursiveUtility.SS.specRad_le_norm
#print axioms Miao.RecursiveUtility.SS.norm_le_specRad_of_mem_spectrum
#print axioms Miao.RecursiveUtility.SS.specRad_eq_of_rowsum_eq
#print axioms Miao.RecursiveUtility.SS.specRad_eq_of_colsum_eq
#print axioms Miao.RecursiveUtility.SS.eventually_abs_entry_pow_le
#print axioms Miao.RecursiveUtility.SS.resPartial
#print axioms Miao.RecursiveUtility.SS.res
#print axioms Miao.RecursiveUtility.SS.res_apply
#print axioms Miao.RecursiveUtility.SS.smul_one_sub_mul_resPartial
#print axioms Miao.RecursiveUtility.SS.resPartial_mul_smul_one_sub
#print axioms Miao.RecursiveUtility.SS.resPartial_apply
#print axioms Miao.RecursiveUtility.SS.summable_res_entry
#print axioms Miao.RecursiveUtility.SS.tendsto_resPartial_apply
#print axioms Miao.RecursiveUtility.SS.tendsto_inv_pow_mul_apply
#print axioms Miao.RecursiveUtility.SS.smul_one_sub_mul_res
#print axioms Miao.RecursiveUtility.SS.res_mul_smul_one_sub
#print axioms Miao.RecursiveUtility.SS.res_nonneg
#print axioms Miao.RecursiveUtility.SS.inv_le_res_diag
#print axioms Miao.RecursiveUtility.SS.exists_mem_spectrum_norm_eq
#print axioms Miao.RecursiveUtility.SS.eventually_norm_entry_pow_complexify_le
#print axioms Miao.RecursiveUtility.SS.smul_one_sub_mul_res_real
#print axioms Miao.RecursiveUtility.SS.norm_res_complexify_le
#print axioms Miao.RecursiveUtility.SS.norm_le_card_mul_of_entry_norm_le
#print axioms Miao.RecursiveUtility.SS.notMem_spectrum_of_res_bounded
#print axioms Miao.RecursiveUtility.SS.exists_res_entry_gt
#print axioms Miao.RecursiveUtility.SS.isCompact_simplex
#print axioms Miao.RecursiveUtility.SS.perron_frobenius
#print axioms Miao.RecursiveUtility.SS.perron_frobenius_left
#print axioms Miao.RecursiveUtility.SS.le_specRad_of_colsum_ge
#print axioms Miao.RecursiveUtility.SS.specRad_le_of_colsum_le
#print axioms Miao.RecursiveUtility.SS.le_specRad_of_rowsum_ge
#print axioms Miao.RecursiveUtility.SS.specRad_le_of_rowsum_le
#print axioms Miao.RecursiveUtility.SS.tendsto_rpow_one_div_natCast
#print axioms Miao.RecursiveUtility.SS.norm_pow_mul_le_norm_mulVec
#print axioms Miao.RecursiveUtility.SS.tendsto_norm_pow_mulVec_rpow
#print axioms Miao.RecursiveUtility.SS.IsMarkov.specRad_eq_one
#print axioms Miao.RecursiveUtility.SS.IsMarkov.exists_stationary
#print axioms Miao.RecursiveUtility.SS.IsMarkov.not_mulVec_ge_add
#print axioms Miao.RecursiveUtility.SS.Irreducible
#print axioms Miao.RecursiveUtility.SS.irreducible_of_pos
#print axioms Miao.RecursiveUtility.SS.Irreducible.transpose
#print axioms Miao.RecursiveUtility.SS.pow_mulVec_eq_of_mulVec_eq
#print axioms Miao.RecursiveUtility.SS.Irreducible.pos_of_mulVec_eq_smul
#print axioms Miao.RecursiveUtility.SS.Irreducible.specRad_pos
#print axioms Miao.RecursiveUtility.SS.Irreducible.exists_pos_eigenvector
#print axioms Miao.RecursiveUtility.SS.Irreducible.exists_pos_left_eigenvector
#print axioms Miao.RecursiveUtility.SS.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms Miao.RecursiveUtility.SS.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms Miao.RecursiveUtility.SS.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms Miao.RecursiveUtility.SS.discountOp
#print axioms Miao.RecursiveUtility.SS.discountOp_apply
#print axioms Miao.RecursiveUtility.SS.discountOp_nonneg
#print axioms Miao.RecursiveUtility.SS.discountOp_const
#print axioms Miao.RecursiveUtility.SS.specRad_smul_isMarkov
#print axioms Miao.RecursiveUtility.SS.summable_pow_apply
#print axioms Miao.RecursiveUtility.SS.summable_pow_mulVec
#print axioms Miao.RecursiveUtility.SS.mulVec_tsum_pow_mulVec
#print axioms Miao.RecursiveUtility.SS.tsum_pow_mulVec_eq
#print axioms Miao.RecursiveUtility.SS.eq_of_eq_add_mulVec
#print axioms Miao.RecursiveUtility.SS.inv_mulVec_eq_add
#print axioms Miao.RecursiveUtility.SS.inv_mulVec_eq_tsum
#print axioms Miao.RecursiveUtility.SS.eq_add_mulVec_iff
#print axioms Miao.RecursiveUtility.SS.specRad_lt_one_iff_existsUnique_pos
#print axioms Miao.RecursiveUtility.SS.globallyStable_of_iterate_contraction
#print axioms Miao.RecursiveUtility.SS.globallyStable_of_iterate_contraction_univ
#print axioms Miao.RecursiveUtility.SS.affineOp
#print axioms Miao.RecursiveUtility.SS.affineOp_iterate_sub
#print axioms Miao.RecursiveUtility.SS.exists_isContractionOn_iterate_affineOp
#print axioms Miao.RecursiveUtility.SS.globallyStable_affineOp
#print axioms Miao.RecursiveUtility.SS.isFixedPt_affineOp_inv
#print axioms Miao.RecursiveUtility.SS.mulVec_le_mulVec_of_nonneg
#print axioms Miao.RecursiveUtility.SS.norm_abs_fun
#print axioms Miao.RecursiveUtility.SS.norm_le_norm_of_abs_le_fun
#print axioms Miao.RecursiveUtility.SS.abs_iterate_sub_le_pow_mulVec
#print axioms Miao.RecursiveUtility.SS.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms Miao.RecursiveUtility.SS.globallyStable_of_abs_sub_le
#print axioms Miao.RecursiveUtility.SS.GloballyStableOn
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_univ_iff
#print axioms Miao.RecursiveUtility.SS.GloballyStableOn.existsUnique
#print axioms Miao.RecursiveUtility.SS.GloballyStableOn.of_conj
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_iff_of_conj
#print axioms Miao.RecursiveUtility.SS.iterate_le_iterate_of_monotoneOn
#print axioms Miao.RecursiveUtility.SS.knaster_tarski
#print axioms Miao.RecursiveUtility.SS.exists_continuum_fixedPts
#print axioms Miao.RecursiveUtility.SS.du_concave
#print axioms Miao.RecursiveUtility.SS.exists_delta_of_lt
#print axioms Miao.RecursiveUtility.SS.du_concave_of_lt
#print axioms Miao.RecursiveUtility.SS.neg_mem_Icc_iff
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_of_reflect
#print axioms Miao.RecursiveUtility.SS.du_convex
#print axioms Miao.RecursiveUtility.SS.du_convex_of_lt
#print axioms Miao.RecursiveUtility.SS.concaveOn_comp
#print axioms Miao.RecursiveUtility.SS.posCone
#print axioms Miao.RecursiveUtility.SS.convex_posCone
#print axioms Miao.RecursiveUtility.SS.Irreducible.exists_pos_row
#print axioms Miao.RecursiveUtility.SS.mulVec_pos_of_row
#print axioms Miao.RecursiveUtility.SS.Irreducible.of_pos_mul
#print axioms Miao.RecursiveUtility.SS.powF
#print axioms Miao.RecursiveUtility.SS.powF_pos
#print axioms Miao.RecursiveUtility.SS.powF_monotoneOn
#print axioms Miao.RecursiveUtility.SS.hasDerivAt_powF
#print axioms Miao.RecursiveUtility.SS.continuousOn_powF
#print axioms Miao.RecursiveUtility.SS.differentiableOn_powF
#print axioms Miao.RecursiveUtility.SS.convexOn_powF
#print axioms Miao.RecursiveUtility.SS.concaveOn_powF
#print axioms Miao.RecursiveUtility.SS.powG
#print axioms Miao.RecursiveUtility.SS.powG_apply
#print axioms Miao.RecursiveUtility.SS.powG_mapsTo
#print axioms Miao.RecursiveUtility.SS.powG_monotoneOn
#print axioms Miao.RecursiveUtility.SS.convexOn_powG
#print axioms Miao.RecursiveUtility.SS.concaveOn_powG
#print axioms Miao.RecursiveUtility.SS.specRad_rpow_lt_one_of_isFixedPt
#print axioms Miao.RecursiveUtility.SS.not_isFixedPt_powG
#print axioms Miao.RecursiveUtility.SS.scalar_bounds
#print axioms Miao.RecursiveUtility.SS.powG_smul_eigen
#print axioms Miao.RecursiveUtility.SS.exists_thresholds
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_powG_Icc
#print axioms Miao.RecursiveUtility.SS.exists_interval
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_powG
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_powG_iff
#print axioms Miao.RecursiveUtility.SS.kleinmanA
#print axioms Miao.RecursiveUtility.SS.IsKleinmanSol
#print axioms Miao.RecursiveUtility.SS.isKleinmanSol_iff
#print axioms Miao.RecursiveUtility.SS.existsUnique_kleinmanSol_iff
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.mk
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.mapsTo
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.mono
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.const
#print axioms Miao.RecursiveUtility.SS.IsMarkov.isCertEquiv
#print axioms Miao.RecursiveUtility.SS.isCertEquiv_mulVec_iff
#print axioms Miao.RecursiveUtility.SS.IsMarkov.mulVec_pos
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.zero_and_nonneg
#print axioms Miao.RecursiveUtility.SS.IsCertEquiv.convex_comb
#print axioms Miao.RecursiveUtility.SS.PosHomogeneous
#print axioms Miao.RecursiveUtility.SS.Superadditive
#print axioms Miao.RecursiveUtility.SS.Subadditive
#print axioms Miao.RecursiveUtility.SS.ConstSubadditive
#print axioms Miao.RecursiveUtility.SS.mulVec_properties
#print axioms Miao.RecursiveUtility.SS.nonexpansive_of_constSubadditive
#print axioms Miao.RecursiveUtility.SS.convexOn_of_subadditive
#print axioms Miao.RecursiveUtility.SS.concaveOn_of_superadditive
#print axioms Miao.RecursiveUtility.SS.entR
#print axioms Miao.RecursiveUtility.SS.entR_add_const
#print axioms Miao.RecursiveUtility.SS.isCertEquiv_entR
#print axioms Miao.RecursiveUtility.SS.constSubadditive_entR
#print axioms Miao.RecursiveUtility.SS.log_sum_exp_le
#print axioms Miao.RecursiveUtility.SS.concaveOn_entR
#print axioms Miao.RecursiveUtility.SS.kpR
#print axioms Miao.RecursiveUtility.SS.kpR_pos
#print axioms Miao.RecursiveUtility.SS.isCertEquiv_kpR
#print axioms Miao.RecursiveUtility.SS.posHomogeneous_kpR
#print axioms Miao.RecursiveUtility.SS.sum_rpow_normalize
#print axioms Miao.RecursiveUtility.SS.sum_rpow_add_le
#print axioms Miao.RecursiveUtility.SS.le_sum_rpow_add
#print axioms Miao.RecursiveUtility.SS.convexOn_rpow_of_neg
#print axioms Miao.RecursiveUtility.SS.subadditive_kpR
#print axioms Miao.RecursiveUtility.SS.superadditive_kpR
#print axioms Miao.RecursiveUtility.SS.smul_mem_posCone
#print axioms Miao.RecursiveUtility.SS.convexOn_kpR
#print axioms Miao.RecursiveUtility.SS.concaveOn_kpR
#print axioms Miao.RecursiveUtility.SS.condCdf
#print axioms Miao.RecursiveUtility.SS.quantR
#print axioms Miao.RecursiveUtility.SS.isLeast_quantR
#print axioms Miao.RecursiveUtility.SS.isCertEquiv_quantR
#print axioms Miao.RecursiveUtility.SS.quantR_add_const
#print axioms Miao.RecursiveUtility.SS.constSubadditive_quantR
#print axioms Miao.RecursiveUtility.SS.MonotoneKernel
#print axioms Miao.RecursiveUtility.SS.MonotoneKernel.antitone
#print axioms Miao.RecursiveUtility.SS.monotone_entR
#print axioms Miao.RecursiveUtility.SS.monotone_kpR
#print axioms Miao.RecursiveUtility.SS.IsAggregator
#print axioms Miao.RecursiveUtility.SS.IsAggregator.mk
#print axioms Miao.RecursiveUtility.SS.IsAggregator.values
#print axioms Miao.RecursiveUtility.SS.IsAggregator.mapsTo
#print axioms Miao.RecursiveUtility.SS.IsAggregator.mono
#print axioms Miao.RecursiveUtility.SS.leontief
#print axioms Miao.RecursiveUtility.SS.uzawa
#print axioms Miao.RecursiveUtility.SS.cesAgg
#print axioms Miao.RecursiveUtility.SS.additive
#print axioms Miao.RecursiveUtility.SS.cesUzawa
#print axioms Miao.RecursiveUtility.SS.additive_eq_uzawa
#print axioms Miao.RecursiveUtility.SS.additive_eq_cesAgg
#print axioms Miao.RecursiveUtility.SS.isAggregator_leontief
#print axioms Miao.RecursiveUtility.SS.isAggregator_uzawa
#print axioms Miao.RecursiveUtility.SS.isAggregator_additive
#print axioms Miao.RecursiveUtility.SS.isAggregator_cesUzawa
#print axioms Miao.RecursiveUtility.SS.isAggregator_cesAgg
#print axioms Miao.RecursiveUtility.SS.koopmans
#print axioms Miao.RecursiveUtility.SS.koopmans_mapsTo_monotoneOn
#print axioms Miao.RecursiveUtility.SS.koopmans_additive_entR
#print axioms Miao.RecursiveUtility.SS.koopmans_cesAgg_kpR
#print axioms Miao.RecursiveUtility.SS.koopmans_additive_mulVec
#print axioms Miao.RecursiveUtility.SS.ces_eis
#print axioms Miao.RecursiveUtility.SS.iterate_additive_eq
#print axioms Miao.RecursiveUtility.SS.additive_lifetimeValue
#print axioms Miao.RecursiveUtility.SS.monotone_of_globallyStableOn
#print axioms Miao.RecursiveUtility.SS.monotone_koopmans_fixedPt
#print axioms Miao.RecursiveUtility.SS.IsBlackwellAgg
#print axioms Miao.RecursiveUtility.SS.isBlackwellAgg_additive
#print axioms Miao.RecursiveUtility.SS.isBlackwellAgg_leontief
#print axioms Miao.RecursiveUtility.SS.isContractionOn_koopmans
#print axioms Miao.RecursiveUtility.SS.globallyStable_koopmans
#print axioms Miao.RecursiveUtility.SS.globallyStable_riskSensitive
#print axioms Miao.RecursiveUtility.SS.globallyStable_leontief
#print axioms Miao.RecursiveUtility.SS.globallyStable_quantile
#print axioms Miao.RecursiveUtility.SS.globallyStable_leontief_quantile
#print axioms Miao.RecursiveUtility.SS.koopmans_uzawa_mulVec
#print axioms Miao.RecursiveUtility.SS.uzawa_lifetimeValue
#print axioms Miao.RecursiveUtility.SS.irreducible_uzawa
#print axioms Miao.RecursiveUtility.SS.uzawa_no_pos_fixedPt
#print axioms Miao.RecursiveUtility.SS.nonnegCone
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_uzawa_concave
#print axioms Miao.RecursiveUtility.SS.ezK
#print axioms Miao.RecursiveUtility.SS.ezK_eq_koopmans
#print axioms Miao.RecursiveUtility.SS.ezK_apply_ez
#print axioms Miao.RecursiveUtility.SS.ezK_mapsTo
#print axioms Miao.RecursiveUtility.SS.powMap
#print axioms Miao.RecursiveUtility.SS.powMap_mapsTo
#print axioms Miao.RecursiveUtility.SS.powMap_inv
#print axioms Miao.RecursiveUtility.SS.powMap_inv'
#print axioms Miao.RecursiveUtility.SS.continuousOn_powMap
#print axioms Miao.RecursiveUtility.SS.ezB
#print axioms Miao.RecursiveUtility.SS.powMap_ezK
#print axioms Miao.RecursiveUtility.SS.irreducible_ezB
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_ezK_iff
#print axioms Miao.RecursiveUtility.SS.globallyStableOn_ez
#print axioms Miao.RecursiveUtility.SS.ez_deriv_tendsto_atTop
#print axioms Miao.RecursiveUtility.SS.monotone_ez_lifetimeValue
#print axioms Miao.RecursiveUtility.SS.RDP
#print axioms Miao.RecursiveUtility.SS.RDP.mk
#print axioms Miao.RecursiveUtility.SS.RDP.Γ
#print axioms Miao.RecursiveUtility.SS.RDP.Γ_nonempty
#print axioms Miao.RecursiveUtility.SS.RDP.V
#print axioms Miao.RecursiveUtility.SS.RDP.B
#print axioms Miao.RecursiveUtility.SS.RDP.mono
#print axioms Miao.RecursiveUtility.SS.RDP.consistent
#print axioms Miao.RecursiveUtility.SS.RDP.IsFeasible
#print axioms Miao.RecursiveUtility.SS.RDP.Policy
#print axioms Miao.RecursiveUtility.SS.RDP.defaultPolicy
#print axioms Miao.RecursiveUtility.SS.RDP.policy_nonempty
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_apply
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_mapsTo
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_monotoneOn
#print axioms Miao.RecursiveUtility.SS.RDP.WellPosed
#print axioms Miao.RecursiveUtility.SS.RDP.IsGloballyStable
#print axioms Miao.RecursiveUtility.SS.RDP.IsGloballyStable.wellPosed
#print axioms Miao.RecursiveUtility.SS.RDP.IsContinuous
#print axioms Miao.RecursiveUtility.SS.RDP.vσ
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_spec
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_mem
#print axioms Miao.RecursiveUtility.SS.RDP.isFixedPt_vσ
#print axioms Miao.RecursiveUtility.SS.RDP.eq_vσ_of_isFixedPt
#print axioms Miao.RecursiveUtility.SS.RDP.tendsto_iterate_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.T
#print axioms Miao.RecursiveUtility.SS.RDP.B_le_T
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_le_T
#print axioms Miao.RecursiveUtility.SS.RDP.IsGreedy
#print axioms Miao.RecursiveUtility.SS.RDP.greedy
#print axioms Miao.RecursiveUtility.SS.RDP.greedy_mem
#print axioms Miao.RecursiveUtility.SS.RDP.isGreedy_greedy
#print axioms Miao.RecursiveUtility.SS.RDP.greedyPolicy
#print axioms Miao.RecursiveUtility.SS.RDP.isGreedy_iff_Tσ_eq_T
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_eq_T_of_isGreedy
#print axioms Miao.RecursiveUtility.SS.RDP.T_mapsTo
#print axioms Miao.RecursiveUtility.SS.RDP.T_monotoneOn
#print axioms Miao.RecursiveUtility.SS.RDP.T_apply_eq_sup'
#print axioms Miao.RecursiveUtility.SS.RDP.isGreatest_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.antiGreedy
#print axioms Miao.RecursiveUtility.SS.RDP.isLeast_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.iterate_T_succ
#print axioms Miao.RecursiveUtility.SS.RDP.iterate_Tσ_succ
#print axioms Miao.RecursiveUtility.SS.RDP.iterate_T_mono
#print axioms Miao.RecursiveUtility.SS.RDP.iterate_Tσ_mono
#print axioms Miao.RecursiveUtility.SS.RDP.vstar
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_le_vstar
#print axioms Miao.RecursiveUtility.SS.RDP.IsOptimal
#print axioms Miao.RecursiveUtility.SS.RDP.PrincipleOfOptimality
#print axioms Miao.RecursiveUtility.SS.RDP.howard
#print axioms Miao.RecursiveUtility.SS.RDP.opiW
#print axioms Miao.RecursiveUtility.SS.RDP.hpiPolicy
#print axioms Miao.RecursiveUtility.SS.RDP.hpiValue
#print axioms Miao.RecursiveUtility.SS.RDP.hpiValue_succ
#print axioms Miao.RecursiveUtility.SS.RDP.opiValue
#print axioms Miao.RecursiveUtility.SS.RDP.opiValue_one
#print axioms Miao.RecursiveUtility.SS.RDP.nonstationary_le
#print axioms Miao.RecursiveUtility.SS.RDP.Comparable
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_le_of_Tσ_le
#print axioms Miao.RecursiveUtility.SS.RDP.le_vσ_of_le_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.IsGloballyStable.comparable
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_le_vσ_greedy
#print axioms Miao.RecursiveUtility.SS.RDP.eq_vσ_greedy_of_isFixedPt
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_le_of_isFixedPt
#print axioms Miao.RecursiveUtility.SS.RDP.hpiValue_mono
#print axioms Miao.RecursiveUtility.SS.RDP.exists_hpiValue_succ_eq
#print axioms Miao.RecursiveUtility.SS.RDP.isFixedPt_T_hpiValue
#print axioms Miao.RecursiveUtility.SS.RDP.vstar_spec
#print axioms Miao.RecursiveUtility.SS.RDP.eq_vstar_of_isFixedPt
#print axioms Miao.RecursiveUtility.SS.RDP.principleOfOptimality
#print axioms Miao.RecursiveUtility.SS.RDP.exists_isOptimal
#print axioms Miao.RecursiveUtility.SS.RDP.hpi_terminates
#print axioms Miao.RecursiveUtility.SS.RDP.tendsto_iterate_T_vσ
#print axioms Miao.RecursiveUtility.SS.RDP.opiValue_spec
#print axioms Miao.RecursiveUtility.SS.RDP.opi_converges
#print axioms Miao.RecursiveUtility.SS.RDP.optimality_of_globallyStable
#print axioms Miao.RecursiveUtility.SS.RDP.nonstationary_le_vstar
#print axioms Miao.RecursiveUtility.SS.RDP.IsBoundedBy
#print axioms Miao.RecursiveUtility.SS.RDP.Tσ_mapsTo_Icc
#print axioms Miao.RecursiveUtility.SS.RDP.restrictIcc
#print axioms Miao.RecursiveUtility.SS.RDP.exists_fixedPt_Icc
#print axioms Miao.RecursiveUtility.SS.RDP.vσ_mem_Icc
#print axioms Miao.RecursiveUtility.SS.RDP.comparable_of_bounded
#print axioms Miao.RecursiveUtility.SS.RDP.optimality_of_bounded
#print axioms Miao.RecursiveUtility.SS.continuousOn_comp_pi
#print axioms Miao.RecursiveUtility.SS.RDP.isGloballyStable_iff_of_conj
#print axioms Miao.RecursiveUtility.SS.kernelAt
#print axioms Miao.RecursiveUtility.SS.kernelAt_apply
#print axioms Miao.RecursiveUtility.SS.isMarkov_kernelAt
#print axioms Miao.RecursiveUtility.SS.MDP
#print axioms Miao.RecursiveUtility.SS.MDP.mk
#print axioms Miao.RecursiveUtility.SS.MDP.Γ
#print axioms Miao.RecursiveUtility.SS.MDP.Γ_nonempty
#print axioms Miao.RecursiveUtility.SS.MDP.β
#print axioms Miao.RecursiveUtility.SS.MDP.β_pos
#print axioms Miao.RecursiveUtility.SS.MDP.β_lt_one
#print axioms Miao.RecursiveUtility.SS.MDP.r
#print axioms Miao.RecursiveUtility.SS.MDP.P
#print axioms Miao.RecursiveUtility.SS.MDP.P_nonneg
#print axioms Miao.RecursiveUtility.SS.MDP.P_rowsum
#print axioms Miao.RecursiveUtility.SS.MDP.isMarkov_P
#print axioms Miao.RecursiveUtility.SS.MDP.Pσ
#print axioms Miao.RecursiveUtility.SS.MDP.isMarkov_Pσ
#print axioms Miao.RecursiveUtility.SS.MDP.rσ
#print axioms Miao.RecursiveUtility.SS.MDP.toRDP
#print axioms Miao.RecursiveUtility.SS.MDP.toRDP_B
#print axioms Miao.RecursiveUtility.SS.MDP.toRDP_Tσ
#print axioms Miao.RecursiveUtility.SS.cakeEating
#print axioms Miao.RecursiveUtility.SS.stopping
#print axioms Miao.RecursiveUtility.SS.stopping_T
#print axioms Miao.RecursiveUtility.SS.stokeyLucas
#print axioms Miao.RecursiveUtility.SS.stokeyLucas_B
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount
#print axioms Miao.RecursiveUtility.SS.MDP.riskSensitive
#print axioms Miao.RecursiveUtility.SS.MDP.riskSensitive_B
#print axioms Miao.RecursiveUtility.SS.MDP.quantile
#print axioms Miao.RecursiveUtility.SS.ezAgg_monotoneOn
#print axioms Miao.RecursiveUtility.SS.MDP.epsteinZin
#print axioms Miao.RecursiveUtility.SS.MDP.epsteinZin_B
#print axioms Miao.RecursiveUtility.SS.pathRDP
#print axioms Miao.RecursiveUtility.SS.pathRDP_not_wellPosed
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting.isContractionOn_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting.isContractionOn_T
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting.isContinuous
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting.isGloballyStable
#print axioms Miao.RecursiveUtility.SS.RDP.IsContracting.norm_vstar_sub_vσ_le
#print axioms Miao.RecursiveUtility.SS.RDP.SatisfiesBlackwell
#print axioms Miao.RecursiveUtility.SS.RDP.SatisfiesBlackwell.isContracting
#print axioms Miao.RecursiveUtility.SS.RDP.SatisfiesBlackwell.isBoundedBy
#print axioms Miao.RecursiveUtility.SS.MDP.satisfiesBlackwell
#print axioms Miao.RecursiveUtility.SS.MDP.isContracting
#print axioms Miao.RecursiveUtility.SS.MDP.isGloballyStable
#print axioms Miao.RecursiveUtility.SS.MDP.vσ_eq
#print axioms Miao.RecursiveUtility.SS.MDP.isBoundedBy
#print axioms Miao.RecursiveUtility.SS.stopping_satisfiesBlackwell
#print axioms Miao.RecursiveUtility.SS.stopping_isContracting
#print axioms Miao.RecursiveUtility.SS.stopping_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.stopping_isBoundedBy
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount_satisfiesBlackwell
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount_isContracting
#print axioms Miao.RecursiveUtility.SS.savings_satisfiesBlackwell
#print axioms Miao.RecursiveUtility.SS.quantileJobSearch
#print axioms Miao.RecursiveUtility.SS.quantileJobSearch_isContracting
#print axioms Miao.RecursiveUtility.SS.riskSensitiveJobSearch
#print axioms Miao.RecursiveUtility.SS.riskSensitiveJobSearch_isContracting
#print axioms Miao.RecursiveUtility.SS.optimalDefault
#print axioms Miao.RecursiveUtility.SS.optimalDefault_isContracting
#print axioms Miao.RecursiveUtility.SS.MDP.riskSensitive_isContracting
#print axioms Miao.RecursiveUtility.SS.MDP.riskSensitive_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.MDP.quantile_isContracting
#print axioms Miao.RecursiveUtility.SS.MDP.quantile_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.RDP.Lσ
#print axioms Miao.RecursiveUtility.SS.RDP.IsEventuallyContracting
#print axioms Miao.RecursiveUtility.SS.RDP.IsEventuallyContracting.isGloballyStable
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount_isEventuallyContracting
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.MDP.absReward
#print axioms Miao.RecursiveUtility.SS.MDP.withDiscount_isBoundedBy
#print axioms Miao.RecursiveUtility.SS.firmExit
#print axioms Miao.RecursiveUtility.SS.firmExit_T
#print axioms Miao.RecursiveUtility.SS.firmExit_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.RDP.IsConvexRDP
#print axioms Miao.RecursiveUtility.SS.RDP.IsConcaveRDP
#print axioms Miao.RecursiveUtility.SS.RDP.exists_delta_concave
#print axioms Miao.RecursiveUtility.SS.RDP.exists_delta_convex
#print axioms Miao.RecursiveUtility.SS.RDP.concaveOn_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.convexOn_Tσ
#print axioms Miao.RecursiveUtility.SS.RDP.IsConcaveRDP.isGloballyStable
#print axioms Miao.RecursiveUtility.SS.RDP.IsConvexRDP.isGloballyStable
#print axioms Miao.RecursiveUtility.SS.MDP.isBoundedBy_eps
#print axioms Miao.RecursiveUtility.SS.MDP.toRDP_B_combo
#print axioms Miao.RecursiveUtility.SS.MDP.restrict_isConvex_isConcave
#print axioms Miao.RecursiveUtility.SS.iInf_add_iInf_le
#print axioms Miao.RecursiveUtility.SS.add_mul_iInf
#print axioms Miao.RecursiveUtility.SS.advB
#print axioms Miao.RecursiveUtility.SS.AdvConditions
#print axioms Miao.RecursiveUtility.SS.AdvConditions.mk
#print axioms Miao.RecursiveUtility.SS.AdvConditions.nonempty
#print axioms Miao.RecursiveUtility.SS.AdvConditions.mono
#print axioms Miao.RecursiveUtility.SS.AdvConditions.eps_pos
#print axioms Miao.RecursiveUtility.SS.AdvConditions.lower
#print axioms Miao.RecursiveUtility.SS.AdvConditions.le
#print axioms Miao.RecursiveUtility.SS.AdvConditions.upper
#print axioms Miao.RecursiveUtility.SS.AdvConditions.concave
#print axioms Miao.RecursiveUtility.SS.AdvConditions.lower_mem
#print axioms Miao.RecursiveUtility.SS.AdvConditions.bddBelow
#print axioms Miao.RecursiveUtility.SS.AdvConditions.le_advB
#print axioms Miao.RecursiveUtility.SS.AdvConditions.advB_le
#print axioms Miao.RecursiveUtility.SS.AdvConditions.advB_mono
#print axioms Miao.RecursiveUtility.SS.AdvConditions.advB_mem
#print axioms Miao.RecursiveUtility.SS.adversarialRDP
#print axioms Miao.RecursiveUtility.SS.adversarialRDP_isConcaveRDP
#print axioms Miao.RecursiveUtility.SS.adversarialRDP_isGloballyStable
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.mk
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Γ
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Γ_nonempty
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Dset
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Dset_nonempty
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.β
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.β_pos
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.β_lt_one
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.r
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.r₁
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.r₂
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.r_bounds
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.P
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.P_nonneg
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.P_rowsum
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Bd
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.v₁
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.v₂
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.Bd_const
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.advConditions
#print axioms Miao.RecursiveUtility.SS.PerturbedMDP.isConcaveRDP
#print axioms Miao.RecursiveUtility.SS.robustMDP
#print axioms Miao.RecursiveUtility.SS.robustMDP_advB
#print axioms Miao.RecursiveUtility.SS.robustMDP_isConcaveRDP
#print axioms Miao.RecursiveUtility.SS.bddBelow_sum_mul_dist
#print axioms Miao.RecursiveUtility.SS.robustJobSearch
#print axioms Miao.RecursiveUtility.SS.robustJobSearch_isContracting
#print axioms Miao.RecursiveUtility.SS.penalty_absorbed
#print axioms Miao.RecursiveUtility.SS.klDiv
#print axioms Miao.RecursiveUtility.SS.AbsCont
#print axioms Miao.RecursiveUtility.SS.sum_exp_mul_pos
#print axioms Miao.RecursiveUtility.SS.sum_mul_sub_klDiv_le
#print axioms Miao.RecursiveUtility.SS.gibbs
#print axioms Miao.RecursiveUtility.SS.isDistribution_gibbs
#print axioms Miao.RecursiveUtility.SS.absCont_gibbs
#print axioms Miao.RecursiveUtility.SS.sum_mul_sub_klDiv_gibbs
#print axioms Miao.RecursiveUtility.SS.klDuality
#print axioms Miao.RecursiveUtility.SS.entropic_isLeast
#print axioms Miao.RecursiveUtility.SS.MDP.riskSensitive_B_eq_robust
#print axioms Miao.RecursiveUtility.ku_InC
#print axioms Miao.RecursiveUtility.ku_norm
#print axioms Miao.RecursiveUtility.ku_inC_iff
#print axioms Miao.RecursiveUtility.ku_bdd
#print axioms Miao.RecursiveUtility.ku_norm_nonneg
#print axioms Miao.RecursiveUtility.ku_abs_le
#print axioms Miao.RecursiveUtility.ku_norm_le
#print axioms Miao.RecursiveUtility.ku_norm_sub_comm
#print axioms Miao.RecursiveUtility.ku_inC_add
#print axioms Miao.RecursiveUtility.ku_inC_smul
#print axioms Miao.RecursiveUtility.ku_inC_sub
#print axioms Miao.RecursiveUtility.ku_inC_zero
#print axioms Miao.RecursiveUtility.ku_inC_self
#print axioms Miao.RecursiveUtility.ku_ex_7_1_norm
#print axioms Miao.RecursiveUtility.ku_toBCF
#print axioms Miao.RecursiveUtility.ku_toBCF_apply
#print axioms Miao.RecursiveUtility.ku_inC_mul
#print axioms Miao.RecursiveUtility.ku_norm_mul_sub_le
#print axioms Miao.RecursiveUtility.ku_dist_toBCF_le
#print axioms Miao.RecursiveUtility.ku_ex_7_1
#print axioms Miao.RecursiveUtility.ku_exists_unique_fixedPoint
#print axioms Miao.RecursiveUtility.ku_inC_of_le
#print axioms Miao.RecursiveUtility.ku_le_add_of_disc
#print axioms Miao.RecursiveUtility.ku_thm_7_3_6_contraction
#print axioms Miao.RecursiveUtility.ku_thm_7_3_6
#print axioms Miao.RecursiveUtility.ku_thm_7_3_6_c
#print axioms Miao.RecursiveUtility.ku_thm_7_3_6_selfMap
#print axioms Miao.RecursiveUtility.ku_thm_7_3_6_of_continuous
#print axioms Miao.RecursiveUtility.ku_intro_partial
#print axioms Miao.RecursiveUtility.ku_intro_mrs_const
#print axioms Miao.RecursiveUtility.ku_intro_knife_edge
#print axioms Miao.RecursiveUtility.ku_intro_growth
#print axioms Miao.RecursiveUtility.ku_intro_rra
#print axioms Miao.RecursiveUtility.ku_intro_eis
#print axioms Miao.RecursiveUtility.ku_intro_timing
#print axioms Miao.RecursiveUtility.ku_shift
#print axioms Miao.RecursiveUtility.ku_tail
#print axioms Miao.RecursiveUtility.ku_cons
#print axioms Miao.RecursiveUtility.ku_cons_zero
#print axioms Miao.RecursiveUtility.ku_shift_cons
#print axioms Miao.RecursiveUtility.ku_cons_shift
#print axioms Miao.RecursiveUtility.ku_tail_zero
#print axioms Miao.RecursiveUtility.ku_tail_succ
#print axioms Miao.RecursiveUtility.ku_bddSeq
#print axioms Miao.RecursiveUtility.ku_bddSeq_closed
#print axioms Miao.RecursiveUtility.ku_Represents
#print axioms Miao.RecursiveUtility.eq_20_1
#print axioms Miao.RecursiveUtility.eq_20_1_additive
#print axioms Miao.RecursiveUtility.ku_K1
#print axioms Miao.RecursiveUtility.ku_K2
#print axioms Miao.RecursiveUtility.ku_K3
#print axioms Miao.RecursiveUtility.ku_K1_of_recursive
#print axioms Miao.RecursiveUtility.ku_K2_of_recursive
#print axioms Miao.RecursiveUtility.ku_K3_iff_of_recursive
#print axioms Miao.RecursiveUtility.ku_const_mem_bddSeq
#print axioms Miao.RecursiveUtility.ku_K1_counterexample
#print axioms Miao.RecursiveUtility.ku_K3_counterexample
#print axioms Miao.RecursiveUtility.ku_koopmans_1960
#print axioms Miao.RecursiveUtility.ku_ordinal_unique
#print axioms Miao.RecursiveUtility.definition_20_1_1
#print axioms Miao.RecursiveUtility.ku_dynConsistent_of_recursive
#print axioms Miao.RecursiveUtility.ku_dynConsistent_of_K1
#print axioms Miao.RecursiveUtility.ku_IsSubjDiscount
#print axioms Miao.RecursiveUtility.example_20_1_1
#print axioms Miao.RecursiveUtility.example_20_1_1_epstein_hynes
#print axioms Miao.RecursiveUtility.ku_ces
#print axioms Miao.RecursiveUtility.ku_ces_pos
#print axioms Miao.RecursiveUtility.ku_ces_rpow
#print axioms Miao.RecursiveUtility.ku_ces_hasDerivAt_x
#print axioms Miao.RecursiveUtility.ku_ces_hasDerivAt_y
#print axioms Miao.RecursiveUtility.example_20_1_2_const
#print axioms Miao.RecursiveUtility.example_20_1_2_discount
#print axioms Miao.RecursiveUtility.ku_shift_update_zero
#print axioms Miao.RecursiveUtility.ku_shift_update_succ
#print axioms Miao.RecursiveUtility.example_20_1_2_mrs
#print axioms Miao.RecursiveUtility.example_20_1_2
#print axioms Miao.RecursiveUtility.example_20_1_2_misprint
#print axioms Miao.RecursiveUtility.ku_TW
#print axioms Miao.RecursiveUtility.ku_TW_continuous
#print axioms Miao.RecursiveUtility.ku_W5_misprint
#print axioms Miao.RecursiveUtility.ku_TW_mapsTo
#print axioms Miao.RecursiveUtility.ku_TW_contraction
#print axioms Miao.RecursiveUtility.ku_TW_exists_unique
#print axioms Miao.RecursiveUtility.ku_TW_iterate_bound
#print axioms Miao.RecursiveUtility.ku_TW_tendsto
#print axioms Miao.RecursiveUtility.ku_TW_unique_of_bound
#print axioms Miao.RecursiveUtility.ku_TW_monotone
#print axioms Miao.RecursiveUtility.theorem_20_1_2_T0
#print axioms Miao.RecursiveUtility.theorem_20_1_2_disc
#print axioms Miao.RecursiveUtility.theorem_20_1_2_via_7_3_6
#print axioms Miao.RecursiveUtility.ku_ConcaveS
#print axioms Miao.RecursiveUtility.ku_concaveS_of_tendsto
#print axioms Miao.RecursiveUtility.ku_bshift
#print axioms Miao.RecursiveUtility.ku_bshift_apply
#print axioms Miao.RecursiveUtility.ku_seqθ
#print axioms Miao.RecursiveUtility.ku_Lθ
#print axioms Miao.RecursiveUtility.ku_thetaNorm
#print axioms Miao.RecursiveUtility.ku_thetaNorm_seqθ
#print axioms Miao.RecursiveUtility.ku_Lθ_surj
#print axioms Miao.RecursiveUtility.ku_Lθ_complete
#print axioms Miao.RecursiveUtility.ku_seqθ_one
#print axioms Miao.RecursiveUtility.ku_seqθ_zero
#print axioms Miao.RecursiveUtility.ku_σθ
#print axioms Miao.RecursiveUtility.ku_seqθ_σθ
#print axioms Miao.RecursiveUtility.ku_continuous_σθ
#print axioms Miao.RecursiveUtility.ku_continuous_head
#print axioms Miao.RecursiveUtility.ku_head_mem
#print axioms Miao.RecursiveUtility.ku_continuous_W
#print axioms Miao.RecursiveUtility.ku_convex_Lθ
#print axioms Miao.RecursiveUtility.ku_σθ_mix
#print axioms Miao.RecursiveUtility.ku_TW_concave
#print axioms Miao.RecursiveUtility.theorem_20_1_1
#print axioms Miao.RecursiveUtility.theorem_20_1_1_mono
#print axioms Miao.RecursiveUtility.theorem_20_1_1_concave
#print axioms Miao.RecursiveUtility.theorem_20_1_2
#print axioms Miao.RecursiveUtility.theorem_20_1_2_concave
#print axioms Miao.RecursiveUtility.theorem_20_1_2_strict
#print axioms Miao.RecursiveUtility.example_20_1_1_exists
#print axioms Miao.RecursiveUtility.ku_additive_not_W1
#print axioms Miao.RecursiveUtility.ku_pointwise_not_sup
#print axioms Miao.RecursiveUtility.ku_exW
#print axioms Miao.RecursiveUtility.ku_exϕ
#print axioms Miao.RecursiveUtility.ku_exϕ_pos
#print axioms Miao.RecursiveUtility.ku_head_le_norm
#print axioms Miao.RecursiveUtility.ku_example_682_W0
#print axioms Miao.RecursiveUtility.ku_zeroθ
#print axioms Miao.RecursiveUtility.ku_example_682_misprint
#print axioms Miao.RecursiveUtility.ku_norm_σθ_le
#print axioms Miao.RecursiveUtility.ku_example_682_ratio
#print axioms Miao.RecursiveUtility.ku_example_682_sup
#print axioms Miao.RecursiveUtility.ku_exW_continuousOn
#print axioms Miao.RecursiveUtility.ku_exW_lipschitz
#print axioms Miao.RecursiveUtility.ku_exϕ_continuous
#print axioms Miao.RecursiveUtility.ku_example_682
#print axioms Miao.RecursiveUtility.ku_example_682_series
#print axioms Miao.RecursiveUtility.ku_Meas
#print axioms Miao.RecursiveUtility.ku_Adapted
#print axioms Miao.RecursiveUtility.ku_E
#print axioms Miao.RecursiveUtility.ku_update_agree
#print axioms Miao.RecursiveUtility.ku_E_meas
#print axioms Miao.RecursiveUtility.ku_Reach
#print axioms Miao.RecursiveUtility.ku_reach_update
#print axioms Miao.RecursiveUtility.ku_reach_pred
#print axioms Miao.RecursiveUtility.definition_20_2_1
#print axioms Miao.RecursiveUtility.definition_20_2_2
#print axioms Miao.RecursiveUtility.definition_20_2_3
#print axioms Miao.RecursiveUtility.ku_UncertaintyAgg
#print axioms Miao.RecursiveUtility.eq_20_2
#print axioms Miao.RecursiveUtility.ku_definition_20_2_3_uncertaintyAgg
#print axioms Miao.RecursiveUtility.ku_E_isCE
#print axioms Miao.RecursiveUtility.ku_dynConsistent_of_eq_20_2
#print axioms Miao.RecursiveUtility.ku_Eiter
#print axioms Miao.RecursiveUtility.ku_Eiter_zero
#print axioms Miao.RecursiveUtility.ku_Eiter_succ
#print axioms Miao.RecursiveUtility.ku_Eiter_abs_le
#print axioms Miao.RecursiveUtility.ku_additive_sum
#print axioms Miao.RecursiveUtility.ku_timeAdditive_eu
#print axioms Miao.RecursiveUtility.ku_timeAdditive_eu_sum
#print axioms Miao.RecursiveUtility.ku_timeAdditive_R
#print axioms Miao.RecursiveUtility.ku_kpCE
#print axioms Miao.RecursiveUtility.ku_kpCE_eq_kpR
#print axioms Miao.RecursiveUtility.ku_E_pos
#print axioms Miao.RecursiveUtility.ku_kpCE_pos
#print axioms Miao.RecursiveUtility.ku_kpCE_isCE
#print axioms Miao.RecursiveUtility.ku_kpCE_mono
#print axioms Miao.RecursiveUtility.ku_kpCE_strictMono
#print axioms Miao.RecursiveUtility.ku_ces_strictMonoOn
#print axioms Miao.RecursiveUtility.eq_20_3
#print axioms Miao.RecursiveUtility.ku_ez_dynConsistent
#print axioms Miao.RecursiveUtility.ku_ez_rra
#print axioms Miao.RecursiveUtility.ku_ez_eis
#print axioms Miao.RecursiveUtility.ku_ez_expected_power
#print axioms Miao.RecursiveUtility.ku_ez_expected_power_sum
#print axioms Miao.RecursiveUtility.ku_ez_markov
#print axioms Miao.RecursiveUtility.ku_ces_homog
#print axioms Miao.RecursiveUtility.ku_ez_markov_homogeneous
#print axioms Miao.RecursiveUtility.ku_expCE
#print axioms Miao.RecursiveUtility.ku_expCE_isCE
#print axioms Miao.RecursiveUtility.ku_expCE_translation
#print axioms Miao.RecursiveUtility.eq_20_4
#print axioms Miao.RecursiveUtility.ku_ces_limit
#print axioms Miao.RecursiveUtility.eq_20_5
#print axioms Miao.RecursiveUtility.ku_ce_unique
#print axioms Miao.RecursiveUtility.ku_ce_exists
#print axioms Miao.RecursiveUtility.ku_ce_counterexample
#print axioms Miao.RecursiveUtility.ku_allais
#print axioms Miao.RecursiveUtility.ku_allais_u0
#print axioms Miao.RecursiveUtility.ku_allais_paradox
#print axioms Miao.RecursiveUtility.ku_wsum_pos
#print axioms Miao.RecursiveUtility.eq_20_6
#print axioms Miao.RecursiveUtility.ku_euM
#print axioms Miao.RecursiveUtility.ku_euM_i
#print axioms Miao.RecursiveUtility.ku_euM_ii
#print axioms Miao.RecursiveUtility.ku_euM_iii
#print axioms Miao.RecursiveUtility.ku_euM_iv
#print axioms Miao.RecursiveUtility.ku_euM_iv_misprint
#print axioms Miao.RecursiveUtility.ku_euM_ce
#print axioms Miao.RecursiveUtility.ku_wM
#print axioms Miao.RecursiveUtility.ku_wM_i
#print axioms Miao.RecursiveUtility.ku_wM_zero
#print axioms Miao.RecursiveUtility.ku_wM_ce
#print axioms Miao.RecursiveUtility.ku_wM_params
#print axioms Miao.RecursiveUtility.ku_wM_eq
#print axioms Miao.RecursiveUtility.ku_wM_local
#print axioms Miao.RecursiveUtility.ku_wM_params_not_necessary
#print axioms Miao.RecursiveUtility.ku_gulM
#print axioms Miao.RecursiveUtility.ku_gulM_i
#print axioms Miao.RecursiveUtility.ku_gulM_zero
#print axioms Miao.RecursiveUtility.ku_gulM_ce
#print axioms Miao.RecursiveUtility.ku_gulM_ce_hat
#print axioms Miao.RecursiveUtility.ku_gulM_hat_misprint
#print axioms Miao.RecursiveUtility.ku_recWeighted_ce
#print axioms Miao.RecursiveUtility.ku_recWeighted
#print axioms Miao.RecursiveUtility.ku_recGul
#print axioms Miao.RecursiveUtility.ku_ezAux
#print axioms Miao.RecursiveUtility.ku_ezFin
#print axioms Miao.RecursiveUtility.ku_ezFin_T
#print axioms Miao.RecursiveUtility.ku_ezFin_succ
#print axioms Miao.RecursiveUtility.ku_PosPlan
#print axioms Miao.RecursiveUtility.ku_convex_PosPlan
#print axioms Miao.RecursiveUtility.ku_ezAux_pos
#print axioms Miao.RecursiveUtility.ku_ezFin_pos
#print axioms Miao.RecursiveUtility.ku_ezFin_dynUtility
#print axioms Miao.RecursiveUtility.ku_ezFin_meas
#print axioms Miao.RecursiveUtility.ku_kpCE_homog
#print axioms Miao.RecursiveUtility.ku_ezFin_homog
#print axioms Miao.RecursiveUtility.ku_Q
#print axioms Miao.RecursiveUtility.ku_Q_markov
#print axioms Miao.RecursiveUtility.ku_ces_eq_kpR
#print axioms Miao.RecursiveUtility.ku_ces_concave
#print axioms Miao.RecursiveUtility.ex_20_1
#print axioms Miao.RecursiveUtility.ex_20_1_not_strict
#print axioms Miao.RecursiveUtility.aa_E
#print axioms Miao.RecursiveUtility.aa_E_const
#print axioms Miao.RecursiveUtility.aa_E_mono
#print axioms Miao.RecursiveUtility.aa_E_add
#print axioms Miao.RecursiveUtility.aa_E_smul
#print axioms Miao.RecursiveUtility.aa_E_pos
#print axioms Miao.RecursiveUtility.aa_W
#print axioms Miao.RecursiveUtility.aa_KP
#print axioms Miao.RecursiveUtility.aa_ezU
#print axioms Miao.RecursiveUtility.aa_W_pos
#print axioms Miao.RecursiveUtility.aa_KP_pos
#print axioms Miao.RecursiveUtility.aa_KP_const
#print axioms Miao.RecursiveUtility.aa_W_diag
#print axioms Miao.RecursiveUtility.aa_W_strictMonoOn
#print axioms Miao.RecursiveUtility.aa_KP_mono
#print axioms Miao.RecursiveUtility.aa_ezU_pos
#print axioms Miao.RecursiveUtility.aa_Ex
#print axioms Miao.RecursiveUtility.aa_linear_unroll
#print axioms Miao.RecursiveUtility.aa_logmgf_hasDerivAt
#print axioms Miao.RecursiveUtility.aa_tendsto_logmgf
#print axioms Miao.RecursiveUtility.aa_softmin_bounds
#print axioms Miao.RecursiveUtility.aa_tendsto_softmin
#print axioms Miao.RecursiveUtility.aa_maxmin
#print axioms Miao.RecursiveUtility.aa_E_ge_neg
#print axioms Miao.RecursiveUtility.aa_maxmin_bdd
#print axioms Miao.RecursiveUtility.aa_maxmin_le
#print axioms Miao.RecursiveUtility.aa_le_maxmin
#print axioms Miao.RecursiveUtility.aa_maxmin_attained
#print axioms Miao.RecursiveUtility.aa_maxmin_singleton
#print axioms Miao.RecursiveUtility.aa_maxmin_mono
#print axioms Miao.RecursiveUtility.aa_maxmin_add_const
#print axioms Miao.RecursiveUtility.aa_maxmin_const
#print axioms Miao.RecursiveUtility.aa_maxmin_smul
#print axioms Miao.RecursiveUtility.aa_maxmin_superadditive
#print axioms Miao.RecursiveUtility.aa_ellsberg_no_prior
#print axioms Miao.RecursiveUtility.aa_ellsbergPriors
#print axioms Miao.RecursiveUtility.aa_ellsbergPrior
#print axioms Miao.RecursiveUtility.aa_ellsbergPrior_isDistribution
#print axioms Miao.RecursiveUtility.aa_E_bool
#print axioms Miao.RecursiveUtility.aa_ellsberg_black
#print axioms Miao.RecursiveUtility.aa_ellsberg_white
#print axioms Miao.RecursiveUtility.aa_ellsberg_maxmin
#print axioms Miao.RecursiveUtility.aa_rmpU
#print axioms Miao.RecursiveUtility.aa_hayashiU
#print axioms Miao.RecursiveUtility.aa_hayashiU_additive
#print axioms Miao.RecursiveUtility.aa_selU
#print axioms Miao.RecursiveUtility.aa_selU_eq_sum
#print axioms Miao.RecursiveUtility.aa_rmpU_isLeast_selection
#print axioms Miao.RecursiveUtility.aa_rectangular_recursion
#print axioms Miao.RecursiveUtility.aa_nrPrior
#print axioms Miao.RecursiveUtility.aa_nonrectangular_counterexample
#print axioms Miao.RecursiveUtility.aa_Δ
#print axioms Miao.RecursiveUtility.aa_variational
#print axioms Miao.RecursiveUtility.aa_variational_zero
#print axioms Miao.RecursiveUtility.aa_phiDiv
#print axioms Miao.RecursiveUtility.aa_divU
#print axioms Miao.RecursiveUtility.aa_phiDiv_self
#print axioms Miao.RecursiveUtility.aa_phiDiv_nonneg
#print axioms Miao.RecursiveUtility.aa_divU_bdd
#print axioms Miao.RecursiveUtility.aa_divU_le_E
#print axioms Miao.RecursiveUtility.aa_divU_mono
#print axioms Miao.RecursiveUtility.aa_klPhi
#print axioms Miao.RecursiveUtility.aa_klPhi_one
#print axioms Miao.RecursiveUtility.aa_klPhi_nonneg
#print axioms Miao.RecursiveUtility.aa_klPhi_superlinear
#print axioms Miao.RecursiveUtility.aa_phiDiv_kl
#print axioms Miao.RecursiveUtility.aa_multiplier_isLeast
#print axioms Miao.RecursiveUtility.aa_divU_kl
#print axioms Miao.RecursiveUtility.aa_riskSensitive_tendsto
#print axioms Miao.RecursiveUtility.aa_expU
#print axioms Miao.RecursiveUtility.aa_riskSensitive_eq_ce
#print axioms Miao.RecursiveUtility.aa_expU_arrowPratt
#print axioms Miao.RecursiveUtility.aa_chiPhi
#print axioms Miao.RecursiveUtility.aa_chiPhi_one
#print axioms Miao.RecursiveUtility.aa_chiPhi_nonneg
#print axioms Miao.RecursiveUtility.aa_chiPhi_superlinear
#print axioms Miao.RecursiveUtility.aa_Var
#print axioms Miao.RecursiveUtility.aa_chi2_identity
#print axioms Miao.RecursiveUtility.aa_chi2_mmv
#print axioms Miao.RecursiveUtility.aa_Admissible
#print axioms Miao.RecursiveUtility.aa_admissible_one
#print axioms Miao.RecursiveUtility.aa_admissible_isDistribution
#print axioms Miao.RecursiveUtility.aa_M
#print axioms Miao.RecursiveUtility.aa_M_martingale
#print axioms Miao.RecursiveUtility.aa_divObj
#print axioms Miao.RecursiveUtility.aa_divR
#print axioms Miao.RecursiveUtility.aa_rdU
#print axioms Miao.RecursiveUtility.aa_rdUm
#print axioms Miao.RecursiveUtility.aa_divObj_ge
#print axioms Miao.RecursiveUtility.aa_divR_le
#print axioms Miao.RecursiveUtility.aa_divObj_sub
#print axioms Miao.RecursiveUtility.aa_distort
#print axioms Miao.RecursiveUtility.aa_rdUm_unroll
#print axioms Miao.RecursiveUtility.aa_Ex_change
#print axioms Miao.RecursiveUtility.aa_rdUm_eq_sum
#print axioms Miao.RecursiveUtility.aa_rdU_le_rdUm
#print axioms Miao.RecursiveUtility.aa_rdU_isGLB
#print axioms Miao.RecursiveUtility.aa_divR_kl
#print axioms Miao.RecursiveUtility.aa_jensen_rpow
#print axioms Miao.RecursiveUtility.aa_powMean
#print axioms Miao.RecursiveUtility.aa_powMean_mono
#print axioms Miao.RecursiveUtility.aa_predictive
#print axioms Miao.RecursiveUtility.aa_predictive_isDistribution
#print axioms Miao.RecursiveUtility.aa_E_predictive
#print axioms Miao.RecursiveUtility.aa_kmmU
#print axioms Miao.RecursiveUtility.aa_kmm_affine
#print axioms Miao.RecursiveUtility.aa_kmm_concave_le
#print axioms Miao.RecursiveUtility.aa_smoothM
#print axioms Miao.RecursiveUtility.aa_smoothM_linear
#print axioms Miao.RecursiveUtility.aa_posterior
#print axioms Miao.RecursiveUtility.aa_posterior_isDistribution
#print axioms Miao.RecursiveUtility.aa_posterior_martingale
#print axioms Miao.RecursiveUtility.aa_powU
#print axioms Miao.RecursiveUtility.aa_powUinv
#print axioms Miao.RecursiveUtility.aa_powUinv_powU
#print axioms Miao.RecursiveUtility.aa_ju
#print axioms Miao.RecursiveUtility.aa_smoothM_power
#print axioms Miao.RecursiveUtility.aa_juU
#print axioms Miao.RecursiveUtility.aa_ju_eq_powMean
#print axioms Miao.RecursiveUtility.aa_ju_neutral
#print axioms Miao.RecursiveUtility.aa_juU_neutral
#print axioms Miao.RecursiveUtility.aa_ju_antitone
#print axioms Miao.RecursiveUtility.aa_ju_le_KP
#print axioms Miao.RecursiveUtility.aa_KP_le_ju
#print axioms Miao.RecursiveUtility.aa_W_ju_antitone
#print axioms Miao.RecursiveUtility.aa_W_tendsto_rho_one
#print axioms Miao.RecursiveUtility.eq_20_16
#print axioms Miao.RecursiveUtility.eq_20_17
#print axioms Miao.RecursiveUtility.eq_20_18
#print axioms Miao.RecursiveUtility.aa_expUinv
#print axioms Miao.RecursiveUtility.aa_smoothM_exp
#print axioms Miao.RecursiveUtility.aa_smoothM_exp_equal
#print axioms Miao.RecursiveUtility.aa_smoothM_expPhi
#print axioms Miao.RecursiveUtility.eq_20_19
#print axioms Miao.RecursiveUtility.aa_juMiao_illDefined
#print axioms Miao.RecursiveUtility.aa_kmm09U
#print axioms Miao.RecursiveUtility.aa_juU_pos
#print axioms Miao.RecursiveUtility.aa_juMiao_step
#print axioms Miao.RecursiveUtility.aa_juMiao_ordinal
#print axioms Miao.RecursiveUtility.aa_Lott
#print axioms Miao.RecursiveUtility.aa_mix
#print axioms Miao.RecursiveUtility.aa_mix_mem
#print axioms Miao.RecursiveUtility.aa_integrable
#print axioms Miao.RecursiveUtility.aa_integral_mix
#print axioms Miao.RecursiveUtility.aa_U0
#print axioms Miao.RecursiveUtility.aa_PrefersEarly
#print axioms Miao.RecursiveUtility.aa_PrefersLate
#print axioms Miao.RecursiveUtility.definition_20_2_4
#print axioms Miao.RecursiveUtility.aa_Y
#print axioms Miao.RecursiveUtility.aa_Y_convex
#print axioms Miao.RecursiveUtility.theorem_20_2_1
#print axioms Miao.RecursiveUtility.theorem_20_2_1_late
#print axioms Miao.RecursiveUtility.aa_timeAdditive_indifferent
#print axioms Miao.RecursiveUtility.aa_timeAdditive_indifferent_34
#print axioms Miao.RecursiveUtility.aa_ezKP
#print axioms Miao.RecursiveUtility.aa_ezKP_eq
#print axioms Miao.RecursiveUtility.aa_powF_strictConvexOn
#print axioms Miao.RecursiveUtility.aa_powF_strictConcaveOn
#print axioms Miao.RecursiveUtility.aa_ezKP_eq_powF
#print axioms Miao.RecursiveUtility.aa_strictConvexOn_comp
#print axioms Miao.RecursiveUtility.aa_strictConcaveOn_comp
#print axioms Miao.RecursiveUtility.aa_ezKP_strict
#print axioms Miao.RecursiveUtility.aa_ezKP_diag
#print axioms Miao.RecursiveUtility.aa_powU_bound
#print axioms Miao.RecursiveUtility.aa_powU_measurable
#print axioms Miao.RecursiveUtility.aa_Y_subset
#print axioms Miao.RecursiveUtility.ex_20_3
#print axioms Miao.RecursiveUtility.aa_ez_strictEarly
#print axioms Miao.RecursiveUtility.aa_ez_indifferent
#print axioms Miao.RecursiveUtility.aa_recU
#print axioms Miao.RecursiveUtility.aa_posPlans
#print axioms Miao.RecursiveUtility.aa_posPlans_convex
#print axioms Miao.RecursiveUtility.aa_recU_concaveOn
#print axioms Miao.RecursiveUtility.aa_recU_congr
#print axioms Miao.RecursiveUtility.aa_recU_not_strictConcave
#print axioms Miao.RecursiveUtility.aa_ezU_eq_recU
#print axioms Miao.RecursiveUtility.aa_KP_concaveOn
#print axioms Miao.RecursiveUtility.aa_W_concaveOn
#print axioms Miao.RecursiveUtility.aa_ezU_concaveOn
#print axioms Miao.RecursiveUtility.aa_ezU_smul
#print axioms Miao.RecursiveUtility.aa_ezU_not_strictConcave
#print axioms Miao.RecursiveUtility.aa_Homogeneous1
#print axioms Miao.RecursiveUtility.aa_LevelCond
#print axioms Miao.RecursiveUtility.aa_Superadd
#print axioms Miao.RecursiveUtility.lemma_20_3_1_i_iff_iii
#print axioms Miao.RecursiveUtility.lemma_20_3_1_i_ii
#print axioms Miao.RecursiveUtility.lemma_20_3_1
#print axioms Miao.RecursiveUtility.aa_skiadasCex
#print axioms Miao.RecursiveUtility.lemma_20_3_1_counterexample
#print axioms Miao.RecursiveUtility.aa_Deterministic
#print axioms Miao.RecursiveUtility.aa_MoreRiskAverse
#print axioms Miao.RecursiveUtility.aa_RiskAverse
#print axioms Miao.RecursiveUtility.aa_IsCE
#print axioms Miao.RecursiveUtility.aa_recU_deterministic
#print axioms Miao.RecursiveUtility.aa_recU_le
#print axioms Miao.RecursiveUtility.proposition_20_3_1
#print axioms Miao.RecursiveUtility.aa_riskAverse_never
#print axioms Miao.RecursiveUtility.aa_RiskAverse'
#print axioms Miao.RecursiveUtility.aa_coinE
#print axioms Miao.RecursiveUtility.aa_moreRiskAverse_not_riskAverse
#print axioms Miao.RecursiveUtility.aa_CELe
#print axioms Miao.RecursiveUtility.aa_pratt_of_concave
#print axioms Miao.RecursiveUtility.aa_concave_of_pratt
#print axioms Miao.RecursiveUtility.proposition_20_3_1_pratt
#print axioms Miao.RecursiveUtility.aa_euCE
#print axioms Miao.RecursiveUtility.aa_euCE_isCE
#print axioms Miao.RecursiveUtility.aa_euCE_mono
#print axioms Miao.RecursiveUtility.proposition_20_3_1_ez
#print axioms Miao.RecursiveUtility.aa_IsGradientDensity
#print axioms Miao.RecursiveUtility.aa_IsSupergradient
#print axioms Miao.RecursiveUtility.aa_CEDerivPrinted
#print axioms Miao.RecursiveUtility.aa_HasCEDeriv
#print axioms Miao.RecursiveUtility.aa_cePrinted_apply
#print axioms Miao.RecursiveUtility.aa_CEDerivPrinted_not_unique
#print axioms Miao.RecursiveUtility.aa_HasCEDeriv_expectation
#print axioms Miao.RecursiveUtility.aa_not_HasCEDeriv_expectation_zero
#print axioms Miao.RecursiveUtility.aa_euCE_hasCEDeriv
#print axioms Miao.RecursiveUtility.aa_gradV
#print axioms Miao.RecursiveUtility.aa_GradHyp
#print axioms Miao.RecursiveUtility.aa_gradV_hasDerivAt
#print axioms Miao.RecursiveUtility.aa_Ex_congr
#print axioms Miao.RecursiveUtility.aa_gradπ
#print axioms Miao.RecursiveUtility.proposition_20_3_2
#print axioms Miao.RecursiveUtility.proposition_20_3_2_gradient
#print axioms Miao.RecursiveUtility.aa_pricingKernel
#print axioms Miao.RecursiveUtility.aa_marginal_value_wealth
#print axioms Miao.RecursiveUtility.aa_lambda0_eq_mu
#print axioms Miao.RecursiveUtility.aa_W_hasFDerivAt
#print axioms Miao.RecursiveUtility.aa_KP_hasCEDeriv
#print axioms Miao.RecursiveUtility.eq_20_20
#print axioms Miao.RecursiveUtility.aa_ezMh
#print axioms Miao.RecursiveUtility.aa_ezW₁
#print axioms Miao.RecursiveUtility.aa_ezW₂
#print axioms Miao.RecursiveUtility.aa_ezκ
#print axioms Miao.RecursiveUtility.aa_M_pos
#print axioms Miao.RecursiveUtility.example_20_3_1
#print axioms Miao.RecursiveUtility.aa_ez_kernel_antitone
#print axioms Miao.RecursiveUtility.aa_ju_hasFDerivAt
#print axioms Miao.RecursiveUtility.example_20_3_2
#print axioms Miao.RecursiveUtility.aa_smooth_kernel_antitone
#print axioms Miao.RecursiveUtility.aa_Ex_smul
#print axioms Miao.RecursiveUtility.example_20_3_3
#print axioms Miao.RecursiveUtility.example_20_3_3_exists
#print axioms Miao.RecursiveUtility.aa_klDensity
#print axioms Miao.RecursiveUtility.aa_klDensity_attains
#print axioms Miao.RecursiveUtility.aa_riskSensitive_hasCEDeriv
#print axioms Miao.RecursiveUtility.ex_20_2_divergence
#print axioms Miao.RecursiveUtility.aa_divR_supergradient
#print axioms Miao.RecursiveUtility.pa_E
#print axioms Miao.RecursiveUtility.pa_W
#print axioms Miao.RecursiveUtility.pa_CE
#print axioms Miao.RecursiveUtility.pa_M
#print axioms Miao.RecursiveUtility.pa_E_add
#print axioms Miao.RecursiveUtility.pa_E_sub
#print axioms Miao.RecursiveUtility.pa_E_const_mul
#print axioms Miao.RecursiveUtility.pa_E_mul_const
#print axioms Miao.RecursiveUtility.pa_E_const
#print axioms Miao.RecursiveUtility.pa_E_congr
#print axioms Miao.RecursiveUtility.pa_E_pos
#print axioms Miao.RecursiveUtility.pa_eq_of_log_eq
#print axioms Miao.RecursiveUtility.pa_CE_pos
#print axioms Miao.RecursiveUtility.pa_CE_eq_kpR
#print axioms Miao.RecursiveUtility.pa_CE_homog
#print axioms Miao.RecursiveUtility.pa_W_homog
#print axioms Miao.RecursiveUtility.pa_W_pos
#print axioms Miao.RecursiveUtility.pa_wealthReturn
#print axioms Miao.RecursiveUtility.pa_wealthReturn_eq
#print axioms Miao.RecursiveUtility.pa_nextWealth
#print axioms Miao.RecursiveUtility.pa_bellmanInner
#print axioms Miao.RecursiveUtility.pa_bellmanInner_pos
#print axioms Miao.RecursiveUtility.pa_bellman_conjecture
#print axioms Miao.RecursiveUtility.pa_value_homogeneous
#print axioms Miao.RecursiveUtility.pa_bellmanInner_hasDerivAt
#print axioms Miao.RecursiveUtility.pa_bellman_hasDerivAt
#print axioms Miao.RecursiveUtility.eq_20_22
#print axioms Miao.RecursiveUtility.eq_20_23
#print axioms Miao.RecursiveUtility.eq_20_25
#print axioms Miao.RecursiveUtility.pa_Anext
#print axioms Miao.RecursiveUtility.eq_20_24
#print axioms Miao.RecursiveUtility.eq_20_26
#print axioms Miao.RecursiveUtility.pa_Rw
#print axioms Miao.RecursiveUtility.pa_Rw_update
#print axioms Miao.RecursiveUtility.pa_portfolio_foc
#print axioms Miao.RecursiveUtility.pa_portfolio_foc_X
#print axioms Miao.RecursiveUtility.eq_20_27
#print axioms Miao.RecursiveUtility.pa_sum_portfolio_foc
#print axioms Miao.RecursiveUtility.pa_Mbar
#print axioms Miao.RecursiveUtility.pa_Mbar_eq
#print axioms Miao.RecursiveUtility.eq_20_28
#print axioms Miao.RecursiveUtility.eq_20_29
#print axioms Miao.RecursiveUtility.eq_20_31
#print axioms Miao.RecursiveUtility.pa_M_eq_Mbar
#print axioms Miao.RecursiveUtility.pa_riskfree_rate
#print axioms Miao.RecursiveUtility.pa_Cov
#print axioms Miao.RecursiveUtility.pa_equity_premium
#print axioms Miao.RecursiveUtility.pa_lin
#print axioms Miao.RecursiveUtility.pa_quad
#print axioms Miao.RecursiveUtility.pa_JointGaussian
#print axioms Miao.RecursiveUtility.pa_jointGaussian_rank_one
#print axioms Miao.RecursiveUtility.pa_log_integral_exp_gaussian
#print axioms Miao.RecursiveUtility.pa_integral_exp_lin
#print axioms Miao.RecursiveUtility.pa_lognormal_euler
#print axioms Miao.RecursiveUtility.pa_lin_three
#print axioms Miao.RecursiveUtility.pa_quad_three
#print axioms Miao.RecursiveUtility.pa_sum_three
#print axioms Miao.RecursiveUtility.pa_levels_eq_exp
#print axioms Miao.RecursiveUtility.pa_eq_20_26_log
#print axioms Miao.RecursiveUtility.eq_20_32
#print axioms Miao.RecursiveUtility.eq_20_33
#print axioms Miao.RecursiveUtility.eq_20_34
#print axioms Miao.RecursiveUtility.eq_20_35
#print axioms Miao.RecursiveUtility.pa_expected_equity_return
#print axioms Miao.RecursiveUtility.pa_eq_20_35_weights
#print axioms Miao.RecursiveUtility.pa_varrho
#print axioms Miao.RecursiveUtility.pa_kappa
#print axioms Miao.RecursiveUtility.pa_varrho_pos
#print axioms Miao.RecursiveUtility.pa_varrho_lt_one
#print axioms Miao.RecursiveUtility.pa_cs_exact
#print axioms Miao.RecursiveUtility.pa_cs_hasDerivAt
#print axioms Miao.RecursiveUtility.pa_cs_kappa
#print axioms Miao.RecursiveUtility.eq_20_36
#print axioms Miao.RecursiveUtility.eq_20_38
#print axioms Miao.RecursiveUtility.pa_cs_iterate
#print axioms Miao.RecursiveUtility.eq_20_37
#print axioms Miao.RecursiveUtility.eq_20_37_cond
#print axioms Miao.RecursiveUtility.eq_20_39
#print axioms Miao.RecursiveUtility.eq_20_40
#print axioms Miao.RecursiveUtility.eq_20_41
#print axioms Miao.RecursiveUtility.pa_forecast
#print axioms Miao.RecursiveUtility.pa_forecast_zero
#print axioms Miao.RecursiveUtility.pa_forecast_succ
#print axioms Miao.RecursiveUtility.pa_forecast_revision
#print axioms Miao.RecursiveUtility.pa_sum_forecast
#print axioms Miao.RecursiveUtility.pa_sum_revision
#print axioms Miao.RecursiveUtility.eq_20_42
#print axioms Miao.RecursiveUtility.eq_20_43
#print axioms Miao.RecursiveUtility.pa_pd_procyclical
#print axioms Miao.RecursiveUtility.pa_consol_yield
#print axioms Miao.RecursiveUtility.pa_consol_news
#print axioms Miao.RecursiveUtility.pa_consol_lambda_one_counterexample
#print axioms Miao.RecursiveUtility.pa_sigma_iw
#print axioms Miao.RecursiveUtility.pa_premium_gamma
#print axioms Miao.RecursiveUtility.pa_lrr_cov
#print axioms Miao.RecursiveUtility.pa_lrr_equity_premium
#print axioms Miao.RecursiveUtility.eq_20_44
#print axioms Miao.RecursiveUtility.eq_20_45
#print axioms Miao.RecursiveUtility.pa_term_premium_signs
#print axioms Miao.RecursiveUtility.pa_stdNormal_pi
#print axioms Miao.RecursiveUtility.pa_integral_exp_shocks
#print axioms Miao.RecursiveUtility.pa_euler_shocks_iff
#print axioms Miao.RecursiveUtility.pa_cov_shocks
#print axioms Miao.RecursiveUtility.pa_lognormal_premium
#print axioms Miao.RecursiveUtility.pa_cov_sum_uncorrelated
#print axioms Miao.RecursiveUtility.PABansalYaron
#print axioms Miao.RecursiveUtility.PABansalYaron.mk
#print axioms Miao.RecursiveUtility.PABansalYaron.β
#print axioms Miao.RecursiveUtility.PABansalYaron.ρ
#print axioms Miao.RecursiveUtility.PABansalYaron.γ
#print axioms Miao.RecursiveUtility.PABansalYaron.μ
#print axioms Miao.RecursiveUtility.PABansalYaron.μd
#print axioms Miao.RecursiveUtility.PABansalYaron.ρx
#print axioms Miao.RecursiveUtility.PABansalYaron.φe
#print axioms Miao.RecursiveUtility.PABansalYaron.σbar2
#print axioms Miao.RecursiveUtility.PABansalYaron.ν1
#print axioms Miao.RecursiveUtility.PABansalYaron.σw
#print axioms Miao.RecursiveUtility.PABansalYaron.φ
#print axioms Miao.RecursiveUtility.PABansalYaron.φd
#print axioms Miao.RecursiveUtility.PABansalYaron.κ0
#print axioms Miao.RecursiveUtility.PABansalYaron.κ1
#print axioms Miao.RecursiveUtility.PABansalYaron.κ0e
#print axioms Miao.RecursiveUtility.PABansalYaron.κ1e
#print axioms Miao.RecursiveUtility.pa_by_θ
#print axioms Miao.RecursiveUtility.pa_by_g
#print axioms Miao.RecursiveUtility.pa_by_x'
#print axioms Miao.RecursiveUtility.pa_by_v'
#print axioms Miao.RecursiveUtility.pa_by_gd
#print axioms Miao.RecursiveUtility.pa_by_rw
#print axioms Miao.RecursiveUtility.pa_by_m
#print axioms Miao.RecursiveUtility.pa_by_re
#print axioms Miao.RecursiveUtility.pa_sum_four
#print axioms Miao.RecursiveUtility.pa_match_coeffs
#print axioms Miao.RecursiveUtility.pa_by_θ_sub_one
#print axioms Miao.RecursiveUtility.pa_by_θ_mul
#print axioms Miao.RecursiveUtility.pa_integral_affine_shocks
#print axioms Miao.RecursiveUtility.eq_20_46
#print axioms Miao.RecursiveUtility.eq_20_47
#print axioms Miao.RecursiveUtility.eq_20_48
#print axioms Miao.RecursiveUtility.pa_by_matching_wealth
#print axioms Miao.RecursiveUtility.pa_by_A1
#print axioms Miao.RecursiveUtility.pa_by_A1_pos
#print axioms Miao.RecursiveUtility.pa_by_A1_neg
#print axioms Miao.RecursiveUtility.pa_by_A2formula
#print axioms Miao.RecursiveUtility.pa_by_A2
#print axioms Miao.RecursiveUtility.pa_by_A2_neg
#print axioms Miao.RecursiveUtility.pa_by_A2_magnified
#print axioms Miao.RecursiveUtility.pa_by_B
#print axioms Miao.RecursiveUtility.pa_by_lam_eta
#print axioms Miao.RecursiveUtility.pa_by_lam_e
#print axioms Miao.RecursiveUtility.pa_by_lam_w
#print axioms Miao.RecursiveUtility.pa_by_bee
#print axioms Miao.RecursiveUtility.pa_by_bew
#print axioms Miao.RecursiveUtility.pa_by_gamma_rho
#print axioms Miao.RecursiveUtility.eq_20_50
#print axioms Miao.RecursiveUtility.pa_by_rw_affine
#print axioms Miao.RecursiveUtility.pa_by_Erw
#print axioms Miao.RecursiveUtility.pa_by_var_rw
#print axioms Miao.RecursiveUtility.pa_by_Em
#print axioms Miao.RecursiveUtility.eq_20_51
#print axioms Miao.RecursiveUtility.pa_by_m_affine
#print axioms Miao.RecursiveUtility.pa_by_Em_integral
#print axioms Miao.RecursiveUtility.pa_by_lam_eta_neg
#print axioms Miao.RecursiveUtility.pa_by_lam_e_pos
#print axioms Miao.RecursiveUtility.pa_by_lam_w_neg
#print axioms Miao.RecursiveUtility.pa_by_lam_w_not_pos
#print axioms Miao.RecursiveUtility.pa_by_power_utility
#print axioms Miao.RecursiveUtility.eq_20_52
#print axioms Miao.RecursiveUtility.eq_20_53
#print axioms Miao.RecursiveUtility.eq_20_55
#print axioms Miao.RecursiveUtility.pa_by_re_news
#print axioms Miao.RecursiveUtility.pa_by_re_affine
#print axioms Miao.RecursiveUtility.pa_by_Ere
#print axioms Miao.RecursiveUtility.pa_by_var_re
#print axioms Miao.RecursiveUtility.eq_20_54
#print axioms Miao.RecursiveUtility.eq_20_56
#print axioms Miao.RecursiveUtility.pa_by_He
#print axioms Miao.RecursiveUtility.pa_by_matching_equity
#print axioms Miao.RecursiveUtility.pa_by_A1e
#print axioms Miao.RecursiveUtility.pa_by_A1e_pos
#print axioms Miao.RecursiveUtility.pa_by_A2e
#print axioms Miao.RecursiveUtility.pa_by_re_decomp
#print axioms Miao.RecursiveUtility.pa_cov_lin_uncorrelated
#print axioms Miao.RecursiveUtility.pa_by_uncond_var
#print axioms Miao.RecursiveUtility.pa_by_riskfree
#print axioms Miao.RecursiveUtility.pa_by_riskfree_final
#print axioms Miao.RecursiveUtility.pa_by_lam_e_B
#print axioms Miao.RecursiveUtility.pa_by_riskfree_state
#print axioms Miao.RecursiveUtility.pa_by_var_riskfree
#print axioms Miao.RecursiveUtility.pa_simplex
#print axioms Miao.RecursiveUtility.pa_dot
#print axioms Miao.RecursiveUtility.pa_Vhat
#print axioms Miao.RecursiveUtility.pa_FreeDisposal
#print axioms Miao.RecursiveUtility.pa_feasible
#print axioms Miao.RecursiveUtility.pa_uvec
#print axioms Miao.RecursiveUtility.pa_U0
#print axioms Miao.RecursiveUtility.pa_U0bar
#print axioms Miao.RecursiveUtility.pa_ParetoOptimal
#print axioms Miao.RecursiveUtility.definition_20_5_1
#print axioms Miao.RecursiveUtility.pa_negishi_pareto
#print axioms Miao.RecursiveUtility.pa_feasible_isCompact
#print axioms Miao.RecursiveUtility.pa_feasible_convex
#print axioms Miao.RecursiveUtility.pa_zero_feasible
#print axioms Miao.RecursiveUtility.lemma_20_5_1_plain_closed
#print axioms Miao.RecursiveUtility.pa_U0bar_bdd
#print axioms Miao.RecursiveUtility.lemma_20_5_1
#print axioms Miao.RecursiveUtility.lemma_20_5_1_counterexample
#print axioms Miao.RecursiveUtility.pa_clm_apply
#print axioms Miao.RecursiveUtility.pa_mem_iff_support
#print axioms Miao.RecursiveUtility.lemma_20_5_2
#print axioms Miao.RecursiveUtility.pa_Vhat_U0bar
#print axioms Miao.RecursiveUtility.lemma_20_5_2_counterexample
#print axioms Miao.RecursiveUtility.PARecEconomy
#print axioms Miao.RecursiveUtility.PARecEconomy.mk
#print axioms Miao.RecursiveUtility.PARecEconomy.e0
#print axioms Miao.RecursiveUtility.PARecEconomy.e1
#print axioms Miao.RecursiveUtility.PARecEconomy.W
#print axioms Miao.RecursiveUtility.PARecEconomy.R
#print axioms Miao.RecursiveUtility.PARecEconomy.U1
#print axioms Miao.RecursiveUtility.pa_rec_feasible
#print axioms Miao.RecursiveUtility.pa_rec_U
#print axioms Miao.RecursiveUtility.pa_rec_values
#print axioms Miao.RecursiveUtility.pa_promise_ok
#print axioms Miao.RecursiveUtility.pa_bellman_values
#print axioms Miao.RecursiveUtility.pa_bellman_le_rec
#print axioms Miao.RecursiveUtility.proposition_20_5_1
#print axioms Miao.RecursiveUtility.proposition_20_5_2
#print axioms Miao.RecursiveUtility.proposition_20_5_2_counterexample
#print axioms Miao.RecursiveUtility.pa_dwu_F
#print axioms Miao.RecursiveUtility.pa_dwu_duality
#print axioms Miao.RecursiveUtility.pa_dwu_variational
#print axioms Miao.RecursiveUtility.pa_dwu_planner
#print axioms Miao.RecursiveUtility.pa_expCE
#print axioms Miao.RecursiveUtility.pa_expCE_gaussian
#print axioms Miao.RecursiveUtility.pa_weilK
#print axioms Miao.RecursiveUtility.ex_20_5_ce
#print axioms Miao.RecursiveUtility.ex_20_5_K
#print axioms Miao.RecursiveUtility.ex_20_5_A
#print axioms Miao.RecursiveUtility.pa_weilObj
#print axioms Miao.RecursiveUtility.ex_20_5
#print axioms Miao.RecursiveUtility.ex_20_5_mpc
#print axioms Miao.RecursiveUtility.ex_20_5_precautionary
#print axioms Miao.RecursiveUtility.pa_clm_pi_apply
#print axioms Miao.RecursiveUtility.pa_clm_prod_apply
#print axioms Miao.RecursiveUtility.pa_planner
#print axioms Miao.RecursiveUtility.pa_planner_hasDerivAt
#print axioms Miao.RecursiveUtility.ex_20_6_sharing0
#print axioms Miao.RecursiveUtility.ex_20_6_sharing1
#print axioms Miao.RecursiveUtility.ex_20_6_euler
#print axioms Miao.RecursiveUtility.pa_multCE
#print axioms Miao.RecursiveUtility.pa_distortion
#print axioms Miao.RecursiveUtility.pa_multiplier_hasDerivAt
#print axioms Miao.RecursiveUtility.pa_multPlanner
#print axioms Miao.RecursiveUtility.ex_20_7
