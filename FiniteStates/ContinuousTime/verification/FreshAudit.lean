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
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 10 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

The spectral radius `ρ(A)` of Vol. 1 (1.15) and the facts about it that
Chapters 6–10 use: Gelfand's formula (Lemma 1.2.2), the eventual bound
`‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1), invariance
under transposition, monotonicity in the entries (Exercise 2.2.28), and the
row-sum characterisations of the ℓ∞ operator norm. These are the results of
the `FiniteStates/OperatorsFixedPoints` project restated for a matrix indexed by
an arbitrary finite type `X`, as Chapter 6 needs them on product state spaces
`Y × Z`; each chapter project is self-contained.
-/

open Filter Topology Matrix Finset

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

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

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

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

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

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

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear valuation and eventual contractions, restated

Facts from Vol. 1, Chapter 6 used in Chapters 7–10, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

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
Chapters 8–10; each chapter project is self-contained.

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

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.1 (pp. 292–294).
Restated from the `FiniteStates/AbstractDynamicProgramming` project (Chapter 9), on which
the optimality theory of continuous-time MDPs in Chapter 10 rests.

A self-map `S` of a partially ordered set with exactly one fixed point `v̄` is upward stable if
`v ≼ Sv` implies `v ≼ v̄`, downward stable if `Sv ≼ v` implies `v̄ ≼ v`, and order stable if both
hold. No topology is involved.

* Exercise 9.1.1: `Tv = r + Av` with `A ≥ 0` and `ρ(A) < 1` is order stable on `ℝ^X`.
* Lemma 9.1.1: an order-preserving globally stable self-map of `V ⊆ ℝ^X` is order stable on `V`.
* Lemma 9.1.2: `S` is order stable on `V` iff it is order stable on the order dual `Vᵒᵈ`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Abstract dynamic programs and max-optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.1.2 and §9.2.1.1–§9.2.1.5
(pp. 294–300), with the proofs of §B.4 (pp. 349–351).
Restated from the `FiniteStates/AbstractDynamicProgramming` project (Chapter 9), on which
the optimality theory of continuous-time MDPs in Chapter 10 rests.

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

namespace SargentStachurski.ContinuousTime

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

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exponentials

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.1 (pp. 308–312).

* Example 10.1.1: `u_t = e^{rt}u₀` is the unique solution of `u̇ = ru` from `u₀`.
* Exercise 10.1.1 and **Lemma 10.1.1**: the exponential distribution is memoryless, and a counter
  CDF `G` with `0 < G < 1` on `(0, ∞)` is memoryless only if `G(t) = e^{−θt}` for some `θ > 0`.
* The matrix exponential (10.6): Exercise 10.1.2 (the partial sums are bounded by `e^{‖A‖}`) and
  **Lemma 10.1.2**: (i) conjugation (Exercise 10.1.3), (ii) commuting sums,
  (iii) `e^{mA} = (e^A)^m`, (iv) eigenvalues, (v) `d/dt e^{tA} = Ae^{tA} = e^{tA}A`
  (Exercise 10.1.4), (vi) transposes, (vii) the fundamental theorem of calculus
  (Exercise 10.1.6); Exercise 10.1.5 (`(e^A)⁻¹ = e^{−A}`).
* An eigenvector of `A` with eigenvalue `λ` is an eigenvector of `e^A` with eigenvalue `e^λ`.
  The converse in Lemma 10.1.2 (iv) is false: `e^{2πi} = 1`, so the `1 × 1` matrix `(2πi)` has
  `e^0 = 1` as an eigenvalue of its exponential while `0` is not one of its eigenvalues.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Scalar exponentials (§10.1.1.1) -/

/-- **Example 10.1.1** (p. 309), existence: `t ↦ e^{rt}u₀` solves `u̇ = ru`. -/
theorem hasDerivAt_exp_mul (r u₀ t : ℝ) :
    HasDerivAt (fun t => Real.exp (r * t) * u₀) (r * (Real.exp (r * t) * u₀)) t := by
  have h := ((hasDerivAt_id t).const_mul r).exp.mul_const u₀
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

/-- **Example 10.1.1** (p. 309), uniqueness: a solution of `ẏ = ry` on `[0, ∞)` with `y(0) = u₀`
is `y(t) = e^{rt}u₀`. -/
theorem eq_exp_of_hasDerivAt {r u₀ : ℝ} {y : ℝ → ℝ} (hy0 : y 0 = u₀)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (r * y t) t) {t : ℝ} (ht : 0 ≤ t) :
    y t = Real.exp (r * t) * u₀ := by
  set g : ℝ → ℝ := fun s => y s * Real.exp (-r * s)
  have hg : ∀ s, 0 ≤ s → HasDerivAt g 0 s := fun s hs => by
    have h1 := (hy s hs).mul (((hasDerivAt_id s).const_mul (-r)).exp)
    simp only [id, mul_one] at h1
    exact h1.congr_deriv (by ring)
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hg s hs.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun s hs =>
    (hg s hs.1).hasDerivWithinAt
  have h := hconst t ⟨ht, le_rfl⟩
  simp only [g, mul_zero, Real.exp_zero, mul_one, hy0] at h
  have hpos : Real.exp (-r * t) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc y t = y t * (Real.exp (-r * t) * Real.exp (r * t)) := by rw [hpos, mul_one]
    _ = (y t * Real.exp (-r * t)) * Real.exp (r * t) := by ring
    _ = Real.exp (r * t) * u₀ := by rw [h, mul_comm]

/-! ### The exponential distribution (§10.1.1.2) -/

/-- **Exercise 10.1.1** (p. 310): the counter CDF `G(t) = e^{−θt}` of `Exp(θ)` is memoryless:
`G(s + t) = G(s)G(t)`, so `P{W > s + t | W > s} = G(s + t)/G(s) = G(t)`. -/
theorem exp_memoryless (θ s t : ℝ) :
    Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) ∧
      Real.exp (-θ * (s + t)) / Real.exp (-θ * s) = Real.exp (-θ * t) := by
  have h : Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) := by
    rw [← Real.exp_add]
    ring_nf
  refine ⟨h, ?_⟩
  rw [h, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-- Additivity on `(0, ∞)` gives `g(ks) = kg(s)`. -/
theorem add_nsmul_of_additive {g : ℝ → ℝ} (hg : ∀ s > 0, ∀ t > 0, g (s + t) = g s + g t)
    {s : ℝ} (hs : 0 < s) : ∀ k : ℕ, 0 < k → g (k * s) = k * g s := by
  intro k hk
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · have hks : 0 < (k : ℝ) * s := mul_pos (by exact_mod_cast hk') hs
      push_cast
      rw [add_mul, one_mul, hg _ hks _ hs, ih hk', add_mul, one_mul]

/-- **Lemma 10.1.1** (p. 310), (ii) ⇒ (i): if a counter CDF `G` is decreasing, `0 < G < 1` on
`(0, ∞)`, and memoryless (`G(s + t) = G(s)G(t)` for `s, t > 0`), then `G(t) = e^{−θt}` on `(0, ∞)`
for `θ = −ln G(1) > 0`. -/
theorem eq_exp_of_memoryless {G : ℝ → ℝ} (hanti : AntitoneOn G (Ioi 0))
    (hG : ∀ t > 0, 0 < G t ∧ G t < 1) (hmul : ∀ s > 0, ∀ t > 0, G (s + t) = G s * G t) :
    ∃ θ > 0, ∀ t > 0, G t = Real.exp (-θ * t) := by
  set g : ℝ → ℝ := fun t => -Real.log (G t)
  have hgpos : ∀ t > 0, 0 < g t := fun t ht =>
    neg_pos.2 (Real.log_neg (hG t ht).1 (hG t ht).2)
  have hgadd : ∀ s > 0, ∀ t > 0, g (s + t) = g s + g t := fun s hs t ht => by
    simp only [g, hmul s hs t ht, Real.log_mul (hG s hs).1.ne' (hG t ht).1.ne']
    ring
  have hgmono : MonotoneOn g (Ioi 0) := fun s hs t ht hst =>
    neg_le_neg (Real.log_le_log (hG t ht).1 (hanti hs ht hst))
  -- `g(q) = q g(1)` for positive rationals `q = m/n`
  have hrat : ∀ m n : ℕ, 0 < m → 0 < n → g ((m : ℝ) / n) = (m : ℝ) / n * g 1 := by
    intro m n hm hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : 0 < (m : ℝ) / n := div_pos (by exact_mod_cast hm) hn'
    have h1 := add_nsmul_of_additive hgadd hq n hn
    rw [mul_div_cancel₀ _ hn'.ne'] at h1
    have h2 := add_nsmul_of_additive hgadd one_pos m hm
    rw [mul_one] at h2
    rw [h2] at h1
    field_simp
    linarith
  have hrat' : ∀ q : ℚ, 0 < q → g q = q * g 1 := by
    intro q hq
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have h := hrat q.num.toNat q.den (by omega) q.pos
    have hcast : ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]]
      exact_mod_cast (Rat.num_div_den q)
    rw [hcast] at h
    exact h
  have g1 := hgpos 1 one_pos
  refine ⟨g 1, g1, fun t ht => ?_⟩
  have hgt : g t = t * g 1 := by
    rcases lt_trichotomy (g t) (t * g 1) with hlt | heq | hgt'
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show g t / g 1 < t by rwa [div_lt_iff₀ g1])
      have hq0 : (0 : ℝ) < q := lt_trans (div_pos (hgpos t ht) g1) hq1
      have := hgmono (show (q : ℝ) ∈ Set.Ioi 0 from hq0) ht hq2.le
      rw [hrat' q (by exact_mod_cast hq0)] at this
      rw [div_lt_iff₀ g1] at hq1
      linarith
    · exact heq
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < g t / g 1 by rwa [lt_div_iff₀ g1])
      have hq0 : (0 : ℝ) < q := ht.trans hq1
      have := hgmono ht (show (q : ℝ) ∈ Set.Ioi 0 from hq0) hq1.le
      rw [hrat' q (by exact_mod_cast hq0)] at this
      rw [lt_div_iff₀ g1] at hq2
      linarith
  have hG' : G t = Real.exp (-(g t)) := by
    simp only [g, neg_neg]
    exact (Real.exp_log (hG t ht).1).symm
  rw [hG', hgt]
  ring_nf

/-- **Lemma 10.1.1** (p. 310), (i) ⇒ (ii): for `θ > 0`, `G(t) = e^{−θt}` is decreasing, lies in
`(0, 1)` for `t > 0`, and is memoryless. -/
theorem exp_counter_properties {θ : ℝ} (hθ : 0 < θ) :
    Antitone (fun t => Real.exp (-θ * t)) ∧ (∀ t > 0, 0 < Real.exp (-θ * t) ∧
      Real.exp (-θ * t) < 1) ∧
      ∀ s t, Real.exp (-θ * (s + t)) = Real.exp (-θ * s) * Real.exp (-θ * t) :=
  ⟨fun s t hst => Real.exp_le_exp.2 (by nlinarith), fun t ht =>
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by nlinarith)⟩, fun s t => (exp_memoryless θ s t).1⟩

/-! ### The matrix exponential (§10.1.1.3) -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `‖I‖ ≤ 1` in the operator norm. -/
theorem norm_one_le : ‖(1 : Matrix X X ℝ)‖ ≤ 1 :=
  norm_le_of_rowsum_abs_le _ zero_le_one fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne' hj]) (by simp)]
    simp

/-- `‖Aᵏ‖ ≤ ‖A‖ᵏ`. -/
theorem norm_pow_le_pow (A : Matrix X X ℝ) (k : ℕ) : ‖A ^ k‖ ≤ ‖A‖ ^ k := by
  induction k with
  | zero => simpa using norm_one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- **Exercise 10.1.2** (p. 311): the partial sums of (10.6) are bounded:
`‖∑_{k<m} Aᵏ/k!‖ ≤ e^{‖A‖}`. -/
theorem norm_partialSum_exp_le (A : Matrix X X ℝ) (m : ℕ) :
    ‖∑ k ∈ range m, ((k.factorial : ℝ)⁻¹) • A ^ k‖ ≤ Real.exp ‖A‖ := by
  refine (norm_sum_le _ _).trans ((sum_le_sum fun k _ => ?_).trans
    (Real.sum_le_exp_of_nonneg (norm_nonneg A) m))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le_pow A k) (by positivity)

/-- **Lemma 10.1.2 (i)** and **Exercise 10.1.3** (pp. 311–312): if `A = PDP⁻¹` then
`e^A = Pe^DP⁻¹`. -/
theorem exp_conj_eq {P D : Matrix X X ℝ} (hP : IsUnit P) :
    NormedSpace.exp (P * D * P⁻¹) = P * NormedSpace.exp D * P⁻¹ :=
  Matrix.exp_conj P D hP

/-- **Lemma 10.1.2 (ii)** (p. 311): commuting matrices have `e^{A+B} = e^Ae^B`. -/
theorem exp_add_eq {A B : Matrix X X ℝ} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B :=
  Matrix.exp_add_of_commute A B h

/-- **Lemma 10.1.2 (iii)** (p. 311): `e^{mA} = (e^A)^m`. -/
theorem exp_natCast_smul (m : ℕ) (A : Matrix X X ℝ) :
    NormedSpace.exp ((m : ℝ) • A) = NormedSpace.exp A ^ m := by
  rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]

/-- **Lemma 10.1.2 (v)** and **Exercise 10.1.4** (pp. 311–312): `d/dt e^{tA} = e^{tA}A`. -/
theorem hasDerivAt_exp_smul (A : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (NormedSpace.exp (t • A) * A) t :=
  hasDerivAt_exp_smul_const A t

/-- **Lemma 10.1.2 (v)** (p. 311): `d/dt e^{tA} = Ae^{tA}`. -/
theorem hasDerivAt_exp_smul' (A : Matrix X X ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (A * NormedSpace.exp (t • A)) t :=
  hasDerivAt_exp_smul_const' A t

/-- `e^{tA}` commutes with `A`. -/
theorem exp_smul_mul_comm (A : Matrix X X ℝ) (t : ℝ) :
    NormedSpace.exp (t • A) * A = A * NormedSpace.exp (t • A) :=
  (hasDerivAt_exp_smul A t).unique (hasDerivAt_exp_smul' A t)

/-- **Lemma 10.1.2 (vi)** (p. 311): `e^{Aᵀ} = (e^A)ᵀ`. -/
theorem exp_transpose_eq (A : Matrix X X ℝ) :
    NormedSpace.exp Aᵀ = (NormedSpace.exp A)ᵀ :=
  Matrix.exp_transpose A

/-- `t ↦ e^{tA}` is continuous. -/
theorem continuous_exp_smul (A : Matrix X X ℝ) :
    Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul A t).continuousAt

/-- **Lemma 10.1.2 (vii)** and **Exercise 10.1.6** (pp. 311–312):
`e^{tA} − e^{sA} = ∫_s^t e^{τA}A dτ`. -/
theorem exp_smul_sub_eq_integral (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp (t • A) - NormedSpace.exp (s • A) =
      ∫ τ in s..t, NormedSpace.exp (τ • A) * A := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hasDerivAt_exp_smul A τ)
    ?_).symm
  exact ((continuous_exp_smul A).mul continuous_const).intervalIntegrable _ _

/-- **Exercise 10.1.5** (p. 312): `e^A` is invertible with inverse `e^{−A}`. -/
theorem exp_mul_exp_neg (A : Matrix X X ℝ) :
    IsUnit (NormedSpace.exp A) ∧ NormedSpace.exp A * NormedSpace.exp (-A) = 1 ∧
      NormedSpace.exp (-A) = (NormedSpace.exp A)⁻¹ := by
  refine ⟨Matrix.isUnit_exp A, ?_, Matrix.exp_neg A⟩
  rw [← Matrix.exp_add_of_commute A (-A) (Commute.neg_right (Commute.refl A)), add_neg_cancel,
    NormedSpace.exp_zero]

/-! ### Eigenvectors and the exponential -/

/-- If `Aw = cw` then `e^A w = e^c w`, over `ℝ` or `ℂ`. -/
theorem exp_mulVec_of_eigen {𝕂 : Type*} [RCLike 𝕂] {A : Matrix X X 𝕂} {w : X → 𝕂} {c : 𝕂}
    (h : A *ᵥ w = c • w) : NormedSpace.exp A *ᵥ w = NormedSpace.exp c • w := by
  have : CompleteSpace (Matrix X X 𝕂) := FiniteDimensional.complete 𝕂 _
  have hpow : ∀ n : ℕ, A ^ n *ᵥ w = c ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul,
        pow_succ]
  let L : Matrix X X 𝕂 →L[𝕂] (X → 𝕂) := LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun a M => Matrix.smul_mulVec a M w }
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) A).mapL L
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) c).smul_const w
  refine h1.unique ?_
  convert h2 using 1
  funext n
  change ((n.factorial⁻¹ : 𝕂) • A ^ n) *ᵥ w = ((n.factorial⁻¹ : 𝕂) • c ^ n) • w
  rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]

/-- **Lemma 10.1.2 (iv)** (p. 311), forward direction for a real eigenpair: if `Aw = λw` then
`e^A w = e^λ w`. -/
theorem exp_mulVec_of_eigen_real {A : Matrix X X ℝ} {w : X → ℝ} {c : ℝ} (h : A *ᵥ w = c • w) :
    NormedSpace.exp A *ᵥ w = Real.exp c • w := by
  rw [Real.exp_eq_exp_ℝ]
  exact exp_mulVec_of_eigen h

omit [Fintype X] [DecidableEq X] in
/-- **Lemma 10.1.2 (iv)** (p. 311), converse refuted: for the `1 × 1` matrix `B = (2πi)`, `e^0 = 1`
is an eigenvalue of `e^B = I` but `0` is not an eigenvalue of `B`. -/
theorem exp_eigenvalue_converse_false :
    ∃ B : Matrix (Fin 1) (Fin 1) ℂ, Complex.exp 0 ∈ spectrum ℂ (NormedSpace.exp B) ∧
      (0 : ℂ) ∉ spectrum ℂ B := by
  have : CompleteSpace (Matrix (Fin 1) (Fin 1) ℂ) := FiniteDimensional.complete ℂ _
  refine ⟨algebraMap ℂ _ (2 * Real.pi * Complex.I), ?_, ?_⟩
  · rw [show NormedSpace.exp (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (2 * Real.pi * Complex.I)) =
        algebraMap ℂ _ (NormedSpace.exp (2 * Real.pi * Complex.I)) from
        (NormedSpace.algebraMap_exp_comm _).symm, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I,
      Complex.exp_zero, spectrum.scalar_eq]
    exact Set.mem_singleton 1
  · rw [spectrum.scalar_eq, Set.mem_singleton_iff]
    exact (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero).symm

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exponential flows and linear initial value problems

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.1–§10.1.2.3 (pp. 312–315).

* The flow `S_t = e^{tA}` has the semigroup property `S₀ = I`, `S_{s+t} = S_t S_s`
  (Example 10.1.2 is the scalar case).
* **Proposition 10.1.3**: `u_t = e^{tA}u₀` is the unique continuously differentiable solution of
  `u̇ = Au` on `[0, ∞)` (the book omits the uniqueness proof; here `e^{−tA}u_t` has derivative
  zero). Exercise 10.1.7 is the row-vector version `φ̇ = φP`.
* Exercise 10.1.8: `e^{tD} = diag(e^{tλ_j})`; (10.15): `e^{tλ} → 0` iff `Re λ < 0`.
* The bound `‖e^A‖ ≤ e^{‖A‖}`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The semigroup property of `S_t = e^{tA}` (§10.1.2.1): `S₀ = I` and `S_{s+t} = S_t S_s`. -/
theorem exp_smul_semigroup (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp ((0 : ℝ) • A) = 1 ∧
      NormedSpace.exp ((s + t) • A) = NormedSpace.exp (t • A) * NormedSpace.exp (s • A) := by
  refine ⟨by rw [zero_smul, NormedSpace.exp_zero], ?_⟩
  rw [add_comm, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left t |>.smul_right s)

/-- `e^{tA}e^{−tA} = I`. -/
theorem exp_smul_mul_exp_neg_smul (A : Matrix X X ℝ) (t : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) = 1 := by
  rw [← (exp_smul_semigroup A (-t) t).2, neg_add_cancel, zero_smul, NormedSpace.exp_zero]

/-- The linear map `M ↦ Mv` as a continuous linear map. -/
noncomputable def mulVecCLM (w : X → ℝ) : Matrix X X ℝ →L[ℝ] (X → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ w
      map_add' := fun M N => Matrix.add_mulVec M N w
      map_smul' := fun a M => Matrix.smul_mulVec a M w }

/-- The entry map `M ↦ M x y` as a continuous linear map. -/
noncomputable def entryCLM (x y : X) : Matrix X X ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Entries of `t ↦ e^{tA}` are differentiable, with `d/dt e^{tA} = Ae^{tA}` entrywise. -/
theorem hasDerivAt_exp_smul_entry (A : Matrix X X ℝ) (t : ℝ) (x y : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) x y) ((A * NormedSpace.exp (t • A)) x y) t :=
  (entryCLM x y).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)

/-- Entries of `t ↦ e^{−tA}` are differentiable, with derivative `−Ae^{−tA}`. -/
theorem hasDerivAt_exp_neg_smul_entry (A : Matrix X X ℝ) (t : ℝ) (x y : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • A) x y)
      (-(A * NormedSpace.exp ((-t) • A)) x y) t := by
  have h := (hasDerivAt_exp_smul_entry A (-t) x y).comp t (hasDerivAt_neg t)
  have e : (A * NormedSpace.exp ((-t) • A)) x y * -1 = (-(A * NormedSpace.exp ((-t) • A))) x y := by
    rw [Matrix.neg_apply]
    ring
  exact h.congr_deriv e

omit [DecidableEq X] in
/-- Product rule for `t ↦ M_t v_t`, with `M` differentiable entrywise. -/
theorem hasDerivAt_mulVec_of_entry {M : ℝ → Matrix X X ℝ} {M' : Matrix X X ℝ} {v : ℝ → X → ℝ}
    {v' : X → ℝ} {t : ℝ} (hM : ∀ x y, HasDerivAt (fun s => M s x y) (M' x y) t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => M s *ᵥ v s) (M' *ᵥ v t + M t *ᵥ v') t := by
  rw [hasDerivAt_pi]
  intro x
  have hv' : ∀ y, HasDerivAt (fun s => v s y) (v' y) t := hasDerivAt_pi.1 hv
  have h := HasDerivAt.fun_sum (u := univ) fun y _ => (hM x y).mul (hv' y)
  simp only [Pi.add_apply, mulVec, dotProduct]
  convert h using 1
  rw [← Finset.sum_add_distrib]

/-- `t ↦ e^{tA}u₀` has derivative `A e^{tA}u₀` (Proposition 10.1.3, existence). -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix X X ℝ) (u₀ : X → ℝ) (t : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp (s • A) *ᵥ u₀) (A *ᵥ (NormedSpace.exp (t • A) *ᵥ u₀))
      t := by
  have h := (mulVecCLM u₀).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul' A t)
  rw [Matrix.mulVec_mulVec]
  exact h

/-- **Proposition 10.1.3** (p. 313): `u_t = e^{tA}u₀` is the unique solution of `u̇ = Au` with
`u(0) = u₀` among functions differentiable on `[0, ∞)`. -/
theorem ivp_unique (A : Matrix X X ℝ) (u₀ : X → ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) *ᵥ u₀)
      (A *ᵥ (NormedSpace.exp (t • A) *ᵥ u₀)) t) ∧
      ∀ u : ℝ → X → ℝ, u 0 = u₀ → (∀ t : ℝ, 0 ≤ t → HasDerivAt u (A *ᵥ u t) t) →
        ∀ t : ℝ, 0 ≤ t → u t = NormedSpace.exp (t • A) *ᵥ u₀ := by
  refine ⟨hasDerivAt_exp_smul_mulVec A u₀, fun u hu0 hu t ht => ?_⟩
  set g : ℝ → X → ℝ := fun s => NormedSpace.exp ((-s) • A) *ᵥ u s
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := fun s hs => by
    have h := hasDerivAt_mulVec_of_entry (M' := -(A * NormedSpace.exp ((-s) • A)))
      (hasDerivAt_exp_neg_smul_entry A s) (hu s hs)
    convert h using 1
    rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec, ← exp_smul_mul_comm A (-s), neg_add_cancel]
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hg s hs.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun s hs => (hg s hs.1).hasDerivWithinAt
  have h := hconst t ⟨ht, le_rfl⟩
  simp only [g, neg_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hu0] at h
  calc u t = (NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A)) *ᵥ u t := by
        rw [exp_smul_mul_exp_neg_smul, Matrix.one_mulVec]
    _ = NormedSpace.exp (t • A) *ᵥ (NormedSpace.exp ((-t) • A) *ᵥ u t) := by
        rw [Matrix.mulVec_mulVec]
    _ = NormedSpace.exp (t • A) *ᵥ u₀ := by rw [h]

/-- **Exercise 10.1.7** (p. 314): the row-vector IVP `φ̇ = φP`, `φ(0) = φ₀`, has the unique solution
`φ_t = φ₀e^{tP}` on `[0, ∞)`. -/
theorem ivp_unique_row (P : Matrix X X ℝ) (φ₀ : X → ℝ) (φ : ℝ → X → ℝ) (hφ0 : φ 0 = φ₀)
    (hφ : ∀ t, 0 ≤ t → HasDerivAt φ (φ t ᵥ* P) t) (t : ℝ) (ht : 0 ≤ t) :
    φ t = φ₀ ᵥ* NormedSpace.exp (t • P) := by
  have h := (ivp_unique Pᵀ φ₀).2 φ hφ0 (fun s hs => by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
    exact hφ s hs) t ht
  rw [h, ← Matrix.vecMul_transpose, ← Matrix.transpose_smul, Matrix.exp_transpose,
    Matrix.transpose_transpose]

/-- **Exercise 10.1.8** (p. 314): `e^{tD} = diag(e^{tλ₁}, …, e^{tλₙ})` for `D = diag(λ)`. -/
theorem exp_smul_diagonal (d : X → ℝ) (t : ℝ) :
    NormedSpace.exp (t • Matrix.diagonal d) = Matrix.diagonal fun i => Real.exp (t * d i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have h := congrFun (exp_mulVec_of_eigen_real (A := t • Matrix.diagonal d)
      (w := Pi.single i 1) (c := t * d i) (by
        ext k
        by_cases hk : k = i
        · subst hk; simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
        · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hk, Pi.single_apply])) i
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
    rw [Matrix.diagonal_apply_eq, ← h]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  · have h := congrFun (exp_mulVec_of_eigen_real (A := t • Matrix.diagonal d)
      (w := Pi.single j 1) (c := t * d j) (by
        ext k
        by_cases hk : k = j
        · subst hk; simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
        · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hk, Pi.single_apply])) i
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hij, smul_eq_mul, mul_zero] at h
    rw [Matrix.diagonal_apply_ne _ hij, ← h]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- (10.15) (p. 315): for `λ ∈ ℂ`, `e^{tλ} → 0` as `t → ∞` iff `Re λ < 0`. -/
theorem tendsto_exp_mul_zero_iff (c : ℂ) :
    Tendsto (fun t : ℝ => Complex.exp (t * c)) atTop (𝓝 0) ↔ c.re < 0 := by
  have hnorm : ∀ t : ℝ, ‖Complex.exp (t * c)‖ = Real.exp (t * c.re) := fun t => by
    rw [Complex.norm_exp]
    simp
  constructor
  · intro h
    by_contra hre
    push Not at hre
    have h1 := (tendsto_zero_iff_norm_tendsto_zero.1 h).eventually (gt_mem_nhds one_pos)
    obtain ⟨t, ht1, ht⟩ := (h1.and (eventually_ge_atTop (0 : ℝ))).exists
    rw [hnorm] at ht1
    have : 1 ≤ Real.exp (t * c.re) := Real.one_le_exp (mul_nonneg ht hre)
    linarith
  · intro hre
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hnorm]
    exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hre)

/-- `‖e^A‖ ≤ e^{‖A‖}`, from Exercise 10.1.2. -/
theorem norm_exp_le (A : Matrix X X ℝ) : ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).tendsto_sum_nat
  exact le_of_tendsto' h.norm fun m => norm_partialSum_exp_le A m

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral bound and stability of exponential flows

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.3–§10.1.2.4 (pp. 314–317).

The spectral bound (10.16) is `s(A) = max_{λ ∈ σ(A)} Re λ`, over the complex eigenvalues of `A`.

* The spectral mapping theorem for the exponential: `σ(e^A) = e^{σ(A)}`. One inclusion is
  Mathlib's `spectrum.exp_mem_exp`; for the other, an eigenvalue `μ` of `e^A` has an eigenspace
  invariant under `A` (which commutes with `e^A`), and an eigenvector `w` of `A` in it gives
  `μw = e^A w = e^λ w`. With it, the converse of Lemma 10.1.2 (iv) fails for a real matrix:
  `e^0` is an eigenvalue of `e^A` for `A = (0, −2π; 2π, 0)`, while `0` is not an eigenvalue of `A`.
* **Lemma 10.1.4**: `τs(A) = s(τA)` for `τ > 0` (Exercise 10.1.9), `e^{s(A)} = ρ(e^A)`
  (Exercise 10.1.10), and `s(A) = lim_k (1/k) ln ‖e^{kA}‖` over `k ∈ ℕ` (Exercise 10.1.11).
* **Theorem 10.1.5**: (i) `s(A) < 0`, (ii) `‖e^{tA}‖ → 0`, (iii) `‖e^{tA}‖ ≤ Me^{−ωt}` and
  (iv) `∫₀^∞ ‖e^{tA}u₀‖^p dt < ∞` for all `p ≥ 1` and `u₀` are equivalent. The book cites Engel and
  Nagel for the proof and asks for (i) ⇒ (ii) and (iii) ⇒ (iv) (Exercise 10.1.12). For
  (iv) ⇒ (i), an eigenvalue `λ` with `Re λ ≥ 0` and eigenvector `a + ib` give
  `‖e^{tA}a‖ + ‖e^{tA}b‖ ≥ c > 0` for all `t ≥ 0`.
-/

open Finset Matrix Filter Topology Function Set MeasureTheory
open scoped Pointwise

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `complexify` commutes with the exponential. -/
theorem complexify_exp (A : Matrix X X ℝ) :
    complexify (NormedSpace.exp A) = NormedSpace.exp (complexify A) :=
  NormedSpace.map_exp (Complex.ofRealHom.mapMatrix (m := X))
    (Continuous.matrix_map continuous_id Complex.continuous_ofReal) A

omit [Fintype X] [DecidableEq X] in
/-- `complexify (tA) = t · complexify A`. -/
theorem complexify_smul (t : ℝ) (A : Matrix X X ℝ) :
    complexify (t • A) = (t : ℂ) • complexify A := by
  ext i j
  simp [complexify_apply]

/-- The spectral mapping theorem for the exponential: `σ(e^A) = e^{σ(A)}`. -/
theorem spectrum_complexify_exp (A : Matrix X X ℝ) :
    spectrum ℂ (complexify (NormedSpace.exp A)) = Complex.exp '' spectrum ℂ (complexify A) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  set B := complexify A
  rw [complexify_exp]
  ext μ
  constructor
  · intro hμ
    -- `μ` is an eigenvalue of `e^B`; its eigenspace is invariant under `B`
    have hμ' : μ ∈ spectrum ℂ (complexify (NormedSpace.exp A)) := by rwa [complexify_exp]
    obtain ⟨e, he, hee⟩ := (mem_spectrum_iff_eigenpair (NormedSpace.exp A) μ).1 hμ'
    rw [complexify_exp] at hee
    set E : Submodule ℂ (X → ℂ) :=
      LinearMap.ker (Matrix.toLin' (NormedSpace.exp B) - μ • LinearMap.id)
    have hmemE : ∀ v, v ∈ E ↔ NormedSpace.exp B *ᵥ v = μ • v := fun v => by
      simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hcomm : NormedSpace.exp B * B = B * NormedSpace.exp B :=
      ((Commute.refl B).exp_left).eq
    have hinv : ∀ v ∈ E, Matrix.toLin' B v ∈ E := fun v hv => by
      rw [hmemE] at hv ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_smul]
    let g : Module.End ℂ E := (Matrix.toLin' B).restrict hinv
    have hne : Nontrivial E := ⟨⟨⟨e, (hmemE e).2 hee⟩, 0, fun h => he (congrArg Subtype.val h)⟩⟩
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw0 : (w : X → ℂ) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hBw : B *ᵥ (w : X → ℂ) = c • (w : X → ℂ) := by
      have := congrArg Subtype.val hw.apply_eq_smul
      simpa [g, LinearMap.restrict_apply, Matrix.toLin'_apply] using this
    have hexp1 := exp_mulVec_of_eigen hBw
    have hexp2 := (hmemE w).1 w.2
    rw [hexp1] at hexp2
    have hμc : μ = NormedSpace.exp c := by
      by_contra hne'
      have h0 : (NormedSpace.exp c - μ) • (w : X → ℂ) = 0 := by rw [sub_smul, hexp2, sub_self]
      rcases smul_eq_zero.1 h0 with h | h
      · exact hne' (sub_eq_zero.1 h).symm
      · exact hw0 h
    refine ⟨c, (mem_spectrum_iff_eigenpair A c).2 ⟨w, hw0, hBw⟩, ?_⟩
    rw [hμc, Complex.exp_eq_exp_ℂ]
  · rintro ⟨c, hc, rfl⟩
    rw [Complex.exp_eq_exp_ℂ]
    exact spectrum.exp_mem_exp B hc

/-- The spectral bound (10.16): `s(A) = max_{λ ∈ σ(A)} Re λ`. -/
noncomputable def spectralBound (A : Matrix X X ℝ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (complexify A))

/-- **Lemma 10.1.2 (iv)** (p. 311), converse refuted for a real matrix: for the rotation generator
`A = (0, −2π; 2π, 0)`, `e^0 = 1` is an eigenvalue of `e^A` (since `2πi` is an eigenvalue of `A`),
but `0` is not an eigenvalue of `A`. -/
theorem exp_eigenvalue_converse_false_real :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, Complex.exp 0 ∈ spectrum ℂ (complexify (NormedSpace.exp A)) ∧
      (0 : ℂ) ∉ spectrum ℂ (complexify A) := by
  refine ⟨!![0, -(2 * Real.pi); 2 * Real.pi, 0], ?_, ?_⟩
  · rw [spectrum_complexify_exp]
    refine ⟨2 * Real.pi * Complex.I, ?_, by rw [Complex.exp_zero, Complex.exp_two_pi_mul_I]⟩
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      Matrix.det_fin_two]
    simp [complexify_apply, Algebra.algebraMap_eq_smul_one]
    ring_nf
    simp [Complex.I_sq]
  · rw [spectrum.mem_iff, not_not, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_fin_two]
    simp [complexify_apply, Real.pi_ne_zero]

variable [Nonempty X]

theorem spectrum_nonempty (A : Matrix X X ℝ) : (spectrum ℂ (complexify A)).Nonempty := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  exact spectrum.nonempty _

omit [Nonempty X] in
theorem re_spectrum_finite (A : Matrix X X ℝ) : (Complex.re '' spectrum ℂ (complexify A)).Finite :=
  (Matrix.finite_spectrum _).image _

omit [Nonempty X] in
/-- `Re λ ≤ s(A)` for every eigenvalue `λ`. -/
theorem re_le_spectralBound {A : Matrix X X ℝ} {c : ℂ} (hc : c ∈ spectrum ℂ (complexify A)) :
    c.re ≤ spectralBound A :=
  le_csSup (re_spectrum_finite A).bddAbove ⟨c, hc, rfl⟩

/-- `s(A)` is attained. -/
theorem exists_re_eq_spectralBound (A : Matrix X X ℝ) :
    ∃ c ∈ spectrum ℂ (complexify A), c.re = spectralBound A :=
  ((spectrum_nonempty A).image _).csSup_mem (re_spectrum_finite A)

/-- **Lemma 10.1.4** and **Exercise 10.1.10** (p. 316): `e^{s(A)} = ρ(e^A)`. -/
theorem specRad_exp (A : Matrix X X ℝ) :
    specRad (NormedSpace.exp A) = Real.exp (spectralBound A) := by
  have hnn : ∀ z : ℂ, ((‖z‖₊ : NNReal) : ENNReal) = ENNReal.ofReal ‖z‖ := fun z => by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  have hsr : spectralRadius ℂ (complexify (NormedSpace.exp A)) =
      ENNReal.ofReal (Real.exp (spectralBound A)) := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
    · rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, spectrum_complexify_exp] at hμ
      rcases hμ with ⟨c, hc, rfl⟩ | hμ0
      swap
      · rw [Set.mem_singleton_iff] at hμ0
        rw [hμ0, nnnorm_zero, ENNReal.coe_zero]
        exact bot_le
      rw [hnn, Complex.norm_exp]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (re_le_spectralBound hc))
    · obtain ⟨c, hc, hre⟩ := exists_re_eq_spectralBound A
      have hmem : Complex.exp c ∈ spectrum ℂ (complexify (NormedSpace.exp A)) := by
        rw [spectrum_complexify_exp]
        exact ⟨c, hc, rfl⟩
      have := le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ (complexify (NormedSpace.exp A))) =>
        ((‖k‖₊ : NNReal) : ENNReal)) _ (spectrum_subset_quasispectrum ℂ _ hmem)
      rw [hnn, Complex.norm_exp, hre] at this
      exact this
  unfold specRad
  rw [hsr, ENNReal.toReal_ofReal (Real.exp_pos _).le]

omit [Nonempty X] in
/-- **Lemma 10.1.4** and **Exercise 10.1.9** (p. 316): `τs(A) = s(τA)` for `τ > 0`. -/
theorem spectralBound_smul [Nonempty X] {τ : ℝ} (hτ : 0 < τ) (A : Matrix X X ℝ) :
    τ * spectralBound A = spectralBound (τ • A) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  unfold spectralBound
  rw [complexify_smul, spectrum.smul_eq_smul _ _ (spectrum_nonempty A)]
  have himg : Complex.re '' ((τ : ℂ) • spectrum ℂ (complexify A)) =
      τ • (Complex.re '' spectrum ℂ (complexify A)) := by
    ext r
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c.re, ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨τ * c, ⟨c, hc, rfl⟩, by simp⟩
  rw [himg, Real.sSup_smul_of_nonneg hτ.le, smul_eq_mul]

/-- `e^{kA}` is invertible, so its norm is positive. -/
theorem norm_exp_pos (A : Matrix X X ℝ) : 0 < ‖NormedSpace.exp A‖ := by
  refine norm_pos_iff.2 fun h => ?_
  have h1 := (exp_mul_exp_neg A).2.1
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- **Lemma 10.1.4** and **Exercise 10.1.11** (p. 316): `s(A) = lim_{k → ∞} (1/k) ln ‖e^{kA}‖`,
the limit over `k ∈ ℕ`. -/
theorem tendsto_log_norm_exp (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => (1 / (k : ℝ)) * Real.log ‖NormedSpace.exp ((k : ℝ) • A)‖) atTop
      (𝓝 (spectralBound A)) := by
  have h := tendsto_norm_pow_rpow (NormedSpace.exp A)
  rw [specRad_exp] at h
  have hlog := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp h
  rw [Real.log_exp] at hlog
  refine hlog.congr fun k => ?_
  simp only [Function.comp, exp_natCast_smul]
  have hpos : 0 < ‖NormedSpace.exp A ^ k‖ := by
    rw [← exp_natCast_smul]
    exact norm_exp_pos _
  rw [Real.log_rpow hpos]

omit [Nonempty X] in
/-- `e^{tA} = e^{sA}e^{tA}` for commuting multiples. -/
theorem exp_smul_add (A : Matrix X X ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t)

/-- Theorem 10.1.5 (i) ⇒ (iii): if `s(A) < 0` then `‖e^{tA}‖ ≤ Me^{−ωt}` for some `M, ω > 0`. -/
theorem exists_exp_bound {A : Matrix X X ℝ} (hs : spectralBound A < 0) :
    ∃ M ω : ℝ, 0 < M ∧ 0 < ω ∧ ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ M * Real.exp (-ω * t) := by
  have hρ : specRad (NormedSpace.exp A) < 1 := by
    rw [specRad_exp]
    exact Real.exp_lt_one_iff.2 hs
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 < r := (specRad_nonneg _).trans_lt hr1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_norm_pow_le (NormedSpace.exp A) hr1)
  set C : ℝ := ∑ k ∈ range K, ‖NormedSpace.exp A ^ k‖ / r ^ k + 1
  have hC1 : 1 ≤ C := le_add_of_nonneg_left (sum_nonneg fun k _ => by positivity)
  have hCk : ∀ k : ℕ, ‖NormedSpace.exp A ^ k‖ ≤ C * r ^ k := by
    intro k
    by_cases hk : k < K
    · have h1 : ‖NormedSpace.exp A ^ k‖ / r ^ k ≤ C :=
        (single_le_sum (f := fun k => ‖NormedSpace.exp A ^ k‖ / r ^ k)
          (fun k _ => by positivity) (mem_range.2 hk)).trans (le_add_of_nonneg_right zero_le_one)
      rwa [div_le_iff₀ (by positivity)] at h1
    · exact (hK k (not_lt.1 hk)).trans (le_mul_of_one_le_left (by positivity) hC1)
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr2
  refine ⟨C * Real.exp ‖A‖ / r, -Real.log r, by positivity, by linarith, fun t ht => ?_⟩
  set k := ⌊t⌋₊
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht
  have htk : t < k + 1 := Nat.lt_floor_add_one t
  have hsplit : NormedSpace.exp (t • A) =
      NormedSpace.exp ((k : ℝ) • A) * NormedSpace.exp ((t - k) • A) := by
    rw [← exp_smul_add]
    congr 2
    ring
  have hf : ‖NormedSpace.exp ((t - k) • A)‖ ≤ Real.exp ‖A‖ := by
    refine (norm_exp_le _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hrk : r ^ k ≤ Real.exp (-(-Real.log r) * t) / r := by
    rw [neg_neg, le_div_iff₀ hr0, ← pow_succ, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hr0, Real.exp_le_exp, mul_comm (Real.log r) t]
    push_cast
    nlinarith
  calc ‖NormedSpace.exp (t • A)‖ ≤ ‖NormedSpace.exp ((k : ℝ) • A)‖ *
        ‖NormedSpace.exp ((t - k) • A)‖ := by rw [hsplit]; exact norm_mul_le _ _
    _ ≤ (C * r ^ k) * Real.exp ‖A‖ := by
        rw [exp_natCast_smul]
        exact mul_le_mul (hCk k) hf (norm_nonneg _) (by positivity)
    _ ≤ (C * (Real.exp (-(-Real.log r) * t) / r)) * Real.exp ‖A‖ := by
        gcongr
    _ = C * Real.exp ‖A‖ / r * Real.exp (-(-Real.log r) * t) := by ring

/-- **Theorem 10.1.5** (p. 316): for any square matrix `A`, the following are equivalent:
(i) `s(A) < 0`; (ii) `‖e^{tA}‖ → 0` as `t → ∞`; (iii) `‖e^{tA}‖ ≤ Me^{−ωt}` for some `M, ω > 0`;
(iv) `∫₀^∞ ‖e^{tA}u₀‖^p dt < ∞` for every `p ≥ 1` and `u₀`. -/
theorem stability_tfae (A : Matrix X X ℝ) :
    [spectralBound A < 0,
      Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖) atTop (𝓝 0),
      ∃ M ω : ℝ, 0 < M ∧ 0 < ω ∧ ∀ t : ℝ, 0 ≤ t →
        ‖NormedSpace.exp (t • A)‖ ≤ M * Real.exp (-ω * t),
      ∀ p : ℝ, 1 ≤ p → ∀ u₀ : X → ℝ,
        IntegrableOn (fun t : ℝ => ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p) (Ioi 0)].TFAE := by
  tfae_have 1 → 3 := exists_exp_bound
  tfae_have 3 → 2 := by
    rintro ⟨M, ω, hM, hω, hb⟩
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 0).mono fun t ht => hb t ht) ?_
    have : Tendsto (fun t : ℝ => Real.exp (-ω * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    simpa using this.const_mul M
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨T, hT⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    set K : ℕ := ⌈T⌉₊ + 1
    have hK : (0 : ℝ) < K := by positivity
    have hKT : T ≤ K := (Nat.le_ceil T).trans (by simp [K])
    have h1 : Real.exp (spectralBound ((K : ℝ) • A)) < 1 := by
      rw [← specRad_exp]
      exact (specRad_le_norm _).trans_lt (hT K hKT)
    rw [← spectralBound_smul hK] at h1
    have := Real.exp_lt_one_iff.1 h1
    by_contra hge
    exact absurd this (not_lt.2 (mul_nonneg hK.le (not_lt.1 hge)))
  tfae_have 3 → 4 := by
    rintro ⟨M, ω, hM, hω, hb⟩ p hp u₀
    have hp0 : 0 ≤ p := by linarith
    have hint : IntegrableOn (fun t : ℝ => (M * ‖u₀‖) ^ p * Real.exp (-(p * ω) * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul _
    refine hint.mono' ?_ ?_
    · exact (((continuous_exp_smul A).matrix_mulVec continuous_const).norm.rpow_const
        fun _ => Or.inr hp0).aestronglyMeasurable.restrict
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p ≤ (M * Real.exp (-ω * t) * ‖u₀‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul_of_nonneg_right (hb t ht0) (norm_nonneg _))) hp0
        _ = (M * ‖u₀‖) ^ p * Real.exp (-(p * ω) * t) := by
            rw [show M * Real.exp (-ω * t) * ‖u₀‖ = (M * ‖u₀‖) * Real.exp (-ω * t) by ring,
              Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
            congr 2
            ring
  tfae_have 4 → 1 := by
    intro hint
    by_contra hge
    push Not at hge
    obtain ⟨c, hc, hre⟩ := exists_re_eq_spectralBound A
    obtain ⟨e, he, hee⟩ := (mem_spectrum_iff_eigenpair A c).1 hc
    obtain ⟨x0, hx0⟩ : ∃ x0, e x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact he (funext h)
    set a : X → ℝ := fun x => (e x).re
    set b : X → ℝ := fun x => (e x).im
    -- `complexify M *ᵥ e = Ma + i Mb`
    have hsplit : ∀ M : Matrix X X ℝ, ∀ x, (complexify M *ᵥ e) x =
        ((M *ᵥ a) x : ℂ) + ((M *ᵥ b) x : ℂ) * Complex.I := by
      intro M x
      simp only [mulVec, dotProduct, complexify_apply, a, b]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← Complex.re_add_im (e j)]
      ring
    have hlow : ∀ t : ℝ, 0 ≤ t →
        ‖e x0‖ ≤ ‖NormedSpace.exp (t • A) *ᵥ a‖ + ‖NormedSpace.exp (t • A) *ᵥ b‖ := by
      intro t ht
      have he1 : complexify (t • A) *ᵥ e = ((t : ℂ) * c) • e := by
        rw [complexify_smul, Matrix.smul_mulVec, hee, smul_smul]
      have he2 := exp_mulVec_of_eigen he1
      rw [← complexify_exp] at he2
      have hx := congrFun he2 x0
      rw [hsplit, Pi.smul_apply, smul_eq_mul] at hx
      have hnorm : ‖NormedSpace.exp ((t : ℂ) * c) * e x0‖ = Real.exp (t * c.re) * ‖e x0‖ := by
        rw [norm_mul, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
        simp
      have h1 : ‖e x0‖ ≤ ‖NormedSpace.exp ((t : ℂ) * c) * e x0‖ := by
        rw [hnorm]
        exact le_mul_of_one_le_left (norm_nonneg _)
          (Real.one_le_exp (mul_nonneg ht (hre ▸ hge)))
      rw [← hx] at h1
      refine h1.trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      · rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ x0
      · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          ← Real.norm_eq_abs]
        exact norm_le_pi_norm _ x0
    have ha := hint 1 le_rfl a
    have hb := hint 1 le_rfl b
    simp only [Real.rpow_one] at ha hb
    have hsum := ha.add hb
    have hconst : IntegrableOn (fun _ : ℝ => ‖e x0‖) (Ioi 0) := by
      refine hsum.mono' (by fun_prop) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hlow t (le_of_lt ht)
    rw [integrableOn_const_iff, Real.volume_Ioi] at hconst
    rcases hconst with h | h
    · exact hx0 (by simpa using h)
    · exact absurd h (lt_irrefl _)
  tfae_finish

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Strongly continuous semigroups on `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.2.5 (pp. 317–318).

A family `(S_t)_{t ≥ 0}` of linear operators on `ℝ^X` is a `C₀`-semigroup if `S₀ = I`,
`S_{t+t'} = S_t S_{t'}` and `t ↦ S_t u` is continuous on `[0, ∞)` for every `u`.

* Example 10.1.3: `S_t = e^{tA}` is a `C₀`-semigroup.
* **Proposition 10.1.6**: every `C₀`-semigroup on `ℝ^X` is exponential, `S_t = e^{tA}`, and `A` is
  its infinitesimal generator (10.19), `A = lim_{t ↓ 0} (S_t − I)/t`. The book cites Engel and Nagel
  (Theorem 2.12). The proof here: `V(h) = ∫₀^h S_τ dτ` has `V(h)/h → I`, so `W = V(h₀)` is
  invertible for some `h₀ > 0`; then `S_h W = V(h + h₀) − V(h)`, so `S` is differentiable with
  `Ṡ_h = S_h A`, `A = (S_{h₀} − I)W⁻¹`; finally `S_h e^{−hA}` has derivative zero.

Matrix-valued derivatives and limits are taken entry by entry, as in the book (p. 312).
-/

open Finset Matrix Filter Topology Function Set MeasureTheory

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A strongly continuous (`C₀`) semigroup on `ℝ^X` (p. 317). -/
structure IsC0Semigroup (S : ℝ → Matrix X X ℝ) : Prop where
  zero : S 0 = 1
  add : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t
  cont : ∀ u : X → ℝ, ContinuousOn (fun t => S t *ᵥ u) (Ici 0)

/-- **Example 10.1.3** (p. 317): `S_t = e^{tA}` is a `C₀`-semigroup. -/
theorem isC0Semigroup_exp (A : Matrix X X ℝ) :
    IsC0Semigroup fun t : ℝ => NormedSpace.exp (t • A) where
  zero := by rw [zero_smul, NormedSpace.exp_zero]
  add s t _ _ := exp_smul_add A s t
  cont u := fun t _ => (hasDerivAt_exp_smul_mulVec A u t).continuousAt.continuousWithinAt

omit [DecidableEq X] in
/-- Product rule for matrix products, entrywise, at a point. -/
theorem hasDerivAt_mul_entry {M N : ℝ → Matrix X X ℝ} {M' N' : Matrix X X ℝ} {t : ℝ}
    (hM : ∀ x y, HasDerivAt (fun s => M s x y) (M' x y) t)
    (hN : ∀ x y, HasDerivAt (fun s => N s x y) (N' x y) t) (x y : X) :
    HasDerivAt (fun s => (M s * N s) x y) ((M' * N t + M t * N') x y) t := by
  have h := HasDerivAt.fun_sum (u := univ) fun z _ => (hM x z).mul (hN z y)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  rw [← Finset.sum_add_distrib]

namespace IsC0Semigroup

variable {S : ℝ → Matrix X X ℝ} (h : IsC0Semigroup S)
include h

/-- The entries of a `C₀`-semigroup are continuous on `[0, ∞)`. -/
theorem continuousOn_entry (x y : X) : ContinuousOn (fun t => S t x y) (Ici 0) := by
  have h1 := (continuous_apply x).comp_continuousOn (h.cont (Pi.single y 1))
  refine h1.congr fun t _ => ?_
  simp [Function.comp, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The entries are interval integrable on `[0, b]` for `b ≥ 0`. -/
theorem intervalIntegrable_entry (x y : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t => S t x y) volume a b :=
  ((h.continuousOn_entry x y).mono fun _ hs => le_trans (le_min ha hb) hs.1).intervalIntegrable

/-- `V(h) = ∫₀^h S_τ dτ`, entrywise. -/
noncomputable def V (S : ℝ → Matrix X X ℝ) (b : ℝ) : Matrix X X ℝ :=
  fun x y => ∫ τ in (0 : ℝ)..b, S τ x y

/-- `d/dh V(h) = S_h` for `h > 0`. -/
theorem hasDerivAt_V {b : ℝ} (hb : 0 < b) (x y : X) :
    HasDerivAt (fun c => V S c x y) (S b x y) b :=
  intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable_entry x y le_rfl hb.le)
    ((h.continuousOn_entry x y).mono Ioi_subset_Ici_self |>.stronglyMeasurableAtFilter isOpen_Ioi b
      hb)
    ((h.continuousOn_entry x y).continuousAt (Ici_mem_nhds hb))

/-- `V(h)/h → I` as `h ↓ 0`, entrywise. -/
theorem tendsto_V_div (x y : X) :
    Tendsto (fun c => c⁻¹ * V S c x y) (𝓝[>] 0) (𝓝 ((1 : Matrix X X ℝ) x y)) := by
  have hd : HasDerivWithinAt (fun c => V S c x y) (S 0 x y) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (h.intervalIntegrable_entry x y le_rfl le_rfl)
      (((h.continuousOn_entry x y).mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Ioi 0)
      (((h.continuousOn_entry x y) 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self)
  have hs := hasDerivWithinAt_iff_tendsto_slope.1 hd
  rw [show Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 by ext; simp [lt_iff_le_and_ne, eq_comm]] at hs
  rw [h.zero] at hs
  refine hs.congr fun c => ?_
  simp [slope_def_field, V, div_eq_inv_mul]

/-- There is `h₀ > 0` with `V(h₀)` invertible. -/
theorem exists_V_isUnit : ∃ h₀ : ℝ, 0 < h₀ ∧ IsUnit (V S h₀) := by
  have hT : Tendsto (fun c => c⁻¹ • V S c) (𝓝[>] 0) (𝓝 (1 : Matrix X X ℝ)) :=
    tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => by
      simpa [Matrix.smul_apply] using h.tendsto_V_div x y
  have hdet := ((continuous_id.matrix_det).tendsto (1 : Matrix X X ℝ)).comp hT
  simp only [id, Matrix.det_one] at hdet
  obtain ⟨c, hc, hcpos⟩ := ((hdet.eventually (isOpen_ne.mem_nhds one_ne_zero)).and
    self_mem_nhdsWithin).exists
  refine ⟨c, hcpos, (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hc ?_)⟩
  change (c⁻¹ • V S c).det = 0
  rw [Matrix.det_smul, h0, mul_zero]

/-- `S_h V(h₀) = V(h + h₀) − V(h)` for `h, h₀ ≥ 0`. -/
theorem mul_V {b h₀ : ℝ} (hb : 0 ≤ b) (hh₀ : 0 ≤ h₀) :
    S b * V S h₀ = V S (b + h₀) - V S b := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.sub_apply, V]
  calc ∑ z, S b x z * ∫ τ in (0 : ℝ)..h₀, S τ z y
      = ∑ z, ∫ τ in (0 : ℝ)..h₀, S b x z * S τ z y := by
        simp only [intervalIntegral.integral_const_mul]
    _ = ∫ τ in (0 : ℝ)..h₀, ∑ z, S b x z * S τ z y := by
        rw [intervalIntegral.integral_finsetSum fun z _ =>
          (h.intervalIntegrable_entry z y le_rfl hh₀).const_mul _]
    _ = ∫ τ in (0 : ℝ)..h₀, S (b + τ) x y := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        have hτ0 : 0 ≤ τ := by
          rw [uIcc_of_le hh₀] at hτ
          exact hτ.1
        simp only [h.add b τ hb hτ0, Matrix.mul_apply]
    _ = ∫ σ in b..b + h₀, S σ x y := by
        rw [intervalIntegral.integral_comp_add_left (fun σ => S σ x y), add_zero]
    _ = (∫ τ in (0 : ℝ)..b + h₀, S τ x y) - ∫ τ in (0 : ℝ)..b, S τ x y :=
        (intervalIntegral.integral_interval_sub_left
          (h.intervalIntegrable_entry x y le_rfl (by linarith))
          (h.intervalIntegrable_entry x y le_rfl hb)).symm

/-- `Ṡ_h = S_h A` for `h > 0`, with `A = (S_{h₀} − I)V(h₀)⁻¹`. -/
theorem hasDerivAt_entry {h₀ : ℝ} (hh₀ : 0 < h₀) (hW : IsUnit (V S h₀)) {b : ℝ} (hb : 0 < b)
    (x y : X) :
    HasDerivAt (fun c => S c x y) ((S b * ((S h₀ - 1) * (V S h₀)⁻¹)) x y) b := by
  set W := V S h₀
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).1 hW
  -- `S_c = (V(c + h₀) − V(c))W⁻¹` near `b`
  have heq : ∀ᶠ c in 𝓝 b, S c x y = ((V S (c + h₀) - V S c) * W⁻¹) x y := by
    filter_upwards [Ioi_mem_nhds hb] with c hc
    rw [← h.mul_V (le_of_lt hc) hh₀.le, Matrix.mul_nonsing_inv_cancel_right _ _ hWdet]
  have hd : HasDerivAt (fun c => ((V S (c + h₀) - V S c) * W⁻¹) x y)
      (((S (b + h₀) - S b) * W⁻¹) x y) b := by
    simp only [Matrix.mul_apply, Matrix.sub_apply]
    refine HasDerivAt.fun_sum fun z _ => HasDerivAt.mul_const ?_ _
    have h1 : HasDerivAt (fun c => V S (c + h₀) x z) (S (b + h₀) x z) b := by
      have := (h.hasDerivAt_V (show (0 : ℝ) < b + h₀ by linarith) x z).comp b
        ((hasDerivAt_id b).add_const h₀)
      simp only [id, mul_one] at this
      exact this
    exact h1.sub (h.hasDerivAt_V hb x z)
  have hval : (S (b + h₀) - S b) * W⁻¹ = S b * ((S h₀ - 1) * W⁻¹) := by
    rw [h.add b h₀ hb.le hh₀.le, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one]
  rw [← hval]
  exact hd.congr_of_eventuallyEq heq

/-- **Proposition 10.1.6** (p. 318): every `C₀`-semigroup on `ℝ^X` is exponential, `S_t = e^{tA}`
for `t ≥ 0`, and `A` is its infinitesimal generator (10.19): `(S_t − I)/t → A` as `t ↓ 0`. -/
theorem exists_eq_exp :
    ∃ A : Matrix X X ℝ, (∀ t, 0 ≤ t → S t = NormedSpace.exp (t • A)) ∧
      ∀ x y, Tendsto (fun t => (S t x y - (1 : Matrix X X ℝ) x y) / t) (𝓝[>] 0) (𝓝 (A x y)) := by
  obtain ⟨h₀, hh₀, hW⟩ := h.exists_V_isUnit
  obtain ⟨A, hA⟩ : ∃ A, A = (S h₀ - 1) * (V S h₀)⁻¹ := ⟨_, rfl⟩
  set g : ℝ → Matrix X X ℝ := fun c => S c * NormedSpace.exp ((-c) • A)
  -- `g` has derivative zero on `(0, ∞)`
  have hg : ∀ c, 0 < c → ∀ x y, HasDerivAt (fun s => g s x y) 0 c := fun c hc x y => by
    have hp := hasDerivAt_mul_entry (M' := S c * A) (N' := -(A * NormedSpace.exp ((-c) • A)))
      (fun x y => by rw [hA]; exact h.hasDerivAt_entry hh₀ hW hc x y)
      (fun x y => hasDerivAt_exp_neg_smul_entry A c x y) x y
    convert hp using 1
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply]
  have hgcont : ∀ x y, ContinuousOn (fun s => g s x y) (Ici 0) := fun x y => by
    simp only [g, Matrix.mul_apply]
    refine continuousOn_finsetSum _ fun z _ => (h.continuousOn_entry x z).mul ?_
    exact (continuous_apply_apply z y |>.comp (continuous_exp_smul A |>.comp continuous_neg))
      |>.continuousOn
  have hg0 : g 0 = 1 := by simp [g, h.zero]
  have hgt : ∀ t, 0 ≤ t → g t = 1 := by
    intro t ht
    rcases ht.lt_or_eq with htpos | rfl
    · ext x y
      -- `g` is constant on `[ε, t]` for every `ε ∈ (0, t]`
      have hconst : ∀ᶠ ε in 𝓝[>] 0, g t x y = g ε x y := by
        filter_upwards [Ioo_mem_nhdsGT htpos] with ε hε
        have hc := constant_of_has_deriv_right_zero (a := ε) (b := t) ((hgcont x y).mono fun s hs =>
          le_trans hε.1.le hs.1) fun s hs => (hg s (lt_of_lt_of_le hε.1 hs.1) x y).hasDerivWithinAt
        exact hc t ⟨hε.2.le, le_rfl⟩
      have hlim : Tendsto (fun ε => g ε x y) (𝓝[>] 0) (𝓝 (g 0 x y)) :=
        ((hgcont x y) 0 (Set.mem_Ici.2 le_rfl)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      have := tendsto_nhds_unique (tendsto_const_nhds.congr' hconst) hlim
      rw [this, hg0]
    · exact hg0
  have hS : ∀ t, 0 ≤ t → S t = NormedSpace.exp (t • A) := fun t ht => by
    have hinv : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
      have := exp_smul_mul_exp_neg_smul A (-t)
      rwa [neg_neg] at this
    calc S t = S t * (NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A)) := by
          rw [hinv, Matrix.mul_one]
      _ = g t * NormedSpace.exp (t • A) := by simp only [g, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • A) := by rw [hgt t ht, Matrix.one_mul]
  refine ⟨A, hS, fun x y => ?_⟩
  have hslope := (hasDerivAt_exp_smul_entry A 0 x y).tendsto_slope_zero_right
  rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, smul_eq_mul, hS t (le_of_lt ht), div_eq_inv_mul]

end IsC0Semigroup

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Intensity matrices and Markov semigroups

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.3 (pp. 318–322).

`Q` is an intensity matrix (10.20) if `Q(x, x') ≥ 0` for `x ≠ x'` and every row sums to zero.

* Example 10.1.4.
* **Proposition 10.1.7**: for `P_t = e^{tQ}`, (i) `Q` is an intensity matrix, (ii) every `P_t`,
  `t ≥ 0`, is stochastic, and (iii) the distributions are invariant for `ψ̇ = ψQ`, are equivalent;
  with Exercises 10.1.13 (`P_t 1 = 1`), 10.1.14 (`Q = θ(K − I)` with `K` stochastic), 10.1.15
  (`P_t ≥ 0`), 10.1.16 and 10.1.17 (the converse, by differentiating at `t = 0`).
* Exercise 10.1.18: `(P_h − I)/h` is an intensity matrix; Exercise 10.1.19:
  `P_h(x, x') = hQ(x, x') + o(h)` for `x ≠ x'`.
* The Chapman–Kolmogorov equation (10.29), the Kolmogorov backward and forward equations, and
  **Proposition 10.1.8**: a differentiable `t ↦ P_t` with `P₀ = I` solving either equation is
  `e^{tQ}`.
-/

open Finset Matrix Filter Topology Function Set Asymptotics

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `Q` is an intensity matrix (10.20): nonnegative off the diagonal, with zero row sums. -/
def IsIntensity (Q : Matrix X X ℝ) : Prop :=
  (∀ x x', x ≠ x' → 0 ≤ Q x x') ∧ ∀ x, ∑ x', Q x x' = 0

omit [Fintype X] [DecidableEq X] in
/-- **Example 10.1.4** (p. 319). -/
theorem isIntensity_example :
    IsIntensity (!![-2, 1, 1; 0, -1, 1; 2, 1, -3] : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · fin_cases x <;> fin_cases x' <;> simp_all
  · fin_cases x <;> simp [Fin.sum_univ_three] <;> norm_num

/-- An entrywise nonnegative matrix has an entrywise nonnegative exponential. -/
theorem exp_nonneg_of_nonneg {M : Matrix X X ℝ} (hM : ∀ x y, 0 ≤ M x y) (x y : X) :
    0 ≤ NormedSpace.exp M x y := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M).mapL (entryCLM x y)
  exact h.nonneg fun n => mul_nonneg (by positivity) (pow_nonneg_entries hM n x y)

/-- `e^{cI} = e^c I`. -/
theorem exp_smul_one (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix X X ℝ)) = Real.exp c • (1 : Matrix X X ℝ) := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  rw [Algebra.smul_def, mul_one, show NormedSpace.exp (algebraMap ℝ (Matrix X X ℝ) c) =
    algebraMap ℝ _ (NormedSpace.exp c) from (NormedSpace.algebraMap_exp_comm c).symm,
    Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]

/-- **Exercise 10.1.13** (p. 320): for an intensity matrix, `P_t 1 = 1`. -/
theorem exp_smul_mulVec_one {Q : Matrix X X ℝ} (hQ : IsIntensity Q) (t : ℝ) :
    NormedSpace.exp (t • Q) *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h : (t • Q) *ᵥ (fun _ => (1 : ℝ)) = (0 : ℝ) • fun _ => 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, ← Finset.mul_sum, hQ.2 x]
  rw [exp_mulVec_of_eigen_real h, Real.exp_zero, one_smul]

/-- The `θ` of Exercise 10.1.14: the largest `|Q(x, x)|`. -/
noncomputable def intensityBound [Nonempty X] (Q : Matrix X X ℝ) : ℝ :=
  univ.sup' univ_nonempty fun x => |Q x x|

/-- The stochastic matrix `K = I + Q/θ` of Exercise 10.1.14 (`K = I` if `θ = 0`). -/
noncomputable def intensityJump [Nonempty X] (Q : Matrix X X ℝ) : Matrix X X ℝ :=
  if intensityBound Q = 0 then 1 else 1 + (intensityBound Q)⁻¹ • Q

/-- **Exercise 10.1.14** (p. 320): `K` is stochastic and `Q = θ(K − I)`. -/
theorem intensityJump_spec [Nonempty X] {Q : Matrix X X ℝ} (hQ : IsIntensity Q) :
    IsMarkov (intensityJump Q) ∧ Q = intensityBound Q • (intensityJump Q - 1) := by
  have hθ0 : 0 ≤ intensityBound Q := (abs_nonneg _).trans (Finset.le_sup' (fun x => |Q x x|)
    (mem_univ (Classical.arbitrary X)))
  have hdiag : ∀ x, |Q x x| ≤ intensityBound Q := fun x =>
    Finset.le_sup' (fun x => |Q x x|) (mem_univ x)
  by_cases hθ : intensityBound Q = 0
  · -- every diagonal entry vanishes, so every row vanishes
    have hQ0 : Q = 0 := by
      ext x x'
      have hxx : Q x x = 0 := abs_eq_zero.1 (le_antisymm (hθ ▸ hdiag x) (abs_nonneg _))
      have hrow := hQ.2 x
      rw [← Finset.add_sum_erase _ _ (mem_univ x), hxx, zero_add] at hrow
      by_cases hx : x = x'
      · subst hx
        exact hxx
      · exact le_antisymm ((Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
          hQ.1 x y (Finset.ne_of_mem_erase hy).symm).1 hrow x' (Finset.mem_erase.2
            ⟨Ne.symm hx, mem_univ _⟩)).le (hQ.1 x x' hx)
    have hJ : intensityJump Q = 1 := by simp [intensityJump, hθ]
    rw [hJ, hθ, zero_smul]
    refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, hQ0⟩
    · rw [Matrix.one_apply]
      split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  · have hθpos : 0 < intensityBound Q := lt_of_le_of_ne hθ0 (Ne.symm hθ)
    have hJ : intensityJump Q = 1 + (intensityBound Q)⁻¹ • Q := by simp [intensityJump, hθ]
    rw [hJ]
    refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, ?_⟩
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      by_cases hx : x = x'
      · subst hx
        simp only [↓reduceIte]
        have h2 : -intensityBound Q ≤ Q x x := by linarith [neg_abs_le (Q x x), hdiag x]
        have : -1 ≤ (intensityBound Q)⁻¹ * Q x x := by
          rw [le_inv_mul_iff₀ hθpos]
          linarith
        linarith
      · simp only [hx, ↓reduceIte, zero_add]
        exact mul_nonneg (inv_nonneg.2 hθ0) (hQ.1 x x' hx)
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hQ.2 x, mul_zero, add_zero]
      simp [Matrix.one_apply]
    · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hθ, one_smul]

/-- **Exercise 10.1.15** (p. 320): for an intensity matrix, `P_t ≥ 0` for `t ≥ 0`. -/
theorem exp_smul_nonneg [Nonempty X] {Q : Matrix X X ℝ} (hQ : IsIntensity Q) {t : ℝ} (ht : 0 ≤ t)
    (x y : X) : 0 ≤ NormedSpace.exp (t • Q) x y := by
  obtain ⟨hK, hQK⟩ := intensityJump_spec hQ
  set θ := intensityBound Q
  set K := intensityJump Q
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (Finset.le_sup' (fun x => |Q x x|)
    (mem_univ (Classical.arbitrary X)))
  have hsplit : t • Q = (t * θ) • K + (-(t * θ)) • (1 : Matrix X X ℝ) := by
    rw [hQK]
    module
  have hcomm : Commute ((t * θ) • K) ((-(t * θ)) • (1 : Matrix X X ℝ)) :=
    ((Commute.one_right K).smul_left _).smul_right _
  rw [hsplit, exp_add_eq hcomm, exp_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
    smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_nonneg_of_nonneg (fun a b => mul_nonneg
    (mul_nonneg ht hθ0) (hK.nonneg a b)) x y)

/-- **Proposition 10.1.7** (p. 319): for `P_t = e^{tQ}`, the following are equivalent:
(i) `Q` is an intensity matrix; (ii) `P_t` is stochastic for all `t ≥ 0`; (iii) the set of
distributions is invariant for `ψ̇ = ψQ`: `ψ₀ ∈ D(X) ⇒ ψ₀e^{tQ} ∈ D(X)` for all `t ≥ 0`. -/
theorem intensity_tfae [Nonempty X] (Q : Matrix X X ℝ) :
    [IsIntensity Q, ∀ t : ℝ, 0 ≤ t → IsMarkov (NormedSpace.exp (t • Q)),
      ∀ ψ : X → ℝ, IsDistribution ψ → ∀ t : ℝ, 0 ≤ t →
        IsDistribution (ψ ᵥ* NormedSpace.exp (t • Q))].TFAE := by
  tfae_have 1 → 2 := fun hQ t ht => ⟨exp_smul_nonneg hQ ht, fun x => by
    have := congrFun (exp_smul_mulVec_one hQ t) x
    simpa [Matrix.mulVec, dotProduct] using this⟩
  tfae_have 2 → 3 := fun hP ψ hψ t ht => by
    obtain ⟨h0, h1⟩ := hP t ht
    refine ⟨fun x' => sum_nonneg fun x _ => mul_nonneg (hψ.nonneg x) (h0 x x'), ?_⟩
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, h1, hψ.sum_eq_one]
  tfae_have 3 → 1 := by
    intro hinv
    -- row `x` of `P_t` is the distribution `δ_x P_t`
    have hrow : ∀ x, ∀ t : ℝ, 0 ≤ t → IsDistribution fun x' => NormedSpace.exp (t • Q) x x' :=
      fun x t ht => by
        have h := hinv (Pi.single x 1) ⟨fun y => by
          by_cases hy : y = x
          · subst hy; simp
          · simp [hy], by simp⟩ t ht
        have e : (Pi.single x 1 ᵥ* NormedSpace.exp (t • Q)) =
            fun x' => NormedSpace.exp (t • Q) x x' := by
          funext x'
          simp [Matrix.vecMul, dotProduct, Pi.single_apply]
        rwa [e] at h
    refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
    · -- Exercise 10.1.17: a nonnegative function vanishing at `0` has nonnegative right slope
      have hd := hasDerivAt_exp_smul_entry Q 0 x x'
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
      refine ge_of_tendsto hd.tendsto_slope_zero_right ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [zero_add, zero_smul, NormedSpace.exp_zero, Matrix.one_apply_ne hxx', sub_zero,
        smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 (le_of_lt ht)) ((hrow x t (le_of_lt ht)).nonneg x')
    · -- Exercise 10.1.16: the row sum is constant, so its derivative vanishes
      have hd := HasDerivAt.fun_sum (u := univ) fun x' _ => hasDerivAt_exp_smul_entry Q 0 x x'
      simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
      refine tendsto_nhds_unique hd.tendsto_slope_zero_right (tendsto_const_nhds.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [zero_add, zero_smul, NormedSpace.exp_zero, (hrow x t (le_of_lt ht)).sum_eq_one]
      simp [Matrix.one_apply]
  tfae_finish

/-- **Exercise 10.1.18** (p. 321): for `h > 0` and `P_h` stochastic, `(P_h − I)/h` is an intensity
matrix. -/
theorem isIntensity_of_isMarkov {P : Matrix X X ℝ} (hP : IsMarkov P) {h : ℝ} (hh : 0 < h) :
    IsIntensity (h⁻¹ • (P - 1)) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne hxx', sub_zero,
      smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hh.le) (hP.nonneg x x')
  · simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hP.rowsum x]
    rw [Finset.sum_eq_single x (fun y _ hy => by rw [Matrix.one_apply_ne' hy]) (by simp)]
    simp

/-- **Exercise 10.1.19** (p. 321), (10.28): `P_h(x, x') = hQ(x, x') + o(h)` for `x ≠ x'`. -/
theorem exp_smul_entry_isLittleO (Q : Matrix X X ℝ) {x x' : X} (hxx' : x ≠ x') :
    (fun h : ℝ => NormedSpace.exp (h • Q) x x' - h * Q x x') =o[𝓝 0] fun h => h := by
  have hd := hasDerivAt_exp_smul_entry Q 0 x x'
  rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at hd
  have h := hasDerivAt_iff_isLittleO.1 hd
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_apply_ne hxx', sub_zero,
    smul_eq_mul] at h
  exact h.congr_left fun h => by ring

/-- The Chapman–Kolmogorov equation (10.29): `P_{s+t}(x, x') = ∑_z P_s(x, z)P_t(z, x')`. -/
theorem chapman_kolmogorov (Q : Matrix X X ℝ) (s t : ℝ) (x x' : X) :
    NormedSpace.exp ((s + t) • Q) x x' =
      ∑ z, NormedSpace.exp (s • Q) x z * NormedSpace.exp (t • Q) z x' := by
  rw [exp_smul_add, Matrix.mul_apply]

/-- The Kolmogorov backward equation `Ṗ_t = QP_t`, entrywise. -/
theorem kolmogorov_backward (Q : Matrix X X ℝ) (t : ℝ) (x x' : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Q) x x') ((Q * NormedSpace.exp (t • Q)) x x') t :=
  hasDerivAt_exp_smul_entry Q t x x'

/-- The Kolmogorov forward equation `Ṗ_t = P_tQ`, entrywise. -/
theorem kolmogorov_forward (Q : Matrix X X ℝ) (t : ℝ) (x x' : X) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Q) x x')
      ((NormedSpace.exp (t • Q) * Q) x x') t := by
  rw [exp_smul_mul_comm]
  exact hasDerivAt_exp_smul_entry Q t x x'

omit [DecidableEq X] in
/-- Product rule for matrix products, entrywise, within a set. -/
theorem hasDerivWithinAt_mul_entry {M N : ℝ → Matrix X X ℝ} {M' N' : Matrix X X ℝ} {s : Set ℝ}
    {t : ℝ} (hM : ∀ x y, HasDerivWithinAt (fun r => M r x y) (M' x y) s t)
    (hN : ∀ x y, HasDerivWithinAt (fun r => N r x y) (N' x y) s t) (x y : X) :
    HasDerivWithinAt (fun r => (M r * N r) x y) ((M' * N t + M t * N') x y) s t := by
  have h := HasDerivWithinAt.fun_sum (u := univ) fun z _ => (hM x z).mul (hN z y)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  rw [← Finset.sum_add_distrib]

omit [Fintype X] in
/-- A matrix function with `g₀ = I`, continuous and with zero right derivative on `[0, ∞)`, is
constantly `I` there. -/
theorem eq_one_of_deriv_zero {g : ℝ → Matrix X X ℝ} (hg0 : g 0 = 1)
    (hg : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun r => g r x y) 0 (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : g t = 1 := by
  ext x y
  have hcont : ContinuousOn (fun r => g r x y) (Icc 0 t) := fun r hr =>
    ((hg r hr.1 x y).continuousWithinAt).mono fun s hs => hs.1
  have hc := constant_of_has_deriv_right_zero hcont fun r hr =>
    (hg r hr.1 x y).mono fun s hs => le_trans hr.1 hs
  rw [hc t ⟨ht, le_rfl⟩, hg0]

/-- **Proposition 10.1.8** (p. 322): if `t ↦ P_t` is differentiable on `[0, ∞)` with `P₀ = I` and
satisfies the backward equation `Ṗ_t = QP_t`, then `P_t = e^{tQ}`. -/
theorem eq_exp_of_backward {Q : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ} (hP0 : P 0 = 1)
    (hP : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun s => P s x y) ((Q * P t) x y) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • Q) := by
  have hg : ∀ r, 0 ≤ r → ∀ x y, HasDerivWithinAt
      (fun s => (NormedSpace.exp ((-s) • Q) * P s) x y) 0 (Ici 0) r := fun r hr x y => by
    have h := hasDerivWithinAt_mul_entry (M' := -(Q * NormedSpace.exp ((-r) • Q)))
      (N' := Q * P r) (fun a b => (hasDerivAt_exp_neg_smul_entry Q r a b).hasDerivWithinAt)
      (hP r hr) x y
    convert h using 1
    rw [Matrix.neg_mul, ← exp_smul_mul_comm, Matrix.mul_assoc, neg_add_cancel, Matrix.zero_apply]
  have h1 := eq_one_of_deriv_zero (g := fun s => NormedSpace.exp ((-s) • Q) * P s)
    (by simp [hP0]) hg ht
  calc P t = NormedSpace.exp (t • Q) * (NormedSpace.exp ((-t) • Q) * P t) := by
        rw [← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.one_mul]
    _ = NormedSpace.exp (t • Q) := by rw [h1, Matrix.mul_one]

/-- **Proposition 10.1.8** (p. 322): the same with the forward equation `Ṗ_t = P_tQ`. -/
theorem eq_exp_of_forward {Q : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ} (hP0 : P 0 = 1)
    (hP : ∀ t, 0 ≤ t → ∀ x y, HasDerivWithinAt (fun s => P s x y) ((P t * Q) x y) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • Q) := by
  have hg : ∀ r, 0 ≤ r → ∀ x y, HasDerivWithinAt
      (fun s => (P s * NormedSpace.exp ((-s) • Q)) x y) 0 (Ici 0) r := fun r hr x y => by
    have h := hasDerivWithinAt_mul_entry (M' := P r * Q)
      (N' := -(Q * NormedSpace.exp ((-r) • Q))) (hP r hr)
      (fun a b => (hasDerivAt_exp_neg_smul_entry Q r a b).hasDerivWithinAt) x y
    convert h using 1
    rw [Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply]
  have h1 := eq_one_of_deriv_zero (g := fun s => P s * NormedSpace.exp ((-s) • Q))
    (by simp [hP0]) hg ht
  have hinv : NormedSpace.exp ((-t) • Q) * NormedSpace.exp (t • Q) = 1 := by
    have := exp_smul_mul_exp_neg_smul Q (-t)
    rwa [neg_neg] at this
  calc P t = (P t * NormedSpace.exp ((-t) • Q)) * NormedSpace.exp (t • Q) := by
        rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = NormedSpace.exp (t • Q) := by rw [h1, Matrix.one_mul]

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Jump chains

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.1.4.2–§10.1.4.4 (pp. 323–329).

A jump chain is built from a rate function `λ : X → (0, ∞)` and a jump matrix `Π ∈ M(ℝ^X)`; its
intensity matrix is `Q(x, x') = λ(x)(Π(x, x') − I(x, x'))` (10.31).

* (10.31) is an intensity matrix; conversely (§10.1.4.4), an intensity matrix with nonzero rows is
  `λ(Π − I)` for `λ(x) = −Q(x, x)` and the stochastic `Π = I + Q/λ`.
* The integrated Kolmogorov backward equation: (10.32) and (10.36) are the same equation, by the
  change of variables `s = t − τ`.
* **Lemma 10.1.11**: a continuous solution of (10.32) has `P₀ = I` and `Ṗ_t = QP_t`; with
  Proposition 10.1.8 it is `e^{tQ}` (the analytic part of the proof of Proposition 10.1.9).
* Exercise 10.1.20: the inventory jump matrix (10.37) is stochastic.

Lemma 10.1.10, that the transition probabilities of the process built by Algorithm 10.1 satisfy
(10.32), is a statement about the law of a stochastic process and is not formalised (see
`docs/corrections.md`).
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The intensity matrix (10.31) of a jump chain: `Q(x, x') = λ(x)(Π(x, x') − I(x, x'))`. -/
def jumpIntensity (lam : X → ℝ) (J : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => lam x * (J x x' - (1 : Matrix X X ℝ) x x')

/-- (10.31) is an intensity matrix when `λ ≥ 0` and `Π` is stochastic (p. 324). -/
theorem isIntensity_jumpIntensity {lam : X → ℝ} (hlam : ∀ x, 0 ≤ lam x) {J : Matrix X X ℝ}
    (hJ : IsMarkov J) : IsIntensity (jumpIntensity lam J) := by
  refine ⟨fun x x' hxx' => ?_, fun x => ?_⟩
  · simp only [jumpIntensity, Matrix.of_apply, Matrix.one_apply_ne hxx', sub_zero]
    exact mul_nonneg (hlam x) (hJ.nonneg x x')
  · simp only [jumpIntensity, Matrix.of_apply, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hJ.rowsum x]
    simp [Matrix.one_apply]

/-- The jump matrix of an intensity matrix with nonzero rows (§10.1.4.4): `Π = I + Q/λ`,
`λ(x) = −Q(x, x)`. -/
noncomputable def intensityJumpChain (Q : Matrix X X ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => (1 : Matrix X X ℝ) x x' + Q x x' / (-Q x x)

/-- §10.1.4.4 (p. 327): if `Q` is an intensity matrix with `Q(x, x) < 0` for all `x`, then
`Π = I + Q/λ` is stochastic and `Q = λ(Π − I)` with `λ(x) = −Q(x, x) > 0`. -/
theorem intensityJumpChain_spec {Q : Matrix X X ℝ} (hQ : IsIntensity Q) (hdiag : ∀ x, Q x x < 0) :
    IsMarkov (intensityJumpChain Q) ∧
      Q = jumpIntensity (fun x => -Q x x) (intensityJumpChain Q) := by
  have hlam : ∀ x, 0 < -Q x x := fun x => neg_pos.2 (hdiag x)
  refine ⟨⟨fun x x' => ?_, fun x => ?_⟩, ?_⟩
  · simp only [intensityJumpChain, Matrix.of_apply, Matrix.one_apply]
    by_cases hx : x = x'
    · subst hx
      simp only [↓reduceIte]
      rw [div_neg, div_self (hdiag x).ne]
      norm_num
    · simp only [hx, ↓reduceIte, zero_add]
      exact div_nonneg (hQ.1 x x' hx) (hlam x).le
  · simp only [intensityJumpChain, Matrix.of_apply, Finset.sum_add_distrib, ← Finset.sum_div,
      hQ.2 x, zero_div, add_zero]
    simp [Matrix.one_apply]
  · ext x x'
    simp only [jumpIntensity, intensityJumpChain, Matrix.of_apply, add_sub_cancel_left]
    field_simp [(hlam x).ne']
    rw [mul_div_assoc, div_self (hdiag x).ne, mul_one]

/-- The integrated backward equations (10.32) and (10.36) agree, by `s = t − τ`. -/
theorem integral_backward_eq (f : ℝ → ℝ) (c t : ℝ) :
    Real.exp (-t * c) * (∫ s in (0 : ℝ)..t, f s * Real.exp (s * c)) =
      ∫ τ in (0 : ℝ)..t, f (t - τ) * Real.exp (-τ * c) := by
  have h := intervalIntegral.integral_comp_sub_left (fun s => f s * Real.exp (s * c)) (a := 0)
    (b := t) t
  simp only [sub_self, sub_zero] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

omit [DecidableEq X] in
/-- The fundamental theorem of calculus on `[0, ∞)`: for `f` continuous on `[0, ∞)`,
`u ↦ ∫₀^u f` has derivative `f(t)` within `[0, ∞)` at every `t ≥ 0`. -/
theorem hasDerivWithinAt_integral_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, f s) (f t) (Ici 0) t := by
  have hint : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono fun s hs => le_trans (le_min le_rfl ht) hs.1).intervalIntegrable
  rcases ht.lt_or_eq with htpos | rfl
  · exact (intervalIntegral.integral_hasDerivAt_right hint
      ((hf.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t htpos)
      (hf.continuousAt (Ici_mem_nhds htpos))).hasDerivWithinAt
  · exact intervalIntegral.integral_hasDerivWithinAt_right hint
      ((hf.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0)
      ((hf 0 (Set.mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self)

/-- **Lemma 10.1.11** (p. 325): if the entries of `t ↦ P_t` are continuous on `[0, ∞)` and satisfy
the integrated Kolmogorov backward equation (10.32), then `P₀ = I` and `Ṗ_t = QP_t` on `[0, ∞)`,
for `Q = λ(Π − I)`. -/
theorem backward_of_integrated {lam : X → ℝ} {J : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ}
    (hcont : ∀ x x', ContinuousOn (fun t => P t x x') (Ici 0))
    (hint : ∀ t, 0 ≤ t → ∀ x x', P t x x' = Real.exp (-t * lam x) * (1 : Matrix X X ℝ) x x' +
      lam x * ∫ τ in (0 : ℝ)..t, (J * P (t - τ)) x x' * Real.exp (-τ * lam x)) :
    P 0 = 1 ∧ ∀ t, 0 ≤ t → ∀ x x', HasDerivWithinAt (fun s => P s x x')
      ((jumpIntensity lam J * P t) x x') (Ici 0) t := by
  refine ⟨?_, fun t ht x x' => ?_⟩
  · ext x x'
    rw [hint 0 le_rfl]
    simp
  -- rewrite (10.32) as (10.36)
  set h : ℝ → ℝ := fun s => (J * P s) x x' * Real.exp (s * lam x)
  have h36 : ∀ s, 0 ≤ s → P s x x' = Real.exp (-s * lam x) *
      ((1 : Matrix X X ℝ) x x' + lam x * ∫ σ in (0 : ℝ)..s, h σ) := fun s hs => by
    rw [hint s hs x x', mul_add, mul_left_comm (Real.exp _), integral_backward_eq]
  have hhcont : ContinuousOn h (Ici 0) := by
    refine ContinuousOn.mul ?_
      (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn
    simp only [Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun z _ => continuousOn_const.mul (hcont z x')
  have hG := hasDerivWithinAt_integral_Ici hhcont ht
  have hE : HasDerivWithinAt (fun s => Real.exp (-s * lam x)) (-lam x * Real.exp (-t * lam x))
      (Ici 0) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s * lam x) (-lam x) t := by
      simpa using (hasDerivAt_id t).neg.mul_const (lam x)
    exact (h1.exp.congr_deriv (by ring)).hasDerivWithinAt
  have hF := hE.mul ((hG.const_mul (lam x)).const_add ((1 : Matrix X X ℝ) x x'))
  refine (hF.congr (fun s hs => h36 s hs) (h36 t ht)).congr_deriv ?_
  -- `−λP_t + λ(ΠP_t) = (λ(Π − I)P_t)(x, x')`
  have hexp : Real.exp (-t * lam x) * Real.exp (t * lam x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hR : ∑ j, lam x * (J x j - (1 : Matrix X X ℝ) x j) * P t j x' =
      lam x * ∑ j, J x j * P t j x' - lam x * P t x x' := by
    have e1 : ∑ j, lam x * (J x j - (1 : Matrix X X ℝ) x j) * P t j x' =
        ∑ j, lam x * (J x j * P t j x') - ∑ j, lam x * ((1 : Matrix X X ℝ) x j * P t j x') := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_eq_single (f := fun j => (1 : Matrix X X ℝ) x j * P t j x') x
      (fun j _ hj => by rw [Matrix.one_apply_ne' hj, zero_mul]) (by simp), Matrix.one_apply_eq,
      one_mul]
  have h36t := h36 t ht
  simp only [h, Matrix.mul_apply] at h36t
  simp only [h, jumpIntensity, Matrix.mul_apply, Matrix.of_apply]
  rw [hR]
  linear_combination (lam x * ∑ j, J x j * P t j x') * hexp + lam x * h36t

/-- **Proposition 10.1.9**, analytic part (p. 324): a continuous solution of the integrated backward
equation (10.32) is the Markov semigroup `P_t = e^{tQ}` with `Q = λ(Π − I)`. -/
theorem eq_exp_of_integrated {lam : X → ℝ} {J : Matrix X X ℝ} {P : ℝ → Matrix X X ℝ}
    (hcont : ∀ x x', ContinuousOn (fun t => P t x x') (Ici 0))
    (hint : ∀ t, 0 ≤ t → ∀ x x', P t x x' = Real.exp (-t * lam x) * (1 : Matrix X X ℝ) x x' +
      lam x * ∫ τ in (0 : ℝ)..t, (J * P (t - τ)) x x' * Real.exp (-τ * lam x))
    {t : ℝ} (ht : 0 ≤ t) : P t = NormedSpace.exp (t • jumpIntensity lam J) := by
  obtain ⟨h0, hd⟩ := backward_of_integrated hcont hint
  exact eq_exp_of_backward h0 hd ht

/-! ### Inventory dynamics (§10.1.4.3) -/

/-- The inventory jump matrix (10.37) on `X = {0, …, b}`: from `0` the firm restocks to `b`;
from `0 < x ≤ b` inventory falls to `x − U ∧ x`, where `P{U = k} = φ(k)`, `k ≥ 1`. -/
noncomputable def inventoryJump (b : ℕ) (φ : ℕ → ℝ) (x y : Fin (b + 1)) : ℝ :=
  if (x : ℕ) = 0 then (if (y : ℕ) = b then 1 else 0)
  else if (x : ℕ) ≤ y then 0
  else if 0 < (y : ℕ) then φ (x - y)
  else 1 - ∑ k ∈ range x, φ k

/-- **Exercise 10.1.20** (p. 326): for a distribution `φ` of `U` on `{1, 2, …}`, the inventory jump
matrix `Π` is stochastic. -/
theorem isMarkov_inventoryJump (b : ℕ) {φ : ℕ → ℝ} (hφ0 : φ 0 = 0) (hφ : ∀ k, 0 ≤ φ k)
    (hsum : HasSum φ 1) : IsMarkov (Matrix.of (inventoryJump b φ)) := by
  have hS : ∀ n, ∑ k ∈ range n, φ k ≤ 1 := fun n =>
    sum_le_hasSum (range n) (fun k _ => hφ k) hsum
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [Matrix.of_apply, inventoryJump]
    split_ifs <;> first | exact hφ _ | linarith [hS x]
  · simp only [Matrix.of_apply, inventoryJump]
    rw [Fin.sum_univ_eq_sum_range (fun y => if (x : ℕ) = 0 then (if y = b then 1 else 0)
      else if (x : ℕ) ≤ y then 0 else if 0 < y then φ (x - y) else 1 - ∑ k ∈ range x, φ k) (b + 1)]
    by_cases hx : (x : ℕ) = 0
    · simp [hx]
    · have hxb : (x : ℕ) ≤ b := Nat.lt_succ_iff.1 x.2
      have hsplit : ∀ y, (if (x : ℕ) = 0 then (if y = b then (1 : ℝ) else 0)
          else if (x : ℕ) ≤ y then 0 else if 0 < y then φ (x - y)
          else 1 - ∑ k ∈ range x, φ k) =
          (if y = 0 then 1 - ∑ k ∈ range x, φ k else 0) +
            (if y ∈ Finset.Ico 1 (x : ℕ) then φ (x - y) else 0) := fun y => by
        simp only [hx, ↓reduceIte, Finset.mem_Ico]
        by_cases hy0 : y = 0
        · subst hy0
          have : ¬ (x : ℕ) ≤ 0 := by omega
          simp [this]
        · by_cases hxy : (x : ℕ) ≤ y
          · simp [hxy, hy0]
          · simp [hxy, hy0, show y < (x : ℕ) by omega, Nat.pos_of_ne_zero hy0]
      simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
        show 0 < b + 1 by omega, ↓reduceIte]
      rw [← Finset.sum_filter, show (Finset.range (b + 1)).filter (· ∈ Finset.Ico 1 (x : ℕ)) =
          Finset.Ico 1 (x : ℕ) by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega]
      rw [Finset.sum_Ico_reflect φ 1 (show (x : ℕ) ≤ x + 1 by omega)]
      rw [show (x : ℕ) + 1 - x = 1 by omega, show (x : ℕ) + 1 - 1 = x by omega,
        Finset.sum_range_eq_add_Ico φ (Nat.pos_of_ne_zero hx), hφ0, zero_add]
      ring

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Valuation in continuous time

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.2.1 (pp. 329–334).

For a positive exponential semigroup `K_t = e^{tA}` and a reward `h`, lifetime value is
`v = ∫₀^∞ K_t h dt` (10.38).

* **Proposition 10.2.1**: if `s(A) < 0` then (i) the integral is finite and
  `v = ∫₀^t K_τ h dτ + K_t v` (10.39); (ii) `A` is invertible and `v = −A⁻¹h`; (iii) `A⁻¹ ≤ 0`; and
  (iv) `Uw = h + (I + A)w` is order stable with unique fixed point `v`. Here `Av = −h` comes from
  the improper fundamental theorem of calculus, `∫₀^∞ (d/dt) e^{tA}h dt = −h`.
* Exercise 10.2.1: the path discount `η(s, t) = exp(−∫_s^t δ(X_τ) dτ)` is positive, `η(s, s) = 1`
  and `η(0, s + t) = η(0, s)η(s, s + t)`.
* **Proposition 10.2.3**: for an intensity matrix `Q` and `δ > 0`, `s(Q − δI) = −δ`, so
  `δI − Q` is invertible with `(δI − Q)⁻¹ ≥ 0`, `v = (δI − Q)⁻¹h`, and
  `Uw = h + (Q + (1 − δ)I)w` is order stable with unique fixed point `v`.

Proposition 10.2.2 (the Feynman–Kac semigroup of a continuous-time Markov chain) and the
interchange of expectation and integration in (10.44) concern the law of the chain and are not
formalised; Proposition 10.2.3 takes the semigroup form `v = ∫₀^∞ e^{−δt}P_t h dt` as the
definition of lifetime value.
-/

open Finset Matrix Filter Topology Function Set MeasureTheory

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `t ↦ e^{tA}h` is continuous. -/
theorem continuous_exp_smul_mulVec (A : Matrix X X ℝ) (h : X → ℝ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h :=
  (continuous_exp_smul A).matrix_mulVec continuous_const

/-- `v ↦ Mv` as a continuous linear map. -/
noncomputable def mulVecLinCLM (M : Matrix X X ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

/-- The coordinate map `f ↦ f(x)` as a continuous linear map. -/
noncomputable def projCLM (x : X) : (X → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.proj x)

/-- Lifetime value (10.38): `v = ∫₀^∞ e^{tA}h dt`. -/
noncomputable def lifetimeValue (A : Matrix X X ℝ) (h : X → ℝ) : X → ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), NormedSpace.exp (t • A) *ᵥ h

variable [Nonempty X]

/-- **Proposition 10.2.1 (i)** (p. 329): for `s(A) < 0`, `t ↦ e^{tA}h` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_mulVec {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    IntegrableOn (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h) (Ioi 0) := by
  have h4' : ∀ p : ℝ, 1 ≤ p → ∀ u₀ : X → ℝ, IntegrableOn
      (fun t : ℝ => ‖NormedSpace.exp (t • A) *ᵥ u₀‖ ^ p) (Set.Ioi 0) :=
    ((stability_tfae A).out 1 4).1 hs
  have h4 := h4' 1 le_rfl h
  simp only [Real.rpow_one] at h4
  exact (integrable_norm_iff (continuous_exp_smul_mulVec A h).aestronglyMeasurable).1 h4

omit [Nonempty X] in
/-- A matrix with negative spectral bound is invertible: `0` is not an eigenvalue. -/
theorem isUnit_of_spectralBound_neg {A : Matrix X X ℝ} (hs : spectralBound A < 0) : IsUnit A := by
  have h0 : (0 : ℂ) ∉ spectrum ℂ (complexify A) := fun h0 => by
    have := re_le_spectralBound h0
    simp only [Complex.zero_re] at this
    linarith
  rw [spectrum.notMem_iff, map_zero, zero_sub, IsUnit.neg_iff] at h0
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 h0
  have e : (complexify A).det = ((A.det : ℝ) : ℂ) := (Complex.ofRealHom.map_det A).symm
  rw [e] at hdet
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun hz => ?_)
  rw [hz, Complex.ofReal_zero] at hdet
  exact not_isUnit_zero hdet

/-- **Proposition 10.2.1 (ii)** (p. 329): for `s(A) < 0`, `Av = −h`. -/
theorem mulVec_lifetimeValue {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    A *ᵥ lifetimeValue A h = -h := by
  have hcomm : ∀ t : ℝ, A *ᵥ (NormedSpace.exp (t • A) *ᵥ h) = NormedSpace.exp (t • A) *ᵥ (A *ᵥ h) :=
    fun t => by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_smul_mul_comm]
  have hlim : Tendsto (fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖) atTop (𝓝 0) :=
      ((stability_tfae A).out 1 2).1 hs
    refine squeeze_zero (fun _ => norm_nonneg _) (fun t => Matrix.linfty_opNorm_mulVec _ _) ?_
    simpa using h2.mul_const ‖h‖
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => NormedSpace.exp (t • A) *ᵥ h)
    (f' := fun t => A *ᵥ (NormedSpace.exp (t • A) *ᵥ h))
    (continuous_exp_smul_mulVec A h).continuousWithinAt
    (fun t _ => hasDerivAt_exp_smul_mulVec A h t)
    (by simp_rw [hcomm]; exact integrableOn_exp_mulVec hs (A *ᵥ h)) hlim
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, zero_sub] at hftc
  rw [← hftc, lifetimeValue]
  exact ((mulVecLinCLM A).integral_comp_comm (integrableOn_exp_mulVec hs h)).symm

/-- **Proposition 10.2.1 (ii)** (p. 329): for `s(A) < 0`, `A` is invertible and `v = −A⁻¹h`. -/
theorem lifetimeValue_eq {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ) :
    IsUnit A ∧ lifetimeValue A h = -(A⁻¹ *ᵥ h) := by
  have hA := isUnit_of_spectralBound_neg hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  refine ⟨hA, ?_⟩
  rw [← mulVec_neg, ← mulVec_lifetimeValue hs h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **Proposition 10.2.1 (i)** (p. 329), (10.39): `v = ∫₀^t K_τ h dτ + K_t v` for `t ≥ 0`. -/
theorem lifetimeValue_eq_integral_add {A : Matrix X X ℝ} (hs : spectralBound A < 0) (h : X → ℝ)
    (t : ℝ) :
    lifetimeValue A h = (∫ τ in (0 : ℝ)..t, NormedSpace.exp (τ • A) *ᵥ h) +
      NormedSpace.exp (t • A) *ᵥ lifetimeValue A h := by
  set v := lifetimeValue A h
  have hv : A *ᵥ v = -h := mulVec_lifetimeValue hs h
  have hint : ∀ τ : ℝ, NormedSpace.exp (τ • A) *ᵥ h =
      -(A *ᵥ (NormedSpace.exp (τ • A) *ᵥ v)) := fun τ => by
    rw [Matrix.mulVec_mulVec, ← exp_smul_mul_comm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_neg,
      neg_neg]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => NormedSpace.exp (τ • A) *ᵥ v)
    (f' := fun τ => A *ᵥ (NormedSpace.exp (τ • A) *ᵥ v)) (a := 0) (b := t)
    (fun τ _ => hasDerivAt_exp_smul_mulVec A v τ)
    ((continuous_const.matrix_mulVec (continuous_exp_smul_mulVec A v)).intervalIntegrable _ _)
  simp_rw [hint]
  rw [intervalIntegral.integral_neg, hftc]
  simp

/-- **Proposition 10.2.1 (iii)** (p. 329): if moreover `e^{tA} ≥ 0` for `t ≥ 0`, then `A⁻¹ ≤ 0`
entrywise. -/
theorem inv_nonpos {A : Matrix X X ℝ} (hs : spectralBound A < 0)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y) (x y : X) :
    A⁻¹ x y ≤ 0 := by
  have hval := (lifetimeValue_eq hs (Pi.single y 1)).2
  have hnn : 0 ≤ lifetimeValue A (Pi.single y 1) x := by
    rw [lifetimeValue, show (∫ t in Set.Ioi (0 : ℝ), NormedSpace.exp (t • A) *ᵥ Pi.single y 1) x =
      ∫ t in Set.Ioi (0 : ℝ), (NormedSpace.exp (t • A) *ᵥ Pi.single y 1) x from
      ((projCLM x).integral_comp_comm (integrableOn_exp_mulVec hs _)).symm]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact hpos t (le_of_lt ht) x y
  rw [hval] at hnn
  simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hnn
  linarith

omit [Nonempty X] in
/-- `−A⁻¹` is a positive operator when `A⁻¹ ≤ 0`. -/
theorem neg_inv_mulVec_nonneg {A : Matrix X X ℝ} (hA : ∀ x y, A⁻¹ x y ≤ 0) {f : X → ℝ}
    (hf : 0 ≤ f) : 0 ≤ -(A⁻¹ *ᵥ f) := fun x => by
  simp only [Pi.neg_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, neg_nonneg]
  exact Finset.sum_nonpos fun y _ => mul_nonpos_of_nonpos_of_nonneg (hA x y) (hf y)

/-- **Proposition 10.2.1 (iv)** (p. 330): `Uw = h + (I + A)w` is order stable on `ℝ^X`, with unique
fixed point `v`. -/
theorem orderStable_valuation {A : Matrix X X ℝ} (hs : spectralBound A < 0)
    (hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y) (h : X → ℝ) :
    OrderStable (fun w => h + (1 + A) *ᵥ w) ∧ IsFixedPt (fun w => h + (1 + A) *ᵥ w)
      (lifetimeValue A h) := by
  obtain ⟨hA, hv⟩ := lifetimeValue_eq hs h
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have hneg := inv_nonpos hs hpos
  have hfix : IsFixedPt (fun w => h + (1 + A) *ᵥ w) (lifetimeValue A h) := by
    change h + (1 + A) *ᵥ lifetimeValue A h = lifetimeValue A h
    rw [Matrix.add_mulVec, Matrix.one_mulVec, mulVec_lifetimeValue hs h]
    abel
  -- `v − w = −A⁻¹(h + Aw)`
  have key : ∀ w, lifetimeValue A h - w = -(A⁻¹ *ᵥ (h + A *ᵥ w)) := fun w => by
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
    abel
  refine ⟨orderStable_of_up_down hfix (fun w hw => ?_) (fun w hw => ?_), hfix⟩
  · have hw' : 0 ≤ h + A *ᵥ w := fun x => by
      have := hw x
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply] at this
      simp only [Pi.add_apply, Pi.zero_apply]
      linarith
    have := neg_inv_mulVec_nonneg hneg hw'
    rw [← key] at this
    exact sub_nonneg.1 this
  · have hw' : 0 ≤ -(h + A *ᵥ w) := fun x => by
      have := hw x
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply] at this
      simp only [Pi.neg_apply, Pi.add_apply, Pi.zero_apply]
      linarith
    have := neg_inv_mulVec_nonneg hneg hw'
    rw [Matrix.mulVec_neg, neg_neg, ← neg_neg (A⁻¹ *ᵥ (h + A *ᵥ w)), ← key] at this
    intro x
    have := this x
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at this
    linarith

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- **Exercise 10.2.1** (p. 332): along a path `τ ↦ X_τ` with `τ ↦ δ(X_τ)` locally integrable,
`η(s, t) = exp(−∫_s^t δ(X_τ) dτ)` satisfies (i) `η > 0`, (ii) `η(s, s) = 1` and
(iii) `η(0, s + t) = η(0, s)η(s, s + t)`. -/
theorem pathDiscount_properties {S : Type*} (path : ℝ → S) (δ : S → ℝ)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun τ => δ (path τ)) volume a b) (s t : ℝ) :
    0 < Real.exp (-∫ τ in s..t, δ (path τ)) ∧ Real.exp (-∫ τ in s..s, δ (path τ)) = 1 ∧
      Real.exp (-∫ τ in (0 : ℝ)..s + t, δ (path τ)) =
        Real.exp (-∫ τ in (0 : ℝ)..s, δ (path τ)) * Real.exp (-∫ τ in s..s + t, δ (path τ)) := by
  refine ⟨Real.exp_pos _, by simp, ?_⟩
  rw [← Real.exp_add,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + t))]
  ring_nf

omit [Nonempty X] in
/-- `e^{t(Q − δI)} = e^{−tδ}e^{tQ}`. -/
theorem exp_smul_sub_smul_one (Q : Matrix X X ℝ) (δ t : ℝ) :
    NormedSpace.exp (t • (Q - δ • (1 : Matrix X X ℝ))) =
      Real.exp (-(t * δ)) • NormedSpace.exp (t • Q) := by
  have hsplit : t • (Q - δ • (1 : Matrix X X ℝ)) = t • Q + (-(t * δ)) • (1 : Matrix X X ℝ) := by
    module
  rw [hsplit, exp_add_eq (((Commute.one_right Q).smul_left t).smul_right _), exp_smul_one,
    Matrix.mul_smul, Matrix.mul_one]

/-- **Proposition 10.2.3** (p. 333): for an intensity matrix `Q` and `δ > 0`, `s(Q − δI) = −δ`;
`δI − Q` is invertible with `(δI − Q)⁻¹ ≥ 0`; lifetime value `v = ∫₀^∞ e^{−δt}P_t h dt` equals
`(δI − Q)⁻¹h`; and `Uw = h + (Q + (1 − δ)I)w` is order stable with unique fixed point `v`. -/
theorem constant_discounting {Q : Matrix X X ℝ} (hQ : IsIntensity Q) {δ : ℝ} (hδ : 0 < δ)
    (h : X → ℝ) :
    spectralBound (Q - δ • 1) = -δ ∧ IsUnit (δ • (1 : Matrix X X ℝ) - Q) ∧
      (∀ x y, 0 ≤ (δ • (1 : Matrix X X ℝ) - Q)⁻¹ x y) ∧
      lifetimeValue (Q - δ • 1) h = (δ • (1 : Matrix X X ℝ) - Q)⁻¹ *ᵥ h ∧
      OrderStable (fun w => h + (Q + (1 - δ) • (1 : Matrix X X ℝ)) *ᵥ w) ∧
      IsFixedPt (fun w => h + (Q + (1 - δ) • (1 : Matrix X X ℝ)) *ᵥ w)
        (lifetimeValue (Q - δ • 1) h) := by
  set A := Q - δ • (1 : Matrix X X ℝ)
  have hmarkov := ((intensity_tfae Q).out 1 2).1 hQ
  -- `s(A) = −δ`
  have hs : spectralBound A = -δ := by
    have h1 := specRad_exp A
    have hexpA : NormedSpace.exp A = Real.exp (-δ) • NormedSpace.exp Q := by
      have := exp_smul_sub_smul_one Q δ 1
      simpa only [one_smul, one_mul] using this
    have hm1 : IsMarkov (NormedSpace.exp Q) := by
      have := hmarkov 1 zero_le_one
      rwa [one_smul] at this
    rw [hexpA, specRad_smul_isMarkov hm1 (Real.exp_pos _).le] at h1
    exact (Real.exp_injective h1).symm
  have hsneg : spectralBound A < 0 := by rw [hs]; linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ x y, 0 ≤ NormedSpace.exp (t • A) x y := fun t ht x y => by
    rw [exp_smul_sub_smul_one, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (Real.exp_pos _).le (exp_smul_nonneg hQ ht x y)
  obtain ⟨hA, hv⟩ := lifetimeValue_eq hsneg h
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have hnegA : δ • (1 : Matrix X X ℝ) - Q = -A := by simp [A]
  have hinv : (δ • (1 : Matrix X X ℝ) - Q)⁻¹ = -A⁻¹ := by
    rw [hnegA]
    exact Matrix.inv_eq_right_inv (by rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hdet])
  have hU : Q + (1 - δ) • (1 : Matrix X X ℝ) = 1 + A := by
    simp only [A]
    module
  obtain ⟨hos, hfix⟩ := orderStable_valuation hsneg hpos h
  refine ⟨hs, by rw [hnegA]; exact hA.neg, fun x y => ?_, ?_, by rw [hU]; exact hos,
    by rw [hU]; exact hfix⟩
  · rw [hinv, Matrix.neg_apply]
    exact neg_nonneg.2 (inv_nonpos hsneg hpos x y)
  · rw [hv, hinv, Matrix.neg_mulVec]

end SargentStachurski.ContinuousTime

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous-time Markov decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §10.2.2–§10.2.4 (pp. 334–339).

A continuous-time MDP `C = (Γ, δ, r, Q)` has a nonempty feasible correspondence `Γ`, a discount
rate `δ > 0`, a flow reward `r` and an intensity kernel `Q` on the feasible state-action pairs.

* (10.49): the `σ`-value function `v_σ = ∫₀^∞ e^{−δt}P^σ_t r_σ dt` equals `(δI − Q_σ)⁻¹r_σ`.
* (10.51): the policy operators `T_σ v = r_σ + (Q_σ + (1 − δ)I)v` form an order stable ADP.
* **Exercise 10.2.2**: `σ` is `v`-greedy in the sense of (10.50) iff it is `v`-greedy for the ADP.
* (10.53): the Bellman operator of the ADP.
* **Theorem 10.2.4**: `v*` is the unique solution of the HJB equation (10.52), Bellman's
  principle of optimality holds, an optimal policy exists, and continuous-time HPI
  (Algorithm 10.2) stops, `σₖ₊₁ = σₖ`, at an optimal policy after finitely many steps.
* §10.2.4 (job search): **Exercise 10.2.3** (the jump probabilities `Π` are a stochastic kernel),
  `Q_σ = λ(Π_σ − I)` is an intensity matrix, and Theorem 10.2.4 applies.
-/

open Finset Matrix Function Set

namespace SargentStachurski.ContinuousTime

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A continuous-time MDP `C = (Γ, δ, r, Q)` (§10.2.2.1, p. 334). The reward and the kernel are
given on all of `X × A`; only their values on `G = {(x, a) : a ∈ Γ(x)}` matter. -/
structure CTMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the discount rate -/
  δ : ℝ
  δ_pos : 0 < δ
  /-- the flow reward -/
  r : X → A → ℝ
  /-- the intensity kernel -/
  Q : X → A → X → ℝ
  Q_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', x ≠ x' → 0 ≤ Q x a x'
  Q_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', Q x a x' = 0

namespace CTMDP

variable {X A : Type*} [Fintype X] (C : CTMDP X A)

/-- The feasible policies `Σ = {σ ∈ A^X : σ(x) ∈ Γ(x)}` (10.47). -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ C.Γ x}

/-- `Σ` is nonempty. -/
theorem nonempty_policy : Nonempty C.Policy :=
  ⟨⟨fun x => (C.Γ_nonempty x).choose, fun x => (C.Γ_nonempty x).choose_spec⟩⟩

/-- `Q_σ(x, x') = Q(x, σ(x), x')`. -/
def Qσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => C.Q x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => C.r x (σ x)

/-- `Q_σ` is an intensity matrix for every feasible `σ`. -/
theorem isIntensity_Qσ (σ : C.Policy) : IsIntensity (C.Qσ σ.1) :=
  ⟨fun x x' h => C.Q_nonneg x _ (σ.2 x) x' h, fun x => C.Q_sum x _ (σ.2 x)⟩

/-- The objective in (10.50): `r(x, a) + ∑_{x'} v(x')Q(x, a, x')`. -/
def flow (v : X → ℝ) (x : X) (a : A) : ℝ := C.r x a + ∑ x', v x' * C.Q x a x'

/-- `σ` is `v`-greedy for `C` (10.50): `σ(x)` maximises `r(x, a) + ∑_{x'} v(x')Q(x, a, x')` over
`Γ(x)` for every `x`. -/
def IsGreedy (v : X → ℝ) (σ : C.Policy) : Prop :=
  ∀ x, ∀ a ∈ C.Γ x, C.flow v x a ≤ C.flow v x (σ.1 x)

/-- A `v`-greedy policy exists. -/
theorem exists_greedy (v : X → ℝ) : ∃ σ : C.Policy, C.IsGreedy v σ := by
  choose f hf hmax using fun x => Finset.exists_max_image (C.Γ x) (C.flow v x) (C.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun x a ha => hmax x a ha⟩

/-- A `v`-min-greedy policy exists. -/
theorem exists_minGreedy (v : X → ℝ) :
    ∃ σ : C.Policy, ∀ x, ∀ a ∈ C.Γ x, C.flow v x (σ.1 x) ≤ C.flow v x a := by
  choose f hf hmin using fun x => Finset.exists_min_image (C.Γ x) (C.flow v x) (C.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun x a ha => hmin x a ha⟩

variable [DecidableEq X]

/-- The `σ`-value function (10.48), in semigroup form: `v_σ = ∫₀^∞ e^{t(Q_σ − δI)}r_σ dt`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := lifetimeValue (C.Qσ σ - C.δ • 1) (C.rσ σ)

/-- (10.48): `v_σ = ∫₀^∞ e^{−δt}P^σ_t r_σ dt` with `P^σ_t = e^{tQ_σ}`. -/
theorem vσ_eq_integral (σ : X → A) :
    C.vσ σ = ∫ t in Ioi (0 : ℝ), Real.exp (-(t * C.δ)) •
      (NormedSpace.exp (t • C.Qσ σ) *ᵥ C.rσ σ) := by
  simp only [vσ, lifetimeValue, exp_smul_sub_smul_one, Matrix.smul_mulVec]

/-- (10.49) (p. 335): `v_σ = (δI − Q_σ)⁻¹r_σ`. -/
theorem vσ_eq [Nonempty X] (σ : C.Policy) :
    C.vσ σ.1 = (C.δ • (1 : Matrix X X ℝ) - C.Qσ σ.1)⁻¹ *ᵥ C.rσ σ.1 :=
  (constant_discounting (C.isIntensity_Qσ σ) C.δ_pos (C.rσ σ.1)).2.2.2.1

/-- The policy operator `T_σ v = r_σ + (Q_σ + (1 − δ)I)v` (10.51). -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := C.rσ σ + (C.Qσ σ + (1 - C.δ) • 1) *ᵥ v

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    C.Tσ σ v x = C.flow v x (σ x) + (1 - C.δ) * v x := by
  simp only [Tσ, flow, rσ, Qσ, Pi.add_apply, Matrix.add_mulVec, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [mul_comm (v _)]
  ring

/-- Each `T_σ` is order stable with fixed point `v_σ` (§10.2.2.5, via Proposition 10.2.3). -/
theorem orderStable_Tσ [Nonempty X] (σ : C.Policy) :
    OrderStable (C.Tσ σ.1) ∧ IsFixedPt (C.Tσ σ.1) (C.vσ σ.1) :=
  (constant_discounting (C.isIntensity_Qσ σ) C.δ_pos (C.rσ σ.1)).2.2.2.2

/-- The ADP `A = (ℝ^X, {T_σ})` of §10.2.2.5. -/
noncomputable def toADP : ADP (X → ℝ) C.Policy where
  T σ := C.Tσ σ.1
  exists_greedy v := by
    obtain ⟨σ, hσ⟩ := C.exists_greedy v
    refine ⟨σ, fun τ x => ?_⟩
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]
  exists_minGreedy v := by
    obtain ⟨σ, hσ⟩ := C.exists_minGreedy v
    refine ⟨σ, fun τ x => ?_⟩
    change C.Tσ σ.1 v x ≤ C.Tσ τ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]

/-- `A` is order stable (§10.2.2.5). -/
theorem isOrderStable_toADP [Nonempty X] : C.toADP.IsOrderStable := fun σ =>
  (C.orderStable_Tσ σ).1

/-- The `σ`-value functions of `C` and of `A` agree. -/
theorem toADP_vσ [Nonempty X] (hw : C.toADP.WellPosed) (σ : C.Policy) :
    C.toADP.vσ hw σ = C.vσ σ.1 :=
  (ADP.eq_vσ_of_isFixedPt hw (C.orderStable_Tσ σ).2).symm

/-- **Exercise 10.2.2** (p. 336): `σ` is `v`-greedy in the sense of (10.50) iff it is `v`-greedy
for the ADP `A` in the sense of §9.1.2.2. -/
theorem isGreedy_iff (v : X → ℝ) (σ : C.Policy) : C.IsGreedy v σ ↔ C.toADP.IsGreedy v σ := by
  constructor
  · intro hσ τ x
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x
    rw [C.Tσ_apply, C.Tσ_apply]
    linarith [hσ x _ (τ.2 x)]
  · intro hσ x a ha
    let τ : C.Policy := ⟨Function.update σ.1 x a, fun y => by
      rcases eq_or_ne y x with rfl | hy
      · rw [Function.update_self]
        exact ha
      · rw [Function.update_of_ne hy]
        exact σ.2 y⟩
    have h := hσ τ x
    change C.Tσ τ.1 v x ≤ C.Tσ σ.1 v x at h
    rw [C.Tσ_apply, C.Tσ_apply, show τ.1 x = a from Function.update_self x a σ.1] at h
    linarith

/-- The ADP's chosen `v`-greedy policy is `v`-greedy in the sense of (10.50). -/
theorem isGreedy_greedy (v : X → ℝ) : C.IsGreedy v (C.toADP.greedy v) :=
  (C.isGreedy_iff v _).2 (C.toADP.isGreedy_greedy v)

/-- (10.53) (p. 337): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑_{x'} v(x')Q(x, a, x')} + (1 − δ)v(x)`.
-/
theorem bellman_apply (v : X → ℝ) (x : X) :
    C.toADP.bellman v x = (C.Γ x).sup' (C.Γ_nonempty x) (C.flow v x) + (1 - C.δ) * v x := by
  change C.Tσ (C.toADP.greedy v).1 v x = _
  rw [C.Tσ_apply]
  congr 1
  exact le_antisymm (Finset.le_sup' (C.flow v x) ((C.toADP.greedy v).2 x))
    (Finset.sup'_le _ _ fun a ha => C.isGreedy_greedy v x a ha)

/-- `v` satisfies the Hamilton–Jacobi–Bellman equation (10.52):
`δv(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑_{x'} v(x')Q(x, a, x')}` for all `x`. -/
def IsHJB (v : X → ℝ) : Prop := ∀ x, C.δ * v x = (C.Γ x).sup' (C.Γ_nonempty x) (C.flow v x)

/-- Fixed points of the Bellman operator (10.53) are exactly the solutions of the HJB equation. -/
theorem isFixedPt_bellman_iff (v : X → ℝ) : IsFixedPt C.toADP.bellman v ↔ C.IsHJB v := by
  constructor
  · intro h x
    have hx := congrFun h.eq x
    rw [C.bellman_apply] at hx
    linear_combination -hx
  · intro h
    change C.toADP.bellman v = v
    funext x
    rw [C.bellman_apply]
    linear_combination -(h x)

/-- Continuous-time HPI (Algorithm 10.2): `σₖ₊₁` is a `vₖ`-greedy policy, where
`vₖ = (δI − Q_{σₖ})⁻¹r_{σₖ}`. -/
noncomputable def hpiPolicy (σ₀ : C.Policy) : ℕ → C.Policy
  | 0 => σ₀
  | k + 1 => C.toADP.greedy (C.vσ (hpiPolicy σ₀ k).1)

theorem hpiPolicy_eq [Nonempty X] (hw : C.toADP.WellPosed) (σ₀ : C.Policy) (k : ℕ) :
    C.hpiPolicy σ₀ k = C.toADP.hpiPolicy hw σ₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change C.toADP.greedy (C.vσ (C.hpiPolicy σ₀ k).1) =
      C.toADP.greedy (C.toADP.vσ hw (C.toADP.hpiPolicy hw σ₀ k))
    rw [ih, C.toADP_vσ]

/-- **Theorem 10.2.4** (p. 337): for a continuous-time MDP, (i) the value function
`v* = ⋁_σ v_σ` exists and is the unique solution of the HJB equation (10.52), (ii) `C` obeys
Bellman's principle of optimality, (iii) an optimal policy exists, and continuous-time HPI
(Algorithm 10.2) reaches `σₖ₊₁ = σₖ` with `σₖ` optimal after finitely many steps. -/
theorem optimality [Nonempty X] [Finite A] :
    ∃ vstar : X → ℝ, IsGreatest (Set.range fun σ : C.Policy => C.vσ σ.1) vstar ∧
      (∀ v, C.IsHJB v ↔ v = vstar) ∧
      (∀ σ : C.Policy, C.vσ σ.1 = vstar ↔ C.IsGreedy vstar σ) ∧
      (∃ σ : C.Policy, C.vσ σ.1 = vstar) ∧
      ∀ σ₀ : C.Policy, ∃ k, C.hpiPolicy σ₀ (k + 1) = C.hpiPolicy σ₀ k ∧
        C.vσ (C.hpiPolicy σ₀ k).1 = vstar := by
  have hos := C.isOrderStable_toADP
  have : Finite C.Policy := inferInstanceAs (Finite {σ : X → A // ∀ x, σ x ∈ C.Γ x})
  have := C.nonempty_policy
  obtain ⟨vstar, h1, h2, h3, h4, -⟩ := hos.maxOptimality
  have hv := C.toADP_vσ hos.wellPosed
  have hopt : ∀ σ, C.toADP.IsOptimal hos.wellPosed σ ↔ C.vσ σ.1 = vstar := fun σ => by
    constructor
    · intro ho
      obtain ⟨τ, hτ⟩ := h1.1
      refine le_antisymm ?_ ?_
      · rw [← hv]
        exact h1.2 ⟨σ, rfl⟩
      · rw [← hτ, ← hv]
        exact ho τ
    · intro he τ
      rw [hv σ, he]
      exact h1.2 ⟨τ, rfl⟩
  have hrange : (Set.range fun σ : C.Policy => C.vσ σ.1) = Set.range (C.toADP.vσ hos.wellPosed) :=
    congrArg Set.range (funext fun σ => (hv σ).symm)
  refine ⟨vstar, hrange ▸ h1, fun v => (C.isFixedPt_bellman_iff v).symm.trans (h2 v),
    fun σ => (hopt σ).symm.trans ((h3 σ).trans (C.isGreedy_iff vstar σ).symm), ?_,
    fun σ₀ => ?_⟩
  · obtain ⟨σ, hσ⟩ := h4
    exact ⟨σ, (hopt σ).1 hσ⟩
  · obtain ⟨k, hk, -, ho⟩ := hos.hpi_terminates σ₀
    refine ⟨k + 1, ?_, ?_⟩
    · rw [C.hpiPolicy_eq hos.wellPosed, C.hpiPolicy_eq hos.wellPosed]
      change C.toADP.greedy (C.toADP.hpiValue hos.wellPosed σ₀ (k + 1)) =
        C.toADP.greedy (C.toADP.hpiValue hos.wellPosed σ₀ k)
      rw [hk]
    · rw [C.hpiPolicy_eq hos.wellPosed]
      exact (hopt _).1 ho

end CTMDP

/-! ### §10.2.4: job search -/

variable {W : Type*} [Fintype W]

/-- The jump probabilities `Π(x, a, x')` of §10.2.4 (p. 338), with states `x = (s, w)`,
`s = true` meaning employed and `a = true` meaning accept. -/
def jsJump (P : Matrix W W ℝ) (x : Bool × W) (a : Bool) (x' : Bool × W) : ℝ :=
  if x.1 then (if x'.1 then 0 else P x.2 x'.2) else (if x'.1 = a then P x.2 x'.2 else 0)

/-- **Exercise 10.2.3** (p. 339): `Π ≥ 0` and `∑_{x'} Π(x, a, x') = 1` for all `(x, a)`. -/
theorem jsJump_stochastic {P : Matrix W W ℝ} (hP : IsMarkov P) :
    (∀ x a x', 0 ≤ jsJump P x a x') ∧ ∀ x a, ∑ x', jsJump P x a x' = 1 := by
  refine ⟨fun x a x' => ?_, fun x a => ?_⟩
  · simp only [jsJump]
    split_ifs
    · exact le_rfl
    · exact hP.nonneg _ _
    · exact hP.nonneg _ _
    · exact le_rfl
  · rcases x with ⟨s, w⟩
    simp only [jsJump, Fintype.sum_prod_type, Fintype.sum_bool]
    cases s <;> cases a <;> simp [hP.rowsum w]

/-- The jump rate `λ(s, w) = 1{s = 0}κ + 1{s = 1}α`. -/
def jsRate (α κ : ℝ) (x : Bool × W) : ℝ := if x.1 then α else κ

omit [Fintype W] in
theorem jsRate_nonneg {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 ≤ κ) (x : Bool × W) : 0 ≤ jsRate α κ x := by
  unfold jsRate
  split_ifs
  · exact hα
  · exact hκ

/-- For each action `a`, `Π(·, a, ·)` is a stochastic matrix. -/
theorem jsJump_isMarkov {P : Matrix W W ℝ} (hP : IsMarkov P) (a : Bool) :
    IsMarkov (Matrix.of fun x x' => jsJump P x a x') :=
  ⟨fun x x' => (jsJump_stochastic hP).1 x a x', fun x => (jsJump_stochastic hP).2 x a⟩

/-- The continuous-time job search MDP of §10.2.4: `Γ(x) = A`, `Q(x, a, x') = λ(x)(Π(x, a, x') −
I(x, x'))` and `r((s, w), a) = c1{s = 0} + w1{s = 1}`. -/
def jobSearch [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P) {α κ δ : ℝ} (hα : 0 ≤ α)
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) : CTMDP (Bool × W) Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  δ := δ
  δ_pos := hδ
  r x _ := if x.1 then wage x.2 else c
  Q x a x' := jumpIntensity (jsRate α κ) (Matrix.of fun y y' => jsJump P y a y') x x'
  Q_nonneg x a _ x' h :=
    (isIntensity_jumpIntensity (jsRate_nonneg hα hκ) (jsJump_isMarkov hP a)).1 x x' h
  Q_sum x a _ := (isIntensity_jumpIntensity (jsRate_nonneg hα hκ) (jsJump_isMarkov hP a)).2 x

/-- For every `σ ∈ Σ = {0, 1}^X`, `Q_σ(x, x') = λ(x)(Π(x, σ(x), x') − I(x, x'))` is the intensity
matrix of a jump chain (p. 339). -/
theorem jobSearch_Qσ [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P) {α κ δ : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) (σ : Bool × W → Bool) :
    (jobSearch hP hα hκ hδ c wage).Qσ σ =
        jumpIntensity (jsRate α κ) (Matrix.of fun x x' => jsJump P x (σ x) x') ∧
      IsMarkov (Matrix.of fun x x' => jsJump P x (σ x) x') ∧
      IsIntensity ((jobSearch hP hα hκ hδ c wage).Qσ σ) := by
  have hM : IsMarkov (Matrix.of fun x x' => jsJump P x (σ x) x') :=
    ⟨fun x x' => (jsJump_stochastic hP).1 x _ x', fun x => (jsJump_stochastic hP).2 x _⟩
  have he : (jobSearch hP hα hκ hδ c wage).Qσ σ =
      jumpIntensity (jsRate α κ) (Matrix.of fun x x' => jsJump P x (σ x) x') := by
    ext x x'
    rfl
  exact ⟨he, hM, he ▸ isIntensity_jumpIntensity (jsRate_nonneg hα hκ) hM⟩

/-- §10.2.4 (p. 339): Theorem 10.2.4 applies to job search, so an optimal policy exists, the value
function is the unique solution of the HJB equation, and HPI finds an optimal policy in finitely
many steps. -/
theorem jobSearch_optimality [Nonempty W] [DecidableEq W] {P : Matrix W W ℝ} (hP : IsMarkov P)
    {α κ δ : ℝ} (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hδ : 0 < δ) (c : ℝ) (wage : W → ℝ) :
    ∃ vstar : Bool × W → ℝ,
      (∀ v, (jobSearch hP hα hκ hδ c wage).IsHJB v ↔ v = vstar) ∧
      (∃ σ : (jobSearch hP hα hκ hδ c wage).Policy,
        IsGreatest (Set.range fun τ : (jobSearch hP hα hκ hδ c wage).Policy =>
          (jobSearch hP hα hκ hδ c wage).vσ τ.1) ((jobSearch hP hα hκ hδ c wage).vσ σ.1)) ∧
      ∀ σ₀, ∃ k, (jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ (k + 1) =
          (jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ k ∧
        (jobSearch hP hα hκ hδ c wage).vσ ((jobSearch hP hα hκ hδ c wage).hpiPolicy σ₀ k).1 =
          vstar := by
  obtain ⟨vstar, h1, h2, -, ⟨σ, hσ⟩, h5⟩ := (jobSearch hP hα hκ hδ c wage).optimality
  exact ⟨vstar, h2, ⟨σ, hσ ▸ h1⟩, h5⟩

end SargentStachurski.ContinuousTime

set_option linter.style.longLine false
#print axioms SargentStachurski.ContinuousTime.IsMarkov
#print axioms SargentStachurski.ContinuousTime.IsMarkov.mk
#print axioms SargentStachurski.ContinuousTime.IsMarkov.nonneg
#print axioms SargentStachurski.ContinuousTime.IsMarkov.rowsum
#print axioms SargentStachurski.ContinuousTime.IsDistribution
#print axioms SargentStachurski.ContinuousTime.IsDistribution.mk
#print axioms SargentStachurski.ContinuousTime.IsDistribution.nonneg
#print axioms SargentStachurski.ContinuousTime.IsDistribution.sum_eq_one
#print axioms SargentStachurski.ContinuousTime.mulVec_apply_eq
#print axioms SargentStachurski.ContinuousTime.IsMarkov.mul
#print axioms SargentStachurski.ContinuousTime.IsMarkov.pow
#print axioms SargentStachurski.ContinuousTime.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.ContinuousTime.IsMarkov.mulVec_const
#print axioms SargentStachurski.ContinuousTime.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.ContinuousTime.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.ContinuousTime.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.ContinuousTime.GloballyStable
#print axioms SargentStachurski.ContinuousTime.IsContractionOn
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.mk
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.mapsTo
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.nonneg
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.lt_one
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.iterate_mem
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.ContinuousTime.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.ContinuousTime.fixedPt_le_of_le
#print axioms SargentStachurski.ContinuousTime.le_fixedPt_of_le_apply
#print axioms SargentStachurski.ContinuousTime.isContractionOn_of_blackwell
#print axioms SargentStachurski.ContinuousTime.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.ContinuousTime.pow_nonneg_entries
#print axioms SargentStachurski.ContinuousTime.pow_le_pow_entries
#print axioms SargentStachurski.ContinuousTime.complexify
#print axioms SargentStachurski.ContinuousTime.complexify_apply
#print axioms SargentStachurski.ContinuousTime.complexify_pow
#print axioms SargentStachurski.ContinuousTime.complexify_transpose
#print axioms SargentStachurski.ContinuousTime.nnnorm_complexify
#print axioms SargentStachurski.ContinuousTime.norm_complexify
#print axioms SargentStachurski.ContinuousTime.specRad
#print axioms SargentStachurski.ContinuousTime.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.ContinuousTime.specRad_nonneg
#print axioms SargentStachurski.ContinuousTime.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.ContinuousTime.tendsto_norm_pow_rpow
#print axioms SargentStachurski.ContinuousTime.eventually_norm_pow_le
#print axioms SargentStachurski.ContinuousTime.tendsto_norm_pow_zero
#print axioms SargentStachurski.ContinuousTime.summable_pow
#print axioms SargentStachurski.ContinuousTime.one_sub_mul_tsum
#print axioms SargentStachurski.ContinuousTime.tsum_mul_one_sub
#print axioms SargentStachurski.ContinuousTime.neumann_series
#print axioms SargentStachurski.ContinuousTime.specRad_transpose
#print axioms SargentStachurski.ContinuousTime.norm_le_norm_of_abs_le
#print axioms SargentStachurski.ContinuousTime.specRad_le_of_le
#print axioms SargentStachurski.ContinuousTime.rowsum_abs_le_norm
#print axioms SargentStachurski.ContinuousTime.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.ContinuousTime.abs_entry_le_norm
#print axioms SargentStachurski.ContinuousTime.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.ContinuousTime.specRad_le_norm
#print axioms SargentStachurski.ContinuousTime.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.ContinuousTime.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.ContinuousTime.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.ContinuousTime.eventually_abs_entry_pow_le
#print axioms SargentStachurski.ContinuousTime.resPartial
#print axioms SargentStachurski.ContinuousTime.res
#print axioms SargentStachurski.ContinuousTime.res_apply
#print axioms SargentStachurski.ContinuousTime.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.ContinuousTime.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.ContinuousTime.resPartial_apply
#print axioms SargentStachurski.ContinuousTime.summable_res_entry
#print axioms SargentStachurski.ContinuousTime.tendsto_resPartial_apply
#print axioms SargentStachurski.ContinuousTime.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.ContinuousTime.smul_one_sub_mul_res
#print axioms SargentStachurski.ContinuousTime.res_mul_smul_one_sub
#print axioms SargentStachurski.ContinuousTime.res_nonneg
#print axioms SargentStachurski.ContinuousTime.inv_le_res_diag
#print axioms SargentStachurski.ContinuousTime.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.ContinuousTime.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.ContinuousTime.smul_one_sub_mul_res_real
#print axioms SargentStachurski.ContinuousTime.norm_res_complexify_le
#print axioms SargentStachurski.ContinuousTime.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.ContinuousTime.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.ContinuousTime.exists_res_entry_gt
#print axioms SargentStachurski.ContinuousTime.isCompact_simplex
#print axioms SargentStachurski.ContinuousTime.perron_frobenius
#print axioms SargentStachurski.ContinuousTime.perron_frobenius_left
#print axioms SargentStachurski.ContinuousTime.le_specRad_of_colsum_ge
#print axioms SargentStachurski.ContinuousTime.specRad_le_of_colsum_le
#print axioms SargentStachurski.ContinuousTime.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.ContinuousTime.specRad_le_of_rowsum_le
#print axioms SargentStachurski.ContinuousTime.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.ContinuousTime.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.ContinuousTime.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.ContinuousTime.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.ContinuousTime.IsMarkov.exists_stationary
#print axioms SargentStachurski.ContinuousTime.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.ContinuousTime.Irreducible
#print axioms SargentStachurski.ContinuousTime.irreducible_of_pos
#print axioms SargentStachurski.ContinuousTime.Irreducible.transpose
#print axioms SargentStachurski.ContinuousTime.pow_mulVec_eq_of_mulVec_eq
#print axioms SargentStachurski.ContinuousTime.Irreducible.pos_of_mulVec_eq_smul
#print axioms SargentStachurski.ContinuousTime.Irreducible.specRad_pos
#print axioms SargentStachurski.ContinuousTime.Irreducible.exists_pos_eigenvector
#print axioms SargentStachurski.ContinuousTime.Irreducible.exists_pos_left_eigenvector
#print axioms SargentStachurski.ContinuousTime.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms SargentStachurski.ContinuousTime.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms SargentStachurski.ContinuousTime.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms SargentStachurski.ContinuousTime.discountOp
#print axioms SargentStachurski.ContinuousTime.discountOp_apply
#print axioms SargentStachurski.ContinuousTime.discountOp_nonneg
#print axioms SargentStachurski.ContinuousTime.discountOp_const
#print axioms SargentStachurski.ContinuousTime.specRad_smul_isMarkov
#print axioms SargentStachurski.ContinuousTime.summable_pow_apply
#print axioms SargentStachurski.ContinuousTime.summable_pow_mulVec
#print axioms SargentStachurski.ContinuousTime.mulVec_tsum_pow_mulVec
#print axioms SargentStachurski.ContinuousTime.tsum_pow_mulVec_eq
#print axioms SargentStachurski.ContinuousTime.eq_of_eq_add_mulVec
#print axioms SargentStachurski.ContinuousTime.inv_mulVec_eq_add
#print axioms SargentStachurski.ContinuousTime.inv_mulVec_eq_tsum
#print axioms SargentStachurski.ContinuousTime.eq_add_mulVec_iff
#print axioms SargentStachurski.ContinuousTime.specRad_lt_one_iff_existsUnique_pos
#print axioms SargentStachurski.ContinuousTime.globallyStable_of_iterate_contraction
#print axioms SargentStachurski.ContinuousTime.globallyStable_of_iterate_contraction_univ
#print axioms SargentStachurski.ContinuousTime.affineOp
#print axioms SargentStachurski.ContinuousTime.affineOp_iterate_sub
#print axioms SargentStachurski.ContinuousTime.exists_isContractionOn_iterate_affineOp
#print axioms SargentStachurski.ContinuousTime.globallyStable_affineOp
#print axioms SargentStachurski.ContinuousTime.isFixedPt_affineOp_inv
#print axioms SargentStachurski.ContinuousTime.mulVec_le_mulVec_of_nonneg
#print axioms SargentStachurski.ContinuousTime.norm_abs_fun
#print axioms SargentStachurski.ContinuousTime.norm_le_norm_of_abs_le_fun
#print axioms SargentStachurski.ContinuousTime.abs_iterate_sub_le_pow_mulVec
#print axioms SargentStachurski.ContinuousTime.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms SargentStachurski.ContinuousTime.globallyStable_of_abs_sub_le
#print axioms SargentStachurski.ContinuousTime.GloballyStableOn
#print axioms SargentStachurski.ContinuousTime.globallyStableOn_univ_iff
#print axioms SargentStachurski.ContinuousTime.GloballyStableOn.existsUnique
#print axioms SargentStachurski.ContinuousTime.GloballyStableOn.of_conj
#print axioms SargentStachurski.ContinuousTime.globallyStableOn_iff_of_conj
#print axioms SargentStachurski.ContinuousTime.iterate_le_iterate_of_monotoneOn
#print axioms SargentStachurski.ContinuousTime.knaster_tarski
#print axioms SargentStachurski.ContinuousTime.exists_continuum_fixedPts
#print axioms SargentStachurski.ContinuousTime.du_concave
#print axioms SargentStachurski.ContinuousTime.exists_delta_of_lt
#print axioms SargentStachurski.ContinuousTime.du_concave_of_lt
#print axioms SargentStachurski.ContinuousTime.neg_mem_Icc_iff
#print axioms SargentStachurski.ContinuousTime.globallyStableOn_of_reflect
#print axioms SargentStachurski.ContinuousTime.du_convex
#print axioms SargentStachurski.ContinuousTime.du_convex_of_lt
#print axioms SargentStachurski.ContinuousTime.concaveOn_comp
#print axioms SargentStachurski.ContinuousTime.OrderStable
#print axioms SargentStachurski.ContinuousTime.orderStable_of_up_down
#print axioms SargentStachurski.ContinuousTime.orderStable_of_globallyStable
#print axioms SargentStachurski.ContinuousTime.orderStable_restrict
#print axioms SargentStachurski.ContinuousTime.orderStable_affineOp
#print axioms SargentStachurski.ContinuousTime.orderStable_dual_iff
#print axioms SargentStachurski.ContinuousTime.ADP
#print axioms SargentStachurski.ContinuousTime.ADP.mk
#print axioms SargentStachurski.ContinuousTime.ADP.T
#print axioms SargentStachurski.ContinuousTime.ADP.exists_greedy
#print axioms SargentStachurski.ContinuousTime.ADP.exists_minGreedy
#print axioms SargentStachurski.ContinuousTime.ADP.IsGreedy
#print axioms SargentStachurski.ContinuousTime.ADP.greedy
#print axioms SargentStachurski.ContinuousTime.ADP.isGreedy_greedy
#print axioms SargentStachurski.ContinuousTime.ADP.bellman
#print axioms SargentStachurski.ContinuousTime.ADP.T_le_bellman
#print axioms SargentStachurski.ContinuousTime.ADP.isGreatest_bellman
#print axioms SargentStachurski.ContinuousTime.ADP.isGreedy_iff
#print axioms SargentStachurski.ContinuousTime.ADP.monotone_bellman
#print axioms SargentStachurski.ContinuousTime.ADP.WellPosed
#print axioms SargentStachurski.ContinuousTime.ADP.vσ
#print axioms SargentStachurski.ContinuousTime.ADP.isFixedPt_vσ
#print axioms SargentStachurski.ContinuousTime.ADP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.ContinuousTime.ADP.Vu
#print axioms SargentStachurski.ContinuousTime.ADP.vσ_mem_Vu
#print axioms SargentStachurski.ContinuousTime.ADP.howard
#print axioms SargentStachurski.ContinuousTime.ADP.hpiPolicy
#print axioms SargentStachurski.ContinuousTime.ADP.hpiValue
#print axioms SargentStachurski.ContinuousTime.ADP.hpiValue_succ
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable
#print axioms SargentStachurski.ContinuousTime.ADP.IsMaxStable
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.ContinuousTime.ADP.IsOptimal
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.le_howard
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.isOptimal_of_isFixedPt
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.isFixedPt_of_howard
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.howard_fixed
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.hpiValue_le_succ
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.exists_hpiValue_succ_eq
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.hpi_terminates
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.isMaxStable
#print axioms SargentStachurski.ContinuousTime.ADP.IsMaxStable.optimality
#print axioms SargentStachurski.ContinuousTime.ADP.IsOrderStable.maxOptimality
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_mul
#print axioms SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt
#print axioms SargentStachurski.ContinuousTime.exp_memoryless
#print axioms SargentStachurski.ContinuousTime.add_nsmul_of_additive
#print axioms SargentStachurski.ContinuousTime.eq_exp_of_memoryless
#print axioms SargentStachurski.ContinuousTime.exp_counter_properties
#print axioms SargentStachurski.ContinuousTime.norm_one_le
#print axioms SargentStachurski.ContinuousTime.norm_pow_le_pow
#print axioms SargentStachurski.ContinuousTime.norm_partialSum_exp_le
#print axioms SargentStachurski.ContinuousTime.exp_conj_eq
#print axioms SargentStachurski.ContinuousTime.exp_add_eq
#print axioms SargentStachurski.ContinuousTime.exp_natCast_smul
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_smul
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_smul'
#print axioms SargentStachurski.ContinuousTime.exp_smul_mul_comm
#print axioms SargentStachurski.ContinuousTime.exp_transpose_eq
#print axioms SargentStachurski.ContinuousTime.continuous_exp_smul
#print axioms SargentStachurski.ContinuousTime.exp_smul_sub_eq_integral
#print axioms SargentStachurski.ContinuousTime.exp_mul_exp_neg
#print axioms SargentStachurski.ContinuousTime.exp_mulVec_of_eigen
#print axioms SargentStachurski.ContinuousTime.exp_mulVec_of_eigen_real
#print axioms SargentStachurski.ContinuousTime.exp_eigenvalue_converse_false
#print axioms SargentStachurski.ContinuousTime.exp_smul_semigroup
#print axioms SargentStachurski.ContinuousTime.exp_smul_mul_exp_neg_smul
#print axioms SargentStachurski.ContinuousTime.mulVecCLM
#print axioms SargentStachurski.ContinuousTime.entryCLM
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_smul_entry
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_neg_smul_entry
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_mulVec_of_entry
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_exp_smul_mulVec
#print axioms SargentStachurski.ContinuousTime.ivp_unique
#print axioms SargentStachurski.ContinuousTime.ivp_unique_row
#print axioms SargentStachurski.ContinuousTime.exp_smul_diagonal
#print axioms SargentStachurski.ContinuousTime.tendsto_exp_mul_zero_iff
#print axioms SargentStachurski.ContinuousTime.norm_exp_le
#print axioms SargentStachurski.ContinuousTime.complexify_exp
#print axioms SargentStachurski.ContinuousTime.complexify_smul
#print axioms SargentStachurski.ContinuousTime.spectrum_complexify_exp
#print axioms SargentStachurski.ContinuousTime.spectralBound
#print axioms SargentStachurski.ContinuousTime.exp_eigenvalue_converse_false_real
#print axioms SargentStachurski.ContinuousTime.spectrum_nonempty
#print axioms SargentStachurski.ContinuousTime.re_spectrum_finite
#print axioms SargentStachurski.ContinuousTime.re_le_spectralBound
#print axioms SargentStachurski.ContinuousTime.exists_re_eq_spectralBound
#print axioms SargentStachurski.ContinuousTime.specRad_exp
#print axioms SargentStachurski.ContinuousTime.spectralBound_smul
#print axioms SargentStachurski.ContinuousTime.norm_exp_pos
#print axioms SargentStachurski.ContinuousTime.tendsto_log_norm_exp
#print axioms SargentStachurski.ContinuousTime.exp_smul_add
#print axioms SargentStachurski.ContinuousTime.exists_exp_bound
#print axioms SargentStachurski.ContinuousTime.stability_tfae
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.mk
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.zero
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.add
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.cont
#print axioms SargentStachurski.ContinuousTime.isC0Semigroup_exp
#print axioms SargentStachurski.ContinuousTime.hasDerivAt_mul_entry
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.continuousOn_entry
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.intervalIntegrable_entry
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.V
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.hasDerivAt_V
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.tendsto_V_div
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.exists_V_isUnit
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.mul_V
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.hasDerivAt_entry
#print axioms SargentStachurski.ContinuousTime.IsC0Semigroup.exists_eq_exp
#print axioms SargentStachurski.ContinuousTime.IsIntensity
#print axioms SargentStachurski.ContinuousTime.isIntensity_example
#print axioms SargentStachurski.ContinuousTime.exp_nonneg_of_nonneg
#print axioms SargentStachurski.ContinuousTime.exp_smul_one
#print axioms SargentStachurski.ContinuousTime.exp_smul_mulVec_one
#print axioms SargentStachurski.ContinuousTime.intensityBound
#print axioms SargentStachurski.ContinuousTime.intensityJump
#print axioms SargentStachurski.ContinuousTime.intensityJump_spec
#print axioms SargentStachurski.ContinuousTime.exp_smul_nonneg
#print axioms SargentStachurski.ContinuousTime.intensity_tfae
#print axioms SargentStachurski.ContinuousTime.isIntensity_of_isMarkov
#print axioms SargentStachurski.ContinuousTime.exp_smul_entry_isLittleO
#print axioms SargentStachurski.ContinuousTime.chapman_kolmogorov
#print axioms SargentStachurski.ContinuousTime.kolmogorov_backward
#print axioms SargentStachurski.ContinuousTime.kolmogorov_forward
#print axioms SargentStachurski.ContinuousTime.hasDerivWithinAt_mul_entry
#print axioms SargentStachurski.ContinuousTime.eq_one_of_deriv_zero
#print axioms SargentStachurski.ContinuousTime.eq_exp_of_backward
#print axioms SargentStachurski.ContinuousTime.eq_exp_of_forward
#print axioms SargentStachurski.ContinuousTime.jumpIntensity
#print axioms SargentStachurski.ContinuousTime.isIntensity_jumpIntensity
#print axioms SargentStachurski.ContinuousTime.intensityJumpChain
#print axioms SargentStachurski.ContinuousTime.intensityJumpChain_spec
#print axioms SargentStachurski.ContinuousTime.integral_backward_eq
#print axioms SargentStachurski.ContinuousTime.hasDerivWithinAt_integral_Ici
#print axioms SargentStachurski.ContinuousTime.backward_of_integrated
#print axioms SargentStachurski.ContinuousTime.eq_exp_of_integrated
#print axioms SargentStachurski.ContinuousTime.inventoryJump
#print axioms SargentStachurski.ContinuousTime.isMarkov_inventoryJump
#print axioms SargentStachurski.ContinuousTime.continuous_exp_smul_mulVec
#print axioms SargentStachurski.ContinuousTime.mulVecLinCLM
#print axioms SargentStachurski.ContinuousTime.projCLM
#print axioms SargentStachurski.ContinuousTime.lifetimeValue
#print axioms SargentStachurski.ContinuousTime.integrableOn_exp_mulVec
#print axioms SargentStachurski.ContinuousTime.isUnit_of_spectralBound_neg
#print axioms SargentStachurski.ContinuousTime.mulVec_lifetimeValue
#print axioms SargentStachurski.ContinuousTime.lifetimeValue_eq
#print axioms SargentStachurski.ContinuousTime.lifetimeValue_eq_integral_add
#print axioms SargentStachurski.ContinuousTime.inv_nonpos
#print axioms SargentStachurski.ContinuousTime.neg_inv_mulVec_nonneg
#print axioms SargentStachurski.ContinuousTime.orderStable_valuation
#print axioms SargentStachurski.ContinuousTime.pathDiscount_properties
#print axioms SargentStachurski.ContinuousTime.exp_smul_sub_smul_one
#print axioms SargentStachurski.ContinuousTime.constant_discounting
#print axioms SargentStachurski.ContinuousTime.CTMDP
#print axioms SargentStachurski.ContinuousTime.CTMDP.mk
#print axioms SargentStachurski.ContinuousTime.CTMDP.Γ
#print axioms SargentStachurski.ContinuousTime.CTMDP.Γ_nonempty
#print axioms SargentStachurski.ContinuousTime.CTMDP.δ
#print axioms SargentStachurski.ContinuousTime.CTMDP.δ_pos
#print axioms SargentStachurski.ContinuousTime.CTMDP.r
#print axioms SargentStachurski.ContinuousTime.CTMDP.Q
#print axioms SargentStachurski.ContinuousTime.CTMDP.Q_nonneg
#print axioms SargentStachurski.ContinuousTime.CTMDP.Q_sum
#print axioms SargentStachurski.ContinuousTime.CTMDP.Policy
#print axioms SargentStachurski.ContinuousTime.CTMDP.nonempty_policy
#print axioms SargentStachurski.ContinuousTime.CTMDP.Qσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.rσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.isIntensity_Qσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.flow
#print axioms SargentStachurski.ContinuousTime.CTMDP.IsGreedy
#print axioms SargentStachurski.ContinuousTime.CTMDP.exists_greedy
#print axioms SargentStachurski.ContinuousTime.CTMDP.exists_minGreedy
#print axioms SargentStachurski.ContinuousTime.CTMDP.vσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.vσ_eq_integral
#print axioms SargentStachurski.ContinuousTime.CTMDP.vσ_eq
#print axioms SargentStachurski.ContinuousTime.CTMDP.Tσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.Tσ_apply
#print axioms SargentStachurski.ContinuousTime.CTMDP.orderStable_Tσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.toADP
#print axioms SargentStachurski.ContinuousTime.CTMDP.isOrderStable_toADP
#print axioms SargentStachurski.ContinuousTime.CTMDP.toADP_vσ
#print axioms SargentStachurski.ContinuousTime.CTMDP.isGreedy_iff
#print axioms SargentStachurski.ContinuousTime.CTMDP.isGreedy_greedy
#print axioms SargentStachurski.ContinuousTime.CTMDP.bellman_apply
#print axioms SargentStachurski.ContinuousTime.CTMDP.IsHJB
#print axioms SargentStachurski.ContinuousTime.CTMDP.isFixedPt_bellman_iff
#print axioms SargentStachurski.ContinuousTime.CTMDP.hpiPolicy
#print axioms SargentStachurski.ContinuousTime.CTMDP.hpiPolicy_eq
#print axioms SargentStachurski.ContinuousTime.CTMDP.optimality
#print axioms SargentStachurski.ContinuousTime.jsJump
#print axioms SargentStachurski.ContinuousTime.jsJump_stochastic
#print axioms SargentStachurski.ContinuousTime.jsRate
#print axioms SargentStachurski.ContinuousTime.jsRate_nonneg
#print axioms SargentStachurski.ContinuousTime.jsJump_isMarkov
#print axioms SargentStachurski.ContinuousTime.jobSearch
#print axioms SargentStachurski.ContinuousTime.jobSearch_Qσ
#print axioms SargentStachurski.ContinuousTime.jobSearch_optimality
