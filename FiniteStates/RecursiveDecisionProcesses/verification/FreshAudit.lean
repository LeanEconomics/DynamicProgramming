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
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 8 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear valuation and eventual contractions, restated

Facts from Vol. 1, Chapter 6 used in Chapters 7–8, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A power-transformed affine equation

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Certainty equivalent operators

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregators, Koopmans operators and lifetime values

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin preferences

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive decision processes

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality for recursive decision processes

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples of recursive decision processes

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contracting RDPs

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Eventually contracting RDPs

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convex and concave RDPs

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Adversarial agents, robustness and KL penalties

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

namespace SargentStachurski.RecursiveDecisionProcesses

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

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.1.4.1 (pp. 261–263).

For the Epstein–Zin RDP of Example 8.1.7 on `V = (0, ∞)^X`, with `θ = γ/α`:

* (8.23)–(8.24): the transformed RDP `R̂` with
  `B̂(x, a, v) = [r(x, a) + β(∑ v(x')P(x, a, x'))^{1/θ}]^θ` on `(0, ∞)^X`, written with the map
  `G` of Theorem 7.1.4.
* Exercise 8.1.19: `R` and `R̂` are topologically conjugate under `φ(t) = t^γ` on `(0, ∞)`.
* Lemma 8.1.5: if every `P_σ` is irreducible, `R̂` is globally stable (Theorem 7.1.4 with
  `ρ(β^θ P_σ)^{1/θ} = β < 1`).
* Proposition 8.1.4: if every `P_σ` is irreducible, `R` is globally stable, by
  Proposition 8.1.3; so Theorem 8.1.1 applies. The policy operators of `R` are the Epstein–Zin
  Koopmans operators (7.14), and Proposition 7.2.3 gives the same conclusion directly.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Every row of a Markov matrix has a positive entry. -/
theorem IsMarkov.exists_pos {X : Type*} [Fintype X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (x : X) : ∃ x', 0 < P x x' := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have : ∑ x', P x x' ≤ 0 := sum_nonpos fun x' _ => hcon x'
  linarith [hP.rowsum x]

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The matrix `β^θ P_a` of (8.24) is nonnegative, with a positive entry in every row. -/
theorem ezB_kernelAt_nonneg (θ : ℝ) (a : A) (x x' : X) :
    0 ≤ ezB (fun _ => M.β) θ (kernelAt M.P a) x x' :=
  mul_nonneg (Real.rpow_nonneg M.β_pos.le _) (M.P_nonneg x a x')

theorem ezB_kernelAt_row (θ : ℝ) (a : A) (x : X) :
    ∃ x', 0 < ezB (fun _ => M.β) θ (kernelAt M.P a) x x' := by
  obtain ⟨x', hx'⟩ := (M.isMarkov_P a).exists_pos x
  exact ⟨x', mul_pos (Real.rpow_pos_of_pos M.β_pos _) hx'⟩

/-- The transformed Epstein–Zin RDP `R̂` (8.23)–(8.24) on `V = (0, ∞)^X`:
`B̂(x, a, v) = [r(x, a) + (β^θ ∑ v(x')P(x, a, x'))^{1/θ}]^θ = [r(x, a) + β(∑ vP)^{1/θ}]^θ`. -/
noncomputable def epsteinZinHat (hr : ∀ x a, 0 < M.r x a) {θ : ℝ} (hθ : θ ≠ 0) : RDP X A where
  Γ := M.Γ
  Γ_nonempty := M.Γ_nonempty
  V := posCone X
  B := fun x a v => powG (ezB (fun _ => M.β) θ (kernelAt M.P a)) (fun y => M.r y a) θ v x
  mono := fun x a _ _ hv _ hw hvw => powG_monotoneOn (M.ezB_kernelAt_nonneg θ a)
    (M.ezB_kernelAt_row θ a) (fun y => (hr y a).le) hθ hv hw hvw x
  consistent := fun σ _ _ hv x => powG_mapsTo (M.ezB_kernelAt_nonneg θ (σ x))
    (M.ezB_kernelAt_row θ (σ x)) (fun y => (hr y (σ x)).le) θ hv x

/-- The policy operators of `R̂` are the maps `G` of Theorem 7.1.4 for `A = β^θ P_σ`, `h = r_σ`. -/
theorem epsteinZinHat_Tσ (hr : ∀ x a, 0 < M.r x a) {θ : ℝ} (hθ : θ ≠ 0) (σ : X → A) :
    (M.epsteinZinHat hr hθ).Tσ σ = powG (ezB (fun _ => M.β) θ (M.Pσ σ)) (M.rσ σ) θ := rfl

/-- **Lemma 8.1.5** (p. 262): if every `P_σ` is irreducible, `R̂` is globally stable. -/
theorem epsteinZinHat_isGloballyStable [DecidableEq X] [Nonempty X] (hr : ∀ x a, 0 < M.r x a)
    {θ : ℝ} (hθ : θ ≠ 0) (hirr : ∀ σ, M.toRDP.IsFeasible σ → Irreducible (M.Pσ σ)) :
    (M.epsteinZinHat hr hθ).IsGloballyStable := by
  intro σ hσ
  rw [epsteinZinHat_Tσ]
  refine globallyStableOn_powG (irreducible_ezB (fun _ => M.β_pos) θ (hirr σ hσ))
    (fun x => hr x (σ x)) hθ ?_
  have hB : ezB (fun _ => M.β) θ (M.Pσ σ) = M.β ^ θ • M.Pσ σ := by
    ext x x'
    simp [ezB, Pσ]
  rw [hB, specRad_smul_isMarkov (M.isMarkov_Pσ σ) (Real.rpow_nonneg M.β_pos.le _),
    Real.rpow_rpow_inv M.β_pos.le hθ]
  exact M.β_lt_one

/-- **Exercise 8.1.19** (p. 262): `B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]` with `φ(t) = t^γ` and
`θ = γ/α`. -/
theorem epsteinZin_B_eq_conj (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    (M.epsteinZin hr hα hγ).B x a v =
      ((M.epsteinZinHat hr (div_ne_zero hγ hα)).B x a (fun x' => v x' ^ γ)) ^ γ⁻¹ := by
  have h := congrFun (powMap_ezK (M.isMarkov_P a) (fun y => (hr y a).le) (fun _ => M.β_pos) hα
    hγ hv) x
  have hpos : 0 < ezK (fun y => M.r y a) (fun _ => M.β) α γ (kernelAt M.P a) v x :=
    ezK_mapsTo (M.isMarkov_P a) (fun y => (hr y a).le) (fun _ => M.β_pos) α γ hv x
  change ezK (fun y => M.r y a) (fun _ => M.β) α γ (kernelAt M.P a) v x =
    (powG (ezB (fun _ => M.β) (γ / α) (kernelAt M.P a)) (fun y => M.r y a) (γ / α)
      (powMap γ v) x) ^ γ⁻¹
  rw [← h]
  exact (Real.rpow_rpow_inv hpos.le hγ).symm

/-- **Proposition 8.1.4** (p. 262): if every `P_σ` is irreducible, the Epstein–Zin RDP is
globally stable, via Exercise 8.1.19, Proposition 8.1.3 and Lemma 8.1.5. -/
theorem epsteinZin_isGloballyStable [DecidableEq X] [Nonempty X] (hr : ∀ x a, 0 < M.r x a)
    {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hirr : ∀ σ, M.toRDP.IsFeasible σ → Irreducible (M.Pσ σ)) :
    (M.epsteinZin hr hα hγ).IsGloballyStable := by
  have hc : ContinuousOn (fun t : ℝ => t ^ γ) (Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  have hc' : ContinuousOn (fun t : ℝ => t ^ γ⁻¹) (Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  refine (RDP.isGloballyStable_iff_of_conj (R := M.epsteinZin hr hα hγ)
    (R' := M.epsteinZinHat hr (div_ne_zero hγ hα)) rfl
    (M := Ioi 0) (M' := Ioi 0) rfl rfl (fun t (ht : 0 < t) => Real.rpow_pos_of_pos ht γ)
    (fun t (ht : 0 < t) => Real.rpow_pos_of_pos ht γ⁻¹)
    (fun t (ht : 0 < t) => Real.rpow_inv_rpow ht.le hγ)
    (fun t (ht : 0 < t) => Real.rpow_rpow_inv ht.le hγ) hc hc'
    fun x a _ v hv => M.epsteinZin_B_eq_conj hr hα hγ x a hv).2 ?_
  exact M.epsteinZinHat_isGloballyStable hr _ hirr

/-- The policy operators of the Epstein–Zin RDP are the Koopmans operators (7.14) of `P_σ`. -/
theorem epsteinZin_Tσ (hr : ∀ x a, 0 < M.r x a) {α γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (σ : X → A) :
    (M.epsteinZin hr hα hγ).Tσ σ = ezK (M.rσ σ) (fun _ => M.β) α γ (M.Pσ σ) := rfl

end MDP

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Smooth ambiguity

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.4 (pp. 283–286).

The smooth ambiguity aggregator (8.52) of Ju and Miao, with a finite parameter set `Θ` and
subjective beliefs `μ(x, ·)` a distribution on `Θ`:
`B(x, a, v) = (r(x, a) + β[∑_θ (∑ v(x')^γ P_θ(x, a, x'))^{κ/γ} μ(x, θ)]^{α/κ})^{1/α}`.

* Exercise 8.3.5: with `κ = γ` (ambiguity neutrality) it is the Epstein–Zin aggregator for the
  mixture kernel `∑ μ(x, θ)P_θ`.
* For `κ < γ < 0 < α`, with `ξ = γ/κ ∈ (0, 1)` and `ζ = α/κ < 0`:
  Exercise 8.3.6 (the bounds (8.53) for `v₁ = (r₁/(1 − β))^{1/α}`, `v₂ = ((r₂ + ε)/(1 − β))^{1/α}`),
  Exercise 8.3.7 (`R = (Γ, [v₁, v₂], B)` is an RDP), the transformed aggregator (8.54) and
  Exercise 8.3.8 (`R̂` is an RDP with `v̂₁ < B̂(x, a, v̂₁)`), Exercise 8.3.9 (`R` and `R̂` are
  conjugate under `φ(t) = t^κ`), Lemma 8.3.6 (`B̂(x, a, ·)` is concave) and Proposition 8.3.5
  (`R` is globally stable).

Two printed details are corrected (see `docs/corrections.md`): the exponent in (8.54) must be
`ζ = α/κ`, not `κ/α`, for Exercise 8.3.9 to hold; and since `φ` reverses order, the transformed
value space is `V̂ = [v₂^κ, v₁^κ]`, not `[v₂^{1/κ}, v₁^{1/κ}]`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

variable {X Θ : Type*} [Fintype X] [Fintype Θ]

/-- The smooth ambiguity aggregator (8.52) at a fixed `(x, a)`, with beliefs `μ` on `Θ` and
kernels `P_θ`. -/
noncomputable def smoothB (r β α γ κ : ℝ) (μ : Θ → ℝ) (P : Θ → X → ℝ) (v : X → ℝ) : ℝ :=
  (r + β * (∑ θ, μ θ * (∑ x', v x' ^ γ * P θ x') ^ (κ / γ)) ^ (α / κ)) ^ α⁻¹

/-- **Exercise 8.3.5** (p. 284): under ambiguity neutrality `κ = γ` the smooth ambiguity aggregator
is the Epstein–Zin aggregator (8.10) for the mixture kernel `∑_θ μ(θ)P_θ`. -/
theorem smoothB_neutral (r β α : ℝ) {γ : ℝ} (hγ : γ ≠ 0) (μ : Θ → ℝ) (P : Θ → X → ℝ)
    (v : X → ℝ) :
    smoothB r β α γ γ μ P v = (r + β * (∑ x', v x' ^ γ * ∑ θ, μ θ * P θ x') ^ (α / γ)) ^ α⁻¹ := by
  have h : ∑ θ, μ θ * ∑ x', v x' ^ γ * P θ x' = ∑ x', v x' ^ γ * ∑ θ, μ θ * P θ x' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  simp only [smoothB, div_self hγ, Real.rpow_one, h]

/-- A convex combination of positive numbers with distribution weights is positive. -/
theorem sum_dist_mul_pos {Θ : Type*} [Fintype Θ] {μ : Θ → ℝ} (hμ : IsDistribution μ)
    {f : Θ → ℝ} (hf : ∀ θ, 0 < f θ) : 0 < ∑ θ, μ θ * f θ := by
  obtain ⟨θ, hθ⟩ : ∃ θ, 0 < μ θ := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : ∑ θ, μ θ ≤ 0 := sum_nonpos fun θ _ => hcon θ
    linarith [hμ.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos hθ (hf θ)) (single_le_sum
    (f := fun θ => μ θ * f θ) (fun θ' _ => mul_nonneg (hμ.nonneg θ') (hf θ').le) (mem_univ θ))

/-- The smooth ambiguity model of §8.3.4, with `κ < γ < 0 < α`, rewards in `[r₁, r₂]` with
`r₁ > 0`, kernels `P_θ` and beliefs `μ(x, ·)` that are distributions. -/
structure SmoothAmbiguity (X A Θ : Type*) [Fintype X] [Fintype A] [Fintype Θ] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  r : X → A → ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₁_pos : 0 < r₁
  r₁_le_r₂ : r₁ ≤ r₂
  r_bounds : ∀ x a, r₁ ≤ r x a ∧ r x a ≤ r₂
  P : Θ → X → A → X → ℝ
  P_nonneg : ∀ θ x a x', 0 ≤ P θ x a x'
  P_rowsum : ∀ θ x a, ∑ x', P θ x a x' = 1
  μ : X → Θ → ℝ
  μ_dist : ∀ x, IsDistribution (μ x)
  α : ℝ
  γ : ℝ
  κ : ℝ
  κ_lt_γ : κ < γ
  γ_neg : γ < 0
  α_pos : 0 < α

namespace SmoothAmbiguity

variable {X A Θ : Type*} [Fintype X] [Fintype A] [Fintype Θ] (S : SmoothAmbiguity X A Θ)

theorem κ_neg : S.κ < 0 := S.κ_lt_γ.trans S.γ_neg

theorem r_pos (x : X) (a : A) : 0 < S.r x a := S.r₁_pos.trans_le (S.r_bounds x a).1

/-- The aggregator (8.52). -/
noncomputable def B (x : X) (a : A) (v : X → ℝ) : ℝ :=
  smoothB (S.r x a) S.β S.α S.γ S.κ (S.μ x) (fun θ => S.P θ x a) v

/-- `ξ = γ/κ ∈ (0, 1)`. -/
noncomputable def ξ : ℝ := S.γ / S.κ

/-- `ζ = α/κ < 0` (printed as `κ/α`). -/
noncomputable def ζ : ℝ := S.α / S.κ

theorem ξ_pos : 0 < S.ξ := div_pos_of_neg_of_neg S.γ_neg S.κ_neg

theorem ξ_le_one : S.ξ ≤ 1 := (div_le_one_of_neg S.κ_neg).2 S.κ_lt_γ.le

theorem ζ_neg : S.ζ < 0 := div_neg_of_pos_of_neg S.α_pos S.κ_neg

/-- `P_θ` at action `a`. -/
def Pa (θ : Θ) (a : A) : Matrix X X ℝ := kernelAt (S.P θ) a

theorem isMarkov_Pa (θ : Θ) (a : A) : IsMarkov (S.Pa θ a) :=
  isMarkov_kernelAt (S.P_nonneg θ) (S.P_rowsum θ) a

/-- The inner certainty equivalent of (8.54): `g(v̂) = ∑_θ μ(x, θ)(∑ v̂(x')^ξ P_θ(x, a, x'))^{1/ξ}`.
-/
noncomputable def g (x : X) (a : A) (w : X → ℝ) : ℝ := ∑ θ, S.μ x θ * kpR S.ξ (S.Pa θ a) w x

/-- The transformed aggregator (8.54): `B̂(x, a, v̂) = (r(x, a) + β g(v̂)^ζ)^{1/ζ}`. -/
noncomputable def Bhat (x : X) (a : A) (w : X → ℝ) : ℝ :=
  (S.r x a + S.β * S.g x a w ^ S.ζ) ^ S.ζ⁻¹

theorem g_pos (x : X) (a : A) {w : X → ℝ} (hw : w ∈ posCone X) : 0 < S.g x a w :=
  sum_dist_mul_pos (S.μ_dist x) fun θ => kpR_pos (S.isMarkov_Pa θ a) hw x

theorem Bhat_pos (x : X) (a : A) {w : X → ℝ} (hw : w ∈ posCone X) : 0 < S.Bhat x a w :=
  Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.g_pos x a hw).le _))) _

/-- The inner sums `∑ v(x')^γ P_θ(x, a, x')` are positive on `(0, ∞)^X`. -/
theorem inner_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) (θ : Θ) :
    0 < ∑ x', v x' ^ S.γ * S.P θ x a x' := by
  have := (S.isMarkov_Pa θ a).mulVec_pos (fun x' => Real.rpow_pos_of_pos (hv x') S.γ) x
  rwa [mulVec_apply_eq] at this

/-- The certainty equivalent `∑_θ μ(x, θ)(∑ v^γ P_θ)^{κ/γ}` is positive on `(0, ∞)^X`. -/
theorem ce_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    0 < ∑ θ, S.μ x θ * (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) :=
  sum_dist_mul_pos (S.μ_dist x) fun θ => Real.rpow_pos_of_pos (S.inner_pos x a hv θ) _

theorem B_pos (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) : 0 < S.B x a v :=
  Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.ce_pos x a hv).le _))) _

/-- **Exercise 8.3.9 (i)** (p. 285), in the form `B̂(x, a, v^κ) = B(x, a, v)^κ`. -/
theorem Bhat_pow (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    S.Bhat x a (fun x' => v x' ^ S.κ) = S.B x a v ^ S.κ := by
  have hκ : S.κ ≠ 0 := S.κ_neg.ne
  have hγ : S.γ ≠ 0 := S.γ_neg.ne
  have hkp : ∀ θ, kpR S.ξ (S.Pa θ a) (fun x' => v x' ^ S.κ) x =
      (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) := fun θ => by
    have e : ∀ x', (v x' ^ S.κ) ^ (S.γ / S.κ) = v x' ^ S.γ := fun x' => by
      rw [← Real.rpow_mul (hv x').le, show S.κ * (S.γ / S.κ) = S.γ by field_simp]
    simp only [kpR, mulVec_apply_eq, Pa, kernelAt_apply, e, ξ, inv_div]
  have hbase : 0 < S.r x a + S.β *
      (∑ θ, S.μ x θ * (∑ x', v x' ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ)) ^ (S.α / S.κ) :=
    add_pos_of_pos_of_nonneg (S.r_pos x a)
      (mul_nonneg S.β_pos.le (Real.rpow_nonneg (S.ce_pos x a hv).le _))
  unfold Bhat g
  simp only [hkp]
  simp only [B, smoothB, ζ]
  rw [← Real.rpow_mul hbase.le, inv_div, inv_mul_eq_div]

/-- Exercise 8.3.9 (i): `B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]` with `φ(t) = t^κ`. -/
theorem B_eq_conj (x : X) (a : A) {v : X → ℝ} (hv : v ∈ posCone X) :
    S.B x a v = S.Bhat x a (fun x' => v x' ^ S.κ) ^ S.κ⁻¹ := by
  rw [S.Bhat_pow x a hv, Real.rpow_rpow_inv (S.B_pos x a hv).le S.κ_neg.ne]

/-- `B̂(x, a, ·)` is order preserving on `(0, ∞)^X`. -/
theorem Bhat_monotoneOn (x : X) (a : A) : MonotoneOn (S.Bhat x a) (posCone X) :=
  fun v hv w hw hvw => ezAgg_monotoneOn (S.r_pos x a) S.β_pos.le S.ζ_neg.ne (S.g_pos x a hv)
    (S.g_pos x a hw) (sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left
      ((isCertEquiv_kpR S.ξ_pos.ne' (S.isMarkov_Pa θ a)).mono v hv w hw hvw x)
      ((S.μ_dist x).nonneg θ))

omit [Fintype X] in
theorem pow_mem_posCone {v : X → ℝ} (hv : v ∈ posCone X) (p : ℝ) :
    (fun x' => v x' ^ p) ∈ posCone X := fun x' => Real.rpow_pos_of_pos (hv x') p

/-- `B(x, a, ·)` is order preserving on `(0, ∞)^X`: `t ↦ t^κ` and `t ↦ t^{1/κ}` both reverse order.
-/
theorem B_monotoneOn (x : X) (a : A) : MonotoneOn (S.B x a) (posCone X) := fun v hv w hw hvw => by
  rw [S.B_eq_conj x a hv, S.B_eq_conj x a hw]
  have hκv : (fun x' => w x' ^ S.κ) ≤ fun x' => v x' ^ S.κ := fun x' =>
    Real.rpow_le_rpow_of_nonpos (hv x') (hvw x') S.κ_neg.le
  have h1 := S.Bhat_monotoneOn x a (pow_mem_posCone hw _) (pow_mem_posCone hv _) hκv
  exact Real.rpow_le_rpow_of_nonpos (S.Bhat_pos x a (pow_mem_posCone hw _)) h1
    (inv_nonpos.2 S.κ_neg.le)

/-- At a constant `c > 0`, `B(x, a, c) = (r(x, a) + βc^α)^{1/α}`. -/
theorem B_const (x : X) (a : A) {c : ℝ} (hc : 0 < c) :
    S.B x a (fun _ => c) = (S.r x a + S.β * c ^ S.α) ^ S.α⁻¹ := by
  have hκ : S.κ ≠ 0 := S.κ_neg.ne
  have hγ : S.γ ≠ 0 := S.γ_neg.ne
  have h1 : ∀ θ, (∑ x', c ^ S.γ * S.P θ x a x') ^ (S.κ / S.γ) = c ^ S.κ := fun θ => by
    rw [← Finset.mul_sum, S.P_rowsum θ x a, mul_one, ← Real.rpow_mul hc.le,
      show S.γ * (S.κ / S.γ) = S.κ by field_simp]
  simp only [B, smoothB, h1]
  rw [← Finset.sum_mul, (S.μ_dist x).sum_eq_one, one_mul, ← Real.rpow_mul hc.le,
    show S.κ * (S.α / S.κ) = S.α by field_simp]

/-! ### The value space (Exercises 8.3.6–8.3.7) -/

/-- `v₁ = (r₁/(1 − β))^{1/α}`. -/
noncomputable def v₁ : ℝ := (S.r₁ / (1 - S.β)) ^ S.α⁻¹

/-- `v₂ = ((r₂ + ε)/(1 − β))^{1/α}`. -/
noncomputable def v₂ (ε : ℝ) : ℝ := ((S.r₂ + ε) / (1 - S.β)) ^ S.α⁻¹

theorem one_sub_β_pos : 0 < 1 - S.β := by linarith [S.β_lt_one]

theorem v₁_pos : 0 < S.v₁ := Real.rpow_pos_of_pos (div_pos S.r₁_pos S.one_sub_β_pos) _

theorem v₁_le_v₂ {ε : ℝ} (hε : 0 < ε) : S.v₁ ≤ S.v₂ ε :=
  Real.rpow_le_rpow (div_pos S.r₁_pos S.one_sub_β_pos).le
    (div_le_div_of_nonneg_right (by linarith [S.r₁_le_r₂]) S.one_sub_β_pos.le)
    (inv_nonneg.2 S.α_pos.le)

theorem v₂_pos {ε : ℝ} (hε : 0 < ε) : 0 < S.v₂ ε := S.v₁_pos.trans_le (S.v₁_le_v₂ hε)

/-- **Exercise 8.3.6** (p. 284), (8.53), lower bound: `v₁ ≤ B(x, a, v₁)`. -/
theorem v₁_le_B (x : X) (a : A) : S.v₁ ≤ S.B x a (fun _ => S.v₁) := by
  have hq : 0 < S.r₁ / (1 - S.β) := div_pos S.r₁_pos S.one_sub_β_pos
  rw [S.B_const x a S.v₁_pos, v₁, Real.rpow_inv_rpow hq.le S.α_pos.ne']
  refine Real.rpow_le_rpow hq.le ?_ (inv_nonneg.2 S.α_pos.le)
  have e : S.r₁ / (1 - S.β) = S.r₁ + S.β * (S.r₁ / (1 - S.β)) := by
    field_simp [S.one_sub_β_pos.ne']
    ring
  have := (S.r_bounds x a).1
  linarith

/-- **Exercise 8.3.6** (p. 284), (8.53), strict upper bound: `B(x, a, v₂) < v₂`. -/
theorem B_lt_v₂ (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) : S.B x a (fun _ => S.v₂ ε) < S.v₂ ε := by
  have hq : 0 < (S.r₂ + ε) / (1 - S.β) :=
    div_pos (by linarith [S.r₁_pos, S.r₁_le_r₂]) S.one_sub_β_pos
  rw [S.B_const x a (S.v₂_pos hε), v₂, Real.rpow_inv_rpow hq.le S.α_pos.ne']
  refine Real.rpow_lt_rpow (add_pos_of_pos_of_nonneg (S.r_pos x a)
    (mul_nonneg S.β_pos.le hq.le)).le ?_ (inv_pos.2 S.α_pos)
  have e : (S.r₂ + ε) / (1 - S.β) = S.r₂ + ε + S.β * ((S.r₂ + ε) / (1 - S.β)) := by
    field_simp [S.one_sub_β_pos.ne']
    ring
  have := (S.r_bounds x a).2
  linarith

omit [Fintype X] in
theorem Icc_subset_posCone {c d : ℝ} (hc : 0 < c) :
    Icc (fun _ : X => c) (fun _ => d) ⊆ posCone X := fun _ hv x => hc.trans_le (hv.1 x)

/-- `B(x, a, v) ∈ [v₁, v₂]` for `v ∈ [v₁, v₂]`. -/
theorem B_mem (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) {v : X → ℝ}
    (hv : v ∈ Icc (fun _ : X => S.v₁) (fun _ => S.v₂ ε)) : S.B x a v ∈ Icc S.v₁ (S.v₂ ε) :=
  ⟨(S.v₁_le_B x a).trans (S.B_monotoneOn x a (fun _ => S.v₁_pos)
      (Icc_subset_posCone S.v₁_pos hv) hv.1),
    (S.B_monotoneOn x a (Icc_subset_posCone S.v₁_pos hv) (fun _ => S.v₂_pos hε) hv.2).trans
      (S.B_lt_v₂ x a hε).le⟩

/-- **Exercise 8.3.7** (p. 284): `R = (Γ, [v₁, v₂], B)` is an RDP. -/
noncomputable def toRDP {ε : ℝ} (hε : 0 < ε) : RDP X A where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  V := Icc (fun _ => S.v₁) (fun _ => S.v₂ ε)
  B := S.B
  mono := fun x a _ _ hv _ hw hvw => S.B_monotoneOn x a (Icc_subset_posCone S.v₁_pos hv)
    (Icc_subset_posCone S.v₁_pos hw) hvw
  consistent := fun σ _ _ hv => ⟨fun x => (S.B_mem x (σ x) hε hv).1,
    fun x => (S.B_mem x (σ x) hε hv).2⟩

/-! ### The transformed RDP (Exercises 8.3.8–8.3.9) -/

/-- `v̂₁ = v₂^κ` (printed `v₂^{1/κ}`). -/
noncomputable def w₁ (ε : ℝ) : ℝ := S.v₂ ε ^ S.κ

/-- `v̂₂ = v₁^κ` (printed `v₁^{1/κ}`). -/
noncomputable def w₂ : ℝ := S.v₁ ^ S.κ

theorem w₁_pos {ε : ℝ} (hε : 0 < ε) : 0 < S.w₁ ε := Real.rpow_pos_of_pos (S.v₂_pos hε) _

theorem w₁_le_w₂ {ε : ℝ} (hε : 0 < ε) : S.w₁ ε ≤ S.w₂ :=
  Real.rpow_le_rpow_of_nonpos S.v₁_pos (S.v₁_le_v₂ hε) S.κ_neg.le

/-- `φ(t) = t^κ` maps `[v₁, v₂]` into `[v̂₁, v̂₂]`. -/
theorem pow_mem {ε : ℝ} {t : ℝ} (ht : t ∈ Icc S.v₁ (S.v₂ ε)) :
    t ^ S.κ ∈ Icc (S.w₁ ε) S.w₂ :=
  ⟨Real.rpow_le_rpow_of_nonpos (S.v₁_pos.trans_le ht.1) ht.2 S.κ_neg.le,
    Real.rpow_le_rpow_of_nonpos S.v₁_pos ht.1 S.κ_neg.le⟩

/-- `φ⁻¹(t) = t^{1/κ}` maps `[v̂₁, v̂₂]` into `[v₁, v₂]`. -/
theorem pow_inv_mem {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc (S.w₁ ε) S.w₂) :
    t ^ S.κ⁻¹ ∈ Icc S.v₁ (S.v₂ ε) := by
  have hκ : S.κ⁻¹ ≤ 0 := inv_nonpos.2 S.κ_neg.le
  have ht0 : 0 < t := (S.w₁_pos hε).trans_le ht.1
  constructor
  · have := Real.rpow_le_rpow_of_nonpos ht0 ht.2 hκ
    rwa [w₂, Real.rpow_rpow_inv S.v₁_pos.le S.κ_neg.ne] at this
  · have := Real.rpow_le_rpow_of_nonpos (S.w₁_pos hε) ht.1 hκ
    rwa [w₁, Real.rpow_rpow_inv (S.v₂_pos hε).le S.κ_neg.ne] at this

/-- `B̂(x, a, v̂) ∈ [v̂₁, v̂₂]` for `v̂ ∈ [v̂₁, v̂₂]`. -/
theorem Bhat_mem (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) {w : X → ℝ}
    (hw : w ∈ Icc (fun _ : X => S.w₁ ε) (fun _ => S.w₂)) : S.Bhat x a w ∈ Icc (S.w₁ ε) S.w₂ := by
  set u : X → ℝ := fun x' => w x' ^ S.κ⁻¹
  have hu : u ∈ Icc (fun _ : X => S.v₁) (fun _ => S.v₂ ε) :=
    ⟨fun x' => (S.pow_inv_mem hε ⟨hw.1 x', hw.2 x'⟩).1,
      fun x' => (S.pow_inv_mem hε ⟨hw.1 x', hw.2 x'⟩).2⟩
  have hwu : w = fun x' => u x' ^ S.κ := funext fun x' =>
    (Real.rpow_inv_rpow ((S.w₁_pos hε).trans_le (hw.1 x')).le S.κ_neg.ne).symm
  rw [hwu, S.Bhat_pow x a (Icc_subset_posCone S.v₁_pos hu)]
  exact S.pow_mem (S.B_mem x a hε hu)

/-- The transformed RDP `R̂ = (Γ, [v̂₁, v̂₂], B̂)` of (8.54): **Exercise 8.3.8** (p. 285). -/
noncomputable def toRDPHat {ε : ℝ} (hε : 0 < ε) : RDP X A where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  V := Icc (fun _ => S.w₁ ε) (fun _ => S.w₂)
  B := S.Bhat
  mono := fun x a _ _ hv _ hw hvw => S.Bhat_monotoneOn x a (Icc_subset_posCone (S.w₁_pos hε) hv)
    (Icc_subset_posCone (S.w₁_pos hε) hw) hvw
  consistent := fun σ _ _ hv => ⟨fun x => (S.Bhat_mem x (σ x) hε hv).1,
    fun x => (S.Bhat_mem x (σ x) hε hv).2⟩

/-- **Exercise 8.3.8** (p. 285): `v̂₁ < B̂(x, a, v̂₁)` and `B̂(x, a, v̂₂) ≤ v̂₂`. -/
theorem Bhat_bounds (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) :
    S.w₁ ε < S.Bhat x a (fun _ => S.w₁ ε) ∧ S.Bhat x a (fun _ => S.w₂) ≤ S.w₂ := by
  constructor
  · have e : (fun _ : X => S.w₁ ε) = fun _ => S.v₂ ε ^ S.κ := rfl
    rw [e, S.Bhat_pow x a (fun _ => S.v₂_pos hε), w₁]
    exact Real.rpow_lt_rpow_of_neg (S.B_pos x a fun _ => S.v₂_pos hε) (S.B_lt_v₂ x a hε) S.κ_neg
  · have e : (fun _ : X => S.w₂) = fun _ => S.v₁ ^ S.κ := rfl
    rw [e, S.Bhat_pow x a (fun _ => S.v₁_pos), w₂]
    exact Real.rpow_le_rpow_of_nonpos S.v₁_pos (S.v₁_le_B x a) S.κ_neg.le

/-! ### Concavity and global stability -/

/-- `ψ(t) = (r + βt^ζ)^{1/ζ}` is concave on `(0, ∞)` for `ζ < 0`: it is `β^{1/ζ}` times the map
`t ↦ (r/β + t^ζ)^{1/ζ}` of Exercise 7.1.8. -/
theorem concaveOn_psi (x : X) (a : A) :
    ConcaveOn ℝ (Ioi 0) fun t : ℝ => (S.r x a + S.β * t ^ S.ζ) ^ S.ζ⁻¹ := by
  have hθ : S.ζ⁻¹ ≠ 0 := inv_ne_zero S.ζ_neg.ne
  have hθ1 : ¬ (0 < S.ζ⁻¹ ∧ S.ζ⁻¹ ≤ 1) := fun h => absurd h.1 (not_lt.2 (inv_nonpos.2 S.ζ_neg.le))
  have hh : 0 ≤ S.r x a / S.β := div_nonneg (S.r_pos x a).le S.β_pos.le
  have hc := (concaveOn_powF hh hθ hθ1).smul (Real.rpow_nonneg S.β_pos.le S.ζ⁻¹)
  refine ⟨convex_Ioi 0, fun y hy z hz s t hs ht hst => ?_⟩
  have key : ∀ u : ℝ, 0 < u → (S.r x a + S.β * u ^ S.ζ) ^ S.ζ⁻¹ =
      S.β ^ S.ζ⁻¹ • powF (S.r x a / S.β) S.ζ⁻¹ u := fun u hu => by
    rw [smul_eq_mul, powF, inv_inv, ← Real.mul_rpow S.β_pos.le
      (add_nonneg hh (Real.rpow_nonneg hu.le _))]
    have hb : S.β * (S.r x a / S.β) = S.r x a := by field_simp [S.β_pos.ne']
    rw [mul_add, hb]
  have hyz : 0 < s • y + t • z := (convex_Ioi (0 : ℝ)) hy hz hs ht hst
  change s • (S.r x a + S.β * y ^ S.ζ) ^ S.ζ⁻¹ + t • (S.r x a + S.β * z ^ S.ζ) ^ S.ζ⁻¹ ≤
    (S.r x a + S.β * (s • y + t • z) ^ S.ζ) ^ S.ζ⁻¹
  rw [key y hy, key z hz, key _ hyz]
  exact hc.2 hy hz hs ht hst

/-- **Lemma 8.3.6** (p. 285): `B̂(x, a, ·)` is concave on `[v̂₁, v̂₂]`. -/
theorem concaveOn_Bhat (x : X) (a : A) {ε : ℝ} (hε : 0 < ε) :
    ConcaveOn ℝ (Icc (fun _ : X => S.w₁ ε) (fun _ => S.w₂)) (S.Bhat x a) := by
  have hsub := Icc_subset_posCone (X := X) (d := S.w₂) (S.w₁_pos hε)
  refine ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst => ?_⟩
  have hvp := hsub hv
  have hwp := hsub hw
  have hvw : s • v + t • w ∈ posCone X := convex_posCone hvp hwp hs ht hst
  -- concavity of the inner certainty equivalent
  have hg : s • S.g x a v + t • S.g x a w ≤ S.g x a (s • v + t • w) := by
    simp only [g, smul_eq_mul, Finset.mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun θ _ => ?_
    have := (concaveOn_kpR S.ξ_pos.ne' S.ξ_le_one (S.isMarkov_Pa θ a)).2 hvp hwp hs ht hst x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have hμ := (S.μ_dist x).nonneg θ
    nlinarith [mul_le_mul_of_nonneg_left this hμ]
  have hgv := S.g_pos x a hvp
  have hgw := S.g_pos x a hwp
  have hcomb : 0 < s • S.g x a v + t • S.g x a w := (convex_Ioi (0 : ℝ)) hgv hgw hs ht hst
  calc s • S.Bhat x a v + t • S.Bhat x a w
      ≤ (S.r x a + S.β * (s • S.g x a v + t • S.g x a w) ^ S.ζ) ^ S.ζ⁻¹ :=
        (S.concaveOn_psi x a).2 hgv hgw hs ht hst
    _ ≤ S.Bhat x a (s • v + t • w) :=
        ezAgg_monotoneOn (S.r_pos x a) S.β_pos.le S.ζ_neg.ne hcomb (S.g_pos x a hvw) hg

/-- `R̂` is a concave RDP (Exercise 8.3.8 and Lemma 8.3.6). -/
theorem toRDPHat_isConcaveRDP {ε : ℝ} (hε : 0 < ε) :
    (S.toRDPHat hε).IsConcaveRDP (fun _ => S.w₁ ε) (fun _ => S.w₂) :=
  ⟨fun _ => S.w₁_le_w₂ hε, rfl, fun x a _ => S.concaveOn_Bhat x a hε,
    RDP.exists_delta_concave _ (fun _ => S.w₁_le_w₂ hε) fun x a _ => (S.Bhat_bounds x a hε).1⟩

/-- **Proposition 8.3.5** (p. 285): the smooth ambiguity RDP is globally stable, by
Exercise 8.3.9, Proposition 8.1.3, Lemma 8.3.6 and Proposition 8.2.5; so Theorem 8.1.1 applies. -/
theorem toRDP_isGloballyStable {ε : ℝ} (hε : 0 < ε) : (S.toRDP hε).IsGloballyStable := by
  have hV : (S.toRDP hε).V = {v | ∀ x, v x ∈ Icc S.v₁ (S.v₂ ε)} :=
    Set.ext fun _ => ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
  have hV' : (S.toRDPHat hε).V = {v | ∀ x, v x ∈ Icc (S.w₁ ε) S.w₂} :=
    Set.ext fun _ => ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
  refine (RDP.isGloballyStable_iff_of_conj (R := S.toRDP hε) (R' := S.toRDPHat hε) rfl hV hV'
    (φ := fun t => t ^ S.κ) (ψ := fun t => t ^ S.κ⁻¹) (fun t ht => S.pow_mem ht)
    (fun t ht => S.pow_inv_mem hε ht)
    (fun t ht => Real.rpow_inv_rpow ((S.w₁_pos hε).trans_le ht.1).le S.κ_neg.ne)
    (fun t ht => Real.rpow_rpow_inv (S.v₁_pos.trans_le ht.1).le S.κ_neg.ne)
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (S.v₁_pos.trans_le ht.1)))
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ((S.w₁_pos hε).trans_le ht.1)))
    fun x a _ v hv => S.B_eq_conj x a (Icc_subset_posCone S.v₁_pos hv)).2 ?_
  exact (S.toRDPHat_isConcaveRDP hε).isGloballyStable

end SmoothAmbiguity

end SargentStachurski.RecursiveDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimization, shortest paths and negative discount rates

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.3.5 (pp. 286–289) and
Exercise 8.1.17 (p. 260).

Minimisation reduces to maximisation by reflection: `R⁻ = (Γ, −V, B⁻)` with
`B⁻(x, a, v) = −B(x, a, −v)` has policy operators `T⁻_σ v = −T_σ(−v)`, values `−v_σ`, value
function `−v_*` (`v_*` the min-value function), and its `v`-greedy policies are the
`(−v)`-min-greedy policies of `R`.

* Theorem 8.3.7 (min-optimality; the book defers its proof to §9.2.3): for globally stable `R`,
  (i) `v_*` is the unique solution of the min-Bellman equation in `V`, (ii) Bellman's principle of
  min-optimality, (iii) a min-optimal policy exists, (iv) min-HPI returns a min-optimal policy in
  finitely many steps; also min-VFI converges.
* Exercise 8.1.17: on a graph whose only cycle is the self-loop at `d` (stated with a rank function
  that strictly decreases along every edge out of `x ≠ d`), with `c ≥ 0` and `c(d, d) = 0`, the
  maximum cost-to-go `C`, the fixed point of `v ↦ max_{x'} {c(x, x') + v(x')}` reached in finitely
  many steps, gives the bounds `v₁ = 0`, `v₂ = C` of (8.20).
* Proposition 8.3.8: if moreover `c(x, x') > 0` for `x ≠ d`, the shortest path RDP on `[0, C]` is
  concave, hence globally stable, and Theorem 8.3.7 applies.
* Exercise 8.3.10 and Proposition 8.3.9: the same with `B(x, x', v) = c(x, x') + βv(x')`, `β > 1`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The reflected RDP `R⁻ = (Γ, −V, B⁻)` with `B⁻(x, a, v) = −B(x, a, −v)`. -/
def neg : RDP X A where
  Γ := R.Γ
  Γ_nonempty := R.Γ_nonempty
  V := {v | -v ∈ R.V}
  B := fun x a v => -R.B x a (-v)
  mono := fun x a ha v hv w hw hvw => neg_le_neg (R.mono x a ha (-w) hw (-v) hv (neg_le_neg hvw))
  consistent := fun σ hσ v hv => by
    change -(fun x => -R.B x (σ x) (-v)) ∈ R.V
    have : -(fun x => -R.B x (σ x) (-v)) = fun x => R.B x (σ x) (-v) := by
      funext x
      simp
    rw [this]
    exact R.consistent σ hσ (-v) hv

theorem neg_Tσ (σ : X → A) (v : X → ℝ) : R.neg.Tσ σ v = -R.Tσ σ (-v) := rfl

theorem neg_isFeasible {σ : X → A} : R.neg.IsFeasible σ ↔ R.IsFeasible σ := Iff.rfl

theorem neg_mem {v : X → ℝ} : v ∈ R.neg.V ↔ -v ∈ R.V := Iff.rfl

/-- Global stability is invariant under reflection. -/
theorem isGloballyStable_neg_iff : R.IsGloballyStable ↔ R.neg.IsGloballyStable := by
  have key : ∀ σ, R.IsFeasible σ →
      (GloballyStableOn (R.Tσ σ) R.V ↔ GloballyStableOn (R.neg.Tσ σ) R.neg.V) := fun σ hσ =>
    globallyStableOn_iff_of_conj (fun v => -v) (fun v => -v)
      (fun v hv => by change -(-v) ∈ R.V; rwa [neg_neg])
      (fun v hv => hv) (fun v _ => neg_neg v) (fun v _ => neg_neg v)
      continuous_neg.continuousOn continuous_neg.continuousOn (R.Tσ_mapsTo hσ)
      fun v _ => by rw [neg_Tσ, neg_neg]
  exact ⟨fun h σ hσ => (key σ hσ).1 (h σ hσ), fun h σ hσ => (key σ hσ).2 (h σ hσ)⟩

/-- Well-posedness is invariant under reflection, with `v⁻_σ = −v_σ`. -/
theorem WellPosed.neg {R : RDP X A} (hw : R.WellPosed) : R.neg.WellPosed := by
  intro σ hσ
  refine ⟨-R.vσ σ, ⟨by change -(-R.vσ σ) ∈ R.V; rw [neg_neg]; exact vσ_mem hw hσ, ?_⟩,
    fun u ⟨hu, hfix⟩ => ?_⟩
  · change -R.Tσ σ (-(-R.vσ σ)) = -R.vσ σ
    rw [neg_neg, (isFixedPt_vσ hw hσ).eq]
  · have h1 : IsFixedPt (R.Tσ σ) (-u) := by
      have := hfix.eq
      change -R.Tσ σ (-u) = u at this
      change R.Tσ σ (-u) = -u
      exact neg_eq_iff_eq_neg.1 this
    rw [← eq_vσ_of_isFixedPt hw hσ hu h1, neg_neg]

theorem neg_vσ {R : RDP X A} (hw : R.WellPosed) {σ : X → A} (hσ : R.IsFeasible σ) :
    R.neg.vσ σ = -R.vσ σ := by
  refine (eq_vσ_of_isFixedPt hw.neg hσ ?_ ?_).symm
  · change -(-R.vσ σ) ∈ R.V
    rw [neg_neg]
    exact vσ_mem hw hσ
  · change -R.Tσ σ (-(-R.vσ σ)) = -R.vσ σ
    rw [neg_neg, (isFixedPt_vσ hw hσ).eq]

/-- A `v`-min-greedy policy (§8.3.5): `σ(x)` minimises `B(x, ·, v)` over `Γ(x)`. -/
def IsMinGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  R.IsFeasible σ ∧ ∀ x, ∀ a ∈ R.Γ x, R.B x (σ x) v ≤ R.B x a v

theorem isMinGreedy_iff (v : X → ℝ) (σ : X → A) : R.IsMinGreedy v σ ↔ R.neg.IsGreedy (-v) σ := by
  refine and_congr Iff.rfl (forall_congr' fun x => forall₂_congr fun a _ => ?_)
  change _ ↔ -R.B x a (-(-v)) ≤ -R.B x (σ x) (-(-v))
  rw [neg_neg, neg_le_neg_iff]

/-- The Bellman min-operator `(Tv)(x) = min_{a ∈ Γ(x)} B(x, a, v)`. -/
noncomputable def Tmin (v : X → ℝ) : X → ℝ := fun x =>
  (R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a v

theorem neg_T (v : X → ℝ) : R.neg.T v = -R.Tmin (-v) := by
  funext x
  change (R.Γ x).sup' (R.Γ_nonempty x) (fun a => -R.B x a (-v)) =
    -(R.Γ x).inf' (R.Γ_nonempty x) fun a => R.B x a (-v)
  refine le_antisymm (Finset.sup'_le _ _ fun a ha => neg_le_neg (Finset.inf'_le _ ha)) ?_
  rw [neg_le]
  exact Finset.le_inf' _ _ fun a ha => neg_le.1 (Finset.le_sup' (fun a => -R.B x a (-v)) ha)

theorem iterate_neg_T (v : X → ℝ) (k : ℕ) : R.neg.T^[k] v = -R.Tmin^[k] (-v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, neg_T, ih, neg_neg]

variable [DecidableEq X] [DecidableEq A]

/-- The min-value function `v_* = ⋀_σ v_σ` (§8.3.5). -/
noncomputable def vmin : X → ℝ := fun x =>
  univ.inf' (univ_nonempty_iff.2 R.policy_nonempty) fun σ : R.Policy => R.vσ σ.1 x

/-- A min-optimal policy: `v_σ = v_*`. -/
def IsMinOptimal (σ : X → A) : Prop := R.IsFeasible σ ∧ R.vσ σ = R.vmin

theorem neg_vstar {R : RDP X A} (hw : R.WellPosed) : R.neg.vstar = -R.vmin := by
  funext x
  refine le_antisymm (Finset.sup'_le _ _ fun τ _ => ?_) ?_
  · rw [neg_vσ hw τ.2, Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
    exact Finset.inf'_le (fun σ : R.Policy => R.vσ σ.1 x) (mem_univ (⟨τ.1, τ.2⟩ : R.Policy))
  · rw [Pi.neg_apply, neg_le]
    refine Finset.le_inf' _ _ fun σ _ => ?_
    rw [neg_le]
    have := Finset.le_sup' (fun τ : R.neg.Policy => R.neg.vσ τ.1 x)
      (mem_univ (⟨σ.1, σ.2⟩ : R.neg.Policy))
    simp only [neg_vσ hw σ.2, Pi.neg_apply] at this
    exact this

theorem isMinOptimal_iff {R : RDP X A} (hw : R.WellPosed) (σ : X → A) :
    R.IsMinOptimal σ ↔ R.neg.IsOptimal σ := by
  constructor
  · rintro ⟨hσ, h⟩
    exact ⟨hσ, by rw [neg_vσ hw hσ, neg_vstar hw, h]⟩
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, ?_⟩
    rw [neg_vσ hw hσ, neg_vstar hw] at h
    exact neg_injective h

omit [DecidableEq X] [DecidableEq A] in
/-- The min-HPI step: `σₖ₊₁` (HPI for `R⁻`) is `v_{σₖ}`-min-greedy for `R`, so the HPI sequence of
`R⁻` is min-HPI for `R`. -/
theorem minHpi_isMinGreedy {R : RDP X A} (hw : R.WellPosed) (σ : R.neg.Policy) (k : ℕ) :
    R.IsMinGreedy (R.vσ (R.neg.hpiPolicy σ k).1) (R.neg.hpiPolicy σ (k + 1)).1 := by
  rw [isMinGreedy_iff, ← neg_vσ hw (R.neg.hpiPolicy σ k).2]
  exact R.neg.isGreedy_greedy _

/-- **Theorem 8.3.7 (min-optimality)** (p. 286): for a globally stable RDP, (i) `v_*` is the unique
solution of the min-Bellman equation in `V`, (ii) Bellman's principle of min-optimality holds,
(iii) a min-optimal policy exists and (iv) min-HPI returns a min-optimal policy in finitely many
steps. -/
theorem minOptimality {R : RDP X A} (hR : R.IsGloballyStable) :
    (R.vmin ∈ R.V ∧ IsFixedPt R.Tmin R.vmin ∧ ∀ v ∈ R.V, IsFixedPt R.Tmin v → v = R.vmin) ∧
      (∀ σ, R.IsFeasible σ → (R.IsMinOptimal σ ↔ R.IsMinGreedy R.vmin σ)) ∧
      (∃ σ, R.IsMinOptimal σ) ∧
      ∀ σ : R.neg.Policy, ∃ k, R.vσ (R.neg.hpiPolicy σ (k + 1)).1 = R.vσ (R.neg.hpiPolicy σ k).1 ∧
        R.IsMinOptimal (R.neg.hpiPolicy σ (k + 1)).1 := by
  have hw := hR.wellPosed
  have hN := (isGloballyStable_neg_iff R).1 hR
  obtain ⟨⟨hmem, hfix, huniq⟩, hpo, ⟨σ0, hσ0⟩, hhpi, -⟩ := optimality_of_globallyStable hN
  rw [neg_vstar hw] at hmem hfix huniq
  refine ⟨⟨?_, ?_, fun v hv hv' => ?_⟩, fun σ hσ => ?_, ⟨σ0, (isMinOptimal_iff hw σ0).2 hσ0⟩,
    fun σ => ?_⟩
  · have : -(-R.vmin) ∈ R.V := hmem
    rwa [neg_neg] at this
  · have h := hfix.eq
    rw [neg_T, neg_neg] at h
    exact neg_injective h
  · have h1 : -v ∈ R.neg.V := by change -(-v) ∈ R.V; rwa [neg_neg]
    have h2 : IsFixedPt R.neg.T (-v) := by
      change R.neg.T (-v) = -v
      rw [neg_T, neg_neg, hv'.eq]
    exact neg_injective (huniq _ h1 h2)
  · rw [isMinOptimal_iff hw, hpo σ hσ, neg_vstar hw, isMinGreedy_iff]
  · obtain ⟨k, hk, hopt⟩ := hhpi σ
    refine ⟨k, ?_, (isMinOptimal_iff hw _).2 hopt⟩
    have e1 := neg_vσ hw (R.neg.hpiPolicy σ (k + 1)).2
    have e2 := neg_vσ hw (R.neg.hpiPolicy σ k).2
    simp only [hpiValue] at hk
    rw [e1, e2] at hk
    exact neg_injective hk

/-- Min-VFI converges from any `v_σ` (the `m = 1` case of the min-OPI result noted after
Theorem 8.3.7). -/
theorem tendsto_iterate_Tmin {R : RDP X A} (hR : R.IsGloballyStable) {σ : X → A}
    (hσ : R.IsFeasible σ) : Tendsto (fun k => R.Tmin^[k] (R.vσ σ)) atTop (𝓝 R.vmin) := by
  have hw := hR.wellPosed
  have h := (tendsto_iterate_T_vσ ((isGloballyStable_neg_iff R).1 hR) hσ).neg
  rw [neg_vstar hw, neg_neg, neg_vσ hw hσ] at h
  simpa only [iterate_neg_T, neg_neg] using h

end RDP

/-! ### Shortest paths and negative discount rates (§8.3.5.1–§8.3.5.2) -/

variable {X : Type*} [Fintype X] (O : X → Finset X) (hO : ∀ x, (O x).Nonempty) (c : X → X → ℝ)
  (β : ℝ)

/-- The maximum-cost Bellman operator `(Mv)(x) = max_{x' ∈ O(x)} {c(x, x') + βv(x')}`. -/
noncomputable def maxCost (v : X → ℝ) : X → ℝ := fun x =>
  (O x).sup' (hO x) fun x' => c x x' + β * v x'

/-- The maximum cost-to-go `C = M^N 0`, `N = max rank`: under the hypotheses of Exercise 8.1.17 the
iteration has stopped by then, and `C(x)` is the largest cost of any path from `x` to `d`. -/
noncomputable def maxCostToGo (rank : X → ℕ) : X → ℝ := (maxCost O hO c β)^[univ.sup rank] 0

variable {O hO c β} {d : X} (hOd : O d = {d}) (hcd : c d d = 0) (hc : ∀ x x', 0 ≤ c x x')
  (hβ : 0 ≤ β) {rank : X → ℕ} (hrank : ∀ x, x ≠ d → ∀ x' ∈ O x, rank x' < rank x)
include hOd hcd

omit [Fintype X] in
theorem maxCost_apply_d (v : X → ℝ) : maxCost O hO c β v d = β * v d := by
  have hd : d ∈ O d := by rw [hOd]; exact mem_singleton_self d
  refine le_antisymm (Finset.sup'_le _ _ fun x' hx' => ?_) ?_
  · rw [hOd, Finset.mem_singleton] at hx'
    rw [hx', hcd, zero_add]
  · have := Finset.le_sup' (fun x' => c d x' + β * v x') hd
    simp only [hcd, zero_add] at this
    exact this

omit [Fintype X] in
theorem iterate_maxCost_d (k : ℕ) : (maxCost O hO c β)^[k] 0 d = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', maxCost_apply_d hOd hcd, ih, mul_zero]

omit [Fintype X] in
include hrank in
/-- The iteration stabilises: `M^{k+1}0 = M^k 0` at `x` once `k ≥ rank x`. -/
theorem iterate_maxCost_stable :
    ∀ n, ∀ x, rank x ≤ n → ∀ k, n ≤ k →
      (maxCost O hO c β)^[k + 1] 0 x = (maxCost O hO c β)^[k] 0 x := by
  intro n
  induction n with
  | zero =>
    intro x hx k _
    by_cases hxd : x = d
    · subst hxd
      rw [iterate_maxCost_d hOd hcd, iterate_maxCost_d hOd hcd]
    · obtain ⟨x', hx'⟩ := hO x
      exact absurd (hrank x hxd x' hx') (by omega)
  | succ n ih =>
    intro x hx k hk
    by_cases hxd : x = d
    · subst hxd
      rw [iterate_maxCost_d hOd hcd, iterate_maxCost_d hOd hcd]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      conv_lhs => rw [iterate_succ_apply']
      conv_rhs => rw [iterate_succ_apply']
      refine Finset.sup'_congr (hO x) rfl fun x' hx' => ?_
      rw [ih x' (by have := hrank x hxd x' hx'; omega) j (by omega)]

include hrank in
/-- `C = MC`: the maximum cost-to-go solves the maximum-cost Bellman equation. -/
theorem maxCost_maxCostToGo : maxCost O hO c β (maxCostToGo O hO c β rank) =
    maxCostToGo O hO c β rank := by
  funext x
  have := iterate_maxCost_stable (hO := hO) (β := β) hOd hcd hrank _ x
    (Finset.le_sup (mem_univ x)) _ le_rfl
  rw [iterate_succ_apply'] at this
  exact this

omit hOd hcd in
include hc hβ in
theorem maxCostToGo_nonneg : 0 ≤ maxCostToGo O hO c β rank := by
  have hk : ∀ k, 0 ≤ (maxCost O hO c β)^[k] 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [iterate_succ_apply']
      intro x
      obtain ⟨x', hx'⟩ := hO x
      exact (add_nonneg (hc x x') (mul_nonneg hβ (ih x'))).trans
        (Finset.le_sup' (fun x' => c x x' + β * (maxCost O hO c β)^[k] 0 x') hx')
  exact hk _

theorem maxCostToGo_d : maxCostToGo O hO c β rank d = 0 := iterate_maxCost_d hOd hcd _

include hc hβ hrank in
/-- **Exercise 8.1.17** (p. 260), and Exercise 8.3.10 for `β > 1`: the RDP `B(x, x', v) =
c(x, x') + βv(x')` satisfies (8.20) with `v₁ = 0` and `v₂ = C`, and `C` is finite. -/
theorem pathRDP_isBoundedBy :
    (pathRDP O hO c hβ).IsBoundedBy 0 (maxCostToGo O hO c β rank) := by
  refine ⟨maxCostToGo_nonneg hc hβ, fun _ _ => mem_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · change 0 ≤ c x a + β * 0
    rw [mul_zero, add_zero]
    exact hc x a
  · change c x a + β * maxCostToGo O hO c β rank a ≤ maxCostToGo O hO c β rank x
    rw [← maxCost_maxCostToGo hOd hcd hrank]
    nth_rewrite 2 [← maxCost_maxCostToGo hOd hcd hrank]
    exact Finset.le_sup' (fun x' => c x x' + β * maxCost O hO c β (maxCostToGo O hO c β rank) x')
      ha

include hc hβ hrank in
/-- **Propositions 8.3.8 and 8.3.9** (pp. 287–289): if also `c(x, x') > 0` for `x ≠ d`, the RDP
`(O, [0, C], B)` with `B(x, x', v) = c(x, x') + βv(x')` (shortest paths: `β = 1`; negative discount
rate: `β > 1`) is concave, hence globally stable; so its min-value function `v_*` is the unique
solution of `v(x) = min_{x' ∈ O(x)} {c(x, x') + βv(x')}` in `[0, C]`, and a policy is min-optimal
iff it is `v_*`-min-greedy. -/
theorem pathRDP_minOptimal [DecidableEq X] (hcpos : ∀ x, x ≠ d → ∀ x' ∈ O x, 0 < c x x') :
    let R := (pathRDP O hO c hβ).restrictIcc (pathRDP_isBoundedBy (hO := hO) hOd hcd hc hβ hrank)
    R.IsConcaveRDP 0 (maxCostToGo O hO c β rank) ∧ R.IsGloballyStable ∧
      (R.vmin ∈ R.V ∧ IsFixedPt R.Tmin R.vmin ∧ ∀ v ∈ R.V, IsFixedPt R.Tmin v → v = R.vmin) ∧
      ∀ σ, R.IsFeasible σ → (R.IsMinOptimal σ ↔ R.IsMinGreedy R.vmin σ) := by
  intro R
  have hb := pathRDP_isBoundedBy (hO := hO) hOd hcd hc hβ hrank
  set C := maxCostToGo O hO c β rank
  -- (8.56): `c(x, x') ≥ δC(x)`
  set w : X → ℝ := fun x => if x = d then 1 else (O x).inf' (hO x) (c x)
  have hw : ∀ x, (0 : X → ℝ) x < w x := fun x => by
    by_cases hxd : x = d
    · simp [w, hxd]
    · simp only [w, hxd, ↓reduceIte, Pi.zero_apply]
      obtain ⟨a, ha, hmin⟩ := (O x).exists_min_image (c x) (hO x)
      rw [show (O x).inf' (hO x) (c x) = c x a from
        le_antisymm (Finset.inf'_le _ ha) (Finset.le_inf' _ _ hmin)]
      exact hcpos x hxd a ha
  obtain ⟨δ, hδ, hδw⟩ := exists_delta_of_lt hb.1 hw
  have hconc : R.IsConcaveRDP 0 C := by
    refine ⟨hb.1, rfl, fun x a _ => ⟨convex_Icc _ _, fun v _ v' _ s t _ _ hst => le_of_eq ?_⟩,
      δ, hδ, fun x a ha => ?_⟩
    · change s * (c x a + β * v a) + t * (c x a + β * v' a) = c x a + β * (s * v a + t * v' a)
      obtain rfl : t = 1 - s := by linarith
      ring
    · change 0 + δ * (C x - 0) ≤ c x a + β * 0
      rw [mul_zero, add_zero, zero_add, sub_zero]
      by_cases hxd : x = d
      · subst hxd
        rw [show C x = 0 from maxCostToGo_d hOd hcd, mul_zero]
        exact hc _ a
      · have h1 := hδw x
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          zero_add, sub_zero, w, hxd, ↓reduceIte] at h1
        exact h1.trans (Finset.inf'_le _ ha)
  have hGS := hconc.isGloballyStable
  obtain ⟨h1, h2, -, -⟩ := RDP.minOptimality hGS
  exact ⟨hconc, hGS, h1, h2⟩

end SargentStachurski.RecursiveDecisionProcesses

set_option linter.style.longLine false
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.rowsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsDistribution
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsDistribution.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsDistribution.nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsDistribution.sum_eq_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.mulVec_apply_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.mul
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.pow
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.mulVec_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.GloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.iterate_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.RecursiveDecisionProcesses.fixedPt_le_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_fixedPt_of_le_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.isContractionOn_of_blackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.pow_nonneg_entries
#print axioms SargentStachurski.RecursiveDecisionProcesses.pow_le_pow_entries
#print axioms SargentStachurski.RecursiveDecisionProcesses.complexify
#print axioms SargentStachurski.RecursiveDecisionProcesses.complexify_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.complexify_pow
#print axioms SargentStachurski.RecursiveDecisionProcesses.complexify_transpose
#print axioms SargentStachurski.RecursiveDecisionProcesses.nnnorm_complexify
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_complexify
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad
#print axioms SargentStachurski.RecursiveDecisionProcesses.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_norm_pow_rpow
#print axioms SargentStachurski.RecursiveDecisionProcesses.eventually_norm_pow_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_norm_pow_zero
#print axioms SargentStachurski.RecursiveDecisionProcesses.summable_pow
#print axioms SargentStachurski.RecursiveDecisionProcesses.one_sub_mul_tsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.tsum_mul_one_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.neumann_series
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_transpose
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_le_norm_of_abs_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_le_of_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.rowsum_abs_le_norm
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_entry_le_norm
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_le_norm
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.eventually_abs_entry_pow_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.resPartial
#print axioms SargentStachurski.RecursiveDecisionProcesses.res
#print axioms SargentStachurski.RecursiveDecisionProcesses.res_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.RecursiveDecisionProcesses.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.resPartial_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.summable_res_entry
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_resPartial_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.smul_one_sub_mul_res
#print axioms SargentStachurski.RecursiveDecisionProcesses.res_mul_smul_one_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.res_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.inv_le_res_diag
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.smul_one_sub_mul_res_real
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_res_complexify_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_res_entry_gt
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCompact_simplex
#print axioms SargentStachurski.RecursiveDecisionProcesses.perron_frobenius
#print axioms SargentStachurski.RecursiveDecisionProcesses.perron_frobenius_left
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_specRad_of_colsum_ge
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_le_of_colsum_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_le_of_rowsum_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.exists_stationary
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible
#print axioms SargentStachurski.RecursiveDecisionProcesses.irreducible_of_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.transpose
#print axioms SargentStachurski.RecursiveDecisionProcesses.pow_mulVec_eq_of_mulVec_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.pos_of_mulVec_eq_smul
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.specRad_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.exists_pos_eigenvector
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.exists_pos_left_eigenvector
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms SargentStachurski.RecursiveDecisionProcesses.discountOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.discountOp_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.discountOp_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.discountOp_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_smul_isMarkov
#print axioms SargentStachurski.RecursiveDecisionProcesses.summable_pow_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.summable_pow_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.mulVec_tsum_pow_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.tsum_pow_mulVec_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.eq_of_eq_add_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.inv_mulVec_eq_add
#print axioms SargentStachurski.RecursiveDecisionProcesses.inv_mulVec_eq_tsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.eq_add_mulVec_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_lt_one_iff_existsUnique_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_of_iterate_contraction
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_of_iterate_contraction_univ
#print axioms SargentStachurski.RecursiveDecisionProcesses.affineOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.affineOp_iterate_sub
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_isContractionOn_iterate_affineOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_affineOp
#print axioms SargentStachurski.RecursiveDecisionProcesses.isFixedPt_affineOp_inv
#print axioms SargentStachurski.RecursiveDecisionProcesses.mulVec_le_mulVec_of_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_abs_fun
#print axioms SargentStachurski.RecursiveDecisionProcesses.norm_le_norm_of_abs_le_fun
#print axioms SargentStachurski.RecursiveDecisionProcesses.abs_iterate_sub_le_pow_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_of_abs_sub_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.GloballyStableOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_univ_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.GloballyStableOn.existsUnique
#print axioms SargentStachurski.RecursiveDecisionProcesses.GloballyStableOn.of_conj
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_iff_of_conj
#print axioms SargentStachurski.RecursiveDecisionProcesses.iterate_le_iterate_of_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.knaster_tarski
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_continuum_fixedPts
#print axioms SargentStachurski.RecursiveDecisionProcesses.du_concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_delta_of_lt
#print axioms SargentStachurski.RecursiveDecisionProcesses.du_concave_of_lt
#print axioms SargentStachurski.RecursiveDecisionProcesses.neg_mem_Icc_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_of_reflect
#print axioms SargentStachurski.RecursiveDecisionProcesses.du_convex
#print axioms SargentStachurski.RecursiveDecisionProcesses.du_convex_of_lt
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_comp
#print axioms SargentStachurski.RecursiveDecisionProcesses.posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.convex_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.exists_pos_row
#print axioms SargentStachurski.RecursiveDecisionProcesses.mulVec_pos_of_row
#print axioms SargentStachurski.RecursiveDecisionProcesses.Irreducible.of_pos_mul
#print axioms SargentStachurski.RecursiveDecisionProcesses.powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.powF_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.powF_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.hasDerivAt_powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.continuousOn_powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.differentiableOn_powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.convexOn_powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_powF
#print axioms SargentStachurski.RecursiveDecisionProcesses.powG
#print axioms SargentStachurski.RecursiveDecisionProcesses.powG_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.powG_mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.powG_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.convexOn_powG
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_powG
#print axioms SargentStachurski.RecursiveDecisionProcesses.specRad_rpow_lt_one_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.not_isFixedPt_powG
#print axioms SargentStachurski.RecursiveDecisionProcesses.scalar_bounds
#print axioms SargentStachurski.RecursiveDecisionProcesses.powG_smul_eigen
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_thresholds
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_powG_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.exists_interval
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_powG
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_powG_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.kleinmanA
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsKleinmanSol
#print axioms SargentStachurski.RecursiveDecisionProcesses.isKleinmanSol_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.existsUnique_kleinmanSol_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.const
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.isCertEquiv
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCertEquiv_mulVec_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.mulVec_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.zero_and_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsCertEquiv.convex_comb
#print axioms SargentStachurski.RecursiveDecisionProcesses.PosHomogeneous
#print axioms SargentStachurski.RecursiveDecisionProcesses.Superadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.Subadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.ConstSubadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.mulVec_properties
#print axioms SargentStachurski.RecursiveDecisionProcesses.nonexpansive_of_constSubadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.convexOn_of_subadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_of_superadditive
#print axioms SargentStachurski.RecursiveDecisionProcesses.entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.entR_add_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCertEquiv_entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.constSubadditive_entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.log_sum_exp_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.kpR_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCertEquiv_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.posHomogeneous_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_rpow_normalize
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_rpow_add_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.le_sum_rpow_add
#print axioms SargentStachurski.RecursiveDecisionProcesses.convexOn_rpow_of_neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.subadditive_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.superadditive_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.smul_mem_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.convexOn_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.concaveOn_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.condCdf
#print axioms SargentStachurski.RecursiveDecisionProcesses.quantR
#print axioms SargentStachurski.RecursiveDecisionProcesses.isLeast_quantR
#print axioms SargentStachurski.RecursiveDecisionProcesses.isCertEquiv_quantR
#print axioms SargentStachurski.RecursiveDecisionProcesses.quantR_add_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.constSubadditive_quantR
#print axioms SargentStachurski.RecursiveDecisionProcesses.MonotoneKernel
#print axioms SargentStachurski.RecursiveDecisionProcesses.MonotoneKernel.antitone
#print axioms SargentStachurski.RecursiveDecisionProcesses.monotone_entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.monotone_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsAggregator
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsAggregator.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsAggregator.values
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsAggregator.mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsAggregator.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.leontief
#print axioms SargentStachurski.RecursiveDecisionProcesses.uzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.cesAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.additive
#print axioms SargentStachurski.RecursiveDecisionProcesses.cesUzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.additive_eq_uzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.additive_eq_cesAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.isAggregator_leontief
#print axioms SargentStachurski.RecursiveDecisionProcesses.isAggregator_uzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.isAggregator_additive
#print axioms SargentStachurski.RecursiveDecisionProcesses.isAggregator_cesUzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.isAggregator_cesAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans_mapsTo_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans_additive_entR
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans_cesAgg_kpR
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans_additive_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.ces_eis
#print axioms SargentStachurski.RecursiveDecisionProcesses.iterate_additive_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.additive_lifetimeValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.monotone_of_globallyStableOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.monotone_koopmans_fixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsBlackwellAgg
#print axioms SargentStachurski.RecursiveDecisionProcesses.isBlackwellAgg_additive
#print axioms SargentStachurski.RecursiveDecisionProcesses.isBlackwellAgg_leontief
#print axioms SargentStachurski.RecursiveDecisionProcesses.isContractionOn_koopmans
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_koopmans
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_riskSensitive
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_leontief
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_quantile
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStable_leontief_quantile
#print axioms SargentStachurski.RecursiveDecisionProcesses.koopmans_uzawa_mulVec
#print axioms SargentStachurski.RecursiveDecisionProcesses.uzawa_lifetimeValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.irreducible_uzawa
#print axioms SargentStachurski.RecursiveDecisionProcesses.uzawa_no_pos_fixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.nonnegCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_uzawa_concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezK
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezK_eq_koopmans
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezK_apply_ez
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezK_mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.powMap
#print axioms SargentStachurski.RecursiveDecisionProcesses.powMap_mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.powMap_inv
#print axioms SargentStachurski.RecursiveDecisionProcesses.powMap_inv'
#print axioms SargentStachurski.RecursiveDecisionProcesses.continuousOn_powMap
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezB
#print axioms SargentStachurski.RecursiveDecisionProcesses.powMap_ezK
#print axioms SargentStachurski.RecursiveDecisionProcesses.irreducible_ezB
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_ezK_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.globallyStableOn_ez
#print axioms SargentStachurski.RecursiveDecisionProcesses.ez_deriv_tendsto_atTop
#print axioms SargentStachurski.RecursiveDecisionProcesses.monotone_ez_lifetimeValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Γ_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.V
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.consistent
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsFeasible
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Policy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.defaultPolicy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.policy_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.WellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContinuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_spec
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isFixedPt_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.tendsto_iterate_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.B_le_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_le_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.greedy_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreedy_greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.greedyPolicy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreedy_iff_Tσ_eq_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_eq_T_of_isGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.T_mapsTo
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.T_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.T_apply_eq_sup'
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGreatest_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.antiGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isLeast_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.iterate_T_succ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.iterate_Tσ_succ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.iterate_T_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.iterate_Tσ_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_le_vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsOptimal
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.PrincipleOfOptimality
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.howard
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.opiW
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.hpiPolicy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.hpiValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.hpiValue_succ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.opiValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.opiValue_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.nonstationary_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Comparable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_le_of_Tσ_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.le_vσ_of_le_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsGloballyStable.comparable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_le_vσ_greedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.eq_vσ_greedy_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_le_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.hpiValue_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_hpiValue_succ_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isFixedPt_T_hpiValue
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vstar_spec
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.principleOfOptimality
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_isOptimal
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.hpi_terminates
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.tendsto_iterate_T_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.opiValue_spec
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.opi_converges
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.optimality_of_globallyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.nonstationary_le_vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tσ_mapsTo_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.restrictIcc
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_fixedPt_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vσ_mem_Icc
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.comparable_of_bounded
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.optimality_of_bounded
#print axioms SargentStachurski.RecursiveDecisionProcesses.continuousOn_comp_pi
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGloballyStable_iff_of_conj
#print axioms SargentStachurski.RecursiveDecisionProcesses.kernelAt
#print axioms SargentStachurski.RecursiveDecisionProcesses.kernelAt_apply
#print axioms SargentStachurski.RecursiveDecisionProcesses.isMarkov_kernelAt
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.Γ_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.β_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.β_lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.r
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.P
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.P_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.P_rowsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isMarkov_P
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.Pσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isMarkov_Pσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.rσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.toRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.toRDP_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.toRDP_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.cakeEating
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.stokeyLucas
#print axioms SargentStachurski.RecursiveDecisionProcesses.stokeyLucas_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.riskSensitive
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.riskSensitive_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.quantile
#print axioms SargentStachurski.RecursiveDecisionProcesses.ezAgg_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZin
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZin_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.pathRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.pathRDP_not_wellPosed
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting.isContractionOn_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting.isContractionOn_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting.isContinuous
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting.isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsContracting.norm_vstar_sub_vσ_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.SatisfiesBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.SatisfiesBlackwell.isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.SatisfiesBlackwell.isBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.satisfiesBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.vσ_eq
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping_satisfiesBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.stopping_isBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount_satisfiesBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.savings_satisfiesBlackwell
#print axioms SargentStachurski.RecursiveDecisionProcesses.quantileJobSearch
#print axioms SargentStachurski.RecursiveDecisionProcesses.quantileJobSearch_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.riskSensitiveJobSearch
#print axioms SargentStachurski.RecursiveDecisionProcesses.riskSensitiveJobSearch_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.optimalDefault
#print axioms SargentStachurski.RecursiveDecisionProcesses.optimalDefault_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.riskSensitive_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.riskSensitive_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.quantile_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.quantile_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Lσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsEventuallyContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsEventuallyContracting.isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount_isEventuallyContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.absReward
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.withDiscount_isBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmExit
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmExit_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.firmExit_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsConvexRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsConcaveRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_delta_concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.exists_delta_convex
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.concaveOn_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.convexOn_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsConcaveRDP.isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsConvexRDP.isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.isBoundedBy_eps
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.toRDP_B_combo
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.restrict_isConvex_isConcave
#print axioms SargentStachurski.RecursiveDecisionProcesses.iInf_add_iInf_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.add_mul_iInf
#print axioms SargentStachurski.RecursiveDecisionProcesses.advB
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.eps_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.lower
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.le
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.upper
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.concave
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.lower_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.bddBelow
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.le_advB
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.advB_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.advB_mono
#print axioms SargentStachurski.RecursiveDecisionProcesses.AdvConditions.advB_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.adversarialRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.adversarialRDP_isConcaveRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.adversarialRDP_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Γ_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Dset
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Dset_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.β_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.β_lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.r
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.r₁
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.r₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.r_bounds
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.P
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.P_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.P_rowsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Bd
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.v₁
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.v₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.Bd_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.advConditions
#print axioms SargentStachurski.RecursiveDecisionProcesses.PerturbedMDP.isConcaveRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.robustMDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.robustMDP_advB
#print axioms SargentStachurski.RecursiveDecisionProcesses.robustMDP_isConcaveRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.bddBelow_sum_mul_dist
#print axioms SargentStachurski.RecursiveDecisionProcesses.robustJobSearch
#print axioms SargentStachurski.RecursiveDecisionProcesses.robustJobSearch_isContracting
#print axioms SargentStachurski.RecursiveDecisionProcesses.penalty_absorbed
#print axioms SargentStachurski.RecursiveDecisionProcesses.klDiv
#print axioms SargentStachurski.RecursiveDecisionProcesses.AbsCont
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_exp_mul_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_mul_sub_klDiv_le
#print axioms SargentStachurski.RecursiveDecisionProcesses.gibbs
#print axioms SargentStachurski.RecursiveDecisionProcesses.isDistribution_gibbs
#print axioms SargentStachurski.RecursiveDecisionProcesses.absCont_gibbs
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_mul_sub_klDiv_gibbs
#print axioms SargentStachurski.RecursiveDecisionProcesses.klDuality
#print axioms SargentStachurski.RecursiveDecisionProcesses.entropic_isLeast
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.riskSensitive_B_eq_robust
#print axioms SargentStachurski.RecursiveDecisionProcesses.IsMarkov.exists_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.ezB_kernelAt_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.ezB_kernelAt_row
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZinHat
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZinHat_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZinHat_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZin_B_eq_conj
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZin_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.MDP.epsteinZin_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.smoothB
#print axioms SargentStachurski.RecursiveDecisionProcesses.smoothB_neutral
#print axioms SargentStachurski.RecursiveDecisionProcesses.sum_dist_mul_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.mk
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Γ_nonempty
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.β
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.β_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.β_lt_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r₁
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r₁_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r₁_le_r₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r_bounds
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.P
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.P_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.P_rowsum
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.μ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.μ_dist
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.α
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.κ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.κ_lt_γ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.γ_neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.α_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.κ_neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.r_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ξ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ζ
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ξ_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ξ_le_one
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ζ_neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Pa
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.isMarkov_Pa
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.g
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.g_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.inner_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.ce_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat_pow
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_eq_conj
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.pow_mem_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_monotoneOn
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_const
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₁
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.one_sub_β_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₁_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₁_le_v₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₂_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.v₁_le_B
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_lt_v₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Icc_subset_posCone
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.B_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.toRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.w₁
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.w₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.w₁_pos
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.w₁_le_w₂
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.pow_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.pow_inv_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.toRDPHat
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.Bhat_bounds
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.concaveOn_psi
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.concaveOn_Bhat
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.toRDPHat_isConcaveRDP
#print axioms SargentStachurski.RecursiveDecisionProcesses.SmoothAmbiguity.toRDP_isGloballyStable
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_Tσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_isFeasible
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_mem
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isGloballyStable_neg_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.WellPosed.neg
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_vσ
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsMinGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isMinGreedy_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.Tmin
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.iterate_neg_T
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.vmin
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.IsMinOptimal
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.neg_vstar
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.isMinOptimal_iff
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.minHpi_isMinGreedy
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.minOptimality
#print axioms SargentStachurski.RecursiveDecisionProcesses.RDP.tendsto_iterate_Tmin
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCost
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCostToGo
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCost_apply_d
#print axioms SargentStachurski.RecursiveDecisionProcesses.iterate_maxCost_d
#print axioms SargentStachurski.RecursiveDecisionProcesses.iterate_maxCost_stable
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCost_maxCostToGo
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCostToGo_nonneg
#print axioms SargentStachurski.RecursiveDecisionProcesses.maxCostToGo_d
#print axioms SargentStachurski.RecursiveDecisionProcesses.pathRDP_isBoundedBy
#print axioms SargentStachurski.RecursiveDecisionProcesses.pathRDP_minOptimal
