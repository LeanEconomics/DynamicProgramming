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
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 7 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

The spectral radius `ρ(A)` of Vol. 1 (1.15) and the facts about it that
Chapter 6 uses: Gelfand's formula (Lemma 1.2.2), the eventual bound
`‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1), invariance
under transposition, monotonicity in the entries (Exercise 2.2.28), and the
row-sum characterisations of the ℓ∞ operator norm. These are the results of
the `FiniteStates/OperatorsFixedPoints` project restated for a matrix indexed by
an arbitrary finite type `X`, as Chapter 6 needs them on product state spaces
`Y × Z`; each chapter project is self-contained.
-/

open Filter Topology Matrix Finset

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

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
unique stationary distribution, and it is everywhere positive.

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear valuation and eventual contractions, restated

Facts from Vol. 1, Chapter 6 used in Chapter 7, restated from the
`FiniteStates/StochasticDiscounting` project: the discount operator, Theorem 6.1.1
(`v = h + Lv` has the unique solution `(I − L)⁻¹h = ∑ₜ Lᵗh` when `ρ(L) < 1`),
`ρ(βP) = β`, Lemma 6.1.4 (for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
unique positive solution), Theorem 6.1.5 (eventual contractions are globally
stable), Example 6.1.2 (affine maps) and Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fixed points of order-preserving maps: Knaster–Tarski and Du

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.1–§7.1.2.2
(pp. 213–217).

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concavity and stability in one dimension

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.2.1 (pp. 214–216).

* Proposition 7.1.2: an increasing concave self-map `g` of `(0, ∞)` is globally
  stable if every `x > 0` lies between an `a` with `a < g(a)` and a `b` with
  `g(b) ≤ b`. Orbits are monotone and bounded, concave functions are continuous on
  open intervals, so orbits converge to fixed points; and concavity together with
  `a < g(a)` rules out two fixed points.
* Exercise 7.1.2: the Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` satisfies the
  conditions, with the threshold `k* = (sA/δ)^{1/(1−α)}`.
* Exercise 7.1.3: the condition `a < g(a)` cannot be weakened to `a ≤ g(a)`; the
  identity satisfies the weakened conditions and has a fixed point at every `x`.
* Exercise 7.1.4: `g(k) = sf(k) + (1 − δ)k` is globally stable for any positive,
  increasing, concave, differentiable `f` satisfying the Inada conditions, by the
  tangent-line bounds `f(a) − f(a/2) ≥ f'(a)a/2` and `f(b) ≤ f(c) + f'(c)(b − c)`.
* Exercise 7.1.5: the Fajgelbaum et al. (2017) uncertainty map
  `g(s) = ρ²(1/s + a/η²)⁻¹ + γ` is globally stable on `(0, ∞)`.
-/

open Filter Topology Function Set

namespace SargentStachurski.NonlinearValuation

/-! ### Proposition 7.1.2 -/

/-- The orbit of `x` under an increasing self-map of `(0, ∞)` converges to a fixed point when it is
bounded on the side it moves towards. -/
theorem exists_fixedPt_tendsto_of_concave {g : ℝ → ℝ} (hmaps : MapsTo g (Ioi 0) (Ioi 0))
    (hmono : MonotoneOn g (Ioi 0)) (hcont : ContinuousOn g (Ioi 0)) {x a b : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) (hga : a < g a) (hgb : g b ≤ b) :
    ∃ L, 0 < L ∧ g L = L ∧ Tendsto (fun k : ℕ => g^[k] x) atTop (𝓝 L) := by
  have hx : x ∈ Ioi (0 : ℝ) := lt_of_lt_of_le ha hax
  have hb : b ∈ Ioi (0 : ℝ) := lt_of_lt_of_le hx hxb
  have hmem : ∀ k, g^[k] x ∈ Ioi (0 : ℝ) := fun k => hmaps.iterate k hx
  -- the iterates stay in `[a, b]`
  have hup : ∀ k, g^[k] x ≤ b := by
    intro k
    induction k with
    | zero => simpa using hxb
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (hmono (hmem k) hb ih).trans hgb
  have hlo : ∀ k, a ≤ g^[k] x := by
    intro k
    induction k with
    | zero => simpa using hax
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hga.le.trans (hmono ha (hmem k) ih)
  -- a limit `L` of the orbit is a fixed point
  have hfix : ∀ L, 0 < L → Tendsto (fun k : ℕ => g^[k] x) atTop (𝓝 L) → g L = L := by
    intro L hL hlim
    have h1 : Tendsto (fun k : ℕ => g (g^[k] x)) atTop (𝓝 (g L)) :=
      ((hcont.continuousAt (Ioi_mem_nhds hL)).tendsto).comp hlim
    have h2 : Tendsto (fun k : ℕ => g (g^[k] x)) atTop (𝓝 L) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k => ?_
      simp [iterate_succ_apply']
    exact tendsto_nhds_unique h1 h2
  rcases le_total x (g x) with hxg | hxg
  · -- increasing orbit
    have hmon : Monotone fun k : ℕ => g^[k] x := by
      refine monotone_nat_of_le_succ fun k => ?_
      induction k with
      | zero => simpa using hxg
      | succ k ih =>
        calc g^[k + 1] x = g (g^[k] x) := iterate_succ_apply' _ _ _
          _ ≤ g (g^[k + 1] x) := hmono (hmem k) (hmem (k + 1)) ih
          _ = g^[k + 1 + 1] x := (iterate_succ_apply' _ _ _).symm
    have hbdd : BddAbove (range fun k : ℕ => g^[k] x) := ⟨b, by rintro _ ⟨k, rfl⟩; exact hup k⟩
    have hlim := tendsto_atTop_ciSup hmon hbdd
    have hL : 0 < ⨆ k : ℕ, g^[k] x := lt_of_lt_of_le (hmem 0) (le_ciSup hbdd 0)
    exact ⟨_, hL, hfix _ hL hlim, hlim⟩
  · -- decreasing orbit
    have hanti : Antitone fun k : ℕ => g^[k] x := by
      refine antitone_nat_of_succ_le fun k => ?_
      induction k with
      | zero => simpa using hxg
      | succ k ih =>
        calc g^[k + 1 + 1] x = g (g^[k + 1] x) := iterate_succ_apply' _ _ _
          _ ≤ g (g^[k] x) := hmono (hmem (k + 1)) (hmem k) ih
          _ = g^[k + 1] x := (iterate_succ_apply' _ _ _).symm
    have hbdd : BddBelow (range fun k : ℕ => g^[k] x) := ⟨a, by rintro _ ⟨k, rfl⟩; exact hlo k⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hL : 0 < ⨅ k : ℕ, g^[k] x := lt_of_lt_of_le ha (le_ciInf hlo)
    exact ⟨_, hL, hfix _ hL hlim, hlim⟩

/-- **Proposition 7.1.2** (p. 214): if `g` is an increasing concave self-map of `(0, ∞)` and every
`x > 0` satisfies `a ≤ x ≤ b` for some `a, b > 0` with `a < g(a)` and `g(b) ≤ b`, then `g` is
globally stable on `(0, ∞)`. -/
theorem globallyStableOn_of_concave {g : ℝ → ℝ} (hmaps : MapsTo g (Ioi 0) (Ioi 0))
    (hmono : MonotoneOn g (Ioi 0)) (hconc : ConcaveOn ℝ (Ioi 0) g)
    (hab : ∀ x, 0 < x → ∃ a b, 0 < a ∧ a ≤ x ∧ x ≤ b ∧ a < g a ∧ g b ≤ b) :
    GloballyStableOn g (Ioi 0) := by
  have hcont : ContinuousOn g (Ioi 0) := by
    have := hconc.continuousOn_interior
    rwa [interior_Ioi] at this
  -- uniqueness: two fixed points `x ≤ y` coincide
  have huniq : ∀ x y, 0 < x → 0 < y → g x = x → g y = y → x ≤ y → x = y := by
    intro x y hx hy hgx hgy hxy
    by_contra hne
    have hlt : x < y := lt_of_le_of_ne hxy hne
    obtain ⟨a, -, ha, hax, -, hga, -⟩ := hab x hx
    set l := (y - x) / (y - a) with hl
    have hya : 0 < y - a := by linarith
    have hl0 : 0 < l := div_pos (by linarith) hya
    have hl1 : l ≤ 1 := (div_le_one hya).2 (by linarith)
    have hxeq : l * a + (1 - l) * y = x := by
      rw [hl]
      field_simp
      ring
    have h1 := hconc.2 (show a ∈ Ioi (0 : ℝ) from ha) (show y ∈ Ioi (0 : ℝ) from hy) hl0.le
      (by linarith) (by ring : l + (1 - l) = 1)
    simp only [smul_eq_mul, hxeq, hgx, hgy] at h1
    nlinarith [mul_lt_mul_of_pos_left hga hl0]
  obtain ⟨a, b, ha, hax, hxb, hga, hgb⟩ := hab 1 one_pos
  obtain ⟨L, hL, hgL, -⟩ := exists_fixedPt_tendsto_of_concave hmaps hmono hcont ha hax hxb hga hgb
  have huniq' : ∀ y, 0 < y → g y = y → y = L := fun y hy hgy => by
    rcases le_total y L with h | h
    · exact huniq y L hy hL hgy hgL h
    · exact (huniq L y hL hy hgL hgy h).symm
  refine ⟨L, hL, hgL, fun y hy hgy => huniq' y hy hgy, fun x hx => ?_⟩
  obtain ⟨a', b', ha', hax', hxb', hga', hgb'⟩ := hab x hx
  obtain ⟨L', hL', hgL', hlim⟩ :=
    exists_fixedPt_tendsto_of_concave hmaps hmono hcont ha' hax' hxb' hga' hgb'
  rwa [huniq' L' hL' hgL'] at hlim

/-! ### Exercise 7.1.2: the Solow–Swan model -/

/-- The Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` (Vol. 1, (1.19), Exercise 1.2.25). -/
noncomputable def solowSwan (s A α δ : ℝ) (k : ℝ) : ℝ := s * A * k ^ α + (1 - δ) * k

/-- Exercise 7.1.2 (p. 216): the Solow–Swan map with `A, s > 0`, `0 < α < 1` and `0 < δ < 1`
satisfies the conditions of Proposition 7.1.2, so it is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_solowSwan {s A α δ : ℝ} (hs : 0 < s) (hA : 0 < A) (hα0 : 0 < α)
    (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : GloballyStableOn (solowSwan s A α δ) (Ioi 0) := by
  have hsA : 0 < s * A := mul_pos hs hA
  set kstar : ℝ := (s * A / δ) ^ (1 - α)⁻¹ with hk
  have h1α : 0 < 1 - α := by linarith
  have hkpos : 0 < kstar := Real.rpow_pos_of_pos (div_pos hsA hδ0) _
  have hkpow : kstar ^ (1 - α) = s * A / δ :=
    Real.rpow_inv_rpow (div_pos hsA hδ0).le h1α.ne'
  -- `k = kᵅ k^{1−α}`
  have hsplit : ∀ k : ℝ, 0 < k → k = k ^ α * k ^ (1 - α) := fun k hk => by
    rw [← Real.rpow_add hk]
    simp
  -- below `k*` the map moves up, above `k*` it moves down
  have hup : ∀ k : ℝ, 0 < k → k < kstar → k < solowSwan s A α δ k := by
    intro k hk hlt
    have h1 : k ^ (1 - α) < s * A / δ := by
      rw [← hkpow]
      exact Real.rpow_lt_rpow hk.le hlt h1α
    have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have h2 : δ * k ^ (1 - α) < s * A := by
      rw [lt_div_iff₀ hδ0] at h1
      linarith
    have h3 : δ * k < s * A * k ^ α := by
      conv_lhs => rw [hsplit k hk]
      nlinarith [mul_lt_mul_of_pos_right h2 hkα]
    unfold solowSwan
    linarith
  have hdown : ∀ k : ℝ, 0 < k → kstar ≤ k → solowSwan s A α δ k ≤ k := by
    intro k hk hle
    have h1 : s * A / δ ≤ k ^ (1 - α) := by
      rw [← hkpow]
      exact Real.rpow_le_rpow hkpos.le hle h1α.le
    have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have h2 : s * A ≤ δ * k ^ (1 - α) := by
      rw [div_le_iff₀ hδ0] at h1
      linarith
    unfold solowSwan
    have h3 : s * A * k ^ α ≤ δ * (k ^ α * k ^ (1 - α)) := by nlinarith
    rw [← hsplit k hk] at h3
    linarith
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro k hk
    have : 0 < k ^ α := Real.rpow_pos_of_pos hk α
    have hk' : (0 : ℝ) < k := hk
    change 0 < s * A * k ^ α + (1 - δ) * k
    nlinarith
  · intro k hk k' hk' hkk'
    unfold solowSwan
    have := Real.rpow_le_rpow (le_of_lt hk) hkk' hα0.le
    nlinarith
  · have h1 : ConcaveOn ℝ (Ioi 0) fun k : ℝ => k ^ α :=
      (Real.concaveOn_rpow hα0.le hα1.le).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h2 := (h1.smul hsA.le).add ((concaveOn_id (convex_Ioi (0 : ℝ))).smul (by linarith :
      (0 : ℝ) ≤ 1 - δ))
    refine h2.congr fun k _ => ?_
    simp [solowSwan, smul_eq_mul]
  · intro x hx
    refine ⟨min x (kstar / 2), max x kstar, lt_min hx (by positivity), min_le_left _ _,
      le_max_left _ _, hup _ (lt_min hx (by positivity)) ((min_le_right _ _).trans_lt
        (by linarith)), hdown _ (lt_of_lt_of_le hx (le_max_left _ _)) (le_max_right _ _)⟩

/-! ### Exercise 7.1.3 -/

/-- Exercise 7.1.3 (p. 216): the condition `a < g(a)` in Proposition 7.1.2 cannot be weakened to
`a ≤ g(a)`: the identity map is an increasing concave self-map of `(0, ∞)` satisfying the weakened
conditions, but it is not globally stable. -/
theorem not_globallyStableOn_id :
    MapsTo (id : ℝ → ℝ) (Ioi 0) (Ioi 0) ∧ MonotoneOn (id : ℝ → ℝ) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi (0 : ℝ)) id ∧
      (∀ x : ℝ, 0 < x → ∃ a b : ℝ, 0 < a ∧ a ≤ x ∧ x ≤ b ∧ a ≤ id a ∧ id b ≤ b) ∧
      ¬ GloballyStableOn (id : ℝ → ℝ) (Ioi 0) := by
  refine ⟨fun x hx => hx, fun _ _ _ _ h => h, concaveOn_id (convex_Ioi 0),
    fun x hx => ⟨x, x, hx, le_rfl, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  rintro ⟨u, -, -, huniq, -⟩
  have h1 := huniq 1 (mem_Ioi.2 one_pos) rfl
  have h2 := huniq 2 (mem_Ioi.2 two_pos) rfl
  linarith

/-! ### Exercise 7.1.4: Inada conditions -/

/-- Exercise 7.1.4 (p. 216): if `f` is strictly positive, increasing, concave and differentiable on
`(0, ∞)` with `f'(k) → ∞` as `k ↓ 0` and `f'(k) → 0` as `k → ∞`, and `0 < s, δ < 1`, then
`g(k) = sf(k) + (1 − δ)k` is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_solow_inada {f : ℝ → ℝ} {s δ : ℝ} (hs0 : 0 < s) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hfpos : ∀ k, 0 < k → 0 < f k) (hfmono : MonotoneOn f (Ioi 0))
    (hfconc : ConcaveOn ℝ (Ioi 0) f) (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hinada0 : Tendsto (deriv f) (𝓝[>] 0) atTop) (hinada1 : Tendsto (deriv f) atTop (𝓝 0)) :
    GloballyStableOn (fun k => s * f k + (1 - δ) * k) (Ioi 0) := by
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro k hk
    have := hfpos k hk
    have hk' : (0 : ℝ) < k := hk
    change 0 < s * f k + (1 - δ) * k
    nlinarith
  · intro k hk k' hk' hkk'
    have := hfmono hk hk' hkk'
    change s * f k + (1 - δ) * k ≤ s * f k' + (1 - δ) * k'
    nlinarith
  · have h2 := (hfconc.smul hs0.le).add ((concaveOn_id (convex_Ioi (0 : ℝ))).smul (by linarith :
      (0 : ℝ) ≤ 1 - δ))
    refine h2.congr fun k _ => ?_
    simp [smul_eq_mul]
  · intro x hx
    -- small `a`: `f'(a) ≥ 2δ/s`
    obtain ⟨ε, hε, hεP⟩ : ∃ ε > 0, ∀ k, 0 < k → k < ε → 2 * δ / s ≤ deriv f k := by
      have hev := hinada0.eventually (eventually_ge_atTop (2 * δ / s))
      rcases (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev with ⟨ε, hε, hεP⟩
      exact ⟨ε, hε, fun k hk hkε => hεP ⟨hk, by simpa using hkε⟩⟩
    -- large `c`: `f'(c) ≤ δ/(2s)`
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, ∀ c, c₀ ≤ c → deriv f c ≤ δ / (2 * s) := by
      have := hinada1.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < δ / (2 * s)))
      rw [eventually_atTop] at this
      exact this
    set a := min x (ε / 2) with ha
    have ha0 : 0 < a := lt_min hx (by positivity)
    have haε : a < ε := (min_le_right _ _).trans_lt (by linarith)
    set c := max c₀ 1 with hc
    have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    set b := max x (max (c + 1) (2 * s * f c / δ)) with hb
    have hcb : c < b := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
    refine ⟨a, b, ha0, min_le_left _ _, le_max_left _ _, ?_, ?_⟩
    · -- `f(a) − f(a/2) ≥ f'(a)·a/2 ≥ δa/s`
      have h1 := hfconc.deriv_le_slope (mem_Ioi.2 (by positivity : (0 : ℝ) < a / 2))
        (show a ∈ Ioi (0 : ℝ) from ha0) (by linarith) (hfdiff a ha0)
      rw [slope_def_field] at h1
      have h2 := hεP a ha0 haε
      have h3 : a - a / 2 = a / 2 := by ring
      rw [h3, le_div_iff₀ (by positivity)] at h1
      have h4 := hfpos (a / 2) (by positivity)
      have h5 : 2 * δ / s * (a / 2) ≤ deriv f a * (a / 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h6 : 2 * δ / s * (a / 2) = δ * a / s := by field_simp
      have h7 : δ * a < s * f a := by
        rw [h6] at h5
        have := lt_of_le_of_lt (h5.trans h1) (by linarith : f a - f (a / 2) < f a)
        rwa [div_lt_iff₀ hs0, mul_comm (f a) s] at this
      change a < s * f a + (1 - δ) * a
      linarith
    · -- `f(b) ≤ f(c) + f'(c)(b − c)` and `f'(c) ≤ δ/(2s)`
      have h1 := hfconc.slope_le_deriv (show c ∈ Ioi (0 : ℝ) from hc0)
        (show b ∈ Ioi (0 : ℝ) from hc0.trans hcb) hcb (hfdiff c hc0)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
      have h2 := hc₀ c (le_max_left _ _)
      have hbc : 0 ≤ b - c := by linarith
      have h3 : deriv f c * (b - c) ≤ δ / (2 * s) * b := by
        have := mul_le_mul_of_nonneg_right h2 hbc
        have h4 : δ / (2 * s) * (b - c) ≤ δ / (2 * s) * b :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have h5 : 2 * s * f c / δ ≤ b := (le_max_right _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ hδ0] at h5
      have h6 : s * (δ / (2 * s) * b) = δ * b / 2 := by field_simp
      change s * f b + (1 - δ) * b ≤ b
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans' (le_refl _)) hs0.le]

/-! ### Exercise 7.1.5: aggregate uncertainty -/

/-- The law of motion of Fajgelbaum et al. (2017): `g(s) = ρ²(1/s + a/η²)⁻¹ + γ`. -/
noncomputable def fajgelbaum (ρ a η γ : ℝ) (s : ℝ) : ℝ := ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ

/-- `s ↦ (1/s + c)⁻¹` is concave on `(0, ∞)` for `c ≥ 0`. -/
theorem concaveOn_inv_inv_add {c : ℝ} (hc : 0 ≤ c) :
    ConcaveOn ℝ (Ioi 0) fun s => (1 / s + c)⁻¹ := by
  refine ⟨convex_Ioi 0, fun x hx y hy p q hp hq hpq => ?_⟩
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hS : 0 < p * x + q * y := by
    have hm := lt_min hx' hy'
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) hp,
      mul_le_mul_of_nonneg_left (min_le_right x y) hq]
  have hform : ∀ z : ℝ, 0 < z → (1 / z + c)⁻¹ = z / (1 + c * z) := fun z hz => by
    field_simp
  simp only [smul_eq_mul]
  rw [hform x hx', hform y hy', hform _ hS]
  have hq' : q = 1 - p := by linarith
  subst hq'
  have h1 : 0 < 1 + c * x := by positivity
  have h2 : 0 < 1 + c * y := by positivity
  have h3 : 0 < 1 + c * (p * x + (1 - p) * y) := by positivity
  have key : (p * x + (1 - p) * y) / (1 + c * (p * x + (1 - p) * y)) -
      (p * (x / (1 + c * x)) + (1 - p) * (y / (1 + c * y))) =
      c * p * (1 - p) * (y - x) ^ 2 / ((1 + c * x) * (1 + c * y) *
        (1 + c * (p * x + (1 - p) * y))) := by
    field_simp
    ring
  have hnn : 0 ≤ c * p * (1 - p) * (y - x) ^ 2 / ((1 + c * x) * (1 + c * y) *
      (1 + c * (p * x + (1 - p) * y))) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg (mul_nonneg hc hp) hq) (sq_nonneg _)
  linarith

/-- Exercise 7.1.5 (p. 216): for `a, η, γ > 0` and `0 < ρ < 1`, the map
`g(s) = ρ²(1/s + a/η²)⁻¹ + γ` is globally stable on `(0, ∞)`. -/
theorem globallyStableOn_fajgelbaum {ρ a η γ : ℝ} (hρ0 : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (hγ : 0 < γ) : GloballyStableOn (fajgelbaum ρ a η γ) (Ioi 0) := by
  set c := a / η ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hpos : ∀ s : ℝ, 0 < s → 0 < (1 / s + c)⁻¹ := fun s hs => by positivity
  have hbound : ∀ s : ℝ, 0 < s → (1 / s + c)⁻¹ ≤ c⁻¹ := fun s hs =>
    inv_anti₀ hc0 (by have : 0 < 1 / s := (by positivity); linarith)
  refine globallyStableOn_of_concave ?_ ?_ ?_ ?_
  · intro s hs
    have := hpos s hs
    change 0 < ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ
    rw [← hc]
    positivity
  · intro s hs t ht hst
    change ρ ^ 2 * (1 / s + a / η ^ 2)⁻¹ + γ ≤ ρ ^ 2 * (1 / t + a / η ^ 2)⁻¹ + γ
    rw [← hc]
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 / t + c ≤ 1 / s + c := by
      have := one_div_le_one_div_of_le hs' hst
      linarith
    have h2 := inv_anti₀ (by have : 0 < 1 / t := (by positivity); linarith) h1
    nlinarith [sq_nonneg ρ]
  · have h := ((concaveOn_inv_inv_add hc0.le).smul (sq_nonneg ρ)).add_const γ
    refine h.congr fun s _ => ?_
    simp [fajgelbaum, smul_eq_mul, hc]
  · intro x hx
    refine ⟨min x (γ / 2), max x (ρ ^ 2 * c⁻¹ + γ), lt_min hx (by positivity), min_le_left _ _,
      le_max_left _ _, ?_, ?_⟩
    · have := hpos (min x (γ / 2)) (lt_min hx (by positivity))
      have hm : min x (γ / 2) ≤ γ / 2 := min_le_right _ _
      change min x (γ / 2) < ρ ^ 2 * (1 / min x (γ / 2) + a / η ^ 2)⁻¹ + γ
      rw [← hc]
      nlinarith [sq_nonneg ρ, mul_nonneg (sq_nonneg ρ) this.le]
    · have hb : 0 < max x (ρ ^ 2 * c⁻¹ + γ) := lt_of_lt_of_le hx (le_max_left _ _)
      have := hbound _ hb
      change ρ ^ 2 * (1 / max x (ρ ^ 2 * c⁻¹ + γ) + a / η ^ 2)⁻¹ + γ ≤ max x (ρ ^ 2 * c⁻¹ + γ)
      rw [← hc]
      have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg ρ)
      linarith [le_max_right x (ρ ^ 2 * c⁻¹ + γ)]

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A power-transformed affine equation

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.1.3 (pp. 218–219).

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Certainty equivalent operators

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.1–§7.3.1.3
(pp. 232–236).

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregators, Koopmans operators and lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.3.1.4–§7.3.3.2
(pp. 236–242).

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Time additive and risk-sensitive lifetime utility

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.2.1–§7.2.2
(pp. 219–227).

* (7.6) and Exercise 7.2.1: under the ansatz `Vₜ = v(Xₜ)`, the time additive
  recursion (7.5) becomes `v = r + βPv`, uniquely solved by `(I − βP)⁻¹r`.
* The entropic risk-adjusted expectation `E_θ[ξ] = θ⁻¹ log E exp(θξ)` of a random
  variable with a finite distribution `q`: Exercise 7.2.2 (translation), Exercise
  7.2.3 (the Gaussian case `E_θ[ξ] = Eξ + θ Var ξ/2`, by the moment generating
  function), and Lemma 7.2.1 (`E_θ ≤ E` for `θ < 0`, `E_θ ≥ E` for `θ > 0`, with
  strict inequality iff `Var ξ > 0`, by strict Jensen).
* Proposition 7.2.2 is proved in `Koopmans` from Proposition 7.3.3.
* Exercise 7.2.4: with `r(x) = x` and Gaussian AR(1) dynamics, `v(x) = ax + b` with
  `a = 1/(1 − ρβ)` and `b = θ(β/(1 − β))(aσ)²/2` solves (7.11).
* Exercise 7.2.6: with IID states the fixed point is `v* = r + κ` with the constant
  `κ` solving the one-dimensional equation `κ = βκ + βE_θ[r]`, so
  `v* = r + (β/(1 − β))E_θ[r]`.
-/

open Matrix Finset Filter Topology Function Set MeasureTheory ProbabilityTheory

namespace SargentStachurski.NonlinearValuation

variable {X : Type*} [Fintype X]

/-! ### The time additive recursion -/

/-- (7.6) and Exercise 7.2.1 (p. 220): for `P` Markov and `0 ≤ β < 1`, `v* = (I − βP)⁻¹r` solves
`v = r + βPv`, and it is the only solution; hence `Vₜ = v*(Xₜ)` satisfies the recursion (7.5). -/
theorem timeAdditive_solution [DecidableEq X] [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r : X → ℝ) :
    (1 - β • P)⁻¹ *ᵥ r = r + β • (P *ᵥ ((1 - β • P)⁻¹ *ᵥ r)) ∧
      ∀ w, w = r + β • (P *ᵥ w) → w = (1 - β • P)⁻¹ *ᵥ r := by
  have hρ : specRad (β • P) < 1 := by rw [specRad_smul_isMarkov hP hβ0]; exact hβ1
  refine ⟨?_, fun w hw => (eq_add_mulVec_iff hρ r w).1 (by rwa [smul_mulVec])⟩
  rw [← smul_mulVec]
  exact inv_mulVec_eq_add hρ r

/-! ### The entropic risk-adjusted expectation (§7.2.2.2) -/

/-- The entropic risk-adjusted expectation `E_θ[ξ] = θ⁻¹ log ∑ q(x) exp(θξ(x))` of `ξ` under the
finite distribution `q`. -/
noncomputable def entExp (θ : ℝ) (q ξ : X → ℝ) : ℝ := θ⁻¹ * Real.log (∑ x, q x * Real.exp (θ * ξ x))

/-- The entropic certainty equivalent is the risk-adjusted expectation under each row of `P`. -/
theorem entR_eq_entExp (θ : ℝ) (P : Matrix X X ℝ) (v : X → ℝ) (x : X) :
    entR θ P v x = entExp θ (P x) v := rfl

/-- Exercise 7.2.2 (p. 223): `E_θ[ξ + c] = E_θ[ξ] + c`. -/
theorem entExp_add_const {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (c : ℝ) : entExp θ q (fun x => ξ x + c) = entExp θ q ξ + c := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < q x := by
    by_contra hcon
    have : ∑ x, q x ≤ 0 := sum_nonpos fun x _ => not_lt.1 fun h => hcon ⟨x, h⟩
    linarith [hq.sum_eq_one]
  have hS : 0 < ∑ x, q x * Real.exp (θ * ξ x) :=
    lt_of_lt_of_le (mul_pos hx₀ (Real.exp_pos _))
      (single_le_sum (fun x _ => mul_nonneg (hq.nonneg x) (Real.exp_pos _).le) (mem_univ x₀))
  have h1 : ∑ x, q x * Real.exp (θ * (ξ x + c)) =
      Real.exp (θ * c) * ∑ x, q x * Real.exp (θ * ξ x) := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by rw [mul_add, Real.exp_add]; ring
  unfold entExp
  rw [h1, Real.log_mul (Real.exp_pos _).ne' hS.ne', Real.log_exp]
  field_simp
  ring

/-- Exercise 7.2.3 (p. 223): if `ξ ∼ N(μ, v)` then `E_θ[ξ] = μ + θv/2`, from the Gaussian moment
generating function. -/
theorem entExp_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {ξ : Ω → ℝ}
    {μ : ℝ} {v : NNReal} (hξ : HasLaw ξ (gaussianReal μ v) ν) {θ : ℝ} (hθ : θ ≠ 0) :
    θ⁻¹ * Real.log (∫ ω, Real.exp (θ * ξ ω) ∂ν) = μ + θ * v / 2 := by
  have h := mgf_gaussianReal hξ θ
  unfold mgf at h
  rw [h, Real.log_exp]
  field_simp

/-- Jensen's inequality for the exponential: `exp(θE[ξ]) ≤ E[exp(θξ)]`. -/
theorem exp_mean_le {θ : ℝ} {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    Real.exp (θ * ∑ x, q x * ξ x) ≤ ∑ x, q x * Real.exp (θ * ξ x) := by
  have h := convexOn_exp.map_sum_le (t := univ) (w := q) (p := fun x => θ * ξ x)
    (fun x _ => hq.nonneg x) hq.sum_eq_one (fun x _ => mem_univ _)
  simp only [smul_eq_mul] at h
  have e : ∑ x, q x * (θ * ξ x) = θ * ∑ x, q x * ξ x := by
    rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
  rwa [e] at h

/-- `θE[ξ] ≤ log E[exp(θξ)]`. -/
theorem mul_mean_le_log {θ : ℝ} {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    θ * ∑ x, q x * ξ x ≤ Real.log (∑ x, q x * Real.exp (θ * ξ x)) := by
  have h := exp_mean_le (θ := θ) hq ξ
  rwa [← Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h)] at h

/-- **Lemma 7.2.1 (i)** (p. 224): `E_θ[ξ] ≤ E[ξ]` for `θ < 0`. -/
theorem entExp_le_mean {θ : ℝ} (hθ : θ < 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    entExp θ q ξ ≤ ∑ x, q x * ξ x := by
  have h := mul_le_mul_of_nonpos_left (mul_mean_le_log (θ := θ) hq ξ) (inv_lt_zero.2 hθ).le
  rw [← mul_assoc, inv_mul_cancel₀ hθ.ne, one_mul] at h
  exact h

/-- **Lemma 7.2.1 (ii)** (p. 224): `E_θ[ξ] ≥ E[ξ]` for `θ > 0`. -/
theorem mean_le_entExp {θ : ℝ} (hθ : 0 < θ) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ) :
    ∑ x, q x * ξ x ≤ entExp θ q ξ := by
  have h := mul_le_mul_of_nonneg_left (mul_mean_le_log (θ := θ) hq ξ) (inv_pos.2 hθ).le
  rw [← mul_assoc, inv_mul_cancel₀ hθ.ne', one_mul] at h
  exact h

/-- Lemma 7.2.1 (p. 224), strictness: if `Var[ξ] > 0`, then `E_θ[ξ] ≠ E[ξ]` for `θ ≠ 0`, by strict
Jensen on the support of `q`. -/
theorem entExp_ne_mean {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (hvar : 0 < ∑ x, q x * (ξ x - ∑ y, q y * ξ y) ^ 2) : entExp θ q ξ ≠ ∑ x, q x * ξ x := by
  classical
  set E := ∑ y, q y * ξ y with hE
  set t := univ.filter fun x => 0 < q x with ht
  have hsupp : ∀ g : X → ℝ, ∑ x ∈ t, q x * g x = ∑ x, q x * g x := fun g =>
    sum_filter_of_ne fun x _ hx =>
      lt_of_le_of_ne (hq.nonneg x) (fun h => hx (by rw [← h, zero_mul]))
  -- a support point away from the mean, and a second support point with a different value
  have hsupp1 : ∑ x ∈ t, q x = ∑ x, q x :=
    sum_filter_of_ne fun x _ hx => lt_of_le_of_ne (hq.nonneg x) (Ne.symm hx)
  obtain ⟨j, hj⟩ : ∃ j, 0 < q j * (ξ j - E) ^ 2 := by
    by_contra hcon
    have : ∑ x, q x * (ξ x - E) ^ 2 ≤ 0 := sum_nonpos fun x _ => not_lt.1 fun h => hcon ⟨x, h⟩
    linarith
  have hqj : 0 < q j := by
    rcases (hq.nonneg j).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hj; exact absurd hj (lt_irrefl 0)
  have hjE : ξ j ≠ E := fun h => by rw [h, sub_self] at hj; simp at hj
  obtain ⟨k, hk, hjk⟩ : ∃ k ∈ t, ξ j ≠ ξ k := by
    by_contra hcon
    have hall : ∀ k ∈ t, ξ k = ξ j := fun k hk => by
      by_contra hne
      exact hcon ⟨k, hk, fun h => hne h.symm⟩
    have : E = ξ j := by
      rw [hE, ← hsupp ξ, sum_congr rfl fun k hk => by rw [hall k hk], ← sum_mul, hsupp1,
        hq.sum_eq_one, one_mul]
    exact hjE this.symm
  have hj' : j ∈ t := mem_filter.2 ⟨mem_univ _, hqj⟩
  have hstrict := strictConvexOn_exp.map_sum_lt (t := t) (w := q) (p := fun x => θ * ξ x)
    (fun x hx => (mem_filter.1 hx).2) (by rw [hsupp1]; exact hq.sum_eq_one)
    (fun x _ => mem_univ _) ⟨j, hj', k, hk, fun h => hjk (mul_left_cancel₀ hθ h)⟩
  simp only [smul_eq_mul] at hstrict
  have e1 : ∑ x ∈ t, q x * (θ * ξ x) = θ * E := by
    rw [hsupp fun x => θ * ξ x, mul_sum]; exact sum_congr rfl fun x _ => by ring
  rw [e1, hsupp fun x => Real.exp (θ * ξ x)] at hstrict
  have hlog : θ * E < Real.log (∑ x, q x * Real.exp (θ * ξ x)) :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hstrict)).2 hstrict
  intro heq
  unfold entExp at heq
  have : Real.log (∑ x, q x * Real.exp (θ * ξ x)) = θ * E := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hθ, one_mul]
  linarith

/-- Lemma 7.2.1 (p. 224), equality case: if `Var[ξ] = 0` then `E_θ[ξ] = E[ξ]`. -/
theorem entExp_eq_mean {θ : ℝ} (hθ : θ ≠ 0) {q : X → ℝ} (hq : IsDistribution q) (ξ : X → ℝ)
    (hvar : ∑ x, q x * (ξ x - ∑ y, q y * ξ y) ^ 2 = 0) : entExp θ q ξ = ∑ x, q x * ξ x := by
  set E := ∑ y, q y * ξ y with hE
  have hterm := (sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hq.nonneg x) (sq_nonneg _)).1 hvar
  have h1 : ∑ x, q x * Real.exp (θ * ξ x) = Real.exp (θ * E) := by
    have : ∀ x, q x * Real.exp (θ * ξ x) = q x * Real.exp (θ * E) := fun x => by
      rcases mul_eq_zero.1 (hterm x (mem_univ x)) with h | h
      · rw [h, zero_mul, zero_mul]
      · rw [sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)]
    rw [sum_congr rfl fun x _ => this x, ← sum_mul, hq.sum_eq_one, one_mul]
  unfold entExp
  rw [h1, Real.log_exp, ← mul_assoc, inv_mul_cancel₀ hθ, one_mul]

/-! ### Exercise 7.2.4: the Gaussian case -/

/-- `E[exp(a + bW)] = exp(a + b²/2)` for a standard normal `W`. -/
theorem integral_exp_add_mul_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {η : Ω → ℝ} (hη : HasLaw η (gaussianReal 0 1) ν) (a b : ℝ) :
    ∫ ω, Real.exp (a + b * η ω) ∂ν = Real.exp (a + b ^ 2 / 2) := by
  simp_rw [Real.exp_add]
  rw [integral_const_mul]
  have h := mgf_gaussianReal hη b
  unfold mgf at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h, ← Real.exp_add]

/-- Exercise 7.2.4 (p. 225): with `r(x) = x`, `X' = ρx + σW` and `W` standard normal, the affine
function `v(x) = ax + b` with `a = 1/(1 − ρβ)` and `b = θ(β/(1 − β))(aσ)²/2` solves (7.11),
`v(x) = x + βE_θ[v(ρx + σW)]`. -/
theorem riskSensitive_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {W : Ω → ℝ} (hW : HasLaw W (gaussianReal 0 1) ν) {β ρ σ θ : ℝ} (hθ : θ ≠ 0) (hβ : β ≠ 1)
    (hρβ : ρ * β ≠ 1) (x : ℝ) :
    1 / (1 - ρ * β) * x + θ * (β / (1 - β)) * (1 / (1 - ρ * β) * σ) ^ 2 / 2 =
      x + β * (θ⁻¹ * Real.log (∫ ω, Real.exp (θ * (1 / (1 - ρ * β) * (ρ * x + σ * W ω) +
        θ * (β / (1 - β)) * (1 / (1 - ρ * β) * σ) ^ 2 / 2)) ∂ν)) := by
  set a := 1 / (1 - ρ * β) with ha
  set b := θ * (β / (1 - β)) * (a * σ) ^ 2 / 2 with hb
  have h1 : ∀ ω, θ * (a * (ρ * x + σ * W ω) + b) = θ * (a * ρ * x + b) + θ * a * σ * W ω :=
    fun ω => by ring
  simp_rw [h1]
  rw [integral_exp_add_mul_gaussian hW, Real.log_exp]
  have h1ρβ : 1 - ρ * β ≠ 0 := sub_ne_zero.2 (Ne.symm hρβ)
  have h1β : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  rw [hb, ha]
  field_simp
  ring

/-! ### Exercise 7.2.6: IID consumption -/

/-- Exercise 7.2.6 (p. 225): with IID states drawn from `φ`, the risk-sensitive Koopmans operator is
`(Kv)(x) = r(x) + βE_θ^φ[v]`, so a fixed point has the form `v* = r + κ` for a constant `κ`, which
by translation equivariance solves the one-dimensional linear equation `κ = βκ + βE_θ^φ[r]`; hence
`v* = r + (β/(1 − β))E_θ^φ[r]`. -/
theorem riskSensitive_iid {θ : ℝ} (hθ : θ ≠ 0) {φ : X → ℝ} (hφ : IsDistribution φ) (r : X → ℝ)
    {β : ℝ} (hβ : β ≠ 1) :
    IsFixedPt (koopmans (additive r β) (entR θ (Matrix.of fun _ x' => φ x')))
      (fun x => r x + β / (1 - β) * entExp θ φ r) := by
  funext x
  have h1β : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  change r x + β * entExp θ φ (fun x' => r x' + β / (1 - β) * entExp θ φ r) =
    r x + β / (1 - β) * entExp θ φ r
  rw [entExp_add_const hθ hφ]
  field_simp
  ring

/-- Exercise 7.2.6: the IID kernel is Markov, so for `0 ≤ β < 1` the fixed point
`r + (β/(1 − β))E_θ^φ[r]` is the unique lifetime value, by Proposition 7.2.2. -/
theorem riskSensitive_iid_unique {θ : ℝ} (hθ : θ ≠ 0) {φ : X → ℝ} (hφ : IsDistribution φ)
    (r : X → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {v : X → ℝ}
    (hv : IsFixedPt (koopmans (additive r β) (entR θ (Matrix.of fun _ x' => φ x'))) v) :
    v = fun x => r x + β / (1 - β) * entExp θ φ r := by
  have hP : IsMarkov (Matrix.of fun (_ : X) x' => φ x') :=
    ⟨fun _ x' => hφ.nonneg x', fun _ => hφ.sum_eq_one⟩
  obtain ⟨u, -, huniq, -⟩ := globallyStable_riskSensitive hP hθ r hβ0 hβ1
  rw [huniq v hv, huniq _ (riskSensitive_iid hθ hφ r hβ1.ne)]

end SargentStachurski.NonlinearValuation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Epstein–Zin preferences

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §7.2.3 (pp. 227–232),
Exercise 7.3.16 and §7.3.3.3 (p. 243).

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

namespace SargentStachurski.NonlinearValuation

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

end SargentStachurski.NonlinearValuation

set_option linter.style.longLine false
#print axioms SargentStachurski.NonlinearValuation.IsMarkov
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.mk
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.nonneg
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.rowsum
#print axioms SargentStachurski.NonlinearValuation.IsDistribution
#print axioms SargentStachurski.NonlinearValuation.IsDistribution.mk
#print axioms SargentStachurski.NonlinearValuation.IsDistribution.nonneg
#print axioms SargentStachurski.NonlinearValuation.IsDistribution.sum_eq_one
#print axioms SargentStachurski.NonlinearValuation.mulVec_apply_eq
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.mul
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.pow
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.mulVec_const
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.NonlinearValuation.GloballyStable
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.mk
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.mapsTo
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.nonneg
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.lt_one
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.iterate_mem
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.NonlinearValuation.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.NonlinearValuation.fixedPt_le_of_le
#print axioms SargentStachurski.NonlinearValuation.le_fixedPt_of_le_apply
#print axioms SargentStachurski.NonlinearValuation.isContractionOn_of_blackwell
#print axioms SargentStachurski.NonlinearValuation.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.NonlinearValuation.pow_nonneg_entries
#print axioms SargentStachurski.NonlinearValuation.pow_le_pow_entries
#print axioms SargentStachurski.NonlinearValuation.complexify
#print axioms SargentStachurski.NonlinearValuation.complexify_apply
#print axioms SargentStachurski.NonlinearValuation.complexify_pow
#print axioms SargentStachurski.NonlinearValuation.complexify_transpose
#print axioms SargentStachurski.NonlinearValuation.nnnorm_complexify
#print axioms SargentStachurski.NonlinearValuation.norm_complexify
#print axioms SargentStachurski.NonlinearValuation.specRad
#print axioms SargentStachurski.NonlinearValuation.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.NonlinearValuation.specRad_nonneg
#print axioms SargentStachurski.NonlinearValuation.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.NonlinearValuation.tendsto_norm_pow_rpow
#print axioms SargentStachurski.NonlinearValuation.eventually_norm_pow_le
#print axioms SargentStachurski.NonlinearValuation.tendsto_norm_pow_zero
#print axioms SargentStachurski.NonlinearValuation.summable_pow
#print axioms SargentStachurski.NonlinearValuation.one_sub_mul_tsum
#print axioms SargentStachurski.NonlinearValuation.tsum_mul_one_sub
#print axioms SargentStachurski.NonlinearValuation.neumann_series
#print axioms SargentStachurski.NonlinearValuation.specRad_transpose
#print axioms SargentStachurski.NonlinearValuation.norm_le_norm_of_abs_le
#print axioms SargentStachurski.NonlinearValuation.specRad_le_of_le
#print axioms SargentStachurski.NonlinearValuation.rowsum_abs_le_norm
#print axioms SargentStachurski.NonlinearValuation.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.NonlinearValuation.abs_entry_le_norm
#print axioms SargentStachurski.NonlinearValuation.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.NonlinearValuation.specRad_le_norm
#print axioms SargentStachurski.NonlinearValuation.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.NonlinearValuation.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.NonlinearValuation.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.NonlinearValuation.eventually_abs_entry_pow_le
#print axioms SargentStachurski.NonlinearValuation.resPartial
#print axioms SargentStachurski.NonlinearValuation.res
#print axioms SargentStachurski.NonlinearValuation.res_apply
#print axioms SargentStachurski.NonlinearValuation.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.NonlinearValuation.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.NonlinearValuation.resPartial_apply
#print axioms SargentStachurski.NonlinearValuation.summable_res_entry
#print axioms SargentStachurski.NonlinearValuation.tendsto_resPartial_apply
#print axioms SargentStachurski.NonlinearValuation.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.NonlinearValuation.smul_one_sub_mul_res
#print axioms SargentStachurski.NonlinearValuation.res_mul_smul_one_sub
#print axioms SargentStachurski.NonlinearValuation.res_nonneg
#print axioms SargentStachurski.NonlinearValuation.inv_le_res_diag
#print axioms SargentStachurski.NonlinearValuation.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.NonlinearValuation.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.NonlinearValuation.smul_one_sub_mul_res_real
#print axioms SargentStachurski.NonlinearValuation.norm_res_complexify_le
#print axioms SargentStachurski.NonlinearValuation.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.NonlinearValuation.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.NonlinearValuation.exists_res_entry_gt
#print axioms SargentStachurski.NonlinearValuation.isCompact_simplex
#print axioms SargentStachurski.NonlinearValuation.perron_frobenius
#print axioms SargentStachurski.NonlinearValuation.perron_frobenius_left
#print axioms SargentStachurski.NonlinearValuation.le_specRad_of_colsum_ge
#print axioms SargentStachurski.NonlinearValuation.specRad_le_of_colsum_le
#print axioms SargentStachurski.NonlinearValuation.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.NonlinearValuation.specRad_le_of_rowsum_le
#print axioms SargentStachurski.NonlinearValuation.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.NonlinearValuation.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.NonlinearValuation.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.exists_stationary
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.NonlinearValuation.Irreducible
#print axioms SargentStachurski.NonlinearValuation.irreducible_of_pos
#print axioms SargentStachurski.NonlinearValuation.Irreducible.transpose
#print axioms SargentStachurski.NonlinearValuation.pow_mulVec_eq_of_mulVec_eq
#print axioms SargentStachurski.NonlinearValuation.Irreducible.pos_of_mulVec_eq_smul
#print axioms SargentStachurski.NonlinearValuation.Irreducible.specRad_pos
#print axioms SargentStachurski.NonlinearValuation.Irreducible.exists_pos_eigenvector
#print axioms SargentStachurski.NonlinearValuation.Irreducible.exists_pos_left_eigenvector
#print axioms SargentStachurski.NonlinearValuation.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms SargentStachurski.NonlinearValuation.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms SargentStachurski.NonlinearValuation.discountOp
#print axioms SargentStachurski.NonlinearValuation.discountOp_apply
#print axioms SargentStachurski.NonlinearValuation.discountOp_nonneg
#print axioms SargentStachurski.NonlinearValuation.discountOp_const
#print axioms SargentStachurski.NonlinearValuation.specRad_smul_isMarkov
#print axioms SargentStachurski.NonlinearValuation.summable_pow_apply
#print axioms SargentStachurski.NonlinearValuation.summable_pow_mulVec
#print axioms SargentStachurski.NonlinearValuation.mulVec_tsum_pow_mulVec
#print axioms SargentStachurski.NonlinearValuation.tsum_pow_mulVec_eq
#print axioms SargentStachurski.NonlinearValuation.eq_of_eq_add_mulVec
#print axioms SargentStachurski.NonlinearValuation.inv_mulVec_eq_add
#print axioms SargentStachurski.NonlinearValuation.inv_mulVec_eq_tsum
#print axioms SargentStachurski.NonlinearValuation.eq_add_mulVec_iff
#print axioms SargentStachurski.NonlinearValuation.specRad_lt_one_iff_existsUnique_pos
#print axioms SargentStachurski.NonlinearValuation.globallyStable_of_iterate_contraction
#print axioms SargentStachurski.NonlinearValuation.globallyStable_of_iterate_contraction_univ
#print axioms SargentStachurski.NonlinearValuation.affineOp
#print axioms SargentStachurski.NonlinearValuation.affineOp_iterate_sub
#print axioms SargentStachurski.NonlinearValuation.exists_isContractionOn_iterate_affineOp
#print axioms SargentStachurski.NonlinearValuation.globallyStable_affineOp
#print axioms SargentStachurski.NonlinearValuation.isFixedPt_affineOp_inv
#print axioms SargentStachurski.NonlinearValuation.mulVec_le_mulVec_of_nonneg
#print axioms SargentStachurski.NonlinearValuation.norm_abs_fun
#print axioms SargentStachurski.NonlinearValuation.norm_le_norm_of_abs_le_fun
#print axioms SargentStachurski.NonlinearValuation.abs_iterate_sub_le_pow_mulVec
#print axioms SargentStachurski.NonlinearValuation.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms SargentStachurski.NonlinearValuation.globallyStable_of_abs_sub_le
#print axioms SargentStachurski.NonlinearValuation.GloballyStableOn
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_univ_iff
#print axioms SargentStachurski.NonlinearValuation.GloballyStableOn.existsUnique
#print axioms SargentStachurski.NonlinearValuation.GloballyStableOn.of_conj
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_iff_of_conj
#print axioms SargentStachurski.NonlinearValuation.iterate_le_iterate_of_monotoneOn
#print axioms SargentStachurski.NonlinearValuation.knaster_tarski
#print axioms SargentStachurski.NonlinearValuation.exists_continuum_fixedPts
#print axioms SargentStachurski.NonlinearValuation.du_concave
#print axioms SargentStachurski.NonlinearValuation.exists_delta_of_lt
#print axioms SargentStachurski.NonlinearValuation.du_concave_of_lt
#print axioms SargentStachurski.NonlinearValuation.neg_mem_Icc_iff
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_of_reflect
#print axioms SargentStachurski.NonlinearValuation.du_convex
#print axioms SargentStachurski.NonlinearValuation.du_convex_of_lt
#print axioms SargentStachurski.NonlinearValuation.concaveOn_comp
#print axioms SargentStachurski.NonlinearValuation.exists_fixedPt_tendsto_of_concave
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_of_concave
#print axioms SargentStachurski.NonlinearValuation.solowSwan
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_solowSwan
#print axioms SargentStachurski.NonlinearValuation.not_globallyStableOn_id
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_solow_inada
#print axioms SargentStachurski.NonlinearValuation.fajgelbaum
#print axioms SargentStachurski.NonlinearValuation.concaveOn_inv_inv_add
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_fajgelbaum
#print axioms SargentStachurski.NonlinearValuation.posCone
#print axioms SargentStachurski.NonlinearValuation.convex_posCone
#print axioms SargentStachurski.NonlinearValuation.Irreducible.exists_pos_row
#print axioms SargentStachurski.NonlinearValuation.mulVec_pos_of_row
#print axioms SargentStachurski.NonlinearValuation.Irreducible.of_pos_mul
#print axioms SargentStachurski.NonlinearValuation.powF
#print axioms SargentStachurski.NonlinearValuation.powF_pos
#print axioms SargentStachurski.NonlinearValuation.powF_monotoneOn
#print axioms SargentStachurski.NonlinearValuation.hasDerivAt_powF
#print axioms SargentStachurski.NonlinearValuation.continuousOn_powF
#print axioms SargentStachurski.NonlinearValuation.differentiableOn_powF
#print axioms SargentStachurski.NonlinearValuation.convexOn_powF
#print axioms SargentStachurski.NonlinearValuation.concaveOn_powF
#print axioms SargentStachurski.NonlinearValuation.powG
#print axioms SargentStachurski.NonlinearValuation.powG_apply
#print axioms SargentStachurski.NonlinearValuation.powG_mapsTo
#print axioms SargentStachurski.NonlinearValuation.powG_monotoneOn
#print axioms SargentStachurski.NonlinearValuation.convexOn_powG
#print axioms SargentStachurski.NonlinearValuation.concaveOn_powG
#print axioms SargentStachurski.NonlinearValuation.specRad_rpow_lt_one_of_isFixedPt
#print axioms SargentStachurski.NonlinearValuation.not_isFixedPt_powG
#print axioms SargentStachurski.NonlinearValuation.scalar_bounds
#print axioms SargentStachurski.NonlinearValuation.powG_smul_eigen
#print axioms SargentStachurski.NonlinearValuation.exists_thresholds
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_powG_Icc
#print axioms SargentStachurski.NonlinearValuation.exists_interval
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_powG
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_powG_iff
#print axioms SargentStachurski.NonlinearValuation.kleinmanA
#print axioms SargentStachurski.NonlinearValuation.IsKleinmanSol
#print axioms SargentStachurski.NonlinearValuation.isKleinmanSol_iff
#print axioms SargentStachurski.NonlinearValuation.existsUnique_kleinmanSol_iff
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.mk
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.mapsTo
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.mono
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.const
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.isCertEquiv
#print axioms SargentStachurski.NonlinearValuation.isCertEquiv_mulVec_iff
#print axioms SargentStachurski.NonlinearValuation.IsMarkov.mulVec_pos
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.zero_and_nonneg
#print axioms SargentStachurski.NonlinearValuation.IsCertEquiv.convex_comb
#print axioms SargentStachurski.NonlinearValuation.PosHomogeneous
#print axioms SargentStachurski.NonlinearValuation.Superadditive
#print axioms SargentStachurski.NonlinearValuation.Subadditive
#print axioms SargentStachurski.NonlinearValuation.ConstSubadditive
#print axioms SargentStachurski.NonlinearValuation.mulVec_properties
#print axioms SargentStachurski.NonlinearValuation.nonexpansive_of_constSubadditive
#print axioms SargentStachurski.NonlinearValuation.convexOn_of_subadditive
#print axioms SargentStachurski.NonlinearValuation.concaveOn_of_superadditive
#print axioms SargentStachurski.NonlinearValuation.entR
#print axioms SargentStachurski.NonlinearValuation.entR_add_const
#print axioms SargentStachurski.NonlinearValuation.isCertEquiv_entR
#print axioms SargentStachurski.NonlinearValuation.constSubadditive_entR
#print axioms SargentStachurski.NonlinearValuation.log_sum_exp_le
#print axioms SargentStachurski.NonlinearValuation.concaveOn_entR
#print axioms SargentStachurski.NonlinearValuation.kpR
#print axioms SargentStachurski.NonlinearValuation.kpR_pos
#print axioms SargentStachurski.NonlinearValuation.isCertEquiv_kpR
#print axioms SargentStachurski.NonlinearValuation.posHomogeneous_kpR
#print axioms SargentStachurski.NonlinearValuation.sum_rpow_normalize
#print axioms SargentStachurski.NonlinearValuation.sum_rpow_add_le
#print axioms SargentStachurski.NonlinearValuation.le_sum_rpow_add
#print axioms SargentStachurski.NonlinearValuation.convexOn_rpow_of_neg
#print axioms SargentStachurski.NonlinearValuation.subadditive_kpR
#print axioms SargentStachurski.NonlinearValuation.superadditive_kpR
#print axioms SargentStachurski.NonlinearValuation.smul_mem_posCone
#print axioms SargentStachurski.NonlinearValuation.convexOn_kpR
#print axioms SargentStachurski.NonlinearValuation.concaveOn_kpR
#print axioms SargentStachurski.NonlinearValuation.condCdf
#print axioms SargentStachurski.NonlinearValuation.quantR
#print axioms SargentStachurski.NonlinearValuation.isLeast_quantR
#print axioms SargentStachurski.NonlinearValuation.isCertEquiv_quantR
#print axioms SargentStachurski.NonlinearValuation.quantR_add_const
#print axioms SargentStachurski.NonlinearValuation.constSubadditive_quantR
#print axioms SargentStachurski.NonlinearValuation.MonotoneKernel
#print axioms SargentStachurski.NonlinearValuation.MonotoneKernel.antitone
#print axioms SargentStachurski.NonlinearValuation.monotone_entR
#print axioms SargentStachurski.NonlinearValuation.monotone_kpR
#print axioms SargentStachurski.NonlinearValuation.IsAggregator
#print axioms SargentStachurski.NonlinearValuation.IsAggregator.mk
#print axioms SargentStachurski.NonlinearValuation.IsAggregator.values
#print axioms SargentStachurski.NonlinearValuation.IsAggregator.mapsTo
#print axioms SargentStachurski.NonlinearValuation.IsAggregator.mono
#print axioms SargentStachurski.NonlinearValuation.leontief
#print axioms SargentStachurski.NonlinearValuation.uzawa
#print axioms SargentStachurski.NonlinearValuation.cesAgg
#print axioms SargentStachurski.NonlinearValuation.additive
#print axioms SargentStachurski.NonlinearValuation.cesUzawa
#print axioms SargentStachurski.NonlinearValuation.additive_eq_uzawa
#print axioms SargentStachurski.NonlinearValuation.additive_eq_cesAgg
#print axioms SargentStachurski.NonlinearValuation.isAggregator_leontief
#print axioms SargentStachurski.NonlinearValuation.isAggregator_uzawa
#print axioms SargentStachurski.NonlinearValuation.isAggregator_additive
#print axioms SargentStachurski.NonlinearValuation.isAggregator_cesUzawa
#print axioms SargentStachurski.NonlinearValuation.isAggregator_cesAgg
#print axioms SargentStachurski.NonlinearValuation.koopmans
#print axioms SargentStachurski.NonlinearValuation.koopmans_mapsTo_monotoneOn
#print axioms SargentStachurski.NonlinearValuation.koopmans_additive_entR
#print axioms SargentStachurski.NonlinearValuation.koopmans_cesAgg_kpR
#print axioms SargentStachurski.NonlinearValuation.koopmans_additive_mulVec
#print axioms SargentStachurski.NonlinearValuation.ces_eis
#print axioms SargentStachurski.NonlinearValuation.iterate_additive_eq
#print axioms SargentStachurski.NonlinearValuation.additive_lifetimeValue
#print axioms SargentStachurski.NonlinearValuation.monotone_of_globallyStableOn
#print axioms SargentStachurski.NonlinearValuation.monotone_koopmans_fixedPt
#print axioms SargentStachurski.NonlinearValuation.IsBlackwellAgg
#print axioms SargentStachurski.NonlinearValuation.isBlackwellAgg_additive
#print axioms SargentStachurski.NonlinearValuation.isBlackwellAgg_leontief
#print axioms SargentStachurski.NonlinearValuation.isContractionOn_koopmans
#print axioms SargentStachurski.NonlinearValuation.globallyStable_koopmans
#print axioms SargentStachurski.NonlinearValuation.globallyStable_riskSensitive
#print axioms SargentStachurski.NonlinearValuation.globallyStable_leontief
#print axioms SargentStachurski.NonlinearValuation.globallyStable_quantile
#print axioms SargentStachurski.NonlinearValuation.globallyStable_leontief_quantile
#print axioms SargentStachurski.NonlinearValuation.koopmans_uzawa_mulVec
#print axioms SargentStachurski.NonlinearValuation.uzawa_lifetimeValue
#print axioms SargentStachurski.NonlinearValuation.irreducible_uzawa
#print axioms SargentStachurski.NonlinearValuation.uzawa_no_pos_fixedPt
#print axioms SargentStachurski.NonlinearValuation.nonnegCone
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_uzawa_concave
#print axioms SargentStachurski.NonlinearValuation.timeAdditive_solution
#print axioms SargentStachurski.NonlinearValuation.entExp
#print axioms SargentStachurski.NonlinearValuation.entR_eq_entExp
#print axioms SargentStachurski.NonlinearValuation.entExp_add_const
#print axioms SargentStachurski.NonlinearValuation.entExp_gaussian
#print axioms SargentStachurski.NonlinearValuation.exp_mean_le
#print axioms SargentStachurski.NonlinearValuation.mul_mean_le_log
#print axioms SargentStachurski.NonlinearValuation.entExp_le_mean
#print axioms SargentStachurski.NonlinearValuation.mean_le_entExp
#print axioms SargentStachurski.NonlinearValuation.entExp_ne_mean
#print axioms SargentStachurski.NonlinearValuation.entExp_eq_mean
#print axioms SargentStachurski.NonlinearValuation.integral_exp_add_mul_gaussian
#print axioms SargentStachurski.NonlinearValuation.riskSensitive_gaussian
#print axioms SargentStachurski.NonlinearValuation.riskSensitive_iid
#print axioms SargentStachurski.NonlinearValuation.riskSensitive_iid_unique
#print axioms SargentStachurski.NonlinearValuation.ezK
#print axioms SargentStachurski.NonlinearValuation.ezK_eq_koopmans
#print axioms SargentStachurski.NonlinearValuation.ezK_apply_ez
#print axioms SargentStachurski.NonlinearValuation.ezK_mapsTo
#print axioms SargentStachurski.NonlinearValuation.powMap
#print axioms SargentStachurski.NonlinearValuation.powMap_mapsTo
#print axioms SargentStachurski.NonlinearValuation.powMap_inv
#print axioms SargentStachurski.NonlinearValuation.powMap_inv'
#print axioms SargentStachurski.NonlinearValuation.continuousOn_powMap
#print axioms SargentStachurski.NonlinearValuation.ezB
#print axioms SargentStachurski.NonlinearValuation.powMap_ezK
#print axioms SargentStachurski.NonlinearValuation.irreducible_ezB
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_ezK_iff
#print axioms SargentStachurski.NonlinearValuation.globallyStableOn_ez
#print axioms SargentStachurski.NonlinearValuation.ez_deriv_tendsto_atTop
#print axioms SargentStachurski.NonlinearValuation.monotone_ez_lifetimeValue
