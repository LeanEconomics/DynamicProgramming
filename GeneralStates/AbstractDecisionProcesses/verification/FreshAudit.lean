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
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic.LinearCombination
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Topology.EMetricSpace.Lipschitz
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Volume 2, Chapter 2 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.AbstractDecisionProcesses

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

end SargentStachurski.AbstractDecisionProcesses

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

namespace SargentStachurski.AbstractDecisionProcesses

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

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contractions for the supremum distance

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Appendix A (§A.2.2, §A.4.2, §A.5.2):
the facts about bounded functions and contractions that Chapter 1 uses.

Value functions live in a set `V` of real functions on a set `X`, such as the bounded measurable
functions `bX` (§A.4.2.4). The supremum distance is handled pointwise: `T` is a `β`-contraction
on `V` when `|v − w| ≤ c` everywhere implies `|Tv − Tw| ≤ βc` everywhere.

* **Banach's theorem on `bX`**: if every element of `V` is bounded and `V` is closed under
  uniform limits, then a `β`-contraction of `V` with `β < 1` has a unique fixed point, and its
  iterates converge to it uniformly from every starting point, at rate `β^n` (global stability,
  §A.2.2.2). The set `bX` of bounded measurable functions is closed under uniform limits.
* An order preserving globally stable map is order stable (Lemma A.5.19): `v ≤ Tv` implies
  `v ≤ v̄` and `Tv ≤ v` implies `v̄ ≤ v`.
* `|α ∨ x − α ∨ y| ≤ |x − y|` (p. 8) and Corollary A.5.13, `|sup f − sup g| ≤ sup |f − g|`.
-/

open Filter Topology Set Function

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*}

/-- `f` is bounded. -/
def IsBdd (f : X → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

/-- `T` is a `β`-contraction of `V` for the supremum distance (§A.2.2.2). -/
def IsSupContraction (V : Set (X → ℝ)) (T : (X → ℝ) → X → ℝ) (β : ℝ) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, ∀ c : ℝ, (∀ x, |v x - w x| ≤ c) → ∀ x, |T v x - T w x| ≤ β * c

/-- `V` is closed under uniform limits of sequences. -/
def IsUniformlyClosed (V : Set (X → ℝ)) : Prop :=
  ∀ f : ℕ → X → ℝ, (∀ n, f n ∈ V) → ∀ g, TendstoUniformly f g atTop → g ∈ V

theorem isBdd_const (c : ℝ) : IsBdd (fun _ : X => c) := ⟨|c|, fun _ => le_rfl⟩

theorem IsBdd.sub {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (f - g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, fun x => ?_⟩
  simp only [Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hM x) (hN x))

theorem IsBdd.add {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (f + g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, fun x => ?_⟩
  simp only [Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hM x) (hN x))

theorem IsBdd.nonneg_bound {f : X → ℝ} (hf : IsBdd f) : ∃ M, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

/-- Two bounded functions are within a finite supremum distance. -/
theorem IsBdd.exists_dist {f g : X → ℝ} (hf : IsBdd f) (hg : IsBdd g) :
    ∃ c, 0 ≤ c ∧ ∀ x, |f x - g x| ≤ c := by
  obtain ⟨c, hc0, hc⟩ := (hf.sub hg).nonneg_bound
  exact ⟨c, hc0, hc⟩

variable {V : Set (X → ℝ)} {T : (X → ℝ) → X → ℝ} {β : ℝ}

/-- Iterating the contraction inequality: `|v − w| ≤ c` gives `|Tⁿv − Tⁿw| ≤ βⁿc`. -/
theorem IsSupContraction.iterate (hT : MapsTo T V V) (hc : IsSupContraction V T β)
    {v w : X → ℝ} (hv : v ∈ V) (hw : w ∈ V) {c : ℝ} (hvw : ∀ x, |v x - w x| ≤ c) (n : ℕ) :
    ∀ x, |T^[n] v x - T^[n] w x| ≤ β ^ n * c := by
  induction n with
  | zero => simpa using hvw
  | succ n ih =>
    intro x
    rw [iterate_succ_apply', iterate_succ_apply', pow_succ, mul_comm (β ^ n) β, mul_assoc]
    exact hc _ (hT.iterate n hv) _ (hT.iterate n hw) _ ih x

/-- A contraction has at most one fixed point among bounded functions. -/
theorem IsSupContraction.eq_of_isFixedPt (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : IsSupContraction V T β) {u w : X → ℝ} (hu : u ∈ V) (hw : w ∈ V) (hub : IsBdd u)
    (hwb : IsBdd w) (hTu : T u = u) (hTw : T w = w) : u = w := by
  obtain ⟨c, -, hcd⟩ := hub.exists_dist hwb
  have key : ∀ n : ℕ, ∀ x, |u x - w x| ≤ β ^ n * c := by
    intro n
    induction n with
    | zero => simpa using hcd
    | succ n ih =>
      intro x
      have := hc u hu w hw _ ih x
      rw [hTu, hTw] at this
      rwa [pow_succ, mul_comm (β ^ n) β, mul_assoc]
  funext x
  have hlim : Tendsto (fun n : ℕ => β ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const c
  have h0 : |u x - w x| ≤ 0 := ge_of_tendsto' hlim fun n => key n x
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **Banach's theorem on `bX`**, construction step: from any `v ∈ V` the iterates `Tⁿv`
converge uniformly, at rate `βⁿc/(1 − β)` where `|Tv − v| ≤ c`, to a fixed point of `T` in `V`. -/
theorem IsSupContraction.exists_limit (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbdd : ∀ v ∈ V, IsBdd v) (hV : IsUniformlyClosed V) (hT : MapsTo T V V)
    (hc : IsSupContraction V T β) {v : X → ℝ} (hv : v ∈ V) :
    ∃ u ∈ V, T u = u ∧ TendstoUniformly (fun n => T^[n] v) u atTop ∧
      ∃ c, 0 ≤ c ∧ ∀ n x, |T^[n] v x - u x| ≤ c * β ^ n / (1 - β) := by
  obtain ⟨c, hc0, hcd⟩ := (hbdd _ (hT hv)).exists_dist (hbdd _ hv)
  -- consecutive iterates are `βⁿc` apart
  have hstep : ∀ n x, dist (T^[n] v x) (T^[n + 1] v x) ≤ c * β ^ n := fun n x => by
    have := hc.iterate hT (hT hv) hv hcd n x
    rw [Real.dist_eq, abs_sub_comm, iterate_succ_apply, mul_comm]
    exact this
  have hlim : ∀ x, ∃ a, Tendsto (fun n => T^[n] v x) atTop (𝓝 a) := fun x =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric β c hβ1 (hstep · x))
  choose u hu using hlim
  have hbound : ∀ n x, |T^[n] v x - u x| ≤ c * β ^ n / (1 - β) := fun n x => by
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto β c hβ1 (hstep · x) (hu x) n
  have hrate : Tendsto (fun n : ℕ => c * β ^ n / (1 - β)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul c).div_const (1 - β)
  have hunif : TendstoUniformly (fun n => T^[n] v) u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hrate).2 ε hε] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact (hbound n x).trans_lt hn
  have huV : u ∈ V := hV _ (fun n => hT.iterate n hv) u hunif
  refine ⟨u, huV, ?_, hunif, c, hc0, hbound⟩
  -- `T u = u`: `T^{n+1} v → u` and `|T u − T^{n+1} v| ≤ β · rate`
  funext x
  have h1 : Tendsto (fun n => T^[n + 1] v x) atTop (𝓝 (u x)) :=
    (hu x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => T^[n + 1] v x) atTop (𝓝 (T u x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (hrate.const_mul β |>.trans
      (by simp))
    rw [Real.dist_eq, iterate_succ_apply', abs_sub_comm]
    exact hc _ huV _ (hT.iterate n hv) _ (fun y => by
      rw [abs_sub_comm]; exact hbound n y) x
  exact tendsto_nhds_unique h2 h1

/-- **Banach's contraction mapping theorem on `bX`** (§A.2.2.2): a `β`-contraction (`β < 1`) of a
nonempty set `V` of bounded functions closed under uniform limits is globally stable. -/
theorem IsSupContraction.globallyStable (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hbdd : ∀ v ∈ V, IsBdd v) (hV : IsUniformlyClosed V) (hT : MapsTo T V V)
    (hc : IsSupContraction V T β) (hne : V.Nonempty) :
    ∃ u ∈ V, T u = u ∧ (∀ w ∈ V, T w = w → w = u) ∧
      ∀ v ∈ V, TendstoUniformly (fun n => T^[n] v) u atTop := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨u, huV, hTu, -, -⟩ := hc.exists_limit hβ0 hβ1 hbdd hV hT hv₀
  refine ⟨u, huV, hTu, fun w hw hTw =>
    hc.eq_of_isFixedPt hβ0 hβ1 hw huV (hbdd w hw) (hbdd u huV) hTw hTu, fun v hv => ?_⟩
  obtain ⟨u', hu'V, hTu', hlim, -⟩ := hc.exists_limit hβ0 hβ1 hbdd hV hT hv
  rwa [hc.eq_of_isFixedPt hβ0 hβ1 hu'V huV (hbdd _ hu'V) (hbdd _ huV) hTu' hTu] at hlim

/-- **Lemma A.5.19**, first half: if `T` is order preserving on `V` and its iterates from `v`
converge to `u`, then `v ≤ Tv` implies `v ≤ u`. -/
theorem le_of_le_map_of_tendsto (hT : MapsTo T V V)
    (hmono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T v ≤ T w) {v u : X → ℝ} (hv : v ∈ V)
    (hlim : TendstoUniformly (fun n => T^[n] v) u atTop) (hle : v ≤ T v) : v ≤ u := by
  have hn : ∀ n, v ≤ T^[n] v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact hle.trans (hmono _ hv _ (hT.iterate n hv) ih)
  exact fun x => ge_of_tendsto' (hlim.tendsto_at x) fun n => hn n x

/-- **Lemma A.5.19**, second half: `Tv ≤ v` implies `u ≤ v`. -/
theorem le_of_map_le_of_tendsto (hT : MapsTo T V V)
    (hmono : ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T v ≤ T w) {v u : X → ℝ} (hv : v ∈ V)
    (hlim : TendstoUniformly (fun n => T^[n] v) u atTop) (hle : T v ≤ v) : u ≤ v := by
  have hn : ∀ n, T^[n] v ≤ v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact (hmono _ (hT.iterate n hv) _ hv ih).trans hle
  exact fun x => le_of_tendsto' (hlim.tendsto_at x) fun n => hn n x

/-! ### Bounded measurable functions -/

/-- `bX`: the bounded measurable real functions on a measurable space (§A.4.2.4). -/
def bX (X : Type*) [MeasurableSpace X] : Set (X → ℝ) := {f | Measurable f ∧ IsBdd f}

/-- `bX` is closed under uniform limits. -/
theorem isUniformlyClosed_bX [MeasurableSpace X] : IsUniformlyClosed (bX X) := by
  intro f hf g hg
  refine ⟨measurable_of_tendsto_metrizable (fun n => (hf n).1)
    (tendsto_pi_nhds.2 fun x => hg.tendsto_at x), ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.1 hg 1 one_pos).exists
  obtain ⟨M, hM⟩ := (hf N).2
  refine ⟨M + 1, fun x => ?_⟩
  have h := hN x
  rw [Real.dist_eq] at h
  calc |g x| = |f N x + (g x - f N x)| := by ring_nf
    _ ≤ |f N x| + |g x - f N x| := abs_add_le _ _
    _ ≤ M + 1 := add_le_add (hM x) h.le

theorem const_mem_bX [MeasurableSpace X] (c : ℝ) : (fun _ : X => c) ∈ bX X :=
  ⟨measurable_const, isBdd_const c⟩

/-! ### Two elementary inequalities -/

/-- `|α ∨ x − α ∨ y| ≤ |x − y|` (p. 8). -/
theorem abs_max_sub_max_le (α x y : ℝ) : |max α x - max α y| ≤ |x - y| := by
  rw [max_comm α x, max_comm α y]
  exact abs_max_sub_max_le_abs x y α

/-- **Corollary A.5.13** (p. 377), for bounded above families of reals:
`|sup f − sup g| ≤ c` whenever `|f − g| ≤ c` pointwise. -/
theorem abs_ciSup_sub_ciSup_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) {c : ℝ} (hfg : ∀ i, |f i - g i| ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (hfg i)).1
      have := le_ciSup hg i
      linarith
  · rw [sub_le_iff_le_add]
    exact ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (hfg i)).2
      have := le_ciSup hf i
      linarith

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contracting dynamic programs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Chapter 1: the common structure of the
proofs of Theorems 1.1.1 and 1.2.1–1.2.2 (§1.1.1.4, pp. 9–10).

A *contracting dynamic program* is a family of policy operators `T_σ` on a set `V` of bounded
functions closed under uniform limits, each order preserving and a `β`-contraction for the
supremum distance (`β < 1`), such that every `v ∈ V` has a `v`-greedy policy. This is the
setting of the firm problem (§1.1), finite MDPs (§1.2) and the optimal savings problem (§1.3).

* `v_σ` is the unique fixed point of `T_σ` in `V`, the limit of `T_σⁿ v` from every `v ∈ V`.
* The Bellman operator `Tv = T_σ v` for a `v`-greedy `σ` is the pointwise supremum
  `sup_σ T_σ v`, is order preserving and is a `β`-contraction.
* **Theorem 1.1.1** (abstract form): the value function `v* = sup_σ v_σ` is the greatest
  element of `{v_σ}`, the unique solution of the Bellman equation in `V`, and a policy is
  optimal iff it is `v*`-greedy; an optimal policy exists, and `Tᵏv → v*` (VFI).
* **Theorem 1.2.2**: HPI reaches an optimal policy in finitely many steps when the policy set is
  finite, and, when the policy operators shift constants by `β` (`T_σ(v − c) = T_σ v − βc`),
  OPI converges from every starting point.
* **Lemma 1.2.3**: `Tv ≤ v` implies `v* ≤ v`.
-/

open Filter Topology Set Function

namespace SargentStachurski.AbstractDecisionProcesses

/-- A contracting dynamic program: policy operators `T_σ` on a set `V` of bounded functions. -/
structure ContractingDP (X P : Type*) where
  /-- the candidate value functions -/
  V : Set (X → ℝ)
  /-- the policy operators -/
  T : P → (X → ℝ) → X → ℝ
  /-- the modulus of contraction -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  nonempty : V.Nonempty
  bdd : ∀ v ∈ V, IsBdd v
  closed : IsUniformlyClosed V
  mapsTo : ∀ σ, MapsTo (T σ) V V
  mono : ∀ σ, ∀ v ∈ V, ∀ w ∈ V, v ≤ w → T σ v ≤ T σ w
  contraction : ∀ σ, IsSupContraction V (T σ) β
  exists_greedy : ∀ v ∈ V, ∃ σ, ∀ τ, T τ v ≤ T σ v

namespace ContractingDP

variable {X P : Type*} (D : ContractingDP X P)

/-- Each policy operator is globally stable on `V` (§1.1.1.2). -/
theorem globallyStable (σ : P) :
    ∃ u ∈ D.V, D.T σ u = u ∧ (∀ w ∈ D.V, D.T σ w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => (D.T σ)^[n] v) u atTop :=
  (D.contraction σ).globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed (D.mapsTo σ) D.nonempty

/-- The `σ`-value function: the unique fixed point of `T_σ` in `V`. -/
noncomputable def vσ (σ : P) : X → ℝ := (D.globallyStable σ).choose

theorem vσ_mem (σ : P) : D.vσ σ ∈ D.V := (D.globallyStable σ).choose_spec.1

theorem T_vσ (σ : P) : D.T σ (D.vσ σ) = D.vσ σ := (D.globallyStable σ).choose_spec.2.1

theorem eq_vσ {σ : P} {w : X → ℝ} (hw : w ∈ D.V) (h : D.T σ w = w) : w = D.vσ σ :=
  (D.globallyStable σ).choose_spec.2.2.1 w hw h

theorem tendsto_vσ (σ : P) {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => (D.T σ)^[n] v) (D.vσ σ) atTop :=
  (D.globallyStable σ).choose_spec.2.2.2 v hv

/-- Order stability of `T_σ`: `v ≤ T_σ v` implies `v ≤ v_σ`. -/
theorem le_vσ {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.T σ v) : v ≤ D.vσ σ :=
  le_of_le_map_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- Order stability of `T_σ`: `T_σ v ≤ v` implies `v_σ ≤ v`. -/
theorem vσ_le {σ : P} {v : X → ℝ} (hv : v ∈ D.V) (h : D.T σ v ≤ v) : D.vσ σ ≤ v :=
  le_of_map_le_of_tendsto (D.mapsTo σ) (D.mono σ) hv (D.tendsto_vσ σ hv) h

/-- `σ` is `v`-greedy: `T_τ v ≤ T_σ v` for every policy `τ`. -/
def IsGreedy (v : X → ℝ) (σ : P) : Prop := ∀ τ, D.T τ v ≤ D.T σ v

include D in
/-- The policy set is nonempty. -/
theorem nonempty_policy : Nonempty P :=
  ⟨(D.exists_greedy _ D.nonempty.some_mem).choose⟩

/-- A chosen `v`-greedy policy (an arbitrary policy off `V`). -/
noncomputable def greedy (v : X → ℝ) : P :=
  @Classical.epsilon P D.nonempty_policy fun σ => v ∈ D.V → D.IsGreedy v σ

theorem isGreedy_greedy {v : X → ℝ} (hv : v ∈ D.V) : D.IsGreedy v (D.greedy v) := by
  obtain ⟨σ, hσ⟩ := D.exists_greedy v hv
  exact @Classical.epsilon_spec P (fun σ => v ∈ D.V → D.IsGreedy v σ) ⟨σ, fun _ => hσ⟩ hv

/-- The Bellman operator `Tv = T_σ v` for the chosen `v`-greedy `σ`. -/
noncomputable def bellman (v : X → ℝ) : X → ℝ := D.T (D.greedy v) v

theorem bellman_mapsTo : MapsTo D.bellman D.V D.V := fun _ hv => D.mapsTo _ hv

theorem T_le_bellman (σ : P) {v : X → ℝ} (hv : v ∈ D.V) : D.T σ v ≤ D.bellman v :=
  D.isGreedy_greedy hv σ

/-- Greedy policies are those attaining the Bellman operator (Exercises 1.1.3 and 1.2.4). -/
theorem isGreedy_iff {v : X → ℝ} (hv : v ∈ D.V) (σ : P) :
    D.IsGreedy v σ ↔ D.T σ v = D.bellman v :=
  ⟨fun h => le_antisymm (D.T_le_bellman σ hv) (h _), fun h τ => h ▸ D.T_le_bellman τ hv⟩

/-- The Bellman operator is the pointwise supremum of the policy operators. -/
theorem bellman_eq_iSup {v : X → ℝ} (hv : v ∈ D.V) (x : X) :
    D.bellman v x = ⨆ σ, D.T σ v x := by
  have := D.nonempty_policy
  refine le_antisymm ?_ (ciSup_le fun σ => D.T_le_bellman σ hv x)
  exact le_ciSup (f := fun σ => D.T σ v x)
    ⟨D.bellman v x, by rintro _ ⟨σ, rfl⟩; exact D.T_le_bellman σ hv x⟩ (D.greedy v)

theorem bellman_mono {v w : X → ℝ} (hv : v ∈ D.V) (hw : w ∈ D.V) (h : v ≤ w) :
    D.bellman v ≤ D.bellman w :=
  (D.mono _ v hv w hw h).trans (D.T_le_bellman _ hw)

/-- The Bellman operator is a `β`-contraction (§1.1.1.3, Exercise 1.2.3). -/
theorem bellman_contraction : IsSupContraction D.V D.bellman D.β := by
  intro v hv w hw c hc x
  have h1 := D.contraction (D.greedy v) v hv w hw c hc x
  have h2 := D.contraction (D.greedy w) v hv w hw c hc x
  have a1 := D.T_le_bellman (D.greedy v) hw x
  have a2 := D.T_le_bellman (D.greedy w) hv x
  rw [abs_le] at h1 h2 ⊢
  simp only [bellman] at a1 a2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem bellman_globallyStable :
    ∃ u ∈ D.V, D.bellman u = u ∧ (∀ w ∈ D.V, D.bellman w = w → w = u) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) u atTop :=
  D.bellman_contraction.globallyStable D.β_nonneg D.β_lt_one D.bdd D.closed D.bellman_mapsTo
    D.nonempty

/-- The value function `v*`, the fixed point of the Bellman operator. -/
noncomputable def vstar : X → ℝ := D.bellman_globallyStable.choose

theorem vstar_mem : D.vstar ∈ D.V := D.bellman_globallyStable.choose_spec.1

theorem bellman_vstar : D.bellman D.vstar = D.vstar := D.bellman_globallyStable.choose_spec.2.1

theorem eq_vstar {w : X → ℝ} (hw : w ∈ D.V) (h : D.bellman w = w) : w = D.vstar :=
  D.bellman_globallyStable.choose_spec.2.2.1 w hw h

/-- **VFI** (§1.1.1.3): `Tᵏ v → v*` uniformly for every `v ∈ V`. -/
theorem tendsto_bellman_iterate {v : X → ℝ} (hv : v ∈ D.V) :
    TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop :=
  D.bellman_globallyStable.choose_spec.2.2.2 v hv

/-- Every `σ`-value function lies below `v*` (the second inequality in the proof of
Theorem 1.1.1). -/
theorem vσ_le_vstar (σ : P) : D.vσ σ ≤ D.vstar :=
  D.vσ_le D.vstar_mem ((D.T_le_bellman σ D.vstar_mem).trans D.bellman_vstar.le)

/-- `σ` attains `v*` iff it is `v*`-greedy. -/
theorem vσ_eq_vstar_iff (σ : P) : D.vσ σ = D.vstar ↔ D.IsGreedy D.vstar σ := by
  rw [D.isGreedy_iff D.vstar_mem, D.bellman_vstar]
  constructor
  · intro h
    rw [← h, D.T_vσ]
  · intro h
    exact (D.eq_vσ D.vstar_mem h).symm

/-- A `σ` is optimal: `v_τ ≤ v_σ` for every `τ`. -/
def IsOptimal (σ : P) : Prop := ∀ τ, D.vσ τ ≤ D.vσ σ

theorem isOptimal_iff (σ : P) : D.IsOptimal σ ↔ D.vσ σ = D.vstar := by
  constructor
  · intro h
    refine le_antisymm (D.vσ_le_vstar σ) ?_
    have hg := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
    exact hg ▸ h _
  · intro h τ
    exact h ▸ D.vσ_le_vstar τ

/-- **Theorem 1.1.1**, abstract form (pp. 6–10): `v*` is the greatest `σ`-value function and the
pointwise supremum of them, it is the unique solution of the Bellman equation in `V`, a policy
is optimal iff it is `v*`-greedy, an optimal policy exists, and VFI converges. -/
theorem optimality :
    IsGreatest (range D.vσ) D.vstar ∧ (∀ x, D.vstar x = ⨆ σ, D.vσ σ x) ∧
      (∀ v ∈ D.V, D.bellman v = v ↔ v = D.vstar) ∧
      (∀ σ, D.IsOptimal σ ↔ D.IsGreedy D.vstar σ) ∧ (∃ σ, D.IsOptimal σ) ∧
      ∀ v ∈ D.V, TendstoUniformly (fun n => D.bellman^[n] v) D.vstar atTop := by
  have hopt := (D.vσ_eq_vstar_iff (D.greedy D.vstar)).2 (D.isGreedy_greedy D.vstar_mem)
  have := D.nonempty_policy
  refine ⟨⟨⟨_, hopt⟩, ?_⟩, fun x => ?_, fun v hv => ⟨D.eq_vstar hv, fun h => h ▸ D.bellman_vstar⟩,
    fun σ => (D.isOptimal_iff σ).trans (D.vσ_eq_vstar_iff σ),
    ⟨_, (D.isOptimal_iff _).2 hopt⟩, fun v hv => D.tendsto_bellman_iterate hv⟩
  · rintro _ ⟨σ, rfl⟩
    exact D.vσ_le_vstar σ
  · refine le_antisymm ?_ (ciSup_le fun σ => D.vσ_le_vstar σ x)
    conv_lhs => rw [← hopt]
    exact le_ciSup ⟨D.vstar x, by rintro _ ⟨σ, rfl⟩; exact D.vσ_le_vstar σ x⟩ _

/-- **Lemma 1.2.3** (p. 25): `Tv ≤ v` implies `v* ≤ v`. -/
theorem vstar_le_of_bellman_le {v : X → ℝ} (hv : v ∈ D.V) (h : D.bellman v ≤ v) :
    D.vstar ≤ v :=
  le_of_map_le_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-- `v ≤ Tv` implies `v ≤ v*`. -/
theorem le_vstar_of_le_bellman {v : X → ℝ} (hv : v ∈ D.V) (h : v ≤ D.bellman v) :
    v ≤ D.vstar :=
  le_of_le_map_of_tendsto D.bellman_mapsTo (fun _ ha _ hb hab => D.bellman_mono ha hb hab) hv
    (D.tendsto_bellman_iterate hv) h

/-! ### Howard policy iteration -/

/-- HPI (Algorithm 1.2): `σ₀` given and `σ_{k+1}` a `v_{σ_k}`-greedy policy. -/
noncomputable def hpiPolicy (σ₀ : P) : ℕ → P
  | 0 => σ₀
  | k + 1 => D.greedy (D.vσ (hpiPolicy σ₀ k))

/-- HPI values increase. -/
theorem vσ_hpi_le_succ (σ₀ : P) (k : ℕ) :
    D.vσ (D.hpiPolicy σ₀ k) ≤ D.vσ (D.hpiPolicy σ₀ (k + 1)) := by
  set σ := D.hpiPolicy σ₀ k
  refine D.le_vσ (D.vσ_mem σ) ?_
  change D.vσ σ ≤ D.T (D.greedy (D.vσ σ)) (D.vσ σ)
  calc D.vσ σ = D.T σ (D.vσ σ) := (D.T_vσ σ).symm
    _ ≤ _ := D.isGreedy_greedy (D.vσ_mem σ) σ

/-- A repeated HPI value is `v*`. -/
theorem vσ_hpi_eq_vstar {σ₀ : P} {k : ℕ}
    (h : D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k)) :
    D.vσ (D.hpiPolicy σ₀ k) = D.vstar := by
  set v := D.vσ (D.hpiPolicy σ₀ k)
  refine D.eq_vstar (D.vσ_mem _) ?_
  change D.T (D.greedy v) v = v
  have hτ : D.vσ (D.greedy v) = v := h
  calc D.T (D.greedy v) v = D.T (D.greedy v) (D.vσ (D.greedy v)) := by rw [hτ]
    _ = D.vσ (D.greedy v) := D.T_vσ _
    _ = v := hτ

/-- **Theorem 1.2.2**, HPI part (p. 24): with finitely many policies, HPI reaches `v*` in finitely
many steps, after which every policy it produces is optimal. -/
theorem hpi_terminates [Finite P] (σ₀ : P) :
    ∃ k, ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar ∧ D.IsOptimal (D.hpiPolicy σ₀ j) := by
  have hk : ∃ k, D.vσ (D.hpiPolicy σ₀ (k + 1)) = D.vσ (D.hpiPolicy σ₀ k) := by
    by_contra hne
    push Not at hne
    have hsm : StrictMono fun k => D.vσ (D.hpiPolicy σ₀ k) :=
      strictMono_nat_of_lt_succ fun k => lt_of_le_of_ne (D.vσ_hpi_le_succ σ₀ k) (hne k).symm
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (D.hpiPolicy σ₀)
    exact hij (hsm.injective (by simp only [heq]))
  obtain ⟨k, hk⟩ := hk
  have h0 := D.vσ_hpi_eq_vstar hk
  have hall : ∀ j, k ≤ j → D.vσ (D.hpiPolicy σ₀ j) = D.vstar := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact h0
    | succ j _ ih =>
      change D.vσ (D.greedy (D.vσ (D.hpiPolicy σ₀ j))) = D.vstar
      rw [ih]
      exact (D.vσ_eq_vstar_iff _).2 (D.isGreedy_greedy D.vstar_mem)
  exact ⟨k, fun j hj => ⟨hall j hj, (D.isOptimal_iff _).2 (hall j hj)⟩⟩

/-! ### Optimistic policy iteration -/

/-- OPI (Algorithm 1.3): `v_{n+1} = T_σ^m v_n` for the chosen `v_n`-greedy `σ`. -/
noncomputable def opi (m : ℕ) (v₀ : X → ℝ) : ℕ → X → ℝ
  | 0 => v₀
  | n + 1 => (D.T (D.greedy (opi m v₀ n)))^[m] (opi m v₀ n)

/-- One OPI step from a point mapped up by `T` (Lemmas 2.2.1–2.2.4 of Chapter 2): if `u ≤ Tu`,
`σ` is `u`-greedy and `m ≥ 1`, then `w = T_σ^m u` satisfies `Tu ≤ w ≤ v*` and `w ≤ Tw`. -/
theorem opi_step {m : ℕ} (hm : 1 ≤ m) {u : X → ℝ} (hu : u ∈ D.V) (hup : u ≤ D.bellman u)
    {σ : P} (hσ : D.IsGreedy u σ) :
    (D.T σ)^[m] u ∈ D.V ∧ D.bellman u ≤ (D.T σ)^[m] u ∧ (D.T σ)^[m] u ≤ D.vstar ∧
      (D.T σ)^[m] u ≤ D.bellman ((D.T σ)^[m] u) := by
  have hTu : D.T σ u = D.bellman u := (D.isGreedy_iff hu σ).1 hσ
  have hle : u ≤ D.T σ u := hTu ▸ hup
  -- the iterates `T_σᵏ u` increase
  have hinc : ∀ k, (D.T σ)^[k] u ≤ (D.T σ)^[k + 1] u := by
    intro k
    induction k with
    | zero => simpa using hle
    | succ k ih =>
      have := D.mono σ _ ((D.mapsTo σ).iterate k hu) _ ((D.mapsTo σ).iterate (k + 1) hu) ih
      simpa only [iterate_succ_apply'] using this
  have hmono : Monotone fun k => (D.T σ)^[k] u := monotone_nat_of_le_succ hinc
  have hwV := (D.mapsTo σ).iterate m hu
  refine ⟨hwV, ?_, ?_, ?_⟩
  · rw [← hTu]
    simpa using hmono hm
  · -- `T_σ^m u ≤ T_σ^m v_σ = v_σ ≤ v*`
    have hvσ := D.le_vσ hu hle
    have : ∀ k, (D.T σ)^[k] u ≤ D.vσ σ := by
      intro k
      induction k with
      | zero => exact hvσ
      | succ k ih =>
        rw [iterate_succ_apply']
        calc D.T σ ((D.T σ)^[k] u) ≤ D.T σ (D.vσ σ) :=
              D.mono σ _ ((D.mapsTo σ).iterate k hu) _ (D.vσ_mem σ) ih
          _ = D.vσ σ := D.T_vσ σ
    exact (this m).trans (D.vσ_le_vstar σ)
  · calc (D.T σ)^[m] u ≤ (D.T σ)^[m + 1] u := hinc m
      _ = D.T σ ((D.T σ)^[m] u) := iterate_succ_apply' _ _ _
      _ ≤ D.bellman ((D.T σ)^[m] u) := D.T_le_bellman σ hwV

/-- **Theorem 1.2.2**, OPI part (p. 24): if each `T_σ` shifts constants by `β`, then for every
`m ≥ 1` and every `v₀ ∈ V` the OPI sequence converges uniformly to `v*`. The proof runs OPI from
`v₀ − c`, which is mapped up by `T`, and squeezes it between `Tⁿ(v₀ − c)` and `v*`. -/
theorem tendsto_opi {m : ℕ} (hm : 1 ≤ m)
    (hshift : ∀ σ, ∀ v ∈ D.V, ∀ c : ℝ, D.T σ (fun x => v x - c) = fun x => D.T σ v x - D.β * c)
    (hVshift : ∀ v ∈ D.V, ∀ c : ℝ, (fun x => v x - c) ∈ D.V) {v₀ : X → ℝ} (hv₀ : v₀ ∈ D.V) :
    TendstoUniformly (D.opi m v₀) D.vstar atTop := by
  set β := D.β
  -- shifting commutes with iterates of `T_σ` and with the greedy choice
  have hiter : ∀ σ k, ∀ v ∈ D.V, ∀ c : ℝ,
      (D.T σ)^[k] (fun x => v x - c) = fun x => (D.T σ)^[k] v x - β ^ k * c := by
    intro σ k
    induction k with
    | zero => intro v _ c; simp
    | succ k ih =>
      intro v hv c
      rw [iterate_succ_apply', iterate_succ_apply', ih v hv c,
        hshift σ _ ((D.mapsTo σ).iterate k hv)]
      funext x
      ring
  have hgreedy : ∀ v ∈ D.V, ∀ c : ℝ, D.IsGreedy (fun x => v x - c) (D.greedy v) := by
    intro v hv c τ x
    rw [hshift τ v hv, hshift _ v hv]
    simp only
    linarith [D.isGreedy_greedy hv τ x]
  have hbshift : ∀ v ∈ D.V, ∀ c : ℝ,
      D.bellman (fun x => v x - c) = fun x => D.bellman v x - β * c := by
    intro v hv c
    rw [← (D.isGreedy_iff (hVshift v hv c) _).1 (hgreedy v hv c), hshift _ v hv]
    rfl
  -- the starting shift
  obtain ⟨c₁, hc₁0, hc₁⟩ := (D.bdd _ (D.bellman_mapsTo hv₀)).exists_dist (D.bdd _ hv₀)
  set c := c₁ / (1 - β)
  have h1β : 0 < 1 - β := sub_pos.2 D.β_lt_one
  have hc0 : 0 ≤ c := div_nonneg hc₁0 h1β.le
  have hcc : c₁ = (1 - β) * c := by rw [mul_div_cancel₀ _ h1β.ne']
  set u : ℕ → X → ℝ := fun n x => D.opi m v₀ n x - β ^ (n * m) * c
  have hu0 : u 0 = fun x => v₀ x - c := by funext x; simp [u, opi]
  have hstep : ∀ n, D.opi m v₀ n ∈ D.V → u (n + 1) =
      (D.T (D.greedy (D.opi m v₀ n)))^[m] (u n) := by
    intro n hn
    have : u n = fun x => D.opi m v₀ n x - β ^ (n * m) * c := rfl
    rw [this, hiter _ m _ hn]
    funext x
    simp only [u, opi]
    rw [add_mul, one_mul, pow_add]
    ring
  have hu0V : u 0 ∈ D.V := hu0 ▸ hVshift v₀ hv₀ c
  -- invariants: `u n ∈ V`, `u n ≤ T(u n)`, `Tⁿ u₀ ≤ u n ≤ v*`, and `opi n ∈ V`
  have hinv : ∀ n, D.opi m v₀ n ∈ D.V ∧ u n ∈ D.V ∧ u n ≤ D.bellman (u n) ∧
      D.bellman^[n] (u 0) ≤ u n ∧ u n ≤ D.vstar := by
    intro n
    induction n with
    | zero =>
      have hup : u 0 ≤ D.bellman (u 0) := by
        rw [hu0, hbshift v₀ hv₀ c]
        intro x
        have := (abs_le.1 (hc₁ x)).1
        simp only
        nlinarith
      exact ⟨hv₀, hu0V, hup, le_rfl, D.le_vstar_of_le_bellman hu0V hup⟩
    | succ n ih =>
      obtain ⟨hon, hun, hup, hlow, -⟩ := ih
      have hσ : D.IsGreedy (u n) (D.greedy (D.opi m v₀ n)) := by
        have := hgreedy _ hon (β ^ (n * m) * c)
        exact this
      obtain ⟨hwV, hTw, hwle, hwup⟩ := D.opi_step hm hun hup hσ
      have hon' : D.opi m v₀ (n + 1) ∈ D.V := (D.mapsTo _).iterate m hon
      rw [← hstep n hon] at hwV hTw hwle hwup
      refine ⟨hon', hwV, hwup, ?_, hwle⟩
      rw [iterate_succ_apply']
      exact (D.bellman_mono (D.bellman_mapsTo.iterate n hu0V) hun hlow).trans hTw
  -- squeeze: `Tⁿ u₀ ≤ u n ≤ v*` and `Tⁿ u₀ → v*`, while `opi n − u n = β^{nm} c → 0`
  have hlim := D.tendsto_bellman_iterate hu0V
  have hpow : Tendsto (fun n : ℕ => β ^ n * c) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.β_nonneg D.β_lt_one).mul_const c
  rw [Metric.tendstoUniformly_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim (ε / 2) (half_pos hε), (tendsto_order.1 hpow).2 (ε / 2) (half_pos hε)]
    with n hn hn' x
  obtain ⟨-, -, -, hlow, hup⟩ := hinv n
  have h1 := hn x
  have hpm : β ^ (n * m) ≤ β ^ n :=
    pow_le_pow_of_le_one D.β_nonneg D.β_lt_one.le (Nat.le_mul_of_pos_right n hm)
  have hpm' : β ^ (n * m) * c ≤ β ^ n * c := mul_le_mul_of_nonneg_right hpm hc0
  have hpm0 : 0 ≤ β ^ (n * m) * c := mul_nonneg (pow_nonneg D.β_nonneg _) hc0
  have hl := hlow x
  have hu := hup x
  simp only [u] at hl hu
  rw [Real.dist_eq] at h1 ⊢
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end ContractingDP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov operators on bounded measurable functions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.5.4 (pp. 385–389), as used in
Chapter 1.

A stochastic kernel `P` on a measurable space `X` (a Markov kernel) acts on bounded measurable
functions by `(Pv)(x) = ∫ v(x') P(x, dx')`. The Markov operator maps `bX` into itself, is linear
and order preserving, fixes constants, and does not increase the supremum distance (`‖P‖ = 1`,
Lemma A.5.30).
-/

open MeasureTheory ProbabilityTheory Set Function

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- The Markov operator `(Pv)(x) = ∫ v(x') P(x, dx')` (§A.5.4.2). -/
noncomputable def markovOp (P : Kernel X X) (v : X → ℝ) (x : X) : ℝ := ∫ y, v y ∂(P x)

variable (P : Kernel X X) [IsMarkovKernel P]

theorem integrable_of_mem_bX {v : X → ℝ} (hv : v ∈ bX X) (x : X) : Integrable v (P x) := by
  obtain ⟨M, hM⟩ := hv.2
  exact Integrable.of_bound hv.1.aestronglyMeasurable M (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hM y)

omit [IsMarkovKernel P] in
theorem measurable_markovOp {v : X → ℝ} (hv : Measurable v) : Measurable (markovOp P v) :=
  (hv.stronglyMeasurable.integral_kernel (κ := P)).measurable

theorem abs_markovOp_le {v : X → ℝ} {M : ℝ} (hM : ∀ x, |v x| ≤ M) (x : X) :
    |markovOp P v x| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := P x) (f := v) (C := M)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  simpa [markovOp] using this

theorem markovOp_mem_bX {v : X → ℝ} (hv : v ∈ bX X) : markovOp P v ∈ bX X := by
  obtain ⟨M, hM⟩ := hv.2
  exact ⟨measurable_markovOp P hv.1, M, abs_markovOp_le P hM⟩

/-- `P` is order preserving on `bX`. -/
theorem markovOp_mono {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) (h : v ≤ w) :
    markovOp P v ≤ markovOp P w := fun x =>
  integral_mono (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x) h

/-- `P1 = 1`: the Markov operator fixes constants. -/
theorem markovOp_const (c : ℝ) : markovOp P (fun _ => c) = fun _ => c := by
  funext x
  simp [markovOp]

theorem markovOp_add {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) :
    markovOp P (v + w) = markovOp P v + markovOp P w := by
  funext x
  exact integral_add (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x)

theorem markovOp_sub {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) :
    markovOp P (v - w) = markovOp P v - markovOp P w := by
  funext x
  exact integral_sub (integrable_of_mem_bX P hv x) (integrable_of_mem_bX P hw x)

omit [IsMarkovKernel P] in
theorem markovOp_smul (a : ℝ) (v : X → ℝ) : markovOp P (a • v) = a • markovOp P v := by
  funext x
  simp only [markovOp, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul a _

/-- Shifting by a constant: `P(v − c) = Pv − c`. -/
theorem markovOp_sub_const {v : X → ℝ} (hv : v ∈ bX X) (c : ℝ) :
    markovOp P (fun x => v x - c) = fun x => markovOp P v x - c := by
  have := markovOp_sub P hv (const_mem_bX c)
  rw [markovOp_const] at this
  exact this

/-- `‖P‖ = 1` (Lemma A.5.30): `|v − w| ≤ c` gives `|Pv − Pw| ≤ c`. -/
theorem abs_markovOp_sub_le {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ}
    (h : ∀ x, |v x - w x| ≤ c) (x : X) : |markovOp P v x - markovOp P w x| ≤ c := by
  have := abs_markovOp_le P (v := v - w) h x
  rwa [markovOp_sub P hv hw] at this

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Affine maps `v ↦ r + βLv` and the Neumann series

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Theorem A.4.10 and Corollary A.4.11
(pp. 367–368), in the form Chapter 1 uses them: (1.3), (1.17) and (1.44).

An operator `L` on `bX` is *Markov-like* when it maps `bX` into itself, is linear and order
preserving there, and satisfies `|v| ≤ M ⟹ |Lv| ≤ M` (so `‖L‖ ≤ 1`). Markov operators of
stochastic kernels are Markov-like. For `r ∈ bX` and `β ∈ [0, 1)` the map `v ↦ r + βLv` is a
`β`-contraction on `bX`, hence globally stable, and its fixed point is the Neumann series
`∑ₜ βᵗLᵗr = (I − βL)⁻¹r`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- A linear, order preserving operator on `bX` of norm at most one. -/
structure IsMarkovLike (L : (X → ℝ) → X → ℝ) : Prop where
  mapsTo : MapsTo L (bX X) (bX X)
  add : ∀ v ∈ bX X, ∀ w ∈ bX X, L (v + w) = L v + L w
  smul : ∀ a : ℝ, ∀ v ∈ bX X, L (a • v) = a • L v
  mono : ∀ v ∈ bX X, ∀ w ∈ bX X, v ≤ w → L v ≤ L w
  abs_le : ∀ v ∈ bX X, ∀ M : ℝ, (∀ x, |v x| ≤ M) → ∀ x, |L v x| ≤ M

/-- The Markov operator of a stochastic kernel is Markov-like (§A.5.4). -/
theorem isMarkovLike_markovOp (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovLike (markovOp P) :=
  ⟨fun _ h => markovOp_mem_bX P h, fun _ hv _ hw => markovOp_add P hv hw,
    fun a v _ => markovOp_smul P a v, fun _ hv _ hw h => markovOp_mono P hv hw h,
    fun _ _ _ hM => abs_markovOp_le P hM⟩

namespace IsMarkovLike

variable {L : (X → ℝ) → X → ℝ} (hL : IsMarkovLike L)
include hL

theorem sub {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) : L (v - w) = L v - L w := by
  have hnw : (-1 : ℝ) • w ∈ bX X := by
    obtain ⟨M, hM⟩ := hw.2
    exact ⟨hw.1.const_smul _, M, fun x => by simpa using hM x⟩
  have := hL.add v hv _ hnw
  rw [hL.smul _ w hw] at this
  simpa [sub_eq_add_neg] using this

theorem abs_sub_le {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) {c : ℝ}
    (h : ∀ x, |v x - w x| ≤ c) (x : X) : |L v x - L w x| ≤ c := by
  have hvw : v - w ∈ bX X := ⟨hv.1.sub hw.1, hv.2.sub hw.2⟩
  have := hL.abs_le _ hvw c h x
  rwa [hL.sub hv hw] at this

theorem iterate_mem {r : X → ℝ} (hr : r ∈ bX X) (t : ℕ) : L^[t] r ∈ bX X :=
  hL.mapsTo.iterate t hr

theorem abs_iterate_le {r : X → ℝ} (hr : r ∈ bX X) {M : ℝ} (hM : ∀ x, |r x| ≤ M) (t : ℕ)
    (x : X) : |L^[t] r x| ≤ M := by
  induction t generalizing x with
  | zero => exact hM x
  | succ t ih =>
    rw [iterate_succ_apply']
    exact hL.abs_le _ (hL.iterate_mem hr t) M ih x

end IsMarkovLike

/-- The affine map `v ↦ r + βLv`. -/
def affineOp (r : X → ℝ) (β : ℝ) (L : (X → ℝ) → X → ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => r x + β * L v x

variable {L : (X → ℝ) → X → ℝ} {r : X → ℝ} {β : ℝ}

theorem affineOp_mapsTo (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) :
    MapsTo (affineOp r β L) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, N, hN⟩ := hL.mapsTo hv
  obtain ⟨M, hM⟩ := hr.2
  refine ⟨hr.1.add (measurable_const.mul hm), M + β * N, fun x => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add (hM x) ?_)
  rw [abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hN x) hβ0

theorem affineOp_mono (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) {v w : X → ℝ} (hv : v ∈ bX X)
    (hw : w ∈ bX X) (h : v ≤ w) : affineOp r β L v ≤ affineOp r β L w := fun x =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (hL.mono v hv w hw h x) hβ0)

theorem affineOp_contraction (hL : IsMarkovLike L) (hβ0 : 0 ≤ β) :
    IsSupContraction (bX X) (affineOp r β L) β := by
  intro v hv w hw c h x
  simp only [affineOp, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hL.abs_sub_le hv hw h x) hβ0

/-- Corollary A.4.11: `v ↦ r + βLv` is globally stable on `bX`. -/
theorem affineOp_globallyStable (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ u ∈ bX X, affineOp r β L u = u ∧ (∀ w ∈ bX X, affineOp r β L w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => (affineOp r β L)^[n] v) u atTop :=
  (affineOp_contraction hL hβ0).globallyStable hβ0 hβ1 (fun _ h => h.2) isUniformlyClosed_bX
    (affineOp_mapsTo hL hr hβ0) ⟨_, const_mem_bX 0⟩

/-- The `n`-th iterate of `v ↦ r + βLv` from `0` is the partial Neumann sum `∑_{t<n} βᵗLᵗr`. -/
theorem affineOp_iterate_zero (hL : IsMarkovLike L) (hr : r ∈ bX X) (n : ℕ) :
    (affineOp r β L)^[n] (fun _ => 0) = fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x := by
  have hterm : ∀ t, β ^ t • L^[t] r ∈ bX X := fun t => by
    obtain ⟨M, hM⟩ := (hL.iterate_mem hr t).2
    refine ⟨(hL.iterate_mem hr t).1.const_smul _, |β ^ t| * M, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have hsplit : ∀ n, (fun x => ∑ t ∈ Finset.range (n + 1), β ^ t * L^[t] r x) =
      (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) + β ^ n • L^[n] r := by
    intro n; funext x; simp [Finset.sum_range_succ]
  have hmem : ∀ n, (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) ∈ bX X := by
    intro n
    induction n with
    | zero => simpa using const_mem_bX (X := X) 0
    | succ n ih =>
      rw [hsplit]
      exact ⟨ih.1.add (hterm n).1, ih.2.add (hterm n).2⟩
  -- `L` passes through the partial sums
  have hsumL : ∀ n, L (fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t] r x) =
      fun x => ∑ t ∈ Finset.range n, β ^ t * L^[t + 1] r x := by
    intro n
    induction n with
    | zero =>
      have := hL.smul 0 (fun _ => (0 : ℝ)) (const_mem_bX 0)
      simp only [zero_smul] at this
      simp only [Finset.range_zero, Finset.sum_empty]
      exact this
    | succ n ih =>
      rw [hsplit, hL.add _ (hmem n) _ (hterm n), hL.smul _ _ (hL.iterate_mem hr n), ih]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ,
        iterate_succ_apply']
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    funext x
    change r x + β * L (fun y => ∑ t ∈ Finset.range n, β ^ t * L^[t] r y) x = _
    rw [hsumL, Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, iterate_zero_apply,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ]
    ring

/-- **The Neumann series** (Theorem A.4.10, as in (1.3), (1.17), (1.44)): the fixed point of
`v ↦ r + βLv` in `bX` is `∑ₜ βᵗLᵗr = (I − βL)⁻¹r`. -/
theorem affineOp_hasSum (hL : IsMarkovLike L) (hr : r ∈ bX X) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : X → ℝ} (hu : u ∈ bX X) (hfix : affineOp r β L u = u) (x : X) :
    HasSum (fun t => β ^ t * L^[t] r x) (u x) := by
  obtain ⟨M, hM⟩ := hr.2
  have hsum : Summable fun t => β ^ t * L^[t] r x :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hβ0 hβ1 |>.mul_left M) fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hL.abs_iterate_le hr hM t x) (pow_nonneg hβ0 t)
  obtain ⟨u', -, -, huniq, hlim⟩ := affineOp_globallyStable hL hr hβ0 hβ1
  have hu' := huniq u hu hfix
  have hlimx := (hlim _ (const_mem_bX 0)).tendsto_at x
  simp only [affineOp_iterate_zero hL hr] at hlimx
  rw [← hu'] at hlimx
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlimx) ▸ hsum.hasSum

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A firm problem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.1.1 (pp. 2–10).

Profits are `π(X_t)` for a Markov state `(X_t)` with stochastic kernel `P` on a measurable space
`X`, `π ∈ bX`, and `β ∈ [0, 1)`.

* **Valuation** (§1.1.1.1): `v = π + βPv` (1.2) has a unique solution in `bX`, given by the
  Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π` (1.3) (Exercise 1.1.1, in its functional form).
* **Control** (§1.1.1.2): the manager may sell the firm for `s`. A policy is a measurable
  `σ : X → {0, 1}` (here `Bool`, `true` meaning sell), with policy operator
  `T_σ v = σs + (1 − σ)(π + βPv)` (1.5), a `β`-contraction on `bX` with fixed point `v_σ`.
* **Theorem 1.1.1** (p. 6): `v* = sup_σ v_σ` is the unique solution in `bX` of the Bellman
  equation `v = s ∨ (π + βPv)` (1.6), an optimal policy exists, and a policy is optimal iff it
  is `v*`-greedy (1.7); Exercises 1.1.2 and 1.1.3; the Bellman operator (1.9) is a
  `β`-contraction and `Tᵏv → v*` (§1.1.1.3); Remark 1.1.2 (sell at ties).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- The firm problem of §1.1.1. -/
structure FirmProblem (X : Type*) [MeasurableSpace X] where
  /-- the stochastic kernel of the state -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the profit function `π` -/
  profit : X → ℝ
  profit_mem : profit ∈ bX X
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the sale price -/
  s : ℝ

/-- Policies (§1.1.1.2): measurable maps `X → {0, 1}`, with `true` meaning sell. -/
def FirmPolicy (X : Type*) [MeasurableSpace X] : Type _ := {σ : X → Bool // Measurable σ}

namespace FirmProblem

variable (F : FirmProblem X)

/-! ### Valuation -/

theorem isMarkovLike_P : IsMarkovLike (markovOp F.P) := by
  have := F.isMarkov
  exact isMarkovLike_markovOp F.P

/-- The valuation operator `v ↦ π + βPv` of (1.2). -/
noncomputable def valOp : (X → ℝ) → X → ℝ := affineOp F.profit F.β (markovOp F.P)

theorem valOp_mapsTo : MapsTo F.valOp (bX X) (bX X) :=
  affineOp_mapsTo F.isMarkovLike_P F.profit_mem F.β_nonneg

theorem valOp_contraction : IsSupContraction (bX X) F.valOp F.β :=
  affineOp_contraction F.isMarkovLike_P F.β_nonneg

/-- (1.2): `v = π + βPv` has a unique solution in `bX`, the limit of iterates from any `v ∈ bX`. -/
theorem valuation_globallyStable :
    ∃ u ∈ bX X, F.valOp u = u ∧ (∀ w ∈ bX X, F.valOp w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.valOp^[n] v) u atTop :=
  affineOp_globallyStable F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one

/-- The value of the firm, the solution of (1.2). -/
noncomputable def value : X → ℝ := F.valuation_globallyStable.choose

theorem value_mem : F.value ∈ bX X := F.valuation_globallyStable.choose_spec.1

/-- (1.2) and **Exercise 1.1.1** (p. 4): `v = π + βPv`. -/
theorem value_eq (x : X) : F.value x = F.profit x + F.β * markovOp F.P F.value x :=
  (congrFun F.valuation_globallyStable.choose_spec.2.1 x).symm

/-- (1.3) (p. 4): the value of the firm is the Neumann series `v = ∑ₜ βᵗPᵗπ = (I − βP)⁻¹π`. -/
theorem value_hasSum (x : X) :
    HasSum (fun t => F.β ^ t * (markovOp F.P)^[t] F.profit x) (F.value x) :=
  affineOp_hasSum F.isMarkovLike_P F.profit_mem F.β_nonneg F.β_lt_one F.value_mem
    F.valuation_globallyStable.choose_spec.2.1 x

/-! ### Control -/

/-- The policy operator (1.5): `T_σ v = s` where `σ` sells and `π + βPv` where it continues. -/
noncomputable def Tσ (σ : X → Bool) (v : X → ℝ) : X → ℝ :=
  fun x => if σ x then F.s else F.profit x + F.β * markovOp F.P v x

/-- (1.5) in the book's form `T_σ v = σs + (1 − σ)(π + βPv)`, with `σ ∈ {0, 1}`. -/
theorem Tσ_eq (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x = (if σ x then 1 else 0) * F.s +
      (1 - if σ x then 1 else 0) * (F.profit x + F.β * markovOp F.P v x) := by
  unfold Tσ
  cases σ x <;> simp

theorem Tσ_mapsTo {σ : X → Bool} (hσ : Measurable σ) : MapsTo (F.Tσ σ) (bX X) (bX X) := by
  intro v hv
  obtain ⟨hm, M, hM⟩ := F.valOp_mapsTo hv
  refine ⟨Measurable.ite (hσ (measurableSet_singleton true)) measurable_const hm,
    max |F.s| M, fun x => ?_⟩
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact (hM x).trans (le_max_right _ _)

theorem Tσ_mono (σ : X → Bool) {v w : X → ℝ} (hv : v ∈ bX X) (hw : w ∈ bX X) (h : v ≤ w) :
    F.Tσ σ v ≤ F.Tσ σ w := by
  have := F.isMarkov
  intro x
  simp only [Tσ]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (markovOp_mono F.P hv hw h x)
      F.β_nonneg)

/-- §1.1.1.2: each `T_σ` is a `β`-contraction on `bX`. -/
theorem Tσ_contraction (σ : X → Bool) : IsSupContraction (bX X) (F.Tσ σ) F.β := by
  intro v hv w hw c h x
  simp only [Tσ]
  split_ifs
  · simpa using mul_nonneg F.β_nonneg ((abs_nonneg _).trans (h x))
  · exact F.valOp_contraction v hv w hw c h x

/-- The policy that sells exactly when `s ≥ π + βPv` is measurable (§2.3.1). -/
theorem measurable_sellPolicy {v : X → ℝ} (hv : v ∈ bX X) :
    Measurable fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s) := by
  refine measurable_to_bool ?_
  have hm := (F.valOp_mapsTo hv).1
  have : (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) ⁻¹' {true} =
      {x | F.valOp v x ≤ F.s} := by
    ext x; simp [valOp, affineOp]
  rw [this]
  exact measurableSet_le hm measurable_const

/-- `T_σ v ≤ s ∨ (π + βPv)`, with equality for the selling policy above. -/
theorem Tσ_le_max (σ : X → Bool) (v : X → ℝ) (x : X) :
    F.Tσ σ v x ≤ max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Tσ_sellPolicy (v : X → ℝ) (x : X) :
    F.Tσ (fun x => decide (F.profit x + F.β * markovOp F.P v x ≤ F.s)) v x =
      max F.s (F.profit x + F.β * markovOp F.P v x) := by
  simp only [Tσ]
  by_cases h : F.profit x + F.β * markovOp F.P v x ≤ F.s
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

/-- The firm problem as a contracting dynamic program on `bX`. -/
noncomputable def toDP : ContractingDP X (FirmPolicy X) where
  V := bX X
  T σ := F.Tσ σ.1
  β := F.β
  β_nonneg := F.β_nonneg
  β_lt_one := F.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd := fun _ h => h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := F.Tσ_mapsTo σ.2
  mono σ _ hv _ hw h := F.Tσ_mono σ.1 hv hw h
  contraction σ := F.Tσ_contraction σ.1
  exists_greedy v hv := ⟨⟨_, F.measurable_sellPolicy hv⟩, fun τ x => by
    change F.Tσ τ.1 v x ≤ F.Tσ _ v x
    rw [F.Tσ_sellPolicy]
    exact F.Tσ_le_max τ.1 v x⟩

/-- The firm's Bellman operator is `Tv = s ∨ (π + βPv)` (1.9). -/
theorem bellman_eq {v : X → ℝ} (hv : v ∈ bX X) (x : X) :
    F.toDP.bellman v x = max F.s (F.profit x + F.β * markovOp F.P v x) := by
  refine le_antisymm (F.Tσ_le_max _ v x) ?_
  rw [← F.Tσ_sellPolicy]
  exact F.toDP.T_le_bellman ⟨_, F.measurable_sellPolicy hv⟩ hv x

/-- `σ` is `v`-greedy in the sense of (1.8): at each `x`, `σ(x)` maximizes
`as + (1 − a)(π(x) + β(Pv)(x))` over `a ∈ {0, 1}`. -/
def IsGreedy (v : X → ℝ) (σ : X → Bool) : Prop :=
  ∀ x, ∀ a : Bool, (if a then F.s else F.profit x + F.β * markovOp F.P v x) ≤ F.Tσ σ v x

/-- (1.8) agrees with greedy policies of the dynamic program (§2.3.1). -/
theorem isGreedy_iff (v : X → ℝ) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.toDP.IsGreedy v σ := by
  constructor
  · intro h τ x
    change F.Tσ τ.1 v x ≤ F.Tσ σ.1 v x
    have := h x (τ.1 x)
    simp only [Tσ] at this ⊢
    exact this
  · intro h x a
    have := h ⟨fun _ => a, measurable_const⟩ x
    change F.Tσ (fun _ => a) v x ≤ F.Tσ σ.1 v x at this
    simpa only [Tσ] using this

/-- **Exercise 1.1.3** (p. 8): `σ` is `v`-greedy iff `Tv = T_σ v`. -/
theorem isGreedy_iff_bellman {v : X → ℝ} (hv : v ∈ bX X) (σ : FirmPolicy X) :
    F.IsGreedy v σ.1 ↔ F.Tσ σ.1 v = F.toDP.bellman v :=
  (F.isGreedy_iff v σ).trans (F.toDP.isGreedy_iff hv σ)

/-- **Exercise 1.1.2** (p. 6): if `|π| ≤ M` and `|s| ≤ M`, every `σ`-value function satisfies
`|v_σ| ≤ M/(1 − β)`; in particular `v* = sup_σ v_σ` is a well-defined real function. -/
theorem abs_vσ_le {M : ℝ} (hπ : ∀ x, |F.profit x| ≤ M) (hs : |F.s| ≤ M) (σ : FirmPolicy X)
    (x : X) : |F.toDP.vσ σ x| ≤ M / (1 - F.β) := by
  have := F.isMarkov
  have h1β : 0 < 1 - F.β := sub_pos.2 F.β_lt_one
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hs
  set K := M / (1 - F.β)
  have hK : M + F.β * K = K := by
    have : K * (1 - F.β) = M := div_mul_cancel₀ M h1β.ne'
    linear_combination -this
  have hKM : M ≤ K := by
    rw [le_div_iff₀ h1β]; nlinarith [F.β_nonneg]
  have hup : F.toDP.T σ (fun _ => K) ≤ fun _ => K := fun y => by
    change F.Tσ σ.1 _ y ≤ K
    simp only [Tσ, markovOp_const]
    split_ifs
    · exact (le_abs_self _).trans (hs.trans hKM)
    · linarith [(abs_le.1 (hπ y)).2]
  have hdown : (fun _ => -K) ≤ F.toDP.T σ (fun _ => -K) := fun y => by
    change -K ≤ F.Tσ σ.1 _ y
    simp only [Tσ, markovOp_const]
    split_ifs
    · linarith [(abs_le.1 hs).1]
    · linarith [(abs_le.1 (hπ y)).1]
  rw [abs_le]
  exact ⟨F.toDP.le_vσ (const_mem_bX _) hdown x, F.toDP.vσ_le (const_mem_bX _) hup x⟩

/-- **Theorem 1.1.1** (p. 6): the value function `v* = sup_σ v_σ` is the unique `v ∈ bX` solving
the Bellman equation `v = s ∨ (π + βPv)` (1.6); at least one optimal policy exists; a policy is
optimal iff it is `v*`-greedy (1.7); and VFI converges, `Tᵏv → v*` uniformly (§1.1.1.3). -/
theorem theorem_1_1_1 :
    F.toDP.vstar ∈ bX X ∧ (∀ x, F.toDP.vstar x = ⨆ σ, F.toDP.vσ σ x) ∧
      (∀ x, F.toDP.vstar x = max F.s (F.profit x + F.β * markovOp F.P F.toDP.vstar x)) ∧
      (∀ v ∈ bX X, (∀ x, v x = max F.s (F.profit x + F.β * markovOp F.P v x)) →
        v = F.toDP.vstar) ∧
      (∃ σ, F.toDP.IsOptimal σ) ∧ (∀ σ, F.toDP.IsOptimal σ ↔ F.IsGreedy F.toDP.vstar σ.1) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => F.toDP.bellman^[n] v) F.toDP.vstar atTop := by
  obtain ⟨-, hsup, hfix, hopt, hex, hvfi⟩ := F.toDP.optimality
  have hmem : F.toDP.vstar ∈ bX X := F.toDP.vstar_mem
  refine ⟨hmem, hsup, fun x => ?_, fun v hv h => (hfix v hv).1 (funext fun x => ?_), hex,
    fun σ => (hopt σ).trans (F.isGreedy_iff _ σ).symm, hvfi⟩
  · rw [← F.bellman_eq hmem x, F.toDP.bellman_vstar]
  · rw [F.bellman_eq hv x]; exact (h x).symm

/-- **Remark 1.1.2** (p. 7): the policy that sells whenever `s ≥ π + βPv*` is optimal. -/
theorem sellPolicy_optimal :
    F.toDP.IsOptimal ⟨_, F.measurable_sellPolicy F.toDP.vstar_mem⟩ := by
  refine (F.toDP.optimality.2.2.2.1 _).2 ((F.isGreedy_iff _ _).1 fun x a => ?_)
  rw [F.Tσ_sellPolicy]
  cases a
  · exact le_max_right _ _
  · exact le_max_left _ _

end FirmProblem

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite Markov decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.2.1 (pp. 19–26).

A finite MDP has a finite state space `X`, a nonempty finite feasible set `Γ(x)` of actions, a
reward `r`, a discount factor `β ∈ [0, 1)` and transition probabilities `P(x, a, ·)` on the
feasible pairs. The action set need not be finite: only the sets `Γ(x)` are.

* **Exercise 1.2.1**: `T_σ v = r_σ + βP_σ v` (1.18) is a `β`-contraction on `ℝ^X` whose fixed
  point is `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.17); `I − βP_σ` is invertible.
* **Exercise 1.2.2**: with `r̄ ≥ |r|` on `G` and `M = r̄/(1 − β)`, each `T_σ` maps `[−M, M]` into
  itself and `|v_σ| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* The Bellman operator (1.20); **Exercise 1.2.3** (it is a `β`-contraction); `v`-greedy policies
  (1.21) and **Exercise 1.2.4**.
* **Theorem 1.2.1**: `v*` is the unique solution of the Bellman equation (1.19), a policy is
  optimal iff it is `v*`-greedy, and an optimal policy exists.
* **Theorem 1.2.2**: VFI and OPI (for every `m ≥ 1`) converge to `v*` from every starting point,
  and HPI reaches an optimal policy in finitely many steps.
* **Lemma 1.2.3** and **Proposition 1.2.4**: `v*` is the unique solution of the linear program
  (1.23) for any everywhere positive weight `c`.
-/

open Filter Topology Set Function Matrix

namespace SargentStachurski.AbstractDecisionProcesses

/-- A finite MDP `(Γ, r, β, P)` (§1.2.1.1). The kernel is required to be stochastic on the
feasible pairs only. -/
structure FiniteMDP (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', 0 ≤ P x a x'
  P_sum : ∀ x, ∀ a ∈ Γ x, ∑ x', P x a x' = 1

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- The feasible policies `Σ = {σ ∈ A^X : σ(x) ∈ Γ(x)}` (1.15). -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

/-- The value of action `a` at `x` given `v`: `r(x, a) + β ∑_{x'} v(x')P(x, a, x')`. -/
def Q (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ x', v x' * M.P x a x'

/-- The policy operator (1.18): `(T_σ v)(x) = r(x, σ(x)) + β ∑_{x'} v(x')P(x, σ(x), x')`. -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.Q v x (σ x)

omit [Fintype X] in
/-- Every function on a finite set is bounded. -/
theorem isBdd_of_finite [Finite X] (v : X → ℝ) : IsBdd v := by
  have := Fintype.ofFinite X
  exact ⟨∑ x, |v x|, fun x =>
    Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)⟩

/-- `|∑ v P − ∑ w P| ≤ c` when `|v − w| ≤ c`, for a feasible pair. -/
theorem abs_sum_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) :
    |∑ x', v x' * M.P x a x' - ∑ x', w x' * M.P x a x'| ≤ c := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ x', (v x' * M.P x a x' - w x' * M.P x a x')|
      ≤ ∑ x', |v x' * M.P x a x' - w x' * M.P x a x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x', c * M.P x a x' := Finset.sum_le_sum fun y _ => by
        rw [← sub_mul, abs_mul, abs_of_nonneg (M.P_nonneg x a ha y)]
        exact mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)
    _ = c := by rw [← Finset.mul_sum, M.P_sum x a ha, mul_one]

theorem Q_mono {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} (h : v ≤ w) : M.Q v x a ≤ M.Q w x a :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a ha y)) M.β_nonneg)

theorem abs_Q_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {c : ℝ}
    (h : ∀ y, |v y - w y| ≤ c) : |M.Q v x a - M.Q w x a| ≤ M.β * c := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le ha h) M.β_nonneg

/-- Shifting by a constant: `Q(v − c) = Qv − βc` on feasible pairs. -/
theorem Q_sub_const {x : X} {a : A} (ha : a ∈ M.Γ x) (v : X → ℝ) (c : ℝ) :
    M.Q (fun y => v y - c) x a = M.Q v x a - M.β * c := by
  simp only [Q, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, M.P_sum x a ha]
  ring

/-- A `v`-greedy action exists at every state. -/
theorem exists_greedy (v : X → ℝ) :
    ∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x) := by
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, hmax⟩

/-- The finite MDP as a contracting dynamic program on `ℝ^X`. -/
def toDP : ContractingDP X M.Policy where
  V := univ
  T σ := M.Tσ σ.1
  β := M.β
  β_nonneg := M.β_nonneg
  β_lt_one := M.β_lt_one
  nonempty := ⟨0, trivial⟩
  bdd v _ := isBdd_of_finite v
  closed _ _ _ _ := trivial
  mapsTo _ _ _ := trivial
  mono σ _ _ _ _ h x := M.Q_mono (σ.2 x) h
  contraction σ _ _ _ _ _ h x := M.abs_Q_sub_le (σ.2 x) h
  exists_greedy v _ := by
    obtain ⟨σ, hσ⟩ := M.exists_greedy v
    exact ⟨σ, fun τ x => hσ x _ (τ.2 x)⟩

/-- `σ` is `v`-greedy in the sense of (1.21). -/
def IsGreedy (v : X → ℝ) (σ : M.Policy) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ M.Q v x (σ.1 x)

/-- **Exercise 1.2.4** (p. 22): `σ` is `v`-greedy iff `T_σ v ≥ T_τ v` for all `τ ∈ Σ`. -/
theorem isGreedy_iff (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ ↔ M.toDP.IsGreedy v σ := by
  classical
  constructor
  · exact fun h τ x => h x _ (τ.2 x)
  · intro h x a ha
    let τ : M.Policy := ⟨Function.update σ.1 x a, fun y => by
      rcases eq_or_ne y x with rfl | hy
      · rw [Function.update_self]; exact ha
      · rw [Function.update_of_ne hy]; exact σ.2 y⟩
    have := h τ x
    change M.Q v x (Function.update σ.1 x a x) ≤ M.Q v x (σ.1 x) at this
    rwa [Function.update_self] at this

/-- The Bellman operator (1.20): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
theorem bellman_eq (v : X → ℝ) (x : X) :
    M.toDP.bellman v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) := by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  refine le_antisymm (Finset.le_sup' (M.Q v x) ((M.toDP.greedy v).2 x)) ?_
  refine Finset.sup'_le _ _ fun a ha => (hσ x a ha).trans ?_
  exact M.toDP.T_le_bellman σ (mem_univ v) x

/-- **Exercise 1.2.3** (p. 22): the Bellman operator is a `β`-contraction on `(ℝ^X, d_∞)`. -/
theorem bellman_contraction : IsSupContraction univ M.toDP.bellman M.β :=
  M.toDP.bellman_contraction

/-! ### Lifetime values as matrix expressions -/

/-- `P_σ(x, x') = P(x, σ(x), x')` (1.16). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

/-- `r_σ(x) = r(x, σ(x))` (1.16). -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

theorem Tσ_eq_mulVec (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + (M.β • M.Pσ σ) *ᵥ v := by
  funext x
  simp only [Tσ, Q, rσ, Pσ, Pi.add_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul, mulVec,
    dotProduct, Matrix.of_apply]
  congr 2
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- `|P_σ w| ≤ c` when `|w| ≤ c`. -/
theorem abs_Pσ_mulVec_le (σ : M.Policy) {w : X → ℝ} {c : ℝ} (h : ∀ y, |w y| ≤ c) (x : X) :
    |(M.Pσ σ.1 *ᵥ w) x| ≤ c := by
  have := M.abs_sum_sub_le (σ.2 x) (v := w) (w := 0) (c := c) (by simpa using h)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] at this
  simpa [Pσ, mulVec, dotProduct, mul_comm] using this

/-- **Exercise 1.2.1** (p. 21), (1.17): `I − βP_σ` is invertible and `v_σ = (I − βP_σ)⁻¹r_σ`. -/
theorem vσ_eq_inv [DecidableEq X] (σ : M.Policy) :
    IsUnit (1 - M.β • M.Pσ σ.1) ∧ M.toDP.vσ σ = (1 - M.β • M.Pσ σ.1)⁻¹ *ᵥ M.rσ σ.1 := by
  set B := M.β • M.Pσ σ.1
  -- `z = Bz` forces `z = 0`
  have hzero : ∀ z : X → ℝ, z = B *ᵥ z → z = 0 := by
    intro z hz
    have hc : IsSupContraction (univ : Set (X → ℝ)) (fun v => B *ᵥ v) M.β := by
      intro v _ w _ c h x
      have e : (B *ᵥ v) x - (B *ᵥ w) x = M.β * (M.Pσ σ.1 *ᵥ (v - w)) x := by
        simp only [B, smul_mulVec, mulVec_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      change |(B *ᵥ v) x - (B *ᵥ w) x| ≤ M.β * c
      rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
      exact mul_le_mul_of_nonneg_left
        (M.abs_Pσ_mulVec_le σ (fun y => by simpa using h y) x) M.β_nonneg
    exact hc.eq_of_isFixedPt M.β_nonneg M.β_lt_one (mem_univ z) (mem_univ 0)
      (isBdd_of_finite z) (isBdd_of_finite 0) hz.symm (by simp)
  have hunit : IsUnit (1 - B) := by
    rw [← mulVec_injective_iff_isUnit]
    intro u w huw
    have : u - w = B *ᵥ (u - w) := by
      have h2 : (1 - B) *ᵥ (u - w) = 0 := by rw [mulVec_sub, huw, sub_self]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h2
      exact h2
    exact sub_eq_zero.1 (hzero _ this)
  refine ⟨hunit, ?_⟩
  have hfix : M.toDP.vσ σ = M.rσ σ.1 + B *ᵥ M.toDP.vσ σ := by
    conv_lhs => rw [← M.toDP.T_vσ σ]
    exact M.Tσ_eq_mulVec σ.1 _
  have h1 : (1 - B) *ᵥ M.toDP.vσ σ = M.rσ σ.1 := by
    rw [sub_mulVec, one_mulVec]
    nth_rewrite 1 [hfix]
    abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]

/-- (1.17) (p. 21): `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum [DecidableEq X] (σ : M.Policy) (x : X) :
    HasSum (fun t => ((M.β • M.Pσ σ.1) ^ t *ᵥ M.rσ σ.1) x) (M.toDP.vσ σ x) := by
  set B := M.β • M.Pσ σ.1
  obtain ⟨R, hR⟩ := isBdd_of_finite (M.rσ σ.1)
  have hbound : ∀ t y, |(B ^ t *ᵥ M.rσ σ.1) y| ≤ M.β ^ t * R := by
    intro t
    induction t with
    | zero => simpa using hR
    | succ t ih =>
      intro y
      rw [pow_succ', ← mulVec_mulVec, smul_mulVec, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg M.β_nonneg, pow_succ, mul_comm (M.β ^ t) M.β, mul_assoc]
      exact mul_le_mul_of_nonneg_left (M.abs_Pσ_mulVec_le σ ih y) M.β_nonneg
  have hsum : Summable fun t => (B ^ t *ᵥ M.rσ σ.1) x :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right R)
      fun t => by rw [Real.norm_eq_abs]; exact hbound t x
  -- the partial sums are the iterates of `T_σ` from `0`
  have hiter : ∀ n, (M.toDP.T σ)^[n] 0 = ∑ t ∈ Finset.range n, B ^ t *ᵥ M.rσ σ.1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', ih]
      change M.Tσ σ.1 _ = _
      rw [M.Tσ_eq_mulVec, mulVec_sum, Finset.sum_range_succ', pow_zero, one_mulVec, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by rw [mulVec_mulVec, pow_succ']
  have hlim := (M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x
  simp only [hiter, Finset.sum_apply] at hlim
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim) ▸ hsum.hasSum

/-- **Exercise 1.2.2** (p. 21): if `|r| ≤ r̄` on `G` and `M = r̄/(1 − β)`, then (i) every `T_σ`
maps `[−M, M]` into itself and (ii) `|v_σ| ≤ M`. -/
theorem abs_vσ_le {rbar : ℝ} (hr : ∀ x, ∀ a ∈ M.Γ x, |M.r x a| ≤ rbar) :
    (∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β)) ∧
      ∀ σ x, |M.toDP.vσ σ x| ≤ rbar / (1 - M.β) := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  have hK : rbar + M.β * (rbar / (1 - M.β)) = rbar / (1 - M.β) := by
    have : rbar / (1 - M.β) * (1 - M.β) = rbar := div_mul_cancel₀ _ h1β.ne'
    linear_combination -this
  have hself : ∀ σ : M.Policy, ∀ v : X → ℝ, (∀ x, |v x| ≤ rbar / (1 - M.β)) →
      ∀ x, |M.Tσ σ.1 v x| ≤ rbar / (1 - M.β) := by
    intro σ v hv x
    have hP := M.abs_Pσ_mulVec_le σ hv x
    simp only [Pσ, mulVec, dotProduct, Matrix.of_apply] at hP
    simp only [Tσ, Q]
    calc |M.r x (σ.1 x) + M.β * ∑ x', v x' * M.P x (σ.1 x) x'|
        ≤ |M.r x (σ.1 x)| + M.β * |∑ x', v x' * M.P x (σ.1 x) x'| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg M.β_nonneg]
      _ ≤ rbar + M.β * (rbar / (1 - M.β)) := by
          refine add_le_add (hr x _ (σ.2 x)) (mul_le_mul_of_nonneg_left ?_ M.β_nonneg)
          simpa only [mul_comm] using hP
      _ = rbar / (1 - M.β) := hK
  refine ⟨hself, fun σ x => ?_⟩
  -- the iterates from `0` stay in `[−M, M]`, and so does their limit `v_σ`
  have hrbar : 0 ≤ rbar / (1 - M.β) := by
    have hr0 : 0 ≤ rbar := (abs_nonneg _).trans (hr x _ (σ.2 x))
    positivity
  have hit : ∀ n y, |(M.toDP.T σ)^[n] 0 y| ≤ rbar / (1 - M.β) := by
    intro n
    induction n with
    | zero => intro y; simpa using hrbar
    | succ n ih => intro y; rw [iterate_succ_apply']; exact hself σ _ ih y
  exact le_of_tendsto' (((M.toDP.tendsto_vσ σ (mem_univ 0)).tendsto_at x).abs) fun n => hit n x

/-! ### Optimality and algorithms -/

/-- `Σ` is finite: each `Γ(x)` is. -/
theorem finite_policy : Finite M.Policy := by
  classical
  refine Finite.of_injective (fun σ : M.Policy => fun x => (⟨σ.1 x, σ.2 x⟩ : M.Γ x)) ?_
  intro σ τ h
  apply Subtype.ext
  funext x
  have := congrFun h x
  simpa using congrArg Subtype.val this

/-- **Theorem 1.2.1** (p. 22): the value function `v*` is the unique solution in `ℝ^X` of the
Bellman equation (1.19), a policy is optimal iff it is `v*`-greedy (1.21), and an optimal policy
exists. -/
theorem theorem_1_2_1 :
    (∀ x, M.toDP.vstar x = ⨆ σ, M.toDP.vσ σ x) ∧
      (∀ x, M.toDP.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q M.toDP.vstar x)) ∧
      (∀ v : X → ℝ, (∀ x, v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x)) → v = M.toDP.vstar) ∧
      (∀ σ, M.toDP.IsOptimal σ ↔ M.IsGreedy M.toDP.vstar σ) ∧ ∃ σ, M.toDP.IsOptimal σ := by
  obtain ⟨-, hsup, hfix, hopt, hex, -⟩ := M.toDP.optimality
  refine ⟨hsup, fun x => ?_, fun v hv => (hfix v (mem_univ v)).1 (funext fun x => ?_),
    fun σ => (hopt σ).trans (M.isGreedy_iff _ σ).symm, hex⟩
  · rw [← M.bellman_eq, M.toDP.bellman_vstar]
  · rw [M.bellman_eq]; exact (hv x).symm

/-- **Theorem 1.2.2** (p. 24): VFI converges, OPI converges for every `m ≥ 1`, from every
starting point, and HPI reaches an optimal policy in finitely many steps. -/
theorem theorem_1_2_2 :
    (∀ v, TendstoUniformly (fun n => M.toDP.bellman^[n] v) M.toDP.vstar atTop) ∧
      (∀ m, 1 ≤ m → ∀ v, TendstoUniformly (M.toDP.opi m v) M.toDP.vstar atTop) ∧
      ∀ σ₀, ∃ k, ∀ j, k ≤ j → M.toDP.vσ (M.toDP.hpiPolicy σ₀ j) = M.toDP.vstar ∧
        M.toDP.IsOptimal (M.toDP.hpiPolicy σ₀ j) := by
  have := M.finite_policy
  refine ⟨fun v => M.toDP.tendsto_bellman_iterate (mem_univ v), fun m hm v => ?_,
    M.toDP.hpi_terminates⟩
  refine M.toDP.tendsto_opi hm (fun σ v _ c => ?_) (fun _ _ _ => trivial) (mem_univ v)
  funext x
  exact M.Q_sub_const (σ.2 x) v c

/-- **Lemma 1.2.3** (p. 25): if `Tv ≤ v` then `v* ≤ v`. -/
theorem vstar_le {v : X → ℝ} (h : ∀ x, (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) ≤ v x) :
    M.toDP.vstar ≤ v :=
  M.toDP.vstar_le_of_bellman_le (mem_univ v) fun x => (M.bellman_eq v x).trans_le (h x)

/-- The constraint set of the linear program (1.23). -/
def IsLPFeasible (v : X → ℝ) : Prop := ∀ x, ∀ a ∈ M.Γ x, M.Q v x a ≤ v x

/-- **Proposition 1.2.4** (p. 25): for any everywhere positive `c`, the value function `v*` is
the unique solution of the linear program `min ⟨c, v⟩` subject to
`r(x, a) + β ∑ v(x')P(x, a, x') ≤ v(x)` for all `(x, a) ∈ G` (1.23). -/
theorem lp_solution {c : X → ℝ} (hc : ∀ x, 0 < c x) :
    IsLeast {s | ∃ v, M.IsLPFeasible v ∧ s = ∑ x, c x * v x} (∑ x, c x * M.toDP.vstar x) ∧
      ∀ v, M.IsLPFeasible v → ∑ x, c x * v x ≤ ∑ x, c x * M.toDP.vstar x → v = M.toDP.vstar := by
  have hfeas : M.IsLPFeasible M.toDP.vstar := fun x a ha => by
    rw [← congrFun M.toDP.bellman_vstar x, M.bellman_eq]
    exact Finset.le_sup' (M.Q M.toDP.vstar x) ha
  have hge : ∀ v, M.IsLPFeasible v → M.toDP.vstar ≤ v := fun v hv =>
    M.vstar_le fun x => Finset.sup'_le _ _ fun a ha => hv x a ha
  refine ⟨⟨⟨_, hfeas, rfl⟩, ?_⟩, fun v hv hle => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hge v hv x) (hc x).le
  · have hvs := hge v hv
    have hsum : ∑ x, c x * (v x - M.toDP.vstar x) = 0 := by
      have h0 : 0 ≤ ∑ x, c x * (v x - M.toDP.vstar x) :=
        Finset.sum_nonneg fun x _ => mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))
      have : ∑ x, c x * (v x - M.toDP.vstar x) = ∑ x, c x * v x - ∑ x, c x * M.toDP.vstar x := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      mul_nonneg (hc x).le (sub_nonneg.2 (hvs x))).1 hsum
    funext x
    have := hterm x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc x).ne'
    · linarith

end FiniteMDP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.3.1–§1.3.2 (pp. 36–43).

Wealth `w ∈ ℝ₊` evolves as `W_{t+1} = R(W_t − C_t) + Y_{t+1}` with iid income `Y ∼ φ`, and
utility `u` is continuous and bounded (Assumption 1.3.1; the density of `φ` is not needed
here). A feasible policy is a Borel `σ : ℝ₊ → ℝ₊` with `σ(w) ≤ w`.

* **Exercise 1.3.1** and **Lemma 1.3.1**: each policy operator
  `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)` (1.42) maps `bℝ₊` into itself and is
  globally stable, with fixed point `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.44); lifetime
  values are limits of finite-horizon values (1.47).
* (1.48): `|v_σ| ≤ M/(1 − β)` when `|u| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* **Exercise 1.3.2**: the Bellman operator (1.51) is a `β`-contraction.
* §2.3.2: a policy is greedy in the dynamic-program sense iff it is `v`-greedy in the sense
  of (1.49) (a policy can be changed at a single wealth level).
* §1.3.2.2, (i)–(iii): given the existence of greedy policies (Lemma 1.3.2 (i), which rests on
  the density of `φ` and is proved in Chapter 6), an optimal policy exists, `v*` is the unique
  solution of the Bellman equation (1.50) in `bℝ₊`, and a policy is optimal iff it is
  `v*`-greedy.
-/

open MeasureTheory Filter Topology Set Function

open scoped NNReal

namespace SargentStachurski.AbstractDecisionProcesses

/-- The optimal savings problem of §1.3 (with bounded continuous utility). -/
structure OptimalSavings where
  /-- the utility function -/
  u : ℝ≥0 → ℝ
  u_cont : Continuous u
  u_bdd : IsBdd u
  /-- the distribution of labor income -/
  φ : Measure ℝ≥0
  φ_prob : IsProbabilityMeasure φ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the gross return on assets -/
  R : ℝ≥0

/-- Feasible policies (§1.3.1.1): Borel `σ` with `0 ≤ σ(w) ≤ w`. -/
def SavingsPolicy : Type := {σ : ℝ≥0 → ℝ≥0 // Measurable σ ∧ ∀ w, σ w ≤ w}

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The expected continuation value of saving `w − c`: `∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def cont (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := ∫ y, v (S.R * (w - c) + y) ∂S.φ

/-- The Markov operator `(P_σ v)(w) = ∫ v(R(w − σ(w)) + y) φ(dy)` (proof of Lemma 1.3.1). -/
noncomputable def Pσ (σ : ℝ≥0 → ℝ≥0) (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ := S.cont v w (σ w)

/-- `r_σ = u ∘ σ`. -/
def rσ (σ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ := fun w => S.u (σ w)

/-- The policy operator (1.42): `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)`. -/
noncomputable def Tσ (σ : ℝ≥0 → ℝ≥0) : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := affineOp (S.rσ σ) S.β (S.Pσ σ)

theorem integrable_comp {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (a : ℝ≥0) :
    Integrable (fun y => v (a + y)) S.φ := by
  have := S.φ_prob
  obtain ⟨M, hM⟩ := hv.2
  exact Integrable.of_bound (hv.1.comp (measurable_const.add measurable_id)).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

theorem abs_cont_le {v : ℝ≥0 → ℝ} {M : ℝ} (hM : ∀ w, |v w| ≤ M) (w c : ℝ≥0) :
    |S.cont v w c| ≤ M := by
  have := S.φ_prob
  have := norm_integral_le_of_norm_le_const (μ := S.φ) (f := fun y => v (S.R * (w - c) + y))
    (C := M) (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [cont] using this

/-- `P_σ` is a Markov operator on `bℝ₊`. -/
theorem isMarkovLike_Pσ {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : IsMarkovLike (S.Pσ σ) := by
  have := S.φ_prob
  refine ⟨fun v hv => ?_, fun v hv w hw => ?_, fun a v _ => ?_, fun v hv w hw h => ?_,
    fun v hv M hM x => S.abs_cont_le hM _ _⟩
  · obtain ⟨M, hM⟩ := hv.2
    have hf : StronglyMeasurable fun p : ℝ≥0 × ℝ≥0 => v (S.R * (p.1 - σ p.1) + p.2) :=
      (hv.1.comp ((measurable_const.mul (measurable_fst.sub (hσ.comp measurable_fst))).add
        measurable_snd)).stronglyMeasurable
    exact ⟨hf.integral_prod_right'.measurable, M, fun w => S.abs_cont_le hM _ _⟩
  · funext x
    exact integral_add (S.integrable_comp hv _) (S.integrable_comp hw _)
  · funext x
    simp only [Pσ, cont, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul a _
  · intro x
    exact integral_mono (S.integrable_comp hv _) (S.integrable_comp hw _) fun y => h _

theorem rσ_mem {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : S.rσ σ ∈ bX ℝ≥0 := by
  obtain ⟨M, hM⟩ := S.u_bdd
  exact ⟨S.u_cont.measurable.comp hσ, M, fun w => hM _⟩

/-- **Exercise 1.3.1** (p. 38): `T_σ` maps `bℝ₊` into itself. -/
theorem Tσ_mapsTo {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : MapsTo (S.Tσ σ) (bX ℝ≥0) (bX ℝ≥0) :=
  affineOp_mapsTo (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg

/-- **Lemma 1.3.1** (p. 38) and (1.47): each `T_σ` is globally stable on `bℝ₊`: it has a unique
fixed point `v_σ`, and `T_σᵏ v → v_σ` from every terminal value `v ∈ bℝ₊`. -/
theorem Tσ_globallyStable {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) :
    ∃ u ∈ bX ℝ≥0, S.Tσ σ u = u ∧ (∀ w ∈ bX ℝ≥0, S.Tσ σ w = w → w = u) ∧
      ∀ v ∈ bX ℝ≥0, TendstoUniformly (fun n => (S.Tσ σ)^[n] v) u atTop :=
  affineOp_globallyStable (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one

/-- **Lemma 1.3.1**, (1.44): the fixed point of `T_σ` is `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0)
    (hfix : S.Tσ σ v = v) (w : ℝ≥0) :
    HasSum (fun t => S.β ^ t * (S.Pσ σ)^[t] (S.rσ σ) w) (v w) :=
  affineOp_hasSum (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one hv hfix w

/-- (1.48) (p. 40): if `|u| ≤ M` then `|v_σ| ≤ M/(1 − β)`; so `v* = sup_σ v_σ` is well defined. -/
theorem abs_fixedPoint_le {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {M : ℝ}
    (hM : ∀ w, |S.u w| ≤ M) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (hfix : S.Tσ σ v = v)
    (w : ℝ≥0) : |v w| ≤ M / (1 - S.β) := by
  have hL := S.isMarkovLike_Pσ hσ
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  obtain ⟨u, -, -, huniq, hlim⟩ := S.Tσ_globallyStable hσ
  rw [huniq v hv hfix]
  -- the iterates from `0` stay within `M/(1 − β)`
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK : M + S.β * (M / (1 - S.β)) = M / (1 - S.β) := by
    field_simp
    ring
  have hit : ∀ n x, |(S.Tσ σ)^[n] (fun _ => 0) x| ≤ M / (1 - S.β) := by
    intro n
    induction n with
    | zero => intro x; simpa using div_nonneg hM0 h1β.le
    | succ n ih =>
      intro x
      rw [iterate_succ_apply']
      have hmem : (S.Tσ σ)^[n] (fun _ => 0) ∈ bX ℝ≥0 := (S.Tσ_mapsTo hσ).iterate n (const_mem_bX 0)
      calc |S.rσ σ x + S.β * S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x|
          ≤ |S.rσ σ x| + S.β * |S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg S.β_nonneg]
        _ ≤ M + S.β * (M / (1 - S.β)) :=
            add_le_add (hM _) (mul_le_mul_of_nonneg_left (hL.abs_le _ hmem _ ih x) S.β_nonneg)
        _ = M / (1 - S.β) := hK
  exact le_of_tendsto' ((hlim _ (const_mem_bX 0)).tendsto_at w).abs fun n => hit n w

/-! ### The Bellman operator -/

/-- The objective in (1.49)–(1.51): `u(c) + β ∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def objective (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := S.u c + S.β * S.cont v w c

/-- The Bellman operator (1.51): `(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
noncomputable def bellmanOp (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ :=
  ⨆ c : {c : ℝ≥0 // c ≤ w}, S.objective v w c

theorem bddAbove_objective {v : ℝ≥0 → ℝ} (hv : IsBdd v) (w : ℝ≥0) :
    BddAbove (range fun c : {c : ℝ≥0 // c ≤ w} => S.objective v w c) := by
  obtain ⟨M, hM⟩ := S.u_bdd
  obtain ⟨N, hN⟩ := hv
  refine ⟨M + S.β * N, ?_⟩
  rintro _ ⟨c, rfl⟩
  refine add_le_add (le_of_abs_le (hM _)) (mul_le_mul_of_nonneg_left ?_ S.β_nonneg)
  exact le_of_abs_le (S.abs_cont_le hN _ _)

/-- **Exercise 1.3.2** (p. 42): the Bellman operator is a `β`-contraction on `bℝ₊`. -/
theorem bellmanOp_contraction : IsSupContraction (bX ℝ≥0) S.bellmanOp S.β := by
  intro v hv v' hv' c h w
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine abs_ciSup_sub_ciSup_le (S.bddAbove_objective hv.2 w) (S.bddAbove_objective hv'.2 w)
    fun d => ?_
  have hvv' : v - v' ∈ bX ℝ≥0 := ⟨hv.1.sub hv'.1, hv.2.sub hv'.2⟩
  have hsub : S.cont v w d - S.cont v' w d = S.cont (v - v') w d := by
    have := S.φ_prob
    simp only [cont, Pi.sub_apply]
    exact (integral_sub (S.integrable_comp hv _) (S.integrable_comp hv' _)).symm
  simp only [objective, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_nonneg,
    hsub]
  exact mul_le_mul_of_nonneg_left (S.abs_cont_le h _ _) S.β_nonneg

/-! ### Greedy policies and optimality -/

/-- `σ` is `v`-greedy (1.49): `σ(w)` maximizes `u(c) + β ∫ v(R(w − c) + y) φ(dy)` over
`0 ≤ c ≤ w`, for every `w`. -/
def IsGreedy (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) : Prop :=
  ∀ w, ∀ c ≤ w, S.objective v w c ≤ S.objective v w (σ.1 w)

/-- The optimal savings problem as a contracting dynamic program, given that greedy policies
exist (Lemma 1.3.2 (i)). -/
noncomputable def toDP (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    ContractingDP ℝ≥0 SavingsPolicy where
  V := bX ℝ≥0
  T σ := S.Tσ σ.1
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd _ h := h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := S.Tσ_mapsTo σ.2.1
  mono σ _ hv _ hw h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg hv hw h
  contraction σ := affineOp_contraction (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg
  exists_greedy v hv := by
    obtain ⟨σ, hσ⟩ := hgreedy v hv
    exact ⟨σ, fun τ w => hσ w _ (τ.2.2 w)⟩

variable {S} (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ)

/-- §2.3.2 (p. 81): `σ` is greedy for the dynamic program (`T_τ v ≤ T_σ v` for all feasible `τ`)
iff it is `v`-greedy in the sense of (1.49). -/
theorem isGreedy_iff (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) :
    S.IsGreedy v σ ↔ (S.toDP hgreedy).IsGreedy v σ := by
  constructor
  · exact fun h τ w => h w _ (τ.2.2 w)
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]; exact hc
        · simp only [hx, ↓reduceIte]; exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v w ≤ S.Tσ σ.1 v w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this

/-- (1.51): the Bellman operator of the dynamic program is
`(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
theorem bellman_eq {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (w : ℝ≥0) :
    (S.toDP hgreedy).bellman v w = S.bellmanOp v w := by
  have hg := (isGreedy_iff hgreedy v _).2 ((S.toDP hgreedy).isGreedy_greedy hv)
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective hv.2 w) ⟨((S.toDP hgreedy).greedy v).1 w,
    ((S.toDP hgreedy).greedy v).2.2 w⟩

/-- **§1.3.2.2** (p. 42), given greedy policies (Lemma 1.3.2 (i)): (i) an optimal policy
exists, (ii) `v*` is the unique solution of the Bellman equation (1.50) in `bℝ₊`, and (iii) a
policy is optimal iff it is `v*`-greedy. -/
theorem dp_results :
    (∃ σ, (S.toDP hgreedy).IsOptimal σ) ∧
      (S.toDP hgreedy).vstar ∈ bX ℝ≥0 ∧
      (∀ w, (S.toDP hgreedy).vstar w = S.bellmanOp (S.toDP hgreedy).vstar w) ∧
      (∀ v ∈ bX ℝ≥0, (∀ w, v w = S.bellmanOp v w) → v = (S.toDP hgreedy).vstar) ∧
      ∀ σ, (S.toDP hgreedy).IsOptimal σ ↔ S.IsGreedy (S.toDP hgreedy).vstar σ := by
  obtain ⟨-, -, hfix, hopt, hex, -⟩ := (S.toDP hgreedy).optimality
  have hmem := (S.toDP hgreedy).vstar_mem
  refine ⟨hex, hmem, fun w => ?_, fun v hv h => (hfix v hv).1 (funext fun w => ?_),
    fun σ => (hopt σ).trans (isGreedy_iff hgreedy _ σ).symm⟩
  · rw [← bellman_eq hgreedy hmem, (S.toDP hgreedy).bellman_vstar]
  · rw [bellman_eq hgreedy hv]; exact (h w).symm

end OptimalSavings

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order stability, order completeness and order continuity

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Appendix A: §A.1.2.10 (order
stability, Lemma A.1.5) and §A.5.1 (chain and Dedekind completeness, Knaster–Tarski, order
continuity, Tarski–Kantorovich), and Lemma A.5.19. These are the order-theoretic inputs of
Chapter 2.

* `S` is *order stable* if it has a unique fixed point `v̄`, and `v ≼ Sv ⟹ v ≼ v̄` and
  `Sv ≼ v ⟹ v̄ ≼ v`; *strongly* order stable if moreover `Sⁿv ↑ v̄` and `Sⁿv ↓ v̄`.
  **Lemma A.1.5**: both notions are self-dual.
* A poset is *chain complete* if every chain (the empty one included) has a supremum and an
  infimum. **Theorem A.5.2** (Knaster–Tarski) and **Lemma A.5.3**, proved by Zorn's lemma: an
  order preserving self-map of a chain complete poset has a fixed point above any point it maps
  up and below any point it maps down; if the fixed point is unique, the map is order stable.
  **Example A.5.1**: order intervals of `ℝ^X` are chain complete.
* *Countably Dedekind complete* posets; **Example A.5.2** (`ℝ^X`); **Exercise A.5.5** (duality).
* *Order continuous* maps; **Lemma A.5.5** (they are order preserving) and **Theorem A.5.6**
  (Tarski–Kantorovich).
* **Lemma A.5.19**: on a space with a closed partial order, an order preserving globally stable
  map is strongly order stable.
-/

open Set Function Filter Topology

namespace SargentStachurski.AbstractDecisionProcesses

variable {V : Type*} [PartialOrder V]

/-! ### Order stability -/

/-- `S` is order stable on `V` (§A.1.2.10). -/
def OrderStable (S : V → V) : Prop :=
  ∃ u, S u = u ∧ (∀ w, S w = w → w = u) ∧ (∀ v, v ≤ S v → v ≤ u) ∧ ∀ v, S v ≤ v → u ≤ v

/-- `vₙ ↑ v`: `(vₙ)` is increasing with supremum `v`. -/
def IncreasesTo (f : ℕ → V) (v : V) : Prop := Monotone f ∧ IsLUB (range f) v

/-- `vₙ ↓ v`: `(vₙ)` is decreasing with infimum `v`. -/
def DecreasesTo (f : ℕ → V) (v : V) : Prop := Antitone f ∧ IsGLB (range f) v

/-- `S` is strongly order stable on `V` (§A.1.2.10): order stable with `Sⁿv ↑ v̄` when `v ≼ Sv`
and `Sⁿv ↓ v̄` when `Sv ≼ v`. -/
def StronglyOrderStable (S : V → V) : Prop :=
  ∃ u, S u = u ∧ (∀ w, S w = w → w = u) ∧ (∀ v, v ≤ S v → IncreasesTo (fun n => S^[n] v) u) ∧
    ∀ v, S v ≤ v → DecreasesTo (fun n => S^[n] v) u

/-- Upward and downward stability around a fixed point force it to be the only one. -/
theorem orderStable_of_up_down {S : V → V} {u : V} (hu : S u = u)
    (hup : ∀ v, v ≤ S v → v ≤ u) (hdown : ∀ v, S v ≤ v → u ≤ v) : OrderStable S :=
  ⟨u, hu, fun w hw => le_antisymm (hup w hw.ge) (hdown w hw.le), hup, hdown⟩

/-- Strong order stability implies order stability. -/
theorem StronglyOrderStable.orderStable {S : V → V} (h : StronglyOrderStable S) :
    OrderStable S := by
  obtain ⟨u, hu, -, hup, hdown⟩ := h
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · simpa using (hup v hv).2.1 ⟨0, rfl⟩
  · simpa using (hdown v hv).2.1 ⟨0, rfl⟩

/-- The map `S` read on the order dual. -/
def dualMap (S : V → V) : Vᵒᵈ → Vᵒᵈ := OrderDual.toDual ∘ S ∘ OrderDual.ofDual

/-- **Lemma A.1.5** (p. 337): `S` is order stable on `V` iff it is order stable on `V^∂`. -/
theorem orderStable_dual_iff (S : V → V) : OrderStable (dualMap S) ↔ OrderStable S := by
  constructor
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.ofDual u) (congrArg OrderDual.ofDual hu)
      (fun v hv => hdown (OrderDual.toDual v) hv) fun v hv => hup (OrderDual.toDual v) hv
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.toDual u) (congrArg OrderDual.toDual hu)
      (fun v hv => hdown (OrderDual.ofDual v) hv) fun v hv => hup (OrderDual.ofDual v) hv

omit [PartialOrder V] in
theorem dualMap_iterate (S : V → V) (n : ℕ) (v : Vᵒᵈ) :
    (dualMap S)^[n] v = OrderDual.toDual (S^[n] (OrderDual.ofDual v)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, ih]; rfl

/-- **Lemma A.1.5** (p. 337): strong order stability is self-dual too. -/
theorem stronglyOrderStable_dual_iff (S : V → V) :
    StronglyOrderStable (dualMap S) ↔ StronglyOrderStable S := by
  constructor
  · rintro ⟨u, hu, huniq, hup, hdown⟩
    refine ⟨OrderDual.ofDual u, congrArg OrderDual.ofDual hu,
      fun w hw => congrArg OrderDual.ofDual (huniq (OrderDual.toDual w)
        (congrArg OrderDual.toDual hw)), fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨hm, hl⟩ := hdown (OrderDual.toDual v) hv
      simp only [dualMap_iterate] at hm hl
      exact ⟨fun a b hab => hm hab, hl⟩
    · obtain ⟨hm, hl⟩ := hup (OrderDual.toDual v) hv
      simp only [dualMap_iterate] at hm hl
      exact ⟨fun a b hab => hm hab, hl⟩
  · rintro ⟨u, hu, huniq, hup, hdown⟩
    refine ⟨OrderDual.toDual u, congrArg OrderDual.toDual hu,
      fun w hw => congrArg OrderDual.toDual (huniq (OrderDual.ofDual w)
        (congrArg OrderDual.ofDual hw)), fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨hm, hl⟩ := hdown (OrderDual.ofDual v) hv
      simp only [dualMap_iterate]
      exact ⟨fun a b hab => hm hab, hl⟩
    · obtain ⟨hm, hl⟩ := hup (OrderDual.ofDual v) hv
      simp only [dualMap_iterate]
      exact ⟨fun a b hab => hm hab, hl⟩

/-! ### Chain completeness and Knaster–Tarski -/

/-- `V` is chain complete (§A.5.1.1): every chain, including the empty one, has a supremum and
an infimum. -/
def ChainComplete (V : Type*) [PartialOrder V] : Prop :=
  ∀ C : Set V, IsChain (· ≤ ·) C → (∃ s, IsLUB C s) ∧ ∃ i, IsGLB C i

/-- A chain complete poset has a least element. -/
theorem ChainComplete.exists_least (h : ChainComplete V) : ∃ b : V, ∀ v, b ≤ v := by
  obtain ⟨⟨b, hb⟩, -⟩ := h ∅ (Set.pairwise_empty _)
  exact ⟨b, fun v => hb.2 fun _ hx => absurd hx (notMem_empty _)⟩

/-- **Knaster–Tarski** for chain complete posets (Theorem A.5.2), upward form: an order
preserving `S` has a fixed point above every `v` with `v ≼ Sv`. -/
theorem ChainComplete.exists_fixedPt_ge (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    {v : V} (hv : v ≤ S v) : ∃ u, S u = u ∧ v ≤ u := by
  set s := {u | v ≤ u ∧ u ≤ S u}
  obtain ⟨m, hvm, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    obtain ⟨⟨ub, hub⟩, -⟩ := h c hc
    refine ⟨ub, ⟨(hcs hy).1.trans (hub.1 hy), hub.2 fun z hz => ?_⟩, fun z hz => hub.1 hz⟩
    exact (hcs hz).2.trans (hS (hub.1 hz))) v ⟨le_rfl, hv⟩
  have hm : m ∈ s := hmax.prop
  have hSm : S m ∈ s := ⟨hvm.trans hm.2, hS hm.2⟩
  exact ⟨m, le_antisymm (hmax.2 hSm hm.2) hm.2, hvm⟩

/-- **Knaster–Tarski** for chain complete posets, downward form: an order preserving `S` has a
fixed point below every `v` with `Sv ≼ v`. -/
theorem ChainComplete.exists_fixedPt_le (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    {v : V} (hv : S v ≤ v) : ∃ u, S u = u ∧ u ≤ v := by
  obtain ⟨b, hb⟩ := h.exists_least
  set s := {u | u ≤ S u ∧ u ≤ v}
  obtain ⟨m, -, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    obtain ⟨⟨ub, hub⟩, -⟩ := h c hc
    refine ⟨ub, ⟨hub.2 fun z hz => (hcs hz).1.trans (hS (hub.1 hz)),
      hub.2 fun z hz => (hcs hz).2⟩, fun z hz => hub.1 hz⟩) b ⟨hb _, hb _⟩
  have hm : m ∈ s := hmax.prop
  have hSm : S m ∈ s := ⟨hS hm.1, (hS hm.2).trans hv⟩
  exact ⟨m, le_antisymm (hmax.2 hSm hm.1) hm.1, hm.2⟩

/-- **Theorem A.5.2** (Knaster–Tarski, p. 369): an order preserving self-map of a chain complete
poset has a fixed point. -/
theorem ChainComplete.exists_fixedPt (h : ChainComplete V) {S : V → V} (hS : Monotone S) :
    ∃ u, S u = u := by
  obtain ⟨b, hb⟩ := h.exists_least
  obtain ⟨u, hu, -⟩ := h.exists_fixedPt_ge hS (hb (S b))
  exact ⟨u, hu⟩

/-- **Lemma A.5.3** (p. 370): an order preserving self-map of a chain complete poset with at most
one fixed point is order stable. -/
theorem ChainComplete.orderStable (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    (huniq : ∀ u w, S u = u → S w = w → u = w) : OrderStable S := by
  obtain ⟨u, hu⟩ := h.exists_fixedPt hS
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · obtain ⟨w, hw, hvw⟩ := h.exists_fixedPt_ge hS hv
    exact huniq w u hw hu ▸ hvw
  · obtain ⟨w, hw, hwv⟩ := h.exists_fixedPt_le hS hv
    exact huniq w u hw hu ▸ hwv

/-- **Example A.5.1** and **Lemma A.5.4** (p. 369): an order interval `[a, b]` of a conditionally
complete lattice, such as `ℝ^X`, is chain complete. -/
theorem chainComplete_Icc {L : Type*} [ConditionallyCompleteLattice L] {a b : L} (hab : a ≤ b) :
    ChainComplete (Icc a b) := by
  have : Fact (a ≤ b) := ⟨hab⟩
  intro C _
  exact ⟨⟨sSup C, isLUB_sSup C⟩, ⟨sInf C, isGLB_sInf C⟩⟩

/-! ### Dedekind completeness -/

/-- `V` is countably Dedekind complete (§A.5.1.2): every nonempty countable set that is bounded
above has a supremum, and every one bounded below has an infimum. -/
def CountablyDedekindComplete (V : Type*) [PartialOrder V] : Prop :=
  ∀ A : Set V, A.Nonempty → A.Countable →
    (BddAbove A → ∃ s, IsLUB A s) ∧ (BddBelow A → ∃ i, IsGLB A i)

/-- **Example A.5.2** (p. 370): `ℝ^X`, and more generally any conditionally complete lattice, is
(countably) Dedekind complete. -/
theorem countablyDedekindComplete_of_conditionallyCompleteLattice {L : Type*}
    [ConditionallyCompleteLattice L] : CountablyDedekindComplete L :=
  fun A hne _ => ⟨fun hb => ⟨sSup A, isLUB_csSup hne hb⟩, fun hb => ⟨sInf A, isGLB_csInf hne hb⟩⟩

/-- **Exercise A.5.5** (p. 371): the dual of a countably Dedekind complete poset is countably
Dedekind complete. -/
theorem CountablyDedekindComplete.dual (h : CountablyDedekindComplete V) :
    CountablyDedekindComplete Vᵒᵈ := fun A hne hc => by
  obtain ⟨h1, h2⟩ := h (OrderDual.ofDual '' A) (hne.image _) (hc.image _)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨i, hi⟩ := h2 ⟨OrderDual.ofDual b, by rintro _ ⟨a, ha, rfl⟩; exact hb ha⟩
    exact ⟨OrderDual.toDual i, fun a ha => hi.1 ⟨a, ha, rfl⟩,
      fun w hw => hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨t, ht⟩ := h1 ⟨OrderDual.ofDual b, by rintro _ ⟨a, ha, rfl⟩; exact hb ha⟩
    exact ⟨OrderDual.toDual t, fun a ha => ht.1 ⟨a, ha, rfl⟩,
      fun w hw => ht.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩

/-! ### Order continuity -/

/-- `S` is order continuous (§A.5.1.3): `vₙ ↑ v` implies that `Svₙ` has supremum `Sv`. -/
def OrderContinuous {W : Type*} [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Monotone f → IsLUB (range f) v → IsLUB (range (S ∘ f)) (S v)

/-- **Lemma A.5.5** (p. 372): order continuous maps are order preserving. -/
theorem OrderContinuous.monotone {W : Type*} [PartialOrder W] {S : V → W}
    (h : OrderContinuous S) : Monotone S := by
  intro v v' hvv'
  have hf : Monotone fun n : ℕ => if n = 0 then v else v' := by
    intro a b hab
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · simp [ha, hb]
      · simp [ha, hb, hvv']
    · have hb : b ≠ 0 := fun hb => ha (Nat.le_zero.1 (hb ▸ hab))
      simp [ha, hb]
  have hsup : IsLUB (range fun n : ℕ => if n = 0 then v else v') v' := by
    refine ⟨?_, fun w hw => hw ⟨1, by simp⟩⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn, hvv']
    · simp [hn]
  have := (h _ _ hf hsup).1 ⟨0, rfl⟩
  simpa using this

/-- A monotone sequence and its shift have the same suprema. -/
theorem isLUB_range_succ_iff {f : ℕ → V} (hf : Monotone f) (v : V) :
    IsLUB (range fun n => f (n + 1)) v ↔ IsLUB (range f) v := by
  have key : upperBounds (range fun n => f (n + 1)) = upperBounds (range f) := by
    ext w
    simp only [mem_upperBounds, forall_mem_range]
    exact ⟨fun h n => (hf (Nat.le_succ n)).trans (h n), fun h n => h (n + 1)⟩
  rw [IsLUB, IsLUB, key]

/-- **Theorem A.5.6** (Tarski–Kantorovich, p. 372): if `S` is order continuous, `V` is countably
Dedekind complete, and `v_a ≼ v_b` with `v_a ≼ Sv_a` and `Sv_b ≼ v_b`, then `Sⁿv_a ↑ v̄` for
some fixed point `v̄` of `S`. -/
theorem tarski_kantorovich (hV : CountablyDedekindComplete V) {S : V → V}
    (hS : OrderContinuous S) {va vb : V} (hab : va ≤ vb) (ha : va ≤ S va) (hb : S vb ≤ vb) :
    ∃ v, S v = v ∧ IncreasesTo (fun n => S^[n] va) v := by
  have hmono := hS.monotone
  have hinc : Monotone fun n => S^[n] va := monotone_nat_of_le_succ fun n => by
    have := hmono.iterate n ha
    rwa [← iterate_succ_apply] at this
  have hbdd : ∀ n, S^[n] va ≤ vb := by
    intro n
    induction n with
    | zero => exact hab
    | succ n ih => rw [iterate_succ_apply']; exact (hmono ih).trans hb
  obtain ⟨v, hv⟩ := (hV _ (range_nonempty _) (countable_range _)).1
    ⟨vb, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  refine ⟨v, ?_, hinc, hv⟩
  have h1 := hS _ _ hinc hv
  have h2 : IsLUB (range fun n => S^[n + 1] va) v := (isLUB_range_succ_iff hinc v).2 hv
  have h3 : (S ∘ fun n => S^[n] va) = fun n => S^[n + 1] va := by
    funext n; simp only [Function.comp_apply, iterate_succ_apply']
  rw [h3] at h1
  exact h1.unique h2

/-! ### Global stability (`GloballyStable`, §A.2.2.1, is restated in `Basics`) -/

/-- **Lemma A.5.19** (p. 380): on a space whose partial order is closed, an order preserving
globally stable map is strongly order stable. -/
theorem stronglyOrderStable_of_globallyStable {W : Type*} [TopologicalSpace W] [PartialOrder W]
    [OrderClosedTopology W] {S : W → W} (hS : Monotone S) (hg : GloballyStable S) :
    StronglyOrderStable S := by
  obtain ⟨u, hu, huniq, hlim⟩ := hg
  refine ⟨u, hu, huniq, fun v hv => ?_, fun v hv => ?_⟩
  · have hinc : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := hS.iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hinc, isLUB_of_tendsto_atTop hinc (hlim v)⟩
  · have hdec : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := hS.iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hdec, isGLB_of_tendsto_atTop hdec (hlim v)⟩

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Abstract decision processes on posets

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.1 (pp. 59–68).

An **abstract dynamic program** (ADP, Definition 2.1.1) is a partially ordered value space `V`
with a nonempty family of order preserving policy operators `T_σ`, `σ ∈ Σ`. Unlike Volume 1,
the existence of greedy policies is a property (regularity), not part of the definition.

* Greedy policies (Definition 2.1.2), `V_G` (2.2); well-posed, finite, regular, order stable and
  strongly order stable ADPs (§2.1.1.2).
* The Bellman equation (Definition 2.1.3) and the Bellman operator `T = ⋁_σ T_σ`
  (Definition 2.1.4), defined where the supremum exists; **Lemma 2.1.1** (`T` exists and is
  order preserving on `V_G`, and `T_σ v = Tv` iff `σ` is `v`-greedy).
* `V_G`, `V_U`, `V_Σ` (Definition 2.1.5) and **Lemma 2.1.2** (`V_Σ ∩ V_G ⊆ V_U`).
* Optimal policies, the value function `v* = ⋁_σ v_σ` and Bellman's principle of optimality
  (Definition 2.1.6); **Lemma 2.1.3**; the fundamental optimality properties (B1)–(B3)
  (Definition 2.1.7) and **Proposition 2.1.4**; **Exercise 2.1.1**.
* **Theorem 2.1.5** (with downward stability, a fixed point of `T` in `V_G` is equivalent to the
  fundamental optimality properties), **Corollary 2.1.6** and **Theorem 2.1.7** (regular and
  well-posed on a chain complete space).
-/

open Set Function

namespace SargentStachurski.AbstractDecisionProcesses

/-- An abstract dynamic program `(V, 𝕋)` (Definition 2.1.1): order preserving self-maps `T_σ` of a
poset `V`, indexed by a nonempty set of policies `Σ`. -/
structure ADP (V P : Type*) [PartialOrder V] where
  /-- the policy operators -/
  T : P → V → V
  mono : ∀ σ, Monotone (T σ)
  nonempty : Nonempty P

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- `σ` is `v`-greedy (Definition 2.1.2, (2.1)): `T_τ v ≼ T_σ v` for all `τ`. -/
def IsGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T τ v ≤ A.T σ v

/-- `V_G`: the points at which a greedy policy exists (2.2). -/
def VG : Set V := {v | ∃ σ, A.IsGreedy v σ}

/-- Well-posed (§2.1.1.2): every `T_σ` has a unique fixed point. -/
def WellPosed : Prop := ∀ σ, ∃! v, A.T σ v = v

/-- Finite (§2.1.1.2): the family `𝕋` of policy operators is finite. -/
def IsFinite : Prop := (range A.T).Finite

/-- Regular (§2.1.1.2): `V_G = V`. -/
def Regular : Prop := ∀ v, ∃ σ, A.IsGreedy v σ

/-- Order stable (§2.1.1.2): every `T_σ` is order stable. -/
def IsOrderStable : Prop := ∀ σ, OrderStable (A.T σ)

/-- Strongly order stable (§2.1.1.2). -/
def IsStronglyOrderStable : Prop := ∀ σ, StronglyOrderStable (A.T σ)

/-- `w` is `Tv = ⋁_σ T_σ v` (Definition 2.1.4), when the supremum exists. -/
def IsBellmanValue (v w : V) : Prop := IsLUB (range fun σ => A.T σ v) w

/-- `v` satisfies the Bellman equation `v = ⋁_σ T_σ v` (Definition 2.1.3, (2.3)). -/
def SolvesBellman (v : V) : Prop := A.IsBellmanValue v v

theorem IsStronglyOrderStable.isOrderStable {A : ADP V P} (h : A.IsStronglyOrderStable) :
    A.IsOrderStable := fun σ => (h σ).orderStable

/-- Order stability implies well-posedness. -/
theorem IsOrderStable.wellPosed {A : ADP V P} (h : A.IsOrderStable) : A.WellPosed := fun σ => by
  obtain ⟨u, hu, huniq, -⟩ := h σ
  exact ⟨u, hu, huniq⟩

theorem regular_iff : A.Regular ↔ A.VG = univ :=
  ⟨fun h => eq_univ_of_forall h, fun h v => (h ▸ mem_univ v : v ∈ A.VG)⟩

/-! ### The Bellman operator -/

/-- A chosen `v`-greedy policy (the greedy selector of §2.2.1.1); arbitrary off `V_G`. -/
noncomputable def greedy (v : V) : P := @Classical.epsilon P A.nonempty fun σ => A.IsGreedy v σ

theorem isGreedy_greedy {v : V} (hv : v ∈ A.VG) : A.IsGreedy v (A.greedy v) := by
  obtain ⟨σ, hσ⟩ := hv
  exact @Classical.epsilon_spec P (fun σ => A.IsGreedy v σ) ⟨σ, hσ⟩

/-- The Bellman operator `Tv = T_σ v` for the chosen `v`-greedy `σ`; on `V_G` it is
`⋁_σ T_σ v` (Lemma 2.1.1). -/
noncomputable def bellman (v : V) : V := A.T (A.greedy v) v

/-- **Lemma 2.1.1 (ii)(a)** (p. 63): `T_σ v ≼ Tv` on `V_G`. -/
theorem T_le_bellman (σ : P) {v : V} (hv : v ∈ A.VG) : A.T σ v ≤ A.bellman v :=
  A.isGreedy_greedy hv σ

/-- **Lemma 2.1.1 (i)** (p. 63): on `V_G`, `Tv` is the supremum `⋁_σ T_σ v`. -/
theorem isBellmanValue_bellman {v : V} (hv : v ∈ A.VG) : A.IsBellmanValue v (A.bellman v) :=
  ⟨by rintro _ ⟨σ, rfl⟩; exact A.T_le_bellman σ hv, fun _ hw => hw ⟨_, rfl⟩⟩

/-- **Lemma 2.1.1 (ii)(b)** (p. 63): on `V_G`, `T_σ v = Tv` iff `σ` is `v`-greedy. -/
theorem isGreedy_iff {v : V} (hv : v ∈ A.VG) (σ : P) : A.IsGreedy v σ ↔ A.T σ v = A.bellman v :=
  ⟨fun h => le_antisymm (A.T_le_bellman σ hv) (h _), fun h τ => h ▸ A.T_le_bellman τ hv⟩

/-- A supremum attained by a policy operator is a greedy value. -/
theorem isGreedy_of_isBellmanValue {v w : V} {σ : P} (h : A.IsBellmanValue v w)
    (hσ : A.T σ v = w) : A.IsGreedy v σ := fun τ => hσ ▸ h.1 ⟨τ, rfl⟩

/-- On `V_G`, the Bellman equation reads `Tv = v`. -/
theorem solvesBellman_iff {v : V} (hv : v ∈ A.VG) : A.SolvesBellman v ↔ A.bellman v = v :=
  ⟨fun h => (A.isBellmanValue_bellman hv).unique h, fun h => by
    have := A.isBellmanValue_bellman hv
    rwa [h] at this⟩

/-- **Lemma 2.1.1 (i)** (p. 63): `T` is order preserving on `V_G`. -/
theorem bellman_mono {v w : V} (hw : w ∈ A.VG) (h : v ≤ w) :
    A.bellman v ≤ A.bellman w :=
  (A.mono _ h).trans (A.T_le_bellman _ hw)

/-! ### Subsets of the value space -/

/-- `V_U`: the points of `V_G` mapped up by `T` (Definition 2.1.5). -/
def VU : Set V := {v | v ∈ A.VG ∧ v ≤ A.bellman v}

/-- `V_Σ` (written `VSig`): the fixed points of policy operators (Definition 2.1.5). -/
def VSig : Set V := {v | ∃ σ, A.T σ v = v}

/-- **Lemma 2.1.2** (p. 64): `V_Σ ∩ V_G ⊆ V_U`. -/
theorem VSig_inter_VG_subset : A.VSig ∩ A.VG ⊆ A.VU := by
  rintro v ⟨⟨σ, hσ⟩, hv⟩
  exact ⟨hv, hσ.symm.le.trans (A.T_le_bellman σ hv)⟩

/-! ### Optimality -/

variable {A}

/-- The `σ`-value function of a well-posed ADP: the unique fixed point of `T_σ`. -/
noncomputable def vσ (hw : A.WellPosed) (σ : P) : V := (hw σ).exists.choose

theorem T_vσ (hw : A.WellPosed) (σ : P) : A.T σ (A.vσ hw σ) = A.vσ hw σ :=
  (hw σ).exists.choose_spec

theorem eq_vσ (hw : A.WellPosed) {σ : P} {v : V} (h : A.T σ v = v) : v = A.vσ hw σ :=
  (hw σ).unique h (T_vσ hw σ)

theorem VSig_eq_range (hw : A.WellPosed) : A.VSig = range (A.vσ hw) := by
  ext v
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (eq_vσ hw hσ).symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, T_vσ hw σ⟩

variable (A)

/-- `σ` is optimal (§2.1.2.1): `v_σ` is a greatest element of `V_Σ`. -/
def IsOptimal (hw : A.WellPosed) (σ : P) : Prop := IsGreatest A.VSig (A.vσ hw σ)

/-- `v` is the value function `v* = ⋁_σ v_σ` (§2.1.2.1). -/
def IsValueFunction (v : V) : Prop := IsLUB A.VSig v

/-- Bellman's principle of optimality (Definition 2.1.6, (2.5)): the optimal policies are the
`v*`-greedy ones (both sets being empty when `v*` does not exist). -/
def BellmanPrinciple (hw : A.WellPosed) : Prop :=
  ∀ σ, A.IsOptimal hw σ ↔ ∃ v, A.IsValueFunction v ∧ A.IsGreedy v σ

/-- The fundamental optimality properties (Definition 2.1.7): (B1) an optimal policy exists,
(B2) `v*` exists and is the unique solution of the Bellman equation in `V_G`, and (B3) Bellman's
principle of optimality holds. -/
def FundamentalOptimality (hw : A.WellPosed) : Prop :=
  (∃ σ, A.IsOptimal hw σ) ∧
    (∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v ∧
      ∀ w ∈ A.VG, A.SolvesBellman w → w = v) ∧
    A.BellmanPrinciple hw

variable {A}

/-- An optimal policy's value is the value function (p. 64). -/
theorem IsOptimal.isValueFunction {hw : A.WellPosed} {σ : P} (h : A.IsOptimal hw σ) :
    A.IsValueFunction (A.vσ hw σ) := h.isLUB

/-- If `v* = v_σ`, then `σ` is optimal (p. 64). -/
theorem isOptimal_of_isValueFunction {hw : A.WellPosed} {σ : P}
    (h : A.IsValueFunction (A.vσ hw σ)) : A.IsOptimal hw σ :=
  ⟨⟨σ, T_vσ hw σ⟩, h.1⟩

theorem isOptimal_iff {hw : A.WellPosed} {σ : P} {v : V} (hv : A.IsValueFunction v) :
    A.IsOptimal hw σ ↔ A.vσ hw σ = v :=
  ⟨fun h => h.isValueFunction.unique hv, fun h => isOptimal_of_isValueFunction (h ▸ hv)⟩

/-- **Lemma 2.1.3 (i)** (p. 65): if `v*` exists and satisfies the Bellman equation, Bellman's
principle of optimality holds. -/
theorem bellmanPrinciple_of_solves {hw : A.WellPosed} {v : V} (hv : A.IsValueFunction v)
    (hb : A.SolvesBellman v) : A.BellmanPrinciple hw := by
  intro σ
  constructor
  · intro ho
    refine ⟨v, hv, A.isGreedy_of_isBellmanValue hb ?_⟩
    rw [← (isOptimal_iff hv).1 ho]
    exact T_vσ hw σ
  · rintro ⟨w, hw', hg⟩
    have hwv : w = v := hw'.unique hv
    rw [hwv] at hg
    -- `T_σ v* = v*`, so `v_σ = v*`
    have : A.T σ v = v := le_antisymm (hb.1 ⟨σ, rfl⟩) (hb.2 (by rintro _ ⟨τ, rfl⟩; exact hg τ))
    exact (isOptimal_iff hv).2 (eq_vσ hw this).symm

/-- **Lemma 2.1.3 (ii)** (p. 65): `v*` exists in `V_G` and satisfies the Bellman equation iff an
optimal policy exists and Bellman's principle of optimality holds. -/
theorem exists_solves_iff (hw : A.WellPosed) :
    (∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v) ↔
      (∃ σ, A.IsOptimal hw σ) ∧ A.BellmanPrinciple hw := by
  constructor
  · rintro ⟨v, hv, hvG, hb⟩
    have hT := (A.solvesBellman_iff hvG).1 hb
    have hg := A.isGreedy_greedy hvG
    have hσ : A.T (A.greedy v) v = v := hT
    exact ⟨⟨_, (isOptimal_iff hv).2 (eq_vσ hw hσ).symm⟩, bellmanPrinciple_of_solves hv hb⟩
  · rintro ⟨⟨σ, ho⟩, hbp⟩
    obtain ⟨v, hv, hg⟩ := (hbp σ).1 ho
    have hvσ := (isOptimal_iff hv).1 ho
    refine ⟨v, hv, ⟨σ, hg⟩, ?_⟩
    have hTv : A.T σ v = v := hvσ ▸ T_vσ hw σ
    exact ⟨by rintro _ ⟨τ, rfl⟩; exact (hg τ).trans hTv.le,
      fun _ hu => hTv.symm.le.trans (hu ⟨σ, rfl⟩)⟩

/-- **Proposition 2.1.4** (p. 66): the fundamental optimality properties hold iff `v*` exists and
is the unique solution of the Bellman equation in `V_G`. -/
theorem fundamentalOptimality_iff (hw : A.WellPosed) :
    A.FundamentalOptimality hw ↔ ∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v ∧
      ∀ w ∈ A.VG, A.SolvesBellman w → w = v := by
  constructor
  · exact fun h => h.2.1
  · intro h
    obtain ⟨v, hv, hvG, hb, huniq⟩ := h
    obtain ⟨hex, hbp⟩ := (exists_solves_iff hw).1 ⟨v, hv, hvG, hb⟩
    exact ⟨hex, ⟨v, hv, hvG, hb, huniq⟩, hbp⟩

/-- **Exercise 2.1.1** (p. 66): if `v*` exists and is the unique fixed point of `T` in `V`, then
a policy is optimal iff `Tv_σ = v_σ`. (Regularity, assumed in the book so that `T` is defined
everywhere, is not needed when `Tv = v` is read as the Bellman equation (2.3).) -/
theorem isOptimal_iff_solvesBellman (hw : A.WellPosed) {v : V} (hv : A.IsValueFunction v)
    (huniq : ∀ w, A.SolvesBellman w ↔ w = v) (σ : P) :
    A.IsOptimal hw σ ↔ A.SolvesBellman (A.vσ hw σ) := by
  rw [isOptimal_iff hv, huniq]

/-- **Theorem 2.1.5** (p. 66): if `A` is well-posed and `T_σ v ≼ v ⟹ v_σ ≼ v`, then `T` has a
fixed point in `V_G` iff the fundamental optimality properties hold. -/
theorem fundamentalOptimality_iff_exists_fixed (hw : A.WellPosed)
    (hdown : ∀ σ v, A.T σ v ≤ v → A.vσ hw σ ≤ v) :
    (∃ v ∈ A.VG, A.SolvesBellman v) ↔ A.FundamentalOptimality hw := by
  constructor
  · rintro ⟨v, hvG, hb⟩
    -- a fixed point of `T` in `V_G` is a greatest element of `V_Σ`
    have key : ∀ u ∈ A.VG, A.SolvesBellman u → IsGreatest A.VSig u ∧ u ∈ A.VSig := by
      intro u huG hub
      have hT := (A.solvesBellman_iff huG).1 hub
      have hσ : A.T (A.greedy u) u = u := hT
      have hu : u = A.vσ hw (A.greedy u) := eq_vσ hw hσ
      refine ⟨⟨⟨_, hσ⟩, ?_⟩, ⟨_, hσ⟩⟩
      rintro _ ⟨τ, hτ⟩
      rw [eq_vσ hw hτ]
      exact hdown τ u (hub.1 ⟨τ, rfl⟩)
    obtain ⟨hgv, -⟩ := key v hvG hb
    refine (fundamentalOptimality_iff hw).2 ⟨v, hgv.isLUB, hvG, hb, fun w hwG hwb => ?_⟩
    exact (key w hwG hwb).1.unique hgv
  · rintro ⟨-, ⟨v, -, hvG, hb, -⟩, -⟩
    exact ⟨v, hvG, hb⟩

/-- **Corollary 2.1.6** (p. 67): if `A` is order stable and `T` has a fixed point in `V_G`, the
fundamental optimality properties hold. -/
theorem IsOrderStable.fundamentalOptimality (h : A.IsOrderStable) {v : V} (hvG : v ∈ A.VG)
    (hb : A.SolvesBellman v) : A.FundamentalOptimality h.wellPosed := by
  refine (fundamentalOptimality_iff_exists_fixed h.wellPosed fun σ w hw' => ?_).1 ⟨v, hvG, hb⟩
  obtain ⟨u, hu, -, -, hdown⟩ := h σ
  rw [← eq_vσ h.wellPosed hu]
  exact hdown w hw'

/-- In a chain complete space, a well-posed ADP is order stable (Lemma A.5.3). -/
theorem WellPosed.isOrderStable (hw : A.WellPosed) (hV : ChainComplete V) : A.IsOrderStable :=
  fun σ => hV.orderStable (A.mono σ) fun _ _ hu hw' => (hw σ).unique hu hw'

/-- **Theorem 2.1.7** (p. 67): a regular, well-posed ADP on a chain complete space satisfies the
fundamental optimality properties. -/
theorem fundamentalOptimality_of_chainComplete (hw : A.WellPosed) (hr : A.Regular)
    (hV : ChainComplete V) : A.FundamentalOptimality hw := by
  have hos := hw.isOrderStable hV
  have hmono : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
  obtain ⟨v, hv⟩ := hV.exists_fixedPt hmono
  exact hos.fundamentalOptimality (hr v) ((A.solvesBellman_iff (hr v)).2 hv)

end ADP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Algorithms and convergence

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.2.1–§2.2.2 (pp. 68–74).

Value function iteration iterates the Bellman operator `T`; Howard policy iteration iterates the
Howard operator `Hv = v_σ` and optimistic policy iteration the operator `Wv = T_σ^m v`, where `σ`
is the `v`-greedy policy chosen by a greedy selector (Definition 2.2.1). As in the book, every
result below holds for every greedy selector `g`.

* **Lemma 2.2.1** (L1)–(L3), **Lemma 2.2.2** and Remark 2.2.1.
* Convergence of VFI, OPI and HPI (Definition 2.2.2); **Exercise 2.2.1**; **Lemmas 2.2.3–2.2.4**;
  **Corollary 2.2.5** (VFI convergence gives OPI and HPI convergence).
* **Theorem 2.2.6** (finite ADPs: the fundamental optimality properties and finite termination of
  HPI), **Theorem 2.2.7** (chain complete value spaces) and **Theorem 2.2.8** (countably Dedekind
  complete value spaces with order bounded, order continuous ADPs); Exercise 2.2.2.
-/

open Set Function

namespace SargentStachurski.AbstractDecisionProcesses

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- A greedy selector: a choice of `v`-greedy policy at every `v` (§2.2.1.1). -/
def IsSelector (g : V → P) : Prop := ∀ v, A.IsGreedy v (g v)

theorem Regular.isSelector_greedy (hr : A.Regular) : A.IsSelector A.greedy := fun v =>
  A.isGreedy_greedy (hr v)

variable (A) in
/-- The Howard policy operator `Hv = v_σ` for the selected `v`-greedy `σ` (Definition 2.2.1). -/
noncomputable def howard (hw : A.WellPosed) (g : V → P) (v : V) : V := A.vσ hw (g v)

variable (A) in
/-- The optimistic policy operator `Wv = T_σ^m v` for the selected `v`-greedy `σ` (2.6). -/
def opt (m : ℕ) (g : V → P) (v : V) : V := (A.T (g v))^[m] v

/-- With a greedy selector, `T_{g(v)} v = Tv`. -/
theorem IsSelector.T_eq {g : V → P} (hg : A.IsSelector g) (hr : A.Regular) (v : V) :
    A.T (g v) v = A.bellman v :=
  (A.isGreedy_iff (hr v) (g v)).1 (hg v)

theorem mem_VU_iff (hr : A.Regular) {v : V} : v ∈ A.VU ↔ v ≤ A.bellman v :=
  ⟨fun h => h.2, fun h => ⟨hr v, h⟩⟩

/-- **Lemma 2.2.1 (L1)** (p. 69): a fixed point of `H` is a fixed point of `T`. -/
theorem bellman_eq_of_howard_eq (hw : A.WellPosed) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {v : V} (h : A.howard hw g v = v) : A.bellman v = v := by
  rw [← hg.T_eq hr]
  have : A.T (g v) (A.vσ hw (g v)) = A.vσ hw (g v) := T_vσ hw _
  rw [show A.vσ hw (g v) = v from h] at this
  exact this

/-- The iterates `T_σᵏ v` increase when `v ≼ T_σ v`. -/
theorem iterate_mono_of_le {σ : P} {v : V} (hv : v ≤ A.T σ v) :
    Monotone fun k => (A.T σ)^[k] v :=
  monotone_nat_of_le_succ fun k => by
    have := (A.mono σ).iterate k hv
    rwa [← iterate_succ_apply] at this

/-- **Lemma 2.2.1 (L3)** (p. 69): for `v ∈ V_U` and `m ≥ 1`, `Tv ≼ Wv ≼ Tᵐv`. -/
theorem bellman_le_opt (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m)
    {v : V} (hv : v ∈ A.VU) : A.bellman v ≤ A.opt m g v ∧ A.opt m g v ≤ A.bellman^[m] v := by
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine ⟨?_, ?_⟩
  · rw [← hT]
    simpa [opt] using A.iterate_mono_of_le hle hm
  · -- `T_σ ≼ T` and both are order preserving
    have hTmono : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
    have : ∀ k u, (A.T (g v))^[k] u ≤ A.bellman^[k] u := by
      intro k
      induction k with
      | zero => intro u; exact le_rfl
      | succ k ih =>
        intro u
        rw [iterate_succ_apply', iterate_succ_apply']
        exact (A.T_le_bellman _ (hr _)).trans (hTmono (ih u))
    exact this m v

/-- (2.9) (p. 70): for `v ∈ V_U` with `σ` its selected greedy policy and `m ≥ 1`,
`v ≼ Tv = T_σ v ≼ T_σ^m v = Wv ≼ v_σ = Hv`, under upward stability of the policy operators. -/
theorem chain_2_9 (hw : A.WellPosed) (hr : A.Regular) (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ)
    {g : V → P} (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m) {v : V} (hv : v ∈ A.VU) :
    v ≤ A.bellman v ∧ A.bellman v ≤ A.opt m g v ∧ A.opt m g v ≤ A.howard hw g v := by
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine ⟨hv.2, (A.bellman_le_opt hr hg hm hv).1, ?_⟩
  -- `T_σᵏ v ≼ T_σᵏ v_σ = v_σ`
  have hvσ := hup _ _ hle
  have : ∀ k, (A.T (g v))^[k] v ≤ A.vσ hw (g v) := by
    intro k
    induction k with
    | zero => exact hvσ
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (A.mono _ ih).trans (T_vσ hw _).le
  exact this m

/-- **Lemma 2.2.1 (L2)** (p. 69): `T`, `W` and `H` map `V_U` into itself. -/
theorem mapsTo_VU (hw : A.WellPosed) (hr : A.Regular) {g : V → P} (hg : A.IsSelector g)
    (m : ℕ) :
    MapsTo A.bellman A.VU A.VU ∧ MapsTo (A.opt m g) A.VU A.VU ∧
      MapsTo (A.howard hw g) A.VU A.VU := by
  refine ⟨fun v hv => (mem_VU_iff hr).2 (A.bellman_mono (hr _) hv.2), fun v hv => ?_,
    fun v _ => A.VSig_inter_VG_subset ⟨⟨g v, T_vσ hw _⟩, hr _⟩⟩
  -- `Wv = T_σ T_σ^{m−1} v ≼ T T_σ^{m−1} T v = T T_σ^m v = T Wv`
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine (mem_VU_iff hr).2 ?_
  calc A.opt m g v = (A.T (g v))^[m] v := rfl
    _ ≤ (A.T (g v))^[m] (A.T (g v) v) := (A.mono _).iterate m hle
    _ = A.T (g v) ((A.T (g v))^[m] v) := by rw [← iterate_succ_apply, iterate_succ_apply']
    _ ≤ A.bellman ((A.T (g v))^[m] v) := A.T_le_bellman _ (hr _)

/-- (2.8) (p. 70): for `u ≼ v` in `V_U`, `Tu ≼ Wv` and `Tu ≼ Hv`. -/
theorem bellman_le_of_le (hw : A.WellPosed) (hr : A.Regular)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) {g : V → P} (hg : A.IsSelector g) {m : ℕ}
    (hm : 1 ≤ m) {u v : V} (hv : v ∈ A.VU) (huv : u ≤ v) :
    A.bellman u ≤ A.opt m g v ∧ A.bellman u ≤ A.howard hw g v := by
  obtain ⟨-, h2, h3⟩ := A.chain_2_9 hw hr hup hg hm hv
  have := A.bellman_mono (hr v) huv
  exact ⟨this.trans h2, this.trans (h2.trans h3)⟩

/-- **Lemma 2.2.2** (p. 70) and Remark 2.2.1: for a regular ADP whose policy operators are
upward stable, `v ∈ V_U` gives `Tⁿv ≼ Wⁿv` and `Tⁿv ≼ Hⁿv`, and `Tⁿv`, `Wⁿv`, `Hⁿv` increase. -/
theorem iterates_of_mem_VU (hw : A.WellPosed) (hr : A.Regular)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) {g : V → P} (hg : A.IsSelector g) {m : ℕ}
    (hm : 1 ≤ m) {v : V} (hv : v ∈ A.VU) :
    (∀ n, A.bellman^[n] v ≤ (A.opt m g)^[n] v ∧ A.bellman^[n] v ≤ (A.howard hw g)^[n] v) ∧
      Monotone (fun n => A.bellman^[n] v) ∧ Monotone (fun n => (A.opt m g)^[n] v) ∧
      Monotone (fun n => (A.howard hw g)^[n] v) := by
  obtain ⟨hT, hW, hH⟩ := A.mapsTo_VU hw hr hg m
  refine ⟨fun n => ?_, ?_, ?_, ?_⟩
  · induction n with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
      exact ⟨(A.bellman_le_of_le hw hr hup hg hm (hW.iterate n hv) ih.1).1,
        (A.bellman_le_of_le hw hr hup hg hm (hH.iterate n hv) ih.2).2⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    exact (hT.iterate n hv).2
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    obtain ⟨h1, h2, -⟩ := A.chain_2_9 hw hr hup hg hm (hW.iterate n hv)
    exact h1.trans h2
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := A.chain_2_9 hw hr hup hg hm (hH.iterate n hv)
    exact h1.trans (h2.trans h3)

/-! ### Convergence -/

variable (A) in
/-- VFI converges (Definition 2.2.2): `Tⁿv ↑ v*` for all `v ∈ V_U`. -/
def VFIConverges (vstar : V) : Prop := ∀ v ∈ A.VU, IncreasesTo (fun n => A.bellman^[n] v) vstar

variable (A) in
/-- OPI converges (Definition 2.2.2): `Wⁿv ↑ v*` for all `v ∈ V_U` and every step size `m`. -/
def OPIConverges (g : V → P) (vstar : V) : Prop :=
  ∀ m, 1 ≤ m → ∀ v ∈ A.VU, IncreasesTo (fun n => (A.opt m g)^[n] v) vstar

variable (A) in
/-- HPI converges (Definition 2.2.2): `Hⁿv ↑ v*` for all `v ∈ V_U`. -/
def HPIConverges (hw : A.WellPosed) (g : V → P) (vstar : V) : Prop :=
  ∀ v ∈ A.VU, IncreasesTo (fun n => (A.howard hw g)^[n] v) vstar

/-- With step `m = 1`, OPI is VFI. -/
theorem opt_one (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) : A.opt 1 g = A.bellman := by
  funext v
  simp only [opt, iterate_one]
  exact hg.T_eq hr v

/-- **Exercise 2.2.1** (p. 71): convergence of OPI implies convergence of VFI. -/
theorem OPIConverges.vfi (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) {vstar : V}
    (h : A.OPIConverges g vstar) : A.VFIConverges vstar := fun v hv => by
  simpa [opt_one hr hg] using h 1 le_rfl v hv

/-- **Lemma 2.2.3** (p. 71): for an order stable ADP, every `v ∈ V_U` lies below `v*`. -/
theorem le_vstar_of_mem_VU (hos : A.IsOrderStable) {vstar : V}
    (hvs : A.IsValueFunction vstar) {v : V} (hv : v ∈ A.VU) : v ≤ vstar := by
  have hle : v ≤ A.T (A.greedy v) v := hv.2
  obtain ⟨u, hu, -, hup, -⟩ := hos (A.greedy v)
  exact (hup v hle).trans (hvs.1 ⟨_, hu⟩)

/-- Upward stability of order stable policy operators, in terms of `v_σ`. -/
theorem IsOrderStable.le_vσ (hos : A.IsOrderStable) (σ : P) (v : V) (h : v ≤ A.T σ v) :
    v ≤ A.vσ hos.wellPosed σ := by
  obtain ⟨u, hu, -, hup, -⟩ := hos σ
  rw [← eq_vσ hos.wellPosed hu]
  exact hup v h

/-- Downward stability of order stable policy operators, in terms of `v_σ`. -/
theorem IsOrderStable.vσ_le (hos : A.IsOrderStable) (σ : P) (v : V) (h : A.T σ v ≤ v) :
    A.vσ hos.wellPosed σ ≤ v := by
  obtain ⟨u, hu, -, -, hdown⟩ := hos σ
  rw [← eq_vσ hos.wellPosed hu]
  exact hdown v h

/-- **Lemma 2.2.4** (p. 71): `v ≼ Tⁿv ≼ Wⁿv ≼ v*` and `v ≼ Tⁿv ≼ Hⁿv ≼ v*` for `v ∈ V_U`. -/
theorem iterates_le_vstar (hos : A.IsOrderStable) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m) {vstar : V} (hvs : A.IsValueFunction vstar)
    {v : V} (hv : v ∈ A.VU) (n : ℕ) :
    v ≤ A.bellman^[n] v ∧ A.bellman^[n] v ≤ (A.opt m g)^[n] v ∧
      (A.opt m g)^[n] v ≤ vstar ∧ A.bellman^[n] v ≤ (A.howard hos.wellPosed g)^[n] v ∧
      (A.howard hos.wellPosed g)^[n] v ≤ vstar := by
  have hw := hos.wellPosed
  obtain ⟨hcmp, hTm, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hg hm hv
  obtain ⟨-, hW, hH⟩ := A.mapsTo_VU hw hr hg m
  exact ⟨by simpa using hTm (Nat.zero_le n), (hcmp n).1,
    le_vstar_of_mem_VU hos hvs (hW.iterate n hv), (hcmp n).2,
    le_vstar_of_mem_VU hos hvs (hH.iterate n hv)⟩

/-- A sequence squeezed between a sequence increasing to `v*` and `v*` increases to `v*`. -/
theorem increasesTo_of_squeeze {f h : ℕ → V} {vstar : V} (hf : IncreasesTo f vstar)
    (hh : Monotone h) (hfh : ∀ n, f n ≤ h n) (hhv : ∀ n, h n ≤ vstar) : IncreasesTo h vstar :=
  ⟨hh, by rintro _ ⟨n, rfl⟩; exact hhv n, fun u hu =>
    hf.2.2 (by rintro _ ⟨n, rfl⟩; exact (hfh n).trans (hu ⟨n, rfl⟩))⟩

/-- **Corollary 2.2.5** (p. 71): for a regular, order stable ADP, convergence of VFI implies
convergence of OPI and HPI, for every greedy selector. -/
theorem VFIConverges.opi_hpi (hos : A.IsOrderStable) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {vstar : V} (hvs : A.IsValueFunction vstar)
    (h : A.VFIConverges vstar) :
    A.OPIConverges g vstar ∧ A.HPIConverges hos.wellPosed g vstar := by
  refine ⟨fun m hm v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨hcmp, -, hW, -⟩ := A.iterates_of_mem_VU hos.wellPosed hr hos.le_vσ hg hm hv
    exact increasesTo_of_squeeze (h v hv) hW (fun n => (hcmp n).1)
      fun n => (A.iterates_le_vstar hos hr hg hm hvs hv n).2.2.1
  · obtain ⟨hcmp, -, -, hH⟩ := A.iterates_of_mem_VU hos.wellPosed hr hos.le_vσ hg le_rfl hv
    exact increasesTo_of_squeeze (h v hv) hH (fun n => (hcmp n).2)
      fun n => (A.iterates_le_vstar hos hr hg le_rfl hvs hv n).2.2.2.2

/-- `V_U` is nonempty for a regular, well-posed ADP (it contains `V_Σ`). -/
theorem VU_nonempty (hw : A.WellPosed) (hr : A.Regular) : A.VU.Nonempty := by
  obtain ⟨σ⟩ := A.nonempty
  exact ⟨_, A.VSig_inter_VG_subset ⟨⟨σ, T_vσ hw σ⟩, hr _⟩⟩

/-- For a finite ADP, `V_Σ` is finite: `v_σ` depends on `σ` only through `T_σ`. -/
theorem IsFinite.VSig_finite (hfin : A.IsFinite) (hw : A.WellPosed) : A.VSig.Finite := by
  rw [VSig_eq_range hw]
  let φ : (V → V) → V := fun F => A.vσ hw (@Classical.epsilon P A.nonempty fun τ => A.T τ = F)
  refine (hfin.image φ).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨A.T σ, ⟨σ, rfl⟩, ?_⟩
  have hτ : A.T (@Classical.epsilon P A.nonempty fun τ => A.T τ = A.T σ) = A.T σ :=
    @Classical.epsilon_spec P (fun τ => A.T τ = A.T σ) ⟨σ, rfl⟩
  have hfix : A.T (@Classical.epsilon P A.nonempty fun τ => A.T τ = A.T σ) (A.vσ hw σ) =
      A.vσ hw σ := by rw [hτ]; exact T_vσ hw σ
  exact (eq_vσ hw hfix).symm

/-- A monotone sequence in a finite set repeats a value at consecutive indices. -/
theorem exists_succ_eq_of_finite {f : ℕ → V} (hf : Monotone f) {s : Set V} (hs : s.Finite)
    (hfs : ∀ n, f n ∈ s) : ∃ n, f (n + 1) = f n := by
  by_contra hne
  push Not at hne
  have hsm : StrictMono f :=
    strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne (hf (Nat.le_succ n)) (hne n).symm
  exact (infinite_range_of_injective hsm.injective) (hs.subset (by rintro _ ⟨n, rfl⟩; exact hfs n))

/-- **Theorem 2.2.6** (p. 72): a regular, order stable, finite ADP satisfies the fundamental
optimality properties, and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`, for
every greedy selector. -/
theorem fundamentalOptimality_of_finite (hos : A.IsOrderStable) (hr : A.Regular)
    (hfin : A.IsFinite) :
    A.FundamentalOptimality hos.wellPosed ∧ ∀ g, A.IsSelector g → ∀ v ∈ A.VU,
      ∃ n, A.IsValueFunction ((A.howard hos.wellPosed g)^[n] v) := by
  have hw := hos.wellPosed
  -- HPI from `v ∈ V_U` reaches a fixed point of `H`, hence of `T`
  have key : ∀ g, A.IsSelector g → ∀ v ∈ A.VU, ∃ n,
      A.bellman ((A.howard hw g)^[n] v) = (A.howard hw g)^[n] v := by
    intro g hg v hv
    obtain ⟨-, -, -, hH⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hg le_rfl hv
    obtain ⟨n, hn⟩ := exists_succ_eq_of_finite (f := fun n => (A.howard hw g)^[n + 1] v)
      (fun a b hab => hH (Nat.succ_le_succ hab)) (hfin.VSig_finite hw) fun n => by
        rw [iterate_succ_apply']
        exact ⟨g _, T_vσ hw _⟩
    refine ⟨n + 1, A.bellman_eq_of_howard_eq hw hr hg ?_⟩
    rw [← iterate_succ_apply' (A.howard hw g)]
    exact hn
  obtain ⟨v₀, hv₀⟩ := A.VU_nonempty hw hr
  obtain ⟨n, hn⟩ := key _ hr.isSelector_greedy v₀ hv₀
  have hfop := hos.fundamentalOptimality (hr _) ((A.solvesBellman_iff (hr _)).2 hn)
  refine ⟨hfop, fun g hg v hv => ?_⟩
  obtain ⟨-, ⟨u, hu, -, -, huniq⟩, -⟩ := hfop
  obtain ⟨k, hk⟩ := key g hg v hv
  exact ⟨k, huniq _ (hr _) ((A.solvesBellman_iff (hr _)).2 hk) ▸ hu⟩

/-- The value function and an optimal policy under the fundamental optimality properties. -/
theorem FundamentalOptimality.exists_vstar {hw : A.WellPosed} (h : A.FundamentalOptimality hw) :
    ∃ vstar σ, A.IsValueFunction vstar ∧ A.vσ hw σ = vstar ∧ vstar ∈ A.VG ∧
      A.SolvesBellman vstar := by
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, hvG, hb, -⟩, -⟩ := h
  exact ⟨v, σ, hv, (isOptimal_iff hv).1 hσ, hvG, hb⟩

/-- **Theorem 2.2.7** (p. 72): a regular, strongly order stable ADP on a chain complete space
satisfies the fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem convergence_of_chainComplete (hsos : A.IsStronglyOrderStable) (hr : A.Regular)
    (hV : ChainComplete V) :
    A.FundamentalOptimality hsos.isOrderStable.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧
          A.HPIConverges hsos.isOrderStable.wellPosed g vstar := by
  have hos := hsos.isOrderStable
  have hw := hos.wellPosed
  have hfop := fundamentalOptimality_of_chainComplete hw hr hV
  obtain ⟨vstar, σ, hvs, hσ, -, -⟩ := hfop.exists_vstar
  obtain ⟨b, hb⟩ := hV.exists_least
  have hvfi : A.VFIConverges vstar := by
    intro v hv
    obtain ⟨-, hTmono, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hr.isSelector_greedy le_rfl hv
    -- `T_σⁿ ⊥ ↑ v_σ = v*` and `T_σⁿ ⊥ ≼ Tⁿ ⊥ ≼ Tⁿ v`
    obtain ⟨u, hu, -, hup, -⟩ := hsos σ
    have hinc := hup b (hb _)
    rw [eq_vσ hw hu, hσ] at hinc
    have hTmono' : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
    have hcmp : ∀ n, (A.T σ)^[n] b ≤ A.bellman^[n] v := by
      intro n
      induction n with
      | zero => exact hb v
      | succ n ih =>
        rw [iterate_succ_apply', iterate_succ_apply']
        exact (A.T_le_bellman σ (hr _)).trans (hTmono' ih)
    exact increasesTo_of_squeeze hinc hTmono hcmp fun n =>
      (A.iterates_le_vstar hos hr hr.isSelector_greedy le_rfl hvs hv n).2.2.1.trans_eq' (by
        simp [opt_one hr hr.isSelector_greedy])
  exact ⟨hfop, vstar, hvs, hvfi, fun g hg => hvfi.opi_hpi hos hr hg hvs⟩

variable (A) in
/-- Order bounded (§2.2.2.3): some `u` has `T_σ u ≼ u` for all `σ`. -/
def OrderBounded : Prop := ∃ u, ∀ σ, A.T σ u ≤ u

variable (A) in
/-- Order continuous (§2.2.2.3): every `T_σ` is order continuous. -/
def IsOrderContinuous : Prop := ∀ σ, OrderContinuous (A.T σ)

/-- **Exercise 2.2.2** (p. 73): for an order stable ADP with `T_σ u ≼ u` for all `σ`, every
`v ∈ V_U` lies below `u` (regularity, assumed in the book, is not needed). -/
theorem le_of_orderBounded (hos : A.IsOrderStable) {u : V}
    (hu : ∀ σ, A.T σ u ≤ u) {v : V} (hv : v ∈ A.VU) : v ≤ u :=
  (hos.le_vσ _ v hv.2).trans (hos.vσ_le _ u (hu _))

/-- **Theorem 2.2.8** (p. 73): a regular, order stable, order bounded and order continuous ADP on
a countably Dedekind complete space satisfies the fundamental optimality properties, and VFI,
OPI and HPI all converge. -/
theorem convergence_of_dedekind (hos : A.IsOrderStable) (hr : A.Regular)
    (hV : CountablyDedekindComplete V) (hb : A.OrderBounded) (hc : A.IsOrderContinuous) :
    A.FundamentalOptimality hos.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧
          A.HPIConverges hos.wellPosed g vstar := by
  have hw := hos.wellPosed
  obtain ⟨u, hu⟩ := hb
  -- from any `v ∈ V_U`, `Tⁿv` increases to a fixed point of `T`
  have key : ∀ v ∈ A.VU, ∃ vbar, A.bellman vbar = vbar ∧
      IncreasesTo (fun n => A.bellman^[n] v) vbar := by
    intro v hv
    obtain ⟨-, hTmono, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hr.isSelector_greedy le_rfl hv
    obtain ⟨-, hT⟩ := A.mapsTo_VU hw hr hr.isSelector_greedy 1
    have hbdd : ∀ n, A.bellman^[n] v ≤ u := fun n =>
      le_of_orderBounded hos hu ((A.mapsTo_VU hw hr hr.isSelector_greedy 1).1.iterate n hv)
    obtain ⟨vbar, hvbar⟩ := (hV _ (range_nonempty _) (countable_range _)).1
      ⟨u, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
    refine ⟨vbar, le_antisymm ?_ ?_, hTmono, hvbar⟩
    · -- `Tv̄ = T_σ v̄ = ⋁ T_σ vₙ ≼ ⋁ T vₙ = ⋁ vₙ₊₁ = v̄`
      have hσ := (hc (A.greedy vbar)) _ _ hTmono hvbar
      have hshift := (isLUB_range_succ_iff hTmono vbar).2 hvbar
      refine hσ.2 fun _ ⟨n, hn⟩ => hn ▸ ?_
      exact (A.T_le_bellman _ (hr _)).trans (by
        rw [← iterate_succ_apply' A.bellman]
        exact hshift.1 ⟨n, rfl⟩)
    · -- `vₙ₊₁ = T vₙ ≼ T v̄`
      have hshift := (isLUB_range_succ_iff hTmono vbar).2 hvbar
      refine hshift.2 fun _ ⟨n, hn⟩ => hn ▸ ?_
      change A.bellman^[n + 1] v ≤ A.bellman vbar
      rw [iterate_succ_apply']
      exact A.bellman_mono (hr _) (hvbar.1 ⟨n, rfl⟩)
  obtain ⟨v₀, hv₀⟩ := A.VU_nonempty hw hr
  obtain ⟨vbar, hfix, -⟩ := key v₀ hv₀
  have hfop := hos.fundamentalOptimality (hr _) ((A.solvesBellman_iff (hr _)).2 hfix)
  obtain ⟨-, ⟨vstar, hvs, -, -, huniq⟩, -⟩ := id hfop
  have hvfi : A.VFIConverges vstar := by
    intro v hv
    obtain ⟨w, hwfix, hwinc⟩ := key v hv
    rwa [huniq w (hr _) ((A.solvesBellman_iff (hr _)).2 hwfix)] at hwinc
  exact ⟨hfop, vstar, hvs, hvfi, fun g hg => hvfi.opi_hpi hos hr hg hvs⟩

end ADP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.2.3 (pp. 74–78).

Minimization is maximization on the order dual. The min-notions are defined as in §2.2.3.1, and
the dual ADP `(V, 𝕋)^∂ = (V^∂, 𝕋)` (§2.2.3.2) translates each into its max-counterpart.

* **Exercise 2.2.3**: the dual is an ADP, and it is self-dual.
* **Exercise 2.2.4** (i)–(ix): min-greedy, min-regular, min-order bounded, `T▿`, `W▿`, `H▿`,
  `v▿*`, min-optimal and `V▿_G` are the dual's max-notions.
* **Exercise 2.2.5** (Bellman's principle of min-optimality) and **Exercise 2.2.6** (the
  fundamental min-optimality properties and min-convergence of VFI, OPI and HPI).
* **Theorem 2.2.9** (min-version of Theorem 2.1.5) and **Corollary 2.2.10**.
-/

open Set Function

namespace SargentStachurski.AbstractDecisionProcesses

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- The dual ADP `(V^∂, 𝕋)` (§2.2.3.2) and **Exercise 2.2.3**: it is an ADP. -/
def dual : ADP Vᵒᵈ P where
  T σ := dualMap (A.T σ)
  mono σ _ _ h := A.mono σ h
  nonempty := A.nonempty

/-- Every ADP is self-dual (p. 77). -/
theorem dual_dual : A.dual.dual = A := rfl

/-! ### Min-notions (§2.2.3.1) -/

/-- `σ` is `v`-min-greedy: `T_σ v ≼ T_τ v` for all `τ`. -/
def IsMinGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T σ v ≤ A.T τ v

/-- `V▿_G`: the points at which a min-greedy policy exists. -/
def VGmin : Set V := {v | ∃ σ, A.IsMinGreedy v σ}

/-- Min-regular: a `v`-min-greedy policy exists at every `v`. -/
def MinRegular : Prop := ∀ v, ∃ σ, A.IsMinGreedy v σ

/-- Min-order bounded: some `b` has `b ≼ T_σ b` for all `σ`. -/
def MinOrderBounded : Prop := ∃ b, ∀ σ, b ≤ A.T σ b

/-- `w` is `T▿v = ⋀_σ T_σ v`, the Bellman min-operator. -/
def IsMinBellmanValue (v w : V) : Prop := IsGLB (range fun σ => A.T σ v) w

/-- `v` satisfies the Bellman min-equation `T▿v = v`. -/
def SolvesMinBellman (v : V) : Prop := A.IsMinBellmanValue v v

/-- `v` is the min-value function `v▿* = ⋀_σ v_σ`. -/
def IsMinValueFunction (v : V) : Prop := IsGLB A.VSig v

/-- `σ` is min-optimal: `v_σ = v▿*`, i.e. `v_σ` is a least element of `V_Σ`. -/
def IsMinOptimal (hw : A.WellPosed) (σ : P) : Prop := IsLeast A.VSig (A.vσ hw σ)

/-- Bellman's principle of min-optimality. -/
def MinBellmanPrinciple (hw : A.WellPosed) : Prop :=
  ∀ σ, A.IsMinOptimal hw σ ↔ ∃ v, A.IsMinValueFunction v ∧ A.IsMinGreedy v σ

/-- The fundamental min-optimality properties (B1')–(B3'). -/
def MinFundamentalOptimality (hw : A.WellPosed) : Prop :=
  (∃ σ, A.IsMinOptimal hw σ) ∧
    (∃ v, A.IsMinValueFunction v ∧ v ∈ A.VGmin ∧ A.SolvesMinBellman v ∧
      ∀ w ∈ A.VGmin, A.SolvesMinBellman w → w = v) ∧
    A.MinBellmanPrinciple hw

/-! ### Exercise 2.2.4 -/

/-- **Exercise 2.2.4 (i)**: `σ` is `v`-min-greedy for `A` iff it is `v`-max-greedy for `A^∂`. -/
theorem isMinGreedy_iff (v : V) (σ : P) :
    A.IsMinGreedy v σ ↔ A.dual.IsGreedy (OrderDual.toDual v) σ := Iff.rfl

/-- **Exercise 2.2.4 (ii)**: `A` is min-regular iff `A^∂` is max-regular. -/
theorem minRegular_iff : A.MinRegular ↔ A.dual.Regular :=
  ⟨fun h v => h (OrderDual.ofDual v), fun h v => h (OrderDual.toDual v)⟩

/-- **Exercise 2.2.4 (iii)**: `A` is min-order bounded iff `A^∂` is max-order bounded. -/
theorem minOrderBounded_iff : A.MinOrderBounded ↔ A.dual.OrderBounded :=
  ⟨fun ⟨b, hb⟩ => ⟨OrderDual.toDual b, hb⟩, fun ⟨b, hb⟩ => ⟨OrderDual.ofDual b, hb⟩⟩

/-- **Exercise 2.2.4 (iv)**: `T▿v` exists iff `T^∂v` does, and they agree. -/
theorem isMinBellmanValue_iff (v w : V) :
    A.IsMinBellmanValue v w ↔ A.dual.IsBellmanValue (OrderDual.toDual v) (OrderDual.toDual w) :=
  Iff.rfl

/-- **Exercise 2.2.4 (ix)**: `V▿_G = V_G^∂`. -/
theorem VGmin_eq : A.VGmin = OrderDual.ofDual ⁻¹' A.dual.VG := rfl

/-- `V_Σ` is the same for `A` and `A^∂`. -/
theorem dual_VSig : A.dual.VSig = OrderDual.ofDual ⁻¹' A.VSig := rfl

variable {A}

/-- Well-posedness transfers to the dual. -/
theorem WellPosed.dual (hw : A.WellPosed) : A.dual.WellPosed := hw

/-- The `σ`-value functions of `A` and `A^∂` agree. -/
theorem dual_vσ (hw : A.WellPosed) (σ : P) :
    OrderDual.ofDual (A.dual.vσ hw.dual σ) = A.vσ hw σ :=
  eq_vσ hw (T_vσ (A := A.dual) hw.dual σ)

/-- **Exercise 2.2.4 (vii)**: `v▿*` for `A` is `v*^∂` for `A^∂`. -/
theorem isMinValueFunction_iff (v : V) :
    A.IsMinValueFunction v ↔ A.dual.IsValueFunction (OrderDual.toDual v) := Iff.rfl

/-- **Exercise 2.2.4 (viii)**: `σ` is min-optimal for `A` iff max-optimal for `A^∂`. -/
theorem isMinOptimal_iff (hw : A.WellPosed) (σ : P) :
    A.IsMinOptimal hw σ ↔ A.dual.IsOptimal hw.dual σ := by
  unfold IsMinOptimal IsOptimal
  rw [← dual_vσ hw σ]
  rfl

/-- **Exercise 2.2.4 (v)–(vi)**: with a common selector, `W▿ = W^∂` and `H▿ = H^∂`. -/
theorem dual_opt_howard (hw : A.WellPosed) (m : ℕ) (g : V → P) (v : V) :
    A.dual.opt m (g ∘ OrderDual.ofDual) (OrderDual.toDual v) =
        OrderDual.toDual ((A.T (g v))^[m] v) ∧
      OrderDual.ofDual (A.dual.howard hw.dual (g ∘ OrderDual.ofDual) (OrderDual.toDual v)) =
        A.vσ hw (g v) :=
  ⟨dualMap_iterate _ m _, dual_vσ hw (g v)⟩

/-- **Exercise 2.2.5** (p. 77): Bellman's principle of min-optimality holds for `A` iff Bellman's
principle of max-optimality holds for `A^∂`. -/
theorem minBellmanPrinciple_iff (hw : A.WellPosed) :
    A.MinBellmanPrinciple hw ↔ A.dual.BellmanPrinciple hw.dual := by
  refine forall_congr' fun σ => ?_
  rw [isMinOptimal_iff hw σ]
  constructor
  · rintro h
    refine h.trans ⟨fun ⟨v, hv, hg⟩ => ⟨OrderDual.toDual v, hv, hg⟩, fun ⟨v, hv, hg⟩ =>
      ⟨OrderDual.ofDual v, hv, hg⟩⟩
  · rintro h
    refine h.trans ⟨fun ⟨v, hv, hg⟩ => ⟨OrderDual.ofDual v, hv, hg⟩, fun ⟨v, hv, hg⟩ =>
      ⟨OrderDual.toDual v, hv, hg⟩⟩

/-- **Exercise 2.2.6** (p. 78): the fundamental max-optimality properties hold for `A^∂` iff the
fundamental min-optimality properties hold for `A`. -/
theorem minFundamentalOptimality_iff (hw : A.WellPosed) :
    A.MinFundamentalOptimality hw ↔ A.dual.FundamentalOptimality hw.dual := by
  unfold MinFundamentalOptimality FundamentalOptimality
  rw [minBellmanPrinciple_iff hw]
  refine and_congr ⟨fun ⟨σ, h⟩ => ⟨σ, (isMinOptimal_iff hw σ).1 h⟩,
    fun ⟨σ, h⟩ => ⟨σ, (isMinOptimal_iff hw σ).2 h⟩⟩ (and_congr_left' ?_)
  constructor
  · rintro ⟨v, hv, hvG, hb, huniq⟩
    exact ⟨OrderDual.toDual v, hv, hvG, hb, fun w hwG hwb =>
      congrArg OrderDual.toDual (huniq (OrderDual.ofDual w) hwG hwb)⟩
  · rintro ⟨v, hv, hvG, hb, huniq⟩
    exact ⟨OrderDual.ofDual v, hv, hvG, hb, fun w hwG hwb =>
      congrArg OrderDual.ofDual (huniq (OrderDual.toDual w) hwG hwb)⟩

variable (A) in
/-- `V_D`: the points of `V▿_G` mapped down by `T▿`. -/
def VD : Set V := OrderDual.ofDual ⁻¹' A.dual.VU

variable (A) in
/-- min-VFI converges: `T▿ⁿv ↓ v▿*` for all `v ∈ V_D`. -/
def MinVFIConverges (vstar : V) : Prop :=
  ∀ v ∈ A.VD, DecreasesTo (fun n => OrderDual.ofDual (A.dual.bellman^[n] (OrderDual.toDual v)))
    vstar

/-- **Exercise 2.2.6 (i)** (p. 78): max-VFI converges for `A^∂` iff min-VFI converges for `A`. -/
theorem minVFIConverges_iff (vstar : V) :
    A.MinVFIConverges vstar ↔ A.dual.VFIConverges (OrderDual.toDual vstar) := by
  refine forall₂_congr fun v _ => ⟨fun ⟨hm, hl⟩ => ⟨fun a b h => hm h, hl⟩,
    fun ⟨hm, hl⟩ => ⟨fun a b h => hm h, hl⟩⟩

/-- **Theorem 2.2.9** (p. 78): if `A` is well-posed and `v ≼ T_σ v ⟹ v ≼ v_σ`, then `T▿` has a
fixed point in `V▿_G` iff the fundamental min-optimality properties hold. -/
theorem minFundamentalOptimality_iff_exists_fixed (hw : A.WellPosed)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) :
    (∃ v ∈ A.VGmin, A.SolvesMinBellman v) ↔ A.MinFundamentalOptimality hw := by
  rw [minFundamentalOptimality_iff hw,
    ← fundamentalOptimality_iff_exists_fixed hw.dual fun σ v hv => by
      have := hup σ (OrderDual.ofDual v) hv
      rw [← dual_vσ hw σ] at this
      exact this]
  exact ⟨fun ⟨v, hv, hb⟩ => ⟨OrderDual.toDual v, hv, hb⟩,
    fun ⟨v, hv, hb⟩ => ⟨OrderDual.ofDual v, hv, hb⟩⟩

/-- **Corollary 2.2.10** (p. 78): if `A` is order stable and `T▿` has a fixed point in `V▿_G`,
the fundamental min-optimality properties hold. -/
theorem IsOrderStable.minFundamentalOptimality (hos : A.IsOrderStable) {v : V}
    (hvG : v ∈ A.VGmin) (hb : A.SolvesMinBellman v) :
    A.MinFundamentalOptimality hos.wellPosed :=
  (minFundamentalOptimality_iff_exists_fixed hos.wellPosed hos.le_vσ).1 ⟨v, hvG, hb⟩

end ADP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The pointwise order on `bX`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.5.2.4 and Lemma A.1.3 (as used in
§2.3).

`bX` with the pointwise order is a value space for Chapter 2. In it, `vₙ ↑ v` (supremum in `bX`)
is pointwise monotone convergence (Lemma A.1.3), and **Corollary A.5.17** holds: `bX` is
countably Dedekind complete. Markov operators are order continuous (monotone convergence,
Lemma A.5.33).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

/-- A monotone sequence in `bX` converging pointwise to `w ∈ bX` increases to `w` in `bX`. -/
theorem isLUB_of_tendsto_bX {g : ℕ → ↥(bX X)} (hg : Monotone g) {w : ↥(bX X)}
    (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsLUB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Monotone.ge_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact le_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

/-- **Lemma A.1.3** in `bX`: if `vₙ ↑ v` in `bX`, then `vₙ(x) → v(x)` at every `x`. -/
theorem tendsto_of_isLUB_bX {g : ℕ → ↥(bX X)} (hg : Monotone g) {w : ↥(bX X)}
    (hw : IsLUB (range g) w) (x : X) :
    Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x)) := by
  -- the pointwise supremum lies in `bX` and is the supremum in `bX`
  have hbdd : ∀ y, BddAbove (range fun n => (g n : X → ℝ) y) := fun y =>
    ⟨(w : X → ℝ) y, by rintro _ ⟨n, rfl⟩; exact hw.1 ⟨n, rfl⟩ y⟩
  set s : X → ℝ := fun y => ⨆ n, (g n : X → ℝ) y
  have hs : s ∈ bX X := by
    refine ⟨Measurable.iSup fun n => (g n).2.1, ?_⟩
    obtain ⟨M, hM⟩ := (g 0).2.2
    obtain ⟨N, hN⟩ := w.2.2
    refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
    · have := le_ciSup (hbdd y) 0
      linarith [(abs_le.1 (hM y)).1, le_max_left M N]
    · have := ciSup_le fun n => hw.1 ⟨n, rfl⟩ y
      linarith [(abs_le.1 (hN y)).2, le_max_right M N]
  have hup : (⟨s, hs⟩ : ↥(bX X)) ∈ upperBounds (range g) := by
    rintro _ ⟨n, rfl⟩
    exact fun y => le_ciSup (hbdd y) n
  have h1 : w ≤ ⟨s, hs⟩ := hw.2 hup
  have hws : (w : X → ℝ) = s :=
    le_antisymm h1 fun y => ciSup_le fun n => hw.1 ⟨n, rfl⟩ y
  rw [hws]
  exact tendsto_atTop_ciSup (fun a b h => hg h x) (hbdd x)

/-- **Corollary A.5.17** (p. 379): `bX` is countably Dedekind complete. -/
theorem countablyDedekindComplete_bX : CountablyDedekindComplete ↥(bX X) := by
  intro A hne hc
  have : Countable A := hc.to_subtype
  have : Nonempty A := hne.to_subtype
  refine ⟨fun ⟨b, hb⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩
  · have hbdd : ∀ y, BddAbove (range fun f : A => (f.1 : X → ℝ) y) := fun y =>
      ⟨(b : X → ℝ) y, by rintro _ ⟨f, rfl⟩; exact hb f.2 y⟩
    set s : X → ℝ := fun y => ⨆ f : A, (f.1 : X → ℝ) y
    obtain ⟨f₀⟩ := ‹Nonempty A›
    have hs : s ∈ bX X := by
      refine ⟨Measurable.iSup fun f => f.1.2.1, ?_⟩
      obtain ⟨M, hM⟩ := f₀.1.2.2
      obtain ⟨N, hN⟩ := b.2.2
      refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
      · have := le_ciSup (hbdd y) f₀
        linarith [(abs_le.1 (hM y)).1, le_max_left M N]
      · have := ciSup_le fun f : A => hb f.2 y
        linarith [(abs_le.1 (hN y)).2, le_max_right M N]
    refine ⟨⟨s, hs⟩, fun f hf y => le_ciSup (hbdd y) ⟨f, hf⟩, fun u hu y => ?_⟩
    exact ciSup_le fun f => hu f.2 y
  · have hbdd : ∀ y, BddBelow (range fun f : A => (f.1 : X → ℝ) y) := fun y =>
      ⟨(b : X → ℝ) y, by rintro _ ⟨f, rfl⟩; exact hb f.2 y⟩
    set s : X → ℝ := fun y => ⨅ f : A, (f.1 : X → ℝ) y
    obtain ⟨f₀⟩ := ‹Nonempty A›
    have hs : s ∈ bX X := by
      refine ⟨Measurable.iInf fun f => f.1.2.1, ?_⟩
      obtain ⟨M, hM⟩ := f₀.1.2.2
      obtain ⟨N, hN⟩ := b.2.2
      refine ⟨max M N, fun y => abs_le.2 ⟨?_, ?_⟩⟩
      · have := le_ciInf fun f : A => hb f.2 y
        linarith [(abs_le.1 (hN y)).1, le_max_right M N]
      · have := ciInf_le (hbdd y) f₀
        linarith [(abs_le.1 (hM y)).2, le_max_left M N]
    refine ⟨⟨s, hs⟩, fun f hf y => ciInf_le (hbdd y) ⟨f, hf⟩, fun u hu y => ?_⟩
    exact le_ciInf fun f => hu f.2 y

/-- **Lemma A.5.33**-type monotone convergence: if `vₙ ↑ v` pointwise in `bX`, then
`Pvₙ → Pv` pointwise. -/
theorem tendsto_markovOp (P : Kernel X X) [IsMarkovKernel P] {g : ℕ → X → ℝ} {v : X → ℝ}
    (hg : ∀ n, g n ∈ bX X) (hv : v ∈ bX X) (hmono : ∀ y, Monotone fun n => g n y)
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (v y))) (x : X) :
    Tendsto (fun n => markovOp P (g n) x) atTop (𝓝 (markovOp P v x)) :=
  integral_tendsto_of_tendsto_of_monotone (fun n => integrable_of_mem_bX P (hg n) x)
    (integrable_of_mem_bX P hv x) (Filter.Eventually.of_forall hmono)
    (Filter.Eventually.of_forall hlim)

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firm valuation as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.1 (pp. 79–80).

The firm problem of §1.1 is the ADP `(bX, 𝕋_FV)` with the policy operators (2.12) and the
pointwise order.

* **Exercise 2.3.1**: each `T_σ` is an order preserving self-map of `(bX, ≤)`; the ADP is
  well-posed and order stable.
* The ADP's greedy policies are those of (2.13), a greedy policy always exists (regularity), and
  the ADP Bellman operator is `Tv = s ∨ (π + βPv)` (1.9).
* **Exercise 2.3.2** (order continuity) and **Exercise 2.3.3** (order boundedness).
* As the book remarks (p. 80), Theorem 2.2.8 now gives the fundamental optimality properties
  and the convergence of VFI, OPI and HPI for the firm problem.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AbstractDecisionProcesses

variable {X : Type*} [MeasurableSpace X]

namespace FirmProblem

variable (F : FirmProblem X)

/-- The firm ADP `(bX, 𝕋_FV)` (§2.3.1), with policy operators (2.12). -/
noncomputable def adp : ADP ↥(bX X) (FirmPolicy X) where
  T σ v := ⟨F.Tσ σ.1 v.1, F.Tσ_mapsTo σ.2 v.2⟩
  mono σ v w h := F.Tσ_mono σ.1 v.2 w.2 h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- **Exercise 2.3.1** (p. 79): each `T_σ` is an order preserving self-map of `(bX, ≤)`. -/
theorem exercise_2_3_1 (σ : FirmPolicy X) : Monotone (F.adp.T σ) := F.adp.mono σ

/-- The firm ADP is well-posed (§1.1.1.2). -/
theorem adp_wellPosed : F.adp.WellPosed := fun σ => by
  obtain ⟨u, huV, hu, huniq, -⟩ := F.toDP.globallyStable σ
  exact ⟨⟨u, huV⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 w.2 (congrArg Subtype.val hw))⟩

/-- The firm ADP is order stable (Lemma A.5.19). -/
theorem adp_isOrderStable : F.adp.IsOrderStable := fun σ =>
  orderStable_of_up_down (u := ⟨F.toDP.vσ σ, F.toDP.vσ_mem σ⟩) (Subtype.ext (F.toDP.T_vσ σ))
    (fun v hv => F.toDP.le_vσ v.2 hv) fun v hv => F.toDP.vσ_le v.2 hv

/-- §2.3.1 (p. 80): the ADP's `v`-greedy policies are exactly those of (2.13). -/
theorem adp_isGreedy_iff (v : ↥(bX X)) (σ : FirmPolicy X) :
    F.adp.IsGreedy v σ ↔ F.IsGreedy v.1 σ.1 :=
  (F.isGreedy_iff v.1 σ).symm

/-- §2.3.1 (p. 80): the firm ADP is regular. -/
theorem adp_regular : F.adp.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := F.toDP.exists_greedy v.1 v.2
  exact ⟨σ, hσ⟩

/-- §2.3.1 (p. 80): the ADP Bellman operator is `Tv = s ∨ (π + βPv)`, as in (1.9). -/
theorem adp_bellman_apply (v : ↥(bX X)) (x : X) :
    (F.adp.bellman v : X → ℝ) x = max F.s (F.profit x + F.β * markovOp F.P v x) := by
  refine le_antisymm (F.Tσ_le_max _ _ x) ?_
  rw [← F.Tσ_sellPolicy]
  exact F.adp.T_le_bellman ⟨_, F.measurable_sellPolicy v.2⟩ (F.adp_regular v) x

/-- **Exercise 2.3.2** (p. 80): the firm ADP is order continuous. -/
theorem adp_isOrderContinuous : F.adp.IsOrderContinuous := by
  have := F.isMarkov
  intro σ g w hg hw
  have hlim := tendsto_of_isLUB_bX hg hw
  refine isLUB_of_tendsto_bX (fun a b h => F.adp.mono σ (hg h)) fun x => ?_
  change Tendsto (fun n => F.Tσ σ.1 (g n) x) atTop (𝓝 (F.Tσ σ.1 w x))
  simp only [Tσ]
  split_ifs
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds.add ((tendsto_markovOp F.P (fun n => (g n).2) w.2
      (fun y a b h => hg h y) hlim x).const_mul F.β)

/-- **Exercise 2.3.3** (p. 80): the firm ADP is order bounded: with `|π| ≤ M`, the constant
`(|s| + M)/(1 − β)` is mapped down by every `T_σ`. -/
theorem adp_orderBounded : F.adp.OrderBounded := by
  have := F.isMarkov
  obtain ⟨M, hM0, hM⟩ := F.profit_mem.2.nonneg_bound
  have h1β : 0 < 1 - F.β := sub_pos.2 F.β_lt_one
  set K := (|F.s| + M) / (1 - F.β)
  have hK : (1 - F.β) * K = |F.s| + M := mul_div_cancel₀ _ h1β.ne'
  have hsK : F.s ≤ K :=
    (le_abs_self _).trans ((le_add_of_nonneg_right hM0).trans
      (le_div_self (add_nonneg (abs_nonneg _) hM0) h1β (by linarith [F.β_nonneg])))
  refine ⟨⟨fun _ => K, const_mem_bX K⟩, fun σ x => ?_⟩
  change F.Tσ σ.1 (fun _ => K) x ≤ K
  simp only [Tσ, markovOp_const]
  split_ifs
  · exact hsK
  · nlinarith [(abs_le.1 (hM x)).2, abs_nonneg F.s]

/-- §2.3.1 (p. 80), via **Theorem 2.2.8**: the firm ADP satisfies the fundamental optimality
properties, and VFI, OPI and HPI all converge, for every greedy selector. -/
theorem adp_optimality :
    F.adp.FundamentalOptimality F.adp_isOrderStable.wellPosed ∧
      ∃ vstar, F.adp.IsValueFunction vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧
          F.adp.HPIConverges F.adp_isOrderStable.wellPosed g vstar :=
  ADP.convergence_of_dedekind F.adp_isOrderStable F.adp_regular countablyDedekindComplete_bX
    F.adp_orderBounded F.adp_isOrderContinuous

end FirmProblem

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal savings as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.2 (pp. 80–82).

The optimal savings problem of §1.3 is the ADP `(bℝ₊, 𝕋_OS)` with the policy operators (1.42)
and the pointwise order.

* The policy operators are order preserving self-maps of `bℝ₊` (Exercise 1.3.1); the ADP is
  well-posed and order stable (Lemma 1.3.1, Lemma A.5.19).
* The ADP's greedy policies are those of (1.49) ((2.14)–(2.15)); the ADP is regular exactly when
  greedy policies exist (Lemma 1.3.2 (i)), and then its Bellman operator is (1.51).
* **Exercise 2.3.4** (`u ≥ 0` gives `u ∈ V_U`) and **Exercise 2.3.5** (order boundedness and
  order continuity).
* Given Lemma 1.3.2 (i), Theorem 2.2.8 gives the fundamental optimality properties and the
  convergence of VFI, OPI and HPI.
-/

open Set Function Filter Topology MeasureTheory

open scoped NNReal

namespace SargentStachurski.AbstractDecisionProcesses

/-- The policy that consumes all wealth, `σ(w) = w`. -/
def consumeAll : SavingsPolicy := ⟨id, measurable_id, fun _ => le_rfl⟩

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The optimal savings ADP `(bℝ₊, 𝕋_OS)` (§2.3.2). -/
noncomputable def adp : ADP ↥(bX ℝ≥0) SavingsPolicy where
  T σ v := ⟨S.Tσ σ.1 v.1, S.Tσ_mapsTo σ.2.1 v.2⟩
  mono σ v w h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg v.2 w.2 h
  nonempty := ⟨consumeAll⟩

/-- §2.3.2 (p. 81): the optimal savings ADP is well-posed (Lemma 1.3.1). -/
theorem adp_wellPosed : S.adp.WellPosed := fun σ => by
  obtain ⟨u, huV, hu, huniq, -⟩ := S.Tσ_globallyStable σ.2.1
  exact ⟨⟨u, huV⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 w.2 (congrArg Subtype.val hw))⟩

/-- §2.3.2 (p. 81): the optimal savings ADP is order stable (Lemma A.5.19). -/
theorem adp_isOrderStable : S.adp.IsOrderStable := fun σ => by
  obtain ⟨u, huV, hu, -, hlim⟩ := S.Tσ_globallyStable σ.2.1
  have hmono : ∀ v ∈ bX ℝ≥0, ∀ w ∈ bX ℝ≥0, v ≤ w → S.Tσ σ.1 v ≤ S.Tσ σ.1 w :=
    fun _ hv _ hw h => affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg hv hw h
  exact orderStable_of_up_down (u := ⟨u, huV⟩) (Subtype.ext hu)
    (fun v hv => le_of_le_map_of_tendsto (S.Tσ_mapsTo σ.2.1) hmono v.2 (hlim v v.2) hv)
    fun v hv => le_of_map_le_of_tendsto (S.Tσ_mapsTo σ.2.1) hmono v.2 (hlim v v.2) hv

/-- (2.14)–(2.15) (p. 81): `σ` is greedy for the ADP iff it is `v`-greedy in the sense of (1.49).
(A policy can be changed at a single wealth level, so no appeal to Lemma 1.3.2 is needed.) -/
theorem adp_isGreedy_iff (v : ↥(bX ℝ≥0)) (σ : SavingsPolicy) :
    S.adp.IsGreedy v σ ↔ S.IsGreedy v.1 σ := by
  constructor
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]; exact hc
        · simp only [hx, ↓reduceIte]; exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v w ≤ S.Tσ σ.1 v w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this
  · exact fun h τ w => h w _ (τ.2.2 w)

/-- §2.3.2 (p. 81): the ADP is regular iff `v`-greedy policies exist for every `v ∈ bℝ₊`, which
is Lemma 1.3.2 (i). -/
theorem adp_regular_iff : S.adp.Regular ↔ ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ := by
  constructor
  · intro h v hv
    obtain ⟨σ, hσ⟩ := h ⟨v, hv⟩
    exact ⟨σ, (S.adp_isGreedy_iff ⟨v, hv⟩ σ).1 hσ⟩
  · intro h v
    obtain ⟨σ, hσ⟩ := h v.1 v.2
    exact ⟨σ, (S.adp_isGreedy_iff v σ).2 hσ⟩

/-- §2.3.2 (p. 81): for a regular ADP, the Bellman operator is (1.51). -/
theorem adp_bellman_apply (hr : S.adp.Regular) (v : ↥(bX ℝ≥0)) (w : ℝ≥0) :
    (S.adp.bellman v : ℝ≥0 → ℝ) w = S.bellmanOp v w := by
  have hg := (S.adp_isGreedy_iff v _).1 (S.adp.isGreedy_greedy (hr v))
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective v.2.2 w) ⟨(S.adp.greedy v).1 w, (S.adp.greedy v).2.2 w⟩

/-- **Exercise 2.3.4** (p. 82): if `u ≥ 0` then `u ≤ Tu`, i.e. `u ∈ V_U` (the ADP being regular). -/
theorem exercise_2_3_4 (hr : S.adp.Regular) (hu : ∀ c, 0 ≤ S.u c) :
    (⟨S.u, S.u_cont.measurable, S.u_bdd⟩ : ↥(bX ℝ≥0)) ∈ S.adp.VU := by
  have := S.φ_prob
  refine ⟨hr _, ?_⟩
  refine le_trans (fun w => ?_) (S.adp.T_le_bellman consumeAll (hr _))
  change S.u w ≤ S.Tσ id S.u w
  simp only [Tσ, affineOp, rσ, id]
  exact le_add_of_nonneg_right (mul_nonneg S.β_nonneg (integral_nonneg fun y => hu _))

/-- **Exercise 2.3.5** (p. 82), order boundedness: with `|u| ≤ M`, the constant `M/(1 − β)` is
mapped down by every `T_σ`. -/
theorem adp_orderBounded : S.adp.OrderBounded := by
  have := S.φ_prob
  obtain ⟨M, hM0, hM⟩ := S.u_bdd.nonneg_bound
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  set K := M / (1 - S.β)
  have hK : M + S.β * K = K := by
    have : K * (1 - S.β) = M := div_mul_cancel₀ M h1β.ne'
    linarith
  refine ⟨⟨fun _ => K, const_mem_bX K⟩, fun σ w => ?_⟩
  change S.Tσ σ.1 (fun _ => K) w ≤ K
  simp only [Tσ, affineOp, rσ, Pσ, cont, integral_const, probReal_univ, one_smul]
  linarith [(abs_le.1 (hM (σ.1 w))).2]

/-- **Exercise 2.3.5** (p. 82), order continuity, by the monotone convergence theorem. -/
theorem adp_isOrderContinuous : S.adp.IsOrderContinuous := by
  have := S.φ_prob
  intro σ g v hg hv
  have hlim := tendsto_of_isLUB_bX hg hv
  refine isLUB_of_tendsto_bX (fun a b h => S.adp.mono σ (hg h)) fun w => ?_
  change Tendsto (fun n => S.Tσ σ.1 (g n) w) atTop (𝓝 (S.Tσ σ.1 v w))
  simp only [Tσ, affineOp]
  refine tendsto_const_nhds.add (Tendsto.const_mul S.β ?_)
  exact integral_tendsto_of_tendsto_of_monotone (fun n => S.integrable_comp (g n).2 _)
    (S.integrable_comp v.2 _) (Filter.Eventually.of_forall fun y a b h => hg h _)
    (Filter.Eventually.of_forall fun y => hlim _)

/-- §2.3.2 with **Theorem 2.2.8**: given Lemma 1.3.2 (i), the optimal savings ADP satisfies the
fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem adp_optimality (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    S.adp.FundamentalOptimality S.adp_isOrderStable.wellPosed ∧
      ∃ vstar, S.adp.IsValueFunction vstar ∧ S.adp.VFIConverges vstar ∧
        ∀ g, S.adp.IsSelector g → S.adp.OPIConverges g vstar ∧
          S.adp.HPIConverges S.adp_isOrderStable.wellPosed g vstar :=
  ADP.convergence_of_dedekind S.adp_isOrderStable ((S.adp_regular_iff).2 hgreedy)
    countablyDedekindComplete_bX S.adp_orderBounded S.adp_isOrderContinuous

end OptimalSavings

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# MDPs as ADPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.3 (pp. 82–84).

A finite MDP `(Γ, r, β, P)` is the ADP `(ℝ^X, 𝕋_MDP)` with the policy operators (2.16) and the
pointwise order.

* The ADP is well-posed, order continuous and order stable; **Exercise 2.3.6** (order
  bounded), **Exercises 2.3.7–2.3.8** (greedy policies (2.17) and the Bellman operator (2.18)),
  **Exercise 2.3.9** (regular).
* **Proposition 2.3.1**: the fundamental optimality properties hold, VFI, OPI and HPI converge,
  and HPI converges in finitely many steps (Theorems 2.2.6 and 2.2.8).
* **Exercise 2.3.10**: on `V̂ = [−M, M]`, which is chain complete, the ADP is strongly order
  stable, and Theorem 2.2.7 gives the same conclusions.
-/

open Set Function Filter Topology

namespace SargentStachurski.AbstractDecisionProcesses

/-- In a subtype of `ℝ^X`, a monotone sequence converging pointwise to a member increases to it. -/
theorem isLUB_of_tendsto_subtype {X : Type*} {S : Set (X → ℝ)} {g : ℕ → S} (hg : Monotone g)
    {w : S} (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsLUB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Monotone.ge_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact le_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

/-- In a subtype of `ℝ^X`, an antitone sequence converging pointwise to a member decreases to
it. -/
theorem isGLB_of_tendsto_subtype {X : Type*} {S : Set (X → ℝ)} {g : ℕ → S} (hg : Antitone g)
    {w : S} (hlim : ∀ x, Tendsto (fun n => (g n : X → ℝ) x) atTop (𝓝 ((w : X → ℝ) x))) :
    IsGLB (range g) w := by
  refine ⟨?_, fun u hu => ?_⟩
  · rintro _ ⟨n, rfl⟩
    intro x
    exact Antitone.le_of_tendsto (f := fun n => (g n : X → ℝ) x) (fun a b h => hg h x) (hlim x) n
  · intro x
    exact ge_of_tendsto' (hlim x) fun n => hu ⟨n, rfl⟩ x

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- A feasible policy. -/
theorem nonempty_policy : Nonempty M.Policy :=
  ⟨⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩⟩

/-- The ADP `(ℝ^X, 𝕋_MDP)` of a finite MDP (§2.3.3.1), with policy operators (2.16). -/
def adp : ADP (X → ℝ) M.Policy where
  T σ := M.Tσ σ.1
  mono σ _ _ h x := M.Q_mono (σ.2 x) h
  nonempty := M.nonempty_policy

/-- §2.3.3.1 (p. 82): the MDP ADP is well-posed (Exercise 1.2.1). -/
theorem adp_wellPosed : M.adp.WellPosed := fun σ => by
  obtain ⟨u, -, hu, huniq, -⟩ := M.toDP.globallyStable σ
  exact ⟨u, hu, fun w hw => huniq w (mem_univ w) hw⟩

/-- §2.3.3.1 (p. 82): the MDP ADP is order stable (Exercise A.4.4). -/
theorem adp_isOrderStable : M.adp.IsOrderStable := fun σ =>
  orderStable_of_up_down (M.toDP.T_vσ σ) (fun v hv => M.toDP.le_vσ (mem_univ v) hv)
    fun v hv => M.toDP.vσ_le (mem_univ v) hv

/-- §2.3.3.1 (p. 82): the MDP ADP is order continuous. -/
theorem adp_isOrderContinuous : M.adp.IsOrderContinuous := by
  intro σ g w hg hw
  have hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (w x)) := fun x =>
    tendsto_atTop_isLUB (fun a b h => hg h x) (by
      have := (isLUB_pi.1 hw) x
      rwa [← range_comp] at this)
  refine isLUB_of_tendsto_atTop (fun a b h => M.adp.mono σ (hg h)) (tendsto_pi_nhds.2 fun x => ?_)
  change Tendsto (fun n => M.Q (g n) x (σ.1 x)) atTop (𝓝 (M.Q w x (σ.1 x)))
  exact tendsto_const_nhds.add ((tendsto_finsetSum _ fun y _ =>
    (hlim y).mul_const _).const_mul _)

/-- A bound on the rewards over the feasible pairs. -/
noncomputable def rbar : ℝ := ∑ x, ∑ a ∈ M.Γ x, |M.r x a|

theorem abs_r_le_rbar {x : X} {a : A} (ha : a ∈ M.Γ x) : |M.r x a| ≤ M.rbar :=
  (Finset.single_le_sum (f := fun a => |M.r x a|) (fun _ _ => abs_nonneg _) ha).trans
    (Finset.single_le_sum (f := fun x => ∑ a ∈ M.Γ x, |M.r x a|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ x))

/-- **Exercise 2.3.6** (p. 82): the MDP ADP is order bounded. -/
theorem adp_orderBounded : M.adp.OrderBounded := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  set K := M.rbar / (1 - M.β)
  have hK : M.rbar + M.β * K = K := by
    have : K * (1 - M.β) = M.rbar := div_mul_cancel₀ _ h1β.ne'
    linarith
  refine ⟨fun _ => K, fun σ x => ?_⟩
  change M.Q (fun _ => K) x (σ.1 x) ≤ K
  simp only [Q, ← Finset.mul_sum, M.P_sum x _ (σ.2 x), mul_one]
  linarith [(abs_le.1 (M.abs_r_le_rbar (σ.2 x))).2]

/-- **Exercise 2.3.7** (p. 82): a policy satisfying (2.17) is `v`-greedy in the ADP sense. -/
theorem exercise_2_3_7 (v : X → ℝ) (σ : M.Policy) (h : M.IsGreedy v σ) : M.adp.IsGreedy v σ :=
  (M.isGreedy_iff v σ).1 h

/-- **Exercise 2.3.9** (p. 83): the MDP ADP is regular. -/
theorem adp_regular : M.adp.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  exact ⟨σ, M.exercise_2_3_7 v σ hσ⟩

/-- **Exercise 2.3.8** (p. 83): the ADP Bellman operator is (2.18),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
theorem adp_bellman_apply (v : X → ℝ) (x : X) :
    M.adp.bellman v x = (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x) := by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v
  refine le_antisymm (Finset.le_sup' (M.Q v x) ((M.adp.greedy v).2 x)) ?_
  exact Finset.sup'_le _ _ fun a ha =>
    (hσ x a ha).trans (M.adp.T_le_bellman σ (M.adp_regular v) x)

/-- **Proposition 2.3.1** (p. 83): for the MDP ADP (i) the fundamental optimality properties
hold, (ii) VFI, OPI and HPI all converge, and (iii) HPI converges in finitely many steps, for
every greedy selector. -/
theorem proposition_2_3_1 :
    M.adp.FundamentalOptimality M.adp_isOrderStable.wellPosed ∧
      (∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isOrderStable.wellPosed g vstar) ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.adp_isOrderStable.wellPosed g)^[n] v) := by
  have := M.finite_policy
  obtain ⟨h1, h3⟩ := ADP.fundamentalOptimality_of_finite M.adp_isOrderStable M.adp_regular
    (Set.finite_range _)
  obtain ⟨-, h2⟩ := ADP.convergence_of_dedekind M.adp_isOrderStable M.adp_regular
    countablyDedekindComplete_of_conditionallyCompleteLattice M.adp_orderBounded
    M.adp_isOrderContinuous
  exact ⟨h1, h2, h3⟩

/-! ### Exercise 2.3.10: the ADP on `V̂ = [−M, M]` -/

/-- `V̂ = [−M, M]` with `M = r̄/(1 − β)`. -/
def Vhat : Set (X → ℝ) :=
  Icc (fun _ => -(M.rbar / (1 - M.β))) fun _ => M.rbar / (1 - M.β)

theorem mem_Vhat_iff {v : X → ℝ} : v ∈ M.Vhat ↔ ∀ x, |v x| ≤ M.rbar / (1 - M.β) := by
  simp only [Vhat, Set.mem_Icc, Pi.le_def, abs_le]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

/-- Exercise 1.2.2: each `T_σ` maps `V̂` into itself. -/
theorem Tσ_mapsTo_Vhat (σ : M.Policy) : MapsTo (M.Tσ σ.1) M.Vhat M.Vhat := fun v hv =>
  M.mem_Vhat_iff.2 ((M.abs_vσ_le fun _ _ ha => M.abs_r_le_rbar ha).1 σ v (M.mem_Vhat_iff.1 hv))

/-- The MDP ADP restricted to `V̂` (Exercise 2.3.10). -/
def adpHat : ADP ↥M.Vhat M.Policy where
  T σ v := ⟨M.Tσ σ.1 v.1, M.Tσ_mapsTo_Vhat σ v.2⟩
  mono σ _ _ h x := M.Q_mono (σ.2 x) h
  nonempty := M.nonempty_policy

theorem vσ_mem_Vhat (σ : M.Policy) : M.toDP.vσ σ ∈ M.Vhat :=
  M.mem_Vhat_iff.2 ((M.abs_vσ_le fun _ _ ha => M.abs_r_le_rbar ha).2 σ)

/-- **Exercise 2.3.10** (p. 84): on `V̂` the MDP ADP is strongly order stable. -/
theorem adpHat_isStronglyOrderStable : M.adpHat.IsStronglyOrderStable := by
  intro σ
  have hlim : ∀ v : ↥M.Vhat, ∀ x, Tendsto (fun n => ((M.adpHat.T σ)^[n] v : X → ℝ) x) atTop
      (𝓝 (M.toDP.vσ σ x)) := by
    intro v x
    have hiter : ∀ n, ((M.adpHat.T σ)^[n] v : X → ℝ) = (M.Tσ σ.1)^[n] v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl
    simp only [hiter]
    exact (M.toDP.tendsto_vσ σ (mem_univ _)).tendsto_at x
  have hfix : M.adpHat.T σ ⟨_, M.vσ_mem_Vhat σ⟩ = ⟨_, M.vσ_mem_Vhat σ⟩ :=
    Subtype.ext (M.toDP.T_vσ σ)
  refine ⟨⟨_, M.vσ_mem_Vhat σ⟩, hfix, fun w hw => Subtype.ext (M.toDP.eq_vσ (mem_univ _)
    (congrArg Subtype.val hw)), fun v hv => ?_, fun v hv => ?_⟩
  · have hinc : Monotone fun n => (M.adpHat.T σ)^[n] v := monotone_nat_of_le_succ fun n => by
      have := (M.adpHat.mono σ).iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hinc, isLUB_of_tendsto_subtype hinc (hlim v)⟩
  · have hdec : Antitone fun n => (M.adpHat.T σ)^[n] v := antitone_nat_of_succ_le fun n => by
      have := (M.adpHat.mono σ).iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hdec, isGLB_of_tendsto_subtype hdec (hlim v)⟩

/-- On `V̂` the MDP ADP is regular. -/
theorem adpHat_regular : M.adpHat.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_greedy v.1
  exact ⟨σ, fun τ x => hσ x _ (τ.2 x)⟩

/-- **Exercise 2.3.10** (p. 84), via **Theorem 2.2.7**: on the chain complete space `V̂` the MDP
ADP satisfies the fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem exercise_2_3_10 :
    M.adpHat.FundamentalOptimality M.adpHat_isStronglyOrderStable.isOrderStable.wellPosed ∧
      ∃ vstar, M.adpHat.IsValueFunction vstar ∧ M.adpHat.VFIConverges vstar ∧
        ∀ g, M.adpHat.IsSelector g → M.adpHat.OPIConverges g vstar ∧
          M.adpHat.HPIConverges M.adpHat_isStronglyOrderStable.isOrderStable.wellPosed g vstar := by
  have h1β : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  have hK : 0 ≤ M.rbar / (1 - M.β) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) h1β.le
  exact ADP.convergence_of_chainComplete M.adpHat_isStronglyOrderStable M.adpHat_regular
    (chainComplete_Icc fun _ => by linarith)

end FiniteMDP

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control: the Riccati map and the control gain

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.1–§2.3.5.2 and §2.3.5.6
(pp. 89–91, 94).

An LQ problem `(Q, R, A, B)` has `Q` positive semidefinite and `R` positive definite. For
positive semidefinite `P`, set `G(P) = BᵀPB + R` (positive definite), the Riccati map
`R(P) = AᵀPA − AᵀPB G(P)⁻¹ BᵀPA + Q` (2.27), the control gain `F(P) = −G(P)⁻¹BᵀPA` (2.28) and the
policy operators `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)` (2.32).

* **Exercise 2.3.13**: `R(P) = T_{F(P)}(P)`.
* **Exercise 2.3.14**: `R` maps the positive semidefinite cone `𝒫` into itself.
* **Exercise 2.3.16**: each `T_F` is an order preserving self-map of `(𝒫, ≼)` (Loewner order).
* **Lemma 2.3.3**: `F(P)x` is the unique minimizer of `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)`, by
  completing the square: the objective at `F(P)x + d` exceeds its minimum by `dᵀG(P)d`.
* **Exercise 2.3.17**: `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control matrix `G`.
-/

open Matrix

open scoped MatrixOrder

namespace SargentStachurski.AbstractDecisionProcesses

/-- An LQ control problem `(Q, R, A, B)` (§2.3.5.1). -/
structure LQProblem (K U : Type*) [Fintype K] [Fintype U] where
  /-- the state transition matrix -/
  A : Matrix K K ℝ
  /-- the control matrix -/
  B : Matrix K U ℝ
  /-- the state cost -/
  Q : Matrix K K ℝ
  /-- the control cost -/
  R : Matrix U U ℝ
  Q_psd : Q.PosSemidef
  R_pd : R.PosDef

namespace LQProblem

variable {K U : Type*} [Fintype K] [Fintype U] (L : LQProblem K U)

/-- `G(P) = BᵀPB + R`. -/
def gainDen (P : Matrix K K ℝ) : Matrix U U ℝ := L.Bᵀ * P * L.B + L.R

/-- The policy operator (2.32): `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)`. -/
def TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Q + Fᵀ * L.R * F + (L.A + L.B * F)ᵀ * P * (L.A + L.B * F)

/-- The one-period objective `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` of (2.26). -/
def cost (P : Matrix K K ℝ) (x : K → ℝ) (u : U → ℝ) : ℝ :=
  x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) +
    (L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))

/-! ### Positivity and quadratic forms -/

omit [Fintype U] in
theorem posSemidef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
theorem posDef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosDef ↔ Mᵀ = M ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
  rw [posDef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
/-- `Mᵀ P M` is positive semidefinite for positive semidefinite `P`. -/
theorem posSemidef_transpose_mul_mul {n m : Type*} [Fintype n] [Finite m]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (M : Matrix n m ℝ) : (Mᵀ * P * M).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hP.conjTranspose_mul_mul_same M

/-- `G(P) = BᵀPB + R` is positive definite for positive semidefinite `P`. -/
theorem gainDen_posDef {P : Matrix K K ℝ} (hP : P.PosSemidef) : (L.gainDen P).PosDef :=
  Matrix.PosDef.posSemidef_add (posSemidef_transpose_mul_mul hP L.B) L.R_pd

omit [Fintype U] in
/-- For symmetric `S`, `a ⬝ Sb = b ⬝ Sa`. -/
theorem dotProduct_mulVec_comm_of_symm {n : Type*} [Fintype n] {S : Matrix n n ℝ}
    (hS : Sᵀ = S) (a b : n → ℝ) : a ⬝ᵥ (S *ᵥ b) = b ⬝ᵥ (S *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

omit [Fintype U] in
/-- `(Bd) ⬝ w = d ⬝ (Bᵀw)`. -/
theorem mulVec_dotProduct {n m : Type*} [Fintype n] [Fintype m] (B : Matrix n m ℝ) (d : m → ℝ)
    (w : n → ℝ) : (B *ᵥ d) ⬝ᵥ w = d ⬝ᵥ (Bᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

omit [Fintype U] in
/-- `xᵀ(NᵀSN)x = (Nx)ᵀS(Nx)`. -/
theorem dotProduct_transpose_mul_mul {n m : Type*} [Fintype n] [Fintype m] (N : Matrix n m ℝ)
    (S : Matrix n n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((Nᵀ * S * N) *ᵥ x) = (N *ᵥ x) ⬝ᵥ (S *ᵥ (N *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_dotProduct N x]

omit [Fintype U] in
/-- `(a + b)ᵀS(a + b) = aᵀSa + 2bᵀSa + bᵀSb` for symmetric `S`. -/
theorem quad_add {n : Type*} [Fintype n] {S : Matrix n n ℝ} (hS : Sᵀ = S) (a b : n → ℝ) :
    (a + b) ⬝ᵥ (S *ᵥ (a + b)) = a ⬝ᵥ (S *ᵥ a) + 2 * (b ⬝ᵥ (S *ᵥ a)) + b ⬝ᵥ (S *ᵥ b) := by
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_mulVec_comm_of_symm hS a b]
  ring

/-- The quadratic form of `T_F(P)` is the objective at `u = Fx`. -/
theorem dotProduct_TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) (x : K → ℝ) :
    x ⬝ᵥ (L.TF F P *ᵥ x) = L.cost P x (F *ᵥ x) := by
  simp only [TF, cost, add_mulVec, dotProduct_add, dotProduct_transpose_mul_mul, mulVec_mulVec]

/-! ### Exercise 2.3.16 -/

/-- `T_F(P)` is positive semidefinite for positive semidefinite `P`. -/
theorem TF_posSemidef (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P).PosSemidef :=
  (L.Q_psd.add (posSemidef_transpose_mul_mul L.R_pd.posSemidef F)).add
    (posSemidef_transpose_mul_mul hP _)

/-- `T_F(P)` is symmetric for positive semidefinite `P`. -/
theorem TF_transpose (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P)ᵀ = L.TF F P :=
  (posSemidef_iff_real.1 (L.TF_posSemidef F hP)).1

/-- **Exercise 2.3.16** (p. 93): each `T_F` is order preserving for the Loewner order (and maps
`𝒫` into itself, `TF_posSemidef`). -/
theorem TF_mono (F : Matrix U K ℝ) {P P' : Matrix K K ℝ} (h : P ≤ P') : L.TF F P ≤ L.TF F P' := by
  rw [le_iff] at h ⊢
  have : L.TF F P' - L.TF F P = (L.A + L.B * F)ᵀ * (P' - P) * (L.A + L.B * F) := by
    simp only [TF, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [this]
  exact posSemidef_transpose_mul_mul h _

/-- Expanding `T_F(P)`. -/
theorem TF_expand (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.Q + L.Aᵀ * P * L.A + L.Aᵀ * P * (L.B * F) + Fᵀ * (L.Bᵀ * P * L.A) +
      Fᵀ * (L.gainDen P * F) := by
  simp only [TF, gainDen, transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

/-! ### The Riccati map and the control gain -/

variable [DecidableEq U]

/-- The Riccati map (2.27): `R(P) = AᵀPA − AᵀPB(BᵀPB + R)⁻¹BᵀPA + Q`. -/
noncomputable def riccati (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Aᵀ * P * L.A - L.Aᵀ * P * L.B * (L.gainDen P)⁻¹ * L.Bᵀ * P * L.A + L.Q

/-- The control gain map (2.28): `F(P) = −(BᵀPB + R)⁻¹BᵀPA`. -/
noncomputable def gain (P : Matrix K K ℝ) : Matrix U K ℝ := -((L.gainDen P)⁻¹ * L.Bᵀ * P * L.A)

/-- `G(P)F(P) = −BᵀPA`. -/
theorem gainDen_mul_gain {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.gainDen P * L.gain P = -(L.Bᵀ * P * L.A) := by
  have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit)
  simp only [gain, Matrix.mul_neg, ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- **Exercise 2.3.13** (p. 90): `R(P) = (A + BF)ᵀP(A + BF) + FᵀRF + Q` when `F = F(P)`. -/
theorem riccati_eq_TF {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.riccati P = L.TF (L.gain P) P := by
  rw [TF_expand, L.gainDen_mul_gain hP]
  simp only [riccati, gain, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- **Exercise 2.3.14** (p. 90): `R` maps `𝒫` into itself. -/
theorem riccati_posSemidef {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.riccati P).PosSemidef := by
  rw [L.riccati_eq_TF hP]
  exact L.TF_posSemidef _ hP

/-! ### Lemma 2.3.3: the control gain minimizes the one-period objective -/

/-- Completing the square: `J(F(P)x + d) = J(F(P)x) + dᵀG(P)d`. -/
theorem cost_gain_add {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) (d : U → ℝ) :
    L.cost P x (L.gain P *ᵥ x + d) = L.cost P x (L.gain P *ᵥ x) + d ⬝ᵥ (L.gainDen P *ᵥ d) := by
  have hPs : Pᵀ = P := (posSemidef_iff_real.1 hP).1
  have hRs : L.Rᵀ = L.R := (posDef_iff_real.1 L.R_pd).1
  set F := L.gain P
  set y := L.A *ᵥ x + L.B *ᵥ (F *ᵥ x)
  have hGF : L.gainDen P *ᵥ (F *ᵥ x) = -(L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) := by
    rw [mulVec_mulVec, L.gainDen_mul_gain hP, neg_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hsplit : L.A *ᵥ x + L.B *ᵥ (F *ᵥ x + d) = y + L.B *ᵥ d := by
    simp only [y, mulVec_add]
    abel
  -- the cross terms vanish: `R(Fx) + BᵀP(Ax + BFx) = (G F + BᵀPA)x = 0`
  have hcross : d ⬝ᵥ (L.R *ᵥ (F *ᵥ x)) + d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) = 0 := by
    have e : L.gainDen P *ᵥ (F *ᵥ x) =
        L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) := by
      rw [gainDen, add_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [hGF] at e
    have : L.R *ᵥ (F *ᵥ x) + L.Bᵀ *ᵥ (P *ᵥ y) = 0 := by
      simp only [y, mulVec_add]
      rw [← sub_eq_zero]
      have e' := congrArg (fun z => z + L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) e
      simp only [neg_add_cancel] at e'
      rw [sub_zero]
      calc L.R *ᵥ (F *ᵥ x) + (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) + L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))))
          = L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) +
              L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) := by abel
        _ = 0 := e'.symm
    rw [← dotProduct_add, this, dotProduct_zero]
  have h1 := quad_add hRs (F *ᵥ x) d
  have h2 := quad_add hPs y (L.B *ᵥ d)
  have h3 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ y) = d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) := mulVec_dotProduct L.B d _
  have h4 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ (L.B *ᵥ d)) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) :=
    (dotProduct_transpose_mul_mul L.B P d).symm
  have h5 : d ⬝ᵥ (L.gainDen P *ᵥ d) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) + d ⬝ᵥ (L.R *ᵥ d) := by
    rw [gainDen, add_mulVec, dotProduct_add]
  simp only [cost]
  rw [hsplit, h1, h2, h3, h4, h5]
  linear_combination (2 : ℝ) * hcross

/-- **Lemma 2.3.3** (p. 91): `F(P)x` minimizes `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` over
`u ∈ ℝᵐ`, and the minimizer is unique. -/
theorem gain_isMinimizer {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) :
    (∀ u, L.cost P x (L.gain P *ᵥ x) ≤ L.cost P x u) ∧
      ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) → u = L.gain P *ᵥ x := by
  have hG := posDef_iff_real.1 (L.gainDen_posDef hP)
  have key : ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) +
      (u - L.gain P *ᵥ x) ⬝ᵥ (L.gainDen P *ᵥ (u - L.gain P *ᵥ x)) := fun u => by
    have := L.cost_gain_add hP x (u - L.gain P *ᵥ x)
    rwa [add_sub_cancel] at this
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [key u]
    rcases eq_or_ne (u - L.gain P *ᵥ x) 0 with h | h
    · rw [h]; simp
    · linarith [hG.2 h]
  · by_contra hne
    have := hG.2 (sub_ne_zero.2 hne)
    rw [key u] at hu
    linarith

/-- **Exercise 2.3.17** (p. 94): for `P ∈ 𝒫`, `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control
matrix `G`. -/
theorem gain_iff_TF_le {P : Matrix K K ℝ} (hP : P.PosSemidef) (F : Matrix U K ℝ) :
    F = L.gain P ↔ ∀ G : Matrix U K ℝ, L.TF F P ≤ L.TF G P := by
  classical
  constructor
  · rintro rfl G
    rw [le_iff, posSemidef_iff_real]
    refine ⟨by rw [transpose_sub, L.TF_transpose _ hP, L.TF_transpose _ hP], fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg]
    exact (L.gain_isMinimizer hP x).1 _
  · intro h
    -- `xᵀT_F x ≤ xᵀT_{F(P)}x`, so `Fx` attains the minimum, hence `Fx = F(P)x`
    have hx : ∀ x, F *ᵥ x = L.gain P *ᵥ x := by
      intro x
      have h1 := (posSemidef_iff_real.1 (le_iff.1 (h (L.gain P)))).2 x
      rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg] at h1
      exact (L.gain_isMinimizer hP x).2 _ (le_antisymm h1 ((L.gain_isMinimizer hP x).1 _))
    ext i j
    have := congrFun (hx (Pi.single j 1)) i
    simpa [mulVec, dotProduct, Pi.single_apply] using this

end LQProblem

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.3–§2.3.5.8 (pp. 91–95).

A control matrix `F` is *stable* when `ρ(A + BF) < 1`.

* **Exercise 2.3.15**: for stable `F`, `xₜ = (A + BF)ᵗx₀ → 0`.
* **Lemma 2.3.5**: for stable `F`, `T_F` is globally stable on `𝒫` with fixed point
  `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` (2.35), and `xᵀP_F x` is the lifetime cost
  `ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` (2.30).
* The ADP `(𝒫, 𝕋)` with the Loewner order and stable policies (§2.3.5.4) and **Lemma 2.3.6**
  (it is order stable).
* `𝒫_S`, **Lemma 2.3.7** (the control gain of `P ∈ 𝒫_S` is a stable `P`-min-greedy policy),
  **Lemma 2.3.8** (the Bellman min-operator is the Riccati map on `𝒫_S`) and **Lemma 2.3.9**
  (the Riccati equation, the Bellman min-equation and the LQ Bellman equation (2.26) agree).
* §2.3.5.8, given a fixed point `P*` of the Riccati map in `𝒫_S` (Lemma 2.3.4, which the book
  cites from Bertsekas): (a) `P*` is the least element of `𝒫_Σ`, (b) `T P* = P*`, (c) a policy is
  min-optimal iff it is `P*`-min-greedy; hence (2.38) and the optimality of `F(P*)`.
* **Example 2.3.1**: the scalar lifetime cost `c = (F² + 1)∑ (A + BF)^{2t}` (2.31), and with
  `A = B = 1`, `F = −0.6` costs less than `F = −0.9` from every state.
-/

open Matrix Filter Topology Set Function

open scoped MatrixOrder

namespace SargentStachurski.AbstractDecisionProcesses

/-- The positive semidefinite cone `𝒫` (§2.3.5.2). -/
def psdCone (K : Type*) [Fintype K] : Set (Matrix K K ℝ) := {P | P.PosSemidef}

namespace LQProblem

variable {K U : Type*} [Fintype K] [DecidableEq K] [Fintype U] (L : LQProblem K U)

/-- The closed-loop matrix `A + BF`. -/
def closedLoop (F : Matrix U K ℝ) : Matrix K K ℝ := L.A + L.B * F

/-- `F` is a stable control matrix (§2.3.5.3): `ρ(A + BF) < 1`. -/
def IsStable (F : Matrix U K ℝ) : Prop := specRad (L.closedLoop F) < 1

/-- The per-period cost matrix `FᵀRF + Q`. -/
def costMat (F : Matrix U K ℝ) : Matrix K K ℝ := Fᵀ * L.R * F + L.Q

/-- The `t`-th term `((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` of (2.35). -/
def discCost (F : Matrix U K ℝ) (t : ℕ) : Matrix K K ℝ :=
  (L.closedLoop F ^ t)ᵀ * L.costMat F * L.closedLoop F ^ t

omit [DecidableEq K] in
/-- `T_F(P) = (FᵀRF + Q) + (A + BF)ᵀP(A + BF)`. -/
theorem TF_eq (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.costMat F + (L.closedLoop F)ᵀ * P * L.closedLoop F := by
  simp only [TF, costMat, closedLoop]
  abel

/-! ### Exercise 2.3.15 and the decay of `(A + BF)ᵗ` -/

variable {L}

/-- For stable `F`, the entries of `(A + BF)ᵗ` decay geometrically. -/
theorem IsStable.entry_decay [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ t in atTop, ∀ i j, |(L.closedLoop F ^ t) i j| ≤ r ^ t := by
  set r := (specRad (L.closedLoop F) + 1) / 2
  have h0 := specRad_nonneg (L.closedLoop F)
  refine ⟨r, by positivity, by unfold IsStable at hF; simp only [r]; linarith, ?_⟩
  have hr : specRad (L.closedLoop F) < r := by unfold IsStable at hF; simp only [r]; linarith
  simp only [eventually_all]
  exact fun i j => eventually_abs_entry_pow_le _ hr i j

/-- For stable `F`, every entry of `(A + BF)ᵗ` tends to zero. -/
theorem IsStable.tendsto_entry [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (i j : K) :
    Tendsto (fun t => (L.closedLoop F ^ t) i j) atTop (𝓝 0) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hev.mono fun t ht => ht i j)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)

/-- **Exercise 2.3.15** (p. 92): for a stable control matrix, `xₜ = (A + BF)ᵗx₀ → 0`. -/
theorem IsStable.tendsto_state [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (x₀ : K → ℝ) : Tendsto (fun t => (L.closedLoop F ^ t) *ᵥ x₀) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j, 0 * x₀ j by simp]
  exact tendsto_finsetSum _ fun j _ => (hF.tendsto_entry i j).mul_const _

/-! ### Lemma 2.3.5 -/

omit [DecidableEq K] in
/-- `Nᵀ P N` in coordinates. -/
theorem transpose_mul_mul_apply (N P : Matrix K K ℝ) (a b : K) :
    (Nᵀ * P * N) a b = ∑ i, ∑ j, N i a * P i j * N j b := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq K] in
/-- If the entries of `Nₙ` tend to zero, so do those of `NₙᵀPNₙ`. -/
theorem tendsto_transpose_mul_mul_zero {N : ℕ → Matrix K K ℝ}
    (hN : ∀ i j, Tendsto (fun n => N n i j) atTop (𝓝 0)) (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((N n)ᵀ * P * N n) a b) atTop (𝓝 0) := by
  simp only [transpose_mul_mul_apply]
  rw [show (0 : ℝ) = ∑ i : K, ∑ j : K, 0 * P i j * 0 by simp]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((hN i a).mul_const _).mul (hN j b)

/-- The iterates of `T_F`: `T_Fⁿ P = ∑_{t<n} (Mᵗ)ᵀCMᵗ + (Mⁿ)ᵀPMⁿ` with `M = A + BF`,
`C = FᵀRF + Q`. -/
theorem TF_iterate (F : Matrix U K ℝ) (P : Matrix K K ℝ) (n : ℕ) :
    (L.TF F)^[n] P = ∑ t ∈ Finset.range n, L.discCost F t +
      (L.closedLoop F ^ n)ᵀ * P * L.closedLoop F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [discCost] at ih ⊢
    rw [iterate_succ_apply', ih, TF_eq, Finset.sum_range_succ', pow_zero, transpose_one,
      Matrix.one_mul, Matrix.mul_one, pow_succ, transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul, pow_succ,
      transpose_mul, Matrix.mul_assoc]
    abel

variable (L) in
/-- The lifetime cost matrix (2.35): `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ`. -/
noncomputable def PF (F : Matrix U K ℝ) : Matrix K K ℝ :=
  Matrix.of fun a b => ∑' t : ℕ, L.discCost F t a b

/-- (2.35): the series defining `P_F` converges, entry by entry. -/
theorem IsStable.hasSum_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (a b : K) :
    HasSum (fun t => L.discCost F t a b)
      (L.PF F a b) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  set c := ∑ i : K, ∑ j : K, |L.costMat F i j|
  have hsum : Summable fun t => L.discCost F t a b := by
    refine Summable.of_norm_bounded_eventually (g := fun t : ℕ => c * (r ^ 2) ^ t)
      ((summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left c) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with t ht
    rw [Real.norm_eq_abs, discCost, transpose_mul_mul_apply]
    calc |∑ i, ∑ j, (L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b|
        ≤ ∑ i, ∑ j, |(L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, r ^ t * |L.costMat F i j| * r ^ t := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (ht i a) (abs_nonneg _)) (ht j b)
              (abs_nonneg _) (by positivity)
      _ = c * (r ^ 2) ^ t := by
          simp only [c, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  exact hsum.hasSum

/-- **Lemma 2.3.5** (p. 93), convergence: for stable `F`, `T_Fⁿ P → P_F` entrywise from every
`P`. -/
theorem IsStable.tendsto_TF_iterate [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((L.TF F)^[n] P) a b) atTop (𝓝 (L.PF F a b)) := by
  simp only [TF_iterate, Matrix.add_apply, Matrix.sum_apply]
  rw [← add_zero (L.PF F a b)]
  exact (hF.hasSum_PF a b).tendsto_sum_nat.add
    (tendsto_transpose_mul_mul_zero (hF.tendsto_entry) P a b)

omit [DecidableEq K] in
/-- `T_F` is continuous, entry by entry. -/
theorem tendsto_TF {F : Matrix U K ℝ} {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ}
    (h : ∀ i j, Tendsto (fun n => Pn n i j) atTop (𝓝 (P i j))) (a b : K) :
    Tendsto (fun n => L.TF F (Pn n) a b) atTop (𝓝 (L.TF F P a b)) := by
  simp only [TF_eq, Matrix.add_apply, transpose_mul_mul_apply]
  exact tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((h i j).const_mul _).mul_const _)

/-- **Lemma 2.3.5** (p. 93), fixed point: `T_F P_F = P_F`. -/
theorem IsStable.TF_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    L.TF F (L.PF F) = L.PF F := by
  ext a b
  have h1 := (hF.tendsto_TF_iterate 0 a b).comp (tendsto_add_atTop_nat 1)
  have h2 := L.tendsto_TF (F := F) (fun i j => hF.tendsto_TF_iterate 0 i j) a b
  refine tendsto_nhds_unique h2 ?_
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply, iterate_succ_apply']

/-- `P_F` is the only fixed point of `T_F`. -/
theorem IsStable.eq_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) {P : Matrix K K ℝ}
    (hP : L.TF F P = P) : P = L.PF F := by
  ext a b
  have : ∀ n, (L.TF F)^[n] P = P := fun n => iterate_fixed hP n
  exact tendsto_nhds_unique (by simp [this])
    (hF.tendsto_TF_iterate P a b)

/-- `P_F` is positive semidefinite: it is a limit of positive semidefinite partial sums. -/
theorem IsStable.PF_posSemidef [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    (L.PF F).PosSemidef := by
  have hC : (L.costMat F).PosSemidef :=
    (posSemidef_transpose_mul_mul L.R_pd.posSemidef F).add L.Q_psd
  have hmem : ∀ n, ((L.TF F)^[n] 0).PosSemidef := by
    intro n
    induction n with
    | zero => exact PosSemidef.zero
    | succ n ih => rw [iterate_succ_apply']; exact L.TF_posSemidef F ih
  have hlim : Tendsto (fun n => (L.TF F)^[n] 0) atTop (𝓝 (L.PF F)) :=
    tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate 0 a b
  exact posSemidef_is_closed.mem_of_tendsto hlim (Eventually.of_forall hmem)

variable (L) in
/-- `T_F` restricted to the positive semidefinite cone `𝒫`. -/
def TFpsd (F : Matrix U K ℝ) (P : ↥(psdCone K)) : ↥(psdCone K) :=
  ⟨L.TF F P, L.TF_posSemidef F P.2⟩

omit [DecidableEq K] in
theorem TFpsd_iterate (F : Matrix U K ℝ) (P : ↥(psdCone K)) (n : ℕ) :
    ((L.TFpsd F)^[n] P : Matrix K K ℝ) = (L.TF F)^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

omit [DecidableEq K] in
/-- **Lemma 2.3.5** (p. 93): for stable `F`, `T_F` is globally stable on `𝒫`, with fixed point
`P_F` (2.35). -/
theorem IsStable.globallyStable [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    GloballyStable (L.TFpsd F) := by
  classical
  refine ⟨⟨L.PF F, hF.PF_posSemidef⟩, Subtype.ext hF.TF_PF, fun P hP => Subtype.ext
    (hF.eq_PF (congrArg Subtype.val hP)), fun P => ?_⟩
  rw [tendsto_subtype_rng]
  simp only [TFpsd_iterate]
  exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate P a b

/-- (2.30) and (2.35) (p. 93): `xᵀP_F x = ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` with `xₜ = (A + BF)ᵗx`. -/
theorem IsStable.hasSum_cost [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (x : K → ℝ) :
    HasSum (fun t => ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)))
      (x ⬝ᵥ (L.PF F *ᵥ x)) := by
  have e : ∀ t, ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)) =
      x ⬝ᵥ (L.discCost F t *ᵥ x) := fun t => (dotProduct_transpose_mul_mul _ _ x).symm
  simp_rw [e]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact hasSum_sum fun a _ => hasSum_sum fun b _ =>
    ((hF.hasSum_PF a b).mul_right (x b)).mul_left (x a)

/-! ### The ADP `(𝒫, 𝕋)` -/

variable (L) in
/-- The stable control matrices, the policies of §2.3.5.4. -/
def StablePolicy : Type _ := {F : Matrix U K ℝ // L.IsStable F}

/-- The LQ ADP `(𝒫, 𝕋)` (§2.3.5.4) with the Loewner order, given that some stable control matrix
exists (otherwise `𝕋` would be empty). **Exercise 2.3.16** gives monotonicity. -/
noncomputable def adp (hne : ∃ F, L.IsStable F) : ADP ↥(psdCone K) (StablePolicy L) where
  T F := L.TFpsd F.1
  mono F _ _ h := L.TF_mono F.1 h
  nonempty := ⟨⟨_, hne.choose_spec⟩⟩

omit [DecidableEq K] in
/-- **Lemma 2.3.6** (p. 93): the LQ ADP is (strongly) order stable. -/
theorem adp_isStronglyOrderStable [Nonempty K] (hne : ∃ F, L.IsStable F) :
    (adp hne).IsStronglyOrderStable := fun F =>
  stronglyOrderStable_of_globallyStable ((adp hne).mono F) F.2.globallyStable

/-! ### Min-greedy policies and the Bellman min-equation -/

omit [DecidableEq K] in
/-- Symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dotProduct_mulVec_eq {S S' : Matrix K K ℝ} (hS : Sᵀ = S) (hS' : S'ᵀ = S')
    (h : ∀ x, x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (S' *ᵥ x)) : S = S' := by
  classical
  set D := S - S'
  have hD : Dᵀ = D := by simp only [D, transpose_sub, hS, hS']
  have h0 : ∀ x, x ⬝ᵥ (D *ᵥ x) = 0 := fun x => by
    simp only [D, sub_mulVec, dotProduct_sub, h x, sub_self]
  have hentry : ∀ i j, Pi.single i 1 ⬝ᵥ (D *ᵥ Pi.single j 1) = D i j := fun i j => by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← sub_eq_zero]
  ext i j
  have hii := h0 (Pi.single i 1)
  have hjj := h0 (Pi.single j 1)
  have hij := h0 (Pi.single i 1 + Pi.single j 1)
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hentry, hentry, hentry,
    hentry] at hij
  rw [hentry] at hii hjj
  have hsym : D j i = D i j := by
    have := congrFun (congrFun hD i) j
    rwa [transpose_apply] at this
  change D i j = 0
  linarith

variable [DecidableEq U]

variable (L) in
/-- `𝒫_S`: the positive semidefinite `P` whose control gain `F(P)` is stable (§2.3.5.6). -/
def PS : Set (Matrix K K ℝ) := {P | P.PosSemidef ∧ L.IsStable (L.gain P)}

omit [DecidableEq K] in
/-- **Lemma 2.3.7** (p. 94): for `P ∈ 𝒫_S`, the control gain `F(P)` is a stable `P`-min-greedy
policy. -/
theorem gain_isMinGreedy (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinGreedy ⟨P, hP.1⟩ ⟨L.gain P, hP.2⟩ :=
  fun G => (L.gain_iff_TF_le hP.1 _).1 rfl G.1

omit [DecidableEq K] in
/-- **Lemma 2.3.8** (p. 94): on `𝒫_S` the Bellman min-operator is the Riccati map. -/
theorem isMinBellmanValue_riccati (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinBellmanValue ⟨P, hP.1⟩ ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ := by
  have hT : (adp hne).T ⟨L.gain P, hP.2⟩ ⟨P, hP.1⟩ = ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ :=
    Subtype.ext (L.riccati_eq_TF hP.1).symm
  refine ⟨?_, fun w hw => hT ▸ hw ⟨_, rfl⟩⟩
  rintro _ ⟨G, rfl⟩
  rw [← hT]
  exact gain_isMinGreedy hne hP G

omit [DecidableEq K] in
/-- **Lemma 2.3.9** (p. 95): for `P ∈ 𝒫_S`, (i) `R(P) = P` iff (ii) `T▿P = P` iff (iii)
`ℓ(x) = xᵀPx` satisfies the LQ Bellman equation (2.26),
`ℓ(x) = min_u {xᵀQx + uᵀRu + ℓ(Ax + Bu)}`. -/
theorem riccati_tfae (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (L.riccati P = P ↔ (adp hne).SolvesMinBellman ⟨P, hP.1⟩) ∧
      (L.riccati P = P ↔ ∀ x, IsLeast (range (L.cost P x)) (x ⬝ᵥ (P *ᵥ x))) := by
  have h8 := isMinBellmanValue_riccati hne hP
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h x => ?_, fun h => ?_⟩⟩
  · have : (⟨L.riccati P, L.riccati_posSemidef hP.1⟩ : ↥(psdCone K)) = ⟨P, hP.1⟩ :=
      Subtype.ext h
    rw [this] at h8
    exact h8
  · exact congrArg Subtype.val (h8.unique h)
  · have hval : x ⬝ᵥ (P *ᵥ x) = L.cost P x (L.gain P *ᵥ x) := by
      rw [← L.dotProduct_TF, ← L.riccati_eq_TF hP.1, h]
    rw [hval]
    exact ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
  · refine eq_of_dotProduct_mulVec_eq (posSemidef_iff_real.1 (L.riccati_posSemidef hP.1)).1
      (posSemidef_iff_real.1 hP.1).1 fun x => ?_
    rw [L.riccati_eq_TF hP.1, L.dotProduct_TF]
    have hmin : IsLeast (range (L.cost P x)) (L.cost P x (L.gain P *ᵥ x)) :=
      ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
    exact hmin.unique (h x)

omit [DecidableEq K] in
/-- §2.3.5.8 (p. 95): if `P* ∈ 𝒫_S` solves the Riccati equation (as Lemma 2.3.4 provides under
controllability and observability), then (a) `P*` is the least element of `𝒫_Σ`, (b) `P*` solves
the Bellman min-equation, (c) a policy is min-optimal iff it is `P*`-min-greedy, (2.38) holds,
and `F(P*)` is min-optimal. -/
theorem optimality [Nonempty K] (hne : ∃ F, L.IsStable F) {Pstar : Matrix K K ℝ}
    (hPS : Pstar ∈ L.PS) (hfix : L.riccati Pstar = Pstar) :
    IsLeast (adp hne).VSig ⟨Pstar, hPS.1⟩ ∧ (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ ∧
      (∀ F, (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed F ↔
        (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F) ∧
      (∀ x, IsLeast (range (L.cost Pstar x)) (x ⬝ᵥ (Pstar *ᵥ x))) ∧
      (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed
        ⟨L.gain Pstar, hPS.2⟩ := by
  have hos := (adp_isStronglyOrderStable hne).isOrderStable
  have hb : (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ := (riccati_tfae hne hPS).1.1 hfix
  have hG : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) ∈ (adp hne).VGmin :=
    ⟨⟨L.gain Pstar, hPS.2⟩, gain_isMinGreedy hne hPS⟩
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, -, -, huniq⟩, hbp⟩ := hos.minFundamentalOptimality hG hb
  have hvP : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) = v := huniq _ hG hb
  have hc : ∀ F, (adp hne).IsMinOptimal hos.wellPosed F ↔
      (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F := fun F => by
    rw [hbp F]
    constructor
    · rintro ⟨w, hw, hg⟩
      rwa [hvP, ← hw.unique hv]
    · intro hg
      exact ⟨v, hv, hvP ▸ hg⟩
  refine ⟨?_, hb, hc, (riccati_tfae hne hPS).2.1 hfix, (hc _).2 (gain_isMinGreedy hne hPS)⟩
  rw [hvP, ← hσ.isGLB.unique hv]
  exact hσ

/-! ### Example 2.3.1 -/

/-- **Example 2.3.1** (p. 91), (2.31): in the scalar case with `Q = R = 1`, a control `F` with
`|A + BF| < 1` has lifetime cost `ℓ_F(x₀) = c x₀²`, `c = (F² + 1)∑ₜ (A + BF)^{2t} =
(F² + 1)/(1 − (A + BF)²)`. -/
theorem scalar_lifetimeCost {A B F : ℝ} (h : |A + B * F| < 1) (x₀ : ℝ) :
    HasSum (fun t : ℕ => ((A + B * F) ^ t * x₀) ^ 2 * (F ^ 2 + 1))
      ((F ^ 2 + 1) / (1 - (A + B * F) ^ 2) * x₀ ^ 2) := by
  have hq0 : 0 ≤ (A + B * F) ^ 2 := sq_nonneg _
  have hq1 : (A + B * F) ^ 2 < 1 := by
    have := (sq_lt_one_iff_abs_lt_one _).2 h
    exact this
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((F ^ 2 + 1) * x₀ ^ 2)
  convert hg using 1
  · funext t
    rw [mul_pow, ← pow_mul, mul_comm t 2, pow_mul]
    ring
  · field_simp

/-- **Example 2.3.1** (p. 92): with `A = B = 1`, the control `F = −0.6` has lower lifetime cost
than `F = −0.9` from every state (`c = 34/21 < 181/99`). -/
theorem scalar_compare (x₀ : ℝ) :
    ((-0.6 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.6)) ^ 2) * x₀ ^ 2 ≤
      ((-0.9 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.9)) ^ 2) * x₀ ^ 2 := by
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  norm_num

end LQProblem

end SargentStachurski.AbstractDecisionProcesses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Distributional dynamic programming

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.4 (pp. 84–89).

Values are *distributional value functions*: stochastic kernels `η` from `X` to `ℝ` with a
uniformly bounded first moment, ordered pointwise by first-order stochastic dominance `⊴`. For a
policy `σ`, the distributional policy operator `D_σ` maps `η` to the law of `r_σ(x) + βV` with
`V ∼ (P_σ ⊗ η)(x)` (2.21)–(2.23).

* First-order stochastic dominance is a partial order on probability measures on `ℝ`
  (antisymmetry via distribution functions), so `(ℋ, ⊴)` is a poset.
* **Proposition 2.3.2**: each `D_σ` is an order preserving self-map of `(ℋ, ⊴)`, so
  `(ℋ, 𝕋_DDP)` is an ADP; and (2.23), `(D_σ η)(x, h) = ∫∫ h(r_σ(x) + βv) η(x', dv) P_σ(x, dx')`.
* **Exercise 2.3.11**: `D_σ` is a `β`-contraction for the supremum Wasserstein distance:
  `W₁((D_σ η)(x), (D_σ η')(x)) ≤ β sup_{x'} W₁(η(x'), η'(x'))`.
-/

open MeasureTheory ProbabilityTheory Set Function Filter

open scoped ENNReal

namespace SargentStachurski.AbstractDecisionProcesses

/-! ### First-order stochastic dominance -/

/-- `μ ⪯F ν` (§A.5.5): `∫ h dμ ≤ ∫ h dν` for every bounded increasing `h`. -/
def FOSD (μ ν : Measure ℝ) : Prop :=
  ∀ h : ℝ → ℝ, Monotone h → (∃ M, ∀ z, |h z| ≤ M) → ∫ z, h z ∂μ ≤ ∫ z, h z ∂ν

theorem FOSD.refl (μ : Measure ℝ) : FOSD μ μ := fun _ _ _ => le_rfl

theorem FOSD.trans {μ ν ρ : Measure ℝ} (h1 : FOSD μ ν) (h2 : FOSD ν ρ) : FOSD μ ρ :=
  fun h hm hb => (h1 h hm hb).trans (h2 h hm hb)

/-- Stochastic dominance is antisymmetric on probability measures: tails `μ(a, ∞)` determine the
distribution function. -/
theorem FOSD.antisymm {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h1 : FOSD μ ν) (h2 : FOSD ν μ) : μ = ν := by
  have hind : ∀ a, Monotone ((Set.Ioi a).indicator (1 : ℝ → ℝ)) := fun a z z' hzz' => by
    by_cases hz : z ∈ Set.Ioi a
    · have hz' : z' ∈ Set.Ioi a := lt_of_lt_of_le hz hzz'
      simp [indicator_of_mem hz, indicator_of_mem hz']
    · simp only [indicator_of_notMem hz]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hbd : ∀ a, ∃ M, ∀ z, |(Set.Ioi a).indicator (1 : ℝ → ℝ) z| ≤ M := fun a =>
    ⟨1, fun z => by by_cases hz : z ∈ Set.Ioi a <;> simp [hz]⟩
  have htail : ∀ a, μ (Set.Ioi a) = ν (Set.Ioi a) := fun a => by
    have e1 := h1 _ (hind a) (hbd a)
    have e2 := h2 _ (hind a) (hbd a)
    rw [integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Ioi]
      at e1 e2
    have := le_antisymm e1 e2
    rwa [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)] at this
  refine Measure.ext_of_Iic μ ν fun a => ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, htail]

/-! ### Distributional value functions -/

variable {X : Type*} [MeasurableSpace X]

variable (X) in
/-- `ℋ` (§2.3.4.1): stochastic kernels `η` from `X` to `ℝ` with `sup_x ∫ |z| η(x, dz) < ∞`. -/
def DistValue : Type _ :=
  {η : Kernel X ℝ // IsMarkovKernel η ∧ (∀ x, Integrable (fun z : ℝ => z) (η x)) ∧
    ∃ C, ∀ x, ∫ z, |z| ∂(η x) ≤ C}

/-- The pointwise stochastic dominance order `⊴` on `ℋ` (§2.3.4.1). -/
abbrev distOrder : PartialOrder (DistValue X) where
  le η η' := ∀ x, FOSD (η.1 x) (η'.1 x)
  le_refl η x := FOSD.refl _
  le_trans _ _ _ h1 h2 x := (h1 x).trans (h2 x)
  le_antisymm η η' h1 h2 := by
    have := η.2.1
    have := η'.2.1
    exact Subtype.ext (Kernel.ext fun x => FOSD.antisymm (h1 x) (h2 x))

attribute [local instance] distOrder

/-! ### The distributional policy operators -/

variable {A : Type*} [MeasurableSpace A]

/-- A distributional dynamic program (§2.3.4.1): a stochastic kernel `P` from `X × A` to `X`, a
bounded measurable reward `r` and a discount factor `β ∈ [0, 1)`. -/
structure DDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the transition kernel -/
  P : Kernel (X × A) X
  isMarkov : IsMarkovKernel P
  /-- the reward -/
  r : X × A → ℝ
  r_meas : Measurable r
  r_bdd : ∃ M, ∀ p, |r p| ≤ M
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

/-- Measurable policies `σ : X → A`. -/
def DDPPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] : Type _ :=
  {σ : X → A // Measurable σ}

namespace DDP

variable (D : DDP X A)

/-- `P_σ(x, ·) = P(x, σ(x), ·)`. -/
noncomputable def Pσ (σ : DDPPolicy X A) : Kernel X X :=
  D.P.comap (fun x => (x, σ.1 x)) (measurable_id.prodMk σ.2)

theorem isMarkov_Pσ (σ : DDPPolicy X A) : IsMarkovKernel (D.Pσ σ) := by
  have := D.isMarkov
  unfold Pσ
  infer_instance

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : DDPPolicy X A) (x : X) : ℝ := D.r (x, σ.1 x)

theorem measurable_rσ (σ : DDPPolicy X A) : Measurable (D.rσ σ) :=
  D.r_meas.comp (measurable_id.prodMk σ.2)

/-- The distributional policy operator (2.22): `(D_σ η)(x, ·)` is the law of `r_σ(x) + βV` with
`V ∼ (P_σ ⊗ η)(x, ·)` (2.21). -/
noncomputable def Dσ (σ : DDPPolicy X A) (η : Kernel X ℝ) : Kernel X ℝ :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ (η ∘ₖ D.Pσ σ))
    (fun p : X × ℝ => D.rσ σ p.1 + D.β * p.2)

theorem measurable_affine (σ : DDPPolicy X A) :
    Measurable fun p : X × ℝ => D.rσ σ p.1 + D.β * p.2 :=
  (D.measurable_rσ σ).comp measurable_fst |>.add (measurable_const.mul measurable_snd)

/-- `(D_σ η)(x, ·)` is the image of `(P_σ ⊗ η)(x, ·)` under `v ↦ r_σ(x) + βv`. -/
theorem Dσ_apply (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] (x : X) :
    D.Dσ σ η x = ((η ∘ₖ D.Pσ σ) x).map fun v => D.rσ σ x + D.β * v := by
  have := D.isMarkov_Pσ σ
  rw [Dσ, Kernel.map_apply _ (D.measurable_affine σ), Kernel.prod_apply,
    Kernel.deterministic_apply, Measure.dirac_prod, Measure.map_map (D.measurable_affine σ)
      measurable_prodMk_left]
  rfl

theorem measurable_affine_x (σ : DDPPolicy X A) (x : X) :
    Measurable fun v : ℝ => D.rσ σ x + D.β * v :=
  measurable_const.add (measurable_const.mul measurable_id)

/-- (2.23) (p. 85): `(D_σ η)(x, h) = ∫ [∫ h(r_σ(x) + βv) η(x', dv)] P_σ(x, dx')` for every bounded
measurable `h`. -/
theorem integral_Dσ (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] {h : ℝ → ℝ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : X) :
    ∫ z, h z ∂(D.Dσ σ η x) = ∫ x', ∫ v, h (D.rσ σ x + D.β * v) ∂(η x') ∂(D.Pσ σ x) := by
  have := D.isMarkov_Pσ σ
  rw [D.Dσ_apply σ η x, integral_map (D.measurable_affine_x σ x).aemeasurable
    hh.aestronglyMeasurable]
  refine Kernel.integral_comp ?_
  exact Integrable.of_bound ((hh.comp (D.measurable_affine_x σ x)).aestronglyMeasurable) M
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM _)

/-- (2.23) for an integrable test function. -/
theorem integral_Dσ' (σ : DDPPolicy X A) (η : Kernel X ℝ) [IsMarkovKernel η] {h : ℝ → ℝ}
    (hh : Measurable h) {x : X}
    (hint : Integrable (fun v => h (D.rσ σ x + D.β * v)) ((η ∘ₖ D.Pσ σ) x)) :
    ∫ z, h z ∂(D.Dσ σ η x) = ∫ x', ∫ v, h (D.rσ σ x + D.β * v) ∂(η x') ∂(D.Pσ σ x) := by
  rw [D.Dσ_apply σ η x, integral_map (D.measurable_affine_x σ x).aemeasurable
    hh.aestronglyMeasurable]
  exact Kernel.integral_comp hint

/-- `(P_σ ⊗ η)(x, ·)` has a finite first moment, at most that of `η`. -/
theorem comp_moment (σ : DDPPolicy X A) (η : DistValue X) {C : ℝ}
    (hC : ∀ x, ∫ z, |z| ∂(η.1 x) ≤ C) (x : X) :
    Integrable (fun z : ℝ => z) ((η.1 ∘ₖ D.Pσ σ) x) ∧ ∫ z, |z| ∂((η.1 ∘ₖ D.Pσ σ) x) ≤ C := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have hint := η.2.2.1
  have hC0 : 0 ≤ C := (integral_nonneg fun _ => abs_nonneg _).trans (hC x)
  have hlin : ∫⁻ z, ‖z‖ₑ ∂((η.1 ∘ₖ D.Pσ σ) x) ≤ ENNReal.ofReal C := by
    rw [Kernel.lintegral_comp _ _ _ measurable_enorm]
    calc ∫⁻ b, ∫⁻ z, ‖z‖ₑ ∂(η.1 b) ∂(D.Pσ σ x) ≤ ∫⁻ _b, ENNReal.ofReal C ∂(D.Pσ σ x) := by
          refine lintegral_mono fun b => ?_
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint b)]
          exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC b)
      _ = ENNReal.ofReal C := by simp
  have hI : Integrable (fun z : ℝ => z) ((η.1 ∘ₖ D.Pσ σ) x) :=
    ⟨measurable_id.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.ofReal_lt_top⟩
  refine ⟨hI, ?_⟩
  have e := ofReal_integral_norm_eq_lintegral_enorm hI
  rw [← ENNReal.ofReal_le_ofReal_iff hC0]
  simp only [Real.norm_eq_abs] at e
  rw [e]
  exact hlin

/-- **Proposition 2.3.2** (p. 85), self-map: `D_σ` maps `ℋ` into itself; if `|r| ≤ M` and the
first moments of `η` are at most `C`, those of `D_σ η` are at most `M + βC`. -/
noncomputable def Dσℋ (σ : DDPPolicy X A) (η : DistValue X) : DistValue X := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  refine ⟨D.Dσ σ η.1, ?_, fun x => ?_, ?_⟩
  · unfold Dσ
    exact Kernel.IsMarkovKernel.map _ (D.measurable_affine σ)
  · obtain ⟨hI, -⟩ := D.comp_moment σ η η.2.2.2.choose_spec x
    rw [D.Dσ_apply σ η.1 x]
    have e := integrable_map_measure (μ := (η.1 ∘ₖ D.Pσ σ) x) (g := fun z : ℝ => z)
      (f := fun v => D.rσ σ x + D.β * v) measurable_id.aestronglyMeasurable
      (D.measurable_affine_x σ x).aemeasurable
    rw [e]
    exact (integrable_const _).add (hI.const_mul _)
  · obtain ⟨M, hM⟩ := D.r_bdd
    refine ⟨M + D.β * η.2.2.2.choose, fun x => ?_⟩
    obtain ⟨hI, hle⟩ := D.comp_moment σ η η.2.2.2.choose_spec x
    rw [D.Dσ_apply σ η.1 x, integral_map (D.measurable_affine_x σ x).aemeasurable
      continuous_abs.aestronglyMeasurable]
    calc ∫ v, |D.rσ σ x + D.β * v| ∂((η.1 ∘ₖ D.Pσ σ) x)
        ≤ ∫ v, (M + D.β * |v|) ∂((η.1 ∘ₖ D.Pσ σ) x) := by
          refine integral_mono ((integrable_const _).add (hI.const_mul _)).abs
            ((integrable_const _).add (hI.abs.const_mul _)) fun v => ?_
          refine (abs_add_le _ _).trans (add_le_add (hM _) ?_)
          rw [abs_mul, abs_of_nonneg D.β_nonneg]
      _ = M + D.β * ∫ v, |v| ∂((η.1 ∘ₖ D.Pσ σ) x) := by
          rw [integral_add (integrable_const _) (hI.abs.const_mul _), integral_const,
            integral_const_mul]
          simp
      _ ≤ M + D.β * η.2.2.2.choose := by
          gcongr
          exact D.β_nonneg

theorem Dσℋ_coe (σ : DDPPolicy X A) (η : DistValue X) : (D.Dσℋ σ η).1 = D.Dσ σ η.1 := rfl

/-- **Proposition 2.3.2** (p. 85), order preservation: `η ⊴ η'` implies `D_σ η ⊴ D_σ η'`. -/
theorem Dσℋ_mono (σ : DDPPolicy X A) : Monotone (D.Dσℋ σ) := by
  intro η η' hle x h hmono ⟨M, hM⟩
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have := η'.2.1
  have hmeas : Measurable h := hmono.measurable
  rw [Dσℋ_coe, Dσℋ_coe, D.integral_Dσ σ η.1 hmeas hM, D.integral_Dσ σ η'.1 hmeas hM]
  set g : ℝ → ℝ := fun v => h (D.rσ σ x + D.β * v)
  have hgm : Monotone g := fun v w hvw =>
    hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvw D.β_nonneg))
  have hgmeas : Measurable g := hmeas.comp (D.measurable_affine_x σ x)
  have hgb : ∀ v, |g v| ≤ M := fun v => hM _
  have hint : ∀ (κ : Kernel X ℝ), IsMarkovKernel κ →
      Integrable (fun x' => ∫ v, g v ∂(κ x')) (D.Pσ σ x) := fun κ _ =>
    Integrable.of_bound (hgmeas.stronglyMeasurable.integral_kernel (κ := κ)).aestronglyMeasurable
      M (Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs]
        have := norm_integral_le_of_norm_le_const (μ := κ x') (f := g) (C := M)
          (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hgb v)
        simpa using this)
  exact integral_mono (hint η.1 η.2.1) (hint η'.1 η'.2.1) fun x' => hle x' g hgm ⟨M, hgb⟩

/-- The distributional ADP `(ℋ, 𝕋_DDP)` (§2.3.4.1), by Proposition 2.3.2. -/
noncomputable def ddpADP [Nonempty A] : ADP (DistValue X) (DDPPolicy X A) where
  T σ := D.Dσℋ σ
  mono σ := D.Dσℋ_mono σ
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

/-! ### Exercise 2.3.11 -/

/-- A `1`-Lipschitz `h` is integrable under a measure with finite first moment. -/
theorem integrable_of_lipschitz {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun z : ℝ => z) μ) {h : ℝ → ℝ} {K : NNReal} (hh : LipschitzWith K h) :
    Integrable h μ := by
  refine Integrable.mono' ((integrable_const |h 0|).add (hμ.abs.const_mul K))
    hh.continuous.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have := hh.dist_le_mul z 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  calc |h z| = |h 0 + (h z - h 0)| := by ring_nf
    _ ≤ |h 0| + |h z - h 0| := abs_add_le _ _
    _ ≤ |h 0| + K * |z| := add_le_add le_rfl this

/-- **Exercise 2.3.11** (p. 87), in test-function form: if every `1`-Lipschitz `h` has
`∫ h dη(x') − ∫ h dη'(x') ≤ d` at every `x'`, then every `1`-Lipschitz `h` has
`∫ h d(D_σ η)(x) − ∫ h d(D_σ η')(x) ≤ βd`: the map `v ↦ h(r_σ(x) + βv)` is `β`-Lipschitz. -/
theorem lipschitz_contraction (σ : DDPPolicy X A) (η η' : DistValue X) {d : ℝ}
    (hd : ∀ x' (h : ℝ → ℝ), LipschitzWith 1 h →
      ∫ z, h z ∂(η.1 x') - ∫ z, h z ∂(η'.1 x') ≤ d)
    (x : X) {h : ℝ → ℝ} (hh : LipschitzWith 1 h) :
    ∫ z, h z ∂(D.Dσ σ η.1 x) - ∫ z, h z ∂(D.Dσ σ η'.1 x) ≤ D.β * d := by
  have := D.isMarkov_Pσ σ
  have := η.2.1
  have := η'.2.1
  set g : ℝ → ℝ := fun v => h (D.rσ σ x + D.β * v)
  have hgL : LipschitzWith (Real.toNNReal D.β) g := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ D.β_nonneg]
    have := hh.dist_le_mul (D.rσ σ x + D.β * v) (D.rσ σ x + D.β * w)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
    calc |g v - g w| ≤ |D.rσ σ x + D.β * v - (D.rσ σ x + D.β * w)| := this
      _ = D.β * |v - w| := by
          rw [show D.rσ σ x + D.β * v - (D.rσ σ x + D.β * w) = D.β * (v - w) by ring, abs_mul,
            abs_of_nonneg D.β_nonneg]
  -- the integrable form of (2.23) for `h`
  have hcomp : ∀ ν : DistValue X, ∫ z, h z ∂(D.Dσ σ ν.1 x) =
      ∫ x', ∫ v, g v ∂(ν.1 x') ∂(D.Pσ σ x) := fun ν => by
    have := ν.2.1
    obtain ⟨hI, -⟩ := D.comp_moment σ ν ν.2.2.2.choose_spec x
    exact D.integral_Dσ' σ ν.1 hh.continuous.measurable
      (integrable_of_lipschitz (μ := (ν.1 ∘ₖ D.Pσ σ) x) hI hgL)
  -- `x' ↦ ∫ g dν(x')` is integrable under `P_σ(x, ·)`
  have hout : ∀ ν : DistValue X, Integrable (fun x' => ∫ v, g v ∂(ν.1 x')) (D.Pσ σ x) := by
    intro ν
    have := ν.2.1
    obtain ⟨C, hC⟩ := ν.2.2.2
    refine Integrable.of_bound
      (hgL.continuous.measurable.stronglyMeasurable.integral_kernel (κ := ν.1)).aestronglyMeasurable
      (|g 0| + D.β * C) (Eventually.of_forall fun x' => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    have hgi := integrable_of_lipschitz (ν.2.2.1 x') hgL
    calc ∫ v, |g v| ∂(ν.1 x') ≤ ∫ v, (|g 0| + D.β * |v|) ∂(ν.1 x') := by
          refine integral_mono hgi.abs ((integrable_const _).add
            ((ν.2.2.1 x').abs.const_mul _)) fun v => ?_
          have := hgL.dist_le_mul v 0
          rw [Real.dist_eq, Real.dist_eq, sub_zero, Real.coe_toNNReal _ D.β_nonneg] at this
          calc |g v| = |g 0 + (g v - g 0)| := by ring_nf
            _ ≤ |g 0| + |g v - g 0| := abs_add_le _ _
            _ ≤ |g 0| + D.β * |v| := add_le_add le_rfl this
      _ = |g 0| + D.β * ∫ v, |v| ∂(ν.1 x') := by
          rw [integral_add (integrable_const _) ((ν.2.2.1 x').abs.const_mul _), integral_const,
            integral_const_mul]
          simp
      _ ≤ |g 0| + D.β * C := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hC x') D.β_nonneg)
  rw [hcomp η, hcomp η', ← integral_sub (hout η) (hout η')]
  -- each inner difference is at most `βd`
  have hinner : ∀ x', ∫ v, g v ∂(η.1 x') - ∫ v, g v ∂(η'.1 x') ≤ D.β * d := by
    intro x'
    rcases D.β_nonneg.eq_or_lt with hβ | hβ
    · -- `β = 0`: `g` is constant
      have hg : g = fun _ => h (D.rσ σ x) := by funext v; simp [g, ← hβ]
      simp [hg, ← hβ]
    · -- `g/β` is `1`-Lipschitz
      have hL1 : LipschitzWith 1 fun v => g v / D.β := by
        refine LipschitzWith.of_dist_le_mul fun v w => ?_
        rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← sub_div, abs_div,
          abs_of_pos hβ, div_le_iff₀ hβ]
        have := hgL.dist_le_mul v w
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ D.β_nonneg] at this
        linarith
      have := hd x' _ hL1
      rw [integral_div, integral_div, ← sub_div, div_le_iff₀ hβ] at this
      linarith
  calc ∫ x', (∫ v, g v ∂(η.1 x') - ∫ v, g v ∂(η'.1 x')) ∂(D.Pσ σ x)
      ≤ ∫ _x', D.β * d ∂(D.Pσ σ x) :=
        integral_mono ((hout η).sub (hout η')) (integrable_const _) hinner
    _ = D.β * d := by simp

/-- The Wasserstein-1 distance `W₁(μ, ν) = sup_{‖h‖_Lip ≤ 1} (∫ h dμ − ∫ h dν)` (§2.3.4.2). -/
noncomputable def W1 (μ ν : Measure ℝ) : ℝ :=
  sSup {t | ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧ t = ∫ z, h z ∂μ - ∫ z, h z ∂ν}

/-- **Exercise 2.3.11** (p. 87): `D_σ` is a `β`-contraction for the supremum Wasserstein
distance: if `W₁(η(x'), η'(x')) ≤ d` for all `x'`, then `W₁((D_σ η)(x), (D_σ η')(x)) ≤ βd`. -/
theorem W1_contraction (σ : DDPPolicy X A) (η η' : DistValue X) {d : ℝ}
    (hbdd : ∀ x', BddAbove {t | ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧
      t = ∫ z, h z ∂(η.1 x') - ∫ z, h z ∂(η'.1 x')})
    (hd : ∀ x', W1 (η.1 x') (η'.1 x') ≤ d) (x : X) :
    W1 (D.Dσ σ η.1 x) (D.Dσ σ η'.1 x) ≤ D.β * d := by
  refine csSup_le ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken zero_le_one, by simp⟩ ?_
  rintro _ ⟨h, hh, rfl⟩
  exact D.lipschitz_contraction σ η η' (fun x' h hh =>
    (le_csSup (hbdd x') ⟨h, hh, rfl⟩).trans (hd x')) x hh

end DDP

end SargentStachurski.AbstractDecisionProcesses

set_option linter.style.longLine false
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.rowsum
#print axioms SargentStachurski.AbstractDecisionProcesses.IsDistribution
#print axioms SargentStachurski.AbstractDecisionProcesses.IsDistribution.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.IsDistribution.nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.IsDistribution.sum_eq_one
#print axioms SargentStachurski.AbstractDecisionProcesses.mulVec_apply_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.mul
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.pow
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.mulVec_const
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.GloballyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.iterate_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.AbstractDecisionProcesses.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.AbstractDecisionProcesses.fixedPt_le_of_le
#print axioms SargentStachurski.AbstractDecisionProcesses.le_fixedPt_of_le_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.isContractionOn_of_blackwell
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.AbstractDecisionProcesses.pow_nonneg_entries
#print axioms SargentStachurski.AbstractDecisionProcesses.pow_le_pow_entries
#print axioms SargentStachurski.AbstractDecisionProcesses.complexify
#print axioms SargentStachurski.AbstractDecisionProcesses.complexify_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.complexify_pow
#print axioms SargentStachurski.AbstractDecisionProcesses.complexify_transpose
#print axioms SargentStachurski.AbstractDecisionProcesses.nnnorm_complexify
#print axioms SargentStachurski.AbstractDecisionProcesses.norm_complexify
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad
#print axioms SargentStachurski.AbstractDecisionProcesses.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.AbstractDecisionProcesses.tendsto_norm_pow_rpow
#print axioms SargentStachurski.AbstractDecisionProcesses.eventually_norm_pow_le
#print axioms SargentStachurski.AbstractDecisionProcesses.tendsto_norm_pow_zero
#print axioms SargentStachurski.AbstractDecisionProcesses.summable_pow
#print axioms SargentStachurski.AbstractDecisionProcesses.one_sub_mul_tsum
#print axioms SargentStachurski.AbstractDecisionProcesses.tsum_mul_one_sub
#print axioms SargentStachurski.AbstractDecisionProcesses.neumann_series
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_transpose
#print axioms SargentStachurski.AbstractDecisionProcesses.norm_le_norm_of_abs_le
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_le_of_le
#print axioms SargentStachurski.AbstractDecisionProcesses.rowsum_abs_le_norm
#print axioms SargentStachurski.AbstractDecisionProcesses.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_entry_le_norm
#print axioms SargentStachurski.AbstractDecisionProcesses.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_le_norm
#print axioms SargentStachurski.AbstractDecisionProcesses.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.eventually_abs_entry_pow_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsBdd
#print axioms SargentStachurski.AbstractDecisionProcesses.IsSupContraction
#print axioms SargentStachurski.AbstractDecisionProcesses.IsUniformlyClosed
#print axioms SargentStachurski.AbstractDecisionProcesses.isBdd_const
#print axioms SargentStachurski.AbstractDecisionProcesses.IsBdd.sub
#print axioms SargentStachurski.AbstractDecisionProcesses.IsBdd.add
#print axioms SargentStachurski.AbstractDecisionProcesses.IsBdd.nonneg_bound
#print axioms SargentStachurski.AbstractDecisionProcesses.IsBdd.exists_dist
#print axioms SargentStachurski.AbstractDecisionProcesses.IsSupContraction.iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.AbstractDecisionProcesses.IsSupContraction.exists_limit
#print axioms SargentStachurski.AbstractDecisionProcesses.IsSupContraction.globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.le_of_le_map_of_tendsto
#print axioms SargentStachurski.AbstractDecisionProcesses.le_of_map_le_of_tendsto
#print axioms SargentStachurski.AbstractDecisionProcesses.bX
#print axioms SargentStachurski.AbstractDecisionProcesses.isUniformlyClosed_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.const_mem_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_max_sub_max_le
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.V
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.T
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.β
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.β_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.β_lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.nonempty
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bdd
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.closed
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.mono
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.exists_greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.T_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.eq_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.tendsto_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.le_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.IsGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.nonempty_policy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.isGreedy_greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.T_le_bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_eq_iSup
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vstar_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.bellman_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.eq_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.tendsto_bellman_iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_le_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_eq_vstar_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.IsOptimal
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.isOptimal_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.optimality
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vstar_le_of_bellman_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.le_vstar_of_le_bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.hpiPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_hpi_le_succ
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.vσ_hpi_eq_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.hpi_terminates
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.opi
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.opi_step
#print axioms SargentStachurski.AbstractDecisionProcesses.ContractingDP.tendsto_opi
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp
#print axioms SargentStachurski.AbstractDecisionProcesses.integrable_of_mem_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.measurable_markovOp
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_markovOp_le
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_mem_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_const
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_add
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_sub
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_smul
#print axioms SargentStachurski.AbstractDecisionProcesses.markovOp_sub_const
#print axioms SargentStachurski.AbstractDecisionProcesses.abs_markovOp_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.add
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.smul
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.mono
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.abs_le
#print axioms SargentStachurski.AbstractDecisionProcesses.isMarkovLike_markovOp
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.sub
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.abs_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.iterate_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.IsMarkovLike.abs_iterate_le
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_iterate_zero
#print axioms SargentStachurski.AbstractDecisionProcesses.affineOp_hasSum
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.P
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.isMarkov
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.profit
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.profit_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.β
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.β_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.β_lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.s
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.isMarkovLike_P
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.valOp
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.valOp_mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.valOp_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.valuation_globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.value
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.value_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.value_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.value_hasSum
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.measurable_sellPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_le_max
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.Tσ_sellPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.toDP
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.bellman_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.IsGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.isGreedy_iff_bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.abs_vσ_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.theorem_1_1_1
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.sellPolicy_optimal
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Γ
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Γ_nonempty
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.r
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.β
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.β_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.β_lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.P
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.P_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.P_sum
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Policy
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Q
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Tσ
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.isBdd_of_finite
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.abs_sum_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Q_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.abs_Q_sub_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Q_sub_const
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.exists_greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.toDP
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.IsGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.bellman_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.bellman_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Pσ
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.rσ
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Tσ_eq_mulVec
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.abs_Pσ_mulVec_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.vσ_eq_inv
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.vσ_hasSum
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.abs_vσ_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.finite_policy
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.theorem_1_2_1
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.theorem_1_2_2
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.vstar_le
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.IsLPFeasible
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.lp_solution
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.u
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.u_cont
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.u_bdd
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.φ
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.φ_prob
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.β
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.β_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.β_lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.R
#print axioms SargentStachurski.AbstractDecisionProcesses.SavingsPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.cont
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.Pσ
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.rσ
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.Tσ
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.integrable_comp
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.abs_cont_le
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.isMarkovLike_Pσ
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.rσ_mem
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.Tσ_mapsTo
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.Tσ_globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.vσ_hasSum
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.abs_fixedPoint_le
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.objective
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.bellmanOp
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.bddAbove_objective
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.bellmanOp_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.IsGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.toDP
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.bellman_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.dp_results
#print axioms SargentStachurski.AbstractDecisionProcesses.OrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.IncreasesTo
#print axioms SargentStachurski.AbstractDecisionProcesses.DecreasesTo
#print axioms SargentStachurski.AbstractDecisionProcesses.StronglyOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.orderStable_of_up_down
#print axioms SargentStachurski.AbstractDecisionProcesses.StronglyOrderStable.orderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.dualMap
#print axioms SargentStachurski.AbstractDecisionProcesses.orderStable_dual_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.dualMap_iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete.exists_least
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.AbstractDecisionProcesses.ChainComplete.orderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.chainComplete_Icc
#print axioms SargentStachurski.AbstractDecisionProcesses.CountablyDedekindComplete
#print axioms SargentStachurski.AbstractDecisionProcesses.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.AbstractDecisionProcesses.CountablyDedekindComplete.dual
#print axioms SargentStachurski.AbstractDecisionProcesses.OrderContinuous
#print axioms SargentStachurski.AbstractDecisionProcesses.OrderContinuous.monotone
#print axioms SargentStachurski.AbstractDecisionProcesses.isLUB_range_succ_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.tarski_kantorovich
#print axioms SargentStachurski.AbstractDecisionProcesses.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.T
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.mono
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.nonempty
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VG
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.WellPosed
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsFinite
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.Regular
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsBellmanValue
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.SolvesBellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.regular_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isGreedy_greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.T_le_bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.solvesBellman_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellman_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VU
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VSig
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.T_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.eq_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VSig_eq_range
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOptimal
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsValueFunction
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.BellmanPrinciple
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.FundamentalOptimality
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isOptimal_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.exists_solves_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsSelector
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.howard
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.opt
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsSelector.T_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.mem_VU_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.iterate_mono_of_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellman_le_opt
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.chain_2_9
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.mapsTo_VU
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.bellman_le_of_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VFIConverges
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.OPIConverges
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.HPIConverges
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.opt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.OPIConverges.vfi
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.iterates_le_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VU_nonempty
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.OrderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderContinuous
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.le_of_orderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.convergence_of_dedekind
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.dual
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.dual_dual
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsMinGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VGmin
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.MinRegular
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.MinOrderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsMinBellmanValue
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.SolvesMinBellman
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsMinValueFunction
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsMinOptimal
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.MinBellmanPrinciple
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.MinFundamentalOptimality
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isMinGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minRegular_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minOrderBounded_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isMinBellmanValue_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VGmin_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.dual_VSig
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.WellPosed.dual
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.dual_vσ
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isMinValueFunction_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.isMinOptimal_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.dual_opt_howard
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minBellmanPrinciple_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minFundamentalOptimality_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.VD
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.MinVFIConverges
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minVFIConverges_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.AbstractDecisionProcesses.ADP.IsOrderStable.minFundamentalOptimality
#print axioms SargentStachurski.AbstractDecisionProcesses.isLUB_of_tendsto_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.tendsto_of_isLUB_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.countablyDedekindComplete_bX
#print axioms SargentStachurski.AbstractDecisionProcesses.tendsto_markovOp
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.exercise_2_3_1
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_wellPosed
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_isOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_regular
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_bellman_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_isOrderContinuous
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_orderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.FirmProblem.adp_optimality
#print axioms SargentStachurski.AbstractDecisionProcesses.consumeAll
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_wellPosed
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_isOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_isGreedy_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_regular_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_bellman_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.exercise_2_3_4
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_orderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_isOrderContinuous
#print axioms SargentStachurski.AbstractDecisionProcesses.OptimalSavings.adp_optimality
#print axioms SargentStachurski.AbstractDecisionProcesses.isLUB_of_tendsto_subtype
#print axioms SargentStachurski.AbstractDecisionProcesses.isGLB_of_tendsto_subtype
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.nonempty_policy
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_wellPosed
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_isOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_isOrderContinuous
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.rbar
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.abs_r_le_rbar
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_orderBounded
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.exercise_2_3_7
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_regular
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adp_bellman_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.proposition_2_3_1
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Vhat
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.mem_Vhat_iff
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.Tσ_mapsTo_Vhat
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adpHat
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.vσ_mem_Vhat
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adpHat_isStronglyOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.adpHat_regular
#print axioms SargentStachurski.AbstractDecisionProcesses.FiniteMDP.exercise_2_3_10
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.A
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.B
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.Q
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.R
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.Q_psd
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.R_pd
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gainDen
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.cost
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.posSemidef_iff_real
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.posDef_iff_real
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.posSemidef_transpose_mul_mul
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gainDen_posDef
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.dotProduct_mulVec_comm_of_symm
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.mulVec_dotProduct
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.dotProduct_transpose_mul_mul
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.quad_add
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.dotProduct_TF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_posSemidef
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_transpose
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_expand
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.riccati
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gain
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gainDen_mul_gain
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.riccati_eq_TF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.riccati_posSemidef
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.cost_gain_add
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gain_isMinimizer
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gain_iff_TF_le
#print axioms SargentStachurski.AbstractDecisionProcesses.psdCone
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.closedLoop
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.costMat
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.discCost
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.entry_decay
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.tendsto_entry
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.tendsto_state
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.transpose_mul_mul_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.tendsto_transpose_mul_mul_zero
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TF_iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.PF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.hasSum_PF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.tendsto_TF_iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.tendsto_TF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.TF_PF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.eq_PF
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.PF_posSemidef
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TFpsd
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.TFpsd_iterate
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.globallyStable
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.IsStable.hasSum_cost
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.StablePolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.adp
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.adp_isStronglyOrderStable
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.eq_of_dotProduct_mulVec_eq
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.PS
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.gain_isMinGreedy
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.isMinBellmanValue_riccati
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.riccati_tfae
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.optimality
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.scalar_lifetimeCost
#print axioms SargentStachurski.AbstractDecisionProcesses.LQProblem.scalar_compare
#print axioms SargentStachurski.AbstractDecisionProcesses.FOSD
#print axioms SargentStachurski.AbstractDecisionProcesses.FOSD.refl
#print axioms SargentStachurski.AbstractDecisionProcesses.FOSD.trans
#print axioms SargentStachurski.AbstractDecisionProcesses.FOSD.antisymm
#print axioms SargentStachurski.AbstractDecisionProcesses.DistValue
#print axioms SargentStachurski.AbstractDecisionProcesses.distOrder
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.mk
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.P
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.isMarkov
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.r
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.r_meas
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.r_bdd
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.β
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.β_nonneg
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.β_lt_one
#print axioms SargentStachurski.AbstractDecisionProcesses.DDPPolicy
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Pσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.isMarkov_Pσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.rσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.measurable_rσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Dσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.measurable_affine
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Dσ_apply
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.measurable_affine_x
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.integral_Dσ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.integral_Dσ'
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.comp_moment
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Dσℋ
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Dσℋ_coe
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.Dσℋ_mono
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.ddpADP
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.integrable_of_lipschitz
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.lipschitz_contraction
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.W1
#print axioms SargentStachurski.AbstractDecisionProcesses.DDP.W1_contraction
