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
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Probability.Distributions.Gaussian.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Chapter 6 builds on
Markov matrices (§2.3.1.3), the contraction machinery of §1.2.2, Blackwell's
condition (Lemma 2.2.4), the comparison of fixed points of ordered operators
(Proposition 2.2.7) and the estimate `|max f − max g| ≤ max |f − g|`
(Lemma 2.2.2). Each chapter project is self-contained, so these are restated
here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

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

end SargentStachurski.StochasticDiscounting

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

namespace SargentStachurski.StochasticDiscounting

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

end SargentStachurski.StochasticDiscounting

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

namespace SargentStachurski.StochasticDiscounting

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

end SargentStachurski.StochasticDiscounting

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
they are proved in `Irreducible` and `PositiveMatrices`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.StochasticDiscounting

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

end SargentStachurski.StochasticDiscounting

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
coordinate, hence zero. The everywhere-positive case and the convergence
(2.11) are in `PositiveMatrices`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.StochasticDiscounting

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

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Everywhere-positive matrices: Dobrushin's estimate and the convergence (2.11)

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Theorem 2.3.1
(p. 69), last sentence: if `A ≫ 0` then, with the Perron–Frobenius vectors
normalised so that `⟨ε, e⟩ = 1`, `ρ(A)^{−t} Aᵗ → e εᵀ`. This completes the
theorem, whose nonnegative and irreducible parts are in `PerronFrobenius` and
`Irreducible`.

The proof conjugates to a Markov matrix. With `e ≫ 0` the right eigenvector,
`P(x, x') = A(x, x')e(x')/(ρ(A)e(x))` is a Markov matrix with positive entries
and `Pᵗ(x, x') = ρ(A)^{−t}Aᵗ(x, x')e(x')/e(x)`. Dobrushin's ℓ¹ estimate,
restated from the `FiniteStates/MarkovDynamics` project (Exercise 3.1.7): if
every entry of a Markov matrix `P` is at least `η > 0`, then `ψPᵗ → ψ*` for
every distribution `ψ`, where `ψ*` is the unique stationary distribution. Taking
`ψ = δₓ` gives `Pᵗ(x, ·) → ψ*`, so `ρ(A)^{−t}Aᵗ(x, x') → e(x)ψ*(x')/e(x')`, and
`ε := ψ*/e` is the left eigenvector with `⟨ε, e⟩ = ∑ψ* = 1`.
-/

open Matrix Finset Filter Topology

namespace SargentStachurski.StochasticDiscounting

variable {X : Type*} [Fintype X]

/-- `(ψP)(x') = ∑ ψ(x)P(x, x')`. -/
theorem vecMul_apply_eq (P : Matrix X X ℝ) (ψ : X → ℝ) (x' : X) :
    (ψ ᵥ* P) x' = ∑ x, ψ x * P x x' := rfl

/-- `ψ ↦ ψP` maps distributions to distributions. -/
theorem IsMarkov.isDistribution_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) : IsDistribution (ψ ᵥ* P) where
  nonneg x' := sum_nonneg fun x _ => mul_nonneg (hψ.nonneg x) (hP.nonneg x x')
  sum_eq_one := by
    simp only [vecMul_apply_eq]
    rw [sum_comm]
    simp only [← mul_sum, hP.rowsum, mul_one, hψ.sum_eq_one]

/-- `ψ ↦ ψP` preserves total mass. -/
theorem IsMarkov.sum_vecMul {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) :
    ∑ x', (d ᵥ* P) x' = ∑ x, d x := by
  simp only [vecMul_apply_eq]
  rw [sum_comm]
  simp only [← mul_sum, hP.rowsum, mul_one]

/-- The ℓ¹ norm `‖d‖₁ = ∑ |d(x)|` on `ℝ^X`. -/
def l1 (d : X → ℝ) : ℝ := ∑ x, |d x|

theorem l1_nonneg (d : X → ℝ) : 0 ≤ l1 d := sum_nonneg fun _ _ => abs_nonneg _

/-- The supremum norm is bounded by the ℓ¹ norm. -/
theorem norm_le_l1 (d : X → ℝ) : ‖d‖ ≤ l1 d := by
  rw [pi_norm_le_iff_of_nonneg (l1_nonneg d)]
  intro x
  rw [Real.norm_eq_abs]
  exact single_le_sum (fun y _ => abs_nonneg (d y)) (mem_univ x)

/-- Dobrushin's estimate: if every entry of the Markov matrix `P` is at least `η`, then for `d`
with `∑ d = 0`, `‖dP‖₁ ≤ (1 − nη)‖d‖₁`, where `n = |X|`. -/
theorem l1_vecMul_le {P : Matrix X X ℝ} (hP : IsMarkov P) {η : ℝ} (hη : ∀ x x', η ≤ P x x')
    {d : X → ℝ} (hd : ∑ x, d x = 0) :
    l1 (d ᵥ* P) ≤ (1 - Fintype.card X * η) * l1 d := by
  have hkey : ∀ x', (d ᵥ* P) x' = ∑ x, d x * (P x x' - η) := by
    intro x'
    rw [vecMul_apply_eq]
    have : ∑ x, d x * (P x x' - η) = ∑ x, d x * P x x' - (∑ x, d x) * η := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hd, zero_mul, sub_zero]
  have hrow : ∀ x, ∑ x', (P x x' - η) = 1 - Fintype.card X * η := by
    intro x
    rw [sum_sub_distrib, hP.rowsum, sum_const, card_univ, nsmul_eq_mul]
  unfold l1
  calc ∑ x', |(d ᵥ* P) x'| ≤ ∑ x', ∑ x, |d x| * (P x x' - η) := by
        refine sum_le_sum fun x' _ => ?_
        rw [hkey]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hη x x'))]
    _ = ∑ x, |d x| * ∑ x', (P x x' - η) := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = (1 - Fintype.card X * η) * ∑ x, |d x| := by
        simp only [hrow]
        rw [← sum_mul, mul_comm]

variable [DecidableEq X]

/-- `ψ ↦ ψPᵗ` preserves total mass. -/
theorem IsMarkov.sum_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) (d : X → ℝ) (t : ℕ) :
    ∑ x, (d ᵥ* P ^ t) x = ∑ x, d x := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← vecMul_vecMul, hP.sum_vecMul, ih]

/-- `ψPᵗ` is a distribution when `ψ` is. -/
theorem IsMarkov.isDistribution_vecMul_pow {P : Matrix X X ℝ} (hP : IsMarkov P) {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (t : ℕ) : IsDistribution (ψ ᵥ* P ^ t) := by
  induction t with
  | zero => simpa using hψ
  | succ t ih => rw [pow_succ, ← vecMul_vecMul]; exact hP.isDistribution_vecMul ih

/-- The iterated estimate: `‖dPᵗ‖₁ ≤ (1 − nη)ᵗ ‖d‖₁` for `∑ d = 0`. -/
theorem l1_vecMul_pow_le {P : Matrix X X ℝ} (hP : IsMarkov P) {η : ℝ} (hη : ∀ x x', η ≤ P x x')
    (hlam : 0 ≤ 1 - Fintype.card X * η) {d : X → ℝ} (hd : ∑ x, d x = 0) (t : ℕ) :
    l1 (d ᵥ* P ^ t) ≤ (1 - Fintype.card X * η) ^ t * l1 d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← vecMul_vecMul]
    have hsum : ∑ x, (d ᵥ* P ^ t) x = 0 := by rw [hP.sum_vecMul_pow, hd]
    calc l1 ((d ᵥ* P ^ t) ᵥ* P) ≤ (1 - Fintype.card X * η) * l1 (d ᵥ* P ^ t) :=
          l1_vecMul_le hP hη hsum
      _ ≤ (1 - Fintype.card X * η) * ((1 - Fintype.card X * η) ^ t * l1 d) :=
          mul_le_mul_of_nonneg_left ih hlam
      _ = (1 - Fintype.card X * η) ^ (t + 1) * l1 d := by ring

omit [DecidableEq X] in
/-- Coordinatewise continuity of `φ ↦ φP`: limits pass through `ᵥ*`. -/
theorem tendsto_vecMul {P : Matrix X X ℝ} {u : ℕ → X → ℝ} {a : X → ℝ}
    (h : Tendsto u atTop (𝓝 a)) : Tendsto (fun t => u t ᵥ* P) atTop (𝓝 (a ᵥ* P)) := by
  rw [tendsto_pi_nhds] at h ⊢
  intro x'
  simp only [vecMul_apply_eq]
  exact tendsto_finsetSum _ fun x _ => (h x).mul_const _

/-- A stationary `ψ` is fixed by every power. -/
theorem vecMul_pow_of_vecMul_eq {P : Matrix X X ℝ} {ψ : X → ℝ} (h : ψ ᵥ* P = ψ) (k : ℕ) :
    ψ ᵥ* P ^ k = ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, h]

/-- Exercise 3.1.7 (Vol. 1, p. 89), general form: if `P` is a Markov matrix with every entry
positive, then there is a stationary distribution `ψ*`, it is the only one, and `ψPᵗ → ψ*` for
every distribution `ψ`. Dobrushin's estimate makes the orbit of any distribution Cauchy. -/
theorem IsMarkov.tendsto_vecMul_pow_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ ψ' ᵥ* P = ψ' ∧
      (∀ φ, IsDistribution φ → φ ᵥ* P = φ → φ = ψ') ∧
      ∀ ψ, IsDistribution ψ → Tendsto (fun t : ℕ => ψ ᵥ* P ^ t) atTop (𝓝 ψ') := by
  -- the smallest entry `η > 0` and the modulus `λ = 1 − nη ∈ [0, 1)`
  obtain ⟨p, -, hp⟩ := exists_min_image (univ : Finset (X × X)) (fun q => P q.1 q.2) univ_nonempty
  set η := P p.1 p.2 with hηdef
  have hη : ∀ x x', η ≤ P x x' := fun x x' => hp (x, x') (mem_univ _)
  have hηpos : 0 < η := hpos _ _
  set n : ℕ := Fintype.card X with hn
  have hnpos : 0 < n := Fintype.card_pos
  set lam : ℝ := 1 - n * η with hlam
  have hlam0 : 0 ≤ lam := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have h1 := hP.rowsum x
    have h2 : ∑ x' : X, η ≤ ∑ x', P x x' := sum_le_sum fun x' _ => hη x x'
    rw [sum_const, card_univ, nsmul_eq_mul, h1] at h2
    rw [hlam]
    linarith
  have hlam1 : lam < 1 := by
    rw [hlam]
    have : (0 : ℝ) < n * η := by positivity
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
    rw [sum_sub_distrib, hP.sum_vecMul, sub_self]
  have hstep : ∀ t, dist (u t) (u (t + 1)) ≤ l1 (ψ₀ - ψ₀ ᵥ* P) * lam ^ t := by
    intro t
    rw [dist_eq_norm, hu]
    have h1 : ψ₀ ᵥ* P ^ t - ψ₀ ᵥ* P ^ (t + 1) = (ψ₀ - ψ₀ ᵥ* P) ᵥ* P ^ t := by
      rw [sub_vecMul, pow_succ', ← vecMul_vecMul]
    simp only
    rw [h1]
    refine (norm_le_l1 _).trans ?_
    rw [mul_comm]
    exact l1_vecMul_pow_le hP hη hlam0 hzero t
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
  have hstat : ψ' ᵥ* P = ψ' := by
    have h1 : Tendsto (fun t => u (t + 1)) atTop (𝓝 ψ') := hψ'.comp (tendsto_add_atTop_nat 1)
    have h2 : (fun t => u (t + 1)) = fun t => u t ᵥ* P := by
      funext t
      rw [hu]
      simp only
      rw [pow_succ, ← vecMul_vecMul]
    rw [h2] at h1
    exact tendsto_nhds_unique (tendsto_vecMul hψ') h1
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
        rw [sub_vecMul, vecMul_pow_of_vecMul_eq hstat]
      rw [h1]
      exact (norm_le_l1 _).trans (l1_vecMul_pow_le hP hη hlam0 hd t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const (l1 (ψ - ψ'))
  refine ⟨ψ', hψ'dist, hstat, fun φ hφ hφs => ?_, hconv⟩
  -- uniqueness: a stationary `φ` is its own orbit, which converges to `ψ'`
  have h1 : Tendsto (fun t : ℕ => φ ᵥ* P ^ t) atTop (𝓝 ψ') := hconv φ hφ
  have h2 : (fun t : ℕ => φ ᵥ* P ^ t) = fun _ => φ :=
    funext fun t => vecMul_pow_of_vecMul_eq hφs t
  rw [h2] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm

/-- The point mass at `x` is a distribution. -/
theorem isDistribution_single (x : X) : IsDistribution (Pi.single x (1 : ℝ)) where
  nonneg y := by
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  sum_eq_one := by simp

/-- `δₓ Pᵗ` is row `x` of `Pᵗ`. -/
theorem single_vecMul_eq_row (M : Matrix X X ℝ) (x : X) : Pi.single x (1 : ℝ) ᵥ* M = M x := by
  funext x'
  rw [vecMul_apply_eq]
  simp [Pi.single_apply]

/-- Rows of powers of a positive Markov matrix converge to the stationary distribution. -/
theorem IsMarkov.tendsto_pow_apply_of_pos [Nonempty X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hpos : ∀ x x', 0 < P x x') :
    ∃ ψ' : X → ℝ, IsDistribution ψ' ∧ ψ' ᵥ* P = ψ' ∧ (∀ x', 0 < ψ' x') ∧
      ∀ x x', Tendsto (fun t : ℕ => (P ^ t) x x') atTop (𝓝 (ψ' x')) := by
  obtain ⟨ψ', hdist, hstat, -, hconv⟩ := hP.tendsto_vecMul_pow_of_pos hpos
  refine ⟨ψ', hdist, hstat, fun x' => ?_, fun x x' => ?_⟩
  · -- `ψ'(x') = ∑ ψ'(x)P(x, x') > 0` since some `ψ'(x) > 0`
    obtain ⟨y, hy⟩ : ∃ y, 0 < ψ' y := by
      by_contra h
      have := hdist.sum_eq_one
      rw [sum_eq_zero fun y _ =>
        le_antisymm (not_lt.1 fun hy => h ⟨y, hy⟩) (hdist.nonneg y)] at this
      exact zero_ne_one this
    have h1 : ψ' y * P y x' ≤ (ψ' ᵥ* P) x' :=
      single_le_sum (fun z _ => mul_nonneg (hdist.nonneg z) (hP.nonneg z x')) (mem_univ y)
    rw [hstat] at h1
    exact lt_of_lt_of_le (mul_pos hy (hpos y x')) h1
  · have := tendsto_pi_nhds.1 (hconv _ (isDistribution_single x)) x'
    simpa only [single_vecMul_eq_row] using this

/-- The conjugate Markov matrix `P(x, x') = A(x, x')e(x')/(ρe(x))` of a positive matrix with
positive eigenvector `e`, `Ae = ρe`. -/
noncomputable def conjMarkov (A : Matrix X X ℝ) (e : X → ℝ) (ρ : ℝ) : Matrix X X ℝ :=
  Matrix.of fun x x' => A x x' * e x' / (ρ * e x)

omit [Fintype X] [DecidableEq X] in
theorem conjMarkov_apply (A : Matrix X X ℝ) (e : X → ℝ) (ρ : ℝ) (x x' : X) :
    conjMarkov A e ρ x x' = A x x' * e x' / (ρ * e x) := rfl

omit [DecidableEq X] in
/-- The conjugate is a Markov matrix with positive entries. -/
theorem isMarkov_conjMarkov {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') {e : X → ℝ}
    (he : ∀ x, 0 < e x) {ρ : ℝ} (hρ : 0 < ρ) (heA : A *ᵥ e = ρ • e) :
    IsMarkov (conjMarkov A e ρ) ∧ ∀ x x', 0 < conjMarkov A e ρ x x' := by
  have hpos' : ∀ x x', 0 < conjMarkov A e ρ x x' := fun x x' =>
    div_pos (mul_pos (hpos x x') (he x')) (mul_pos hρ (he x))
  refine ⟨⟨fun x x' => (hpos' x x').le, fun x => ?_⟩, hpos'⟩
  simp only [conjMarkov_apply]
  rw [← sum_div]
  have h1 : ∑ x', A x x' * e x' = ρ * e x := by
    have := congrFun heA x
    simpa [mulVec, dotProduct] using this
  rw [h1]
  exact div_self (mul_pos hρ (he x)).ne'

/-- `Pᵗ(x, x') = ρ^{−t}Aᵗ(x, x')e(x')/e(x)` for the conjugate matrix. -/
theorem conjMarkov_pow_apply (A : Matrix X X ℝ) {e : X → ℝ} (he : ∀ x, 0 < e x) {ρ : ℝ}
    (hρ : 0 < ρ) (t : ℕ) (x x' : X) :
    (conjMarkov A e ρ ^ t) x x' = (A ^ t) x x' * e x' / (ρ ^ t * e x) := by
  induction t generalizing x' with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs with h
    · subst h
      have := (he x).ne'
      field_simp
    · simp
  | succ t ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, sum_mul, sum_div]
    refine sum_congr rfl fun z _ => ?_
    rw [ih, conjMarkov_apply]
    have hz := (he z).ne'
    have hx := (he x).ne'
    have hρ' := hρ.ne'
    field_simp
    ring

/-- **Theorem 2.3.1, everywhere-positive case** (p. 69), the convergence (2.11): for `A ≫ 0`
there are positive right and left eigenvectors `e, ε` for `ρ(A)` with `⟨ε, e⟩ = 1` and
`ρ(A)^{−t} Aᵗ(x, x') → e(x)ε(x')` for all `x, x'`. -/
theorem tendsto_pow_of_pos [Nonempty X] {A : Matrix X X ℝ} (hpos : ∀ x x', 0 < A x x') :
    ∃ e ε : X → ℝ, (∀ x, 0 < e x) ∧ (∀ x, 0 < ε x) ∧ A *ᵥ e = specRad A • e ∧
      ε ᵥ* A = specRad A • ε ∧ ε ⬝ᵥ e = 1 ∧
      ∀ x x', Tendsto (fun t : ℕ => (specRad A)⁻¹ ^ t * (A ^ t) x x') atTop (𝓝 (e x * ε x')) := by
  have hirr := irreducible_of_pos hpos
  have hρ := hirr.specRad_pos
  obtain ⟨e, he, heA⟩ := hirr.exists_pos_eigenvector
  set ρ := specRad A with hρdef
  obtain ⟨hPm, hPpos⟩ := isMarkov_conjMarkov hpos he hρ heA
  obtain ⟨ψ, hψdist, hψstat, hψpos, hψconv⟩ := hPm.tendsto_pow_apply_of_pos hPpos
  refine ⟨e, fun x' => ψ x' / e x', he, fun x' => div_pos (hψpos x') (he x'), heA, ?_, ?_, ?_⟩
  · -- `ε A = ρ ε` from `ψP = ψ`
    funext x'
    have h1 := congrFun hψstat x'
    rw [vecMul_apply_eq] at h1
    simp only [conjMarkov_apply] at h1
    rw [vecMul_apply_eq, Pi.smul_apply, smul_eq_mul]
    have hx' := (he x').ne'
    have hρ' := hρ.ne'
    -- `∑ ψ(x) A(x, x') e(x') / (ρ e(x)) = ψ(x')`
    have h2 : ∑ x, ψ x / e x * A x x' = ρ * (ψ x' / e x') := by
      have h3 : ∑ x, ψ x * (A x x' * e x' / (ρ * e x)) =
          (e x' / ρ) * ∑ x, ψ x / e x * A x x' := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        have hx := (he x).ne'
        field_simp
      rw [h3] at h1
      rw [← h1]
      field_simp
    exact h2
  · -- `⟨ε, e⟩ = ∑ ψ = 1`
    have : ∑ x, ψ x / e x * e x = ∑ x, ψ x := sum_congr rfl fun x _ => div_mul_cancel₀ _ (he x).ne'
    change ∑ x, ψ x / e x * e x = 1
    rw [this]
    exact hψdist.sum_eq_one
  · intro x x'
    have h1 := hψconv x x'
    have h2 : ∀ t : ℕ, ρ⁻¹ ^ t * (A ^ t) x x' = (conjMarkov A e ρ ^ t) x x' * e x / e x' := by
      intro t
      rw [conjMarkov_pow_apply A he hρ]
      have hx := (he x).ne'
      have hx' := (he x').ne'
      have hρt : ρ ^ t ≠ 0 := pow_ne_zero _ hρ.ne'
      field_simp
      rw [one_div, inv_pow, mul_comm ((ρ ^ t)⁻¹), inv_mul_cancel_right₀ hρt]
    simp only [h2]
    have := (h1.mul_const (e x)).div_const (e x')
    convert this using 2
    ring

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lifetime valuation with time-varying discount factors

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.1.1–§6.1.2
(pp. 182–189).

* The discount operator `L(x, x') = b(x, x')P(x, x')` of (6.4). In operator
  form the `t`-period discounted expectation `E_x[β₁⋯βₜ h(Xₜ)]` of (6.6) is
  `(Lᵗh)(x)`, with the recursion (6.7) `Lᵗ⁺¹h = Lᵗ(Lh)`.
* Theorem 6.1.1: if `ρ(L) < 1` then `∑ₜ Lᵗh` converges and equals
  `(I − L)⁻¹h`, the unique solution of `v = h + Lv`. With `b ≡ β` this is
  Lemma 3.2.1, since `ρ(βP) = β`.
* Exercise 6.1.1: firm valuation with state-dependent interest rates;
  Exercise 6.1.2: the value is increasing when `P` is monotone, profits are
  increasing and nonnegative, and the interest rate is decreasing. The book
  omits nonnegativity of profits, without which the claim fails
  (see `docs/corrections.md`).
* Lemma 6.1.2: `ρ(L) = lim ℓₜ^{1/t}` with `ℓₜ = max_x (Lᵗ𝟙)(x)`, and
  `ρ(L) < 1` iff some `ℓₜ < 1`.
* Lemma 6.1.3: on a product state space `Y × Z` with the discount factor
  depending on the `Z` component only, `ρ(L) = ρ(L_Z)`. The kernel on `Y` may
  depend on the whole state, which §6.2.1.5 needs.
* Lemma 6.1.4: for `L ≥ 0` and `h ≫ 0`, `ρ(L) < 1` iff `v = h + Lv` has a
  unique solution in `(0, ∞)^X`, by the Perron–Frobenius left eigenvector.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The discount operator (6.4) -/

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

/-- (6.7): the `(t+1)`-period discounted expectation of `h` is the `t`-period discounted
expectation of `f = Lh`, in operator form `Lᵗ⁺¹h = Lᵗ(Lh)`. -/
theorem pow_succ_mulVec (L : Matrix X X ℝ) (h : X → ℝ) (t : ℕ) :
    L ^ (t + 1) *ᵥ h = L ^ t *ᵥ (L *ᵥ h) := by
  rw [pow_succ, ← mulVec_mulVec]

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

/-! ### Theorem 6.1.1 -/

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

/-- **Theorem 6.1.1** (p. 185) for the discount operator (6.4): the lifetime value (6.3), in its
operator form `∑ₜ Lᵗh`, converges and equals `(I − L)⁻¹h`. -/
theorem discountOp_value {b : X → X → ℝ} {P : Matrix X X ℝ} (hρ : specRad (discountOp b P) < 1)
    (h : X → ℝ) :
    (Summable fun t : ℕ => discountOp b P ^ t *ᵥ h) ∧
      (1 - discountOp b P)⁻¹ *ᵥ h = ∑' t : ℕ, discountOp b P ^ t *ᵥ h :=
  ⟨summable_pow_mulVec hρ h, inv_mulVec_eq_tsum hρ h⟩

omit [DecidableEq X] in
/-- Theorem 6.1.1 with `b ≡ β ∈ [0, 1)` is Lemma 3.2.1: `ρ(βP) = β < 1`. -/
theorem specRad_discountOp_const_lt_one {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : specRad (discountOp (fun _ _ => β) P) < 1 := by
  classical
  rw [discountOp_const, specRad_smul_isMarkov hP hβ0]
  exact hβ1

/-! ### Exercises 6.1.1 and 6.1.2: firm valuation -/

omit [DecidableEq X] [Nonempty X] in
/-- Exercise 6.1.1 (p. 186): with `rₜ = r(Xₜ)` and `βₜ = 1/(1 + rₜ)`, the discount operator is
`L(x, x') = P(x, x')/(1 + r(x'))`. -/
noncomputable def firmDiscountOp (r : X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  discountOp (fun _ x' => 1 / (1 + r x')) P

/-- Exercise 6.1.1 (p. 186): if `ρ(L) < 1` the firm's value is finite and equals
`(I − L)⁻¹π = ∑ₜ Lᵗπ`, computable by solving the linear system `v = π + Lv`. -/
theorem firmValue_eq {r : X → ℝ} {P : Matrix X X ℝ} (hρ : specRad (firmDiscountOp r P) < 1)
    (π : X → ℝ) :
    (1 - firmDiscountOp r P)⁻¹ *ᵥ π = ∑' t : ℕ, firmDiscountOp r P ^ t *ᵥ π ∧
      ∀ v, v = π + firmDiscountOp r P *ᵥ v ↔ v = (1 - firmDiscountOp r P)⁻¹ *ᵥ π :=
  ⟨inv_mulVec_eq_tsum hρ π, eq_add_mulVec_iff hρ π⟩

omit [DecidableEq X] [Nonempty X] in
/-- `Lg = P(b ⊙ g)` with `b(x') = 1/(1 + r(x'))`. -/
theorem firmDiscountOp_mulVec (r : X → ℝ) (P : Matrix X X ℝ) (g : X → ℝ) :
    firmDiscountOp r P *ᵥ g = P *ᵥ fun x' => 1 / (1 + r x') * g x' := by
  funext x
  simp only [firmDiscountOp, discountOp, mulVec, dotProduct, Matrix.of_apply]
  exact sum_congr rfl fun x' _ => by ring

omit [DecidableEq X] [Nonempty X] in
/-- A monotone increasing Markov matrix (Vol. 1, §3.2.2): `Ph` is increasing whenever `h` is. -/
def MonotoneKernel [Preorder X] (P : Matrix X X ℝ) : Prop :=
  ∀ h : X → ℝ, Monotone h → Monotone (P *ᵥ h)

/-- Exercise 6.1.2 (p. 186), with the hypothesis `π ≥ 0` that the book omits: if `P` is monotone
increasing, `π` is increasing and nonnegative, `r > −1` is decreasing and `ρ(L) < 1`, then the
firm's value `v = (I − L)⁻¹π` is increasing. Each term `Lᵗπ` is increasing and nonnegative, and so
is the sum. -/
theorem monotone_firmValue [Preorder X] {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hPm : MonotoneKernel P) {r π : X → ℝ} (hr : Antitone r) (hr1 : ∀ x, -1 < r x)
    (hπ : Monotone π) (hπ0 : ∀ x, 0 ≤ π x) (hρ : specRad (firmDiscountOp r P) < 1) :
    Monotone ((1 - firmDiscountOp r P)⁻¹ *ᵥ π) := by
  rw [inv_mulVec_eq_tsum hρ]
  have hb : Monotone fun x => 1 / (1 + r x) := fun x y hxy =>
    one_div_le_one_div_of_le (by linarith [hr1 y]) (by linarith [hr hxy])
  have hb0 : ∀ x, 0 ≤ 1 / (1 + r x) := fun x =>
    div_nonneg zero_le_one (by linarith [hr1 x])
  have key : ∀ t : ℕ, Monotone (firmDiscountOp r P ^ t *ᵥ π) ∧
      ∀ x, 0 ≤ (firmDiscountOp r P ^ t *ᵥ π) x := by
    intro t
    induction t with
    | zero => simpa using ⟨hπ, hπ0⟩
    | succ t ih =>
      rw [pow_succ', ← mulVec_mulVec, firmDiscountOp_mulVec]
      have hg : Monotone fun x' => 1 / (1 + r x') * (firmDiscountOp r P ^ t *ᵥ π) x' :=
        hb.mul ih.1 hb0 ih.2
      exact ⟨hPm _ hg, fun x => sum_nonneg fun x' _ =>
        mul_nonneg (hP.nonneg x x') (mul_nonneg (hb0 x') (ih.2 x'))⟩
  intro x y hxy
  have hs := summable_pow_mulVec hρ π
  rw [Pi.tsum_apply hs, Pi.tsum_apply hs]
  exact Summable.tsum_le_tsum (fun t => (key t).1 hxy) (Pi.summable.1 hs x) (Pi.summable.1 hs y)

/-! ### Lemma 6.1.2: the spectral radius via expectations -/

omit [Nonempty X] in
/-- `Lᵗ𝟙 ≥ 0` for `L ≥ 0`. -/
theorem pow_mulVec_one_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) (x : X) :
    0 ≤ (L ^ t *ᵥ fun _ => (1 : ℝ)) x :=
  sum_nonneg fun x' _ => mul_nonneg (pow_nonneg_entries hL t x x') zero_le_one

/-- `ℓₜ = max_x E_x[β₁⋯βₜ] = max_x (Lᵗ𝟙)(x)` equals `‖Lᵗ𝟙‖_∞`, as in the proof of Lemma 6.1.2. -/
theorem sup'_pow_mulVec_one_eq_norm {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) :
    (univ.sup' univ_nonempty fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) =
      ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
  have hnn := pow_mulVec_one_nonneg hL t
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun x _ => ?_
    have := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn x)] at this
  · rw [pi_norm_le_iff_of_nonneg
      ((hnn (Classical.arbitrary X)).trans (Finset.le_sup' _ (mem_univ _)))]
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact Finset.le_sup' (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) (mem_univ x)

/-- **Lemma 6.1.2** (p. 186), the formula (6.10): `ρ(L) = lim ℓₜ^{1/t}` with
`ℓₜ = max_x E_x[β₁⋯βₜ] = max_x (Lᵗ𝟙)(x)`, by the local spectral radius (Lemma 2.3.3). -/
theorem tendsto_sup'_pow_mulVec_one_rpow {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') :
    Tendsto (fun t : ℕ =>
      (univ.sup' univ_nonempty fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) ^ (1 / (t : ℝ)))
      atTop (𝓝 (specRad L)) := by
  simp only [sup'_pow_mulVec_one_eq_norm hL]
  exact tendsto_norm_pow_mulVec_rpow L hL fun _ => one_pos

/-- For `L ≥ 0`, `‖Lᵗ‖ = ‖Lᵗ𝟙‖_∞`: the operator norm is the largest row sum. -/
theorem norm_pow_eq_norm_pow_mulVec_one {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (t : ℕ) :
    ‖L ^ t‖ = ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
  have hnn := pow_mulVec_one_nonneg hL t
  apply le_antisymm
  · refine norm_le_of_rowsum_abs_le _ (norm_nonneg _) fun x => ?_
    have h1 : ∑ x', |(L ^ t) x x'| = (L ^ t *ᵥ fun _ => (1 : ℝ)) x := by
      simp only [mulVec, dotProduct, mul_one]
      exact sum_congr rfl fun x' _ => abs_of_nonneg (pow_nonneg_entries hL t x x')
    rw [h1]
    have h2 := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn x)] at h2
  · calc ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ≤ ‖L ^ t‖ * ‖fun _ : X => (1 : ℝ)‖ :=
          Matrix.linfty_opNorm_mulVec _ _
      _ = ‖L ^ t‖ := by rw [pi_norm_const (1 : ℝ), norm_one, mul_one]

/-- `ρ(L) ≤ ‖Lⁿ⁺¹‖^{1/(n+1)}` for every `n`, the finite-step form of Gelfand's formula. -/
theorem specRad_le_norm_pow_rpow (L : Matrix X X ℝ) (n : ℕ) :
    specRad L ≤ ‖L ^ (n + 1)‖ ^ (1 / ((n : ℝ) + 1)) := by
  have h := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div (𝕜 := ℂ) (complexify L) n
  have hone : ‖(1 : Matrix X X ℂ)‖₊ = 1 := by
    have h1 : (1 : Matrix X X ℂ) = complexify 1 := by
      rw [← pow_zero (complexify L), ← complexify_pow, pow_zero]
    rw [h1, nnnorm_complexify]
    apply NNReal.eq
    rw [coe_nnnorm, NNReal.coe_one]
    refine norm_eq_of_rowsum_eq (1 : Matrix X X ℝ) (fun i j => ?_) zero_le_one fun i => ?_
    · rw [Matrix.one_apply]
      split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  rw [hone, ENNReal.coe_one, ENNReal.one_rpow, mul_one, ← complexify_pow, nnnorm_complexify] at h
  have h2 := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top) h
  rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm] at h2
  exact_mod_cast h2

/-- **Lemma 6.1.2** (p. 187), second claim: for `L ≥ 0`, `ρ(L) < 1` iff `ℓₜ = ‖Lᵗ𝟙‖_∞ < 1` for
some `t ≥ 1`. The book cites Stachurski and Zhang (2021); the proof here is that `‖Lᵗ‖ = ℓₜ` for
`L ≥ 0`, `‖Lᵗ‖ → 0` when `ρ(L) < 1`, and `ρ(L) ≤ ‖Lᵗ‖^{1/t}`. -/
theorem specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') :
    specRad L < 1 ↔ ∃ t : ℕ, 0 < t ∧ ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ < 1 := by
  constructor
  · intro hρ
    obtain ⟨t, ht1, ht0⟩ := (((tendsto_norm_pow_zero L hρ).eventually (gt_mem_nhds one_pos)).and
      (eventually_gt_atTop 0)).exists
    exact ⟨t, ht0, by rw [← norm_pow_eq_norm_pow_mulVec_one hL]; exact ht1⟩
  · rintro ⟨t, ht, hlt⟩
    rw [← norm_pow_eq_norm_pow_mulVec_one hL] at hlt
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    calc specRad L ≤ ‖L ^ (n + 1)‖ ^ (1 / ((n : ℝ) + 1)) := specRad_le_norm_pow_rpow L n
      _ < 1 := Real.rpow_lt_one (norm_nonneg _) hlt (by positivity)

/-- The spectral radius of `L ≥ 0` is the limit of `‖Lᵗ𝟙‖^{1/t}` with `𝟙` replaced by any
`h ≫ 0`, as in Lemma 2.3.3; with `h = ψ*` for a stationary distribution this is the content of
Exercise 6.1.3 (`∑ₓ(Lᵗ𝟙)(x)ψ*(x)` is the `ψ*`-weighted ℓ¹ norm, equivalent to `‖·‖_∞`). -/
theorem tendsto_norm_pow_mulVec_rpow' {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {h : X → ℝ}
    (hh : ∀ x, 0 < h x) :
    Tendsto (fun t : ℕ => ‖L ^ t *ᵥ h‖ ^ (1 / (t : ℝ))) atTop (𝓝 (specRad L)) :=
  tendsto_norm_pow_mulVec_rpow L hL hh

/-- Exercise 6.1.3 (p. 187): for an irreducible Markov matrix `P` with stationary distribution
`ψ*`, `ρ(L) = lim (E_{ψ*}[β₁⋯βₜ])^{1/t}` where `E_{ψ*}[β₁⋯βₜ] = ∑ₓ ψ*(x)(Lᵗ𝟙)(x) = ⟨ψ*, Lᵗ𝟙⟩`.
Since `ψ* ≫ 0` (Exercise 2.3.2 (iv)), the weighted sum is squeezed between
`(min ψ*)‖Lᵗ𝟙‖` and `‖Lᵗ𝟙‖`, and both have `t`-th roots converging to `ρ(L)`. -/
theorem tendsto_dotProduct_pow_mulVec_one_rpow {P : Matrix X X ℝ} (hP : IsMarkov P)
    (hirr : Irreducible P) {b : X → X → ℝ} (hb : ∀ x x', 0 ≤ b x x') {ψ : X → ℝ}
    (hψ : IsDistribution ψ) (hψP : ψ ᵥ* P = ψ) :
    Tendsto (fun t : ℕ => (ψ ⬝ᵥ (discountOp b P ^ t *ᵥ fun _ => (1 : ℝ))) ^ (1 / (t : ℝ)))
      atTop (𝓝 (specRad (discountOp b P))) := by
  set L := discountOp b P with hLdef
  have hL : ∀ x x', 0 ≤ L x x' := discountOp_nonneg hb hP.nonneg
  -- `ψ* ≫ 0`
  obtain ⟨ψ', -, -, hψ'pos, huniq⟩ := hP.exists_unique_stationary_of_irreducible hirr
  have hψpos : ∀ x, 0 < ψ x := by
    rw [huniq ψ hψ hψP]
    exact hψ'pos
  obtain ⟨x₀, -, hx₀⟩ := exists_min_image univ ψ univ_nonempty
  set m := ψ x₀ with hm
  have hmpos : 0 < m := hψpos x₀
  have hnn := pow_mulVec_one_nonneg hL
  -- the weighted sum lies between `m‖Lᵗ𝟙‖` and `‖Lᵗ𝟙‖`
  have hupper : ∀ t, ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) ≤ ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by
    intro t
    calc ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) = ∑ x, ψ x * (L ^ t *ᵥ fun _ => (1 : ℝ)) x := rfl
      _ ≤ ∑ x, ψ x * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := sum_le_sum fun x _ => by
          refine mul_le_mul_of_nonneg_left ?_ (hψ.nonneg x)
          have := norm_le_pi_norm (L ^ t *ᵥ fun _ => (1 : ℝ)) x
          rwa [Real.norm_eq_abs, abs_of_nonneg (hnn t x)] at this
      _ = ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ := by rw [← sum_mul, hψ.sum_eq_one, one_mul]
  have hlower : ∀ t, m * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ≤ ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) := by
    intro t
    obtain ⟨x, -, hx⟩ := exists_max_image univ (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x)
      univ_nonempty
    have hnorm : ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ = (L ^ t *ᵥ fun _ => (1 : ℝ)) x := by
      rw [← sup'_pow_mulVec_one_eq_norm hL]
      exact le_antisymm (Finset.sup'_le _ _ fun y _ => hx y (mem_univ y))
        (Finset.le_sup' (fun x => (L ^ t *ᵥ fun _ => (1 : ℝ)) x) (mem_univ x))
    rw [hnorm]
    calc m * (L ^ t *ᵥ fun _ => (1 : ℝ)) x ≤ ψ x * (L ^ t *ᵥ fun _ => (1 : ℝ)) x :=
          mul_le_mul_of_nonneg_right (hx₀ x (mem_univ x)) (hnn t x)
      _ ≤ ∑ y, ψ y * (L ^ t *ᵥ fun _ => (1 : ℝ)) y :=
          single_le_sum (fun y _ => mul_nonneg (hψ.nonneg y) (hnn t y)) (mem_univ x)
      _ = ψ ⬝ᵥ (L ^ t *ᵥ fun _ => (1 : ℝ)) := rfl
  have hG := tendsto_norm_pow_mulVec_rpow L hL fun _ : X => one_pos
  have hlo : Tendsto (fun t : ℕ => m ^ (1 / (t : ℝ)) * ‖L ^ t *ᵥ fun _ => (1 : ℝ)‖ ^ (1 / (t : ℝ)))
      atTop (𝓝 (1 * specRad L)) := (tendsto_rpow_one_div_natCast hmpos).mul hG
  rw [one_mul] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hG (fun t => ?_) (fun t => ?_)
  · rw [← Real.mul_rpow hmpos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (hlower t) (by positivity)
  · exact Real.rpow_le_rpow (dotProduct_nonneg_of_nonneg hψ.nonneg (hnn t)) (hupper t)
      (by positivity)

/-! ### Lemma 6.1.3: discounting that depends on a component of the state -/

variable {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]

omit [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
/-- The discount operator on `X = Y × Z` when the discount factor depends only on the `Z`
component (p. 188): `L((y, z), (y', z')) = b(z, z')Q(z, z')R((y, z), y')`. The kernel `R` on `Y` is
allowed to depend on the whole current state, as in §6.2.1.5; the book's Lemma 6.1.3 has
`R(y, y')`. -/
def productDiscountOp (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) (R : Y × Z → Y → ℝ) :
    Matrix (Y × Z) (Y × Z) ℝ :=
  Matrix.of fun x x' => b x.2 x'.2 * Q x.2 x'.2 * R x x'.1

omit [DecidableEq Y] [DecidableEq Z] in
/-- `L(g ∘ snd) = (L_Z g) ∘ snd` when the rows of `R` sum to one. -/
theorem productDiscountOp_mulVec_comp_snd (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) {R : Y × Z → Y → ℝ}
    (hR : ∀ x, ∑ y', R x y' = 1) (g : Z → ℝ) :
    productDiscountOp b Q R *ᵥ (fun x => g x.2) = fun x => (discountOp b Q *ᵥ g) x.2 := by
  funext x
  simp only [mulVec, dotProduct, productDiscountOp, discountOp, Matrix.of_apply]
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun z' _ => ?_
  have h : ∀ y', b x.2 z' * Q x.2 z' * R x y' * g z' = b x.2 z' * Q x.2 z' * g z' * R x y' :=
    fun y' => by ring
  simp only [h]
  rw [← mul_sum, hR, mul_one]

/-- `Lᵗ𝟙 = (L_Zᵗ𝟙) ∘ snd`: the expected discount factor does not depend on `y`. -/
theorem productDiscountOp_pow_mulVec_one (b : Z → Z → ℝ) (Q : Matrix Z Z ℝ) {R : Y × Z → Y → ℝ}
    (hR : ∀ x, ∑ y', R x y' = 1) (t : ℕ) :
    productDiscountOp b Q R ^ t *ᵥ (fun _ => (1 : ℝ)) =
      fun x => (discountOp b Q ^ t *ᵥ fun _ => (1 : ℝ)) x.2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, productDiscountOp_mulVec_comp_snd b Q hR]
    funext x
    rw [pow_succ', ← mulVec_mulVec]

omit [DecidableEq Y] [DecidableEq Z] in
/-- `‖g ∘ snd‖_∞ = ‖g‖_∞`. -/
theorem norm_comp_snd [Nonempty Y] (g : Z → ℝ) : ‖fun x : Y × Z => g x.2‖ = ‖g‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    exact norm_le_pi_norm g x.2
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro z
    exact norm_le_pi_norm (fun x : Y × Z => g x.2) (Classical.arbitrary Y, z)

omit [DecidableEq Y] [DecidableEq Z] in
/-- **Lemma 6.1.3** (p. 188), in the general form with `R` depending on the whole state:
`ρ(L) = ρ(L_Z)`, since `Lᵗ𝟙 = (L_Zᵗ𝟙) ∘ snd` and both spectral radii are the limits of
Lemma 6.1.2. -/
theorem specRad_productDiscountOp [Nonempty Y] [Nonempty Z] {b : Z → Z → ℝ}
    (hb : ∀ z z', 0 ≤ b z z') {Q : Matrix Z Z ℝ} (hQ : ∀ z z', 0 ≤ Q z z') {R : Y × Z → Y → ℝ}
    (hR0 : ∀ x y', 0 ≤ R x y') (hR : ∀ x, ∑ y', R x y' = 1) :
    specRad (productDiscountOp b Q R) = specRad (discountOp b Q) := by
  classical
  have hL : ∀ x x', 0 ≤ productDiscountOp b Q R x x' := fun x x' =>
    mul_nonneg (mul_nonneg (hb _ _) (hQ _ _)) (hR0 _ _)
  have h1 := tendsto_norm_pow_mulVec_rpow (productDiscountOp b Q R) hL fun _ : Y × Z => one_pos
  have h2 := tendsto_norm_pow_mulVec_rpow (discountOp b Q) (discountOp_nonneg hb hQ)
    fun _ : Z => one_pos
  refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
  rw [productDiscountOp_pow_mulVec_one b Q hR, norm_comp_snd]

omit [DecidableEq Y] [DecidableEq Z] in
/-- **Lemma 6.1.3** (p. 188) as stated in the book: `R` is a Markov matrix on `Y`. -/
theorem specRad_productDiscountOp_isMarkov [Nonempty Y] [Nonempty Z] {b : Z → Z → ℝ}
    (hb : ∀ z z', 0 ≤ b z z') {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) {Rm : Matrix Y Y ℝ}
    (hRm : IsMarkov Rm) :
    specRad (productDiscountOp b Q fun x y' => Rm x.1 y') = specRad (discountOp b Q) :=
  specRad_productDiscountOp hb hQ.nonneg (fun x y' => hRm.nonneg x.1 y') fun x => hRm.rowsum x.1

/-! ### Lemma 6.1.4: necessity of the spectral radius condition -/

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

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Eventual contractions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.1.3 (pp. 189–192).

* A self-map `T` of `U` is eventually contracting if `Tᵏ` is a contraction on
  `U` for some `k` under some norm. Theorem 6.1.5 (Exercise 6.1.4): an
  eventual contraction on a closed set is globally stable. The fixed point of
  `Tᵏ` is fixed by `T`, since `T u*` is another fixed point of `Tᵏ`, and
  `‖Tⁿu − u*‖ ≤ L^{⌊n/k⌋} max_{r<k} ‖Tʳu − u*‖ → 0`.
* Exercise 6.1.5: if `Tᵏ` contracts under one norm then some `Tˡ` contracts
  under any equivalent norm. The equivalence constants, which exist for any two
  norms on `ℝ^X`, are hypotheses here.
* Example 6.1.2: `Tu = Au + b` with `ρ(A) < 1` is eventually contracting under
  the supremum norm, with fixed point `(I − A)⁻¹b`.
* Proposition 6.1.6: if `|Tv − Tw| ≤ L|v − w|` pointwise for a positive linear
  `L` with `ρ(L) < 1`, then `T` is eventually contracting.
* Proposition 6.1.7, the generalised Blackwell condition: an order-preserving
  `T` with `T(v + c) ≤ Tv + Lc` for `c ≥ 0` satisfies the hypothesis of
  Proposition 6.1.6.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Theorem 6.1.5 -/

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

/-! ### Exercise 6.1.5: changing the norm -/

omit [NormedAddCommGroup E] in
/-- Exercise 6.1.5 (p. 190): let `Nₐ, N_b` be two norms with `N_b ≤ c₂Nₐ` and `Nₐ ≤ c₁N_b` (any two
norms on `ℝ^X` are so related). If `Tᵏ` is a contraction on `U` under `Nₐ`, then some `Tˡ` is a
contraction on `U` under `N_b`: take `ℓ = km` with `c₂c₁Lᵐ < 1`. -/
theorem exists_iterate_contraction_of_norm_equiv [AddCommGroup E] (Na Nb : E → ℝ) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hba : ∀ u, Nb u ≤ c₂ * Na u) (hab : ∀ u, Na u ≤ c₁ * Nb u)
    {T : E → E} {U : Set E} (hT : Set.MapsTo T U U) {k : ℕ} {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hcon : ∀ u ∈ U, ∀ v ∈ U, Na (T^[k] u - T^[k] v) ≤ L * Na (u - v)) :
    ∃ ℓ : ℕ, ∃ L' : ℝ, 0 ≤ L' ∧ L' < 1 ∧
      ∀ u ∈ U, ∀ v ∈ U, Nb (T^[ℓ] u - T^[ℓ] v) ≤ L' * Nb (u - v) := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (c₂ * c₁) by positivity) hL1
  have hiter : ∀ (n : ℕ) (u : E), u ∈ U → ∀ v ∈ U,
      Na ((T^[k])^[n] u - (T^[k])^[n] v) ≤ L ^ n * Na (u - v) := by
    intro n
    induction n with
    | zero => intro u _ v _; simp
    | succ n ih =>
      intro u hu v hv
      rw [iterate_succ_apply', iterate_succ_apply']
      calc Na (T^[k] ((T^[k])^[n] u) - T^[k] ((T^[k])^[n] v))
          ≤ L * Na ((T^[k])^[n] u - (T^[k])^[n] v) :=
            hcon _ ((hT.iterate k).iterate n hu) _ ((hT.iterate k).iterate n hv)
        _ ≤ L * (L ^ n * Na (u - v)) := mul_le_mul_of_nonneg_left (ih u hu v hv) hL0
        _ = L ^ (n + 1) * Na (u - v) := by ring
  refine ⟨k * m, c₂ * c₁ * L ^ m, by positivity, ?_, fun u hu v hv => ?_⟩
  · have := (lt_div_iff₀ (by positivity)).1 hm
    linarith
  · rw [iterate_mul]
    calc Nb ((T^[k])^[m] u - (T^[k])^[m] v) ≤ c₂ * Na ((T^[k])^[m] u - (T^[k])^[m] v) := hba _
      _ ≤ c₂ * (L ^ m * Na (u - v)) := mul_le_mul_of_nonneg_left (hiter m u hu v hv) hc₂.le
      _ ≤ c₂ * (L ^ m * (c₁ * Nb (u - v))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hab _) ?_) hc₂.le
          positivity
      _ = c₂ * c₁ * L ^ m * Nb (u - v) := by ring

/-! ### Example 6.1.2: affine maps -/

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- The affine map `Tu = Au + b` of Example 6.1.2. -/
def affineOp (A : Matrix X X ℝ) (b : X → ℝ) (u : X → ℝ) : X → ℝ := A *ᵥ u + b

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
theorem exists_isContractionOn_iterate_affineOp [Nonempty X] {A : Matrix X X ℝ}
    (hρ : specRad A < 1) (b : X → ℝ) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn ((affineOp A b)^[k]) Set.univ ‖A ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero A hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun u _ v _ => ?_⟩
  rw [affineOp_iterate_sub]
  exact Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq X] in
/-- Example 6.1.2 (p. 190): `Tu = Au + b` with `ρ(A) < 1` is globally stable, by Theorem 6.1.5. -/
theorem globallyStable_affineOp [Nonempty X] {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : GloballyStable (affineOp A b) := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_affineOp hρ b
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Example 6.1.2 (p. 190): the fixed point is `(I − A)⁻¹b`, by the Neumann series lemma. -/
theorem isFixedPt_affineOp_inv [Nonempty X] {A : Matrix X X ℝ} (hρ : specRad A < 1)
    (b : X → ℝ) : IsFixedPt (affineOp A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  rw [add_comm]
  exact (inv_mulVec_eq_add hρ b).symm

/-! ### Proposition 6.1.6: a spectral radius condition -/

omit [DecidableEq X] in
/-- A nonnegative matrix preserves `≤`. -/
theorem mulVec_le_mulVec_of_nonneg {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') {f g : X → ℝ}
    (hfg : f ≤ g) : L *ᵥ f ≤ L *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hL x x')

omit [DecidableEq X] in
/-- `‖|f|‖_∞ = ‖f‖_∞`. -/
theorem norm_abs_fun (f : X → ℝ) : ‖fun y => |f y|‖ = ‖f‖ := by
  simp only [Pi.norm_def, Real.nnnorm_abs]

omit [DecidableEq X] in
/-- If `|u| ≤ w` pointwise with `w ≥ 0`, then `‖u‖_∞ ≤ ‖w‖_∞`. -/
theorem norm_le_norm_of_abs_le_fun {u w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (h : ∀ x, |u x| ≤ w x) :
    ‖u‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  refine (h x).trans ?_
  have := norm_le_pi_norm w x
  rwa [Real.norm_eq_abs, abs_of_nonneg (hw x)] at this

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
theorem exists_isContractionOn_iterate_of_abs_sub_le [Nonempty X] {T : (X → ℝ) → (X → ℝ)}
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
theorem globallyStable_of_abs_sub_le [Nonempty X] {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : IsClosed U) (hne : U.Nonempty) (hT : Set.MapsTo T U U) {L : Matrix X X ℝ}
    (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdom : ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x) :
    ∃ u' ∈ U, IsFixedPt T u' ∧ (∀ v ∈ U, IsFixedPt T v → v = u') ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => T^[n] u) atTop (𝓝 u') := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ hdom
  exact globallyStable_of_iterate_contraction hU hne hT hk hc

/-! ### Proposition 6.1.7: a generalised Blackwell condition -/

omit [DecidableEq X] in
/-- **Proposition 6.1.7** (p. 191), the estimate: if `U` is closed under adding nonnegative
functions, `T` is order preserving on `U`, and `T(v + c) ≤ Tv + Lc` for `v ∈ U` and `c ≥ 0`, then
`|Tv − Tw| ≤ L|v − w|` on `U`. -/
theorem abs_sub_le_of_blackwell {T : (X → ℝ) → (X → ℝ)} {U : Set (X → ℝ)}
    (hU : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → v + c ∈ U)
    (hmono : ∀ v ∈ U, ∀ w ∈ U, v ≤ w → T v ≤ T w) {L : Matrix X X ℝ}
    (hdisc : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    ∀ v ∈ U, ∀ w ∈ U, ∀ x, |T v x - T w x| ≤ (L *ᵥ fun y => |v y - w y|) x := by
  have key : ∀ v ∈ U, ∀ w ∈ U, ∀ x, T v x - T w x ≤ (L *ᵥ fun y => |v y - w y|) x := by
    intro v hv w hw x
    have habs0 : (0 : X → ℝ) ≤ fun y => |v y - w y| := fun y => abs_nonneg _
    have hle : v ≤ w + fun y => |v y - w y| := fun y => by
      simp only [Pi.add_apply]
      linarith [le_abs_self (v y - w y)]
    have h1 := hmono v hv _ (hU w hw _ habs0) hle x
    have h2 := hdisc w hw _ habs0 x
    simp only [Pi.add_apply] at h1 h2
    linarith
  intro v hv w hw x
  rw [abs_sub_le_iff]
  refine ⟨key v hv w hw x, ?_⟩
  have := key w hw v hv x
  simpa [abs_sub_comm] using this

/-- **Proposition 6.1.7** (p. 191): under the generalised Blackwell condition with `ρ(L) < 1`, `T`
is eventually contracting on `U`. -/
theorem exists_isContractionOn_iterate_of_blackwell [Nonempty X] {T : (X → ℝ) → (X → ℝ)}
    {U : Set (X → ℝ)} (hT : Set.MapsTo T U U) (hU : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → v + c ∈ U)
    (hmono : ∀ v ∈ U, ∀ w ∈ U, v ≤ w → T v ≤ T w) {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdisc : ∀ v ∈ U, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (T^[k]) U ‖L ^ k‖ :=
  exists_isContractionOn_iterate_of_abs_sub_le hT hL hρ (abs_sub_le_of_blackwell hU hmono hdisc)

omit [DecidableEq X] in
/-- Proposition 6.1.7 with Theorem 6.1.5 on all of `ℝ^X`: an order-preserving `T` with
`T(v + c) ≤ Tv + Lc` for `c ≥ 0` and `ρ(L) < 1` is globally stable. -/
theorem globallyStable_of_blackwell [Nonempty X] {T : (X → ℝ) → (X → ℝ)} (hmono : Monotone T)
    {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x') (hρ : specRad L < 1)
    (hdisc : ∀ v : X → ℝ, ∀ c : X → ℝ, 0 ≤ c → T (v + c) ≤ T v + L *ᵥ c) :
    GloballyStable T := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_blackwell (Set.mapsTo_univ T Set.univ)
    (fun _ _ _ _ => Set.mem_univ _) (fun v _ w _ hvw => hmono hvw) hL hρ
    (fun v _ c hc => hdisc v c hc)
  exact globallyStable_of_iterate_contraction_univ hk hc

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# MDPs with state-dependent discounting: the model and finite lifetime values

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.1–§6.2.1.2
(pp. 192–194).

An MDP with state-dependent discounting replaces the constant `β` of a regular
MDP `(Γ, β, r, P)` by a function `β(x, a, x') ≥ 0` of the current state, the
action and the next state. The policy operator (6.16) is `T_σ v = r_σ + L_σ v`
with the discount operator (6.17) `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`.
Under Assumption 6.2.1, `ρ(L_σ) < 1` for every feasible `σ`:

* Lemma 6.2.1: `I − L_σ` is invertible and `T_σ` has the unique fixed point
  `v_σ = (I − L_σ)⁻¹ r_σ`, (6.18).
* Exercise 6.2.1: `v_σ = ∑ₜ L_σᵗ r_σ`, the lifetime value (6.19) in operator
  form; `T_σᵏv` is the `k`-period value with terminal payoff `v`.
* Exercise 6.2.2: `T_σ` is globally stable on `ℝ^X` (Example 6.1.2).
* Exercise 6.2.3: Assumption 6.2.1 holds whenever `βP ≤ L` on the feasible pairs
  for some `L` with `ρ(L) < 1`; in particular whenever `sup β < 1` (p. 193).

As in Chapter 5, `r`, `β` and `P` are given on all of `X × A`, with `P(x, a, ·)`
a distribution for every `a`; values off the feasible set never enter.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- An MDP with state-dependent discounting (§6.2.1.1): `(Γ, β, r, P)` with
`β : G × X → ℝ₊`. -/
structure SDMDP (X A : Type*) [Fintype X] [Fintype A] where
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  r : X → A → ℝ
  β : X → A → X → ℝ
  β_nonneg : ∀ x a x', 0 ≤ β x a x'
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_rowsum : ∀ x a, ∑ x', P x a x' = 1

namespace SDMDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : SDMDP X A)

/-- The feasible state–action pairs `G`. -/
def Feasible (x : X) (a : A) : Prop := a ∈ M.Γ x

/-- A feasible policy: `σ(x) ∈ Γ(x)` for all `x`. -/
abbrev IsFeasible (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

/-- The set `Σ` of feasible policies, as a subtype. -/
abbrev Policy := {σ : X → A // M.IsFeasible σ}

/-- A feasible policy exists. -/
noncomputable def defaultPolicy : M.Policy :=
  ⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩

theorem policy_nonempty : Nonempty M.Policy := ⟨M.defaultPolicy⟩

/-- The closed-loop transition matrix `P_σ(x, x') = P(x, σ(x), x')` (p. 194). -/
def Pσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.P x (σ x) x'

theorem Pσ_apply (σ : X → A) (x x' : X) : M.Pσ σ x x' = M.P x (σ x) x' := rfl

theorem isMarkov_Pσ (σ : X → A) : IsMarkov (M.Pσ σ) :=
  ⟨fun x x' => M.P_nonneg x (σ x) x', fun x => M.P_rowsum x (σ x)⟩

/-- The discount operator (6.17): `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`. -/
def Lσ (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => M.β x (σ x) x' * M.P x (σ x) x'

theorem Lσ_apply (σ : X → A) (x x' : X) : M.Lσ σ x x' = M.β x (σ x) x' * M.P x (σ x) x' := rfl

theorem Lσ_nonneg (σ : X → A) (x x' : X) : 0 ≤ M.Lσ σ x x' :=
  mul_nonneg (M.β_nonneg _ _ _) (M.P_nonneg _ _ _)

/-- `L_σ` is the discount operator (6.4) for `b(x, x') = β(x, σ(x), x')` and `P_σ`. -/
theorem Lσ_eq_discountOp (σ : X → A) :
    M.Lσ σ = discountOp (fun x x' => M.β x (σ x) x') (M.Pσ σ) := rfl

/-- The reward under `σ`: `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : X → A) : X → ℝ := fun x => M.r x (σ x)

/-- The action value, the expression maximised in (6.15):
`r(x, a) + ∑ v(x')β(x, a, x')P(x, a, x')`. -/
def B (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + ∑ x', v x' * M.β x a x' * M.P x a x'

/-- The policy operator (6.16). -/
def Tσ (σ : X → A) (v : X → ℝ) : X → ℝ := fun x => M.B v x (σ x)

theorem Tσ_apply (σ : X → A) (v : X → ℝ) (x : X) :
    M.Tσ σ v x = M.r x (σ x) + ∑ x', v x' * M.β x (σ x) x' * M.P x (σ x) x' := rfl

/-- (6.16) in operator form: `T_σ v = r_σ + L_σ v`. -/
theorem Tσ_eq (σ : X → A) (v : X → ℝ) : M.Tσ σ v = M.rσ σ + M.Lσ σ *ᵥ v := by
  funext x
  simp only [Tσ, B, rσ, Pi.add_apply, mulVec, dotProduct, Lσ_apply]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- The action value is order preserving in `v`. -/
theorem B_mono {v v' : X → ℝ} (hvv' : v ≤ v') (x : X) (a : A) : M.B v x a ≤ M.B v' x a := by
  unfold B
  refine add_le_add le_rfl (sum_le_sum fun x' _ => ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hvv' x') (M.β_nonneg x a x')) (M.P_nonneg x a x')

/-- `T_σ` is order preserving, since `L_σ ≥ 0`. -/
theorem Tσ_monotone (σ : X → A) : Monotone (M.Tσ σ) := fun _ _ h x => M.B_mono h x (σ x)

/-- **Assumption 6.2.1** (p. 193): `ρ(L_σ) < 1` for every feasible policy. -/
def SpectralCondition : Prop := ∀ σ : X → A, M.IsFeasible σ → specRad (M.Lσ σ) < 1

/-- Exercise 6.2.3 (p. 194): Assumption 6.2.1 holds whenever `β(x, a, x')P(x, a, x') ≤ L(x, x')`
on the feasible pairs for some `L` with `ρ(L) < 1`, by monotonicity of the spectral radius
(Exercise 2.2.28). -/
theorem spectralCondition_of_dominated [Nonempty X] {L : Matrix X X ℝ} (hρ : specRad L < 1)
    (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') : M.SpectralCondition :=
  fun σ hσ => (specRad_le_of_le (M.Lσ_nonneg σ) fun x x' => hdom x (σ x) x' (hσ x)).trans_lt hρ

/-- The sufficient condition of p. 193: if `β ≤ b < 1` on the feasible pairs then
Assumption 6.2.1 holds, since `L_σ ≤ bP_σ` and `ρ(bP_σ) = b`. -/
theorem spectralCondition_of_le [Nonempty X] {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hβ : ∀ x a x', a ∈ M.Γ x → M.β x a x' ≤ b) : M.SpectralCondition := by
  intro σ hσ
  have h1 : specRad (M.Lσ σ) ≤ specRad (b • M.Pσ σ) :=
    specRad_le_of_le (M.Lσ_nonneg σ) fun x x' => by
      rw [Lσ_apply, Matrix.smul_apply, smul_eq_mul, Pσ_apply]
      exact mul_le_mul_of_nonneg_right (hβ x (σ x) x' (hσ x)) (M.P_nonneg _ _ _)
  rw [specRad_smul_isMarkov (M.isMarkov_Pσ σ) hb0] at h1
  exact h1.trans_lt hb1

/-! ### Lifetime values (§6.2.1.2) -/

variable [DecidableEq X]

/-- The lifetime value of `σ`, (6.18): `v_σ = (I − L_σ)⁻¹ r_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ

theorem vσ_eq_inv (σ : X → A) : M.vσ σ = (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ := rfl

/-- Exercise 6.2.1 in finite-horizon form: `T_σᵏv = ∑_{t<k} L_σᵗ r_σ + L_σᵏ v`, the `k`-period
discounted value of following `σ` with terminal payoff `v`. -/
theorem iterate_Tσ_eq (σ : X → A) (v : X → ℝ) (k : ℕ) :
    (M.Tσ σ)^[k] v = (∑ t ∈ range k, M.Lσ σ ^ t *ᵥ M.rσ σ) + M.Lσ σ ^ k *ᵥ v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, Tσ_eq, sum_range_succ', pow_zero, one_mulVec, mulVec_add,
      mulVec_sum]
    have h1 : ∀ (w : X → ℝ) (t : ℕ), M.Lσ σ *ᵥ (M.Lσ σ ^ t *ᵥ w) = M.Lσ σ ^ (t + 1) *ᵥ w :=
      fun w t => by rw [mulVec_mulVec, ← pow_succ']
    simp only [h1]
    abel

variable [Nonempty X]

/-- **Lemma 6.2.1** (p. 193), first part: `I − L_σ` is invertible when `ρ(L_σ) < 1`. -/
theorem isUnit_one_sub_Lσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : IsUnit (1 - M.Lσ σ) :=
  (neumann_series _ hρ).1

/-- **Lemma 6.2.1** (p. 193): `v_σ = (I − L_σ)⁻¹ r_σ` is a fixed point of `T_σ`. -/
theorem isFixedPt_vσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : IsFixedPt (M.Tσ σ) (M.vσ σ) := by
  change M.Tσ σ (M.vσ σ) = M.vσ σ
  rw [Tσ_eq, vσ]
  exact (inv_mulVec_eq_add hρ _).symm

/-- **Lemma 6.2.1** (p. 193): `v_σ` is the only fixed point of `T_σ` in `ℝ^X`. -/
theorem eq_vσ_of_isFixedPt {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) {v : X → ℝ}
    (hv : IsFixedPt (M.Tσ σ) v) : v = M.vσ σ := by
  have h := hv.eq
  rw [Tσ_eq] at h
  exact (eq_add_mulVec_iff hρ _ _).1 h.symm

omit [DecidableEq X] in
/-- Lemma 6.2.1 as a unique-existence statement. -/
theorem existsUnique_fixedPt_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) :
    ∃! v : X → ℝ, IsFixedPt (M.Tσ σ) v := by
  classical
  exact
  ⟨M.vσ σ, M.isFixedPt_vσ hρ, fun _ hv => M.eq_vσ_of_isFixedPt hρ hv⟩

/-- Exercise 6.2.1 (p. 194), (6.19) in operator form: `v_σ = ∑ₜ L_σᵗ r_σ`, the expected discounted
sum of rewards along `P_σ` with the discount factors `β(Xₜ₋₁, σ(Xₜ₋₁), Xₜ)`, by Theorem 6.1.1. -/
theorem vσ_eq_tsum {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) :
    M.vσ σ = ∑' t : ℕ, M.Lσ σ ^ t *ᵥ M.rσ σ :=
  inv_mulVec_eq_tsum hρ _

omit [DecidableEq X] [Nonempty X] in
/-- `T_σ` is the affine map of Example 6.1.2. -/
theorem Tσ_eq_affineOp (σ : X → A) : M.Tσ σ = affineOp (M.Lσ σ) (M.rσ σ) := by
  classical
  funext v
  rw [Tσ_eq, affineOp, add_comm]

omit [DecidableEq X] in
/-- Exercise 6.2.2 (p. 194): under `ρ(L_σ) < 1`, `T_σ` is globally stable on `ℝ^X`. -/
theorem globallyStable_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) : GloballyStable (M.Tσ σ) := by
  classical
  rw [Tσ_eq_affineOp]
  exact globallyStable_affineOp hρ _

/-- `T_σᵏ v → v_σ` for every `v`. -/
theorem tendsto_iterate_Tσ {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) (v : X → ℝ) :
    Tendsto (fun k : ℕ => (M.Tσ σ)^[k] v) atTop (𝓝 (M.vσ σ)) := by
  obtain ⟨u', hu', -, hconv⟩ := M.globallyStable_Tσ hρ
  rw [M.eq_vσ_of_isFixedPt hρ hu'] at hconv
  exact hconv v

end SDMDP

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality with state-dependent discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.3–§6.2.1.4
(pp. 194–195).

The Bellman operator (6.21) maximises the action value over `Γ(x)`; a policy is
`v`-greedy if it attains the maximum, equivalently `T_σ v = Tv`; the value
function is `v* = ⋁_σ v_σ` and a policy is optimal if `v_σ = v*`.

**Proposition 6.2.2.** Under Assumption 6.2.1, (i) `v*` is the unique solution of
the Bellman equation, (ii) a policy is optimal iff it is `v*`-greedy, and (iii) an
optimal policy exists. The book defers the proof to §8.2.2. The proof here uses
only that each `T_σ` is order preserving and globally stable (Lemma 6.2.1,
Exercise 6.2.2), not a contraction property of `T`: `v* ≤ Tv*` since
`v_σ = T_σ v_σ ≤ T_σ v* ≤ Tv*`; for a `v*`-greedy `σ`, `v* ≤ T_σ v*` gives
`v* ≤ v_σ`, so `v_σ = v*` and `Tv* = T_σ v* = v*`. Uniqueness: a fixed point `v̄`
is `v_σ` for its greedy `σ`, so `v̄ ≤ v*`, and `T_σ v̄ ≤ v̄` for every `σ` gives
`v_σ ≤ v̄`.

**Algorithms** (§6.2.1.4): the HPI improvement and termination steps of
Algorithm 6.1, OPI with `m = 1` as VFI and `T_σᵐv → v_σ`. The convergence of
VFI, OPI and HPI under Assumption 6.2.1 alone is Chapter 8's; here VFI converges
under the stronger condition of Exercise 6.2.3, `βP ≤ L` with `ρ(L) < 1`, because
`T` then satisfies (6.13) and Proposition 6.1.6 applies.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- If `Tu ≤ u`, `T` is order preserving and `Tᵏu → u'`, then `u' ≤ u`: the dual of
`le_fixedPt_of_le_apply`. -/
theorem fixedPt_le_of_apply_le {X : Type*} {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T)
    {u u' : X → ℝ} (hu : T u ≤ u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) :
    u' ≤ u := by
  have hle : ∀ k : ℕ, T^[k] u ≤ u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (hT ih).trans hu
  intro x
  exact le_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

namespace SDMDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : SDMDP X A)

/-! ### The Bellman operator (6.21) and greedy policies -/

/-- The Bellman operator (6.21):
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')β(x, a, x')P(x, a, x')}`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (M.Γ x).sup' (M.Γ_nonempty x) (M.B v x)

theorem T_apply (v : X → ℝ) (x : X) :
    M.T v x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + ∑ x', v x' * M.β x a x' * M.P x a x' := rfl

theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.B v x a ≤ M.T v x :=
  Finset.le_sup' (M.B v x) ha

/-- `T_σ v ≤ Tv` for every feasible policy. -/
theorem Tσ_le_T (σ : M.Policy) (v : X → ℝ) : M.Tσ σ.1 v ≤ M.T v := fun x => M.B_le_T v (σ.2 x)

/-- `T` is order preserving. -/
theorem T_monotone : Monotone M.T := fun _ _ hvv' x =>
  Finset.sup'_mono_fun fun a _ => M.B_mono hvv' x a

/-- A `v`-greedy policy (p. 194): feasible, and `σ(x)` maximises the right-hand side of (6.21). -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.B v x a ≤ M.B v x (σ x)

/-- A `v`-greedy policy, chosen by maximising the action value in each state. -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : M.greedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- A `v`-greedy policy exists. -/
theorem isGreedy_greedy (v : X → ℝ) : M.IsGreedy v (M.greedy v) :=
  ⟨M.greedy_mem v, fun x a ha =>
    ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : M.Policy := ⟨M.greedy v, M.greedy_mem v⟩

/-- A feasible `σ` is `v`-greedy iff `T_σ v = Tv` (p. 194). -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ.1 ↔ M.Tσ σ.1 v = M.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (M.B_le_T v (σ.2 x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨σ.2, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ] at this
    rw [this]
    exact M.B_le_T v ha

theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) : M.Tσ σ v = M.T v :=
  (M.isGreedy_iff_Tσ_eq_T v ⟨σ, hσ.1⟩).1 hσ

/-! ### The value function and Proposition 6.2.2 -/

variable [DecidableEq X] [DecidableEq A] [Nonempty X]

/-- The value function `v* = ⋁_{σ ∈ Σ} v_σ` (p. 194). -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.vσ σ.1 x

omit [Nonempty X] in
theorem vσ_le_vstar (σ : M.Policy) : M.vσ σ.1 ≤ M.vstar := fun x =>
  Finset.le_sup' (fun σ : M.Policy => M.vσ σ.1 x) (mem_univ σ)

/-- An optimal policy (p. 194): a feasible `σ` with `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := M.IsFeasible σ ∧ M.vσ σ = M.vstar

/-- `v* ≤ Tv*`: for each `σ`, `v_σ = T_σ v_σ ≤ T_σ v* ≤ Tv*`. -/
theorem vstar_le_T_vstar (hM : M.SpectralCondition) : M.vstar ≤ M.T M.vstar := by
  intro x
  refine Finset.sup'_le _ _ fun σ _ => ?_
  calc M.vσ σ.1 x = M.Tσ σ.1 (M.vσ σ.1) x := by rw [(M.isFixedPt_vσ (hM σ.1 σ.2)).eq]
    _ ≤ M.Tσ σ.1 M.vstar x := M.Tσ_monotone σ.1 (M.vσ_le_vstar σ) x
    _ ≤ M.T M.vstar x := M.Tσ_le_T σ M.vstar x

/-- A `v*`-greedy policy is optimal: `v* ≤ T_σ v*` gives `v* ≤ v_σ` by global stability of
`T_σ`. -/
theorem vσ_eq_vstar_of_isGreedy (hM : M.SpectralCondition) {σ : X → A}
    (hσ : M.IsGreedy M.vstar σ) : M.vσ σ = M.vstar := by
  have h2 : M.vstar ≤ M.Tσ σ M.vstar := by
    rw [M.Tσ_eq_T_of_isGreedy hσ]
    exact M.vstar_le_T_vstar hM
  exact le_antisymm (M.vσ_le_vstar ⟨σ, hσ.1⟩)
    (le_fixedPt_of_le_apply (M.Tσ_monotone σ) h2 (M.tendsto_iterate_Tσ (hM σ hσ.1) _))

/-- **Proposition 6.2.2 (i)**, existence half (p. 194): under Assumption 6.2.1, `v*` solves the
Bellman equation. -/
theorem isFixedPt_T_vstar (hM : M.SpectralCondition) : IsFixedPt M.T M.vstar := by
  set σ := M.greedy M.vstar with hσdef
  have hσ : M.IsGreedy M.vstar σ := M.isGreedy_greedy M.vstar
  have h4 := M.vσ_eq_vstar_of_isGreedy hM hσ
  change M.T M.vstar = M.vstar
  calc M.T M.vstar = M.Tσ σ M.vstar := (M.Tσ_eq_T_of_isGreedy hσ).symm
    _ = M.Tσ σ (M.vσ σ) := by rw [h4]
    _ = M.vσ σ := (M.isFixedPt_vσ (hM σ hσ.1)).eq
    _ = M.vstar := h4

/-- **Proposition 6.2.2 (i)**, uniqueness half: `v*` is the only solution of the Bellman equation
in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt (hM : M.SpectralCondition) {v : X → ℝ} (hv : IsFixedPt M.T v) :
    v = M.vstar := by
  -- `v* ≤ v`: `T_σ v ≤ Tv = v` gives `v_σ ≤ v` for every `σ`
  have hle : ∀ σ : M.Policy, M.vσ σ.1 ≤ v := fun σ =>
    fixedPt_le_of_apply_le (M.Tσ_monotone σ.1) ((M.Tσ_le_T σ v).trans_eq hv.eq)
      (M.tendsto_iterate_Tσ (hM σ.1 σ.2) v)
  have h1 : M.vstar ≤ v := fun x => Finset.sup'_le _ _ fun σ _ => hle σ x
  -- `v ≤ v*`: `v` is the value of its own greedy policy
  have hσ := M.isGreedy_greedy v
  have hfix : IsFixedPt (M.Tσ (M.greedy v)) v := by
    rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy hσ]
    exact hv
  have h2 : v ≤ M.vstar := by
    rw [M.eq_vσ_of_isFixedPt (hM _ hσ.1) hfix]
    exact M.vσ_le_vstar ⟨_, hσ.1⟩
  exact le_antisymm h2 h1

/-- The Bellman equation (6.15):
`v*(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v*(x')β(x, a, x')P(x, a, x')}`. -/
theorem bellman_equation (hM : M.SpectralCondition) (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + ∑ x', M.vstar x' * M.β x a x' * M.P x a x' :=
  (congrFun (M.isFixedPt_T_vstar hM).eq x).symm

omit [Nonempty X] in
/-- Optimality is `v_σ ≥ v_σ'` for every feasible `σ'`. -/
theorem isOptimal_iff (σ : X → A) :
    M.IsOptimal σ ↔ M.IsFeasible σ ∧ ∀ (σ' : M.Policy) (x : X), M.vσ σ'.1 x ≤ M.vσ σ x := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun σ' x => ?_⟩
    rw [h]
    exact M.vσ_le_vstar σ' x
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, funext fun x => le_antisymm (M.vσ_le_vstar ⟨σ, hσ⟩ x) ?_⟩
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x

/-- **Proposition 6.2.2 (ii)** (p. 194): a policy is optimal iff it is `v*`-greedy. -/
theorem isOptimal_iff_isGreedy (hM : M.SpectralCondition) (σ : X → A) :
    M.IsOptimal σ ↔ M.IsGreedy M.vstar σ := by
  constructor
  · rintro ⟨hσ, h⟩
    rw [M.isGreedy_iff_Tσ_eq_T M.vstar ⟨σ, hσ⟩]
    -- `T_σ v* = T_σ v_σ = v_σ = v* = Tv*`
    rw [← h, (M.isFixedPt_vσ (hM σ hσ)).eq, h, (M.isFixedPt_T_vstar hM).eq]
  · intro h
    exact ⟨h.1, M.vσ_eq_vstar_of_isGreedy hM h⟩

/-- **Proposition 6.2.2 (iii)** (p. 195): an optimal policy exists, namely any `v*`-greedy one. -/
theorem isOptimal_greedy_vstar (hM : M.SpectralCondition) : M.IsOptimal (M.greedy M.vstar) :=
  (M.isOptimal_iff_isGreedy hM _).2 (M.isGreedy_greedy _)

theorem exists_isOptimal (hM : M.SpectralCondition) : ∃ σ : X → A, M.IsOptimal σ :=
  ⟨_, M.isOptimal_greedy_vstar hM⟩

/-! ### Algorithms (§6.2.1.4) -/

omit [DecidableEq A] [Nonempty X] in
/-- Algorithm 6.1, line 5: the HPI value update is `v_{k+1} = (I − L_{σₖ})⁻¹ r_{σₖ} = v_{σₖ}`. -/
theorem hpi_update_eq_vσ (σ : X → A) : (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ = M.vσ σ := by
  classical
  exact rfl

omit [DecidableEq A] in
/-- HPI (Algorithm 6.1), the improvement step: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_σ'`. -/
theorem vσ_le_vσ_of_isGreedy (hM : M.SpectralCondition) {σ : X → A} (hσ : M.IsFeasible σ)
    {σ' : X → A} (hσ' : M.IsGreedy (M.vσ σ) σ') : M.vσ σ ≤ M.vσ σ' := by
  classical
  have h : M.vσ σ ≤ M.Tσ σ' (M.vσ σ) := by
    rw [M.Tσ_eq_T_of_isGreedy hσ']
    calc M.vσ σ = M.Tσ σ (M.vσ σ) := (M.isFixedPt_vσ (hM σ hσ)).eq.symm
      _ ≤ M.T (M.vσ σ) := M.Tσ_le_T ⟨σ, hσ⟩ _
  exact le_fixedPt_of_le_apply (M.Tσ_monotone σ') h (M.tendsto_iterate_Tσ (hM σ' hσ'.1) _)

/-- HPI (Algorithm 6.1), the termination criterion (line 6): if `σ'` is `v_σ`-greedy and
`v_σ' = v_σ`, then `σ'` is optimal. -/
theorem isOptimal_of_hpi_fixed (hM : M.SpectralCondition) {σ σ' : X → A}
    (hσ' : M.IsGreedy (M.vσ σ) σ') (heq : M.vσ σ' = M.vσ σ) : M.IsOptimal σ' := by
  have hfix : IsFixedPt M.T (M.vσ σ) := by
    rw [IsFixedPt, ← M.Tσ_eq_T_of_isGreedy hσ', ← heq]
    exact (M.isFixedPt_vσ (hM σ' hσ'.1)).eq
  refine ⟨hσ'.1, ?_⟩
  rw [heq]
  exact M.eq_vstar_of_isFixedPt hM hfix

omit [DecidableEq X] [DecidableEq A] [Nonempty X] in
/-- OPI with `m = 1` is VFI (p. 195): for a `v`-greedy `σ`, `T_σ v = Tv`. -/
theorem opi_one_step_eq_vfi {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (M.Tσ σ)^[1] v = M.T v := by
  rw [iterate_one]
  exact M.Tσ_eq_T_of_isGreedy hσ

omit [DecidableEq A] in
/-- OPI approximates HPI as `m → ∞`: `T_σᵐ v → v_σ` (p. 195). -/
theorem tendsto_opi_inner {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) (v : X → ℝ) :
    Tendsto (fun m : ℕ => (M.Tσ σ)^[m] v) atTop (𝓝 (M.vσ σ)) :=
  M.tendsto_iterate_Tσ hρ v

/-! ### Value function iteration under a dominating discount operator -/

omit [DecidableEq X] [DecidableEq A] [Nonempty X] in
/-- Under the condition (6.20) of Exercise 6.2.3, `T` satisfies (6.13): `|Tv − Tw| ≤ L|v − w|`. -/
theorem abs_T_sub_le_of_dominated {L : Matrix X X ℝ}
    (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') (v w : X → ℝ) (x : X) :
    |M.T v x - M.T w x| ≤ (L *ᵥ fun y => |v y - w y|) x := by
  rw [T_apply, T_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a ha => ?_)
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  calc |∑ x', (v x' * M.β x a x' * M.P x a x' - w x' * M.β x a x' * M.P x a x')|
      ≤ ∑ x', |v x' - w x'| * (M.β x a x' * M.P x a x') := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => le_of_eq ?_)
        rw [show v x' * M.β x a x' * M.P x a x' - w x' * M.β x a x' * M.P x a x' =
          (v x' - w x') * (M.β x a x' * M.P x a x') by ring, abs_mul,
          abs_of_nonneg (mul_nonneg (M.β_nonneg x a x') (M.P_nonneg x a x'))]
    _ ≤ ∑ x', |v x' - w x'| * L x x' := sum_le_sum fun x' _ =>
        mul_le_mul_of_nonneg_left (hdom x a x' ha) (abs_nonneg _)
    _ = (L *ᵥ fun y => |v y - w y|) x := by
        simp only [mulVec, dotProduct]
        exact sum_congr rfl fun x' _ => mul_comm _ _

omit [DecidableEq X] [DecidableEq A] in
/-- Value function iteration under (6.20): `T` is globally stable on `ℝ^X`, by
Proposition 6.1.6 and Theorem 6.1.5. -/
theorem globallyStable_T_of_dominated {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') :
    GloballyStable M.T := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le
    (Set.mapsTo_univ M.T Set.univ) hL hρ fun v _ w _ x => M.abs_T_sub_le_of_dominated hdom v w x
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Value function iteration under (6.20): `Tᵏv → v*` for every `v`. -/
theorem tendsto_iterate_T_of_dominated {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x')
    (v : X → ℝ) : Tendsto (fun k : ℕ => M.T^[k] v) atTop (𝓝 M.vstar) := by
  obtain ⟨u', hu', -, hconv⟩ := M.globallyStable_T_of_dominated hL hρ hdom
  rw [M.eq_vstar_of_isFixedPt (M.spectralCondition_of_dominated hρ hdom) hu'] at hconv
  exact hconv v

end SDMDP

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exogenous discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.5 (pp. 195–196).

The state is `(y, z)` with `y` endogenous and `z` exogenous and `Q`-Markov; the
discount factor `β(z)` depends on the exogenous component only; `R(y, a, y')` is
a stochastic kernel for the endogenous component. The Bellman equation is (6.22),
greedy policies are (6.23), and the model is the MDP with state-dependent
discounting on `Y × Z` with `P((y, z), a, (y', z')) = Q(z, z')R(y, a, y')`.

* Proposition 6.2.3 (Exercise 6.2.4): if `ρ(L_Z) < 1` for
  `L_Z(z, z') = β(z)Q(z, z')`, then Assumption 6.2.1 holds and so do all the
  conclusions of Proposition 6.2.2. For each policy `L_σ` has the product form of
  Lemma 6.1.3 with a kernel on `Y` that depends on `z` through `σ(y, z)`, which is
  why that lemma is proved here in the general form.
* Value function iteration converges in this model: `|Tv − Tw|(y, z)` is bounded
  by `(L_Z g)(z)` where `g(z) = max_y |v − w|(y, z)`, so
  `‖Tᵏv − Tᵏw‖ ≤ ‖L_Zᵏ‖‖v − w‖` and `T` is eventually contracting. The book
  defers the convergence of VFI to Chapter 8.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The exogenous discount model (§6.2.1.5): primitives (i)–(v) of p. 195–196. -/
structure Exogenous (Y Z A : Type*) [Fintype Y] [Fintype Z] [Fintype A] where
  Γ : Y × Z → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  β : Z → ℝ
  β_nonneg : ∀ z, 0 ≤ β z
  r : Y → A → ℝ
  Q : Matrix Z Z ℝ
  Q_markov : IsMarkov Q
  R : Y → A → Y → ℝ
  R_nonneg : ∀ y a y', 0 ≤ R y a y'
  R_rowsum : ∀ y a, ∑ y', R y a y' = 1

namespace Exogenous

variable {Y Z A : Type*} [Fintype Y] [Fintype Z] [Fintype A] (E : Exogenous Y Z A)

/-- The exogenous discount model as an MDP with state-dependent discounting on `Y × Z`
(p. 196): `P(x, a, x') = Q(z, z')R(y, a, y')` and `β(x, a, x') = β(z)`. -/
def toSDMDP : SDMDP (Y × Z) A where
  Γ := E.Γ
  Γ_nonempty := E.Γ_nonempty
  r := fun x a => E.r x.1 a
  β := fun x _ _ => E.β x.2
  β_nonneg := fun x _ _ => E.β_nonneg x.2
  P := fun x a x' => E.Q x.2 x'.2 * E.R x.1 a x'.1
  P_nonneg := fun _ _ _ => mul_nonneg (E.Q_markov.nonneg _ _) (E.R_nonneg _ _ _)
  P_rowsum := fun x a => by
    rw [Fintype.sum_prod_type]
    simp only [← sum_mul, E.Q_markov.rowsum, one_mul, E.R_rowsum]

/-- The exogenous discount operator `L_Z(z, z') = β(z)Q(z, z')` of Proposition 6.2.3. -/
def LZ : Matrix Z Z ℝ := discountOp (fun z _ => E.β z) E.Q

theorem LZ_apply (z z' : Z) : E.LZ z z' = E.β z * E.Q z z' := rfl

theorem LZ_nonneg (z z' : Z) : 0 ≤ E.LZ z z' := mul_nonneg (E.β_nonneg z) (E.Q_markov.nonneg z z')

/-- `L_σ` has the product form of Lemma 6.1.3, with the kernel `R(y, σ(y, z), y')` on `Y`. -/
theorem Lσ_eq (σ : Y × Z → A) :
    E.toSDMDP.Lσ σ = productDiscountOp (fun z _ => E.β z) E.Q fun x y' => E.R x.1 (σ x) y' := by
  ext x x'
  change E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 (σ x) x'.1) = E.β x.2 * E.Q x.2 x'.2 * E.R x.1 (σ x) x'.1
  ring

/-- `ρ(L_σ) = ρ(L_Z)` for every policy, by Lemma 6.1.3. -/
theorem specRad_Lσ [Nonempty Y] [Nonempty Z] (σ : Y × Z → A) :
    specRad (E.toSDMDP.Lσ σ) = specRad E.LZ := by
  rw [Lσ_eq]
  exact specRad_productDiscountOp (fun z _ => E.β_nonneg z) E.Q_markov.nonneg
    (fun x y' => E.R_nonneg _ _ _) fun x => E.R_rowsum _ _

/-- **Proposition 6.2.3** (p. 196), Exercise 6.2.4: if `ρ(L_Z) < 1` then Assumption 6.2.1 holds
for the exogenous discount model. -/
theorem spectralCondition [Nonempty Y] [Nonempty Z] (hρ : specRad E.LZ < 1) :
    E.toSDMDP.SpectralCondition := fun σ _ => by
  rw [E.specRad_Lσ σ]
  exact hρ

variable [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Y] [Nonempty Z]

/-- Proposition 6.2.3: the Bellman equation (6.22),
`v*(y, z) = max_{a ∈ Γ(y, z)} {r(y, a) + β(z) ∑_{y', z'} v*(y', z')Q(z, z')R(y, a, y')}`. -/
theorem bellman_equation (hρ : specRad E.LZ < 1) (y : Y) (z : Z) :
    E.toSDMDP.vstar (y, z) = (E.Γ (y, z)).sup' (E.Γ_nonempty _) fun a =>
      E.r y a + E.β z * ∑ x' : Y × Z, E.toSDMDP.vstar x' * E.Q z x'.2 * E.R y a x'.1 := by
  rw [E.toSDMDP.bellman_equation (E.spectralCondition hρ)]
  refine Finset.sup'_congr _ rfl fun a _ => ?_
  change E.r y a + ∑ x', E.toSDMDP.vstar x' * E.β z * (E.Q z x'.2 * E.R y a x'.1) = _
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- Proposition 6.2.3: `v*` is the unique solution of (6.22). -/
theorem eq_vstar_of_isFixedPt (hρ : specRad E.LZ < 1) {v : Y × Z → ℝ}
    (hv : IsFixedPt E.toSDMDP.T v) : v = E.toSDMDP.vstar :=
  E.toSDMDP.eq_vstar_of_isFixedPt (E.spectralCondition hρ) hv

/-- Proposition 6.2.3: a policy is optimal iff it is `v*`-greedy in the sense of (6.23). -/
theorem isOptimal_iff_isGreedy (hρ : specRad E.LZ < 1) (σ : Y × Z → A) :
    E.toSDMDP.IsOptimal σ ↔ E.toSDMDP.IsGreedy E.toSDMDP.vstar σ :=
  E.toSDMDP.isOptimal_iff_isGreedy (E.spectralCondition hρ) σ

/-- Proposition 6.2.3: an optimal policy exists. -/
theorem exists_isOptimal (hρ : specRad E.LZ < 1) : ∃ σ : Y × Z → A, E.toSDMDP.IsOptimal σ :=
  E.toSDMDP.exists_isOptimal (E.spectralCondition hρ)

/-! ### Value function iteration -/

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- `g(z) = max_y |u(y, z)|`. -/
noncomputable def colMax (u : Y × Z → ℝ) : Z → ℝ := fun z =>
  univ.sup' univ_nonempty fun y => |u (y, z)|

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] [Fintype Z] in
theorem abs_le_colMax (u : Y × Z → ℝ) (x : Y × Z) : |u x| ≤ colMax u x.2 := by
  classical
  exact
  Finset.le_sup' (fun y => |u (y, x.2)|) (mem_univ x.1)

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] [Fintype Z] in
theorem colMax_nonneg (u : Y × Z → ℝ) (z : Z) : 0 ≤ colMax u z := by
  classical
  exact
  (abs_nonneg _).trans (abs_le_colMax u (Classical.arbitrary Y, z))

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- `‖u‖_∞ = ‖g‖_∞`. -/
theorem norm_eq_norm_colMax (u : Y × Z → ℝ) : ‖u‖ = ‖colMax u‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    rw [Real.norm_eq_abs]
    refine (abs_le_colMax u x).trans ?_
    have := norm_le_pi_norm (colMax u) x.2
    rwa [Real.norm_eq_abs, abs_of_nonneg (colMax_nonneg u _)] at this
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (colMax_nonneg u z)]
    refine Finset.sup'_le _ _ fun y _ => ?_
    have := norm_le_pi_norm u (y, z)
    rwa [Real.norm_eq_abs] at this

omit [DecidableEq Y] [DecidableEq Z] [DecidableEq A] [Nonempty Z] in
/-- The one-step bound: `|Tv − Tw|(y, z) ≤ (L_Z g)(z)` with `g = max_y |v − w|`. -/
theorem abs_T_sub_le (v w : Y × Z → ℝ) (x : Y × Z) :
    |E.toSDMDP.T v x - E.toSDMDP.T w x| ≤ (E.LZ *ᵥ colMax (v - w)) x.2 := by
  rw [SDMDP.T_apply, SDMDP.T_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
  change |E.r x.1 a + ∑ x', v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
    (E.r x.1 a + ∑ x', w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1))| ≤ _
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  have hQ := E.Q_markov.nonneg
  calc |∑ x' : Y × Z, (v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
          w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1))|
      ≤ ∑ x' : Y × Z, colMax (v - w) x'.2 * (E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => ?_)
        rw [show v x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) -
            w x' * E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1) =
            (v - w) x' * (E.β x.2 * (E.Q x.2 x'.2 * E.R x.1 a x'.1)) by
              simp only [Pi.sub_apply]; ring, abs_mul,
          abs_of_nonneg (mul_nonneg (E.β_nonneg _) (mul_nonneg (hQ _ _) (E.R_nonneg _ _ _)))]
        exact mul_le_mul_of_nonneg_right (abs_le_colMax (v - w) x')
          (mul_nonneg (E.β_nonneg _) (mul_nonneg (hQ _ _) (E.R_nonneg _ _ _)))
    _ = (E.LZ *ᵥ colMax (v - w)) x.2 := by
        rw [Fintype.sum_prod_type, sum_comm]
        simp only [mulVec, dotProduct, LZ_apply]
        refine sum_congr rfl fun z' _ => ?_
        have h : ∀ y', colMax (v - w) z' * (E.β x.2 * (E.Q x.2 z' * E.R x.1 a y')) =
            E.β x.2 * E.Q x.2 z' * colMax (v - w) z' * E.R x.1 a y' := fun y' => by ring
        simp only [h]
        rw [← mul_sum, E.R_rowsum, mul_one]

omit [DecidableEq Y] [DecidableEq A] [Nonempty Z] in
/-- Iterating: `max_y |Tᵏv − Tᵏw|(y, z) ≤ (L_Zᵏ g)(z)`. -/
theorem colMax_iterate_sub_le (v w : Y × Z → ℝ) (k : ℕ) :
    colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w) ≤ E.LZ ^ k *ᵥ colMax (v - w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro z
    rw [iterate_succ_apply', iterate_succ_apply']
    refine Finset.sup'_le _ _ fun y _ => ?_
    refine (E.abs_T_sub_le _ _ (y, z)).trans ?_
    have := mulVec_le_mulVec_of_nonneg E.LZ_nonneg ih z
    rwa [mulVec_mulVec, ← pow_succ'] at this

omit [DecidableEq Y] [DecidableEq A] [Nonempty Z] in
/-- `‖Tᵏv − Tᵏw‖_∞ ≤ ‖L_Zᵏ‖‖v − w‖_∞`. -/
theorem norm_iterate_T_sub_le (v w : Y × Z → ℝ) (k : ℕ) :
    ‖E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w‖ ≤ ‖E.LZ ^ k‖ * ‖v - w‖ := by
  rw [norm_eq_norm_colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w), norm_eq_norm_colMax (v - w)]
  calc ‖colMax (E.toSDMDP.T^[k] v - E.toSDMDP.T^[k] w)‖ ≤ ‖E.LZ ^ k *ᵥ colMax (v - w)‖ :=
        norm_le_norm_of_abs_le_fun
          (fun z => sum_nonneg fun z' _ =>
            mul_nonneg (pow_nonneg_entries E.LZ_nonneg k z z') (colMax_nonneg _ _))
          (fun z => by
            rw [abs_of_nonneg (colMax_nonneg _ _)]
            exact E.colMax_iterate_sub_le v w k z)
    _ ≤ ‖E.LZ ^ k‖ * ‖colMax (v - w)‖ := Matrix.linfty_opNorm_mulVec _ _

omit [DecidableEq Y] [DecidableEq A] in
/-- Under `ρ(L_Z) < 1` the Bellman operator of the exogenous discount model is eventually
contracting under the supremum norm. -/
theorem exists_isContractionOn_iterate_T (hρ : specRad E.LZ < 1) :
    ∃ k : ℕ, 0 < k ∧ IsContractionOn (E.toSDMDP.T^[k]) Set.univ ‖E.LZ ^ k‖ := by
  obtain ⟨k, hk1, hk0⟩ := (((tendsto_norm_pow_zero E.LZ hρ).eventually (gt_mem_nhds one_pos)).and
    (eventually_gt_atTop 0)).exists
  exact ⟨k, hk0, Set.mapsTo_univ _ _, norm_nonneg _, hk1, fun v _ w _ =>
    E.norm_iterate_T_sub_le v w k⟩

omit [DecidableEq Y] [DecidableEq A] [DecidableEq Z] in
/-- Value function iteration converges in the exogenous discount model: `T` is globally stable
on `ℝ^{Y × Z}` when `ρ(L_Z) < 1`, by Theorem 6.1.5. -/
theorem globallyStable_T (hρ : specRad E.LZ < 1) : GloballyStable E.toSDMDP.T := by
  classical
  obtain ⟨k, hk, hc⟩ := E.exists_isContractionOn_iterate_T hρ
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- `Tᵏv → v*` for every `v` when `ρ(L_Z) < 1`. -/
theorem tendsto_iterate_T (hρ : specRad E.LZ < 1) (v : Y × Z → ℝ) :
    Tendsto (fun k : ℕ => E.toSDMDP.T^[k] v) atTop (𝓝 E.toSDMDP.vstar) := by
  obtain ⟨u', hu', -, hconv⟩ := E.globallyStable_T hρ
  rw [E.eq_vstar_of_isFixedPt hρ hu'] at hconv
  exact hconv v

end Exogenous

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Inventory management with time-varying interest rates

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.2 (pp. 197–199).

The inventory model of §5.2.1 (restated from the `FiniteStates/MarkovDecisionProcesses`
project: states and orders in `{0, …, K}`, geometric demand `φ(d) = p(1 − p)ᵈ`,
update `f(y, a, d) = (y − d) ∨ 0 + a`, reward (5.8)) with the constant discount
factor replaced by `β(Zₜ)` for an exogenous `Q`-Markov process. It is an instance of
the exogenous discount model with `R(y, a, y') = P{f(y, a, D) = y'}`, (6.25)–(6.26),
so by Proposition 6.2.3 all the optimality results hold when `ρ(L_Z) < 1` for
`L_Z(z, z') = β(z)Q(z, z')`, the test performed by Listing 6.1.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

/-- The inventory update (5.6): `f(x, a, d) = (x − d) ∨ 0 + a`, clamped at the capacity `K` so that
the kernel is a distribution for every pair, feasible or not. -/
def inventoryNext (K x a d : ℕ) : ℕ := min ((x - d) + a) K

theorem inventoryNext_lt (K x a d : ℕ) : inventoryNext K x a d < K + 1 := by
  unfold inventoryNext
  omega

/-- The geometric demand distribution `φ(d) = p(1 − p)ᵈ`. -/
noncomputable def geomPmf (p : ℝ) (d : ℕ) : ℝ := p * (1 - p) ^ d

theorem geomPmf_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) : 0 < geomPmf p d :=
  mul_pos hp0 (pow_pos (by linarith) d)

theorem summable_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Summable (geomPmf p) :=
  (summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left p

theorem tsum_geomPmf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∑' d, geomPmf p d = 1 := by
  unfold geomPmf
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by linarith) (by linarith)]
  have h1 : (1 : ℝ) - (1 - p) = p := by ring
  rw [h1, inv_eq_one_div, mul_one_div, div_self hp0.ne']

/-- The inventory kernel (5.9), `R(y, a, y') = P{f(y, a, D) = y'}` for `D ∼ φ`. -/
noncomputable def inventoryKernel (K : ℕ) (p : ℝ) (x a x' : Fin (K + 1)) : ℝ :=
  ∑' d : ℕ, if inventoryNext K x a d = x' then geomPmf p d else 0

theorem summable_inventoryTerm (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    Summable fun d : ℕ => if inventoryNext K x a d = x' then geomPmf p d else 0 :=
  (summable_geomPmf hp0 hp1).of_nonneg_of_le
    (fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl])
    (fun d => by split_ifs <;> [exact le_rfl; exact (geomPmf_pos hp0 hp1 d).le])

theorem inventoryKernel_nonneg (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a x' : Fin (K + 1)) :
    0 ≤ inventoryKernel K p x a x' :=
  tsum_nonneg fun d => by split_ifs <;> [exact (geomPmf_pos hp0 hp1 d).le; exact le_rfl]

/-- `∑_{y'} v(y')R(y, a, y') = ∑_d φ(d) v(f(y, a, d))`: the kernel form (6.26) of the expectation
equals the shock form (6.25). -/
theorem sum_mul_inventoryKernel (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (v : Fin (K + 1) → ℝ) (x a : Fin (K + 1)) :
    ∑ x', v x' * inventoryKernel K p x a x' =
      ∑' d : ℕ, geomPmf p d * v ⟨inventoryNext K x a d, inventoryNext_lt K x a d⟩ := by
  unfold inventoryKernel
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun x' _ => (summable_inventoryTerm K hp0 hp1 x a x').mul_left _]
  refine tsum_congr fun d => ?_
  rw [Finset.sum_eq_single (⟨inventoryNext K x a d, inventoryNext_lt K x a d⟩ : Fin (K + 1))]
  · simp [mul_comm]
  · intro i _ hi
    have : ¬ (inventoryNext K x a d = (i : ℕ)) := fun h => hi (Fin.ext h.symm)
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

theorem inventoryKernel_rowsum (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x a : Fin (K + 1)) :
    ∑ x', inventoryKernel K p x a x' = 1 := by
  have := sum_mul_inventoryKernel K hp0 hp1 (fun _ => 1) x a
  simp only [one_mul, mul_one] at this
  rw [this, tsum_geomPmf hp0 hp1]

/-- The expected revenue `∑_d (x ∧ d)φ(d)` of (5.8). -/
noncomputable def expectedRevenue (p : ℝ) (x : ℕ) : ℝ := ∑' d : ℕ, min (x : ℝ) d * geomPmf p d

/-- The inventory reward (5.8): `r(x, a) = ∑_d (x ∧ d)φ(d) − ca − κ·1{a > 0}`. -/
noncomputable def inventoryReward (p c κ : ℝ) (x a : ℕ) : ℝ :=
  expectedRevenue p x - c * a - κ * (if 0 < a then 1 else 0)

variable {Z : Type*} [Fintype Z]

/-- The inventory model with time-varying interest rates (§6.2.2), as an exogenous discount
model: inventory `y ∈ {0, …, K}`, orders `Γ(y, z) = {0, …, K − y}`, discount factor `β(z)` driven
by a `Q`-Markov exogenous state. -/
noncomputable def inventorySDD (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) :
    Exogenous (Fin (K + 1)) Z (Fin (K + 1)) where
  Γ := fun x => univ.filter fun a => (a : ℕ) ≤ K - x.1
  Γ_nonempty := fun _ => ⟨⟨0, by omega⟩, by simp⟩
  β := β
  β_nonneg := hβ
  r := fun y a => inventoryReward p c κ y a
  Q := Q
  Q_markov := hQ
  R := inventoryKernel K p
  R_nonneg := inventoryKernel_nonneg K hp0 hp1
  R_rowsum := inventoryKernel_rowsum K hp0 hp1

/-- The feasible orders: `a ∈ Γ(y, z) ⟺ a ≤ K − y`. -/
theorem inventorySDD_mem_Γ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (y a : Fin (K + 1)) (z : Z) :
    a ∈ (inventorySDD K hp0 hp1 c κ β hβ hQ).Γ (y, z) ↔ (a : ℕ) ≤ K - y := by
  simp [inventorySDD]

/-- (6.26): the action value is
`B((y, z), a, v) = r(y, a) + β(z) ∑_{y', z'} v(y', z')Q(z, z')R(y, a, y')`. -/
theorem inventorySDD_B_apply (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (v : Fin (K + 1) × Z → ℝ)
    (y a : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.B v (y, z) a =
      inventoryReward p c κ y a + β z * ∑ x', v x' * Q z x'.2 * inventoryKernel K p y a x'.1 := by
  change inventoryReward p c κ y a +
    ∑ x', v x' * β z * (Q z x'.2 * inventoryKernel K p y a x'.1) = _
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- (6.25): the action value in terms of the demand shock,
`B((y, z), a, v) = r(y, a) + β(z) ∑_{d, z'} v(f(y, a, d), z')φ(d)Q(z, z')`. -/
theorem inventorySDD_B_apply' (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) (v : Fin (K + 1) × Z → ℝ)
    (y a : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.B v (y, z) a =
      inventoryReward p c κ y a + β z * ∑ z',
        (∑' d : ℕ, geomPmf p d * v (⟨inventoryNext K y a d, inventoryNext_lt K y a d⟩, z')) *
          Q z z' := by
  rw [inventorySDD_B_apply, Fintype.sum_prod_type, sum_comm]
  congr 2
  refine sum_congr rfl fun z' _ => ?_
  rw [← sum_mul_inventoryKernel K hp0 hp1 (fun y' => v (y', z')) y a, sum_mul]
  exact sum_congr rfl fun y' _ => by ring

/-- The exogenous discount operator of the inventory model: `L(z, z') = β(z)Q(z, z')`, whose
spectral radius Listing 6.1 tests. -/
theorem inventorySDD_LZ (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).LZ = discountOp (fun z _ => β z) Q := rfl

variable [DecidableEq Z] [Nonempty Z]

/-- §6.2.2, p. 198: if `ρ(L) < 1` for `L(z, z') = β(z)Q(z, z')`, all the standard optimality
results hold for the inventory model: `v*` is the unique solution of the Bellman equation (6.24)
with (6.25), a policy is optimal iff it is `v*`-greedy, and an optimal policy exists. -/
theorem inventorySDD_optimality (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ)
    (β : Z → ℝ) (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q)
    (hρ : specRad (discountOp (fun z _ => β z) Q) < 1) :
    let M := (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP
    IsFixedPt M.T M.vstar ∧ (∀ v, IsFixedPt M.T v → v = M.vstar) ∧
      (∀ σ, M.IsOptimal σ ↔ M.IsGreedy M.vstar σ) ∧ ∃ σ, M.IsOptimal σ := by
  intro M
  have hM := (inventorySDD K hp0 hp1 c κ β hβ hQ).spectralCondition hρ
  exact ⟨M.isFixedPt_T_vstar hM, fun v hv => M.eq_vstar_of_isFixedPt hM hv,
    fun σ => M.isOptimal_iff_isGreedy hM σ, M.exists_isOptimal hM⟩

/-- The Bellman equation of the inventory model with time-varying discounting, (6.24) with (6.25):
`v*(y, z) = max_{a ≤ K − y} {r(y, a) + β(z) ∑_{d, z'} v*(f(y, a, d), z')φ(d)Q(z, z')}`. -/
theorem inventorySDD_bellman (K : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c κ : ℝ) (β : Z → ℝ)
    (hβ : ∀ z, 0 ≤ β z) {Q : Matrix Z Z ℝ} (hQ : IsMarkov Q)
    (hρ : specRad (discountOp (fun z _ => β z) Q) < 1) (y : Fin (K + 1)) (z : Z) :
    (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.vstar (y, z) =
      (univ.filter fun a : Fin (K + 1) => (a : ℕ) ≤ K - y).sup'
        ((inventorySDD K hp0 hp1 c κ β hβ hQ).Γ_nonempty (y, z)) fun a =>
          inventoryReward p c κ y a + β z * ∑ z', (∑' d : ℕ, geomPmf p d *
            (inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.vstar
              (⟨inventoryNext K y a d, inventoryNext_lt K y a d⟩, z')) * Q z z' := by
  rw [(inventorySDD K hp0 hp1 c κ β hβ hQ).toSDMDP.bellman_equation
    ((inventorySDD K hp0 hp1 c κ β hβ hQ).spectralCondition hρ)]
  exact Finset.sup'_congr _ rfl fun a _ => inventorySDD_B_apply' K hp0 hp1 c κ β hβ hQ _ y a z

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset pricing in a Markov environment

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.3.1–§6.3.2
(pp. 199–209).

* Markov pricing (6.32): with `Mₜ₊₁ = m(Xₜ, Xₜ₊₁)` and `Gₜ₊₁ = g(Xₜ, Xₜ₊₁)`, the
  price of a one-period payoff is `π(x) = ∑ m(x, x')g(x, x')P(x, x')`.
* An ex-dividend claim on `Dₜ = d(Xₜ)` satisfies (6.34)–(6.35), `π = Aπ + Ad`
  with the Arrow–Debreu discount operator `A(x, x') = m(x, x')P(x, x')`; when
  `ρ(A) < 1` the equilibrium price is `π* = (I − A)⁻¹Ad = ∑_{k≥1} Aᵏd`.
  Exercise 6.3.1: `ρ(A) < 1` is necessary and sufficient for a unique positive
  solution when `m, d ≫ 0` (Lemma 6.1.4). Exercise 6.3.2: the risk-neutral case
  `m ≡ β` needs `β < 1`. Exercise 6.3.3: `π*` satisfies the pricing equation.
  Exercise 6.3.4 and §6.3.1.6: a cum-dividend claim satisfies `π = d + Aπ`, so
  `π = (I − A)⁻¹d = ∑_{k≥0} Aᵏd`, the forward sum, and exceeds the ex-dividend
  price by `d`.
* Nonstationary dividends (§6.3.2): Exercise 6.3.5 in finite form, the
  price-dividend equation (6.39) with the operator (6.40), and Exercise 6.3.6:
  `v* = (I − A)⁻¹A𝟙 = ∑_{t≥1} Aᵗ𝟙`. Exercise 6.3.7: with Gaussian shocks and the
  Lucas SDF, `A(x, x') = β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)P(x, x')`,
  by the Gaussian moment generating function.
-/

open Matrix Finset Filter Topology Function MeasureTheory ProbabilityTheory

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Markov pricing (§6.3.1.4) -/

omit [DecidableEq X] in
/-- The Markov pricing equation (6.32): the price of the payoff `g(Xₜ, Xₜ₊₁)` under the SDF
`m(Xₜ, Xₜ₊₁)` in state `x` is `∑ m(x, x')g(x, x')P(x, x')`. -/
def markovPrice (m g : X → X → ℝ) (P : Matrix X X ℝ) (x : X) : ℝ :=
  ∑ x', m x x' * g x x' * P x x'

omit [Fintype X] [DecidableEq X] in
/-- The Arrow–Debreu discount operator (6.35), Remark 6.3.1: `A(x, x') = m(x, x')P(x, x')`, the
discount operator (6.4) with `b = m`. -/
def adOp (m : X → X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ := discountOp m P

omit [Fintype X] [DecidableEq X] in
theorem adOp_apply (m : X → X → ℝ) (P : Matrix X X ℝ) (x x' : X) :
    adOp m P x x' = m x x' * P x x' := rfl

omit [DecidableEq X] in
/-- Risk-neutral pricing (6.27): a payoff `g(x')` priced with `m ≡ β` is `β(Pg)(x)`. -/
theorem markovPrice_const (β : ℝ) (g : X → ℝ) (P : Matrix X X ℝ) (x : X) :
    markovPrice (fun _ _ => β) (fun _ x' => g x') P x = β * (P *ᵥ g) x := by
  simp only [markovPrice, mulVec, dotProduct, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

omit [DecidableEq X] in
/-- The payoff `g(x')` of a claim on next period's state is priced by `(Ag)(x)`: Remark 6.3.1,
`A` applies one period of discounting. -/
theorem markovPrice_eq_adOp_mulVec (m : X → X → ℝ) (g : X → ℝ) (P : Matrix X X ℝ) (x : X) :
    markovPrice m (fun _ x' => g x') P x = (adOp m P *ᵥ g) x := by
  simp only [markovPrice, mulVec, dotProduct, adOp_apply]
  exact sum_congr rfl fun x' _ => by ring

/-! ### Pricing a stationary dividend stream (§6.3.1.5) -/

variable [Nonempty X]

/-- The ex-dividend pricing equation (6.34)–(6.35): `π = A(π + d)`, i.e. `π = Aπ + Ad`. -/
def IsExDivPrice (A : Matrix X X ℝ) (d π : X → ℝ) : Prop := π = A *ᵥ π + A *ᵥ d

/-- The equilibrium ex-dividend price function `π* = (I − A)⁻¹Ad` (p. 206). -/
noncomputable def exDivPrice (A : Matrix X X ℝ) (d : X → ℝ) : X → ℝ := (1 - A)⁻¹ *ᵥ (A *ᵥ d)

/-- Exercise 6.3.3 (p. 206): `π*` solves the pricing equation (6.33)–(6.34). -/
theorem isExDivPrice_exDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    IsExDivPrice A d (exDivPrice A d) := by
  unfold IsExDivPrice exDivPrice
  rw [add_comm]
  exact inv_mulVec_eq_add hρ _

/-- `π*` is the unique solution of (6.34) when `ρ(A) < 1` (p. 206). -/
theorem eq_exDivPrice_of_isExDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) {d π : X → ℝ}
    (hπ : IsExDivPrice A d π) : π = exDivPrice A d :=
  (eq_add_mulVec_iff hρ (A *ᵥ d) π).1 (hπ.trans (add_comm _ _))

/-- `π* = ∑_{k≥1} Aᵏd` (p. 206): the ex-dividend price is the discounted value of all future
dividends, by Theorem 6.1.1. -/
theorem exDivPrice_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    exDivPrice A d = ∑' k : ℕ, A ^ (k + 1) *ᵥ d := by
  unfold exDivPrice
  rw [inv_mulVec_eq_tsum hρ]
  exact tsum_congr fun k => by rw [mulVec_mulVec, ← pow_succ]

omit [DecidableEq X] [Nonempty X] in
/-- If `P` is Markov and `m, d ≫ 0` then `Ad ≫ 0`. -/
theorem adOp_mulVec_pos {m : X → X → ℝ} (hm : ∀ x x', 0 < m x x') {P : Matrix X X ℝ}
    (hP : IsMarkov P) {d : X → ℝ} (hd : ∀ x, 0 < d x) (x : X) : 0 < (adOp m P *ᵥ d) x := by
  classical
  obtain ⟨x', hx'⟩ : ∃ x', 0 < P x x' := by
    by_contra h
    have h0 : ∑ x', P x x' = 0 :=
      sum_eq_zero fun x' _ => le_antisymm (not_lt.1 fun hx => h ⟨x', hx⟩) (hP.nonneg x x')
    rw [hP.rowsum] at h0
    exact one_ne_zero h0
  exact sum_pos' (fun y _ => mul_nonneg (mul_nonneg (hm x y).le (hP.nonneg x y)) (hd y).le)
    ⟨x', mem_univ x', mul_pos (mul_pos (hm x x') hx') (hd x')⟩

omit [DecidableEq X] in
/-- Exercise 6.3.1 (p. 206): when `m, d ≫ 0` and `P` is Markov, `ρ(A) < 1` is necessary and
sufficient for (6.34) to have a unique solution in `(0, ∞)^X`, by Lemma 6.1.4 with `h = Ad ≫ 0`. -/
theorem specRad_lt_one_iff_existsUnique_pos_exDivPrice {m : X → X → ℝ} (hm : ∀ x x', 0 < m x x')
    {P : Matrix X X ℝ} (hP : IsMarkov P) {d : X → ℝ} (hd : ∀ x, 0 < d x) :
    specRad (adOp m P) < 1 ↔ ∃! π : X → ℝ, (∀ x, 0 < π x) ∧ IsExDivPrice (adOp m P) d π := by
  classical
  have h := specRad_lt_one_iff_existsUnique_pos (L := adOp m P)
    (discountOp_nonneg (fun x x' => (hm x x').le) hP.nonneg) (adOp_mulVec_pos hm hP hd)
  rw [h]
  unfold IsExDivPrice
  simp only [add_comm (adOp m P *ᵥ d)]

omit [DecidableEq X] in
/-- Exercise 6.3.2 (p. 206): in the risk-neutral case `m ≡ β ≥ 0`, `ρ(A) = β`, so `ρ(A) < 1` iff
`β < 1`. -/
theorem specRad_adOp_const {P : Matrix X X ℝ} (hP : IsMarkov P) {β : ℝ} (hβ : 0 ≤ β) :
    specRad (adOp (fun _ _ => β) P) = β := by
  classical
  unfold adOp
  rw [discountOp_const, specRad_smul_isMarkov hP hβ]

/-- Exercise 6.3.4 (p. 206): a cum-dividend claim pays `Dₜ` to the buyer, so its price obeys
`π = d + Aπ`, (6.37). -/
def IsCumDivPrice (A : Matrix X X ℝ) (d π : X → ℝ) : Prop := π = d + A *ᵥ π

/-- The cum-dividend price `(I − A)⁻¹d`. -/
noncomputable def cumDivPrice (A : Matrix X X ℝ) (d : X → ℝ) : X → ℝ := (1 - A)⁻¹ *ᵥ d

/-- Exercise 6.3.4: `(I − A)⁻¹d` is the unique solution of `π = d + Aπ`. -/
theorem isCumDivPrice_iff {A : Matrix X X ℝ} (hρ : specRad A < 1) (d π : X → ℝ) :
    IsCumDivPrice A d π ↔ π = cumDivPrice A d :=
  eq_add_mulVec_iff hρ d π

/-- §6.3.1.6, the forward sum representation: `π = ∑ₜ Aᵗd`, the expected present value of the
dividend stream with the time-`t` dividend discounted by `M₁⋯Mₜ`. -/
theorem cumDivPrice_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    cumDivPrice A d = ∑' t : ℕ, A ^ t *ᵥ d :=
  inv_mulVec_eq_tsum hρ d

/-- The cum-dividend price exceeds the ex-dividend price by the current dividend. -/
theorem cumDivPrice_eq_add_exDivPrice {A : Matrix X X ℝ} (hρ : specRad A < 1) (d : X → ℝ) :
    cumDivPrice A d = d + exDivPrice A d := by
  rw [cumDivPrice_eq_tsum hρ, exDivPrice_eq_tsum hρ, (summable_pow_mulVec hρ d).tsum_eq_zero_add]
  simp

/-! ### Nonstationary dividends (§6.3.2) -/

/-- Exercise 6.3.5 (p. 207), in finite form: if `Π = ∑ᵢ wᵢ Mᵢ(D'ᵢ + Π'ᵢ)` is the price of a claim
on next period's dividend and price over the outcomes `i` with conditional probabilities `wᵢ`,
and `D, D'ᵢ ≠ 0`, then the price-dividend ratio `V = Π/D` obeys (6.38),
`V = ∑ᵢ wᵢ Mᵢ (D'ᵢ/D)(1 + Π'ᵢ/D'ᵢ)`. -/
theorem price_dividend_ratio {ι : Type*} [Fintype ι] (w M D' Pr' : ι → ℝ) {D Pr : ℝ} (hD : D ≠ 0)
    (hD' : ∀ i, D' i ≠ 0) (hPr : Pr = ∑ i, w i * (M i * (D' i + Pr' i))) :
    Pr / D = ∑ i, w i * (M i * (D' i / D) * (1 + Pr' i / D' i)) := by
  rw [hPr, sum_div]
  refine sum_congr rfl fun i _ => ?_
  have := hD' i
  field_simp

/-- The price-dividend operator (6.40) with the expected gross dividend growth `κ̄(x)`:
`A(x, x') = m(x, x')κ̄(x)P(x, x')`. In the book `κ̄(x) = ∫ exp(κ(x, η))φ(dη)`. -/
def pdOp (m : X → X → ℝ) (κbar : X → ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  discountOp (fun x x' => m x x' * κbar x) P

/-- The price-dividend equation (6.39): `v = A(𝟙 + v)`. -/
def IsPDRatio (A : Matrix X X ℝ) (v : X → ℝ) : Prop := v = A *ᵥ (fun _ => 1) + A *ᵥ v

/-- Exercise 6.3.6 (p. 208): when `ρ(A) < 1`, (6.39) has the unique solution
`v* = (I − A)⁻¹A𝟙`. -/
theorem isPDRatio_iff {A : Matrix X X ℝ} (hρ : specRad A < 1) (v : X → ℝ) :
    IsPDRatio A v ↔ v = (1 - A)⁻¹ *ᵥ (A *ᵥ fun _ => 1) :=
  eq_add_mulVec_iff hρ _ v

/-- Exercise 6.3.6, (6.41): `v* = ∑_{t≥1} Aᵗ𝟙`. -/
theorem pdRatio_eq_tsum {A : Matrix X X ℝ} (hρ : specRad A < 1) :
    (1 - A)⁻¹ *ᵥ (A *ᵥ fun _ => (1 : ℝ)) = ∑' t : ℕ, A ^ (t + 1) *ᵥ fun _ => (1 : ℝ) := by
  rw [inv_mulVec_eq_tsum hρ]
  exact tsum_congr fun t => by rw [mulVec_mulVec, ← pow_succ]

/-! ### Exercise 6.3.7: Markov growth with a Lucas SDF -/

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- `E[exp(a + bη)] = exp(a + b²/2)` for a standard normal `η`, from the Gaussian moment generating
function. -/
theorem integral_exp_add_mul_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    {η : Ω → ℝ} (hη : HasLaw η (gaussianReal 0 1) ν) (a b : ℝ) :
    ∫ ω, Real.exp (a + b * η ω) ∂ν = Real.exp (a + b ^ 2 / 2) := by
  simp_rw [Real.exp_add]
  rw [integral_const_mul]
  have h := mgf_gaussianReal hη b
  unfold mgf at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h, ← Real.exp_add]

omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Exercise 6.3.7 (p. 208): with consumption growth `μ_c + x + σ_c η_c`, dividend growth
`μ_d + x + σ_d η_d`, standard normal shocks and the Lucas SDF `β exp(−γ g_c)`, the expected SDF
times the expected gross dividend growth is `β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)`,
so (6.40) reads `A(x, x') = β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)P(x, x')`. -/
theorem lucas_growth_factor {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {ηc ηd : Ω → ℝ}
    (hc : HasLaw ηc (gaussianReal 0 1) ν) (hd : HasLaw ηd (gaussianReal 0 1) ν)
    (β γ μc σc μd σd x : ℝ) :
    (∫ ω, β * Real.exp (-γ * (μc + x + σc * ηc ω)) ∂ν) *
        (∫ ω, Real.exp (μd + x + σd * ηd ω) ∂ν) =
      β * Real.exp (-γ * μc + μd + (1 - γ) * x + (γ ^ 2 * σc ^ 2 + σd ^ 2) / 2) := by
  have h1 : ∫ ω, β * Real.exp (-γ * (μc + x + σc * ηc ω)) ∂ν =
      β * Real.exp (-γ * (μc + x) + (-γ * σc) ^ 2 / 2) := by
    rw [integral_const_mul, ← integral_exp_add_mul_gaussian hc]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    congr 1
    ring
  have h2 : ∫ ω, Real.exp (μd + x + σd * ηd ω) ∂ν = Real.exp (μd + x + σd ^ 2 / 2) :=
    integral_exp_add_mul_gaussian hd (μd + x) σd
  rw [h1, h2, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end SargentStachurski.StochasticDiscounting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Incomplete markets: the Harrison–Kreps pricing operator

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.3.3 (pp. 209–211).

With heterogeneous beliefs `Pᵢ` and risk-neutral agents discounting at
`β ∈ (0, 1)`, the equilibrium price of an ex-dividend claim on `d ≥ 0` solves the
nonlinear equation (6.42), `π(x) = maxᵢ β ∑ (π(x') + d(x'))Pᵢ(x, x')`. The
operator `T` of (6.43) maps `ℝ^X₊` into itself and is a contraction of modulus
`β` under the supremum norm, by Lemma 2.2.2, so (6.42) has a unique solution in
`ℝ^X₊`, computable by successive approximation. Exercise 6.3.9 gives the
alternative proof through Blackwell's condition. The index set of beliefs is any
nonempty finite type, the book's `{1, 2}` included.
-/

open Matrix Finset Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The Harrison–Kreps operator (6.43): `(Tπ)(x) = maxᵢ β ∑ (π(x') + d(x'))Pᵢ(x, x')`. -/
noncomputable def hkOp (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) : X → ℝ := fun x =>
  univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x'

theorem hkOp_apply (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) (x : X) :
    hkOp β P d π x = univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x' := rfl

/-- `π` solves (6.42) iff it is a fixed point of `T` (p. 210). -/
theorem isFixedPt_hkOp_iff (β : ℝ) (P : ι → Matrix X X ℝ) (d π : X → ℝ) :
    IsFixedPt (hkOp β P d) π ↔
      ∀ x, π x = univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x' :=
  ⟨fun h x => (congrFun h.eq x).symm, fun h => funext fun x => (h x).symm⟩

/-- The nonnegative orthant `ℝ^X₊`. -/
def nonnegFns (X : Type*) : Set (X → ℝ) := {π | ∀ x, 0 ≤ π x}

omit [Fintype X] in
theorem isClosed_nonnegFns : IsClosed (nonnegFns X) := by
  have : nonnegFns X = ⋂ x, {π : X → ℝ | 0 ≤ π x} := by
    ext π
    simp [nonnegFns]
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)

/-- `T` maps `ℝ^X₊` into itself when `β ≥ 0`, `d ≥ 0` and the `Pᵢ` are Markov (p. 210). -/
theorem hkOp_mapsTo {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) : Set.MapsTo (hkOp β P d) (nonnegFns X) (nonnegFns X) := by
  intro π hπ x
  rw [hkOp_apply]
  have h0 : 0 ≤ β * ∑ x', (π x' + d x') * P (Classical.arbitrary ι) x x' :=
    mul_nonneg hβ (sum_nonneg fun x' _ =>
      mul_nonneg (add_nonneg (hπ x') (hd x')) ((hP (Classical.arbitrary ι)).nonneg x x'))
  exact h0.trans (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ _))

/-- The estimate of p. 210: `|(Tp)(x) − (Tq)(x)| ≤ β‖p − q‖_∞`, by Lemma 2.2.2 and the Markov
property of each `Pᵢ`. -/
theorem abs_hkOp_sub_le {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    (d p q : X → ℝ) (x : X) : |hkOp β P d p x - hkOp β P d q x| ≤ β * ‖p - q‖ := by
  rw [hkOp_apply, hkOp_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ, ← sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have h := (hP i).abs_mulVec_sub_le p q x
  simp only [mulVec, dotProduct] at h
  rw [← sum_sub_distrib] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  exact sum_congr rfl fun x' _ => by ring

/-- `T` is a contraction of modulus `β` on `ℝ^X₊` under the supremum norm (p. 211). -/
theorem isContractionOn_hkOp {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) :
    IsContractionOn (hkOp β P d) (nonnegFns X) β where
  mapsTo := hkOp_mapsTo hβ0 hP hd
  nonneg := hβ0
  lt_one := hβ1
  norm_sub_le p _ q _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_hkOp_sub_le hβ0 hP d p q x

/-- The Harrison–Kreps equilibrium (p. 211): (6.42) has a unique solution `π*` in `ℝ^X₊`, and
successive approximation from any `π ∈ ℝ^X₊` converges to it. -/
theorem existsUnique_hk_price {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) :
    ∃ π' ∈ nonnegFns X, IsFixedPt (hkOp β P d) π' ∧
      (∀ π ∈ nonnegFns X, IsFixedPt (hkOp β P d) π → π = π') ∧
      ∀ π ∈ nonnegFns X, Tendsto (fun k : ℕ => (hkOp β P d)^[k] π) atTop (𝓝 π') := by
  have hc := isContractionOn_hkOp hβ0 hβ1 hP hd
  obtain ⟨π', hπ', hfix⟩ := hc.exists_fixedPt isClosed_nonnegFns ⟨0, fun _ => le_rfl⟩
  exact ⟨π', hπ', hfix, fun π hπ h => hc.fixedPt_unique hπ hπ' h hfix,
    fun π hπ => hc.tendsto_iterate_fixedPt hπ hπ' hfix⟩

/-! ### Exercise 6.3.9: Blackwell's condition -/

/-- `T` is order preserving. -/
theorem hkOp_monotone {β : ℝ} (hβ : 0 ≤ β) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i))
    (d : X → ℝ) : Monotone (hkOp β P d) := by
  intro p q hpq x
  rw [hkOp_apply, hkOp_apply]
  refine Finset.sup'_mono_fun fun i _ => mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) hβ
  exact mul_le_mul_of_nonneg_right (add_le_add (hpq x') le_rfl) ((hP i).nonneg x x')

/-- `T(π + c) = Tπ + βc` for constants `c`, since each `Pᵢ𝟙 = 𝟙`. -/
theorem hkOp_add_const (β : ℝ) {P : ι → Matrix X X ℝ} (hP : ∀ i, IsMarkov (P i)) (d π : X → ℝ)
    (c : ℝ) : hkOp β P d (π + fun _ => c) = hkOp β P d π + fun _ => β * c := by
  funext x
  rw [Pi.add_apply, hkOp_apply, hkOp_apply]
  have h : ∀ i, β * ∑ x', ((π + fun _ : X => c) x' + d x') * P i x x' =
      β * ∑ x', (π x' + d x') * P i x x' + β * c := by
    intro i
    have h1 : ∑ x', ((π + fun _ : X => c) x' + d x') * P i x x' =
        ∑ x', (π x' + d x') * P i x x' + c * ∑ x', P i x x' := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun x' _ => by simp only [Pi.add_apply]; ring
    rw [h1, (hP i).rowsum, mul_one, mul_add]
  simp only [h]
  -- `max_i (f i + βc) = max_i f i + βc`
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => add_le_add
      (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ i)) le_rfl
  · obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => β * ∑ x', (π x' + d x') * P i x x')
      univ_nonempty
    have hsup : (univ.sup' univ_nonempty fun i => β * ∑ x', (π x' + d x') * P i x x') =
        β * ∑ x', (π x' + d x') * P i x x' :=
      le_antisymm (Finset.sup'_le _ _ fun j _ => hi j (mem_univ j))
        (Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x') (mem_univ i))
    rw [hsup]
    exact Finset.le_sup' (fun i => β * ∑ x', (π x' + d x') * P i x x' + β * c) (mem_univ i)

/-- Exercise 6.3.9 (p. 211): by Blackwell's condition (Lemma 2.2.4), `T` is a contraction of
modulus `β` on all of `ℝ^X`, hence on `ℝ^X₊`. -/
theorem isContractionOn_hkOp_univ {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ι → Matrix X X ℝ}
    (hP : ∀ i, IsMarkov (P i)) (d : X → ℝ) : IsContractionOn (hkOp β P d) Set.univ β :=
  isContractionOn_of_blackwell hβ0 hβ1 (hkOp_monotone hβ0 hP d) fun π c _ => by
    rw [hkOp_add_const β hP d π c]

end SargentStachurski.StochasticDiscounting

set_option linter.style.longLine false
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.mk
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.nonneg
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.rowsum
#print axioms SargentStachurski.StochasticDiscounting.IsDistribution
#print axioms SargentStachurski.StochasticDiscounting.IsDistribution.mk
#print axioms SargentStachurski.StochasticDiscounting.IsDistribution.nonneg
#print axioms SargentStachurski.StochasticDiscounting.IsDistribution.sum_eq_one
#print axioms SargentStachurski.StochasticDiscounting.mulVec_apply_eq
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.mul
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.pow
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.mulVec_const
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.StochasticDiscounting.GloballyStable
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.mk
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.mapsTo
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.nonneg
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.lt_one
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.iterate_mem
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.StochasticDiscounting.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.StochasticDiscounting.fixedPt_le_of_le
#print axioms SargentStachurski.StochasticDiscounting.le_fixedPt_of_le_apply
#print axioms SargentStachurski.StochasticDiscounting.isContractionOn_of_blackwell
#print axioms SargentStachurski.StochasticDiscounting.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.StochasticDiscounting.pow_nonneg_entries
#print axioms SargentStachurski.StochasticDiscounting.pow_le_pow_entries
#print axioms SargentStachurski.StochasticDiscounting.complexify
#print axioms SargentStachurski.StochasticDiscounting.complexify_apply
#print axioms SargentStachurski.StochasticDiscounting.complexify_pow
#print axioms SargentStachurski.StochasticDiscounting.complexify_transpose
#print axioms SargentStachurski.StochasticDiscounting.nnnorm_complexify
#print axioms SargentStachurski.StochasticDiscounting.norm_complexify
#print axioms SargentStachurski.StochasticDiscounting.specRad
#print axioms SargentStachurski.StochasticDiscounting.spectralRadius_complexify_ne_top
#print axioms SargentStachurski.StochasticDiscounting.specRad_nonneg
#print axioms SargentStachurski.StochasticDiscounting.mem_spectrum_iff_eigenpair
#print axioms SargentStachurski.StochasticDiscounting.tendsto_norm_pow_rpow
#print axioms SargentStachurski.StochasticDiscounting.eventually_norm_pow_le
#print axioms SargentStachurski.StochasticDiscounting.tendsto_norm_pow_zero
#print axioms SargentStachurski.StochasticDiscounting.summable_pow
#print axioms SargentStachurski.StochasticDiscounting.one_sub_mul_tsum
#print axioms SargentStachurski.StochasticDiscounting.tsum_mul_one_sub
#print axioms SargentStachurski.StochasticDiscounting.neumann_series
#print axioms SargentStachurski.StochasticDiscounting.specRad_transpose
#print axioms SargentStachurski.StochasticDiscounting.norm_le_norm_of_abs_le
#print axioms SargentStachurski.StochasticDiscounting.specRad_le_of_le
#print axioms SargentStachurski.StochasticDiscounting.rowsum_abs_le_norm
#print axioms SargentStachurski.StochasticDiscounting.norm_le_of_rowsum_abs_le
#print axioms SargentStachurski.StochasticDiscounting.abs_entry_le_norm
#print axioms SargentStachurski.StochasticDiscounting.norm_eq_of_rowsum_eq
#print axioms SargentStachurski.StochasticDiscounting.specRad_le_norm
#print axioms SargentStachurski.StochasticDiscounting.norm_le_specRad_of_mem_spectrum
#print axioms SargentStachurski.StochasticDiscounting.specRad_eq_of_rowsum_eq
#print axioms SargentStachurski.StochasticDiscounting.specRad_eq_of_colsum_eq
#print axioms SargentStachurski.StochasticDiscounting.eventually_abs_entry_pow_le
#print axioms SargentStachurski.StochasticDiscounting.resPartial
#print axioms SargentStachurski.StochasticDiscounting.res
#print axioms SargentStachurski.StochasticDiscounting.res_apply
#print axioms SargentStachurski.StochasticDiscounting.smul_one_sub_mul_resPartial
#print axioms SargentStachurski.StochasticDiscounting.resPartial_mul_smul_one_sub
#print axioms SargentStachurski.StochasticDiscounting.resPartial_apply
#print axioms SargentStachurski.StochasticDiscounting.summable_res_entry
#print axioms SargentStachurski.StochasticDiscounting.tendsto_resPartial_apply
#print axioms SargentStachurski.StochasticDiscounting.tendsto_inv_pow_mul_apply
#print axioms SargentStachurski.StochasticDiscounting.smul_one_sub_mul_res
#print axioms SargentStachurski.StochasticDiscounting.res_mul_smul_one_sub
#print axioms SargentStachurski.StochasticDiscounting.res_nonneg
#print axioms SargentStachurski.StochasticDiscounting.inv_le_res_diag
#print axioms SargentStachurski.StochasticDiscounting.exists_mem_spectrum_norm_eq
#print axioms SargentStachurski.StochasticDiscounting.eventually_norm_entry_pow_complexify_le
#print axioms SargentStachurski.StochasticDiscounting.smul_one_sub_mul_res_real
#print axioms SargentStachurski.StochasticDiscounting.norm_res_complexify_le
#print axioms SargentStachurski.StochasticDiscounting.norm_le_card_mul_of_entry_norm_le
#print axioms SargentStachurski.StochasticDiscounting.notMem_spectrum_of_res_bounded
#print axioms SargentStachurski.StochasticDiscounting.exists_res_entry_gt
#print axioms SargentStachurski.StochasticDiscounting.isCompact_simplex
#print axioms SargentStachurski.StochasticDiscounting.perron_frobenius
#print axioms SargentStachurski.StochasticDiscounting.perron_frobenius_left
#print axioms SargentStachurski.StochasticDiscounting.le_specRad_of_colsum_ge
#print axioms SargentStachurski.StochasticDiscounting.specRad_le_of_colsum_le
#print axioms SargentStachurski.StochasticDiscounting.le_specRad_of_rowsum_ge
#print axioms SargentStachurski.StochasticDiscounting.specRad_le_of_rowsum_le
#print axioms SargentStachurski.StochasticDiscounting.tendsto_rpow_one_div_natCast
#print axioms SargentStachurski.StochasticDiscounting.norm_pow_mul_le_norm_mulVec
#print axioms SargentStachurski.StochasticDiscounting.tendsto_norm_pow_mulVec_rpow
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.specRad_eq_one
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.exists_stationary
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.not_mulVec_ge_add
#print axioms SargentStachurski.StochasticDiscounting.Irreducible
#print axioms SargentStachurski.StochasticDiscounting.irreducible_of_pos
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.transpose
#print axioms SargentStachurski.StochasticDiscounting.pow_mulVec_eq_of_mulVec_eq
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.pos_of_mulVec_eq_smul
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.specRad_pos
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.exists_pos_eigenvector
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.exists_pos_left_eigenvector
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.eq_specRad_of_mulVec_eq_smul
#print axioms SargentStachurski.StochasticDiscounting.Irreducible.exists_eq_smul_of_mulVec_eq_smul
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.exists_unique_stationary_of_irreducible
#print axioms SargentStachurski.StochasticDiscounting.vecMul_apply_eq
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.isDistribution_vecMul
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.sum_vecMul
#print axioms SargentStachurski.StochasticDiscounting.l1
#print axioms SargentStachurski.StochasticDiscounting.l1_nonneg
#print axioms SargentStachurski.StochasticDiscounting.norm_le_l1
#print axioms SargentStachurski.StochasticDiscounting.l1_vecMul_le
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.sum_vecMul_pow
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.isDistribution_vecMul_pow
#print axioms SargentStachurski.StochasticDiscounting.l1_vecMul_pow_le
#print axioms SargentStachurski.StochasticDiscounting.tendsto_vecMul
#print axioms SargentStachurski.StochasticDiscounting.vecMul_pow_of_vecMul_eq
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.tendsto_vecMul_pow_of_pos
#print axioms SargentStachurski.StochasticDiscounting.isDistribution_single
#print axioms SargentStachurski.StochasticDiscounting.single_vecMul_eq_row
#print axioms SargentStachurski.StochasticDiscounting.IsMarkov.tendsto_pow_apply_of_pos
#print axioms SargentStachurski.StochasticDiscounting.conjMarkov
#print axioms SargentStachurski.StochasticDiscounting.conjMarkov_apply
#print axioms SargentStachurski.StochasticDiscounting.isMarkov_conjMarkov
#print axioms SargentStachurski.StochasticDiscounting.conjMarkov_pow_apply
#print axioms SargentStachurski.StochasticDiscounting.tendsto_pow_of_pos
#print axioms SargentStachurski.StochasticDiscounting.discountOp
#print axioms SargentStachurski.StochasticDiscounting.discountOp_apply
#print axioms SargentStachurski.StochasticDiscounting.discountOp_nonneg
#print axioms SargentStachurski.StochasticDiscounting.pow_succ_mulVec
#print axioms SargentStachurski.StochasticDiscounting.discountOp_const
#print axioms SargentStachurski.StochasticDiscounting.specRad_smul_isMarkov
#print axioms SargentStachurski.StochasticDiscounting.summable_pow_apply
#print axioms SargentStachurski.StochasticDiscounting.summable_pow_mulVec
#print axioms SargentStachurski.StochasticDiscounting.mulVec_tsum_pow_mulVec
#print axioms SargentStachurski.StochasticDiscounting.tsum_pow_mulVec_eq
#print axioms SargentStachurski.StochasticDiscounting.eq_of_eq_add_mulVec
#print axioms SargentStachurski.StochasticDiscounting.inv_mulVec_eq_add
#print axioms SargentStachurski.StochasticDiscounting.inv_mulVec_eq_tsum
#print axioms SargentStachurski.StochasticDiscounting.eq_add_mulVec_iff
#print axioms SargentStachurski.StochasticDiscounting.discountOp_value
#print axioms SargentStachurski.StochasticDiscounting.specRad_discountOp_const_lt_one
#print axioms SargentStachurski.StochasticDiscounting.firmDiscountOp
#print axioms SargentStachurski.StochasticDiscounting.firmValue_eq
#print axioms SargentStachurski.StochasticDiscounting.firmDiscountOp_mulVec
#print axioms SargentStachurski.StochasticDiscounting.MonotoneKernel
#print axioms SargentStachurski.StochasticDiscounting.monotone_firmValue
#print axioms SargentStachurski.StochasticDiscounting.pow_mulVec_one_nonneg
#print axioms SargentStachurski.StochasticDiscounting.sup'_pow_mulVec_one_eq_norm
#print axioms SargentStachurski.StochasticDiscounting.tendsto_sup'_pow_mulVec_one_rpow
#print axioms SargentStachurski.StochasticDiscounting.norm_pow_eq_norm_pow_mulVec_one
#print axioms SargentStachurski.StochasticDiscounting.specRad_le_norm_pow_rpow
#print axioms SargentStachurski.StochasticDiscounting.specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt
#print axioms SargentStachurski.StochasticDiscounting.tendsto_norm_pow_mulVec_rpow'
#print axioms SargentStachurski.StochasticDiscounting.tendsto_dotProduct_pow_mulVec_one_rpow
#print axioms SargentStachurski.StochasticDiscounting.productDiscountOp
#print axioms SargentStachurski.StochasticDiscounting.productDiscountOp_mulVec_comp_snd
#print axioms SargentStachurski.StochasticDiscounting.productDiscountOp_pow_mulVec_one
#print axioms SargentStachurski.StochasticDiscounting.norm_comp_snd
#print axioms SargentStachurski.StochasticDiscounting.specRad_productDiscountOp
#print axioms SargentStachurski.StochasticDiscounting.specRad_productDiscountOp_isMarkov
#print axioms SargentStachurski.StochasticDiscounting.specRad_lt_one_iff_existsUnique_pos
#print axioms SargentStachurski.StochasticDiscounting.globallyStable_of_iterate_contraction
#print axioms SargentStachurski.StochasticDiscounting.globallyStable_of_iterate_contraction_univ
#print axioms SargentStachurski.StochasticDiscounting.exists_iterate_contraction_of_norm_equiv
#print axioms SargentStachurski.StochasticDiscounting.affineOp
#print axioms SargentStachurski.StochasticDiscounting.affineOp_iterate_sub
#print axioms SargentStachurski.StochasticDiscounting.exists_isContractionOn_iterate_affineOp
#print axioms SargentStachurski.StochasticDiscounting.globallyStable_affineOp
#print axioms SargentStachurski.StochasticDiscounting.isFixedPt_affineOp_inv
#print axioms SargentStachurski.StochasticDiscounting.mulVec_le_mulVec_of_nonneg
#print axioms SargentStachurski.StochasticDiscounting.norm_abs_fun
#print axioms SargentStachurski.StochasticDiscounting.norm_le_norm_of_abs_le_fun
#print axioms SargentStachurski.StochasticDiscounting.abs_iterate_sub_le_pow_mulVec
#print axioms SargentStachurski.StochasticDiscounting.exists_isContractionOn_iterate_of_abs_sub_le
#print axioms SargentStachurski.StochasticDiscounting.globallyStable_of_abs_sub_le
#print axioms SargentStachurski.StochasticDiscounting.abs_sub_le_of_blackwell
#print axioms SargentStachurski.StochasticDiscounting.exists_isContractionOn_iterate_of_blackwell
#print axioms SargentStachurski.StochasticDiscounting.globallyStable_of_blackwell
#print axioms SargentStachurski.StochasticDiscounting.SDMDP
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.mk
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Γ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Γ_nonempty
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.r
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.β
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.β_nonneg
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.P
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.P_nonneg
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.P_rowsum
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Feasible
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.IsFeasible
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Policy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.defaultPolicy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.policy_nonempty
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Pσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Pσ_apply
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isMarkov_Pσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Lσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Lσ_apply
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Lσ_nonneg
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Lσ_eq_discountOp
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.rσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.B
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_apply
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_eq
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.B_mono
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_monotone
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.SpectralCondition
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.spectralCondition_of_dominated
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.spectralCondition_of_le
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ_eq_inv
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.iterate_Tσ_eq
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isUnit_one_sub_Lσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isFixedPt_vσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.eq_vσ_of_isFixedPt
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.existsUnique_fixedPt_Tσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ_eq_tsum
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_eq_affineOp
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.globallyStable_Tσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.tendsto_iterate_Tσ
#print axioms SargentStachurski.StochasticDiscounting.fixedPt_le_of_apply_le
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.T
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.T_apply
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.B_le_T
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_le_T
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.T_monotone
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.IsGreedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.greedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.greedy_mem
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isGreedy_greedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.greedyPolicy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isGreedy_iff_Tσ_eq_T
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.Tσ_eq_T_of_isGreedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vstar
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ_le_vstar
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.IsOptimal
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vstar_le_T_vstar
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ_eq_vstar_of_isGreedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isFixedPt_T_vstar
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.bellman_equation
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isOptimal_iff
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isOptimal_iff_isGreedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isOptimal_greedy_vstar
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.exists_isOptimal
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.hpi_update_eq_vσ
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.vσ_le_vσ_of_isGreedy
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.isOptimal_of_hpi_fixed
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.opi_one_step_eq_vfi
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.tendsto_opi_inner
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.abs_T_sub_le_of_dominated
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.globallyStable_T_of_dominated
#print axioms SargentStachurski.StochasticDiscounting.SDMDP.tendsto_iterate_T_of_dominated
#print axioms SargentStachurski.StochasticDiscounting.Exogenous
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.mk
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.Γ
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.Γ_nonempty
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.β
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.β_nonneg
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.r
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.Q
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.Q_markov
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.R
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.R_nonneg
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.R_rowsum
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.toSDMDP
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.LZ
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.LZ_apply
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.LZ_nonneg
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.Lσ_eq
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.specRad_Lσ
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.spectralCondition
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.bellman_equation
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.eq_vstar_of_isFixedPt
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.isOptimal_iff_isGreedy
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.exists_isOptimal
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.colMax
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.abs_le_colMax
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.colMax_nonneg
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.norm_eq_norm_colMax
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.abs_T_sub_le
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.colMax_iterate_sub_le
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.norm_iterate_T_sub_le
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.exists_isContractionOn_iterate_T
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.globallyStable_T
#print axioms SargentStachurski.StochasticDiscounting.Exogenous.tendsto_iterate_T
#print axioms SargentStachurski.StochasticDiscounting.inventoryNext
#print axioms SargentStachurski.StochasticDiscounting.inventoryNext_lt
#print axioms SargentStachurski.StochasticDiscounting.geomPmf
#print axioms SargentStachurski.StochasticDiscounting.geomPmf_pos
#print axioms SargentStachurski.StochasticDiscounting.summable_geomPmf
#print axioms SargentStachurski.StochasticDiscounting.tsum_geomPmf
#print axioms SargentStachurski.StochasticDiscounting.inventoryKernel
#print axioms SargentStachurski.StochasticDiscounting.summable_inventoryTerm
#print axioms SargentStachurski.StochasticDiscounting.inventoryKernel_nonneg
#print axioms SargentStachurski.StochasticDiscounting.sum_mul_inventoryKernel
#print axioms SargentStachurski.StochasticDiscounting.inventoryKernel_rowsum
#print axioms SargentStachurski.StochasticDiscounting.expectedRevenue
#print axioms SargentStachurski.StochasticDiscounting.inventoryReward
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_mem_Γ
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_B_apply
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_B_apply'
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_LZ
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_optimality
#print axioms SargentStachurski.StochasticDiscounting.inventorySDD_bellman
#print axioms SargentStachurski.StochasticDiscounting.markovPrice
#print axioms SargentStachurski.StochasticDiscounting.adOp
#print axioms SargentStachurski.StochasticDiscounting.adOp_apply
#print axioms SargentStachurski.StochasticDiscounting.markovPrice_const
#print axioms SargentStachurski.StochasticDiscounting.markovPrice_eq_adOp_mulVec
#print axioms SargentStachurski.StochasticDiscounting.IsExDivPrice
#print axioms SargentStachurski.StochasticDiscounting.exDivPrice
#print axioms SargentStachurski.StochasticDiscounting.isExDivPrice_exDivPrice
#print axioms SargentStachurski.StochasticDiscounting.eq_exDivPrice_of_isExDivPrice
#print axioms SargentStachurski.StochasticDiscounting.exDivPrice_eq_tsum
#print axioms SargentStachurski.StochasticDiscounting.adOp_mulVec_pos
#print axioms SargentStachurski.StochasticDiscounting.specRad_lt_one_iff_existsUnique_pos_exDivPrice
#print axioms SargentStachurski.StochasticDiscounting.specRad_adOp_const
#print axioms SargentStachurski.StochasticDiscounting.IsCumDivPrice
#print axioms SargentStachurski.StochasticDiscounting.cumDivPrice
#print axioms SargentStachurski.StochasticDiscounting.isCumDivPrice_iff
#print axioms SargentStachurski.StochasticDiscounting.cumDivPrice_eq_tsum
#print axioms SargentStachurski.StochasticDiscounting.cumDivPrice_eq_add_exDivPrice
#print axioms SargentStachurski.StochasticDiscounting.price_dividend_ratio
#print axioms SargentStachurski.StochasticDiscounting.pdOp
#print axioms SargentStachurski.StochasticDiscounting.IsPDRatio
#print axioms SargentStachurski.StochasticDiscounting.isPDRatio_iff
#print axioms SargentStachurski.StochasticDiscounting.pdRatio_eq_tsum
#print axioms SargentStachurski.StochasticDiscounting.integral_exp_add_mul_gaussian
#print axioms SargentStachurski.StochasticDiscounting.lucas_growth_factor
#print axioms SargentStachurski.StochasticDiscounting.hkOp
#print axioms SargentStachurski.StochasticDiscounting.hkOp_apply
#print axioms SargentStachurski.StochasticDiscounting.isFixedPt_hkOp_iff
#print axioms SargentStachurski.StochasticDiscounting.nonnegFns
#print axioms SargentStachurski.StochasticDiscounting.isClosed_nonnegFns
#print axioms SargentStachurski.StochasticDiscounting.hkOp_mapsTo
#print axioms SargentStachurski.StochasticDiscounting.abs_hkOp_sub_le
#print axioms SargentStachurski.StochasticDiscounting.isContractionOn_hkOp
#print axioms SargentStachurski.StochasticDiscounting.existsUnique_hk_price
#print axioms SargentStachurski.StochasticDiscounting.hkOp_monotone
#print axioms SargentStachurski.StochasticDiscounting.hkOp_add_const
#print axioms SargentStachurski.StochasticDiscounting.isContractionOn_hkOp_univ
