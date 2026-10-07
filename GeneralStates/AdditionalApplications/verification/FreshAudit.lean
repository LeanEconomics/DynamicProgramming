import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Countable
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Volume 2, Chapter 6 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# ADPs on pospaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.1 (pp. 99–100), with the facts
about partially ordered spaces from §A.5.3.1 used there.

A *pospace* is a topological space with a closed partial order (`OrderClosedTopology`). An ADP
on a pospace is *globally stable* when every policy operator is globally stable.

* **Lemma A.5.18**: a net converging to an upper bound `v` has supremum `v`.
* **Lemma 3.1.1**: a globally stable ADP is strongly order stable.
* **Theorem 3.1.2**: a regular, globally stable ADP whose Bellman operator has a fixed point
  satisfies the fundamental optimality properties, and VFI, OPI and HPI all converge.
* **Corollary 3.1.3** (finite ADPs) and **Theorem 3.1.4** (order bounded ADPs on countably
  Dedekind complete spaces).
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- **Lemma A.5.18** (p. 380): if a net converges to `v` and lies below `v`, its supremum is `v`. -/
theorem isLUB_of_tendsto_of_le {V : Type*} [TopologicalSpace V] [PartialOrder V]
    [OrderClosedTopology V] {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → V} {v : V}
    (hf : Tendsto f l (𝓝 v)) (hle : ∀ i, f i ≤ v) : IsLUB (range f) v := by
  refine ⟨by rintro _ ⟨i, rfl⟩; exact hle i, fun w hw => ?_⟩
  exact le_of_tendsto' hf fun i => hw ⟨i, rfl⟩

/-- The infimum form of Lemma A.5.18. -/
theorem isGLB_of_tendsto_of_le {V : Type*} [TopologicalSpace V] [PartialOrder V]
    [OrderClosedTopology V] {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → V} {v : V}
    (hf : Tendsto f l (𝓝 v)) (hle : ∀ i, v ≤ f i) : IsGLB (range f) v := by
  refine ⟨by rintro _ ⟨i, rfl⟩; exact hle i, fun w hw => ?_⟩
  exact ge_of_tendsto' hf fun i => hw ⟨i, rfl⟩


namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

/-- The iterates of an order preserving `S` increase from any `v` with `v ≼ Sv`. -/
theorem monotone_iterate_of_le {S : V → V} (hS : Monotone S) {v : V} (h : v ≤ S v) :
    Monotone fun n => S^[n] v :=
  monotone_nat_of_le_succ fun n => by
    rw [iterate_succ_apply]
    exact hS.iterate n h

variable (A) in
/-- On a regular ADP the Bellman operator is order preserving on all of `V`. -/
theorem Regular.bellman_monotone (hr : A.Regular) : Monotone A.bellman := fun _ w h =>
  A.bellman_mono (hr w) h

/-- `T_σⁿ v ≼ Tⁿ v` for a regular ADP. -/
theorem Regular.iterate_T_le_bellman (hr : A.Regular) (σ : P) (v : V) (n : ℕ) :
    (A.T σ)^[n] v ≤ A.bellman^[n] v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (A.mono σ ih).trans (A.T_le_bellman σ (hr _))

/-- `Tⁿ u ≼ u` whenever `T_σ u ≼ u` for every `σ`. -/
theorem bellman_iterate_le_of_bound (hr : A.Regular) {u : V} (hu : ∀ σ, A.T σ u ≤ u) (n : ℕ) :
    A.bellman^[n] u ≤ u := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (Regular.bellman_monotone A hr ih).trans (hu _)

variable [TopologicalSpace V]

variable (A) in
/-- `(V, 𝕋)` is globally stable (§3.1.1): every policy operator is globally stable. -/
def IsGloballyStable : Prop := ∀ σ, GloballyStable (A.T σ)

/-- A globally stable ADP is well-posed (p. 99). -/
theorem IsGloballyStable.wellPosed (h : A.IsGloballyStable) : A.WellPosed := fun σ => by
  obtain ⟨u, hu, huniq, -⟩ := h σ
  exact ⟨u, hu, fun w hw => huniq w hw⟩

/-- Under global stability, `T_σⁿ v → v_σ` for every `v`. -/
theorem IsGloballyStable.tendsto_vσ (h : A.IsGloballyStable) (σ : P) (v : V) :
    Tendsto (fun n => (A.T σ)^[n] v) atTop (𝓝 (A.vσ h.wellPosed σ)) := by
  obtain ⟨u, hu, -, hlim⟩ := h σ
  rw [← eq_vσ h.wellPosed hu]
  exact hlim v

variable [OrderClosedTopology V]

/-- **Lemma 3.1.1** (p. 99): a globally stable ADP is strongly order stable (Lemma A.5.19). -/
theorem IsGloballyStable.isStronglyOrderStable (h : A.IsGloballyStable) :
    A.IsStronglyOrderStable := fun σ =>
  stronglyOrderStable_of_globallyStable (A.mono σ) (h σ)

/-- A globally stable ADP is order stable. -/
theorem IsGloballyStable.isOrderStable (h : A.IsGloballyStable) : A.IsOrderStable :=
  h.isStronglyOrderStable.isOrderStable

/-- **Theorem 3.1.2** (p. 99): if `(V, 𝕋)` is regular and globally stable and `T` has a fixed
point in `V`, then (i) the fundamental optimality properties hold and (ii) VFI, OPI and HPI all
converge, for every greedy selector. -/
theorem theorem_3_1_2 (hr : A.Regular) (hgs : A.IsGloballyStable) {w : V}
    (hfix : A.bellman w = w) :
    A.FundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hgs.wellPosed g vstar := by
  have hos := hgs.isOrderStable
  have hw := hgs.wellPosed
  have hFO : A.FundamentalOptimality hw :=
    hos.fundamentalOptimality (hr w) ((A.solvesBellman_iff (hr w)).2 hfix)
  obtain ⟨vstar, σ, hvs, hσ, hvG, hb⟩ := hFO.exists_vstar
  have hTv : A.bellman vstar = vstar := (A.solvesBellman_iff hvG).1 hb
  have hvfi : A.VFIConverges vstar := by
    intro v hv
    have hmono := monotone_iterate_of_le (Regular.bellman_monotone A hr) hv.2
    have hup : ∀ n, A.bellman^[n] v ≤ vstar := fun n => by
      have := (Regular.bellman_monotone A hr).iterate n (le_vstar_of_mem_VU hos hvs hv)
      rwa [iterate_fixed hTv] at this
    have hlow : IsLUB (range fun n => (A.T σ)^[n] v) vstar := by
      refine isLUB_of_tendsto_of_le (hσ ▸ hgs.tendsto_vσ σ v) fun n => ?_
      exact (Regular.iterate_T_le_bellman hr σ v n).trans (hup n)
    refine ⟨hmono, by rintro _ ⟨n, rfl⟩; exact hup n, fun u hu => hlow.2 ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (Regular.iterate_T_le_bellman hr σ v n).trans (hu ⟨n, rfl⟩)
  exact ⟨hFO, vstar, hvs, hvfi, fun g hg => hvfi.opi_hpi hos hr hg hvs⟩

/-- **Corollary 3.1.3** (p. 100): a regular, globally stable, finite ADP satisfies the fundamental
optimality properties, and VFI, OPI and HPI all converge. -/
theorem corollary_3_1_3 (hr : A.Regular) (hgs : A.IsGloballyStable) (hfin : A.IsFinite) :
    A.FundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hgs.wellPosed g vstar := by
  obtain ⟨hFO, -⟩ := fundamentalOptimality_of_finite hgs.isOrderStable hr hfin
  obtain ⟨vstar, -, -, -, hvG, hb⟩ := hFO.exists_vstar
  exact theorem_3_1_2 hr hgs ((A.solvesBellman_iff hvG).1 hb)

/-- **Theorem 3.1.4** (p. 100): if `(V, 𝕋)` is regular, globally stable and order bounded, and `V`
is countably Dedekind complete, then (i) the fundamental optimality properties hold and (ii) VFI,
OPI and HPI all converge. -/
theorem theorem_3_1_4 (hr : A.Regular) (hgs : A.IsGloballyStable) (hb : A.OrderBounded)
    (hV : CountablyDedekindComplete V) :
    A.FundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hgs.wellPosed g vstar := by
  have hos := hgs.isOrderStable
  have hw := hgs.wellPosed
  have hTm := Regular.bellman_monotone A hr
  obtain ⟨u, hu⟩ := hb
  obtain ⟨σ₀⟩ := A.nonempty
  set v := A.vσ hw σ₀
  have hvu : v ≤ u := hos.vσ_le σ₀ u (hu σ₀)
  have hvT : v ≤ A.bellman v :=
    (A.VSig_inter_VG_subset ⟨⟨σ₀, A.T_vσ hw σ₀⟩, hr v⟩).2
  have hmono := monotone_iterate_of_le hTm hvT
  have hbdd : ∀ n, A.bellman^[n] v ≤ u := fun n =>
    (hTm.iterate n hvu).trans (bellman_iterate_le_of_bound hr hu n)
  obtain ⟨vbar, hvbar⟩ := (hV (range fun n => A.bellman^[n] v) (range_nonempty _)
    (countable_range _)).1 ⟨u, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  have hle : vbar ≤ A.bellman vbar := by
    have hsucc := (isLUB_range_succ_iff hmono vbar).2 hvbar
    refine hsucc.2 ?_
    rintro _ ⟨n, rfl⟩
    change A.bellman^[n + 1] v ≤ _
    rw [iterate_succ_apply']
    exact hTm (hvbar.1 ⟨n, rfl⟩)
  set σ := A.greedy vbar
  have hTσ : A.T σ vbar = A.bellman vbar := rfl
  have hvσ : vbar ≤ A.vσ hw σ := hos.le_vσ σ vbar (hle.trans_eq hTσ.symm)
  have hlub : IsLUB (range fun n => (A.T σ)^[n] v) (A.vσ hw σ) :=
    isLUB_of_tendsto_of_le (hgs.tendsto_vσ σ v) fun n =>
      ((Regular.iterate_T_le_bellman hr σ v n).trans (hvbar.1 ⟨n, rfl⟩)).trans hvσ
  have heq : vbar = A.vσ hw σ := le_antisymm hvσ (hlub.2 (by
    rintro _ ⟨n, rfl⟩
    exact (Regular.iterate_T_le_bellman hr σ v n).trans (hvbar.1 ⟨n, rfl⟩)))
  refine theorem_3_1_2 hr hgs (w := vbar) ?_
  rw [← hTσ, heq]
  exact A.T_vσ hw σ


end ADP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# ADPs on partially ordered metric spaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.2 (pp. 100–101), with §A.5.3.2.

A *partially ordered metric space* is a metric space whose partial order is closed. A metric is
*sup-nonexpansive* (A.22) if `d(⋁ v_α, ⋁ w_α) ≤ sup_α d(v_α, w_α)` whenever the suprema exist.
Paired families `(v_α, w_α)` are encoded as sets of pairs.

* **Lemma A.5.21**: with a sup-nonexpansive metric, the Bellman operator inherits the common
  contraction modulus of the policy operators.
* Semi-regularity on a closed `V₀` and geometric convergence of VFI.
* **Theorem 3.1.5**: contracting policy operators on a complete sup-nonexpansive space, semi-regular
  on a nonempty closed `V₀`, give the fundamental optimality properties, `v* ∈ V₀` and geometric
  convergence of VFI; under regularity OPI and HPI converge too.
* Theorem 3.1.5 is false when `V₀ = ∅`, which its statement allows: an explicit counterexample.
* The metrics of `ℝ` and of `ℝⁿ` (the supremum metric) are sup-nonexpansive.
-/

open Set Function Filter Topology

open scoped NNReal

namespace SargentStachurski.AdditionalApplications

/-- A distance `d` is sup-nonexpansive (§A.5.3.2, (A.22)): for every paired family of points,
encoded as a set `S` of pairs, if `⋁ v_α = a` and `⋁ w_α = b` exist and `d(v_α, w_α) ≤ c` for all
`α`, then `d(a, b) ≤ c`. -/
def IsSupNonexpansive {V : Type*} [PartialOrder V] (d : V → V → ℝ) : Prop :=
  ∀ (S : Set (V × V)) (a b : V) (c : ℝ), 0 ≤ c → IsLUB (Prod.fst '' S) a →
    IsLUB (Prod.snd '' S) b → (∀ p ∈ S, d p.1 p.2 ≤ c) → d a b ≤ c

/-- The dual notion, for infima: `d(⋀ v_α, ⋀ w_α) ≤ sup_α d(v_α, w_α)`. -/
def IsInfNonexpansive {V : Type*} [PartialOrder V] (d : V → V → ℝ) : Prop :=
  ∀ (S : Set (V × V)) (a b : V) (c : ℝ), 0 ≤ c → IsGLB (Prod.fst '' S) a →
    IsGLB (Prod.snd '' S) b → (∀ p ∈ S, d p.1 p.2 ≤ c) → d a b ≤ c

/-- Inf-nonexpansiveness is sup-nonexpansiveness for the reversed order. -/
theorem isInfNonexpansive_iff {V : Type*} [PartialOrder V] (d : V → V → ℝ) :
    IsInfNonexpansive d ↔
      IsSupNonexpansive (fun a b : Vᵒᵈ => d (OrderDual.ofDual a) (OrderDual.ofDual b)) := by
  constructor
  · intro h S a b c hc ha hb hS
    exact h ((fun p => (OrderDual.ofDual p.1, OrderDual.ofDual p.2)) '' S) _ _ c hc
      (by rw [image_image]; exact ha) (by rw [image_image]; exact hb)
      (by rintro _ ⟨p, hp, rfl⟩; exact hS p hp)
  · intro h S a b c hc ha hb hS
    exact h ((fun p => (OrderDual.toDual p.1, OrderDual.toDual p.2)) '' S)
      (OrderDual.toDual a) (OrderDual.toDual b) c hc
      (by rw [image_image]; exact ha) (by rw [image_image]; exact hb)
      (by rintro _ ⟨p, hp, rfl⟩; exact hS p hp)


/-- The metric of `ℝ` is sup-nonexpansive (the case `E = ℝ`, `e = 1` of Proposition A.5.23). -/
theorem isSupNonexpansive_real : IsSupNonexpansive (dist : ℝ → ℝ → ℝ) := by
  intro S a b c _ ha hb hS
  rw [Real.dist_eq, abs_le]
  constructor
  · have : b ≤ a + c := hb.2 (by
      rintro _ ⟨p, hp, rfl⟩
      have h1 := (abs_le.1 ((Real.dist_eq _ _).symm.trans_le (hS p hp))).1
      linarith [ha.1 ⟨p, hp, rfl⟩])
    linarith
  · have : a ≤ b + c := ha.2 (by
      rintro _ ⟨p, hp, rfl⟩
      have h1 := (abs_le.1 ((Real.dist_eq _ _).symm.trans_le (hS p hp))).2
      linarith [hb.1 ⟨p, hp, rfl⟩])
    linarith

/-- The supremum metric of `ℝⁿ` (here `ι → ℝ` with `ι` finite) is sup-nonexpansive. -/
theorem isSupNonexpansive_pi {ι : Type*} [Fintype ι] :
    IsSupNonexpansive (dist : (ι → ℝ) → (ι → ℝ) → ℝ) := by
  intro S a b c hc ha hb hS
  refine (dist_pi_le_iff hc).2 fun i => ?_
  let Si : Set (ℝ × ℝ) := (fun p : (ι → ℝ) × (ι → ℝ) => (p.1 i, p.2 i)) '' S
  refine isSupNonexpansive_real Si (a i) (b i) c hc ?_ ?_ ?_
  · have := (isLUB_pi.1 ha) i
    simp only [Si, image_image] at this ⊢
    exact this
  · have := (isLUB_pi.1 hb) i
    simp only [Si, image_image] at this ⊢
    exact this
  · rintro _ ⟨p, hp, rfl⟩
    exact (dist_le_pi_dist p.1 p.2 i).trans (hS p hp)

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable [PseudoMetricSpace V]

/-- **Lemma A.5.21** (p. 381): if the metric is sup-nonexpansive and every `T_σ` is a contraction
of modulus `β`, then `d(Tv, Tw) ≤ β d(v, w)` for `v, w ∈ V_G`. -/
theorem lemma_A_5_21 (hd : IsSupNonexpansive (dist : V → V → ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w) {v w : V} (hv : v ∈ A.VG)
    (hw : w ∈ A.VG) : dist (A.bellman v) (A.bellman w) ≤ β * dist v w := by
  refine hd (range fun σ => (A.T σ v, A.T σ w)) _ _ _ (mul_nonneg hβ dist_nonneg) ?_ ?_ ?_
  · rw [← range_comp]
    exact A.isBellmanValue_bellman hv
  · rw [← range_comp]
    exact A.isBellmanValue_bellman hw
  · rintro _ ⟨σ, rfl⟩
    exact hT σ v w

variable (A) in
/-- `(V, 𝕋)` is semi-regular on `V₀` (§3.1.2): `V₀` is closed, `V₀ ⊆ V_G` and `TV₀ ⊆ V₀`. -/
def IsSemiRegular (V₀ : Set V) : Prop := IsClosed V₀ ∧ V₀ ⊆ A.VG ∧ MapsTo A.bellman V₀ V₀

variable (A) in
/-- VFI is geometrically convergent on `V₀` (§3.1.2): `v*` exists and, for some `β ∈ (0, 1)`,
`d(Tⁿv, v*) = 𝕆(βⁿ)` for each `v ∈ V₀`. -/
def VFIGeometric (V₀ : Set V) (vstar : V) : Prop :=
  A.IsValueFunction vstar ∧
    ∃ β, 0 < β ∧ β < 1 ∧ ∀ v ∈ V₀, ∃ C, ∀ n, dist (A.bellman^[n] v) vstar ≤ C * β ^ n

end ADP

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable [MetricSpace V] [CompleteSpace V]

/-- Policy operators that are contractions of a common modulus `β < 1` on a complete space are
globally stable (Banach's theorem). -/
theorem isGloballyStable_of_contraction (hne : Nonempty V) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w) : A.IsGloballyStable := fun σ => by
  have hc : ContractingWith ⟨β, hβ0⟩ (A.T σ) :=
    ⟨hβ1, LipschitzWith.of_dist_le_mul fun v w => hT σ v w⟩
  exact ⟨hc.fixedPoint _, hc.fixedPoint_isFixedPt, fun v hv => hc.fixedPoint_unique hv,
    hc.tendsto_iterate_fixedPoint⟩

variable [OrderClosedTopology V]

/-- **Theorem 3.1.5** (p. 101): let `(V, 𝕋)` be semi-regular on a nonempty closed `V₀`, let the
metric be complete and sup-nonexpansive, and let each `T_σ` be a contraction of modulus `β`. Then
(i) the fundamental optimality properties hold, (ii) `v* ∈ V₀`, and (iii) VFI is geometrically
convergent on `V₀`; if `(V, 𝕋)` is also regular, OPI and HPI converge. (`V₀ ≠ ∅` is needed:
see `theorem_3_1_5_needs_nonempty`.) -/
theorem theorem_3_1_5 (hd : IsSupNonexpansive (dist : V → V → ℝ)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w) {V₀ : Set V}
    (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    A.FundamentalOptimality (isGloballyStable_of_contraction ⟨hne.some⟩ hβ0 hβ1 hT).wellPosed ∧
      ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
        (A.Regular → ∀ g, A.IsSelector g →
          A.OPIConverges g vstar ∧
            A.HPIConverges (isGloballyStable_of_contraction ⟨hne.some⟩ hβ0 hβ1 hT).wellPosed g
              vstar) := by
  have hgs := isGloballyStable_of_contraction ⟨hne.some⟩ hβ0 hβ1 hT
  have hos := hgs.isOrderStable
  obtain ⟨hcl, hsub, hmaps⟩ := hsr
  have : CompleteSpace V₀ := hcl.completeSpace_coe
  have : Nonempty V₀ := hne.to_subtype
  let T₀ : V₀ → V₀ := fun v => ⟨A.bellman v, hmaps v.2⟩
  have hc : ContractingWith ⟨β, hβ0⟩ T₀ := ⟨hβ1, LipschitzWith.of_dist_le_mul fun v w =>
    lemma_A_5_21 hd hβ0 hT (hsub v.2) (hsub w.2)⟩
  set vbar := hc.fixedPoint T₀
  have hfix : A.bellman vbar = vbar := congrArg Subtype.val hc.fixedPoint_isFixedPt
  have hFO : A.FundamentalOptimality hgs.wellPosed :=
    hos.fundamentalOptimality (hsub vbar.2) ((A.solvesBellman_iff (hsub vbar.2)).2 hfix)
  obtain ⟨-, ⟨v', hv', -, -, huniq⟩, -⟩ := id hFO
  have hvs : A.IsValueFunction vbar := by
    rw [huniq vbar (hsub vbar.2) ((A.solvesBellman_iff (hsub vbar.2)).2 hfix)]
    exact hv'
  have hsemi : Semiconj Subtype.val T₀ A.bellman := fun _ => rfl
  refine ⟨hFO, vbar, vbar.2, ⟨hvs, max β (1 / 2), by positivity, max_lt hβ1 (by norm_num),
    fun v hv => ⟨dist v (A.bellman v) / (1 - β), fun n => ?_⟩⟩, fun hr g hg => ?_⟩
  · have h1 := hc.apriori_dist_iterate_fixedPoint_le ⟨v, hv⟩ n
    have h2 : (T₀^[n] ⟨v, hv⟩ : V) = A.bellman^[n] v := (hsemi.iterate_right n) ⟨v, hv⟩
    rw [Subtype.dist_eq, h2] at h1
    have h3 : β ^ n ≤ max β (1 / 2) ^ n := pow_le_pow_left₀ hβ0 (le_max_left _ _) n
    have h4 : 0 ≤ dist v (A.bellman v) / (1 - β) := div_nonneg dist_nonneg (by linarith)
    calc dist (A.bellman^[n] v) vbar ≤ dist v (A.bellman v) * β ^ n / (1 - β) := h1
      _ = dist v (A.bellman v) / (1 - β) * β ^ n := by ring
      _ ≤ dist v (A.bellman v) / (1 - β) * max β (1 / 2) ^ n := by gcongr
  · obtain ⟨-, w, hw, -, hconv⟩ := theorem_3_1_2 hr hgs hfix
    rw [hvs.unique hw]
    exact hconv g hg


/-- **Theorem 3.1.5 needs `V₀ ≠ ∅`.** The empty set is closed, contained in `V_G` and mapped into
itself, so every ADP is semi-regular on `∅`. On `V = ℝ` with policies `n ∈ ℕ` and
`T_n v = v/2 + 1 − 1/(n + 1)`, every `T_n` is a contraction of modulus `1/2`, the metric is
complete and sup-nonexpansive, yet no greedy policy exists anywhere, so the fundamental optimality
properties fail. -/
theorem theorem_3_1_5_needs_nonempty :
    ∃ A : ADP ℝ ℕ, IsSupNonexpansive (dist : ℝ → ℝ → ℝ) ∧
      (∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ 1 / 2 * dist v w) ∧ A.IsSemiRegular ∅ ∧
        ∀ hw, ¬ A.FundamentalOptimality hw := by
  let A : ADP ℝ ℕ :=
    { T := fun n v => v / 2 + (1 - 1 / ((n : ℝ) + 1))
      mono := fun n v w h => by simp only; linarith
      nonempty := ⟨0⟩ }
  refine ⟨A, isSupNonexpansive_real, fun n v w => ?_, ⟨isClosed_empty, empty_subset _,
    mapsTo_empty _ _⟩, fun hw hFO => ?_⟩
  · simp only [A, Real.dist_eq]
    rw [show v / 2 + (1 - 1 / ((n : ℝ) + 1)) - (w / 2 + (1 - 1 / ((n : ℝ) + 1))) =
      1 / 2 * (v - w) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · obtain ⟨-, ⟨v, -, ⟨n, hn⟩, -⟩, -⟩ := hFO
    have h := hn (n + 1)
    simp only [A, Nat.cast_add, Nat.cast_one] at h
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : 1 / ((n : ℝ) + 1 + 1) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt h1 (by linarith)
    linarith

end ADP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded measurable functions as a Banach lattice

The space `bX` of bounded measurable functions `X → ℝ` (§A.4.2.4) with the supremum norm and the
pointwise order is a Banach lattice (§A.5.3.3). It is built here as a type `BM X` of its own, so
that it carries exactly one topology, the one of the supremum norm. The algebraic, order and
metric structures are definitions, made available with `attribute [local instance]`.

* `BM X` is a normed space over `ℝ`, a lattice, an ordered additive group, has a solid norm
  (a lattice norm) and is complete: a Banach lattice. Its order is therefore closed.
* `BM X` is countably Dedekind complete (Corollary A.5.17).
* The supremum metric is sup-nonexpansive and inf-nonexpansive (Proposition A.5.23 with the order
  unit `𝟙`).
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- `bX` as a type: bounded measurable functions `X → ℝ` (§A.4.2.4). -/
structure BM (X : Type*) [MeasurableSpace X] where
  /-- the underlying function -/
  toFun : X → ℝ
  /-- it is measurable -/
  measurable' : Measurable toFun
  /-- it is bounded -/
  bdd' : ∃ C, ∀ x, |toFun x| ≤ C

namespace BM

variable {X : Type*} [MeasurableSpace X]

theorem ext {f g : BM X} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

theorem bddAbove (f : BM X) : BddAbove (range fun x => |f.toFun x|) := by
  obtain ⟨C, hC⟩ := f.bdd'
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩

/-- The constant function `c`. -/
def const (c : ℝ) : BM X := ⟨fun _ => c, measurable_const, ⟨|c|, fun _ => le_rfl⟩⟩

theorem toFun_injective : Injective (toFun : BM X → X → ℝ) := fun _ _ h =>
  ext fun x => congrFun h x

/-- The zero function. -/
abbrev zero : Zero (BM X) := ⟨const 0⟩

/-- Pointwise addition. -/
abbrev add : Add (BM X) := ⟨fun f g => ⟨fun x => f.toFun x + g.toFun x,
  f.measurable'.add g.measurable', by
    obtain ⟨C, hC⟩ := f.bdd'
    obtain ⟨D, hD⟩ := g.bdd'
    exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩⟩

/-- Pointwise negation. -/
abbrev neg : Neg (BM X) := ⟨fun f => ⟨fun x => -f.toFun x, f.measurable'.neg, by
  obtain ⟨C, hC⟩ := f.bdd'
  exact ⟨C, fun x => by rw [abs_neg]; exact hC x⟩⟩⟩

/-- Pointwise subtraction. -/
abbrev sub : Sub (BM X) := ⟨fun f g => ⟨fun x => f.toFun x - g.toFun x,
  f.measurable'.sub g.measurable', by
    obtain ⟨C, hC⟩ := f.bdd'
    obtain ⟨D, hD⟩ := g.bdd'
    exact ⟨C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩⟩⟩

/-- Multiplication by a real constant, pointwise. -/
def smulReal (c : ℝ) (f : BM X) : BM X := ⟨fun x => c * f.toFun x, f.measurable'.const_mul c, by
  obtain ⟨C, hC⟩ := f.bdd'
  exact ⟨|c| * C, fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩⟩

/-- `ℕ`-multiples, pointwise. -/
abbrev nsmul : SMul ℕ (BM X) := ⟨fun n f => smulReal (n : ℝ) f⟩

/-- `ℤ`-multiples, pointwise. -/
abbrev zsmul : SMul ℤ (BM X) := ⟨fun n f => smulReal (n : ℝ) f⟩

attribute [local instance] zero add neg sub nsmul zsmul in
/-- The additive group structure, pointwise. -/
abbrev addCommGroup : AddCommGroup (BM X) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun f n => funext fun x => (nsmul_eq_mul (n : ℕ) (f.toFun x)).symm)
    (fun f n => funext fun x => (zsmul_eq_mul (f.toFun x) n).symm)

/-- The supremum norm `‖f‖ = sup_x |f(x)|`. -/
noncomputable def supNorm (f : BM X) : ℝ := ⨆ x, |f.toFun x|

theorem abs_le_supNorm (f : BM X) (x : X) : |f.toFun x| ≤ supNorm f :=
  le_ciSup f.bddAbove x

theorem supNorm_le {f : BM X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f.toFun x| ≤ C) :
    supNorm f ≤ C :=
  Real.iSup_le h hC

theorem supNorm_nonneg (f : BM X) : 0 ≤ supNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

attribute [local instance] addCommGroup in
/-- The normed group structure of the supremum norm. -/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup (BM X) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := supNorm
      map_zero' := le_antisymm (supNorm_le le_rfl fun _ => by
        change |(0 : ℝ)| ≤ 0
        simp) (supNorm_nonneg _)
      add_le' := fun f g => supNorm_le (add_nonneg (supNorm_nonneg f) (supNorm_nonneg g))
        fun x => (abs_add_le (f.toFun x) (g.toFun x)).trans
          (add_le_add (abs_le_supNorm f x) (abs_le_supNorm g x))
      neg' := fun f => by
        change (⨆ x, |-f.toFun x|) = ⨆ x, |f.toFun x|
        simp_rw [abs_neg]
      eq_zero_of_map_eq_zero' := fun f h => ext fun x =>
        abs_nonpos_iff.1 ((abs_le_supNorm f x).trans h.le) }

attribute [local instance] normedAddCommGroup

@[simp] theorem add_apply (f g : BM X) (x : X) : (f + g).toFun x = f.toFun x + g.toFun x := rfl

@[simp] theorem sub_apply (f g : BM X) (x : X) : (f - g).toFun x = f.toFun x - g.toFun x := rfl

@[simp] theorem neg_apply (f : BM X) (x : X) : (-f).toFun x = -f.toFun x := rfl

@[simp] theorem zero_apply (x : X) : (0 : BM X).toFun x = 0 := rfl

@[simp] theorem const_apply (c : ℝ) (x : X) : (const c : BM X).toFun x = c := rfl

theorem norm_def (f : BM X) : ‖f‖ = supNorm f := rfl

theorem abs_le_norm (f : BM X) (x : X) : |f.toFun x| ≤ ‖f‖ := abs_le_supNorm f x

theorem norm_le {f : BM X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f.toFun x| ≤ C) : ‖f‖ ≤ C :=
  supNorm_le hC h

theorem abs_sub_le_dist (f g : BM X) (x : X) : |f.toFun x - g.toFun x| ≤ dist f g := by
  rw [dist_eq_norm]
  exact abs_le_norm (f - g) x

theorem dist_le {f g : BM X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f.toFun x - g.toFun x| ≤ C) :
    dist f g ≤ C := by
  rw [dist_eq_norm]
  exact norm_le hC h

/-- Scalar multiplication, pointwise. -/
abbrev module : Module ℝ (BM X) where
  smul := smulReal
  one_smul f := ext fun x => one_mul (f.toFun x)
  mul_smul a b f := ext fun x => mul_assoc a b (f.toFun x)
  smul_zero a := ext fun _ => mul_zero a
  smul_add a f g := ext fun x => mul_add a (f.toFun x) (g.toFun x)
  add_smul a b f := ext fun x => add_mul a b (f.toFun x)
  zero_smul f := ext fun x => zero_mul (f.toFun x)

attribute [local instance] module

@[simp] theorem smul_apply (c : ℝ) (f : BM X) (x : X) : (c • f).toFun x = c * f.toFun x := rfl

/-- `BM X` is a normed space over `ℝ`. -/
noncomputable abbrev normedSpace : NormedSpace ℝ (BM X) where
  norm_smul_le c f := norm_le (mul_nonneg (norm_nonneg c) (norm_nonneg f)) fun x => by
    rw [smul_apply, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le_norm f x) (abs_nonneg c)

/-- The pointwise lattice structure. -/
abbrev lattice : Lattice (BM X) where
  le f g := ∀ x, f.toFun x ≤ g.toFun x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h1 h2 x := (h1 x).trans (h2 x)
  le_antisymm _ _ h1 h2 := ext fun x => le_antisymm (h1 x) (h2 x)
  sup f g := ⟨fun x => max (f.toFun x) (g.toFun x), f.measurable'.max g.measurable', by
    obtain ⟨C, hC⟩ := f.bdd'
    obtain ⟨D, hD⟩ := g.bdd'
    refine ⟨C + D, fun x => abs_le.2 ⟨?_, ?_⟩⟩
    · have h1 := abs_le.1 (hC x)
      have h2 := (abs_nonneg _).trans (hD x)
      linarith [le_max_left (f.toFun x) (g.toFun x)]
    · have h1 := abs_le.1 (hC x)
      have h2 := abs_le.1 (hD x)
      have h3 := (abs_nonneg _).trans (hC x)
      have h4 := (abs_nonneg _).trans (hD x)
      exact max_le (by linarith) (by linarith)⟩
  le_sup_left _ _ _ := le_max_left _ _
  le_sup_right _ _ _ := le_max_right _ _
  sup_le _ _ _ h1 h2 x := max_le (h1 x) (h2 x)
  inf f g := ⟨fun x => min (f.toFun x) (g.toFun x), f.measurable'.min g.measurable', by
    obtain ⟨C, hC⟩ := f.bdd'
    obtain ⟨D, hD⟩ := g.bdd'
    refine ⟨C + D, fun x => abs_le.2 ⟨?_, ?_⟩⟩
    · have h1 := abs_le.1 (hC x)
      have h2 := abs_le.1 (hD x)
      have h3 := (abs_nonneg _).trans (hC x)
      have h4 := (abs_nonneg _).trans (hD x)
      exact le_min (by linarith) (by linarith)
    · have h1 := abs_le.1 (hC x)
      have h2 := (abs_nonneg _).trans (hD x)
      linarith [min_le_left (f.toFun x) (g.toFun x)]⟩
  inf_le_left _ _ _ := min_le_left _ _
  inf_le_right _ _ _ := min_le_right _ _
  le_inf _ _ _ h1 h2 x := le_min (h1 x) (h2 x)

attribute [local instance] lattice

theorem le_def {f g : BM X} : f ≤ g ↔ ∀ x, f.toFun x ≤ g.toFun x := Iff.rfl

@[simp] theorem sup_apply (f g : BM X) (x : X) :
    (f ⊔ g).toFun x = max (f.toFun x) (g.toFun x) := rfl

@[simp] theorem inf_apply (f g : BM X) (x : X) :
    (f ⊓ g).toFun x = min (f.toFun x) (g.toFun x) := rfl

@[simp] theorem abs_apply (f : BM X) (x : X) : |f|.toFun x = |f.toFun x| := rfl

/-- `BM X` is an ordered additive group. -/
theorem isOrderedAddMonoid : IsOrderedAddMonoid (BM X) where
  add_le_add_left _ _ h c x := add_le_add_left (h x) (c.toFun x)

/-- The supremum norm is a lattice norm: `|f| ≤ |g|` implies `‖f‖ ≤ ‖g‖`. -/
theorem hasSolidNorm : HasSolidNorm (BM X) where
  solid f g h := norm_le (norm_nonneg g) fun x =>
    (show |f.toFun x| ≤ |g.toFun x| from h x).trans (abs_le_norm g x)

/-- `BM X` is complete: a uniformly Cauchy sequence of bounded measurable functions converges
uniformly to a bounded measurable function. -/
theorem completeSpace : CompleteSpace (BM X) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hpt : ∀ x, CauchySeq fun n => (u n).toFun x := fun x =>
    Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
      exact ⟨N, fun m hm n hn => by
        rw [Real.dist_eq]
        exact (abs_sub_le_dist _ _ x).trans_lt (hN m hm n hn)⟩
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hpt x)
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable (fun n => (u n).measurable') (tendsto_pi_nhds.2 hg)
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hu 1 one_pos
  have hgb : ∃ C, ∀ x, |g x| ≤ C := ⟨‖u N₁‖ + 1, fun x => by
    refine le_of_tendsto ((hg x).abs) (eventually_atTop.2 ⟨N₁, fun n hn => ?_⟩)
    have h1 := (abs_sub_le_dist _ _ x).trans (hN₁ n hn N₁ le_rfl).le
    have h2 := abs_le_norm (u N₁) x
    have h3 := abs_sub_abs_le_abs_sub ((u n).toFun x) ((u N₁).toFun x)
    linarith⟩
  refine ⟨⟨g, hgm, hgb⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => (dist_le (half_pos hε).le fun x => ?_).trans_lt (half_lt_self hε)⟩
  refine le_of_tendsto (((tendsto_const_nhds (x := (u n).toFun x)).sub (hg x)).abs)
    (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
  exact ((abs_sub_le_dist _ _ x).trans (hN n hn m hm).le)

/-- **Corollary A.5.17** (p. 379): `bX` is countably Dedekind complete. -/
theorem countablyDedekindComplete : CountablyDedekindComplete (BM X) := by
  intro A hne hc
  have : Countable A := hc.to_subtype
  have : Nonempty A := hne.to_subtype
  obtain ⟨f₀, hf₀⟩ := hne
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨l, hl⟩ => ?_⟩
  · have hbdd : ∀ x, BddAbove (range fun f : A => f.1.toFun x) := fun x =>
      ⟨u.toFun x, by rintro _ ⟨f, rfl⟩; exact hu f.2 x⟩
    obtain ⟨C₀, hC₀⟩ := f₀.bdd'
    obtain ⟨Cu, hCu⟩ := u.bdd'
    refine ⟨⟨fun x => ⨆ f : A, f.1.toFun x, Measurable.iSup fun f => f.1.measurable',
      ⟨C₀ + Cu, fun x => abs_le.2 ⟨?_, ?_⟩⟩⟩, fun f hf x => le_ciSup (hbdd x) ⟨f, hf⟩,
      fun w hw x => ciSup_le fun f => hw f.2 x⟩
    · have h1 := le_ciSup (hbdd x) ⟨f₀, hf₀⟩
      have h2 := abs_le.1 (hC₀ x)
      have h3 := (abs_nonneg _).trans (hCu x)
      simp only at h1
      linarith
    · have h1 : (⨆ f : A, f.1.toFun x) ≤ u.toFun x := ciSup_le fun f => hu f.2 x
      have h2 := abs_le.1 (hCu x)
      have h3 := (abs_nonneg _).trans (hC₀ x)
      linarith
  · have hbdd : ∀ x, BddBelow (range fun f : A => f.1.toFun x) := fun x =>
      ⟨l.toFun x, by rintro _ ⟨f, rfl⟩; exact hl f.2 x⟩
    obtain ⟨C₀, hC₀⟩ := f₀.bdd'
    obtain ⟨Cl, hCl⟩ := l.bdd'
    refine ⟨⟨fun x => ⨅ f : A, f.1.toFun x, Measurable.iInf fun f => f.1.measurable',
      ⟨C₀ + Cl, fun x => abs_le.2 ⟨?_, ?_⟩⟩⟩, fun f hf x => ciInf_le (hbdd x) ⟨f, hf⟩,
      fun w hw x => le_ciInf fun f => hw f.2 x⟩
    · have h1 : l.toFun x ≤ ⨅ f : A, f.1.toFun x := le_ciInf fun f => hl f.2 x
      have h2 := abs_le.1 (hCl x)
      have h3 := (abs_nonneg _).trans (hC₀ x)
      linarith
    · have h1 := ciInf_le (hbdd x) ⟨f₀, hf₀⟩
      have h2 := abs_le.1 (hC₀ x)
      have h3 := (abs_nonneg _).trans (hCl x)
      simp only at h1
      linarith

/-- **Proposition A.5.23** for `bX`, with the order unit `𝟙`: the supremum metric is
sup-nonexpansive. -/
theorem isSupNonexpansive : IsSupNonexpansive (dist : BM X → BM X → ℝ) := by
  intro S a b c hc ha hb hS
  have key : ∀ (S' : Set (BM X × BM X)) (a' b' : BM X), IsLUB (Prod.fst '' S') a' →
      IsLUB (Prod.snd '' S') b' → (∀ p ∈ S', dist p.1 p.2 ≤ c) →
        ∀ x, a'.toFun x ≤ b'.toFun x + c := by
    intro S' a' b' ha' hb' hS' x
    have hub : b' + const c ∈ upperBounds (Prod.fst '' S') := by
      rintro _ ⟨p, hp, rfl⟩ y
      have h1 := (abs_le.1 ((abs_sub_le_dist p.1 p.2 y).trans (hS' p hp))).2
      have h2 := hb'.1 ⟨p, hp, rfl⟩ y
      simp only [add_apply, const_apply]
      linarith
    exact ha'.2 hub x
  refine dist_le hc fun x => abs_le.2 ⟨?_, ?_⟩
  · have := key (Prod.swap '' S) b a (by rw [image_image]; exact hb)
      (by rw [image_image]; exact ha)
      (by rintro _ ⟨p, hp, rfl⟩; rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hS p hp) x
    linarith
  · have := key S a b ha hb hS x
    linarith

/-- The supremum metric of `bX` is inf-nonexpansive too. -/
theorem isInfNonexpansive : IsInfNonexpansive (dist : BM X → BM X → ℝ) := by
  intro S a b c hc ha hb hS
  have key : ∀ (S' : Set (BM X × BM X)) (a' b' : BM X), IsGLB (Prod.fst '' S') a' →
      IsGLB (Prod.snd '' S') b' → (∀ p ∈ S', dist p.1 p.2 ≤ c) →
        ∀ x, b'.toFun x - c ≤ a'.toFun x := by
    intro S' a' b' ha' hb' hS' x
    have hlb : b' - const c ∈ lowerBounds (Prod.fst '' S') := by
      rintro _ ⟨p, hp, rfl⟩ y
      have h1 := (abs_le.1 ((abs_sub_le_dist p.1 p.2 y).trans (hS' p hp))).1
      have h2 := hb'.1 ⟨p, hp, rfl⟩ y
      simp only [sub_apply, const_apply]
      linarith
    exact ha'.2 hlb x
  refine dist_le hc fun x => abs_le.2 ⟨?_, ?_⟩
  · have := key S a b ha hb hS x
    linarith
  · have := key (Prod.swap '' S) b a (by rw [image_image]; exact hb)
      (by rw [image_image]; exact ha)
      (by rintro _ ⟨p, hp, rfl⟩; rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hS p hp) x
    linarith

/-- The underlying function of an element of `BM X` lies in the set `bX`. -/
theorem mem_bX (v : BM X) : v.toFun ∈ bX X := ⟨v.measurable', v.bdd'⟩

/-- Uniform convergence of the underlying functions is convergence in `BM X`. -/
theorem tendsto_of_tendstoUniformly {F : ℕ → BM X} {G : BM X}
    (h : TendstoUniformly (fun n => (F n).toFun) G.toFun atTop) : Tendsto F atTop (𝓝 G) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 h (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => (dist_le (half_pos hε).le fun x => ?_).trans_lt (half_lt_self hε)⟩
  rw [abs_sub_comm, ← Real.dist_eq]
  exact (hN n hn x).le

/-- Convergence in `BM X` is uniform convergence of the underlying functions. -/
theorem tendstoUniformly_of_tendsto {F : ℕ → BM X} {G : BM X} (h : Tendsto F atTop (𝓝 G)) :
    TendstoUniformly (fun n => (F n).toFun) G.toFun atTop := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendsto_nhds.1 h ε hε] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_sub_le_dist _ _ x).trans_lt hn

/-- A self-map of `BM X` acting through a map `T'` of functions is globally stable when `T'` is
globally stable on `bX` with uniform convergence (as in Lemma 1.3.1). -/
theorem globallyStable_of_bX {T : BM X → BM X} {T' : (X → ℝ) → X → ℝ}
    (hT : ∀ v, (T v).toFun = T' v.toFun)
    (h : ∃ u ∈ bX X, T' u = u ∧ (∀ w ∈ bX X, T' w = w → w = u) ∧
      ∀ v ∈ bX X, TendstoUniformly (fun n => T'^[n] v) u atTop) : GloballyStable T := by
  obtain ⟨u, hu, hfix, huniq, hlim⟩ := h
  have hit : ∀ n v, (T^[n] v).toFun = T'^[n] v.toFun := by
    intro n
    induction n with
    | zero => exact fun v => rfl
    | succ n ih =>
      intro v
      rw [iterate_succ_apply', iterate_succ_apply', hT, ih]
  refine ⟨⟨u, hu.1, hu.2⟩, ext fun x => by rw [hT]; exact congrFun hfix x, fun w hw =>
    ext fun x => congrFun (huniq w.toFun (mem_bX w) (by rw [← hT]; exact congrArg toFun hw)) x,
    fun v => tendsto_of_tendstoUniformly ?_⟩
  have : (fun n => (T^[n] v).toFun) = fun n => T'^[n] v.toFun := funext fun n => hit n v
  rw [this]
  exact hlim v.toFun (mem_bX v)

end BM

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Contractions and Blackwell's condition in Banach lattices

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.1.1 (pp. 124–126), with §A.2.2.2 and
§A.5.3.3–A.5.3.4.

A Banach lattice is a complete normed lattice-ordered vector space with a lattice (solid) norm:
in Mathlib, `NormedAddCommGroup E`, `Lattice E`, `HasSolidNorm E`, `IsOrderedAddMonoid E`,
`NormedSpace ℝ E` and `CompleteSpace E`, with scalars acting monotonically (`PosSMulMono ℝ E`).

* **Theorem 4.1.1** (with Theorem A.2.8): an eventually contracting self-map of a complete metric
  space (in particular a closed subset of a Banach space) is globally stable, with geometric
  convergence.
* Normalized order units (§A.5.3.4) and **Proposition A.5.23**: the norm is then sup- and
  inf-nonexpansive, also on any subset closed under `v ↦ v + κe`, `κ ≥ 0`.
* **Lemma 4.1.2** (Blackwell's condition) and **Theorem 4.1.3** (optimality for Blackwell ADPs).
* Certainty equivalent operators and **Exercise 4.1.2**.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-! ### Eventually contracting maps -/

/-- Geometric rates: `λ^⌊m/n⌋ ≤ μ⁻¹ (μ^{1/n})^m` with `μ = max λ (1/2)`. -/
theorem pow_div_le_geometric {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) {n : ℕ} (hn : 0 < n)
    (m : ℕ) :
    lam ^ (m / n) ≤ (max lam (1 / 2))⁻¹ * ((max lam (1 / 2)) ^ (1 / (n : ℝ))) ^ m := by
  set μ := max lam (1 / 2) with hμ
  have hμ0 : 0 < μ := lt_max_of_lt_right (by norm_num)
  have hμ1 : μ < 1 := max_lt hlam1 (by norm_num)
  have h1 : lam ^ (m / n) ≤ μ ^ (m / n) := pow_le_pow_left₀ hlam0 (le_max_left _ _) _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (m : ℝ) / n - 1 ≤ ((m / n : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := m) hn
    have : (m : ℝ) < ((m / n : ℕ) : ℝ) * n + n := by exact_mod_cast h
    rw [div_sub_one hn'.ne', div_le_iff₀ hn']
    linarith
  have h2 : μ ^ (m / n) ≤ μ ^ ((m : ℝ) / n - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hμ0 hμ1.le hq
  have h3 : μ ^ ((m : ℝ) / n - 1) = μ⁻¹ * (μ ^ (1 / (n : ℝ))) ^ m := by
    rw [Real.rpow_sub hμ0, Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul hμ0.le]
    field_simp
  linarith [h3 ▸ h2]

/-- **Theorem 4.1.1** (p. 124), with Theorem A.2.8: if `Sⁿ` is a contraction of modulus `λ < 1` on a
complete metric space, then `S` is globally stable, and `d(S^m v, v*) = 𝕆(β^m)` for some
`β ∈ (0, 1)`. -/
theorem theorem_4_1_1 {V : Type*} [MetricSpace V] [CompleteSpace V] [Nonempty V] {S : V → V}
    {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hS : ∀ u v, dist (S^[n] u) (S^[n] v) ≤ lam * dist u v) :
    GloballyStable S ∧ ∃ vstar, S vstar = vstar ∧ ∃ β, 0 < β ∧ β < 1 ∧
      ∀ v, ∃ C, ∀ m, dist (S^[m] v) vstar ≤ C * β ^ m := by
  have hc : ContractingWith ⟨lam, hlam0⟩ S^[n] :=
    ⟨hlam1, LipschitzWith.of_dist_le_mul fun u v => hS u v⟩
  set vstar := hc.fixedPoint _
  have hfixn : IsFixedPt S^[n] vstar := hc.fixedPoint_isFixedPt
  have hfix : S vstar = vstar := ContractingWith.isFixedPt_fixedPoint_iterate hc
  set μ := max lam (1 / 2)
  have hμ0 : 0 < μ := lt_max_of_lt_right (by norm_num)
  have hμ1 : μ < 1 := max_lt hlam1 (by norm_num)
  set β := μ ^ (1 / (n : ℝ))
  have hβ0 : 0 < β := Real.rpow_pos_of_pos hμ0 _
  have hβ1 : β < 1 := Real.rpow_lt_one hμ0.le hμ1 (by positivity)
  -- the rate
  have hrate : ∀ v, ∃ C, ∀ m, dist (S^[m] v) vstar ≤ C * β ^ m := by
    intro v
    set C₀ := (Finset.range n).sup' ⟨0, Finset.mem_range.2 hn⟩ fun r => dist (S^[r] v) vstar
    have hC₀ : ∀ r < n, dist (S^[r] v) vstar ≤ C₀ := fun r hr =>
      Finset.le_sup' (fun r => dist (S^[r] v) vstar) (Finset.mem_range.2 hr)
    have hC₀0 : 0 ≤ C₀ := dist_nonneg.trans (hC₀ 0 hn)
    refine ⟨C₀ * μ⁻¹, fun m => ?_⟩
    have hm : m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
    have hblock : ∀ q, dist (S^[n * q + m % n] v) vstar ≤ lam ^ q * C₀ := by
      intro q
      induction q with
      | zero => simpa using hC₀ (m % n) (Nat.mod_lt _ hn)
      | succ q ih =>
        have : S^[n * (q + 1) + m % n] v = S^[n] (S^[n * q + m % n] v) := by
          rw [← iterate_add_apply]
          congr 1
          ring
        rw [this, ← hfixn.eq]
        calc dist (S^[n] (S^[n * q + m % n] v)) (S^[n] vstar)
            ≤ lam * dist (S^[n * q + m % n] v) vstar := hS _ _
          _ ≤ lam * (lam ^ q * C₀) := mul_le_mul_of_nonneg_left ih hlam0
          _ = lam ^ (q + 1) * C₀ := by ring
    calc dist (S^[m] v) vstar = dist (S^[n * (m / n) + m % n] v) vstar := by rw [← hm]
      _ ≤ lam ^ (m / n) * C₀ := hblock _
      _ ≤ (μ⁻¹ * β ^ m) * C₀ := mul_le_mul_of_nonneg_right
          (pow_div_le_geometric hlam0 hlam1 hn m) hC₀0
      _ = C₀ * μ⁻¹ * β ^ m := by ring
  refine ⟨⟨vstar, hfix, fun w hw => hc.fixedPoint_unique (hw.iterate n), fun v => ?_⟩,
    vstar, hfix, β, hβ0, hβ1, hrate⟩
  obtain ⟨C, hC⟩ := hrate v
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hC ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C

/-! ### Normalized order units -/

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E]

/-- `e` is a normalized order unit (§A.5.3.4): `e ≥ 0`, `‖e‖ = 1` and `|v| ≤ ‖v‖e` for all `v`. -/
def IsNormalizedOrderUnit (e : E) : Prop := 0 ≤ e ∧ ‖e‖ = 1 ∧ ∀ v : E, |v| ≤ ‖v‖ • e

variable {e : E}

omit [HasSolidNorm E] in
theorem IsNormalizedOrderUnit.smul_mono (he : IsNormalizedOrderUnit e) {a b : ℝ} (h : a ≤ b) :
    a • e ≤ b • e := by
  have : 0 ≤ (b - a) • e := smul_nonneg (sub_nonneg.2 h) he.1
  rw [sub_smul] at this
  exact sub_nonneg.1 this

omit [HasSolidNorm E] [PosSMulMono ℝ E] in
theorem IsNormalizedOrderUnit.le_add (he : IsNormalizedOrderUnit e) (v w : E) :
    v ≤ w + ‖v - w‖ • e :=
  sub_le_iff_le_add'.1 ((le_abs_self (v - w)).trans (he.2.2 (v - w)))

/-- `a ≤ b + ce` and `b ≤ a + ce` give `‖a − b‖ ≤ c`. -/
theorem IsNormalizedOrderUnit.norm_sub_le (he : IsNormalizedOrderUnit e) {a b : E} {c : ℝ}
    (hc : 0 ≤ c) (h1 : a ≤ b + c • e) (h2 : b ≤ a + c • e) : ‖a - b‖ ≤ c := by
  have habs : |a - b| ≤ c • e := by
    rw [abs]
    refine sup_le (sub_le_iff_le_add'.2 h1) ?_
    rw [neg_sub]
    exact sub_le_iff_le_add'.2 h2
  have hce : 0 ≤ c • e := smul_nonneg hc he.1
  have h := norm_le_norm_of_abs_le_abs (habs.trans_eq (abs_of_nonneg hce).symm)
  rwa [norm_smul, he.2.1, mul_one, Real.norm_of_nonneg hc] at h

/-- **Proposition A.5.23** (p. 382): with a normalized order unit, the norm is sup-nonexpansive. -/
theorem isSupNonexpansive (he : IsNormalizedOrderUnit e) :
    IsSupNonexpansive (dist : E → E → ℝ) := by
  have key : ∀ (S : Set (E × E)) (a b : E) (c : ℝ), IsLUB (Prod.fst '' S) a →
      IsLUB (Prod.snd '' S) b → (∀ p ∈ S, dist p.1 p.2 ≤ c) → a ≤ b + c • e := by
    intro S a b c ha hb hS
    refine ha.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    calc p.1 ≤ p.2 + ‖p.1 - p.2‖ • e := he.le_add _ _
      _ ≤ b + c • e := add_le_add (hb.1 ⟨p, hp, rfl⟩)
          (he.smul_mono (by rw [← dist_eq_norm]; exact hS p hp))
  intro S a b c hc ha hb hS
  rw [dist_eq_norm]
  exact he.norm_sub_le hc (key S a b c ha hb hS) (key (Prod.swap '' S) b a c
    (by rw [image_image]; exact hb) (by rw [image_image]; exact ha)
    (by rintro _ ⟨p, hp, rfl⟩; rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hS p hp))

/-- With a normalized order unit the norm is inf-nonexpansive too. -/
theorem isInfNonexpansive (he : IsNormalizedOrderUnit e) :
    IsInfNonexpansive (dist : E → E → ℝ) := by
  have key : ∀ (S : Set (E × E)) (a b : E) (c : ℝ), IsGLB (Prod.fst '' S) a →
      IsGLB (Prod.snd '' S) b → (∀ p ∈ S, dist p.1 p.2 ≤ c) → b ≤ a + c • e := by
    intro S a b c ha hb hS
    have hlb : b - c • e ∈ lowerBounds (Prod.fst '' S) := by
      rintro _ ⟨p, hp, rfl⟩
      have h1 := he.le_add p.2 p.1
      rw [← dist_eq_norm, dist_comm] at h1
      have h2 := hb.1 ⟨p, hp, rfl⟩
      have h3 := he.smul_mono (hS p hp)
      rw [sub_le_iff_le_add]
      calc b ≤ p.2 := h2
        _ ≤ p.1 + dist p.1 p.2 • e := h1
        _ ≤ p.1 + c • e := add_le_add le_rfl h3
    exact sub_le_iff_le_add.1 (ha.2 hlb)
  intro S a b c hc ha hb hS
  rw [dist_eq_norm]
  exact he.norm_sub_le hc (key (Prod.swap '' S) b a c (by rw [image_image]; exact hb)
    (by rw [image_image]; exact ha)
    (by rintro _ ⟨p, hp, rfl⟩; rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hS p hp))
    (key S a b c ha hb hS)

/-- **Proposition A.5.23** on a subset `V` closed under `v ↦ v + κe` (`κ ≥ 0`), for instance an
increasing subset: the induced metric is sup-nonexpansive for the order of `V`. -/
theorem isSupNonexpansive_subtype (he : IsNormalizedOrderUnit e) {Vs : Set E}
    (hV : ∀ v ∈ Vs, ∀ κ : ℝ, 0 ≤ κ → v + κ • e ∈ Vs) :
    IsSupNonexpansive (dist : Vs → Vs → ℝ) := by
  have key : ∀ (S : Set (Vs × Vs)) (a b : Vs) (c : ℝ), 0 ≤ c → IsLUB (Prod.fst '' S) a →
      IsLUB (Prod.snd '' S) b → (∀ p ∈ S, dist p.1 p.2 ≤ c) → (a : E) ≤ b + c • e := by
    intro S a b c hc ha hb hS
    have hub : (⟨b + c • e, hV _ b.2 c hc⟩ : Vs) ∈ upperBounds (Prod.fst '' S) := by
      rintro _ ⟨p, hp, rfl⟩
      change (p.1 : E) ≤ b + c • e
      calc (p.1 : E) ≤ p.2 + ‖(p.1 : E) - p.2‖ • e := he.le_add _ _
        _ ≤ b + c • e := add_le_add (hb.1 ⟨p, hp, rfl⟩)
            (he.smul_mono (by rw [← dist_eq_norm, ← Subtype.dist_eq]; exact hS p hp))
    exact ha.2 hub
  intro S a b c hc ha hb hS
  rw [Subtype.dist_eq, dist_eq_norm]
  exact he.norm_sub_le hc (key S a b c hc ha hb hS) (key (Prod.swap '' S) b a c hc
    (by rw [image_image]; exact hb) (by rw [image_image]; exact ha)
    (by rintro _ ⟨p, hp, rfl⟩; rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hS p hp))

/-! ### Blackwell's condition -/

/-- **Lemma 4.1.2** (p. 125): an order preserving `S` with `S(v + κe) ≤ Sv + λκe` for all `κ ≥ 0`
is a contraction of modulus `λ`. -/
theorem lemma_4_1_2 (he : IsNormalizedOrderUnit e) {S : E → E} (hS : Monotone S) {lam : ℝ}
    (hlam : 0 ≤ lam) (hB : ∀ v (κ : ℝ), 0 ≤ κ → S (v + κ • e) ≤ S v + (lam * κ) • e) (v w : E) :
    ‖S v - S w‖ ≤ lam * ‖v - w‖ := by
  refine he.norm_sub_le (mul_nonneg hlam (norm_nonneg _)) ?_ ?_
  · exact (hS (he.le_add v w)).trans (hB w _ (norm_nonneg _))
  · have := (hS (he.le_add w v)).trans (hB v _ (norm_nonneg _))
    rwa [norm_sub_rev] at this

/-- **Lemma 4.1.2** on a subset `V` closed under `v ↦ v + κe`: an order preserving self-map `S` of
`V` with `S(v + κe) ≤ Sv + λκe` is a contraction of modulus `λ` on `V`. -/
theorem lemma_4_1_2_subtype (he : IsNormalizedOrderUnit e) {Vs : Set E}
    (hV : ∀ v ∈ Vs, ∀ κ : ℝ, 0 ≤ κ → v + κ • e ∈ Vs) {S : Vs → Vs} (hS : Monotone S)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hB : ∀ v : Vs, ∀ (κ : ℝ) (hκ : 0 ≤ κ),
      (S ⟨v + κ • e, hV _ v.2 κ hκ⟩ : E) ≤ S v + (lam * κ) • e) (v w : Vs) :
    dist (S v) (S w) ≤ lam * dist v w := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  refine he.norm_sub_le (mul_nonneg hlam (norm_nonneg _)) ?_ ?_
  · have h1 : (S v : E) ≤ S ⟨w + ‖(v : E) - w‖ • e, hV _ w.2 _ (norm_nonneg _)⟩ :=
      hS (he.le_add (v : E) w)
    exact h1.trans (hB w _ (norm_nonneg _))
  · have h1 : (S w : E) ≤ S ⟨v + ‖(w : E) - v‖ • e, hV _ v.2 _ (norm_nonneg _)⟩ :=
      hS (he.le_add (w : E) v)
    have := h1.trans (hB v _ (norm_nonneg _))
    rwa [norm_sub_rev] at this

/-! ### Optimality for Blackwell ADPs -/

variable [CompleteSpace E]

/-- **Theorem 4.1.3** (p. 125): let `V ⊆ E` be closed and increasing (closure under `v ↦ v + κe`
suffices) and let every `T_σ` satisfy Blackwell's condition (4.4) with a common `λ < 1`. If
`(V, 𝕋)` is semi-regular on a nonempty closed `V₀`, then (i) the fundamental optimality properties
hold, (ii) `v* ∈ V₀` and (iii) VFI converges geometrically on `V₀`; if `(V, 𝕋)` is regular, OPI
and HPI converge. -/
theorem theorem_4_1_3 (he : IsNormalizedOrderUnit e) {Vs : Set E} (hcl : IsClosed Vs)
    (hV : ∀ v ∈ Vs, ∀ κ : ℝ, 0 ≤ κ → v + κ • e ∈ Vs) {P : Type*} (A : ADP Vs P) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : ∀ σ, ∀ v : Vs, ∀ (κ : ℝ) (hκ : 0 ≤ κ),
      (A.T σ ⟨v + κ • e, hV _ v.2 κ hκ⟩ : E) ≤ A.T σ v + (lam * κ) • e)
    {V₀ : Set Vs} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) := by
  have : CompleteSpace Vs := hcl.completeSpace_coe
  have hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ lam * dist v w := fun σ =>
    lemma_4_1_2_subtype he hV (A.mono σ) hlam0 (hB σ)
  exact ⟨_, ADP.theorem_3_1_5 (isSupNonexpansive_subtype he hV) hlam0 hlam1 hT hsr hne⟩

/-- **Theorem 4.1.3** with `V = E`. -/
theorem theorem_4_1_3_univ (he : IsNormalizedOrderUnit e) {P : Type*} (A : ADP E P) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : ∀ σ v (κ : ℝ), 0 ≤ κ → A.T σ (v + κ • e) ≤ A.T σ v + (lam * κ) • e)
    {V₀ : Set E} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) := by
  have hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ lam * dist v w := by
    intro σ v w
    rw [dist_eq_norm, dist_eq_norm]
    exact lemma_4_1_2 he (A.mono σ) hlam0 (hB σ) v w
  exact ⟨_, ADP.theorem_3_1_5 (isSupNonexpansive he) hlam0 hlam1 hT hsr hne⟩

/-! ### Certainty equivalent operators -/

/-- A certainty equivalent operator (p. 126): order preserving and `M(v + κe) = Mv + κe`. -/
def IsCertaintyEquivalent (e : E) (M : E → E) : Prop :=
  Monotone M ∧ ∀ v (κ : ℝ), 0 ≤ κ → M (v + κ • e) = M v + κ • e

/-- **Exercise 4.1.2** (p. 126): an ADP with `T_σ v = r_σ + βM_σ v`, `M_σ` certainty equivalent
operators and `0 ≤ β < 1`, satisfies (i)–(iii) of Theorem 4.1.3 when semi-regular on a nonempty
closed `V₀`, and OPI and HPI converge when it is regular. -/
theorem exercise_4_1_2 (he : IsNormalizedOrderUnit e) {P : Type*} (A : ADP E P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r : P → E) (M : P → E → E)
    (hM : ∀ σ, IsCertaintyEquivalent e (M σ)) (hT : ∀ σ v, A.T σ v = r σ + β • M σ v)
    {V₀ : Set E} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) :=
  theorem_4_1_3_univ he A hβ0 hβ1 (fun σ v κ hκ => by
    rw [hT, hT, (hM σ).2 v κ hκ, smul_add, smul_smul, add_assoc]) hsr hne

/-- **Exercise 4.1.2** on a closed subset `V` closed under `v ↦ v + κe`, with certainty equivalent
self-maps `M_σ` of `V`. -/
theorem exercise_4_1_2_subtype (he : IsNormalizedOrderUnit e) {Vs : Set E} (hcl : IsClosed Vs)
    (hV : ∀ v ∈ Vs, ∀ κ : ℝ, 0 ≤ κ → v + κ • e ∈ Vs) {P : Type*} (A : ADP Vs P) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (r : P → E) (M : P → Vs → Vs)
    (hM : ∀ σ, ∀ v : Vs, ∀ (κ : ℝ) (hκ : 0 ≤ κ),
      (M σ ⟨v + κ • e, hV _ v.2 κ hκ⟩ : E) = M σ v + κ • e)
    (hT : ∀ σ v, (A.T σ v : E) = r σ + β • (M σ v : E))
    {V₀ : Set Vs} (hsr : A.IsSemiRegular V₀) (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) :=
  theorem_4_1_3 he hcl hV A hβ0 hβ1 (fun σ v κ hκ => by
    rw [hT, hT, hM σ v κ hκ, smul_add, smul_smul, add_assoc]) hsr hne

end BanachLattice

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order contractions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.1.2 (pp. 126–131), with §A.4.3 and
§A.5.3.6.

`E` is a Banach lattice. A *discount operator* `D` on the positive cone `E₊` fixes `0`, is order
preserving and eventually contracting; `S` is an *order contraction of modulus `D`* when
`|Sv − Sw| ≤ D|v − w|` (4.6).

The value space `V` of an ADP is a complete metric poset carried into `E` by an isometric order
embedding `ι`: `V = E` with `ι = id`, or a closed subset with `ι` the inclusion.

* **Exercise 4.1.3**: `‖Dⁿh‖ ≤ λ‖h‖` on `E₊` for some `n` and `λ < 1`.
* The spectral radius of a bounded operator in Gelfand's form `ρ(A) = inf_k ‖Aᵏ‖^{1/k}`;
  **Exercise A.4.2** (`ρ(A) < 1` gives `‖Aᵏ‖ < 1` for some `k`) and **Example 4.1.1** (positive
  operators with `ρ < 1` are discount operators).
* **Theorem 4.1.4** (order contractions are globally stable, with geometric rate),
  **Example 4.1.2** and **Exercise 4.1.4** (Blackwell-type sufficient condition).
* **Theorems 4.1.5 and 4.1.6** (order contracting ADPs) and **Theorems 4.1.7 and 4.1.8**
  (additive ADPs with positive linear parts).
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E]

/-! ### Discount operators -/

/-- A discount operator on `E` (p. 127): a map `D` of the positive cone `E₊` into itself with
(i) `D0 = 0`, (ii) `D` order preserving and (iii) `D` eventually contracting on `E₊`. -/
def IsDiscountOperator (D : E → E) : Prop :=
  D 0 = 0 ∧ MapsTo D {h | 0 ≤ h} {h | 0 ≤ h} ∧ MonotoneOn D {h | 0 ≤ h} ∧
    ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧
      ∀ u, 0 ≤ u → ∀ v, 0 ≤ v → ‖D^[n] u - D^[n] v‖ ≤ lam * ‖u - v‖

omit [HasSolidNorm E] [IsOrderedAddMonoid E] [NormedSpace ℝ E] in
/-- **Exercise 4.1.3** (p. 127): a discount operator has `‖Dⁿh‖ ≤ λ‖h‖` on `E₊`, for some `n` and
`λ ∈ [0, 1)`. -/
theorem IsDiscountOperator.exercise_4_1_3 {D : E → E} (hD : IsDiscountOperator D) :
    ∃ n, 0 < n ∧ ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ h, 0 ≤ h → ‖D^[n] h‖ ≤ lam * ‖h‖ := by
  obtain ⟨h0, -, -, n, hn, lam, hlam0, hlam1, hc⟩ := hD
  refine ⟨n, hn, lam, hlam0, hlam1, fun h hh => ?_⟩
  have := hc h hh 0 le_rfl
  rwa [iterate_fixed h0, sub_zero, sub_zero] at this

omit [HasSolidNorm E] [IsOrderedAddMonoid E] [NormedSpace ℝ E] in
theorem IsDiscountOperator.iterate_nonneg {D : E → E} (hD : IsDiscountOperator D) (m : ℕ)
    {h : E} (hh : 0 ≤ h) : 0 ≤ D^[m] h :=
  hD.2.1.iterate m hh

omit [HasSolidNorm E] [IsOrderedAddMonoid E] [NormedSpace ℝ E] in
/-- `D^m` is order preserving on `E₊`. -/
theorem IsDiscountOperator.iterate_mono {D : E → E} (hD : IsDiscountOperator D) (m : ℕ)
    {h k : E} (hh : 0 ≤ h) (hk : 0 ≤ k) (hhk : h ≤ k) : D^[m] h ≤ D^[m] k := by
  induction m generalizing h k with
  | zero => exact hhk
  | succ m ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    exact ih (hD.2.1 hh) (hD.2.1 hk) (hD.2.2.1 hh hk hhk)

/-! ### Spectral radius and positive operators -/

/-- The spectral radius in Gelfand's form, `ρ(A) = inf_{k ≥ 1} ‖Aᵏ‖^{1/k}` (§A.4.3). -/
noncomputable def specRad (A : E →L[ℝ] E) : ℝ := ⨅ k : ℕ, ‖A ^ (k + 1)‖ ^ (1 / ((k : ℝ) + 1))

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- **Exercise A.4.2** (p. 367): if `ρ(A) < 1`, then `‖Aᵏ‖ < 1` for some `k ≥ 1`. -/
theorem exercise_A_4_2 {A : E →L[ℝ] E} (h : specRad A < 1) : ∃ k, 0 < k ∧ ‖A ^ k‖ < 1 := by
  obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt h
  refine ⟨k + 1, k.succ_pos, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  exact absurd hk (not_lt.2 (Real.one_le_rpow hge (by positivity)))

omit [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] in
/-- `ρ(A) ≤ ‖A‖`. -/
theorem specRad_le_norm (A : E →L[ℝ] E) : specRad A ≤ ‖A‖ :=
  (ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ 0).trans_eq (by simp)

/-- A positive linear operator: `v ≥ 0` implies `Av ≥ 0` (§A.5.2.2). -/
def IsPositiveOp (A : E →L[ℝ] E) : Prop := ∀ v, 0 ≤ v → 0 ≤ A v

omit [HasSolidNorm E] in
theorem IsPositiveOp.mono {A : E →L[ℝ] E} (hA : IsPositiveOp A) : Monotone A := fun v w h => by
  have := hA (w - v) (sub_nonneg.2 h)
  rwa [map_sub, sub_nonneg] at this

omit [HasSolidNorm E] in
/-- For a positive operator, `|Av| ≤ A|v|`. -/
theorem IsPositiveOp.abs_le {A : E →L[ℝ] E} (hA : IsPositiveOp A) (v : E) : |A v| ≤ A |v| := by
  rw [abs]
  refine sup_le (hA.mono (le_abs_self v)) ?_
  rw [← map_neg]
  exact hA.mono (neg_le_abs v)

omit [HasSolidNorm E] [IsOrderedAddMonoid E] in
theorem IsPositiveOp.iterate {A : E →L[ℝ] E} (hA : IsPositiveOp A) (n : ℕ) :
    IsPositiveOp (A ^ n) := by
  induction n with
  | zero => exact fun v hv => hv
  | succ n ih =>
    intro v hv
    rw [pow_succ]
    exact ih _ (hA v hv)

omit [HasSolidNorm E] in
/-- **Example 4.1.1** (p. 127): a positive linear operator with `ρ(D) < 1` is a discount
operator. -/
theorem example_4_1_1 {D : E →L[ℝ] E} (hD : IsPositiveOp D) (hρ : specRad D < 1) :
    IsDiscountOperator (D : E → E) := by
  obtain ⟨k, hk, hlt⟩ := exercise_A_4_2 hρ
  refine ⟨map_zero D, fun h hh => hD h hh, fun h _ k' _ hhk => hD.mono hhk, k, hk, ‖D ^ k‖,
    norm_nonneg _, hlt, fun u _ v _ => ?_⟩
  rw [← FunLike.coe_pow_eq_iterate, ← map_sub]
  exact (D ^ k).le_opNorm (u - v)

/-! ### Order contractions on a value space embedded in `E` -/

variable {V : Type*} [MetricSpace V] [PartialOrder V]

/-- `ι : V → E` is an isometric order embedding. -/
def IsIsoOrderEmbedding (ι : V → E) : Prop :=
  (∀ v w, dist v w = ‖ι v - ι w‖) ∧ ∀ v w, v ≤ w ↔ ι v ≤ ι w

/-- `S` is an order contraction of modulus `D` (4.6): `D` is a discount operator and
`|Sv − Sw| ≤ D|v − w|`, distances being measured in `E` through `ι`. -/
def IsOrderContraction (ι : V → E) (S : V → V) (D : E → E) : Prop :=
  IsDiscountOperator D ∧ ∀ v w, |ι (S v) - ι (S w)| ≤ D |ι v - ι w|

omit [MetricSpace V] [PartialOrder V] [HasSolidNorm E] [NormedSpace ℝ E] in
theorem IsOrderContraction.iterate {ι : V → E} {S : V → V} {D : E → E}
    (h : IsOrderContraction ι S D) (m : ℕ) (v w : V) :
    |ι (S^[m] v) - ι (S^[m] w)| ≤ D^[m] |ι v - ι w| := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
    exact (h.2 _ _).trans (h.1.2.2.1 (abs_nonneg _) (h.1.iterate_nonneg m (abs_nonneg _)) ih)

omit [NormedSpace ℝ E] in
/-- **Theorem 4.1.4** (p. 127): an order contraction of a closed (complete) `V` is globally stable,
with `‖S^m v − v*‖ = 𝕆(β^m)` for some `β ∈ (0, 1)`. -/
theorem theorem_4_1_4 [CompleteSpace V] [Nonempty V] {ι : V → E} (hι : IsIsoOrderEmbedding ι)
    {S : V → V} {D : E → E} (h : IsOrderContraction ι S D) :
    GloballyStable S ∧ ∃ vstar, S vstar = vstar ∧ ∃ β, 0 < β ∧ β < 1 ∧
      ∀ v, ∃ C, ∀ m, dist (S^[m] v) vstar ≤ C * β ^ m := by
  obtain ⟨n, hn, lam, hlam0, hlam1, hD⟩ := h.1.exercise_4_1_3
  refine theorem_4_1_1 hn hlam0 hlam1 fun u v => ?_
  rw [hι.1, hι.1]
  calc ‖ι (S^[n] u) - ι (S^[n] v)‖ ≤ ‖D^[n] |ι u - ι v|‖ :=
        norm_le_norm_of_abs_le_abs ((h.iterate n u v).trans
          (le_abs_self _))
    _ ≤ lam * ‖|ι u - ι v|‖ := hD _ (abs_nonneg _)
    _ = lam * ‖ι u - ι v‖ := by rw [norm_abs_eq_norm]

omit [MetricSpace V] [PartialOrder V] [HasSolidNorm E] in
/-- **Example 4.1.2** (p. 128): if `D` is positive linear with `ρ(D) < 1` and
`|Sv − Sw| ≤ |Dv − Dw|`, then `S` is an order contraction of modulus `D`. -/
theorem example_4_1_2 {ι : V → E} {S : V → V} {D : E →L[ℝ] E} (hD : IsPositiveOp D)
    (hρ : specRad D < 1) (h : ∀ v w, |ι (S v) - ι (S w)| ≤ |D (ι v) - D (ι w)|) :
    IsOrderContraction ι S D :=
  ⟨example_4_1_1 hD hρ, fun v w => (h v w).trans (by rw [← map_sub]; exact hD.abs_le _)⟩

omit [HasSolidNorm E] [NormedSpace ℝ E] in
/-- **Exercise 4.1.4** (p. 128): on `V = E`, an order preserving `S` with `S(v + h) ≤ Sv + Dh`
for all `h ≥ 0`, `D` a discount operator, is an order contraction of modulus `D`. -/
theorem exercise_4_1_4 {S : E → E} (hS : Monotone S) {D : E → E} (hD : IsDiscountOperator D)
    (h : ∀ v h, 0 ≤ h → S (v + h) ≤ S v + D h) : IsOrderContraction id S D := by
  refine ⟨hD, fun v w => ?_⟩
  simp only [id]
  have key : ∀ a b : E, S a - S b ≤ D |a - b| := fun a b => by
    have h1 : a ≤ b + |a - b| := by
      have := le_abs_self (a - b)
      rw [sub_le_iff_le_add'] at this
      exact this
    exact sub_le_iff_le_add'.2 ((hS h1).trans (h b _ (abs_nonneg _)))
  rw [abs]
  refine sup_le (key v w) ?_
  rw [neg_sub, abs_sub_comm]
  exact key w v

/-! ### Order contracting ADPs -/

variable [OrderClosedTopology V] [CompleteSpace V] [Nonempty V] {P : Type*}

omit [NormedSpace ℝ E] in
/-- **Theorem 4.1.5** (p. 128): if `(V, 𝕋)` is regular, `𝕋` is finite and every `T_σ` is an order
contraction, then (i) the fundamental optimality properties hold and (ii) VFI, OPI and HPI all
converge. -/
theorem theorem_4_1_5 {ι : V → E} (hι : IsIsoOrderEmbedding ι) (A : ADP V P)
    (hr : A.Regular) (hfin : A.IsFinite) (D : P → E → E)
    (hD : ∀ σ, IsOrderContraction ι (A.T σ) (D σ)) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar := by
  have hgs : A.IsGloballyStable := fun σ => (theorem_4_1_4 hι (hD σ)).1
  exact ⟨_, ADP.corollary_3_1_3 hr hgs hfin⟩

omit [HasSolidNorm E] [NormedSpace ℝ E] [OrderClosedTopology V] [CompleteSpace V] [Nonempty V] in
/-- Under a common modulus `D`, the Bellman operator is an order contraction on `V_G`
(proof of Theorem 4.1.6, (4.9)). -/
theorem bellman_orderContraction {ι : V → E} (hι : IsIsoOrderEmbedding ι) (A : ADP V P)
    {D : E → E} (hD : ∀ σ v w, |ι (A.T σ v) - ι (A.T σ w)| ≤ D |ι v - ι w|) {v w : V}
    (hv : v ∈ A.VG) (hw : w ∈ A.VG) :
    |ι (A.bellman v) - ι (A.bellman w)| ≤ D |ι v - ι w| := by
  have key : ∀ a b, a ∈ A.VG → b ∈ A.VG →
      ι (A.bellman a) - ι (A.bellman b) ≤ D |ι a - ι b| := by
    intro a b ha hb
    have h1 : ι (A.T (A.greedy a) b) ≤ ι (A.bellman b) :=
      (hι.2 _ _).1 (A.T_le_bellman _ hb)
    calc ι (A.bellman a) - ι (A.bellman b) ≤ ι (A.T (A.greedy a) a) - ι (A.T (A.greedy a) b) :=
          sub_le_sub le_rfl h1
      _ ≤ |ι (A.T (A.greedy a) a) - ι (A.T (A.greedy a) b)| := le_abs_self _
      _ ≤ D |ι a - ι b| := hD _ a b
  rw [abs]
  refine sup_le (key v w hv hw) ?_
  rw [neg_sub, abs_sub_comm]
  exact key w v hw hv

omit [NormedSpace ℝ E] in
/-- **Theorem 4.1.6** (p. 129): if every `T_σ` is an order contraction of a common modulus `D` and
`(V, 𝕋)` is semi-regular on a nonempty closed `V₀`, then (i) the fundamental optimality properties
hold, (ii) `v* ∈ V₀` and (iii) VFI converges geometrically on `V₀`; if `(V, 𝕋)` is also regular,
OPI and HPI converge. -/
theorem theorem_4_1_6 {ι : V → E} (hι : IsIsoOrderEmbedding ι) (A : ADP V P) {D : E → E}
    (hD : ∀ σ, IsOrderContraction ι (A.T σ) D) {V₀ : Set V} (hsr : A.IsSemiRegular V₀)
    (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) := by
  have hgs : A.IsGloballyStable := fun σ => (theorem_4_1_4 hι (hD σ)).1
  obtain ⟨hcl, hsub, hmaps⟩ := hsr
  have : CompleteSpace V₀ := hcl.completeSpace_coe
  have : Nonempty V₀ := hne.to_subtype
  obtain ⟨σ₀⟩ := A.nonempty
  -- the Bellman operator restricted to `V₀` is an order contraction
  let T₀ : V₀ → V₀ := fun v => ⟨A.bellman v, hmaps v.2⟩
  have hι₀ : IsIsoOrderEmbedding (fun v : V₀ => ι v) :=
    ⟨fun v w => (Subtype.dist_eq v w).trans (hι.1 v w), fun v w => hι.2 v w⟩
  have hT₀ : IsOrderContraction (fun v : V₀ => ι v) T₀ D :=
    ⟨(hD σ₀).1, fun v w => bellman_orderContraction hι A (fun σ => (hD σ).2) (hsub v.2)
      (hsub w.2)⟩
  obtain ⟨-, vbar, hvbar, β, hβ0, hβ1, hrate⟩ := theorem_4_1_4 hι₀ hT₀
  have hfix : A.bellman vbar = vbar := congrArg Subtype.val hvbar
  have hFO : A.FundamentalOptimality hgs.wellPosed :=
    hgs.isOrderStable.fundamentalOptimality (hsub vbar.2)
      ((A.solvesBellman_iff (hsub vbar.2)).2 hfix)
  obtain ⟨-, ⟨v', hv', -, -, huniq⟩, -⟩ := id hFO
  have hvs : A.IsValueFunction vbar := by
    rw [huniq vbar (hsub vbar.2) ((A.solvesBellman_iff (hsub vbar.2)).2 hfix)]
    exact hv'
  have hsemi : Semiconj Subtype.val T₀ A.bellman := fun _ => rfl
  refine ⟨hgs.wellPosed, hFO, vbar, vbar.2, ⟨hvs, β, hβ0, hβ1, fun v hv => ?_⟩, fun hr g hg => ?_⟩
  · obtain ⟨C, hC⟩ := hrate ⟨v, hv⟩
    refine ⟨C, fun m => ?_⟩
    have h2 : (T₀^[m] ⟨v, hv⟩ : V) = A.bellman^[m] v := (hsemi.iterate_right m) ⟨v, hv⟩
    rw [← h2, ← Subtype.dist_eq]
    exact hC m
  · obtain ⟨-, w, hw, -, hconv⟩ := ADP.theorem_3_1_2 hr hgs hfix
    rw [hvs.unique hw]
    exact hconv g hg

/-! ### Order contractive linear models -/

/-- An additive ADP with positive linear parts: `T_σ v = r_σ + K_σ v` (4.1), read through `ι`. -/
def IsAdditive {P : Type*} (ι : V → E) (A : ADP V P) (r : P → E) (K : P → E →L[ℝ] E) : Prop :=
  (∀ σ, IsPositiveOp (K σ)) ∧ ∀ σ v, ι (A.T σ v) = r σ + K σ (ι v)

omit [MetricSpace V] [OrderClosedTopology V] [CompleteSpace V] [Nonempty V] [HasSolidNorm E] in
theorem IsAdditive.abs_sub {ι : V → E} {A : ADP V P} {r : P → E} {K : P → E →L[ℝ] E}
    (h : IsAdditive ι A r K) (σ : P) (v w : V) :
    |ι (A.T σ v) - ι (A.T σ w)| ≤ K σ |ι v - ι w| := by
  rw [h.2, h.2, add_sub_add_left_eq_sub, ← map_sub]
  exact (h.1 σ).abs_le _

/-- **Theorem 4.1.7** (p. 130): a regular additive ADP `T_σ v = r_σ + K_σ v` with `K_σ` positive,
`ρ(K_σ) < 1` and `𝕋` finite satisfies (i) the fundamental optimality properties and (ii)
convergence of VFI, OPI and HPI. -/
theorem theorem_4_1_7 {ι : V → E} (hι : IsIsoOrderEmbedding ι) (A : ADP V P) (hr : A.Regular)
    (hfin : A.IsFinite) {r : P → E} {K : P → E →L[ℝ] E} (hadd : IsAdditive ι A r K)
    (hρ : ∀ σ, specRad (K σ) < 1) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar :=
  theorem_4_1_5 hι A hr hfin (fun σ => K σ) fun σ =>
    ⟨example_4_1_1 (hadd.1 σ) (hρ σ), hadd.abs_sub σ⟩

/-- **Theorem 4.1.8** (p. 130): an additive ADP with positive `K_σ ≤ D` on `E₊` for a discount
operator `D`, semi-regular on a nonempty closed `V₀`, satisfies (i)–(iii) of Theorem 4.1.6; if
it is regular, OPI and HPI converge. -/
theorem theorem_4_1_8 {ι : V → E} (hι : IsIsoOrderEmbedding ι) (A : ADP V P) {r : P → E}
    {K : P → E →L[ℝ] E} (hadd : IsAdditive ι A r K) {D : E → E} (hD : IsDiscountOperator D)
    (hKD : ∀ σ h, 0 ≤ h → K σ h ≤ D h) {V₀ : Set V} (hsr : A.IsSemiRegular V₀)
    (hne : V₀.Nonempty) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧ ∃ vstar ∈ V₀, A.VFIGeometric V₀ vstar ∧
      (A.Regular → ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar) :=
  theorem_4_1_6 hι A (fun σ => ⟨hD, fun v w => (hadd.abs_sub σ v w).trans
    (hKD σ _ (abs_nonneg _))⟩) hsr hne

end BanachLattice

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Operators on `bX`

Bounded linear operators on the Banach lattice `bX = BM X` used in the applications of §4.2, and
**Exercise 4.1.1** (Harrison and Kreps).

* Scalars act monotonically on `bX`, and `𝟙` is a normalized order unit when `X ≠ ∅` (§A.5.3.4).
* The Markov operator `(Pv)(x) = ∫ v(x')P(x, dx')` of a stochastic kernel and the multiplication
  operator `v ↦ hv` of a bounded measurable `h` are bounded positive operators.
* **Exercise 4.1.1** (p. 125): `(Sp)(x) = β max_{i ∈ I} ∫ [p(x') + g(x')]P_i(x, dx')` is a
  contraction of modulus `β` on `bX`, by Lemma 4.1.2.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

namespace BM

variable {X : Type*} [MeasurableSpace X]

/-- Nonnegative scalars act monotonically on `bX`. -/
theorem posSMulMono : PosSMulMono ℝ (BM X) :=
  ⟨fun _ ha _ _ h x => by
    simp only [smul_apply]
    exact mul_le_mul_of_nonneg_left (h x) ha⟩

attribute [local instance] posSMulMono

theorem one_apply (x : X) : (BM.const 1 : BM X).toFun x = 1 := rfl

/-- `𝟙` is a normalized order unit of `bX` when `X` is nonempty. -/
theorem isNormalizedOrderUnit_one [Nonempty X] :
    BanachLattice.IsNormalizedOrderUnit (BM.const 1 : BM X) := by
  refine ⟨fun _ => zero_le_one, le_antisymm (norm_le zero_le_one fun _ => by simp) ?_,
    fun v x => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty X›
    simpa using abs_le_norm (BM.const 1 : BM X) x
  · simp only [abs_apply, smul_apply, const_apply, mul_one]
    exact abs_le_norm v x

/-! ### The Markov operator -/

variable (P : Kernel X X) [IsMarkovKernel P]

/-- The Markov operator of a stochastic kernel on `bX`. -/
noncomputable def markovLin : BM X →ₗ[ℝ] BM X where
  toFun f := ⟨markovOp P f.toFun, measurable_markovOp P f.measurable',
    ⟨‖f‖, abs_markovOp_le P (abs_le_norm f)⟩⟩
  map_add' f g := ext fun x => congrFun (markovOp_add P (mem_bX f) (mem_bX g)) x
  map_smul' a f := ext fun x => congrFun (markovOp_smul P a f.toFun) x

/-- The Markov operator as a bounded linear operator, `‖P‖ ≤ 1`. -/
noncomputable def markovCLM : BM X →L[ℝ] BM X :=
  (markovLin P).mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_le (norm_nonneg f) fun x => abs_markovOp_le P (abs_le_norm f) x

theorem markovCLM_apply (f : BM X) (x : X) :
    (markovCLM P f).toFun x = markovOp P f.toFun x := rfl

theorem markovCLM_isPositive : BanachLattice.IsPositiveOp (markovCLM P) := fun f hf x => by
  rw [markovCLM_apply]
  have := markovOp_mono P (const_mem_bX 0) (mem_bX f) hf x
  rwa [markovOp_const] at this

theorem markovCLM_const (c : ℝ) : markovCLM P (BM.const c) = BM.const c :=
  ext fun x => congrFun (markovOp_const P c) x

/-! ### Multiplication operators -/

/-- Multiplication by `h ∈ bX`, as a linear map. -/
noncomputable def mulLin (h : BM X) : BM X →ₗ[ℝ] BM X where
  toFun f := ⟨fun x => h.toFun x * f.toFun x, h.measurable'.mul f.measurable',
    ⟨‖h‖ * ‖f‖, fun x => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_norm h x) (abs_le_norm f x) (abs_nonneg _) (norm_nonneg _)⟩⟩
  map_add' _ _ := ext fun _ => mul_add _ _ _
  map_smul' a f := ext fun x => by
    simp only [smul_apply, RingHom.id_apply]
    ring

/-- Multiplication by `h ∈ bX` as a bounded linear operator, `‖h·‖ ≤ ‖h‖`. -/
noncomputable def mulCLM (h : BM X) : BM X →L[ℝ] BM X :=
  (mulLin h).mkContinuous ‖h‖ fun f => norm_le (by positivity) fun x => by
    change |h.toFun x * f.toFun x| ≤ ‖h‖ * ‖f‖
    rw [abs_mul]
    exact mul_le_mul (abs_le_norm h x) (abs_le_norm f x) (abs_nonneg _) (norm_nonneg _)

theorem mulCLM_apply (h f : BM X) (x : X) :
    (mulCLM h f).toFun x = h.toFun x * f.toFun x := rfl

theorem mulCLM_isPositive {h : BM X} (hh : 0 ≤ h) : BanachLattice.IsPositiveOp (mulCLM h) :=
  fun _ hf x => mul_nonneg (hh x) (hf x)

end BM

/-! ### Exercise 4.1.1 -/

variable {X : Type*} [MeasurableSpace X]

/-- `max_i (fᵢ + κ) = max_i fᵢ + κ`. -/
theorem sup'_add_const {I : Type*} (s : Finset I) (hs : s.Nonempty) (f : I → ℝ) (κ : ℝ) :
    s.sup' hs (fun i => f i + κ) = s.sup' hs f + κ := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => add_le_add_left (Finset.le_sup' f hi) κ) ?_
  have : s.sup' hs f ≤ s.sup' hs (fun i => f i + κ) - κ := Finset.sup'_le _ _ fun i hi =>
    le_sub_iff_add_le.2 (Finset.le_sup' (fun i => f i + κ) hi)
  linarith

/-- The Harrison–Kreps operator `(Sp)(x) = β max_{i ∈ I} ∫ [p(x') + g(x')]P_i(x, dx')`, for a
finite nonempty family of stochastic kernels. -/
noncomputable def harrisonKreps {I : Type*} [Fintype I] [Nonempty I] (Pk : I → Kernel X X)
    [∀ i, IsMarkovKernel (Pk i)] (β : ℝ) (g : BM X) (p : BM X) : BM X :=
  ⟨fun x => β * Finset.univ.sup' Finset.univ_nonempty fun i => markovOp (Pk i) (p + g).toFun x,
    measurable_const.mul (by
      have := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty fun i _ =>
        measurable_markovOp (Pk i) (p + g).measurable'
      convert this using 1
      funext x
      rw [Finset.sup'_apply]),
    ⟨|β| * ‖p + g‖, fun x => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg β)
      · obtain ⟨i⟩ := ‹Nonempty I›
        exact (neg_le_of_abs_le (abs_markovOp_le (Pk i) (BM.abs_le_norm (p + g)) x)).trans
          (Finset.le_sup' (fun i => markovOp (Pk i) (p + g).toFun x) (Finset.mem_univ i))
      · exact Finset.sup'_le _ _ fun i _ =>
          le_of_abs_le (abs_markovOp_le (Pk i) (BM.abs_le_norm (p + g)) x)⟩⟩

attribute [local instance] BM.posSMulMono

/-- **Exercise 4.1.1** (p. 125): with `g ∈ bX` and `β ∈ [0, 1)`, the Harrison–Kreps operator is a
contraction of modulus `β` on `bX`, by Lemma 4.1.2 with the unit `𝟙`. -/
theorem exercise_4_1_1 [Nonempty X] {I : Type*} [Fintype I] [Nonempty I] (Pk : I → Kernel X X)
    [∀ i, IsMarkovKernel (Pk i)] {β : ℝ} (hβ : 0 ≤ β) (g p q : BM X) :
    ‖harrisonKreps Pk β g p - harrisonKreps Pk β g q‖ ≤ β * ‖p - q‖ := by
  refine BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one (fun p q h x => ?_) hβ
    (fun v κ _ => fun x => ?_) p q
  · refine mul_le_mul_of_nonneg_left (Finset.sup'_le _ _ fun i _ => ?_) hβ
    refine (markovOp_mono (Pk i) (BM.mem_bX _) (BM.mem_bX _) (fun y => ?_) x).trans
      (Finset.le_sup' (fun i => markovOp (Pk i) (q + g).toFun x) (Finset.mem_univ i))
    simp only [BM.add_apply]
    exact add_le_add (h y) le_rfl
  · have hshift : ∀ i, markovOp (Pk i) (v + κ • BM.const 1 + g).toFun x =
        markovOp (Pk i) (v + g).toFun x + κ := fun i => by
      have h1 := markovOp_add (Pk i) (BM.mem_bX (v + g)) (const_mem_bX κ)
      have h2 : (v + κ • BM.const 1 + g).toFun = (v + g).toFun + fun _ => κ := by
        funext y
        simp only [BM.add_apply, BM.smul_apply, BM.const_apply, Pi.add_apply, mul_one]
        ring
      rw [h2, h1, markovOp_const]
      rfl
    simp only [harrisonKreps, BM.add_apply, BM.smul_apply, BM.const_apply, mul_one, hshift]
    rw [sup'_add_const]
    linarith

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Correspondences and maximization

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §A.3.1.3 (pp. 350–351), as used in
Chapter 6.

* Lower and upper hemicontinuous, continuous and compact-valued correspondences, in the book's
  sequential form.
* **Exercise A.3.1**: `Γ(x) = [g(x), h(x)]` with `g ≤ h` continuous is compact-valued and continuous
  (for any topological state space; actions in `ℝ`).
* `HasMaxSelections Γ`: the conclusion of **Theorem A.3.3** (Berge's maximum theorem with a
  measurable selection): for every `q` continuous on `G = graph Γ`, a measurable selection `σ`
  attains `m(x) = max_{a ∈ Γ(x)} q(x, a)` and `m` is continuous. The book cites Aliprantis and
  Border; it is proved here for the interval correspondences of Exercise A.3.1
  (`hasMaxSelections_Icc`, for any sequential state space), which cover every application in
  Chapter 6, using the largest
  maximizer, which is upper semicontinuous and hence Borel.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

variable {X A : Type*}

/-- `Γ` is lower hemicontinuous at `x`: every `y ∈ Γ(x)` is a limit of `yₙ ∈ Γ(xₙ)` along any
`xₙ → x`. -/
def IsLHC [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) (x : X) : Prop :=
  ∀ y ∈ Γ x, ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) →
    ∃ ys : ℕ → A, (∀ n, ys n ∈ Γ (xs n)) ∧ Tendsto ys atTop (𝓝 y)

/-- `Γ` is upper hemicontinuous at `x`: along any `xₙ → x`, every `yₙ ∈ Γ(xₙ)` has a subsequence
converging in `Γ(x)`. -/
def IsUHC [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) (x : X) : Prop :=
  ∀ xs : ℕ → X, Tendsto xs atTop (𝓝 x) → ∀ ys : ℕ → A, (∀ n, ys n ∈ Γ (xs n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y ∈ Γ x, Tendsto (ys ∘ φ) atTop (𝓝 y)

/-- `Γ` is continuous: lower and upper hemicontinuous everywhere. -/
def IsContinuousCorr [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) : Prop :=
  ∀ x, IsLHC Γ x ∧ IsUHC Γ x

/-- The clamp of `y` into `[g, h]`. -/
theorem clamp_mem {g h : ℝ} (hgh : g ≤ h) (y : ℝ) : max g (min y h) ∈ Icc g h :=
  ⟨le_max_left _ _, max_le hgh (min_le_right _ _)⟩

theorem clamp_eq {g h y : ℝ} (hy : y ∈ Icc g h) : max g (min y h) = y := by
  rw [min_eq_left hy.2, max_eq_right hy.1]

/-- A sequence `yₙ ∈ [g(xₙ), h(xₙ)]` with `xₙ → x` has a subsequence converging in
`[g(x), h(x)]`. -/
theorem exists_subseq_Icc [TopologicalSpace X] {g h : X → ℝ} (hg : Continuous g)
    (hh : Continuous h) {xs : ℕ → X} {x : X} (hx : Tendsto xs atTop (𝓝 x)) {ys : ℕ → ℝ}
    (hys : ∀ n, ys n ∈ Icc (g (xs n)) (h (xs n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y ∈ Icc (g x) (h x), Tendsto (ys ∘ φ) atTop (𝓝 y) := by
  obtain ⟨Bg, hBg⟩ := ((hg.tendsto x).comp hx).bddBelow_range
  obtain ⟨Bh, hBh⟩ := ((hh.tendsto x).comp hx).bddAbove_range
  have hmem : ∀ n, ys n ∈ Icc Bg Bh := fun n =>
    ⟨(hBg ⟨n, rfl⟩).trans (hys n).1, (hys n).2.trans (hBh ⟨n, rfl⟩)⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨φ, hφ, y, ⟨?_, ?_⟩, hlim⟩
  · exact le_of_tendsto_of_tendsto' ((hg.tendsto x).comp (hx.comp hφ.tendsto_atTop)) hlim
      fun k => (hys (φ k)).1
  · exact le_of_tendsto_of_tendsto' hlim ((hh.tendsto x).comp (hx.comp hφ.tendsto_atTop))
      fun k => (hys (φ k)).2

/-- **Exercise A.3.1** (p. 350): if `g ≤ h` are continuous, `Γ(x) = [g(x), h(x)]` is
compact-valued and continuous. -/
theorem exercise_A_3_1 [TopologicalSpace X] {g h : X → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hgh : ∀ x, g x ≤ h x) :
    (∀ x, IsCompact (Icc (g x) (h x))) ∧ IsContinuousCorr fun x => Icc (g x) (h x) := by
  refine ⟨fun x => isCompact_Icc, fun x => ⟨fun y hy xs hx => ?_, fun xs hx ys hys => ?_⟩⟩
  · refine ⟨fun n => max (g (xs n)) (min y (h (xs n))), fun n => clamp_mem (hgh _) y, ?_⟩
    have := ((hg.tendsto x).comp hx).max
      ((tendsto_const_nhds (x := y)).min ((hh.tendsto x).comp hx))
    rwa [clamp_eq hy] at this
  · exact exists_subseq_Icc hg hh hx hys

/-- The conclusion of **Theorem A.3.3** for `Γ`: for every `q` continuous on `G = graph Γ`, a
measurable selection `σ` attains `m(x) = max_{a ∈ Γ(x)} q(x, a)`, and `m` is continuous. -/
def HasMaxSelections [TopologicalSpace X] [TopologicalSpace A] [MeasurableSpace X]
    [MeasurableSpace A] (Γ : X → Set A) : Prop :=
  ∀ q : X × A → ℝ, ContinuousOn q {p | p.2 ∈ Γ p.1} →
    ∃ σ : X → A, Measurable σ ∧ (∀ x, σ x ∈ Γ x) ∧ (∀ x, ∀ a ∈ Γ x, q (x, a) ≤ q (x, σ x)) ∧
      Continuous fun x => q (x, σ x)

namespace IccMax

variable [TopologicalSpace X] [SequentialSpace X] {g h : X → ℝ} {q : X × ℝ → ℝ}

/-- The maximizers of `q(x, ·)` on `[g(x), h(x)]`. -/
def argmax (g h : X → ℝ) (q : X × ℝ → ℝ) (x : X) : Set ℝ :=
  {a | a ∈ Icc (g x) (h x) ∧ ∀ b ∈ Icc (g x) (h x), q (x, b) ≤ q (x, a)}

/-- The largest maximizer. -/
noncomputable def sel (g h : X → ℝ) (q : X × ℝ → ℝ) (x : X) : ℝ := sSup (argmax g h q x)

variable (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x)
  (hq : ContinuousOn q {p | p.2 ∈ Icc (g p.1) (h p.1)})
include hg hh hgh hq

omit hg hh hgh [SequentialSpace X] in
theorem continuousOn_section (x : X) : ContinuousOn (fun a => q (x, a)) (Icc (g x) (h x)) :=
  hq.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ha => ha

omit hg hh [SequentialSpace X] in
theorem argmax_nonempty (x : X) : (argmax g h q x).Nonempty := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hgh x))
    (continuousOn_section hq x)
  exact ⟨c, hc, fun b hb => hmax hb⟩

omit hg hh hgh [SequentialSpace X] in
theorem isClosed_argmax (x : X) : IsClosed (argmax g h q x) := by
  have hc := continuousOn_section hq x
  have heq : argmax g h q x = Icc (g x) (h x) ∩
      ⋂ b ∈ Icc (g x) (h x), (Icc (g x) (h x) ∩ (fun a => q (x, a)) ⁻¹' Ici (q (x, b))) := by
    ext a
    simp only [argmax, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ici]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hbm => ⟨ha, hb b hbm⟩⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hbm => (hb b hbm).2⟩
  rw [heq]
  exact isClosed_Icc.inter (isClosed_biInter fun b _ =>
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)

omit hg hh [SequentialSpace X] in
theorem sel_mem (x : X) : sel g h q x ∈ argmax g h q x :=
  (isClosed_argmax hq x).csSup_mem (argmax_nonempty hgh hq x)
    ⟨h x, fun _ ha => ha.1.2⟩

/-- The largest maximizer is upper semicontinuous: `{x | a ≤ σ(x)}` is closed. -/
theorem isClosed_le_sel (a : ℝ) : IsClosed {x | a ≤ sel g h q x} := by
  refine isSeqClosed_iff_isClosed.1 fun xs x hxs hlim => ?_
  have hmem : ∀ n, sel g h q (xs n) ∈ Icc (g (xs n)) (h (xs n)) := fun n =>
    (sel_mem hgh hq (xs n)).1
  obtain ⟨φ, hφ, c, hc, hcφ⟩ := exists_subseq_Icc hg hh hlim hmem
  have hxφ : Tendsto (xs ∘ φ) atTop (𝓝 x) := hlim.comp hφ.tendsto_atTop
  have hcmax : c ∈ argmax g h q x := by
    refine ⟨hc, fun b hb => ?_⟩
    -- clamp `b` into the feasible intervals along the subsequence
    let bs : ℕ → ℝ := fun k => max (g (xs (φ k))) (min b (h (xs (φ k))))
    have hbs : Tendsto bs atTop (𝓝 b) := by
      have := ((hg.tendsto x).comp hxφ).max
        ((tendsto_const_nhds (x := b)).min ((hh.tendsto x).comp hxφ))
      rwa [clamp_eq hb] at this
    have hG1 : Tendsto (fun k => ((xs ∘ φ) k, bs k)) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, b)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hbs, Eventually.of_forall fun k =>
        clamp_mem (hgh _) b⟩
    have hG2 : Tendsto (fun k => ((xs ∘ φ) k, sel g h q (xs (φ k)))) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, c)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hcφ, Eventually.of_forall fun k => hmem _⟩
    exact le_of_tendsto_of_tendsto' ((hq (x, b) hb).tendsto.comp hG1)
      ((hq (x, c) hc).tendsto.comp hG2) fun k =>
        (sel_mem hgh hq (xs (φ k))).2 _ (clamp_mem (hgh _) b)
  have hac : a ≤ c := ge_of_tendsto' hcφ fun k => hxs (φ k)
  exact hac.trans (le_csSup ⟨h x, fun _ ha => ha.1.2⟩ hcmax)

omit hg hh hgh hq in
/-- Points of `[g(x), h(x)]` as `g(x) + t(h(x) − g(x))` with `t ∈ [0, 1]`. -/
theorem exists_param {gx hx a : ℝ} (ha : a ∈ Icc gx hx) :
    ∃ t ∈ Icc (0 : ℝ) 1, gx + max 0 (min t 1) * (hx - gx) = a := by
  rcases eq_or_lt_of_le (ha.1.trans ha.2) with heq | hlt
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have : a = gx := le_antisymm (ha.2.trans heq.symm.le) ha.1
    simp [this]
  · refine ⟨(a - gx) / (hx - gx), ⟨div_nonneg (sub_nonneg.2 ha.1) (sub_pos.2 hlt).le,
      (div_le_one (sub_pos.2 hlt)).2 (sub_le_sub_right ha.2 _)⟩, ?_⟩
    have h0 : 0 ≤ (a - gx) / (hx - gx) := div_nonneg (sub_nonneg.2 ha.1) (sub_pos.2 hlt).le
    have h1 : (a - gx) / (hx - gx) ≤ 1 := (div_le_one (sub_pos.2 hlt)).2 (sub_le_sub_right ha.2 _)
    rw [min_eq_left h1, max_eq_right h0, div_mul_cancel₀ _ (sub_pos.2 hlt).ne']
    ring

omit [SequentialSpace X] in
/-- The maximum `m(x) = q(x, σ(x))` is continuous (Berge). -/
theorem continuous_max : Continuous fun x => q (x, sel g h q x) := by
  let κ : X × ℝ → X × ℝ := fun p => (p.1, g p.1 + max 0 (min p.2 1) * (h p.1 - g p.1))
  have hκ : Continuous κ := continuous_fst.prodMk ((hg.comp continuous_fst).add
    ((continuous_const.max (continuous_snd.min continuous_const)).mul
      ((hh.comp continuous_fst).sub (hg.comp continuous_fst))))
  have hκG : ∀ p, κ p ∈ {p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)} := fun p => by
    have ht0 : 0 ≤ max 0 (min p.2 1) := le_max_left _ _
    have ht1 : max 0 (min p.2 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    have hd : 0 ≤ h p.1 - g p.1 := sub_nonneg.2 (hgh p.1)
    exact ⟨le_add_of_nonneg_right (mul_nonneg ht0 hd), by nlinarith⟩
  have hQ : Continuous (q ∘ κ) := hq.comp_continuous hκ hκG
  have hm := isCompact_Icc.continuous_sSup (f := fun (x : X) (t : ℝ) => (q ∘ κ) (x, t))
    (K := Icc (0 : ℝ) 1) hQ
  refine hm.congr fun x => ?_
  -- the supremum over `t` is attained at the largest maximizer
  have hs := sel_mem hgh hq x
  obtain ⟨t₀, ht₀, ht₀eq⟩ := exists_param hs.1
  refine (IsGreatest.csSup_eq ⟨⟨t₀, ht₀, ?_⟩, ?_⟩)
  · simp only [Function.comp_apply, κ]
    rw [ht₀eq]
  · rintro _ ⟨t, -, rfl⟩
    exact hs.2 _ (hκG (x, t))

/-- The largest maximizer is Borel. -/
theorem measurable_sel [MeasurableSpace X] [OpensMeasurableSpace X] :
    Measurable (sel g h q) :=
  measurable_of_Ici fun a => (isClosed_le_sel hg hh hgh hq a).measurableSet

end IccMax

/-- **Theorem A.3.3** for the interval correspondences of Exercise A.3.1: if `g ≤ h` are
continuous, then `Γ(x) = [g(x), h(x)]` has measurable maximizing selections with continuous
maximum. -/
theorem hasMaxSelections_Icc [TopologicalSpace X] [SequentialSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    {g h : X → ℝ} (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    HasMaxSelections fun x => Icc (g x) (h x) := fun q hq =>
  ⟨IccMax.sel g h q, IccMax.measurable_sel hg hh hgh hq, fun x => (IccMax.sel_mem hgh hq x).1,
    fun x a ha => (IccMax.sel_mem hgh hq x).2 a ha, IccMax.continuous_max hg hh hgh hq⟩

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.2 (pp. 187–192).

A linear decision process `(Γ, r, K)` has a feasible correspondence `Γ`, a bounded measurable
reward `r` and a transition kernel `K` with `Kv ∈ bG` for `v ∈ bX`. Here `K` is written
`K(x, a, dx') = β(x, a)P(x, a, dx')` with `β ≥ 0` bounded measurable and `P` stochastic, which is
how every kernel in the chapter is built.

* Feasible policies are measurable selections of `Γ`; the policy operators (6.4) are
  `T_σ v = r_σ + K_σ v` on `bX`, with `K_σ` a positive bounded linear operator, so `(bX, 𝕋_LDP)` is
  an additive ADP (§6.1.2.2).
* (6.5)–(6.6): if `ρ(K_σ) < 1`, then `v_σ = ∑_{t ≥ 0} K_σ^t r_σ`, as the limit of partial sums.
* (6.7): `σ` is `v`-greedy iff `r(x, τ(x)) + (Kv)(x, τ(x)) ≤ r(x, σ(x)) + (Kv)(x, σ(x))` for all
  feasible `τ` and all `x`.
* **Example 6.1.4**: the firm valuation problem with state-dependent discounting is an LDP.
* **Example 6.1.6**: a risk-sensitive MDP is not an LDP: its policy operators are not affine.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- A linear decision process `(Γ, r, K)` with `K(x, a, dx') = β(x, a)P(x, a, dx')` (§6.1.2.1). -/
structure LDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the reward -/
  r : BM (X × A)
  /-- the discount factor of the transition kernel -/
  β : BM (X × A)
  β_nonneg : 0 ≤ β
  /-- the stochastic part of the transition kernel -/
  P : Kernel (X × A) X
  [P_markov : IsMarkovKernel P]
  /-- a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace LDP

attribute [local instance] LDP.P_markov

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : LDP X A)

/-- Feasible policies: measurable `σ : X → A` with `σ(x) ∈ Γ(x)`. -/
def Policy : Type _ := {σ : X → A // Measurable σ ∧ ∀ x, σ x ∈ M.Γ x}

theorem nonempty_policy : Nonempty M.Policy :=
  ⟨⟨M.exists_policy.choose, M.exists_policy.choose_spec⟩⟩

theorem measurable_graph (σ : M.Policy) : Measurable fun x => (x, σ.1 x) :=
  measurable_id.prodMk σ.2.1

/-- Restriction of `f ∈ bG` along `x ↦ (x, σ(x))`. -/
def along (σ : M.Policy) (f : BM (X × A)) : BM X :=
  ⟨fun x => f.toFun (x, σ.1 x), f.measurable'.comp (M.measurable_graph σ),
    ⟨‖f‖, fun _ => BM.abs_le_norm f _⟩⟩

/-- `r_σ(x) = r(x, σ(x))`. -/
def rσ (σ : M.Policy) : BM X := M.along σ M.r

/-- `β_σ(x) = β(x, σ(x))`. -/
def βσ (σ : M.Policy) : BM X := M.along σ M.β

/-- `P_σ(x, dx') = P(x, σ(x), dx')`. -/
noncomputable abbrev Pσ (σ : M.Policy) : Kernel X X := M.P.comap _ (M.measurable_graph σ)

/-- `K_σ = β_σ P_σ`, `(K_σ v)(x) = β(x, σ(x)) ∫ v(x')P(x, σ(x), dx')`. -/
noncomputable def K (σ : M.Policy) : BM X →L[ℝ] BM X :=
  (BM.mulCLM (M.βσ σ)).comp (BM.markovCLM (M.Pσ σ))

theorem K_apply (σ : M.Policy) (v : BM X) (x : X) :
    (M.K σ v).toFun x = M.β.toFun (x, σ.1 x) * ∫ x', v.toFun x' ∂(M.P (x, σ.1 x)) := rfl

theorem K_isPositive (σ : M.Policy) : BanachLattice.IsPositiveOp (M.K σ) := fun v hv =>
  BM.mulCLM_isPositive (h := M.βσ σ) (fun x => M.β_nonneg (x, σ.1 x)) _
    (BM.markovCLM_isPositive (M.Pσ σ) v hv)

/-- `|∫ v dK(x, a)| ≤ ‖β‖‖v‖`: `K` maps `bX` into `bG`, and `‖K_σ‖ ≤ ‖β‖`. -/
theorem norm_K_le (σ : M.Policy) : ‖M.K σ‖ ≤ ‖M.β‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  refine BM.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => ?_
  rw [K_apply, abs_mul]
  exact mul_le_mul (BM.abs_le_norm M.β _) (abs_markovOp_le (M.Pσ σ) (BM.abs_le_norm v) x)
    (abs_nonneg _) (norm_nonneg _)

/-- The ADP `(bX, 𝕋_LDP)` generated by `(Γ, r, K)` (§6.1.2.2), with `T_σ v = r_σ + K_σ v`. -/
noncomputable def adp : ADP (BM X) M.Policy where
  T σ v := M.rσ σ + M.K σ v
  mono σ _ _ h := add_le_add le_rfl ((M.K_isPositive σ).mono h)
  nonempty := M.nonempty_policy

/-- The policy operator (6.4): `(T_σ v)(x) = r(x, σ(x)) + ∫ v(x')K(x, σ(x), dx')`. -/
theorem T_apply (σ : M.Policy) (v : BM X) (x : X) :
    (M.adp.T σ v).toFun x =
      M.r.toFun (x, σ.1 x) + M.β.toFun (x, σ.1 x) * ∫ x', v.toFun x' ∂(M.P (x, σ.1 x)) := rfl

/-- `T_σ` has the additive form of §4.1.2.3, with positive `K_σ`. -/
theorem isAdditive : BanachLattice.IsAdditive id M.adp M.rσ M.K :=
  ⟨M.K_isPositive, fun _ _ => rfl⟩

/-- The objective `r(x, a) + ∫ v(x')K(x, a, dx')`. -/
noncomputable def obj (v : BM X) (p : X × A) : ℝ :=
  M.r.toFun p + M.β.toFun p * ∫ x', v.toFun x' ∂(M.P p)

theorem T_apply_obj (σ : M.Policy) (v : BM X) (x : X) :
    (M.adp.T σ v).toFun x = M.obj v (x, σ.1 x) := rfl

/-- (6.7): `σ` is `v`-greedy iff `r(x, τ(x)) + ∫ v dK(x, τ(x)) ≤ r(x, σ(x)) + ∫ v dK(x, σ(x))` for
all feasible `τ` and all `x`. -/
theorem isGreedy_iff (v : BM X) (σ : M.Policy) :
    M.adp.IsGreedy v σ ↔ ∀ τ : M.Policy, ∀ x, M.obj v (x, τ.1 x) ≤ M.obj v (x, σ.1 x) :=
  Iff.rfl

/-- A policy maximizing the objective over `Γ(x)` at every `x` (6.8) is `v`-greedy. -/
theorem isGreedy_of_argmax (v : BM X) (σ : M.Policy)
    (h : ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) : M.adp.IsGreedy v σ :=
  fun τ x => h x _ (τ.2.2 x)

/-- With measurable singletons, a `v`-greedy policy maximizes the objective over `Γ(x)` at every
`x` (6.8): change any policy at a single state. -/
theorem argmax_of_isGreedy [MeasurableSingletonClass X] (v : BM X) (σ : M.Policy)
    (h : M.adp.IsGreedy v σ) : ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x) := by
  classical
  intro x a ha
  have hm : Measurable (Function.update σ.1 x a) := by
    rw [show Function.update σ.1 x a = Set.piecewise {x} (fun _ => a) σ.1 from
      (Set.piecewise_singleton x (fun _ => a) σ.1).symm]
    exact Measurable.piecewise (measurableSet_singleton x) measurable_const σ.2.1
  let τ : M.Policy := ⟨Function.update σ.1 x a, hm, fun y => by
    by_cases hy : y = x
    · subst hy; simpa using ha
    · rw [Function.update_of_ne hy]; exact σ.2.2 y⟩
  have := h τ x
  rwa [T_apply_obj, T_apply_obj, show τ.1 x = a from Function.update_self x a σ.1] at this

/-- Iterating `T_σ` from `0` gives the partial sums `∑_{t < n} K_σ^t r_σ`. -/
theorem iterate_T_zero (σ : M.Policy) (n : ℕ) :
    (M.adp.T σ)^[n] 0 = ∑ t ∈ Finset.range n, (M.K σ ^ t) (M.rσ σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ']
    change M.rσ σ + M.K σ (∑ t ∈ Finset.range n, (M.K σ ^ t) (M.rσ σ)) = _
    rw [map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ']
    rfl

/-- If `ρ(K_σ) < 1`, then `T_σ` is globally stable. -/
theorem globallyStable_T (σ : M.Policy) (hρ : BanachLattice.specRad (M.K σ) < 1) :
    GloballyStable (M.adp.T σ) := by
  have : Nonempty (BM X) := ⟨0⟩
  have hι : BanachLattice.IsIsoOrderEmbedding (id : BM X → BM X) :=
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩
  exact (BanachLattice.theorem_4_1_4 hι ⟨BanachLattice.example_4_1_1 (M.K_isPositive σ) hρ,
    M.isAdditive.abs_sub σ⟩).1

/-- (6.5)–(6.6) (p. 191): if `ρ(K_σ) < 1`, the `σ`-value function is the unique solution of
`v_σ = r_σ + K_σ v_σ` and equals `∑_{t ≥ 0} K_σ^t r_σ`. -/
theorem lifetime_value (σ : M.Policy) (hρ : BanachLattice.specRad (M.K σ) < 1) :
    ∃ vσ, M.adp.T σ vσ = vσ ∧ (∀ w, M.adp.T σ w = w → w = vσ) ∧
      Tendsto (fun n => ∑ t ∈ Finset.range n, (M.K σ ^ t) (M.rσ σ)) atTop (𝓝 vσ) := by
  obtain ⟨u, hu, huniq, hlim⟩ := M.globallyStable_T σ hρ
  refine ⟨u, hu, huniq, ?_⟩
  refine (hlim 0).congr fun n => ?_
  exact M.iterate_T_zero σ n

/-! ### Examples -/

/-- **Example 6.1.4** (p. 190): the firm valuation problem with state-dependent discounting as an
LDP, `A = {0, 1}` (`true` = exit), `r(x, a) = as + (1 − a)π(x)` and
`K(x, a, dx') = (1 − a)β(x)P(x, dx')`. -/
noncomputable def firm (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π βf : BM X)
    (hβ : 0 ≤ βf) : LDP X Bool where
  Γ _ := univ
  r := ⟨fun p => if p.2 then s else π.toFun p.1,
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      (π.measurable'.comp measurable_fst),
    ⟨|s| + ‖π‖, fun p => by
      split_ifs
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · exact (BM.abs_le_norm π _).trans (le_add_of_nonneg_left (abs_nonneg _))⟩⟩
  β := ⟨fun p => if p.2 then 0 else βf.toFun p.1,
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      (βf.measurable'.comp measurable_fst),
    ⟨‖βf‖, fun p => by
      split_ifs
      · simp
      · exact BM.abs_le_norm βf _⟩⟩
  β_nonneg p := by
    change 0 ≤ if p.2 then (0 : ℝ) else βf.toFun p.1
    split_ifs
    · exact le_rfl
    · exact hβ _
  P := P.comap Prod.fst measurable_fst
  exists_policy := ⟨fun _ => false, measurable_const, fun _ => Set.mem_univ _⟩

/-- The firm policy operator: `(T_σ v)(x) = s` if `σ(x)` is exit, and
`π(x) + β(x) ∫ v(x')P(x, dx')` otherwise. -/
theorem firm_T_apply (P : Kernel X X) [IsMarkovKernel P] (s : ℝ) (π βf : BM X) (hβ : 0 ≤ βf)
    (σ : (firm P s π βf hβ).Policy) (v : BM X) (x : X) :
    ((firm P s π βf hβ).adp.T σ v).toFun x =
      if σ.1 x then s else π.toFun x + βf.toFun x * ∫ x', v.toFun x' ∂(P x) := by
  rw [T_apply]
  change (if σ.1 x then s else π.toFun x) + (if σ.1 x then (0 : ℝ) else βf.toFun x) *
    ∫ x', v.toFun x' ∂(P x) = _
  split_ifs <;> simp

end LDP

/-- **Example 6.1.6** (p. 191): the risk-sensitive policy operator
`(T_σ v)(x) = r(x, σ(x)) + (β/θ) ln ∑_{x'} exp(θv(x'))P(x, σ(x), x')` is not affine in `v`, so it
does not have the LDP form `r_σ + K_σ v`. Two states, `P` uniform, `β = θ = 1`, `r = 0`: then
`T(2v) − T0 ≠ 2(Tv − T0)` at `v = (1, 0)`. -/
theorem example_6_1_6 :
    let T : (Bool → ℝ) → ℝ := fun v => Real.log ((Real.exp (v true) + Real.exp (v false)) / 2)
    T (fun b => 2 * if b then 1 else 0) - T 0 ≠
      2 * (T (fun b => if b then 1 else 0) - T 0) := by
  intro T
  simp only [T, Pi.zero_apply, Real.exp_zero, ite_true, mul_one]
  norm_num
  intro h
  -- `log((e² + 1)/2) = 2 log((e + 1)/2)` gives `(e² + 1)/2 = ((e + 1)/2)²`, i.e. `(e − 1)² = 0`
  have h1 : (Real.exp 2 + 1) / 2 = ((Real.exp 1 + 1) / 2) ^ 2 := by
    have hpos1 : 0 < (Real.exp 2 + 1) / 2 := by positivity
    have hpos2 : 0 < ((Real.exp 1 + 1) / 2) ^ 2 := by positivity
    rw [← Real.exp_log hpos1, ← Real.exp_log hpos2, Real.log_pow, h]
    push_cast
    ring_nf
  have he : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he] at h1
  have h3 : (Real.exp 1 - 1) ^ 2 = 0 := by nlinarith
  have h4 : Real.exp 1 - 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h3
  have h5 := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
  linarith

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimality for linear decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.3 (pp. 192–194).

* **Proposition 6.1.2** (finite LDPs): if `𝕋_LDP` is finite and `ρ(K_σ) < 1` for every `σ`, the
  fundamental optimality properties hold and VFI, OPI and HPI converge. The book calls regularity
  "obvious in the finite case"; it holds because finitely many policy operators can be pasted
  into one measurable policy that is pointwise best (`regular_of_isFinite`).
* Feller properties: `K` is weak Feller if `Kh ∈ bcG` for `h ∈ bcX`, strong Feller if `Kh` is
  continuous on `G` for every `h ∈ bX`.
* **Proposition 6.1.3** (Feller LDPs): under Assumption 6.1.1 (with the maximum theorem,
  Theorem A.3.3, for `Γ`), a weak Feller `K` and a discount operator `D ≥ K_σ` on `bX₊`, the
  fundamental optimality properties hold, `v* ∈ bcX` and VFI converges geometrically on `bcX`; if
  `K` is strong Feller, OPI and HPI converge (Theorem 4.1.8 with `V₀ = bcX`).
* §6.1.3.2: greedy policies are exactly the pointwise maximizers (6.8), and the Bellman operator
  is (6.9), `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v(x')K(x, a, dx')}`, for all `v ∈ bX` under
  strong Feller and for `v ∈ bcX` under weak Feller.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Measurable least maximizers over a finite set -/

/-- The maximizers of `a ↦ h(x, a)` over a finite type. -/
noncomputable def argmaxSet {X I : Type*} [Fintype I] (h : X → I → ℝ) (x : X) : Finset I :=
  Finset.univ.filter fun i => ∀ j, h x j ≤ h x i

theorem argmaxSet_nonempty {X I : Type*} [Fintype I] [Nonempty I] (h : X → I → ℝ) (x : X) :
    (argmaxSet h x).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (h x) Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩

/-- The least maximizer. -/
noncomputable def argmaxSel {X I : Type*} [Fintype I] [Nonempty I] [LinearOrder I]
    (h : X → I → ℝ) (x : X) : I :=
  (argmaxSet h x).min' (argmaxSet_nonempty h x)

theorem argmaxSel_max {X I : Type*} [Fintype I] [Nonempty I] [LinearOrder I] (h : X → I → ℝ)
    (x : X) (j : I) : h x j ≤ h x (argmaxSel h x) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (argmaxSet_nonempty h x))).2 j

/-- The least maximizer is measurable when each `x ↦ h(x, i)` is. -/
theorem measurable_argmaxSel {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Fintype I] [Nonempty I] [LinearOrder I] {h : X → I → ℝ}
    (hm : ∀ i, Measurable fun x => h x i) : Measurable (argmaxSel h) := by
  classical
  refine measurable_to_countable' fun i => ?_
  have hset : argmaxSel h ⁻¹' {i} =
      {x | ∀ j, h x j ≤ h x i} ∩ ⋂ j, ({x | ∀ k, h x k ≤ h x j}ᶜ ∪ {_x | i ≤ j}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨argmaxSel_max h x, fun j => ?_⟩
      by_cases hj : ∀ k, h x k ≤ h x j
      · exact Or.inr (Finset.min'_le (argmaxSet h x) j
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
      · exact Or.inl hj
    · rintro ⟨hmax, hmin⟩
      refine le_antisymm (Finset.min'_le (argmaxSet h x) i
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax⟩))
        (Finset.le_min' (argmaxSet h x) (argmaxSet_nonempty h x) i fun j hj => ?_)
      rcases hmin j with h1 | h1
      · exact absurd (Finset.mem_filter.1 hj).2 h1
      · exact h1
  rw [hset]
  have hmeas : ∀ j, MeasurableSet {x | ∀ k, h x k ≤ h x j} := fun j => by
    have : {x | ∀ k, h x k ≤ h x j} = ⋂ k, {x | h x k ≤ h x j} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.iInter fun k => measurableSet_le (hm k) (hm j)
  refine (hmeas i).inter (MeasurableSet.iInter fun j => (hmeas j).compl.union ?_)
  by_cases h' : i ≤ j
  · simp [h']
  · simp [h']

namespace LDP

attribute [local instance] LDP.P_markov

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : LDP X A)

/-- With finitely many policy operators, the LDP is regular: paste the finitely many operators
into a measurable policy that is best at every state. -/
theorem regular_of_isFinite (hfin : M.adp.IsFinite) : M.adp.Regular := by
  classical
  have : Finite (range M.adp.T) := hfin.to_subtype
  let k := Nat.card (range M.adp.T)
  let f : range M.adp.T ≃ Fin k := Finite.equivFin _
  let e : Fin k → M.Policy := fun j => (f.symm j).2.choose
  have he : ∀ j, M.adp.T (e j) = (f.symm j).1 := fun j => (f.symm j).2.choose_spec
  have hall : ∀ σ, ∃ j, M.adp.T σ = M.adp.T (e j) := fun σ =>
    ⟨f ⟨_, σ, rfl⟩, by rw [he, Equiv.symm_apply_apply]⟩
  obtain ⟨σ₀⟩ := M.nonempty_policy
  have : Nonempty (Fin k) := ⟨(hall σ₀).choose⟩
  intro v
  let h : X → Fin k → ℝ := fun x j => (M.adp.T (e j) v).toFun x
  let i := argmaxSel h
  have hi : Measurable i := measurable_argmaxSel fun j => (M.adp.T (e j) v).measurable'
  let σ : X → A := fun x => (e (i x)).1 x
  have hσm : Measurable σ := by
    have hF : Measurable fun p : X × Fin k => (e p.2).1 p.1 :=
      measurable_from_prod_countable_left fun j => (e j).2.1
    exact hF.comp (measurable_id.prodMk hi)
  let σp : M.Policy := ⟨σ, hσm, fun x => (e (i x)).2.2 x⟩
  refine ⟨σp, fun τ x => ?_⟩
  obtain ⟨j, hj⟩ := hall τ
  rw [hj]
  change h x j ≤ M.obj v (x, (e (i x)).1 x)
  exact argmaxSel_max h x j

/-- **Proposition 6.1.2** (p. 192): if `𝕋_LDP` is finite and `ρ(K_σ) < 1` for every `σ`, then the
fundamental optimality properties hold and VFI, OPI and HPI all converge. -/
theorem proposition_6_1_2 (hfin : M.adp.IsFinite)
    (hρ : ∀ σ, BanachLattice.specRad (M.K σ) < 1) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have : Nonempty (BM X) := ⟨0⟩
  exact BanachLattice.theorem_4_1_7 ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩ M.adp
    (M.regular_of_isFinite hfin) hfin M.isAdditive hρ

/-! ### Feller LDPs -/

variable [TopologicalSpace X] [TopologicalSpace A]

/-- The feasible state-action pairs `G = graph Γ` (6.3). -/
def G : Set (X × A) := {p | p.2 ∈ M.Γ p.1}

/-- `K` is weak Feller: `Kh` is continuous on `G` whenever `h ∈ bcX` (§6.1.1). -/
def IsWeakFeller : Prop :=
  ∀ h : BM X, Continuous h.toFun →
    ContinuousOn (fun p => M.β.toFun p * ∫ x', h.toFun x' ∂(M.P p)) M.G

/-- `K` is strong Feller: `Kh` is continuous on `G` for every `h ∈ bX` (§6.1.1). -/
def IsStrongFeller : Prop :=
  ∀ h : BM X, ContinuousOn (fun p => M.β.toFun p * ∫ x', h.toFun x' ∂(M.P p)) M.G

theorem IsStrongFeller.isWeakFeller {M : LDP X A} (h : M.IsStrongFeller) : M.IsWeakFeller :=
  fun f _ => h f

/-- `bcX`, the bounded continuous functions, inside `bX`. -/
def bc (X : Type*) [MeasurableSpace X] [TopologicalSpace X] : Set (BM X) :=
  {v | Continuous v.toFun}

theorem isClosed_bc : IsClosed (bc X) := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  exact (BM.tendstoUniformly_of_tendsto hlim).continuous (Frequently.of_forall hvs)

theorem zero_mem_bc : (0 : BM X) ∈ bc X := continuous_const

/-- Assumption 6.1.1 (ii) and the Feller property make the objective continuous on `G`. -/
theorem continuousOn_obj (hr : ContinuousOn M.r.toFun M.G) {v : BM X}
    (hK : ContinuousOn (fun p => M.β.toFun p * ∫ x', v.toFun x' ∂(M.P p)) M.G) :
    ContinuousOn (M.obj v) M.G :=
  hr.add hK

/-- With the maximum theorem for `Γ` and a continuous objective, a greedy policy exists, it attains
the maximum at each state, and the Bellman operator is continuous. -/
theorem greedy_of_continuousOn (hB : HasMaxSelections M.Γ) {v : BM X}
    (hc : ContinuousOn (M.obj v) M.G) :
    ∃ σ : M.Policy, M.adp.IsGreedy v σ ∧
      (∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      Continuous (M.adp.bellman v).toFun := by
  obtain ⟨σ, hσm, hσΓ, hmax, hcont⟩ := hB _ hc
  let σp : M.Policy := ⟨σ, hσm, hσΓ⟩
  have hg : M.adp.IsGreedy v σp := M.isGreedy_of_argmax v σp hmax
  refine ⟨σp, hg, hmax, ?_⟩
  have heq : M.adp.bellman v = M.adp.T σp v := ((M.adp.isGreedy_iff ⟨σp, hg⟩ σp).1 hg).symm
  rw [heq]
  exact hcont

/-- **Proposition 6.1.3** (p. 192): under Assumption 6.1.1 (`Γ` with the maximum theorem,
Theorem A.3.3, and `r` continuous on `G`), if `K` is weak Feller and `K_σ ≤ D` on `bX₊` for a
discount operator `D`, then (i) the fundamental optimality properties hold, (ii) `v* ∈ bcX` and
(iii) VFI converges geometrically on `bcX`; if `K` is strong Feller, OPI and HPI converge. -/
theorem proposition_6_1_3 (hB : HasMaxSelections M.Γ) (hr : ContinuousOn M.r.toFun M.G)
    (hK : M.IsWeakFeller) {D : BM X → BM X} (hD : BanachLattice.IsDiscountOperator D)
    (hKD : ∀ σ h, 0 ≤ h → M.K σ h ≤ D h) :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar ∈ bc X,
      M.adp.VFIGeometric (bc X) vstar ∧
        (M.IsStrongFeller →
          ∀ g, M.adp.IsSelector g →
            M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar) := by
  have : Nonempty (BM X) := ⟨0⟩
  have hsr : M.adp.IsSemiRegular (bc X) := by
    refine ⟨isClosed_bc, fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨σ, hg, -, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
      exact ⟨σ, hg⟩
    · obtain ⟨-, -, -, hc⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
      exact hc
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩ M.adp M.isAdditive hD hKD hsr
    ⟨0, zero_mem_bc⟩
  refine ⟨hw, hFO, vstar, hv, hgeo, fun hS => hconv fun v => ?_⟩
  obtain ⟨σ, hg, -, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hS v))
  exact ⟨σ, hg⟩

/-- §6.1.3.2 (pp. 193–194): if `Γ` has the maximum theorem, `r` is continuous on `G` and `K` is
strong Feller, then for every `v ∈ bX` a policy satisfying (6.8) exists, a policy is `v`-greedy iff
it satisfies (6.8), and the Bellman operator is (6.9),
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v(x')K(x, a, dx')}`. -/
theorem implications [MeasurableSingletonClass X] (hB : HasMaxSelections M.Γ)
    (hr : ContinuousOn M.r.toFun M.G) (hK : M.IsStrongFeller) (v : BM X) :
    (∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      (∀ σ : M.Policy, M.adp.IsGreedy v σ ↔
        ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      ∀ x, IsGreatest ((fun a => M.obj v (x, a)) '' M.Γ x) ((M.adp.bellman v).toFun x) := by
  obtain ⟨σ, hg, hmax, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v))
  have heq : M.adp.bellman v = M.adp.T σ v := ((M.adp.isGreedy_iff ⟨σ, hg⟩ σ).1 hg).symm
  refine ⟨⟨σ, hmax⟩, fun τ => ⟨M.argmax_of_isGreedy v τ, M.isGreedy_of_argmax v τ⟩,
    fun x => ⟨⟨σ.1 x, σ.2.2 x, ?_⟩, ?_⟩⟩
  · rw [heq]
    rfl
  · rintro _ ⟨a, ha, rfl⟩
    rw [heq]
    exact hmax x a ha

/-- §6.1.3.2 (p. 194), weak Feller case: the expressions (6.8)–(6.9) remain valid for `v ∈ bcX`:
a policy attaining the maximum exists and `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∫ v dK(x, a)}`. -/
theorem implications_bc (hB : HasMaxSelections M.Γ) (hr : ContinuousOn M.r.toFun M.G)
    (hK : M.IsWeakFeller) {v : BM X} (hv : v ∈ bc X) :
    (∃ σ : M.Policy, ∀ x, ∀ a ∈ M.Γ x, M.obj v (x, a) ≤ M.obj v (x, σ.1 x)) ∧
      ∀ x, IsGreatest ((fun a => M.obj v (x, a)) '' M.Γ x) ((M.adp.bellman v).toFun x) := by
  obtain ⟨σ, hg, hmax, -⟩ := M.greedy_of_continuousOn hB (M.continuousOn_obj hr (hK v hv))
  have heq : M.adp.bellman v = M.adp.T σ v := ((M.adp.isGreedy_iff ⟨σ, hg⟩ σ).1 hg).symm
  refine ⟨⟨σ, hmax⟩, fun x => ⟨⟨σ.1 x, σ.2.2 x, ?_⟩, ?_⟩⟩
  · rw [heq]
    rfl
  · rintro _ ⟨a, ha, rfl⟩
    rw [heq]
    exact hmax x a ha

end LDP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Feller properties

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.1 (pp. 185–187).

* `shockKernel F φ`: the stochastic kernel `z ↦ law of F(z, W)`, `W ∼ φ`, with
  `∫ h dK(z) = ∫ h(F(z, w)) φ(dw)`.
* **Example 6.1.1**: `(Kh)(x, a) = β(x, a) ∫ h(F(x, a, w)) φ(dw)` is weak Feller when `β` is
  continuous on `G` and `(x, a) ↦ F(x, a, w)` is continuous on `G` for `φ`-almost all `w`.
* **Lemma 6.1.1**: with a density kernel `p` (`∫ p(x, a, x')μ(dx') = 1`) continuous in `(x, a)` for
  `μ`-almost all `x'`, `(Kh)(x, a) = β(x, a) ∫ h(x')p(x, a, x')μ(dx')` is strong Feller. Scheffé's
  lemma (`scheffe`) is proved along the way: `∫ |p(z, ·) − p(z₀, ·)| dμ → 0` as `z → z₀` in `G`.
* **Example 6.1.2**: on a group with a translation-invariant measure,
  `(Kh)(x, a) = β(x) ∫ h(g(x, a) + w)φ(w) dw` with a continuous density `φ` is strong Feller.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

/-! ### Kernels driven by shocks -/

theorem measurable_section {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] {F : Z → W → X} (hF : Measurable (uncurry F)) (z : Z) :
    Measurable (F z) :=
  hF.comp measurable_prodMk_left

/-- The kernel `z ↦ law of F(z, W)` with `W ∼ φ`. -/
noncomputable def shockKernel {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] : Kernel Z X where
  toFun z := φ.map (F z)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    have heq : (fun z => φ.map (F z) s) = fun z => φ (Prod.mk z ⁻¹' (uncurry F ⁻¹' s)) :=
      funext fun z => Measure.map_apply (measurable_section hF z) hs
    rw [heq]
    exact measurable_measure_prodMk_left (hF hs)

theorem shockKernel_apply {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] (z : Z) : shockKernel F hF φ z = φ.map (F z) := rfl

theorem shockKernel_isMarkov {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] : IsMarkovKernel (shockKernel F hF φ) :=
  ⟨fun z => by
    rw [shockKernel_apply]
    infer_instance⟩

/-- `∫ h dK(z) = ∫ h(F(z, w)) φ(dw)`. -/
theorem integral_shockKernel {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] {h : X → ℝ} (hh : Measurable h) (z : Z) :
    ∫ x, h x ∂(shockKernel F hF φ z) = ∫ w, h (F z w) ∂φ := by
  rw [shockKernel_apply, integral_map (measurable_section hF z).aemeasurable
    hh.aestronglyMeasurable]

variable {Y W : Type*} [TopologicalSpace Y] [MeasurableSpace W]

/-- **Example 6.1.1** (p. 186): if `β` is continuous on `G` and `(x, a) ↦ F(x, a, w)` is continuous
on `G` for `φ`-almost all `w`, then `(x, a) ↦ β(x, a) ∫ h(F(x, a, w)) φ(dw)` is continuous on `G`
for every bounded continuous `h`: the kernel is weak Feller. -/
theorem example_6_1_1 [FirstCountableTopology Y] {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X]
    [OpensMeasurableSpace X] {G : Set Y} {β : Y → ℝ} (hβ : ContinuousOn β G) {F : Y → W → X}
    {φ : Measure W} [IsProbabilityMeasure φ] (hFm : ∀ z, Measurable (F z))
    (hFc : ∀ᵐ w ∂φ, ContinuousOn (fun z => F z w) G) {h : X → ℝ} (hc : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ w, h (F z w) ∂φ) G := by
  refine hβ.mul (continuousOn_of_dominated (bound := fun _ => C)
    (fun z _ => (hc.measurable.comp (hFm z)).aestronglyMeasurable)
    (fun z _ => Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hC _)
    (integrable_const C) ?_)
  filter_upwards [hFc] with w hw
  exact hc.comp_continuousOn hw

/-- **Scheffé's lemma** (p. 365) for a density kernel: if `∫ p(z, ·) dμ = 1` on `G` and
`z ↦ p(z, x')` is continuous on `G` for `μ`-almost all `x'`, then
`∫ |p(z, ·) − p(z₀, ·)| dμ → 0` as `z → z₀` within `G`. -/
theorem scheffe [FirstCountableTopology Y] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : Set Y} {p : Y → X → ℝ} (hp0 : ∀ z x, 0 ≤ p z x) (hp1 : ∀ z ∈ G, ∫ x, p z x ∂μ = 1)
    (hpc : ∀ᵐ x ∂μ, ContinuousOn (fun z => p z x) G) {z₀ : Y} (hz₀ : z₀ ∈ G) :
    Tendsto (fun z => ∫ x, |p z x - p z₀ x| ∂μ) (𝓝[G] z₀) (𝓝 0) := by
  have hint : ∀ z ∈ G, Integrable (p z) μ := fun z hz =>
    Integrable.of_integral_ne_zero (by rw [hp1 z hz]; exact one_ne_zero)
  -- `∫ |p_z − p_{z₀}| = 2 ∫ (p_{z₀} − p_z)⁺`
  have hkey : ∀ z ∈ G, ∫ x, |p z x - p z₀ x| ∂μ = 2 * ∫ x, max (p z₀ x - p z x) 0 ∂μ := by
    intro z hz
    have hi1 : Integrable (fun x => p z₀ x - p z x) μ := (hint z₀ hz₀).sub (hint z hz)
    have hi2 : Integrable (fun x => max (p z₀ x - p z x) 0) μ := hi1.pos_part
    have habs : ∀ x, |p z x - p z₀ x| = 2 * max (p z₀ x - p z x) 0 - (p z₀ x - p z x) := by
      intro x
      rcases le_total (p z₀ x) (p z x) with h | h
      · rw [max_eq_right (sub_nonpos.2 h), abs_of_nonneg (sub_nonneg.2 h)]
        ring
      · rw [max_eq_left (sub_nonneg.2 h), abs_of_nonpos (sub_nonpos.2 h)]
        ring
    simp_rw [habs]
    rw [integral_sub (hi2.const_mul 2) hi1, integral_const_mul, integral_sub (hint z₀ hz₀)
      (hint z hz), hp1 z hz, hp1 z₀ hz₀]
    ring
  have hlim : Tendsto (fun z => ∫ x, max (p z₀ x - p z x) 0 ∂μ) (𝓝[G] z₀) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[G] z₀)
      (F := fun z x => max (p z₀ x - p z x) 0) (f := fun _ => (0 : ℝ)) (p z₀)
      (eventually_nhdsWithin_of_forall fun z hz =>
        ((hint z₀ hz₀).sub (hint z hz)).pos_part.aestronglyMeasurable)
      (eventually_nhdsWithin_of_forall fun z _ => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hp0 z x]) (hp0 z₀ x))
      (hint z₀ hz₀) (by
        filter_upwards [hpc] with x hx
        have h1 := ((hx z₀ hz₀).tendsto)
        have h2 := (tendsto_const_nhds (x := p z₀ x)).sub h1
        rw [sub_self] at h2
        have h3 := h2.max (tendsto_const_nhds (x := (0 : ℝ)))
        rwa [max_self] at h3)
    simpa using this
  have := hlim.const_mul 2
  rw [mul_zero] at this
  exact this.congr' (eventually_nhdsWithin_of_forall fun z hz => (hkey z hz).symm)

/-- **Lemma 6.1.1** (p. 187): if `β` is continuous on `G` and `p` is a density kernel with respect
to `μ` such that `(x, a) ↦ p(x, a, x')` is continuous on `G` for `μ`-almost all `x'`, then
`(Kh)(x, a) = β(x, a) ∫ h(x')p(x, a, x')μ(dx')` is continuous on `G` for every bounded measurable
`h`: `K` is strong Feller. -/
theorem lemma_6_1_1 [FirstCountableTopology Y] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : Set Y} {β : Y → ℝ} (hβ : ContinuousOn β G) {p : Y → X → ℝ} (hp0 : ∀ z x, 0 ≤ p z x)
    (hp1 : ∀ z ∈ G, ∫ x, p z x ∂μ = 1) (hpc : ∀ᵐ x ∂μ, ContinuousOn (fun z => p z x) G)
    {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ x, h x * p z x ∂μ) G := by
  refine hβ.mul fun z₀ hz₀ => ?_
  have hint : ∀ z ∈ G, Integrable (p z) μ := fun z hz =>
    Integrable.of_integral_ne_zero (by rw [hp1 z hz]; exact one_ne_zero)
  have hhint : ∀ z ∈ G, Integrable (fun x => h x * p z x) μ := fun z hz =>
    (hint z hz).bdd_mul hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hs := scheffe hp0 hp1 hpc hz₀
  refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ (by simpa using hs.const_mul C))
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← integral_sub (hhint z hz) (hhint z₀ hz₀)]
  calc ‖∫ x, (h x * p z x - h x * p z₀ x) ∂μ‖ ≤ ∫ x, C * |p z x - p z₀ x| ∂μ :=
        norm_integral_le_of_norm_le (((hint z hz).sub (hint z₀ hz₀)).abs.const_mul C)
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _))
    _ = C * ∫ x, |p z x - p z₀ x| ∂μ := integral_const_mul _ _

/-- **Example 6.1.2** (p. 187): on a group `X` with a translation-invariant measure `μ` (Lebesgue
measure on `ℝᵐ`), if `β` and `g` are continuous on `G` and `φ` is a continuous density, then
`(Kh)(x, a) = β(x, a) ∫ h(g(x, a) + w)φ(w)μ(dw)` is continuous on `G` for every bounded measurable
`h`: `K` is strong Feller (change of variable `x' = g(x, a) + w` and Lemma 6.1.1). -/
theorem example_6_1_2 [FirstCountableTopology Y] {X : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.IsAddRightInvariant] {G : Set Y}
    {β : Y → ℝ} (hβ : ContinuousOn β G) {g : Y → X} (hg : ContinuousOn g G) {φ : X → ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∫ x, φ x ∂μ = 1) {h : X → ℝ}
    (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ w, h (g z + w) * φ w ∂μ) G := by
  have heq : ∀ z, ∫ w, h (g z + w) * φ w ∂μ = ∫ x, h x * φ (x - g z) ∂μ := fun z => by
    rw [← integral_sub_right_eq_self (μ := μ) (fun w => h (g z + w) * φ w) (g z)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change h (g z + (x - g z)) * φ (x - g z) = h x * φ (x - g z)
    rw [add_sub_cancel]
  simp_rw [heq]
  exact lemma_6_1_1 hβ (p := fun z x => φ (x - g z)) (fun _ _ => hφ0 _)
    (fun z _ => by rw [integral_sub_right_eq_self (fun x => φ x) (g z)]; exact hφ1)
    (Eventually.of_forall fun x => hφc.comp_continuousOn (continuousOn_const.sub hg)) hm hC

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Maximizers over finite action sets and unique maximizers

Sargent and Stachurski, *Dynamic Programming*, Volume 2, the proof of Lemma 7.1.1 (p. 216) and
the last claim of Theorem A.3.3 (p. 351), as used in Lemma 7.1.2.

* `exists_measurable_argmax`: with finitely many actions, measurable sections `{x | a ∈ Γ(x)}` and
  measurable `x ↦ q(x, a)`, the first maximizer in an enumeration `a₁, …, aₙ` of `A` is a
  measurable selection attaining `max_{a ∈ Γ(x)} q(x, a)`. This is the construction in the proof
  of Lemma 7.1.1.
* `HasContinuousUniqueMax Γ`: the last claim of Theorem A.3.3 (Berge): a selection that is the
  unique maximizer of a function continuous on `G = graph Γ` is continuous. It is proved for the
  interval correspondences `[g(x), h(x)]` of Exercise A.3.1 on any sequential state space
  (`hasContinuousUniqueMax_Icc`): along `xₙ → x`, every subsequence of the maximizers has a further
  subsequence converging to a maximizer at `x`, which must be the unique one.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

variable {X A : Type*}

/-- The construction in the proof of **Lemma 7.1.1** (p. 216): with `A` finite, `{x | a ∈ Γ(x)}`
and `x ↦ q(x, a)` measurable for each `a`, and `Γ` nonempty, the first maximizer in an
enumeration of `A` is a measurable selection attaining `max_{a ∈ Γ(x)} q(x, a)`. -/
theorem exists_measurable_argmax [MeasurableSpace X] [MeasurableSpace A] [Finite A]
    {Γ : X → Set A} (hΓ : ∀ a, MeasurableSet {x | a ∈ Γ x}) (hne : ∀ x, (Γ x).Nonempty)
    {q : X → A → ℝ} (hq : ∀ a, Measurable fun x => q x a) :
    ∃ σ : X → A, Measurable σ ∧ (∀ x, σ x ∈ Γ x) ∧ ∀ x, ∀ a ∈ Γ x, q x a ≤ q x (σ x) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
  -- the indices of the maximizers
  let M : X → Finset (Fin n) := fun x => Finset.univ.filter fun i =>
    e.symm i ∈ Γ x ∧ ∀ j, e.symm j ∈ Γ x → q x (e.symm j) ≤ q x (e.symm i)
  have hM : ∀ x, (M x).Nonempty := fun x => by
    obtain ⟨a, ha⟩ := hne x
    have hF : (Finset.univ.filter fun i : Fin n => e.symm i ∈ Γ x).Nonempty :=
      ⟨e a, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using ha⟩⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun i => q x (e.symm i)) hF
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2,
      fun j hj => hmax j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩⟩
  let idx : X → Fin n := fun x => (M x).min' (hM x)
  have hidx : ∀ x, idx x ∈ M x := fun x => Finset.min'_mem _ _
  have hmemM : ∀ i, MeasurableSet {x | i ∈ M x} := fun i => by
    have heq : {x | i ∈ M x} = {x | e.symm i ∈ Γ x} ∩
        ⋂ j, ({x | e.symm j ∈ Γ x}ᶜ ∪ {x | q x (e.symm j) ≤ q x (e.symm i)}) := by
      ext x
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j => ?_⟩
        by_cases hj : e.symm j ∈ Γ x
        · exact Or.inr (h2 j hj)
        · exact Or.inl hj
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => (h2 j).resolve_left (not_not.2 hj)⟩
    rw [heq]
    exact (hΓ _).inter (MeasurableSet.iInter fun j =>
      (hΓ _).compl.union (measurableSet_le (hq _) (hq _)))
  have hidxm : Measurable idx := by
    refine measurable_to_countable' fun i => ?_
    have heq : idx ⁻¹' {i} = {x | i ∈ M x} ∩ ⋂ j, ({x | j ∈ M x}ᶜ ∪ {_x | i ≤ j}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl
        refine ⟨hidx x, fun j => ?_⟩
        by_cases hj : j ∈ M x
        · exact Or.inr (Finset.min'_le _ j hj)
        · exact Or.inl hj
      · rintro ⟨hi, hmin⟩
        refine le_antisymm (Finset.min'_le _ i hi) (Finset.le_min' _ (hM x) i fun j hj => ?_)
        exact (hmin j).resolve_left (not_not.2 hj)
    rw [heq]
    refine (hmemM i).inter (MeasurableSet.iInter fun j => (hmemM j).compl.union ?_)
    by_cases h' : i ≤ j
    · simp [h']
    · simp [h']
  refine ⟨fun x => e.symm (idx x), (measurable_of_countable _).comp hidxm,
    fun x => (Finset.mem_filter.1 (hidx x)).2.1, fun x a ha => ?_⟩
  have := (Finset.mem_filter.1 (hidx x)).2.2 (e a) (by simpa using ha)
  simpa using this

/-- The last claim of **Theorem A.3.3** (p. 351) for `Γ`: a feasible selection `σ` that is the
unique maximizer of `q(x, ·)` over `Γ(x)`, for `q` continuous on `G = graph Γ`, is continuous. -/
def HasContinuousUniqueMax [TopologicalSpace X] [TopologicalSpace A] (Γ : X → Set A) : Prop :=
  ∀ q : X × A → ℝ, ContinuousOn q {p | p.2 ∈ Γ p.1} → ∀ σ : X → A, (∀ x, σ x ∈ Γ x) →
    (∀ x, ∀ a ∈ Γ x, q (x, a) ≤ q (x, σ x)) →
    (∀ x, ∀ a ∈ Γ x, q (x, σ x) ≤ q (x, a) → a = σ x) → Continuous σ

/-- The last claim of **Theorem A.3.3** for the interval correspondences of Exercise A.3.1: if
`g ≤ h` are continuous, a unique maximizer over `[g(x), h(x)]` of a function continuous on the
graph is continuous in `x`. -/
theorem hasContinuousUniqueMax_Icc [TopologicalSpace X] [SequentialSpace X] {g h : X → ℝ}
    (hg : Continuous g) (hh : Continuous h) (hgh : ∀ x, g x ≤ h x) :
    HasContinuousUniqueMax fun x => Icc (g x) (h x) := by
  intro q hq σ hσ hmax huniq
  refine continuous_iff_seqContinuous.2 fun xs x hx => ?_
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hx' : Tendsto (xs ∘ ns) atTop (𝓝 x) := hx.comp hns
  obtain ⟨φ, hφ, c, hc, hcφ⟩ := exists_subseq_Icc hg hh hx' (ys := fun n => σ (xs (ns n)))
    fun n => hσ (xs (ns n))
  refine ⟨φ, ?_⟩
  have hxφ : Tendsto (xs ∘ ns ∘ φ) atTop (𝓝 x) := hx'.comp hφ.tendsto_atTop
  -- the limit `c` maximizes `q(x, ·)` over `[g(x), h(x)]`
  have hcmax : ∀ b ∈ Icc (g x) (h x), q (x, b) ≤ q (x, c) := by
    intro b hb
    let bs : ℕ → ℝ := fun k => max (g (xs (ns (φ k)))) (min b (h (xs (ns (φ k)))))
    have hbs : Tendsto bs atTop (𝓝 b) := by
      have := ((hg.tendsto x).comp hxφ).max
        ((tendsto_const_nhds (x := b)).min ((hh.tendsto x).comp hxφ))
      rwa [clamp_eq hb] at this
    have hG1 : Tendsto (fun k => ((xs ∘ ns ∘ φ) k, bs k)) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, b)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hbs, Eventually.of_forall fun k =>
        clamp_mem (hgh _) b⟩
    have hG2 : Tendsto (fun k => ((xs ∘ ns ∘ φ) k, σ (xs (ns (φ k))))) atTop
        (𝓝[{p : X × ℝ | p.2 ∈ Icc (g p.1) (h p.1)}] (x, c)) :=
      tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hcφ, Eventually.of_forall fun k => hσ _⟩
    exact le_of_tendsto_of_tendsto' ((hq (x, b) hb).tendsto.comp hG1)
      ((hq (x, c) hc).tendsto.comp hG2) fun k => hmax _ _ (clamp_mem (hgh _) b)
  have hcx : c = σ x := huniq x c hc (hcmax _ (hσ x))
  rw [← hcx]
  exact hcφ

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Recursive decision processes

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.1.1.1 (pp. 208–209), §7.1.2.2
(pp. 213–214) and §7.1.3 (pp. 215–217).

* An RDP `(Γ, V, B)`: a nonempty feasible correspondence `Γ`, a value space `V` of functions
  `X → ℝ` with the pointwise order, and an aggregator `B` that is monotone (7.2) and consistent
  (7.3). The value space is a type `V` with an order embedding `ev : V → ℝ^X`; the book's
  `V ⊆ ℝ^X` is the case where `V` is a subtype and `ev` the inclusion, and the same definition
  covers `bX`, `bℓX₊` and other spaces with their own structure. The aggregator is a function of
  `(x, a)` and of a function `X → ℝ`; only its values on `G × ev(V)` matter.
* §7.1.2.2: the generated ADP `(V, 𝕋)` with `(T_σ v)(x) = B(x, σ(x), v)`; `σ` is `v`-greedy iff
  (7.10) holds; a policy attaining `max_{a ∈ Γ(x)} B(x, a, v)` at every `x` is `v`-greedy and then
  `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)` (7.11).
* **Exercise 7.1.5**: an order isomorphism `φ` of the value ranges with
  `B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]` (7.12) makes the generated ADPs isomorphic.
* **Lemma 7.1.1** (finite actions) and **Lemma 7.1.2** (continuous actions, with Theorem A.3.3 as
  the hypothesis `HasMaxSelections Γ`): greedy policies are the pointwise maximizers, they exist,
  and the Bellman operator is `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)`. Lemma 7.1.1 needs
  `x ↦ B(x, a, v)` and `{x | a ∈ Γ(x)}` measurable, as its proof uses.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

/-- The feasible policies of `Γ` (§7.1.1.1): measurable `σ : X → A` with `σ(x) ∈ Γ(x)`. -/
abbrev FeasiblePolicy {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (Γ : X → Set A) :
    Type _ :=
  {σ : X → A // Measurable σ ∧ ∀ x, σ x ∈ Γ x}

/-- A **recursive decision process** `(Γ, V, B)` (§7.1.1.1): a nonempty feasible correspondence
`Γ`, a value space `V` ordered pointwise through `ev : V → ℝ^X`, and an aggregator `B` satisfying
the monotonicity condition (7.2) and the consistency condition (7.3). -/
structure RDP (X A V : Type*) [MeasurableSpace X] [MeasurableSpace A] [PartialOrder V] where
  /-- the value space as functions `X → ℝ` -/
  ev : V → X → ℝ
  /-- the order of `V` is the pointwise order -/
  ev_le_iff : ∀ v w : V, v ≤ w ↔ ev v ≤ ev w
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the aggregator -/
  B : X → A → (X → ℝ) → ℝ
  /-- the monotonicity condition (7.2) -/
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v w : V, v ≤ w → B x a (ev v) ≤ B x a (ev w)
  /-- the consistency condition (7.3) -/
  consistent : ∀ σ : X → A, Measurable σ → (∀ x, σ x ∈ Γ x) → ∀ v : V,
    ∃ w : V, ev w = fun x => B x (σ x) (ev v)
  /-- `Γ` is nonempty: a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace RDP

variable {X A V : Type*} [MeasurableSpace X] [MeasurableSpace A] [PartialOrder V]
  (R : RDP X A V)

/-- The feasible policies `Σ`. -/
abbrev Policy : Type _ := FeasiblePolicy R.Γ

theorem ev_injective : Injective R.ev := fun v w h =>
  le_antisymm ((R.ev_le_iff v w).2 h.le) ((R.ev_le_iff w v).2 h.ge)

theorem nonempty_Γ (x : X) : (R.Γ x).Nonempty :=
  ⟨R.exists_policy.choose x, R.exists_policy.choose_spec.2 x⟩

/-- The policy operator `(T_σ v)(x) = B(x, σ(x), v)` (§7.1.2.2). -/
noncomputable def T (σ : R.Policy) (v : V) : V := (R.consistent σ.1 σ.2.1 σ.2.2 v).choose

theorem ev_T (σ : R.Policy) (v : V) (x : X) : R.ev (R.T σ v) x = R.B x (σ.1 x) (R.ev v) :=
  congrFun (R.consistent σ.1 σ.2.1 σ.2.2 v).choose_spec x

/-- The ADP `(V, 𝕋)` generated by the RDP (§7.1.2.2). -/
noncomputable def adp : ADP V R.Policy where
  T := R.T
  mono σ v w h := (R.ev_le_iff _ _).2 fun x => by
    rw [R.ev_T, R.ev_T]
    exact R.mono x _ (σ.2.2 x) v w h
  nonempty := ⟨⟨R.exists_policy.choose, R.exists_policy.choose_spec⟩⟩

theorem ev_adp_T (σ : R.Policy) (v : V) (x : X) :
    R.ev (R.adp.T σ v) x = R.B x (σ.1 x) (R.ev v) :=
  R.ev_T σ v x

/-- (7.10): `σ` is `v`-greedy iff `B(x, τ(x), v) ≤ B(x, σ(x), v)` for all `τ ∈ Σ` and `x ∈ X`. -/
theorem isGreedy_iff (v : V) (σ : R.Policy) :
    R.adp.IsGreedy v σ ↔ ∀ τ : R.Policy, ∀ x, R.B x (τ.1 x) (R.ev v) ≤ R.B x (σ.1 x) (R.ev v) := by
  refine forall_congr' fun τ => ?_
  rw [R.ev_le_iff]
  refine forall_congr' fun x => ?_
  rw [R.ev_adp_T, R.ev_adp_T]

/-- `σ` attains `max_{a ∈ Γ(x)} B(x, a, v)` at every `x` ((7.16), (7.18)). -/
def IsArgmax (v : V) (σ : R.Policy) : Prop :=
  ∀ x, ∀ a ∈ R.Γ x, R.B x a (R.ev v) ≤ R.B x (σ.1 x) (R.ev v)

/-- A policy satisfying (7.16) is `v`-greedy (the easy half of Lemmas 7.1.1 (i) and 7.1.2 (i)). -/
theorem isGreedy_of_isArgmax {v : V} {σ : R.Policy} (h : R.IsArgmax v σ) : R.adp.IsGreedy v σ :=
  (R.isGreedy_iff v σ).2 fun τ x => h x _ (τ.2.2 x)

/-- If `σ` attains the maximum at every state, `v ∈ V_G` and the Bellman operator is
`(Tv)(x) = B(x, σ(x), v) = max_{a ∈ Γ(x)} B(x, a, v)` (7.11). -/
theorem bellman_of_isArgmax {v : V} {σ : R.Policy} (h : R.IsArgmax v σ) :
    v ∈ R.adp.VG ∧ (∀ x, R.ev (R.adp.bellman v) x = R.B x (σ.1 x) (R.ev v)) ∧
      ∀ x, IsGreatest ((fun a => R.B x a (R.ev v)) '' R.Γ x) (R.ev (R.adp.bellman v) x) := by
  have hg := R.isGreedy_of_isArgmax h
  have hv : v ∈ R.adp.VG := ⟨σ, hg⟩
  have heq : R.adp.bellman v = R.adp.T σ v := ((R.adp.isGreedy_iff hv σ).1 hg).symm
  have hval : ∀ x, R.ev (R.adp.bellman v) x = R.B x (σ.1 x) (R.ev v) := fun x => by
    rw [heq, R.ev_adp_T]
  refine ⟨hv, hval, fun x => ⟨⟨σ.1 x, σ.2.2 x, (hval x).symm⟩, ?_⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [hval]
  exact h x a ha

/-- If some policy attains the maximum at every state, the `v`-greedy policies are exactly the
policies that do ((7.16), (7.18)): the hard half of Lemmas 7.1.1 (i) and 7.1.2 (i), by
Lemma 2.1.1. -/
theorem isGreedy_iff_isArgmax {v : V} {σ₀ : R.Policy} (h₀ : R.IsArgmax v σ₀) (σ : R.Policy) :
    R.adp.IsGreedy v σ ↔ R.IsArgmax v σ := by
  refine ⟨fun hg x a ha => ?_, R.isGreedy_of_isArgmax⟩
  obtain ⟨hv, hval, -⟩ := R.bellman_of_isArgmax h₀
  have heq : R.adp.T σ v = R.adp.bellman v := (R.adp.isGreedy_iff hv σ).1 hg
  have hx : R.B x (σ.1 x) (R.ev v) = R.B x (σ₀.1 x) (R.ev v) := by
    rw [← R.ev_adp_T, heq, hval]
  rw [hx]
  exact h₀ x a ha

/-- **Lemma 7.1.1** (p. 216): if `A` is finite, and `{x | a ∈ Γ(x)}` and `x ↦ B(x, a, v)` are
measurable for each `a` (as the proof uses), then (i) `σ` is `v`-greedy iff it satisfies (7.16),
(ii) a `v`-greedy policy exists, and (iii) `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)` (7.17). -/
theorem lemma_7_1_1 [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ R.Γ x}) (v : V)
    (hB : ∀ a, Measurable fun x => R.B x a (R.ev v)) :
    (∀ σ : R.Policy, R.adp.IsGreedy v σ ↔ R.IsArgmax v σ) ∧ (∃ σ, R.adp.IsGreedy v σ) ∧
      ∀ x, IsGreatest ((fun a => R.B x a (R.ev v)) '' R.Γ x) (R.ev (R.adp.bellman v) x) := by
  obtain ⟨σ, hσm, hσΓ, hmax⟩ := exists_measurable_argmax hΓ R.nonempty_Γ hB
  let σp : R.Policy := ⟨σ, hσm, hσΓ⟩
  have h₀ : R.IsArgmax v σp := hmax
  exact ⟨R.isGreedy_iff_isArgmax h₀, ⟨σp, R.isGreedy_of_isArgmax h₀⟩,
    (R.bellman_of_isArgmax h₀).2.2⟩

/-- **Lemma 7.1.2** (p. 217): if `Γ` has the maximum theorem (Theorem A.3.3, `HasMaxSelections`)
and `(x, a) ↦ B(x, a, v)` is continuous on `G`, then (i) `σ` is `v`-greedy iff it satisfies (7.18),
(ii) a `v`-greedy policy exists, (iii) `T` is defined at `v`, `Tv` is continuous and
`(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)` (7.19); and a policy that is the unique maximizer at every
state is continuous when `Γ` has the last claim of Theorem A.3.3. -/
theorem lemma_7_1_2 [TopologicalSpace X] [TopologicalSpace A] (hΓ : HasMaxSelections R.Γ)
    (v : V) (hc : ContinuousOn (fun p : X × A => R.B p.1 p.2 (R.ev v)) {p | p.2 ∈ R.Γ p.1}) :
    (∀ σ : R.Policy, R.adp.IsGreedy v σ ↔ R.IsArgmax v σ) ∧ (∃ σ, R.adp.IsGreedy v σ) ∧
      v ∈ R.adp.VG ∧ Continuous (R.ev (R.adp.bellman v)) ∧
      (∀ x, IsGreatest ((fun a => R.B x a (R.ev v)) '' R.Γ x) (R.ev (R.adp.bellman v) x)) ∧
      (HasContinuousUniqueMax R.Γ → ∀ σ : R.Policy, R.IsArgmax v σ →
        (∀ x, ∀ a ∈ R.Γ x, R.B x (σ.1 x) (R.ev v) ≤ R.B x a (R.ev v) → a = σ.1 x) →
        Continuous σ.1) := by
  obtain ⟨σ, hσm, hσΓ, hmax, hcont⟩ := hΓ _ hc
  let σp : R.Policy := ⟨σ, hσm, hσΓ⟩
  have h₀ : R.IsArgmax v σp := hmax
  obtain ⟨hv, hval, hgr⟩ := R.bellman_of_isArgmax h₀
  have hTc : Continuous (R.ev (R.adp.bellman v)) := by
    have : R.ev (R.adp.bellman v) = fun x => R.B x (σ x) (R.ev v) := funext hval
    rw [this]
    exact hcont
  exact ⟨R.isGreedy_iff_isArgmax h₀, ⟨σp, R.isGreedy_of_isArgmax h₀⟩, hv, hTc, hgr,
    fun hU τ hτ huniq => hU _ hc τ.1 τ.2.2 hτ huniq⟩

/-- **Exercise 7.1.5** (p. 214): let `ev(V) ⊆ M^X`, let `φ` be strictly increasing on `M` with
left inverse `φ⁻¹` there, let `V̂ = {φ ∘ v : v ∈ V}`, and let the aggregators be related by (7.12),
`B(x, a, v) = φ⁻¹[B̂(x, a, φ ∘ v)]`. Then `F v = φ ∘ v` is an order isomorphism `V ≃o V̂`
conjugating the policy operators: the generated ADPs are isomorphic. -/
theorem exercise_7_1_5 {V' : Type*} [PartialOrder V'] (R' : RDP X A V') {M : Set ℝ}
    (φ ψ : ℝ → ℝ) (hφ : StrictMonoOn φ M) (hψ : ∀ t ∈ M, ψ (φ t) = t)
    (hM : ∀ v x, R.ev v x ∈ M) (hV : ∀ v : V, ∃ v' : V', R'.ev v' = φ ∘ R.ev v)
    (hV' : ∀ v' : V', ∃ v : V, R'.ev v' = φ ∘ R.ev v)
    (hB : ∀ x, ∀ a ∈ R.Γ x, ∀ v : V, R.B x a (R.ev v) = ψ (R'.B x a (φ ∘ R.ev v))) :
    ∃ F : V ≃o V', (∀ v, R'.ev (F v) = φ ∘ R.ev v) ∧
      ∀ (σ : R.Policy) (σ' : R'.Policy), σ.1 = σ'.1 → ∀ v, F (R.adp.T σ v) = R'.adp.T σ' (F v) := by
  let F : V → V' := fun v => (hV v).choose
  have hF : ∀ v, R'.ev (F v) = φ ∘ R.ev v := fun v => (hV v).choose_spec
  let G : V' → V := fun v' => (hV' v').choose
  have hG : ∀ v', R'.ev v' = φ ∘ R.ev (G v') := fun v' => (hV' v').choose_spec
  -- `φ ∘ ·` is injective and reflects the order on functions with values in `M`
  have hinj : ∀ v w : V, φ ∘ R.ev v = φ ∘ R.ev w → v = w := fun v w h =>
    R.ev_injective (funext fun x => hφ.injOn (hM v x) (hM w x) (congrFun h x))
  have hle : ∀ v w : V, φ ∘ R.ev v ≤ φ ∘ R.ev w ↔ v ≤ w := fun v w => by
    rw [R.ev_le_iff]
    exact forall_congr' fun x => hφ.le_iff_le (hM v x) (hM w x)
  have hGF : ∀ v, G (F v) = v := fun v => hinj _ _ (by rw [← hG, hF])
  have hFG : ∀ v', F (G v') = v' := fun v' => R'.ev_injective (by rw [hF, hG])
  let e : V ≃ V' := ⟨F, G, hGF, hFG⟩
  refine ⟨⟨e, fun {v w} => ?_⟩, hF, fun σ σ' hσ v => R'.ev_injective (funext fun x => ?_)⟩
  · change F v ≤ F w ↔ v ≤ w
    rw [R'.ev_le_iff, hF, hF]
    exact hle v w
  · change R'.ev (F (R.adp.T σ v)) x = R'.ev (R'.adp.T σ' (F v)) x
    rw [hF, Function.comp_apply, R.ev_adp_T, R'.ev_adp_T, hF, hB x _ (σ.2.2 x), ← hσ]
    -- `B̂(x, σ(x), φ ∘ v)` is a value of `T̂_σ(Fv) ∈ V̂ = φ ∘ V`, so lies in `φ(M)`
    obtain ⟨w, hw⟩ := hV' (R'.adp.T σ' (F v))
    have hval : R'.B x (σ.1 x) (φ ∘ R.ev v) = φ (R.ev w x) := by
      rw [← Function.comp_apply (f := φ) (g := R.ev w), ← hw, R'.ev_adp_T, hF, hσ]
    rw [hval, hψ _ (hM w x)]

end RDP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Bounded contracting RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.1 (pp. 218–220).

* §7.2.1.1: value space `V = bX`, an aggregator `B` with `(x, a) ↦ B(x, a, v)` measurable (on
  `X × A`; values off `G` are irrelevant) and monotone in `v`. With `B` bounded in `(x, a) ∈ G` for
  each `v`, `(Γ, bX, B)` is an RDP (`BRDP.toRDP`). The book's "the function `B` is bounded" must be
  read for each fixed `v`: with Blackwell's condition, `v ↦ B(x, a, v)` is unbounded on `bX`.
* Assumption 7.2.1: Blackwell's condition `B(x, a, v + κ) ≤ B(x, a, v) + λκ`, `λ ∈ [0, 1)`.
* **Proposition 7.2.1** (finite actions): the fundamental optimality properties hold, VFI
  converges geometrically on `V` and OPI and HPI converge; if `X` is also finite, HPI reaches `v*`
  in finitely many steps.
* **Proposition 7.2.2** (continuous case): under Assumption 7.2.2 (the maximum theorem for `Γ` and
  `B` continuous on `G` for `v ∈ bcX`), the fundamental optimality properties hold, `v* ∈ bcX` and
  VFI converges geometrically on `bcX`; under Assumption 7.2.3 OPI and HPI converge.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The framework of §7.2.1.1, with `B` bounded on `G` for each `v` (Assumption 7.2.1, first
part): value space `bX`, `B` measurable and monotone in `v`. -/
structure BRDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the aggregator -/
  B : X → A → (X → ℝ) → ℝ
  /-- `(x, a) ↦ B(x, a, v)` is measurable -/
  measurable : ∀ v : BM X, Measurable fun p : X × A => B p.1 p.2 v.toFun
  /-- `B` is monotone in `v` on `G` -/
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v w : BM X, v ≤ w → B x a v.toFun ≤ B x a w.toFun
  /-- `B` is bounded on `G` for each `v` -/
  bdd : ∀ v : BM X, ∃ C, ∀ x, ∀ a ∈ Γ x, |B x a v.toFun| ≤ C
  /-- a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace BRDP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : BRDP X A)

/-- §7.2.1.1 (p. 218): `(Γ, bX, B)` is an RDP. -/
noncomputable def toRDP : RDP X A (BM X) where
  ev := BM.toFun
  ev_le_iff _ _ := Iff.rfl
  Γ := M.Γ
  B := M.B
  mono := M.mono
  consistent σ hσ hσΓ v := by
    obtain ⟨C, hC⟩ := M.bdd v
    exact ⟨⟨fun x => M.B x (σ x) v.toFun, (M.measurable v).comp (measurable_id.prodMk hσ),
      ⟨C, fun x => hC x _ (hσΓ x)⟩⟩, rfl⟩
  exists_policy := M.exists_policy

theorem toRDP_T_apply (σ : M.toRDP.Policy) (v : BM X) (x : X) :
    (M.toRDP.adp.T σ v).toFun x = M.B x (σ.1 x) v.toFun :=
  M.toRDP.ev_adp_T σ v x

/-- Blackwell's condition (Assumption 7.2.1): `B(x, a, v + κ) ≤ B(x, a, v) + λκ` on `G`. -/
def IsBlackwell (lam : ℝ) : Prop :=
  ∀ x, ∀ a ∈ M.Γ x, ∀ v : BM X, ∀ κ : ℝ, 0 ≤ κ →
    M.B x a (fun y => v.toFun y + κ) ≤ M.B x a v.toFun + lam * κ

/-- Blackwell's condition for the policy operators, with `e = 𝟙`. -/
theorem T_blackwell {lam : ℝ} (hB : M.IsBlackwell lam) (σ : M.toRDP.Policy) (v : BM X)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    M.toRDP.adp.T σ (v + κ • BM.const 1) ≤ M.toRDP.adp.T σ v + (lam * κ) • BM.const 1 := by
  refine BM.le_def.2 fun x => ?_
  have h1 : (v + κ • BM.const 1).toFun = fun y => v.toFun y + κ := funext fun y => by
    simp [BM.const_apply]
  change (M.toRDP.adp.T σ (v + κ • BM.const 1)).toFun x ≤
    (M.toRDP.adp.T σ v).toFun x + lam * κ * 1
  rw [M.toRDP_T_apply, M.toRDP_T_apply, h1, mul_one]
  exact hB x _ (σ.2.2 x) v κ hκ

/-- With finitely many actions and measurable sections `{x | a ∈ Γ(x)}`, the RDP is regular
(Lemma 7.1.1). -/
theorem regular_of_finite [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) :
    M.toRDP.adp.Regular := fun v =>
  (M.toRDP.lemma_7_1_1 hΓ v fun _ =>
    (M.measurable v).comp (measurable_id.prodMk measurable_const)).2.1

/-- **Proposition 7.2.1** (p. 219): under Assumption 7.2.1, with `A` finite (and measurable
sections `{x | a ∈ Γ(x)}`), (i) the fundamental optimality properties hold, (ii) VFI converges
geometrically on `V = bX`, and (iii) OPI and HPI converge. -/
theorem proposition_7_2_1 [Nonempty X] [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x})
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.toRDP.adp.VFIGeometric univ vstar ∧
        ∀ g, M.toRDP.adp.IsSelector g →
          M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar := by
  have hr := M.regular_of_finite hΓ
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB)
    ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv hr⟩

/-- **Proposition 7.2.1**, last claim (p. 219): if `X` is also finite, the fundamental optimality
properties hold and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`
(Lemma 3.1.1 and Theorem 2.2.6). -/
theorem proposition_7_2_1_finite [Nonempty X] [Finite X] [Finite A]
    (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∀ g, M.toRDP.adp.IsSelector g → ∀ v ∈ M.toRDP.adp.VU,
        ∃ n, M.toRDP.adp.IsValueFunction ((M.toRDP.adp.howard hw g)^[n] v) := by
  have hT : ∀ σ v w, dist (M.toRDP.adp.T σ v) (M.toRDP.adp.T σ w) ≤ lam * dist v w := by
    intro σ v w
    rw [dist_eq_norm, dist_eq_norm]
    exact BanachLattice.lemma_4_1_2 BM.isNormalizedOrderUnit_one (M.toRDP.adp.mono σ) hlam0
      (M.T_blackwell hB σ) v w
  have hgs := ADP.isGloballyStable_of_contraction ⟨0⟩ hlam0 hlam1 hT
  have hfin : M.toRDP.adp.IsFinite := Set.finite_range _
  exact ⟨_, ADP.fundamentalOptimality_of_finite hgs.isOrderStable (M.regular_of_finite hΓ) hfin⟩

/-- Under Assumption 7.2.2, a greedy policy exists at every `v ∈ bcX` and `Tv ∈ bcX`
(Lemma 7.1.2). -/
theorem greedy_of_continuous [TopologicalSpace X] [TopologicalSpace A]
    (hΓ : HasMaxSelections M.Γ) {v : BM X}
    (hc : ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) :
    v ∈ M.toRDP.adp.VG ∧ Continuous (M.toRDP.adp.bellman v).toFun := by
  obtain ⟨-, -, hv, hTc, -⟩ := M.toRDP.lemma_7_1_2 hΓ v hc
  exact ⟨hv, hTc⟩

/-- **Proposition 7.2.2** (p. 220): under Assumptions 7.2.1 and 7.2.2 (the maximum theorem for `Γ`,
Theorem A.3.3, and `B` continuous on `G` for `v ∈ bcX`), (i) the fundamental optimality properties
hold, (ii) `v* ∈ bcX` and (iii) VFI converges geometrically on `bcX`. Under Assumption 7.2.3
(`B` continuous on `G` for every `v ∈ bX`), OPI and HPI also converge. -/
theorem proposition_7_2_2 [Nonempty X] [TopologicalSpace X] [TopologicalSpace A]
    (hΓ : HasMaxSelections M.Γ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam)
    (hc : ∀ v : BM X, Continuous v.toFun →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc X, M.toRDP.adp.VFIGeometric (LDP.bc X) vstar ∧
        ((∀ v : BM X, ContinuousOn (fun p : X × A => M.B p.1 p.2 v.toFun) {p | p.2 ∈ M.Γ p.1}) →
          ∀ g, M.toRDP.adp.IsSelector g →
            M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar) := by
  have hsr : M.toRDP.adp.IsSemiRegular (LDP.bc X) :=
    ⟨LDP.isClosed_bc, fun v hv => (M.greedy_of_continuous hΓ (hc v hv)).1,
      fun v hv => (M.greedy_of_continuous hΓ (hc v hv)).2⟩
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3_univ
    BM.isNormalizedOrderUnit_one M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) hsr
    ⟨0, LDP.zero_mem_bc⟩
  exact ⟨hw, hFO, vstar, hv, hgeo, fun hall =>
    hconv fun v => (M.greedy_of_continuous hΓ (hall v)).1⟩

end BRDP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Weighted contractions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.2 (pp. 220–223), with the weighted
supremum norm spaces of §A.5.3.5 (pp. 382–383).

* Weighted spaces (§A.5.3.5): for a weight function `ℓ ≥ 1`, `v ↦ v / ℓ` maps `bℓX` onto `bX`,
  preserving the order and carrying `‖·‖ℓ` to the supremum norm (`norm_eq_wnorm`). So `bℓX` is a
  Banach lattice (Theorem A.5.24) and `ℓ` is a normalized order unit (Exercise A.5.25): both are
  transported from `bX` and `𝟙`. The value space `bℓX₊` is represented by the closed cone `bX₊`
  through `v = ℓh` (`wev`), with `bℓcX₊` the continuous `h` when `ℓ` is continuous.
  **Exercises A.5.22** and **A.5.24** are proved.
* §7.2.2.1: a nonnegative aggregator on `bℓX₊`, measurable and monotone, with (U2)
  `B(x, a, v) ≤ M + Nℓ(x)`. **Lemma 7.2.3**: `(Γ, bℓX₊, B)` is an RDP (`WRDP.toRDP`).
* (U1): `B(x, a, v + κℓ) ≤ B(x, a, v) + λκℓ(x)`, `λ ∈ [0, 1)`.
* **Proposition 7.2.4** (finite actions) and **Proposition 7.2.5** (continuous case), by
  Theorem 4.1.3 with `E = bX` (`= bℓX`), `e = 𝟙` (`= ℓ`) and `V = bX₊` (`= bℓX₊`).
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Weighted supremum norm spaces -/

/-- The `ℓ`-weighted supremum norm `‖v‖ℓ = sup_x |v(x)| / ℓ(x)` (§A.5.3.5). -/
noncomputable def wnorm (ℓ : X → ℝ) (v : X → ℝ) : ℝ := ⨆ x, |v x| / ℓ x

/-- `bℓX`: measurable `v` with `‖v‖ℓ < ∞`, i.e. `|v| ≤ Cℓ` (§A.5.3.5). -/
def bl (ℓ : X → ℝ) : Set (X → ℝ) := {v | Measurable v ∧ ∃ C, ∀ x, |v x| ≤ C * ℓ x}

/-- `bℓX₊`: the nonnegative functions in `bℓX`. -/
def blPlus (ℓ : X → ℝ) : Set (X → ℝ) :=
  {v | Measurable v ∧ (∀ x, 0 ≤ v x) ∧ ∃ C, ∀ x, v x ≤ C * ℓ x}

/-- The weighted function `x ↦ ℓ(x)h(x)` of `h ∈ bX`. -/
def wevB (ℓ : X → ℝ) (h : BM X) : X → ℝ := fun x => ℓ x * h.toFun x

theorem wevB_mem {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : BM X) :
    wevB ℓ h ∈ bl ℓ := by
  refine ⟨hℓm.mul h.measurable', ‖h‖, fun x => ?_⟩
  rw [wevB, abs_mul, abs_of_pos (zero_lt_one.trans_le (hℓ1 x)), mul_comm ‖h‖]
  exact mul_le_mul_of_nonneg_left (BM.abs_le_norm h x) (zero_lt_one.trans_le (hℓ1 x)).le

/-- The weighted norm of `ℓh` is the supremum norm of `h`: `v ↦ v / ℓ` is an isometry of `bℓX`
onto `bX`, so `bℓX` is a Banach lattice (Theorem A.5.24). -/
theorem norm_eq_wnorm {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : BM X) :
    ‖h‖ = wnorm ℓ (wevB ℓ h) := by
  rw [BM.norm_def, BM.supNorm, wnorm]
  refine congrArg iSup (funext fun x => ?_)
  have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
  rw [wevB, abs_mul, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne']

/-- **Exercise A.5.22** (p. 383): `bX ⊆ bℓX`. -/
theorem exercise_A_5_22 {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (v : BM X) : v.toFun ∈ bl ℓ :=
  ⟨v.measurable', ‖v‖, fun x => (BM.abs_le_norm v x).trans
    (le_mul_of_one_le_right (norm_nonneg _) (hℓ1 x))⟩

/-- **Exercise A.5.24** (p. 383): convergence in `bℓX` implies pointwise convergence. -/
theorem exercise_A_5_24 {ℓ : X → ℝ} {hs : ℕ → BM X} {h : BM X}
    (hlim : Tendsto hs atTop (𝓝 h)) (x : X) :
    Tendsto (fun n => wevB ℓ (hs n) x) atTop (𝓝 (wevB ℓ h x)) :=
  ((BM.tendstoUniformly_of_tendsto hlim).tendsto_at x).const_mul (ℓ x)

/-- **Exercise A.5.25** (p. 383): `ℓ = ℓ · 𝟙` corresponds to the normalized order unit `𝟙` of
`bX`. -/
theorem exercise_A_5_25 [Nonempty X] (ℓ : X → ℝ) :
    wevB ℓ (BM.const 1) = ℓ ∧ BanachLattice.IsNormalizedOrderUnit (BM.const 1 : BM X) :=
  ⟨funext fun _ => mul_one _, BM.isNormalizedOrderUnit_one⟩

/-- The cone `bX₊`. -/
def posCone (X : Type*) [MeasurableSpace X] : Set (BM X) := {h | 0 ≤ h}

theorem isClosed_posCone : IsClosed (posCone X) := by
  refine isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_
  have hu := BM.tendstoUniformly_of_tendsto hlim
  exact BM.le_def.2 fun x => ge_of_tendsto (hu.tendsto_at x)
    (Eventually.of_forall fun n => BM.le_def.1 (hhs n) x)

theorem add_mem_posCone {h : BM X} (hh : h ∈ posCone X) {κ : ℝ} (hκ : 0 ≤ κ) :
    h + κ • BM.const 1 ∈ posCone X :=
  BM.le_def.2 fun x => by
    have := BM.le_def.1 hh x
    simp only [BM.zero_apply, BM.add_apply, BM.smul_apply, BM.const_apply] at this ⊢
    nlinarith

/-- The value `v = ℓh ∈ bℓX₊` of `h ∈ bX₊`. -/
def wev (ℓ : X → ℝ) (h : posCone X) : X → ℝ := wevB ℓ h.1

theorem wev_mem {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : posCone X) :
    wev ℓ h ∈ blPlus ℓ := by
  refine ⟨hℓm.mul h.1.measurable', fun x => mul_nonneg (zero_le_one.trans (hℓ1 x))
    (BM.le_def.1 h.2 x), ‖h.1‖, fun x => ?_⟩
  rw [wev, wevB, mul_comm ‖h.1‖]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (BM.abs_le_norm h.1 x))
    (zero_le_one.trans (hℓ1 x))

/-- `v / ℓ ∈ bX₊` for `v ∈ bℓX₊`. -/
noncomputable def ofBl {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ blPlus ℓ) : posCone X :=
  ⟨⟨fun x => v x / ℓ x, hv.1.div hℓm, by
    obtain ⟨C, hC⟩ := hv.2.2
    refine ⟨C, fun x => ?_⟩
    have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
    rw [abs_of_nonneg (div_nonneg (hv.2.1 x) hpos.le), div_le_iff₀ hpos]
    exact hC x⟩,
    BM.le_def.2 fun x => div_nonneg (hv.2.1 x) (zero_le_one.trans (hℓ1 x))⟩

theorem wev_ofBl {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ blPlus ℓ) : wev ℓ (ofBl hℓm hℓ1 hv) = v :=
  funext fun x => mul_div_cancel₀ _ (zero_lt_one.trans_le (hℓ1 x)).ne'

theorem wev_le_iff {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (h h' : posCone X) :
    h ≤ h' ↔ wev ℓ h ≤ wev ℓ h' := by
  change (∀ x, h.1.toFun x ≤ h'.1.toFun x) ↔ ∀ x, ℓ x * h.1.toFun x ≤ ℓ x * h'.1.toFun x
  exact forall_congr' fun x => (mul_le_mul_iff_of_pos_left (zero_lt_one.trans_le (hℓ1 x))).symm

/-- `bℓcX₊` inside `bℓX₊`: the `h` with `ℓh` continuous, i.e. `h` continuous when `ℓ` is. -/
def bcPlus (X : Type*) [MeasurableSpace X] [TopologicalSpace X] : Set (posCone X) :=
  {h | Continuous h.1.toFun}

theorem isClosed_bcPlus [TopologicalSpace X] : IsClosed (bcPlus X) :=
  LDP.isClosed_bc.preimage continuous_subtype_val

theorem zero_mem_bcPlus [TopologicalSpace X] :
    (⟨0, BM.le_def.2 fun _ => le_rfl⟩ : posCone X) ∈ bcPlus X :=
  continuous_const

/-! ### The weighted RDP framework -/

/-- The framework of §7.2.2.1 with condition (U2): a weight function `ℓ ≥ 1`, value space
`bℓX₊`, and an aggregator that is measurable, nonnegative and monotone on `bℓX₊`, with
`B(x, a, v) ≤ M + Nℓ(x)` on `G` for each `v`. -/
structure WRDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the weight function -/
  ℓ : X → ℝ
  measurable_ℓ : Measurable ℓ
  one_le_ℓ : ∀ x, 1 ≤ ℓ x
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the aggregator -/
  B : X → A → (X → ℝ) → ℝ
  /-- `(x, a) ↦ B(x, a, v)` is measurable -/
  measurable : ∀ v ∈ blPlus ℓ, Measurable fun p : X × A => B p.1 p.2 v
  /-- `B` is nonnegative on `G` -/
  nonneg : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ blPlus ℓ, 0 ≤ B x a v
  /-- `B` is monotone in `v` on `G` -/
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ blPlus ℓ, ∀ w ∈ blPlus ℓ, v ≤ w → B x a v ≤ B x a w
  /-- (U2) -/
  U2 : ∀ v ∈ blPlus ℓ, ∃ M N : ℝ, 0 ≤ M ∧ 0 ≤ N ∧ ∀ x, ∀ a ∈ Γ x, B x a v ≤ M + N * ℓ x
  /-- a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace WRDP

variable (M : WRDP X A)

/-- **Lemma 7.2.3** (p. 221): `(Γ, bℓX₊, B)` is an RDP. -/
noncomputable def toRDP : RDP X A (posCone X) where
  ev := wev M.ℓ
  ev_le_iff := wev_le_iff M.one_le_ℓ
  Γ := M.Γ
  B := M.B
  mono x a ha v w hvw := M.mono x a ha _ (wev_mem M.measurable_ℓ M.one_le_ℓ v) _
    (wev_mem M.measurable_ℓ M.one_le_ℓ w) ((wev_le_iff M.one_le_ℓ v w).1 hvw)
  consistent σ hσ hσΓ v := by
    have hv := wev_mem M.measurable_ℓ M.one_le_ℓ v
    obtain ⟨K, N, hK, hN, hKN⟩ := M.U2 _ hv
    have hm : (fun x => M.B x (σ x) (wev M.ℓ v)) ∈ blPlus M.ℓ :=
      ⟨(M.measurable _ hv).comp (measurable_id.prodMk hσ),
        fun x => M.nonneg x _ (hσΓ x) _ hv, K + N, fun x => by
          have h1 := hKN x _ (hσΓ x)
          have h2 := M.one_le_ℓ x
          nlinarith⟩
    exact ⟨ofBl M.measurable_ℓ M.one_le_ℓ hm, wev_ofBl _ _ hm⟩
  exists_policy := M.exists_policy

theorem toRDP_T_apply (σ : M.toRDP.Policy) (h : posCone X) (x : X) :
    M.ℓ x * (M.toRDP.adp.T σ h).1.toFun x = M.B x (σ.1 x) (wev M.ℓ h) :=
  M.toRDP.ev_adp_T σ h x

/-- Condition (U1): `B(x, a, v + κℓ) ≤ B(x, a, v) + λκℓ(x)` on `G` for `v ∈ bℓX₊`, `κ ≥ 0`. -/
def IsBlackwell (lam : ℝ) : Prop :=
  ∀ x, ∀ a ∈ M.Γ x, ∀ v ∈ blPlus M.ℓ, ∀ κ : ℝ, 0 ≤ κ →
    M.B x a (fun y => v y + κ * M.ℓ y) ≤ M.B x a v + lam * κ * M.ℓ x

/-- (U1) gives Blackwell's condition (4.4) for the policy operators on `bX₊` with `e = 𝟙`. -/
theorem T_blackwell {lam : ℝ} (hB : M.IsBlackwell lam) (σ : M.toRDP.Policy) (h : posCone X)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ((M.toRDP.adp.T σ ⟨h.1 + κ • BM.const 1, add_mem_posCone h.2 hκ⟩ : posCone X) : BM X) ≤
      (M.toRDP.adp.T σ h : BM X) + (lam * κ) • BM.const 1 := by
  refine BM.le_def.2 fun x => ?_
  have hpos : 0 < M.ℓ x := zero_lt_one.trans_le (M.one_le_ℓ x)
  have hw : wev M.ℓ ⟨h.1 + κ • BM.const 1, add_mem_posCone h.2 hκ⟩ =
      fun y => wev M.ℓ h y + κ * M.ℓ y := funext fun y => by
    simp only [wev, wevB, BM.add_apply, BM.smul_apply, BM.const_apply]
    ring
  refine le_of_mul_le_mul_left ?_ hpos
  rw [M.toRDP_T_apply, hw]
  simp only [BM.add_apply, BM.smul_apply, BM.const_apply]
  calc M.B x (σ.1 x) (fun y => wev M.ℓ h y + κ * M.ℓ y)
      ≤ M.B x (σ.1 x) (wev M.ℓ h) + lam * κ * M.ℓ x :=
        hB x _ (σ.2.2 x) _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) κ hκ
    _ = M.ℓ x * ((M.toRDP.adp.T σ h).1.toFun x + lam * κ * 1) := by
        rw [mul_add, M.toRDP_T_apply]
        ring

/-- With finitely many actions and measurable sections `{x | a ∈ Γ(x)}`, the RDP is regular
(Lemma 7.1.1). -/
theorem regular_of_finite [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) :
    M.toRDP.adp.Regular := fun h =>
  (M.toRDP.lemma_7_1_1 hΓ h fun _ =>
    (M.measurable _ (wev_mem M.measurable_ℓ M.one_le_ℓ h)).comp
      (measurable_id.prodMk measurable_const)).2.1

/-- **Proposition 7.2.4** (p. 222): under (U1)–(U2), with `A` finite (and measurable sections
`{x | a ∈ Γ(x)}`), (i) the fundamental optimality properties hold, (ii) VFI converges
geometrically on `V = bℓX₊`, and (iii) OPI and HPI converge. -/
theorem proposition_7_2_4 [Nonempty X] [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x})
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.toRDP.adp.VFIGeometric univ vstar ∧
        ∀ g, M.toRDP.adp.IsSelector g →
          M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar := by
  have hr := M.regular_of_finite hΓ
  have : Nonempty (posCone X) := ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3
    BM.isNormalizedOrderUnit_one isClosed_posCone (fun _ hv _ hκ => add_mem_posCone hv hκ)
    M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩
    univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv hr⟩

/-- **Proposition 7.2.4**, last claim (p. 222): if `X` is also finite, the fundamental optimality
properties hold and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`. -/
theorem proposition_7_2_4_finite [Nonempty X] [Finite X] [Finite A]
    (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∀ g, M.toRDP.adp.IsSelector g → ∀ v ∈ M.toRDP.adp.VU,
        ∃ n, M.toRDP.adp.IsValueFunction ((M.toRDP.adp.howard hw g)^[n] v) := by
  have : CompleteSpace (posCone X) := isClosed_posCone.completeSpace_coe
  have hT : ∀ σ v w, dist (M.toRDP.adp.T σ v) (M.toRDP.adp.T σ w) ≤ lam * dist v w :=
    fun σ => BanachLattice.lemma_4_1_2_subtype BM.isNormalizedOrderUnit_one
      (fun _ hv _ hκ => add_mem_posCone hv hκ) (M.toRDP.adp.mono σ) hlam0 (M.T_blackwell hB σ)
  have hgs := ADP.isGloballyStable_of_contraction ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩ hlam0
    hlam1 hT
  have hfin : M.toRDP.adp.IsFinite := Set.finite_range _
  exact ⟨_, ADP.fundamentalOptimality_of_finite hgs.isOrderStable (M.regular_of_finite hΓ) hfin⟩

variable [TopologicalSpace X] [TopologicalSpace A]

/-- Under Assumption 7.2.6, for `h ∈ bℓcX₊` (`ℓh` continuous) a greedy policy exists, it attains
`max_{a ∈ Γ(x)} B(x, a, ℓh)`, `Th ∈ bℓcX₊`, and `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)`
(Lemma 7.1.2). -/
theorem greedy_of_continuous (hℓc : Continuous M.ℓ) (hΓ : HasMaxSelections M.Γ)
    (hc : ∀ v ∈ blPlus M.ℓ, Continuous v →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1})
    {h : posCone X} (hh : h ∈ bcPlus X) :
    h ∈ M.toRDP.adp.VG ∧ M.toRDP.adp.bellman h ∈ bcPlus X ∧
      (∃ σ, M.toRDP.IsArgmax h σ) ∧
      ∀ x, IsGreatest ((fun a => M.B x a (wev M.ℓ h)) '' M.Γ x)
        (wev M.ℓ (M.toRDP.adp.bellman h) x) := by
  have hcont : Continuous (wev M.ℓ h) := hℓc.mul hh
  obtain ⟨hiff, ⟨σ, hg⟩, hv, hTc, hgr, -⟩ := M.toRDP.lemma_7_1_2 hΓ h
    (hc _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) hcont)
  refine ⟨hv, ?_, ⟨σ, (hiff σ).1 hg⟩, hgr⟩
  have heq : (M.toRDP.adp.bellman h).1.toFun =
      fun x => wev M.ℓ (M.toRDP.adp.bellman h) x / M.ℓ x := funext fun x => by
    rw [wev, wevB, mul_div_cancel_left₀ _ (zero_lt_one.trans_le (M.one_le_ℓ x)).ne']
  change Continuous (M.toRDP.adp.bellman h).1.toFun
  rw [heq]
  exact hTc.div hℓc fun x => (zero_lt_one.trans_le (M.one_le_ℓ x)).ne'

/-- **Proposition 7.2.5** (p. 222): under (U1)–(U2) and Assumption 7.2.6 (`ℓ` continuous, the
maximum theorem for `Γ`, and `B` continuous on `G` for `v ∈ bℓcX₊`), (i) the fundamental optimality
properties hold, (ii) `v* ∈ bℓcX₊` and (iii) VFI converges geometrically on `bℓcX₊`. Under
Assumption 7.2.7 (`B` continuous on `G` for every `v ∈ bℓX₊`), OPI and HPI also converge. -/
theorem proposition_7_2_5 [Nonempty X] (hℓc : Continuous M.ℓ) (hΓ : HasMaxSelections M.Γ)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam)
    (hc : ∀ v ∈ blPlus M.ℓ, Continuous v →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, Continuous (wev M.ℓ vstar) ∧
        M.toRDP.adp.VFIGeometric (bcPlus X) vstar ∧
        ((∀ v ∈ blPlus M.ℓ, ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}) →
          ∀ g, M.toRDP.adp.IsSelector g →
            M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar) := by
  have hsr : M.toRDP.adp.IsSemiRegular (bcPlus X) :=
    ⟨isClosed_bcPlus, fun _ hh => (M.greedy_of_continuous hℓc hΓ hc hh).1,
      fun _ hh => (M.greedy_of_continuous hℓc hΓ hc hh).2.1⟩
  have : Nonempty (posCone X) := ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3
    BM.isNormalizedOrderUnit_one isClosed_posCone (fun _ hv _ hκ => add_mem_posCone hv hκ)
    M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) hsr ⟨_, zero_mem_bcPlus⟩
  refine ⟨hw, hFO, vstar, hv, hℓc.mul hv, hgeo, fun hall => hconv fun h => ?_⟩
  obtain ⟨-, ⟨σ, hg⟩, -⟩ := M.toRDP.lemma_7_1_2 hΓ h
    (hall _ (wev_mem M.measurable_ℓ M.one_le_ℓ h))
  exact ⟨σ, hg⟩

end WRDP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Properties of solutions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.3 (pp. 223–225), with Lemma A.2.6
(p. 346).

The setting is that of Proposition 7.2.5 (`WRDP.ContinuousCase`).

* **Lemma A.2.6**: a closed set that is invariant under a map whose iterates converge to `v̄`
  contains `v̄`.
* **Exercise 7.2.1**: the increasing functions in `bℓcX₊` form a closed set.
* **Proposition 7.2.6**: under Assumption 7.2.8 (`Γ` increasing and `B(x, a, v) ≤ B(x', a, v)` for
  `x ⪯ x'` and increasing `v`), `v*` is increasing.
* **Proposition 7.2.7**: under Assumption 7.2.9 (`G` convex and `B` concave on `G` for concave `v`),
  `v*` is concave. The state space is a convex set `S` in a vector space `X` (the book takes `X`
  itself convex in a vector space); `G` and the concavity of `v*` are restricted to `S`.
* **Proposition 7.2.8**: under Assumption 7.2.10 (strict concavity in `a`), the optimal policy is
  unique and, with the last claim of Theorem A.3.3 for `Γ`, continuous.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- **Lemma A.2.6** (p. 346): if `Sⁿu → v̄` for every `u ∈ U`, `U` is closed and nonempty, and
`SU ⊆ U`, then `v̄ ∈ U`. -/
theorem lemma_A_2_6 {V : Type*} [TopologicalSpace V] {S : V → V} {vbar : V} {U : Set V}
    (hS : ∀ u ∈ U, Tendsto (fun n => S^[n] u) atTop (𝓝 vbar)) (hU : IsClosed U)
    (hSU : MapsTo S U U) (hne : U.Nonempty) : vbar ∈ U := by
  obtain ⟨u, hu⟩ := hne
  exact hU.mem_of_tendsto (hS u hu) (Eventually.of_forall fun n => hSU.iterate n hu)

/-- A strictly concave function has at most one maximizer. -/
theorem eq_of_isMax_of_strictConcaveOn {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    {f : E → ℝ} (hf : StrictConcaveOn ℝ s f) {a b : E} (ha : a ∈ s) (hb : b ∈ s)
    (hamax : ∀ c ∈ s, f c ≤ f a) (hbmax : ∀ c ∈ s, f c ≤ f b) : a = b := by
  by_contra hne
  have hlt := hf.2 ha hb hne (one_half_pos (α := ℝ)) one_half_pos (add_halves 1)
  have hmid := hamax _ (hf.1 ha hb (one_half_pos (α := ℝ)).le one_half_pos.le (add_halves 1))
  have hab : f a = f b := le_antisymm (hbmax a ha) (hamax b hb)
  rw [smul_eq_mul, smul_eq_mul, hab] at hlt
  rw [hab] at hmid
  linarith

/-- Geometric convergence of VFI on `V₀` gives `Tⁿv → v*` for `v ∈ V₀`. -/
theorem ADP.VFIGeometric.tendsto {V P : Type*} [PartialOrder V] [MetricSpace V] {A : ADP V P}
    {V₀ : Set V} {vstar : V} (h : A.VFIGeometric V₀ vstar) {v : V} (hv : v ∈ V₀) :
    Tendsto (fun n => A.bellman^[n] v) atTop (𝓝 vstar) := by
  obtain ⟨-, β, hβ0, hβ1, hC⟩ := h
  obtain ⟨C, hC⟩ := hC v hv
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hC ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [TopologicalSpace X]
  [TopologicalSpace A]

/-- The zero of `bX₊`. -/
noncomputable def coneZero (X : Type*) [MeasurableSpace X] : posCone X :=
  ⟨0, BM.le_def.2 fun _ => le_rfl⟩

omit [TopologicalSpace X] in
theorem wev_coneZero (ℓ : X → ℝ) : wev ℓ (coneZero X) = 0 :=
  funext fun x => by simp [wev, wevB, coneZero, BM.zero_apply]

/-- **Exercise 7.2.1** (p. 223): the increasing functions in `bℓcX₊` form a closed set. -/
theorem exercise_7_2_1 [Preorder X] (ℓ : X → ℝ) :
    IsClosed {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev ℓ h)} := by
  refine isClosed_bcPlus.inter (isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_)
  have hlim' : Tendsto (fun n => (hs n).1) atTop (𝓝 h.1) :=
    (continuous_subtype_val.tendsto h).comp hlim
  intro x y hxy
  exact le_of_tendsto_of_tendsto' (exercise_A_5_24 hlim' x) (exercise_A_5_24 hlim' y)
    fun n => hhs n hxy

namespace WRDP

variable (M : WRDP X A)

/-- The hypotheses of Proposition 7.2.5: (U1)–(U2) with `λ ∈ [0, 1)` and Assumption 7.2.6. -/
structure ContinuousCase : Prop where
  ℓ_continuous : Continuous M.ℓ
  maxSel : HasMaxSelections M.Γ
  blackwell : ∃ lam, 0 ≤ lam ∧ lam < 1 ∧ M.IsBlackwell lam
  continuousOn : ∀ v ∈ blPlus M.ℓ, Continuous v →
    ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}

variable {M}

/-- Proposition 7.2.5 in the form used below. -/
theorem ContinuousCase.prop [Nonempty X] (hM : M.ContinuousCase) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.VFIGeometric (bcPlus X) vstar := by
  obtain ⟨lam, hlam0, hlam1, hB⟩ := hM.blackwell
  obtain ⟨hw, hFO, vstar, hv, -, hgeo, -⟩ := M.proposition_7_2_5 hM.ℓ_continuous hM.maxSel hlam0
    hlam1 hB hM.continuousOn
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-- The value function lies in every closed `T`-invariant subset of `bℓcX₊` that contains `0`
(Lemma A.2.6). -/
theorem ContinuousCase.vstar_mem [Nonempty X] (hM : M.ContinuousCase) {U : Set (posCone X)}
    (hU : IsClosed U) (hUV : U ⊆ bcPlus X) (hT : MapsTo M.toRDP.adp.bellman U U)
    (h0 : coneZero X ∈ U) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ U, M.toRDP.adp.VFIGeometric (bcPlus X) vstar := by
  obtain ⟨hw, hFO, vstar, -, hgeo⟩ := hM.prop
  exact ⟨hw, hFO, vstar, lemma_A_2_6 (fun u hu => hgeo.tendsto (hUV hu)) hU hT ⟨_, h0⟩, hgeo⟩

/-- **Proposition 7.2.6** (p. 224): under the conditions of Proposition 7.2.5 and Assumption 7.2.8
(`Γ(x) ⊆ Γ(x')` and `B(x, a, v) ≤ B(x', a, v)` for `x ⪯ x'`, `a ∈ Γ(x)` and increasing
`v ∈ bℓcX₊`), the value function `v*` is increasing. -/
theorem proposition_7_2_6 [Nonempty X] [Preorder X] (hM : M.ContinuousCase)
    (hΓmono : ∀ x x', x ≤ x' → M.Γ x ⊆ M.Γ x')
    (hBmono : ∀ x x', x ≤ x' → ∀ v ∈ blPlus M.ℓ, Continuous v → Monotone v →
      ∀ a ∈ M.Γ x, M.B x a v ≤ M.B x' a v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.IsValueFunction vstar ∧ Monotone (wev M.ℓ vstar) := by
  have hT : MapsTo M.toRDP.adp.bellman {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev M.ℓ h)}
      {h : posCone X | h ∈ bcPlus X ∧ Monotone (wev M.ℓ h)} := by
    rintro h ⟨hc, hmono⟩
    obtain ⟨-, hTb, -, hgr⟩ := M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hc
    refine ⟨hTb, fun x x' hxx' => ?_⟩
    obtain ⟨⟨a, ha, hax⟩, -⟩ := hgr x
    rw [← hax]
    exact (hBmono x x' hxx' _ (wev_mem M.measurable_ℓ M.one_le_ℓ h)
      (hM.ℓ_continuous.mul hc) hmono a ha).trans ((hgr x').2 ⟨a, hΓmono x x' hxx' ha, rfl⟩)
  obtain ⟨hw, hFO, vstar, hv, hgeo⟩ := hM.vstar_mem (exercise_7_2_1 M.ℓ) (fun _ h => h.1) hT
    ⟨zero_mem_bcPlus, by rw [wev_coneZero]; exact monotone_const⟩
  exact ⟨hw, hFO, vstar, hv.1, hgeo.1, hv.2⟩

variable [AddCommGroup X] [Module ℝ X] [AddCommGroup A] [Module ℝ A]

omit [MeasurableSpace A] [TopologicalSpace A] [AddCommGroup A] [Module ℝ A] in
/-- The functions in `bℓcX₊` that are concave on `S` form a closed set. -/
theorem isClosed_concave (ℓ : X → ℝ) (S : Set X) (hS : Convex ℝ S) :
    IsClosed {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev ℓ h)} := by
  refine isClosed_bcPlus.inter (isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_)
  have hlim' : Tendsto (fun n => (hs n).1) atTop (𝓝 h.1) :=
    (continuous_subtype_val.tendsto h).comp hlim
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  exact le_of_tendsto_of_tendsto' (((exercise_A_5_24 hlim' x).const_smul a).add
    ((exercise_A_5_24 hlim' y).const_smul b)) (exercise_A_5_24 hlim' _)
    fun n => (hhs n).2 hx hy ha hb hab

/-- The graph of `Γ` over `S`. -/
def feasibleOn (Γ : X → Set A) (S : Set X) : Set (X × A) := {p | p.1 ∈ S ∧ p.2 ∈ Γ p.1}

/-- **Proposition 7.2.7** (p. 224): under the conditions of Proposition 7.2.5 and Assumption 7.2.9
(the feasible pairs over a convex `S` form a convex set and `(x, a) ↦ B(x, a, v)` is concave on
them whenever `v ∈ bℓcX₊` is concave on `S`), the value function `v*` is concave on `S`. -/
theorem proposition_7_2_7 [Nonempty X] (hM : M.ContinuousCase) {S : Set X} (hS : Convex ℝ S)
    (hG : Convex ℝ (feasibleOn M.Γ S))
    (hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      ConcaveOn ℝ (feasibleOn M.Γ S) fun p => M.B p.1 p.2 v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, M.toRDP.adp.IsValueFunction vstar ∧ ConcaveOn ℝ S (wev M.ℓ vstar) := by
  have hT : MapsTo M.toRDP.adp.bellman
      {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev M.ℓ h)}
      {h : posCone X | h ∈ bcPlus X ∧ ConcaveOn ℝ S (wev M.ℓ h)} := by
    rintro h ⟨hc, hconc⟩
    obtain ⟨-, hTb, ⟨σ, hσ⟩, hgr⟩ :=
      M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hc
    obtain ⟨-, hval, -⟩ := M.toRDP.bellman_of_isArgmax hσ
    refine ⟨hTb, hS, fun x hx y hy a b ha hb hab => ?_⟩
    have hp : (x, σ.1 x) ∈ feasibleOn M.Γ S := ⟨hx, σ.2.2 x⟩
    have hq : (y, σ.1 y) ∈ feasibleOn M.Γ S := ⟨hy, σ.2.2 y⟩
    have hmem := hG hp hq ha hb hab
    have hineq := (hBc _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) (hM.ℓ_continuous.mul hc)
      hconc).2 hp hq ha hb hab
    change a • wev M.ℓ (M.toRDP.adp.bellman h) x + b • wev M.ℓ (M.toRDP.adp.bellman h) y ≤
      wev M.ℓ (M.toRDP.adp.bellman h) (a • x + b • y)
    have h1 : wev M.ℓ (M.toRDP.adp.bellman h) x = M.B x (σ.1 x) (wev M.ℓ h) := hval x
    have h2 : wev M.ℓ (M.toRDP.adp.bellman h) y = M.B y (σ.1 y) (wev M.ℓ h) := hval y
    rw [h1, h2]
    exact hineq.trans ((hgr _).2 ⟨_, hmem.2, rfl⟩)
  obtain ⟨hw, hFO, vstar, hv, hgeo⟩ := hM.vstar_mem (isClosed_concave M.ℓ S hS)
    (fun _ h => h.1) hT ⟨zero_mem_bcPlus, by rw [wev_coneZero]; exact concaveOn_const 0 hS⟩
  exact ⟨hw, hFO, vstar, hv.1, hgeo.1, hv.2⟩

/-- **Proposition 7.2.8** (p. 225): under the conditions of Proposition 7.2.7 and
Assumption 7.2.10 (`a ↦ B(x, a, v)` strictly concave on `Γ(x)` for every `x` and every `v ∈ bℓcX₊`
concave on `S`), the optimal policy is unique; it is continuous when `Γ` has the last claim of
Theorem A.3.3 (`HasContinuousUniqueMax`). -/
theorem proposition_7_2_8 [Nonempty X] (hM : M.ContinuousCase) {S : Set X} (hS : Convex ℝ S)
    (hG : Convex ℝ (feasibleOn M.Γ S))
    (hBc : ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      ConcaveOn ℝ (feasibleOn M.Γ S) fun p => M.B p.1 p.2 v)
    (hstrict : ∀ x, ∀ v ∈ blPlus M.ℓ, Continuous v → ConcaveOn ℝ S v →
      StrictConcaveOn ℝ (M.Γ x) fun a => M.B x a v) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ σ, M.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, M.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        (HasContinuousUniqueMax M.Γ → Continuous σ.1) := by
  obtain ⟨hw, hFO, vstar, hv, hvf, hconc⟩ := M.proposition_7_2_7 hM hS hG hBc
  have hvc : Continuous (wev M.ℓ vstar) := hM.ℓ_continuous.mul hv
  have hvm := wev_mem M.measurable_ℓ M.one_le_ℓ vstar
  obtain ⟨hiff, -, -, -, -, hcont⟩ := M.toRDP.lemma_7_1_2 hM.maxSel vstar
    (hM.continuousOn _ hvm hvc)
  obtain ⟨-, -, ⟨σ, hσ⟩, -⟩ :=
    M.greedy_of_continuous hM.ℓ_continuous hM.maxSel hM.continuousOn hv
  -- maximizers of the strictly concave `a ↦ B(x, a, v*)` coincide
  have huniq : ∀ x, ∀ a ∈ M.Γ x, M.B x (σ.1 x) (wev M.ℓ vstar) ≤ M.B x a (wev M.ℓ vstar) →
      a = σ.1 x := fun x a ha hle =>
    eq_of_isMax_of_strictConcaveOn (hstrict x _ hvm hvc hconc) ha (σ.2.2 x)
      (fun c hc => (hσ x c hc).trans hle) (hσ x)
  have hopt : ∀ τ, M.toRDP.adp.IsOptimal hw τ ↔ M.toRDP.IsArgmax vstar τ := fun τ => by
    rw [hFO.2.2 τ]
    constructor
    · rintro ⟨w, hw', hg⟩
      rw [hw'.unique hvf] at hg
      exact (hiff τ).1 hg
    · exact fun h => ⟨vstar, hvf, (hiff τ).2 h⟩
  refine ⟨hw, hFO, σ, (hopt σ).2 hσ, fun τ hτ => ?_, fun hU => hcont hU σ hσ huniq⟩
  have hτ' := (hopt τ).1 hτ
  exact Subtype.ext (funext fun x => huniq x _ (τ.2.2 x) (hτ' x _ (σ.2.2 x)))

end WRDP

end SargentStachurski.AdditionalApplications

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

namespace SargentStachurski.AdditionalApplications

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

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimization on pospaces

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.1.3 (pp. 101–103).

Min-OPI and min-HPI are defined with min-greedy selectors, and every min-notion is transported
from the dual ADP `(V, 𝕋)^∂` (Exercises 2.2.4 and 2.2.6).

* Global stability transfers to the dual (the dual carries the same topology).
* **Theorem 3.1.6** (min-version of Theorem 3.1.2) and **Theorem 3.1.8** (min-version of
  Theorem 3.1.4).
* **Theorem 3.1.7** (min-version of Theorem 3.1.5). The book's proof applies Theorem 3.1.5 to the
  dual, which needs the metric to be sup-nonexpansive for the *reversed* order, i.e.
  inf-nonexpansive. That does not follow from sup-nonexpansiveness: `vShape_sup_not_inf` is a
  three-point poset with a sup-nonexpansive metric that is not inf-nonexpansive. Theorem 3.1.7 is
  proved here under inf-nonexpansiveness.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- A min-greedy selector: a choice of `v`-min-greedy policy at every `v`. -/
def IsMinSelector (g : V → P) : Prop := ∀ v, A.IsMinGreedy v (g v)

variable (A) in
/-- min-OPI converges: `W▿ⁿv ↓ v▿*` for all `v ∈ V_D` and every step size `m ≥ 1`. -/
def MinOPIConverges (g : V → P) (vstar : V) : Prop :=
  ∀ m, 1 ≤ m → ∀ v ∈ A.VD, DecreasesTo (fun n => (A.opt m g)^[n] v) vstar

variable (A) in
/-- min-HPI converges: `H▿ⁿv ↓ v▿*` for all `v ∈ V_D`. -/
def MinHPIConverges (hw : A.WellPosed) (g : V → P) (vstar : V) : Prop :=
  ∀ v ∈ A.VD, DecreasesTo (fun n => (A.howard hw g)^[n] v) vstar

/-- Min-greedy selectors of `A` are the greedy selectors of `A^∂`. -/
theorem isMinSelector_iff (g : V → P) :
    A.IsMinSelector g ↔ A.dual.IsSelector (g ∘ OrderDual.ofDual) :=
  ⟨fun h v => h (OrderDual.ofDual v), fun h v => h (OrderDual.toDual v)⟩

/-- Iterates of `W▿` are the iterates of the dual's `W`. -/
theorem dual_opt_iterate (m : ℕ) (g : V → P) (n : ℕ) (v : V) :
    (A.dual.opt m (g ∘ OrderDual.ofDual))^[n] (OrderDual.toDual v) =
      OrderDual.toDual ((A.opt m g)^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    exact (congrArg _ (dualMap_iterate _ m _)).trans (ih _)

/-- Iterates of `H▿` are the iterates of the dual's `H`. -/
theorem dual_howard_iterate (hw : A.WellPosed) (g : V → P) (n : ℕ) (v : V) :
    (A.dual.howard hw.dual (g ∘ OrderDual.ofDual))^[n] (OrderDual.toDual v) =
      OrderDual.toDual ((A.howard hw g)^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    exact (congrArg _ (dual_opt_howard hw 0 g v).2).trans (ih _)

/-- min-OPI convergence for `A` is OPI convergence for `A^∂` (Exercise 2.2.6). -/
theorem minOPIConverges_iff (g : V → P) (vstar : V) :
    A.MinOPIConverges g vstar ↔
      A.dual.OPIConverges (g ∘ OrderDual.ofDual) (OrderDual.toDual vstar) := by
  refine forall₂_congr fun m _ => ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.ofDual v) hv
    have he : (fun n => (A.dual.opt m (g ∘ OrderDual.ofDual))^[n] v) =
        fun n => OrderDual.toDual ((A.opt m g)^[n] (OrderDual.ofDual v)) :=
      funext fun n => dual_opt_iterate m g n (OrderDual.ofDual v)
    rw [he]
    exact ⟨fun a b hab => hm hab, hl⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.toDual v) hv
    rw [funext fun n => dual_opt_iterate m g n v] at hm hl
    exact ⟨fun a b hab => hm hab, hl⟩

/-- min-HPI convergence for `A` is HPI convergence for `A^∂` (Exercise 2.2.6). -/
theorem minHPIConverges_iff (hw : A.WellPosed) (g : V → P) (vstar : V) :
    A.MinHPIConverges hw g vstar ↔
      A.dual.HPIConverges hw.dual (g ∘ OrderDual.ofDual) (OrderDual.toDual vstar) := by
  refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.ofDual v) hv
    have he : (fun n => (A.dual.howard hw.dual (g ∘ OrderDual.ofDual))^[n] v) =
        fun n => OrderDual.toDual ((A.howard hw g)^[n] (OrderDual.ofDual v)) :=
      funext fun n => dual_howard_iterate hw g n (OrderDual.ofDual v)
    rw [he]
    exact ⟨fun a b hab => hm hab, hl⟩
  · obtain ⟨hm, hl⟩ := h (OrderDual.toDual v) hv
    rw [funext fun n => dual_howard_iterate hw g n v] at hm hl
    exact ⟨fun a b hab => hm hab, hl⟩

/-- Assembling the min-conclusions from the dual's max-conclusions (Exercise 2.2.6). -/
theorem min_of_dual {hw : A.WellPosed}
    (h : A.dual.FundamentalOptimality hw.dual ∧
      ∃ vstar, A.dual.IsValueFunction vstar ∧ A.dual.VFIConverges vstar ∧
        ∀ g, A.dual.IsSelector g → A.dual.OPIConverges g vstar ∧
          A.dual.HPIConverges hw.dual g vstar) :
    A.MinFundamentalOptimality hw ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧ A.MinHPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, hvs, hvfi, hconv⟩ := h
  refine ⟨(minFundamentalOptimality_iff hw).2 hFO, OrderDual.ofDual vstar, hvs,
    (minVFIConverges_iff _).2 hvfi, fun g hg => ?_⟩
  obtain ⟨h1, h2⟩ := hconv _ ((isMinSelector_iff g).1 hg)
  exact ⟨(minOPIConverges_iff g _).2 h1, (minHPIConverges_iff hw g _).2 h2⟩

variable [TopologicalSpace V]

/-- Global stability is self-dual: `(V, 𝕋)^∂` carries the same topology. -/
theorem IsGloballyStable.dual (h : A.IsGloballyStable) : A.dual.IsGloballyStable := fun σ => by
  obtain ⟨u, hu, huniq, hlim⟩ := h σ
  refine ⟨OrderDual.toDual u, congrArg OrderDual.toDual hu, fun w hw =>
    congrArg OrderDual.toDual (huniq (OrderDual.ofDual w) (congrArg OrderDual.ofDual hw)),
    fun w => ?_⟩
  change Tendsto (fun k => (dualMap (A.T σ))^[k] w) atTop _
  rw [funext fun k => dualMap_iterate (A.T σ) k w]
  exact hlim (OrderDual.ofDual w)

variable [OrderClosedTopology V]

/-- **Theorem 3.1.6** (p. 102): if `(V, 𝕋)` is min-regular and globally stable and `T▿` has a
fixed point, then (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI
and min-HPI all converge. -/
theorem theorem_3_1_6 (hr : A.MinRegular) (hgs : A.IsGloballyStable) {w : V}
    (hfix : A.SolvesMinBellman w) :
    A.MinFundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges hgs.wellPosed g vstar := by
  have hrd := (minRegular_iff A).1 hr
  exact min_of_dual (theorem_3_1_2 hrd hgs.dual
    ((A.dual.solvesBellman_iff (hrd (OrderDual.toDual w))).1 hfix))

/-- **Theorem 3.1.8** (p. 102): if `(V, 𝕋)` is min-regular, globally stable and min-order bounded,
and `V` is countably Dedekind complete, then (i) the fundamental min-optimality properties hold and
(ii) min-VFI, min-OPI and min-HPI all converge. -/
theorem theorem_3_1_8 (hr : A.MinRegular) (hgs : A.IsGloballyStable) (hb : A.MinOrderBounded)
    (hV : CountablyDedekindComplete V) :
    A.MinFundamentalOptimality hgs.wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges hgs.wellPosed g vstar :=
  min_of_dual (theorem_3_1_4 ((minRegular_iff A).1 hr) hgs.dual ((minOrderBounded_iff A).1 hb)
    hV.dual)

end ADP

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

/-- **Theorem 3.1.7** (p. 102), with the inf-nonexpansiveness its proof needs: if `(V, 𝕋)` is
min-regular, the metric is complete and inf-nonexpansive, and each `T_σ` is a contraction of
modulus `β`, then (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI and
min-HPI all converge. -/
theorem theorem_3_1_7 [MetricSpace V] [OrderClosedTopology V] [CompleteSpace V] [Nonempty V]
    (hr : A.MinRegular) (hd : IsInfNonexpansive (dist : V → V → ℝ)) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hT : ∀ σ v w, dist (A.T σ v) (A.T σ w) ≤ β * dist v w) :
    A.MinFundamentalOptimality (isGloballyStable_of_contraction ‹_› hβ0 hβ1 hT).wellPosed ∧
      ∃ vstar, A.IsMinValueFunction vstar ∧ A.MinVFIConverges vstar ∧
        ∀ g, A.IsMinSelector g → A.MinOPIConverges g vstar ∧
          A.MinHPIConverges (isGloballyStable_of_contraction ‹_› hβ0 hβ1 hT).wellPosed g
            vstar := by
  have : CompleteSpace Vᵒᵈ := ‹CompleteSpace V›
  have : OrderClosedTopology Vᵒᵈ := ⟨isClosed_le_prod' (α := V)⟩
  have hrd := (minRegular_iff A).1 hr
  have hdd : IsSupNonexpansive (dist : Vᵒᵈ → Vᵒᵈ → ℝ) := (isInfNonexpansive_iff _).1 hd
  have hTd : ∀ σ v w, dist (A.dual.T σ v) (A.dual.T σ w) ≤ β * dist v w := fun σ v w =>
    hT σ (OrderDual.ofDual v) (OrderDual.ofDual w)
  obtain ⟨hFO, vstar, -, ⟨hvs, -⟩, hconv⟩ := theorem_3_1_5 (A := A.dual) hdd hβ0 hβ1 hTd
    ⟨isClosed_univ, fun v _ => hrd v, mapsTo_univ _ _⟩ univ_nonempty
  obtain ⟨v', -, -, -, hv'G, hv'b⟩ := hFO.exists_vstar
  obtain ⟨-, w, hw, hvfi, -⟩ := theorem_3_1_2 hrd (isGloballyStable_of_contraction
    (A := A.dual) ⟨OrderDual.toDual (Classical.arbitrary V)⟩ hβ0 hβ1 hTd)
    ((A.dual.solvesBellman_iff hv'G).1 hv'b)
  refine min_of_dual ⟨hFO, vstar, hvs, ?_, hconv hrd⟩
  rw [hvs.unique hw]
  exact hvfi

end ADP

/-! ### Sup-nonexpansive does not imply inf-nonexpansive -/

/-- The three-point poset `0 < 1`, `0 < 2` with `1, 2` incomparable, on `Fin 3`. -/
abbrev vShapeOrder : PartialOrder (Fin 3) where
  le a b := a = 0 ∨ a = b
  lt a b := (a = 0 ∨ a = b) ∧ ¬(b = 0 ∨ b = a)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with h | h
    · exact Or.inl h
    · rcases hbc with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h.trans h')
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · rcases hba with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

/-- The distance on the three-point poset: `d(1, 2) = 1` and `d(0, 1) = d(0, 2) = 3/2`. -/
noncomputable def vShapeDist (a b : Fin 3) : ℝ :=
  if a = b then 0 else if a = 0 ∨ b = 0 then 3 / 2 else 1

/-- `vShapeDist` is a metric. -/
theorem vShapeDist_metric :
    (∀ a, vShapeDist a a = 0) ∧ (∀ a b, vShapeDist a b = vShapeDist b a) ∧
      (∀ a b, vShapeDist a b = 0 → a = b) ∧
        ∀ a b c, vShapeDist a c ≤ vShapeDist a b + vShapeDist b c := by
  refine ⟨fun a => by simp [vShapeDist], fun a b => ?_, fun a b => ?_, fun a b c => ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [vShapeDist]
  · fin_cases a <;> fin_cases b <;> norm_num [vShapeDist]
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [vShapeDist]

/-- Suprema in the three-point poset: `⋁ T = 0` forces `T ⊆ {0}`, and `⋁ T = a ≠ 0` forces
`a ∈ T`. -/
theorem vShape_isLUB {T : Set (Fin 3)} {a : Fin 3} (h : @IsLUB (Fin 3) vShapeOrder.toLE T a) :
    (a = 0 → ∀ t ∈ T, t = 0) ∧ (a ≠ 0 → a ∈ T) := by
  refine ⟨fun ha t ht => ?_, fun ha => ?_⟩
  · rcases h.1 ht with h' | h'
    · exact h'
    · exact h'.trans ha
  · by_contra hT
    have hub : (0 : Fin 3) ∈ @upperBounds (Fin 3) vShapeOrder.toLE T := fun t ht => by
      rcases h.1 ht with h' | h'
      · exact Or.inl h'
      · exact absurd (h' ▸ ht) hT
    rcases h.2 hub with h' | h'
    · exact ha h'
    · exact ha h'

/-- **Sup-nonexpansive does not imply inf-nonexpansive.** On the three-point poset, `vShapeDist`
is a sup-nonexpansive metric (the order is closed, the metric being discrete) but it is not
inf-nonexpansive: `⋀{1, 2} = 0` and `⋀{1} = 1`, while `d(1, 1) = 0`, `d(2, 1) = 1` and
`d(0, 1) = 3/2`. -/
theorem vShape_sup_not_inf :
    @IsSupNonexpansive (Fin 3) vShapeOrder vShapeDist ∧
      ¬ @IsInfNonexpansive (Fin 3) vShapeOrder vShapeDist := by
  refine ⟨fun S a b c hc ha hb hS => ?_, fun h => ?_⟩
  · by_cases hab : a = b
    · simp [vShapeDist, hab, hc]
    obtain ⟨ha0, ha1⟩ := vShape_isLUB ha
    obtain ⟨hb0, hb1⟩ := vShape_isLUB hb
    by_cases hA : a = 0
    · obtain ⟨p, hp, hpb⟩ := hb1 (fun h0 => hab (hA.trans h0.symm))
      have hp1 : p.1 = a := (ha0 hA p.1 ⟨p, hp, rfl⟩).trans hA.symm
      have := hS p hp
      rwa [hp1, hpb] at this
    by_cases hB : b = 0
    · obtain ⟨p, hp, hpa⟩ := ha1 hA
      have hp2 : p.2 = b := (hb0 hB p.2 ⟨p, hp, rfl⟩).trans hB.symm
      have := hS p hp
      rwa [hpa, hp2] at this
    · obtain ⟨p, hp, hpa⟩ := ha1 hA
      have hle : vShapeDist a b ≤ vShapeDist p.1 p.2 := by
        rw [hpa]
        rcases hb.1 ⟨p, hp, rfl⟩ with h0 | h0
        · rw [h0]
          revert hA hB hab
          fin_cases a <;> fin_cases b <;> norm_num [vShapeDist]
        · rw [h0]
      exact hle.trans (hS p hp)
  · have hfst : Prod.fst '' ({((1 : Fin 3), (1 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))} :
        Set (Fin 3 × Fin 3)) = {1, 2} := by
      simp [image_insert_eq]
    have hsnd : Prod.snd '' ({((1 : Fin 3), (1 : Fin 3)), ((2 : Fin 3), (1 : Fin 3))} :
        Set (Fin 3 × Fin 3)) = {1} := by
      simp [image_insert_eq]
    have hglb1 : @IsGLB (Fin 3) vShapeOrder.toLE {1, 2} 0 := by
      refine ⟨fun t _ => Or.inl rfl, fun l hl => ?_⟩
      have h1 : l = 0 ∨ l = 1 := hl (mem_insert 1 {2})
      have h2 : l = 0 ∨ l = 2 := hl (mem_insert_of_mem 1 (mem_singleton 2))
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact absurd (h1.symm.trans h2) (by decide)
    have hglb2 : @IsGLB (Fin 3) vShapeOrder.toLE {1} 1 :=
      ⟨fun t ht => Or.inr (mem_singleton_iff.1 ht).symm, fun l hl => hl (mem_singleton 1)⟩
    rw [← hfst] at hglb1
    rw [← hsnd] at hglb2
    have key := h _ 0 1 1 zero_le_one hglb1 hglb2 (by
      intro p hp
      simp only [mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> norm_num [vShapeDist])
    norm_num [vShapeDist] at key

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conjugate dynamical systems

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.1 (pp. 148–151).

* Conjugacy (§5.1.1.1): `F` a bijection with `F ∘ S = Ŝ ∘ F`, i.e. `Function.Semiconj F S Ŝ`.
  **Proposition 5.1.1** (iterates, fixed points, unique fixed points; part (iv) is
  **Exercise 5.1.1**), **Example 5.1.1** (log-linearization) and **Example 5.1.2**
  (diagonalization).
* Topological conjugacy (§5.1.1.2): **Proposition 5.1.2** (global stability transfers) and
  **Example 5.1.3** (`Aᵏx → 0` for all `x` iff every eigenvalue of `A` has modulus below one).
* Order conjugacy (§5.1.1.3): **Exercise 5.1.2** (an equivalence relation) and **Lemma 5.1.3**
  (order stability and strong order stability transfer; **Exercise 5.1.3**).
-/

open Set Function Filter Topology
open scoped Matrix

namespace SargentStachurski.AdditionalApplications

/-! ### Conjugacy -/

/-- `v` is the unique fixed point of `S`. -/
def IsUniqueFixed {V : Type*} (S : V → V) (v : V) : Prop := S v = v ∧ ∀ w, S w = w → w = v

/-- `(V, S)` and `(V̂, Ŝ)` are conjugate under the bijection `F` (§5.1.1.1): `F ∘ S = Ŝ ∘ F`. -/
def IsConjugate {V W : Type*} (F : V ≃ W) (S : V → V) (Sh : W → W) : Prop := Semiconj F S Sh

namespace IsConjugate

variable {V W : Type*} {F : V ≃ W} {S : V → V} {Sh : W → W}

/-- The inverse conjugacy: `F⁻¹ ∘ Ŝ = S ∘ F⁻¹`. -/
theorem symm (h : IsConjugate F S Sh) : IsConjugate F.symm Sh S := fun w => by
  apply F.injective
  rw [Equiv.apply_symm_apply, h (F.symm w), Equiv.apply_symm_apply]

/-- **Proposition 5.1.1 (i)** (p. 149): `Sⁿ = F⁻¹ Ŝⁿ F`. -/
theorem iterate (h : IsConjugate F S Sh) (n : ℕ) (v : V) : S^[n] v = F.symm (Sh^[n] (F v)) := by
  rw [← (Semiconj.iterate_right h n) v, Equiv.symm_apply_apply]

/-- **Proposition 5.1.1 (ii)**: `v` is fixed for `S` iff `Fv` is fixed for `Ŝ`. -/
theorem fixed_iff (h : IsConjugate F S Sh) (v : V) : S v = v ↔ Sh (F v) = F v := by
  rw [← h v, F.apply_eq_iff_eq]

/-- **Proposition 5.1.1 (iii)**: `v̂` is fixed for `Ŝ` iff `F⁻¹v̂` is fixed for `S`. -/
theorem fixed_iff_symm (h : IsConjugate F S Sh) (w : W) : Sh w = w ↔ S (F.symm w) = F.symm w :=
  h.symm.fixed_iff w

/-- **Proposition 5.1.1 (iv)** (p. 149) and **Exercise 5.1.1**: `v` is the unique fixed point
of `S` iff `Fv` is the unique fixed point of `Ŝ`. -/
theorem isUniqueFixed_iff (h : IsConjugate F S Sh) (v : V) :
    IsUniqueFixed S v ↔ IsUniqueFixed Sh (F v) := by
  constructor
  · rintro ⟨hv, huniq⟩
    refine ⟨(h.fixed_iff v).1 hv, fun w hw => ?_⟩
    rw [← huniq _ ((h.fixed_iff_symm w).1 hw), Equiv.apply_symm_apply]
  · rintro ⟨hv, huniq⟩
    refine ⟨(h.fixed_iff v).2 hv, fun w hw => F.injective (huniq _ ((h.fixed_iff w).1 hw))⟩

end IsConjugate

/-- **Example 5.1.1** (p. 149): `Sx = ax + b` on `ℝ` is conjugate under `exp` to its
log-linearization `Ŝy = e^b y^a` on `(0, ∞)`. -/
theorem example_5_1_1 (a b : ℝ) :
    IsConjugate Real.expOrderIso.toEquiv (fun x => a * x + b)
      (fun y => ⟨Real.exp b * (y : ℝ) ^ a, mul_pos (Real.exp_pos b) (Real.rpow_pos_of_pos y.2 a)⟩)
      := fun x => by
  apply Subtype.ext
  change Real.exp (a * x + b) = Real.exp b * Real.exp x ^ a
  rw [← Real.exp_mul, ← Real.exp_add, mul_comm x a, add_comm]

/-! ### Diagonalization -/

/-- The coordinate change `x ↦ E⁻¹x` for an invertible matrix `E`. -/
def coordChange {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) :
    (m → ℝ) ≃ (m → ℝ) where
  toFun x := (↑E⁻¹ : Matrix m m ℝ) *ᵥ x
  invFun y := (↑E : Matrix m m ℝ) *ᵥ y
  left_inv x := by dsimp only; rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  right_inv y := by dsimp only; rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/-- **Example 5.1.2** (p. 149): if `A = EDE⁻¹`, then `(ℝᵐ, A)` and `(ℝᵐ, D)` are conjugate under
`F = E⁻¹`. -/
theorem example_5_1_2 {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) (d : m → ℝ)
    {A : Matrix m m ℝ}
    (hA : A = (↑E : Matrix m m ℝ) * Matrix.diagonal d * (↑E⁻¹ : Matrix m m ℝ)) :
    IsConjugate (coordChange E) (A *ᵥ ·) (Matrix.diagonal d *ᵥ ·) := fun x => by
  change (↑E⁻¹ : Matrix m m ℝ) *ᵥ (A *ᵥ x) = Matrix.diagonal d *ᵥ ((↑E⁻¹ : Matrix m m ℝ) *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

/-! ### Topological conjugacy -/

/-- `(V, S)` and `(V̂, Ŝ)` are topologically conjugate (§5.1.1.2): conjugate under a
homeomorphism. -/
def IsTopConjugate {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] (F : V ≃ₜ W)
    (S : V → V) (Sh : W → W) : Prop := Semiconj F S Sh

theorem IsTopConjugate.symm {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] {F : V ≃ₜ W}
    {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) : IsTopConjugate F.symm Sh S :=
  IsConjugate.symm (F := F.toEquiv) h

/-- One direction of Proposition 5.1.2. -/
theorem IsTopConjugate.globallyStable {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    {F : V ≃ₜ W} {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) (hS : GloballyStable S) :
    GloballyStable Sh := by
  obtain ⟨u, hu, huniq, hlim⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  refine ⟨F u, (hc.fixed_iff u).1 hu, fun w hw => ?_, fun w => ?_⟩
  · have := huniq _ ((hc.fixed_iff_symm w).1 hw)
    rw [← this]
    exact (F.apply_symm_apply w).symm
  · have h1 := (F.continuous.tendsto u).comp (hlim (F.symm w))
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [(Semiconj.iterate_right h k) (F.symm w), F.apply_symm_apply]

/-- **Proposition 5.1.2** (p. 150): if `(V, S)` and `(V̂, Ŝ)` are topologically conjugate, `S` is
globally stable iff `Ŝ` is. -/
theorem proposition_5_1_2 {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] {F : V ≃ₜ W}
    {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) : GloballyStable S ↔ GloballyStable Sh :=
  ⟨h.globallyStable, h.symm.globallyStable⟩

/-- `x ↦ E⁻¹x` as a homeomorphism of `ℝᵐ`. -/
def coordHomeo {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) :
    (m → ℝ) ≃ₜ (m → ℝ) where
  toEquiv := coordChange E
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := by
    change Continuous fun y => (↑E : Matrix m m ℝ) *ᵥ y
    exact Continuous.matrix_mulVec continuous_const continuous_id

theorem iterate_diagonal_mulVec {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) (k : ℕ)
    (x : m → ℝ) :
    (Matrix.diagonal d *ᵥ ·)^[k] x = fun i => d i ^ k * x i := by
  induction k with
  | zero => funext i; simp
  | succ k ih =>
    rw [iterate_succ_apply', ih]
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
    ring

/-- The diagonal system is globally stable iff every diagonal entry has modulus below one. -/
theorem globallyStable_diagonal_iff {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) :
    GloballyStable (Matrix.diagonal d *ᵥ ·) ↔ ∀ i, |d i| < 1 := by
  constructor
  · rintro ⟨u, hu, -, hlim⟩ i
    -- the fixed point is `0`, and `Dᵏ e_i → 0` forces `|d i| < 1`
    have hu0 : u = 0 := tendsto_nhds_unique (hlim 0)
      (tendsto_const_nhds.congr fun k => (iterate_fixed (Matrix.mulVec_zero _) k).symm)
    have h := tendsto_pi_nhds.1 (hlim (Pi.single i 1)) i
    rw [hu0] at h
    simp only [iterate_diagonal_mulVec, Pi.single_eq_same, mul_one, Pi.zero_apply] at h
    exact tendsto_pow_atTop_nhds_zero_iff.1 h
  · intro hd
    have hlim : ∀ v : m → ℝ, Tendsto (fun k : ℕ => (Matrix.diagonal d *ᵥ ·)^[k] v) atTop (𝓝 0) :=
      fun v => by
        simp only [iterate_diagonal_mulVec]
        refine tendsto_pi_nhds.2 fun i => ?_
        simpa using (tendsto_pow_atTop_nhds_zero_iff.2 (hd i)).mul_const (v i)
    refine ⟨0, Matrix.mulVec_zero _, fun v hv => ?_, hlim⟩
    have hv' : ∀ k : ℕ, (Matrix.diagonal d *ᵥ ·)^[k] v = v := fun k => hv.iterate k
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k => (hv' k).symm) (hlim v)

/-- **Example 5.1.3** (p. 150): if `A = EDE⁻¹` with `D = diag(d)`, then `A` is globally stable on
`ℝᵐ` iff every eigenvalue `dᵢ` of `A` has modulus below one; in particular `Aᵏv → 0` for all `v`
iff `|dᵢ| < 1` for all `i`. -/
theorem example_5_1_3 {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) (d : m → ℝ)
    {A : Matrix m m ℝ}
    (hA : A = (↑E : Matrix m m ℝ) * Matrix.diagonal d * (↑E⁻¹ : Matrix m m ℝ)) :
    (GloballyStable (A *ᵥ ·) ↔ ∀ i, |d i| < 1) ∧
      ((∀ v : m → ℝ, Tendsto (fun k : ℕ => (A *ᵥ ·)^[k] v) atTop (𝓝 0)) ↔ ∀ i, |d i| < 1) := by
  have hc : IsTopConjugate (coordHomeo E) (A *ᵥ ·) (Matrix.diagonal d *ᵥ ·) :=
    example_5_1_2 E d hA
  have h1 := (proposition_5_1_2 hc).trans (globallyStable_diagonal_iff d)
  refine ⟨h1, ⟨fun h => h1.1 ⟨0, Matrix.mulVec_zero _, fun v hv => ?_, h⟩, fun h => ?_⟩⟩
  · exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k => (hv.iterate k).symm) (h v)
  · obtain ⟨u, hu, -, hlim⟩ := h1.2 h
    have hu0 : u = 0 := tendsto_nhds_unique (hlim 0)
      (tendsto_const_nhds.congr fun k => (iterate_fixed (Matrix.mulVec_zero A) k).symm)
    exact fun v => hu0 ▸ hlim v

/-! ### Order conjugacy -/

/-- `(V, S)` and `(V̂, Ŝ)` are order conjugate under `F` (§5.1.1.3): conjugate under an order
isomorphism `F`. -/
def IsOrderConjugate {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W) (S : V → V)
    (Sh : W → W) : Prop := Semiconj F S Sh

/-- **Exercise A.1.15**: order isomorphisms preserve `↑`. -/
theorem orderIso_increasesTo {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W)
    {f : ℕ → V} {v : V} (h : IncreasesTo f v) : IncreasesTo (F ∘ f) (F v) :=
  ⟨F.monotone.comp h.1, by
    rw [Set.range_comp]; exact (F.isLUB_image' (s := range f)).2 h.2⟩

/-- **Exercise A.1.15**: order isomorphisms preserve `↓`. -/
theorem orderIso_decreasesTo {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W)
    {f : ℕ → V} {v : V} (h : DecreasesTo f v) : DecreasesTo (F ∘ f) (F v) :=
  ⟨F.monotone.comp_antitone h.1, by
    rw [Set.range_comp]; exact (F.isGLB_image' (s := range f)).2 h.2⟩

namespace IsOrderConjugate

variable {V W U : Type*} [PartialOrder V] [PartialOrder W] [PartialOrder U]

/-- **Exercise 5.1.2** (p. 151), reflexivity. -/
theorem refl (S : V → V) : IsOrderConjugate (OrderIso.refl V) S S := fun _ => rfl

/-- **Exercise 5.1.2**, symmetry. -/
theorem symm {F : V ≃o W} {S : V → V} {Sh : W → W} (h : IsOrderConjugate F S Sh) :
    IsOrderConjugate F.symm Sh S :=
  IsConjugate.symm (F := F.toEquiv) h

/-- **Exercise 5.1.2**, transitivity. -/
theorem trans {F : V ≃o W} {G : W ≃o U} {S : V → V} {Sh : W → W} {Sk : U → U}
    (h : IsOrderConjugate F S Sh) (h' : IsOrderConjugate G Sh Sk) :
    IsOrderConjugate (F.trans G) S Sk := fun v => by
  change G (F (S v)) = Sk (G (F v))
  rw [h v, h' (F v)]

variable {F : V ≃o W} {S : V → V} {Sh : W → W}

theorem orderStable (h : IsOrderConjugate F S Sh) (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  refine orderStable_of_up_down ((hc.fixed_iff u).1 hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : F.symm w ≤ S (F.symm w) := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    simpa using F.monotone (hup _ h1)
  · have h1 : S (F.symm w) ≤ F.symm w := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    simpa using F.monotone (hdown _ h1)

theorem stronglyOrderStable (h : IsOrderConjugate F S Sh) (hS : StronglyOrderStable S) :
    StronglyOrderStable Sh := by
  obtain ⟨u, hu, huniq, hup, hdown⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  have hit : ∀ w : W, (fun n => Sh^[n] w) = F ∘ fun n => S^[n] (F.symm w) := fun w => by
    funext n
    simp only [Function.comp_apply]
    rw [(Semiconj.iterate_right h n) (F.symm w), F.apply_symm_apply]
  refine ⟨F u, (hc.fixed_iff u).1 hu, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [← huniq _ ((hc.fixed_iff_symm w).1 hw)]
    exact (F.apply_symm_apply w).symm
  · have h1 : F.symm w ≤ S (F.symm w) := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    rw [hit]
    exact orderIso_increasesTo F (hup _ h1)
  · have h1 : S (F.symm w) ≤ F.symm w := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    rw [hit]
    exact orderIso_decreasesTo F (hdown _ h1)

/-- **Lemma 5.1.3** (p. 151) and **Exercise 5.1.3**: if `(V, S)` and `(V̂, Ŝ)` are order
conjugate, then (i) `S` is order stable iff `Ŝ` is, and (ii) `S` is strongly order stable iff
`Ŝ` is. -/
theorem lemma_5_1_3 (h : IsOrderConjugate F S Sh) :
    (OrderStable S ↔ OrderStable Sh) ∧ (StronglyOrderStable S ↔ StronglyOrderStable Sh) :=
  ⟨⟨h.orderStable, h.symm.orderStable⟩, ⟨h.stronglyOrderStable, h.symm.stronglyOrderStable⟩⟩

end IsOrderConjugate

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Strong semiconjugacy

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.1.1–5.2.1.2 (pp. 160–163).

`(V, S)` and `(V̂, Ŝ)` are strongly semiconjugate under `F, G` when `S = G ∘ F` and `Ŝ = F ∘ G`
(5.14).

* **Exercise 5.2.1**: (5.14) implies (5.15).
* **Lemma 5.2.1**: fixed points, and uniqueness of fixed points, transfer.
* **Lemma 5.2.2 (i)**: order stability transfers when `F, G` are both order preserving or both
  order reversing.
* **Lemma 5.2.2 (ii)**, **Theorem 5.2.3** and **Theorem 5.2.4**: strong order stability transfers
  when the maps also carry decreasing limits. The book's order continuity (§A.5.1.3) only covers
  increasing sequences, and with it alone all three statements fail
  (`SemiconjCounterexample`); the proofs here use limits in both directions.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- `(V, S)` and `(V̂, Ŝ)` are strongly semiconjugate under `F, G` (5.14): `S = G ∘ F` on `V` and
`Ŝ = F ∘ G` on `V̂`. -/
def IsStronglySemiconj {V W : Type*} (S : V → V) (Sh : W → W) (F : V → W) (G : W → V) : Prop :=
  (∀ v, S v = G (F v)) ∧ ∀ w, Sh w = F (G w)

/-- `S` preserves decreasing limits: `vₙ ↓ v` implies that `Svₙ` has infimum `Sv`. -/
def OrderContinuousDown {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Antitone f → IsGLB (range f) v → IsGLB (range (S ∘ f)) (S v)

/-- An order-reversing `S` turns increasing limits into decreasing ones: `vₙ ↑ v` implies that
`Svₙ` has infimum `Sv`. -/
def AntiContinuousUp {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Monotone f → IsLUB (range f) v → IsGLB (range (S ∘ f)) (S v)

/-- An order-reversing `S` turns decreasing limits into increasing ones: `vₙ ↓ v` implies that
`Svₙ` has supremum `Sv` (the hypothesis of Theorem 5.2.4). -/
def AntiContinuousDown {V W : Type*} [PartialOrder V] [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Antitone f → IsGLB (range f) v → IsLUB (range (S ∘ f)) (S v)

namespace IsStronglySemiconj

variable {V W : Type*} {S : V → V} {Sh : W → W} {F : V → W} {G : W → V}

/-- The roles of the two systems can be swapped. -/
theorem swap (h : IsStronglySemiconj S Sh F G) : IsStronglySemiconj Sh S G F := ⟨h.2, h.1⟩

/-- **Exercise 5.2.1** (p. 161): (5.14) implies (5.15), `F ∘ S = Ŝ ∘ F` and `G ∘ Ŝ = S ∘ G`. -/
theorem exercise_5_2_1 (h : IsStronglySemiconj S Sh F G) : Semiconj F S Sh ∧ Semiconj G Sh S :=
  ⟨fun v => by rw [h.1, h.2], fun w => by rw [h.1, h.2]⟩

/-- `Ŝⁿ⁺¹ = F ∘ Sⁿ ∘ G`. -/
theorem iterate_succ (h : IsStronglySemiconj S Sh F G) (n : ℕ) (w : W) :
    Sh^[n + 1] w = F (S^[n] (G w)) := by
  rw [iterate_succ_apply, h.2, ← (Semiconj.iterate_right h.exercise_5_2_1.1 n) (G w)]

/-- **Lemma 5.2.1 (i)** (p. 161): `F` maps fixed points of `S` to fixed points of `Ŝ`. -/
theorem fixed_F (h : IsStronglySemiconj S Sh F G) {v : V} (hv : S v = v) : Sh (F v) = F v := by
  rw [← h.exercise_5_2_1.1 v, hv]

/-- **Lemma 5.2.1 (ii)**: `G` maps fixed points of `Ŝ` to fixed points of `S`. -/
theorem fixed_G (h : IsStronglySemiconj S Sh F G) {w : W} (hw : Sh w = w) : S (G w) = G w :=
  h.swap.fixed_F hw

/-- Unique fixed points transfer under `F`. -/
theorem isUniqueFixed (h : IsStronglySemiconj S Sh F G) {v : V} (hv : IsUniqueFixed S v) :
    IsUniqueFixed Sh (F v) := by
  refine ⟨h.fixed_F hv.1, fun w hw => ?_⟩
  have hGw : G w = v := hv.2 _ (h.fixed_G hw)
  rw [← hw, h.2, hGw]

/-- **Lemma 5.2.1 (iii)**: `S` has a unique fixed point iff `Ŝ` does. -/
theorem existsUnique_iff (h : IsStronglySemiconj S Sh F G) :
    (∃! v, S v = v) ↔ ∃! w, Sh w = w :=
  ⟨fun ⟨v, hv, hu⟩ => ⟨F v, (h.isUniqueFixed ⟨hv, hu⟩).1, (h.isUniqueFixed ⟨hv, hu⟩).2⟩,
    fun ⟨w, hw, hu⟩ => ⟨G w, (h.swap.isUniqueFixed ⟨hw, hu⟩).1, (h.swap.isUniqueFixed ⟨hw, hu⟩).2⟩⟩

variable [PartialOrder V] [PartialOrder W]

/-- One direction of Lemma 5.2.2 (i), with `F` and `G` order preserving. -/
theorem orderStable_mono (h : IsStronglySemiconj S Sh F G) (hF : Monotone F) (hG : Monotone G)
    (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  refine orderStable_of_up_down (h.fixed_F hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : G w ≤ S (G w) := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : Sh w ≤ F u := by rw [h.2]; exact hF (hup _ h1)
    exact hw.trans h2
  · have h1 : S (G w) ≤ G w := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : F u ≤ Sh w := by rw [h.2]; exact hF (hdown _ h1)
    exact h2.trans hw

/-- One direction of Lemma 5.2.2 (i), with `F` and `G` order reversing. -/
theorem orderStable_anti (h : IsStronglySemiconj S Sh F G) (hF : Antitone F) (hG : Antitone G)
    (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  refine orderStable_of_up_down (h.fixed_F hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : S (G w) ≤ G w := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : Sh w ≤ F u := by rw [h.2]; exact hF (hdown _ h1)
    exact hw.trans h2
  · have h1 : G w ≤ S (G w) := by rw [← h.exercise_5_2_1.2 w]; exact hG hw
    have h2 : F u ≤ Sh w := by rw [h.2]; exact hF (hup _ h1)
    exact h2.trans hw

/-- **Lemma 5.2.2 (i)** (p. 162): if `F, G` are both order preserving or both order reversing,
`S` is order stable on `V` iff `Ŝ` is order stable on `V̂`. -/
theorem lemma_5_2_2_i (h : IsStronglySemiconj S Sh F G)
    (hFG : (Monotone F ∧ Monotone G) ∨ (Antitone F ∧ Antitone G)) :
    OrderStable S ↔ OrderStable Sh := by
  rcases hFG with ⟨hF, hG⟩ | ⟨hF, hG⟩
  · exact ⟨h.orderStable_mono hF hG, h.swap.orderStable_mono hG hF⟩
  · exact ⟨h.orderStable_anti hF hG, h.swap.orderStable_anti hG hF⟩

/-- Increasing limits of an orbit can be read off the shifted orbit. -/
theorem increasesTo_of_succ {f : ℕ → V} (hf : Monotone f) {v : V}
    (h : IsLUB (range fun n => f (n + 1)) v) : IncreasesTo f v :=
  ⟨hf, (isLUB_range_succ_iff hf v).1 h⟩

/-- Decreasing limits of an orbit can be read off the shifted orbit. -/
theorem decreasesTo_of_succ {f : ℕ → V} (hf : Antitone f) {v : V}
    (h : IsGLB (range fun n => f (n + 1)) v) : DecreasesTo f v := by
  refine ⟨hf, ?_⟩
  have key : lowerBounds (range fun n => f (n + 1)) = lowerBounds (range f) := by
    ext w
    simp only [mem_lowerBounds, Set.forall_mem_range]
    exact ⟨fun h n => (h n).trans (hf (Nat.le_succ n)), fun h n => h (n + 1)⟩
  rw [IsGLB, ← key]
  exact h

/-- Strong order stability passes from `Ŝ` to `S` when `F, G` are order preserving and `G`
carries increasing and decreasing limits. -/
theorem stronglyOrderStable_mono (h : IsStronglySemiconj S Sh F G) (hF : Monotone F)
    (hG : Monotone G) (hGu : OrderContinuous G) (hGd : OrderContinuousDown G)
    (hSh : StronglyOrderStable Sh) : StronglyOrderStable S := by
  obtain ⟨w₀, hw₀, huniq, hup, hdown⟩ := hSh
  have hfix := h.swap.isUniqueFixed ⟨hw₀, huniq⟩
  refine ⟨G w₀, hfix.1, hfix.2, fun v hv => ?_, fun v hv => ?_⟩
  · have hFv : F v ≤ Sh (F v) := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hup _ hFv
    have hmono : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := (show Monotone S from fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)).iterate n hv
      rwa [← iterate_succ_apply] at this
    refine increasesTo_of_succ hmono ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGu _ _ hm hl
  · have hFv : Sh (F v) ≤ F v := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hdown _ hFv
    have hanti : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := (show Monotone S from fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)).iterate n hv
      rwa [← iterate_succ_apply] at this
    refine decreasesTo_of_succ hanti ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGd _ _ hm hl

/-- Strong order stability passes from `Ŝ` to `S` when `F, G` are order reversing and `G` turns
decreasing limits into increasing ones and vice versa. -/
theorem stronglyOrderStable_anti (h : IsStronglySemiconj S Sh F G) (hF : Antitone F)
    (hG : Antitone G) (hGu : AntiContinuousUp G) (hGd : AntiContinuousDown G)
    (hSh : StronglyOrderStable Sh) : StronglyOrderStable S := by
  obtain ⟨w₀, hw₀, huniq, hup, hdown⟩ := hSh
  have hfix := h.swap.isUniqueFixed ⟨hw₀, huniq⟩
  have hSm : Monotone S := fun a b hab => by rw [h.1, h.1]; exact hG (hF hab)
  refine ⟨G w₀, hfix.1, hfix.2, fun v hv => ?_, fun v hv => ?_⟩
  · have hFv : Sh (F v) ≤ F v := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hdown _ hFv
    have hmono : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := hSm.iterate n hv
      rwa [← iterate_succ_apply] at this
    refine increasesTo_of_succ hmono ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGd _ _ hm hl
  · have hFv : F v ≤ Sh (F v) := by rw [← h.exercise_5_2_1.1 v]; exact hF hv
    obtain ⟨hm, hl⟩ := hup _ hFv
    have hanti : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := hSm.iterate n hv
      rwa [← iterate_succ_apply] at this
    refine decreasesTo_of_succ hanti ?_
    have heq : (fun n => S^[n + 1] v) = G ∘ fun n => Sh^[n] (F v) :=
      funext fun n => h.swap.iterate_succ n v
    rw [heq]
    exact hGu _ _ hm hl

/-- **Lemma 5.2.2 (ii)** (p. 162), with order continuity read in both directions: if `F, G` are
order preserving and carry increasing and decreasing limits, or are order reversing and swap
them, then `S` is strongly order stable iff `Ŝ` is. -/
theorem lemma_5_2_2_ii (h : IsStronglySemiconj S Sh F G)
    (hFG : (Monotone F ∧ Monotone G ∧ OrderContinuous F ∧ OrderContinuousDown F ∧
        OrderContinuous G ∧ OrderContinuousDown G) ∨
      (Antitone F ∧ Antitone G ∧ AntiContinuousUp F ∧ AntiContinuousDown F ∧
        AntiContinuousUp G ∧ AntiContinuousDown G)) :
    StronglyOrderStable S ↔ StronglyOrderStable Sh := by
  rcases hFG with ⟨hF, hG, hFu, hFd, hGu, hGd⟩ | ⟨hF, hG, hFu, hFd, hGu, hGd⟩
  · exact ⟨h.swap.stronglyOrderStable_mono hG hF hFu hFd,
      h.stronglyOrderStable_mono hF hG hGu hGd⟩
  · exact ⟨h.swap.stronglyOrderStable_anti hG hF hFu hFd,
      h.stronglyOrderStable_anti hF hG hGu hGd⟩

/-- **Theorem 5.2.3** (p. 163), with `G` carrying increasing and decreasing limits: if `F, G`
are order preserving and `Ŝ` is strongly order stable with fixed point `w̄`, then `S` is strongly
order stable with fixed point `v̄ = Gw̄`, and `w ≼ Ŝw ⟹ GŜⁿw ↑ v̄` (5.16). -/
theorem theorem_5_2_3 (h : IsStronglySemiconj S Sh F G) (hF : Monotone F) (hG : Monotone G)
    (hGu : OrderContinuous G) (hGd : OrderContinuousDown G) {wbar : W}
    (hSh : StronglyOrderStable Sh) (hw : Sh wbar = wbar) :
    StronglyOrderStable S ∧ S (G wbar) = G wbar ∧
      ∀ w, w ≤ Sh w → IncreasesTo (fun n => G (Sh^[n] w)) (G wbar) := by
  refine ⟨h.stronglyOrderStable_mono hF hG hGu hGd hSh, h.fixed_G hw, fun w hle => ?_⟩
  obtain ⟨u, -, huniq, hup, -⟩ := hSh
  obtain ⟨hm, hl⟩ := hup w hle
  rw [huniq wbar hw]
  exact ⟨hG.comp hm, hGu _ _ hm hl⟩

/-- **Theorem 5.2.4** (p. 163), with `G` also turning increasing limits into decreasing ones: if
`F, G` are order reversing and `Ŝ` is strongly order stable with fixed point `w̄`, then `S` is
strongly order stable with fixed point `v̄ = Gw̄`, and `Ŝw ≼ w ⟹ GŜⁿw ↑ v̄` (5.17). -/
theorem theorem_5_2_4 (h : IsStronglySemiconj S Sh F G) (hF : Antitone F) (hG : Antitone G)
    (hGu : AntiContinuousUp G) (hGd : AntiContinuousDown G) {wbar : W}
    (hSh : StronglyOrderStable Sh) (hw : Sh wbar = wbar) :
    StronglyOrderStable S ∧ S (G wbar) = G wbar ∧
      ∀ w, Sh w ≤ w → IncreasesTo (fun n => G (Sh^[n] w)) (G wbar) := by
  refine ⟨h.stronglyOrderStable_anti hF hG hGu hGd hSh, h.fixed_G hw, fun w hle => ?_⟩
  obtain ⟨u, -, huniq, -, hdown⟩ := hSh
  obtain ⟨hm, hl⟩ := hdown w hle
  rw [huniq wbar hw]
  exact ⟨hG.comp hm, hGd _ _ hm hl⟩

end IsStronglySemiconj

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Factored dynamic programs

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.2.2–5.2.3 (pp. 166–174).

A factored dynamic program `(V, F, V̂, 𝔾)` has maps `F : V → V̂` and `G_σ : V̂ → V` such that
`{G_σ v̂}_σ` has a greatest element `Gv̂` (5.19) for every `v̂`. It generates the primary ADP
`T_σ = G_σ ∘ F` and the subordinate ADP `T̂_σ = F ∘ G_σ`.

* Order-preserving FDPs: **Lemma 5.2.9**, **Lemma 5.2.10**, **Lemma 5.2.11**, **Lemma 5.2.12**,
  **Theorem 5.2.13** (the fundamental optimality properties hold for the primary ADP iff they
  hold for the subordinate one; (5.23); optimal policies) and **Proposition 5.2.14** (the
  converse under strict monotonicity of `F`).
* Order-reversing FDPs: **Lemma 5.2.15**, **Lemma 5.2.16**, **Lemma 5.2.17**,
  **Exercise 5.2.2** and **Theorem 5.2.18**. An order-reversing FDP becomes order preserving once
  `V̂` is replaced by `V̂^∂`, and its subordinate ADP becomes the dual of the original one; this
  reduces the order-reversing case to the order-preserving one.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- A factored dynamic program `(V, F, V̂, 𝔾)` (§5.2.2.1). -/
structure FDP (V W P : Type*) [PartialOrder V] [PartialOrder W] where
  /-- the map `F : V → V̂` -/
  F : V → W
  /-- the maps `G_σ : V̂ → V` -/
  G : P → W → V
  /-- (iv): `{G_σ v̂}_σ` has a greatest element -/
  greatest : ∀ w, ∃ σ, ∀ τ, G τ w ≤ G σ w
  nonempty : Nonempty P

namespace FDP

variable {V W P : Type*} [PartialOrder V] [PartialOrder W] (M : FDP V W P)

/-- An order-preserving FDP: `F` and every `G_σ` are order preserving. -/
def IsOrderPreserving : Prop := Monotone M.F ∧ ∀ σ, Monotone (M.G σ)

/-- An order-reversing FDP (§5.2.3): `F` and every `G_σ` are order reversing. -/
def IsOrderReversing : Prop := Antitone M.F ∧ ∀ σ, Antitone (M.G σ)

/-- Either case: then every `G_σ ∘ F` and `F ∘ G_σ` is order preserving. -/
def Monotonic : Prop := M.IsOrderPreserving ∨ M.IsOrderReversing

/-- A policy attaining the greatest element of `{G_σ v̂}_σ`. -/
noncomputable def gsel (w : W) : P := (M.greatest w).choose

/-- `Gv̂ = ⋁_σ G_σ v̂` (5.19). -/
noncomputable def Gsup (w : W) : V := M.G (M.gsel w) w

theorem G_le_Gsup (σ : P) (w : W) : M.G σ w ≤ M.Gsup w := (M.greatest w).choose_spec σ

theorem isGreatest_Gsup (w : W) : IsGreatest (range fun σ => M.G σ w) (M.Gsup w) :=
  ⟨⟨_, rfl⟩, by rintro _ ⟨σ, rfl⟩; exact M.G_le_Gsup σ w⟩

/-- The primary ADP `(V, 𝕋)`, `T_σ = G_σ ∘ F`. -/
def primary (h : M.Monotonic) : ADP V P where
  T σ v := M.G σ (M.F v)
  mono σ := by
    rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact (hG σ).comp hF
    · exact (hG σ).comp hF
  nonempty := M.nonempty

/-- The subordinate ADP `(V̂, 𝕋̂)`, `T̂_σ = F ∘ G_σ`. -/
def sub (h : M.Monotonic) : ADP W P where
  T σ w := M.F (M.G σ w)
  mono σ := by
    rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact hF.comp (hG σ)
    · exact hF.comp (hG σ)
  nonempty := M.nonempty

variable {M}

theorem primary_regular (h : M.Monotonic) : (M.primary h).Regular := fun v =>
  ⟨M.gsel (M.F v), fun τ => M.G_le_Gsup τ (M.F v)⟩

theorem primary_bellman (h : M.Monotonic) (v : V) : (M.primary h).bellman v = M.Gsup (M.F v) := by
  have hg := (M.primary h).isGreedy_greedy (primary_regular h v)
  exact le_antisymm (M.G_le_Gsup _ _) (hg (M.gsel (M.F v)))

/-- **Lemma 5.2.9** (p. 167) and **Lemma 5.2.15** (p. 171): (i) the Bellman operator of the
primary ADP is `T = G ∘ F`, and (ii) `σ` is `v`-greedy iff `G_σ F v = G F v`. -/
theorem lemma_5_2_9 (h : M.Monotonic) :
    (∀ v, (M.primary h).bellman v = M.Gsup (M.F v)) ∧
      ∀ v σ, (M.primary h).IsGreedy v σ ↔ M.G σ (M.F v) = M.Gsup (M.F v) := by
  refine ⟨primary_bellman h, fun v σ => ⟨fun hg => ?_, fun he τ => ?_⟩⟩
  · exact le_antisymm (M.G_le_Gsup σ _) (hg (M.gsel (M.F v)))
  · change M.G τ (M.F v) ≤ M.G σ (M.F v)
    rw [he]
    exact M.G_le_Gsup τ _

/-- With order preserving `F`, `gsel v̂` is `v̂`-greedy for the subordinate ADP. -/
theorem sub_isGreedy_of_eq (h : M.Monotonic) (hF : Monotone M.F) {w : W} {σ : P}
    (he : M.G σ w = M.Gsup w) : (M.sub h).IsGreedy w σ := fun τ => by
  change M.F (M.G τ w) ≤ M.F (M.G σ w)
  rw [he]
  exact hF (M.G_le_Gsup τ w)

theorem sub_regular (h : M.Monotonic) (hF : Monotone M.F) : (M.sub h).Regular := fun w =>
  ⟨M.gsel w, sub_isGreedy_of_eq h hF rfl⟩

theorem sub_bellman (h : M.Monotonic) (hF : Monotone M.F) (w : W) :
    (M.sub h).bellman w = M.F (M.Gsup w) :=
  (((M.sub h).isGreedy_iff (sub_regular h hF w) _).1 (sub_isGreedy_of_eq h hF rfl)).symm

/-- **Lemma 5.2.10** (p. 168): for an order-preserving FDP, (i) the Bellman operator of the
subordinate ADP is `T̂ = F ∘ G`, and (ii) `G_σ v̂ = Gv̂` implies that `σ` is `v̂`-greedy. -/
theorem lemma_5_2_10 (h : M.Monotonic) (hP : M.IsOrderPreserving) :
    (∀ w, (M.sub h).bellman w = M.F (M.Gsup w)) ∧
      ∀ w σ, M.G σ w = M.Gsup w → (M.sub h).IsGreedy w σ :=
  ⟨sub_bellman h hP.1, fun _ _ he => sub_isGreedy_of_eq h hP.1 he⟩

/-- **Lemma 5.2.11** (p. 168): `(V, T)` and `(V̂, T̂)` are strongly semiconjugate under `F, G`. -/
theorem lemma_5_2_11 (h : M.Monotonic) (hP : M.IsOrderPreserving) :
    IsStronglySemiconj (M.primary h).bellman (M.sub h).bellman M.F M.Gsup :=
  ⟨primary_bellman h, sub_bellman h hP.1⟩

/-- Each pair of policy systems is strongly semiconjugate under `F, G_σ` (5.20). -/
theorem policy_semiconj (h : M.Monotonic) (σ : P) :
    IsStronglySemiconj ((M.primary h).T σ) ((M.sub h).T σ) M.F (M.G σ) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Lemma 5.2.12** (p. 168) and **Exercise 5.2.2** (p. 172): (i) `(V̂, 𝕋̂)` is well-posed iff
`(V, 𝕋)` is, (ii) order stability transfers (for order-preserving and order-reversing FDPs
alike), and the `σ`-value functions obey `v̂_σ = Fv_σ` and `v_σ = G_σ v̂_σ` (5.22), (5.25). -/
theorem lemma_5_2_12 (h : M.Monotonic) :
    ((M.sub h).WellPosed ↔ (M.primary h).WellPosed) ∧
      ((M.sub h).IsOrderStable ↔ (M.primary h).IsOrderStable) ∧
      ∀ (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) σ,
        M.F ((M.primary h).vσ hw σ) = (M.sub h).vσ hw' σ ∧
          M.G σ ((M.sub h).vσ hw' σ) = (M.primary h).vσ hw σ := by
  refine ⟨forall_congr' fun σ => (policy_semiconj h σ).existsUnique_iff.symm,
    forall_congr' fun σ => ((policy_semiconj h σ).lemma_5_2_2_i ?_).symm,
    fun hw hw' σ => ⟨?_, ?_⟩⟩
  · rcases h with ⟨hF, hG⟩ | ⟨hF, hG⟩
    · exact Or.inl ⟨hF, hG σ⟩
    · exact Or.inr ⟨hF, hG σ⟩
  · exact ADP.eq_vσ hw' ((policy_semiconj h σ).fixed_F (ADP.T_vσ hw σ))
  · exact ADP.eq_vσ hw ((policy_semiconj h σ).fixed_G (ADP.T_vσ hw' σ))

/-! ### Optimality for order-preserving FDPs -/

/-- If `v*` is the primary value function and attained, `Fv*` is the subordinate one. -/
theorem sub_isValueFunction (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) {v : V}
    (hv : (M.primary h).IsValueFunction v) {σ₀ : P} (hσ₀ : (M.primary h).IsOptimal hw σ₀) :
    (M.sub h).IsValueFunction (M.F v) := by
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  have hv₀ : (M.primary h).vσ hw σ₀ = v := (ADP.isOptimal_iff hv).1 hσ₀
  refine ⟨?_, fun b hb => ?_⟩
  · rw [ADP.VSig_eq_range hw']
    rintro _ ⟨σ, rfl⟩
    rw [← (h522 σ).1]
    exact hP.1 (hv.1 ⟨σ, ADP.T_vσ hw σ⟩)
  · rw [← hv₀, (h522 σ₀).1]
    exact hb ⟨σ₀, ADP.T_vσ hw' σ₀⟩

/-- If `v̂*` is the subordinate value function and Bellman's principle holds there, `Gv̂*` is the
primary value function, attained by any `σ` with `G_σ v̂* = Gv̂*`. -/
theorem primary_isValueFunction (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) {w : W}
    (hv : (M.sub h).IsValueFunction w) (hbp : (M.sub h).BellmanPrinciple hw') {σ : P}
    (hσ : M.G σ w = M.Gsup w) :
    (M.primary h).IsValueFunction (M.Gsup w) ∧ (M.primary h).vσ hw σ = M.Gsup w := by
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  have hopt : (M.sub h).IsOptimal hw' σ := (hbp σ).2 ⟨w, hv, sub_isGreedy_of_eq h hP.1 hσ⟩
  have hvσ : (M.primary h).vσ hw σ = M.Gsup w := by
    rw [← (h522 σ).2, (ADP.isOptimal_iff hv).1 hopt, hσ]
  refine ⟨IsGreatest.isLUB ⟨⟨σ, hvσ ▸ ADP.T_vσ hw σ⟩, ?_⟩, hvσ⟩
  rw [ADP.VSig_eq_range hw]
  rintro _ ⟨τ, rfl⟩
  rw [← (h522 τ).2]
  exact ((hP.2 τ) (hv.1 ⟨τ, ADP.T_vσ hw' τ⟩)).trans (M.G_le_Gsup τ w)

theorem fo_sub_of_primary (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.primary h).FundamentalOptimality hw) : (M.sub h).FundamentalOptimality hw' := by
  obtain ⟨⟨σ₀, hσ₀⟩, ⟨v, hv, -, hb, huniq⟩, -⟩ := hfo
  have hbv : (M.primary h).bellman v = v :=
    ((M.primary h).solvesBellman_iff (primary_regular h v)).1 hb
  refine (ADP.fundamentalOptimality_iff hw').2 ⟨M.F v, sub_isValueFunction h hP hw hw' hv hσ₀,
    sub_regular h hP.1 _, ?_, fun w' hw'G hw'b => ?_⟩
  · rw [ADP.solvesBellman_iff _ (sub_regular h hP.1 _), sub_bellman h hP.1,
      ← primary_bellman h, hbv]
  · have h1 : (M.sub h).bellman w' = w' := ((M.sub h).solvesBellman_iff hw'G).1 hw'b
    have h2 : (M.primary h).bellman (M.Gsup w') = M.Gsup w' := by
      rw [primary_bellman h, ← sub_bellman h hP.1, h1]
    have h3 : M.Gsup w' = v := huniq _ (primary_regular h _)
      (((M.primary h).solvesBellman_iff (primary_regular h _)).2 h2)
    rw [← h1, sub_bellman h hP.1, h3]

theorem fo_primary_of_sub (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.sub h).FundamentalOptimality hw') : (M.primary h).FundamentalOptimality hw := by
  obtain ⟨-, ⟨w, hv, -, hb, huniq⟩, hbp⟩ := hfo
  have hbw : (M.sub h).bellman w = w :=
    ((M.sub h).solvesBellman_iff (sub_regular h hP.1 w)).1 hb
  refine (ADP.fundamentalOptimality_iff hw).2 ⟨M.Gsup w,
    (primary_isValueFunction h hP hw hw' hv hbp (σ := M.gsel w) rfl).1, primary_regular h _, ?_,
    fun v' hv'G hv'b => ?_⟩
  · rw [ADP.solvesBellman_iff _ (primary_regular h _), primary_bellman h, ← sub_bellman h hP.1,
      hbw]
  · have h1 : (M.primary h).bellman v' = v' := ((M.primary h).solvesBellman_iff hv'G).1 hv'b
    have h2 : (M.sub h).bellman (M.F v') = M.F v' := by
      rw [sub_bellman h hP.1, ← primary_bellman h, h1]
    have h3 : M.F v' = w := huniq _ (sub_regular h hP.1 _)
      (((M.sub h).solvesBellman_iff (sub_regular h hP.1 _)).2 h2)
    rw [← h1, primary_bellman h, h3]

/-- **Theorem 5.2.13** (p. 169): for an order-preserving FDP, (a) the fundamental optimality
properties hold for the primary ADP iff (b) they hold for the subordinate ADP. In that case,
(i) `v* = Gv̂*` and `v̂* = Fv*` (5.23), (ii) `G_σ v̂* = Gv̂*` implies that `σ` is optimal for the
primary ADP, and (iii) optimal policies for the primary ADP are optimal for the subordinate
one. -/
theorem theorem_5_2_13 (h : M.Monotonic) (hP : M.IsOrderPreserving)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) :
    ((M.primary h).FundamentalOptimality hw ↔ (M.sub h).FundamentalOptimality hw') ∧
      ((M.primary h).FundamentalOptimality hw →
        (∀ v w, (M.primary h).IsValueFunction v → (M.sub h).IsValueFunction w →
          v = M.Gsup w ∧ w = M.F v) ∧
        (∀ w σ, (M.sub h).IsValueFunction w → M.G σ w = M.Gsup w →
          (M.primary h).IsOptimal hw σ) ∧
        ∀ σ, (M.primary h).IsOptimal hw σ → (M.sub h).IsOptimal hw' σ) := by
  refine ⟨⟨fo_sub_of_primary h hP hw hw', fo_primary_of_sub h hP hw hw'⟩, fun hfo => ?_⟩
  have hfo' := fo_sub_of_primary h hP hw hw' hfo
  have hbp := hfo'.2.2
  obtain ⟨σ₀, hσ₀⟩ := hfo.1
  have h522 := (lemma_5_2_12 h).2.2 hw hw'
  refine ⟨fun v w hv hw₀ => ⟨?_, ?_⟩, fun w σ hw₀ hσ => ?_, fun σ hσ => ?_⟩
  · exact hv.unique (primary_isValueFunction h hP hw hw' hw₀ hbp (σ := M.gsel w) rfl).1
  · exact hw₀.unique (sub_isValueFunction h hP hw hw' hv hσ₀)
  · obtain ⟨hv, hvσ⟩ := primary_isValueFunction h hP hw hw' hw₀ hbp hσ
    exact (ADP.isOptimal_iff hv).2 hvσ
  · have hv := hσ.isValueFunction
    rw [ADP.isOptimal_iff (sub_isValueFunction h hP hw hw' hv hσ)]
    exact ((h522 σ).1).symm

/-- **Proposition 5.2.14** (p. 171): if the fundamental optimality properties hold for the
subordinate ADP and `F` is strictly order preserving, then (i) they hold for the primary ADP and
(ii) every policy optimal for the subordinate ADP is optimal for the primary ADP. -/
theorem proposition_5_2_14 (h : M.Monotonic) (hP : M.IsOrderPreserving) (hstrict : StrictMono M.F)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed)
    (hfo : (M.sub h).FundamentalOptimality hw') :
    (M.primary h).FundamentalOptimality hw ∧
      ∀ σ, (M.sub h).IsOptimal hw' σ → (M.primary h).IsOptimal hw σ := by
  have hfoP := fo_primary_of_sub h hP hw hw' hfo
  refine ⟨hfoP, fun σ hσ => ?_⟩
  obtain ⟨w, hv, hg⟩ := (hfo.2.2 σ).1 hσ
  have hwG : w ∈ (M.sub h).VG := ⟨σ, hg⟩
  have heq : M.F (M.G σ w) = M.F (M.Gsup w) := by
    rw [← sub_bellman h hP.1]
    exact ((M.sub h).isGreedy_iff hwG σ).1 hg
  have hGσ : M.G σ w = M.Gsup w := by
    by_contra hne
    exact (hstrict (lt_of_le_of_ne (M.G_le_Gsup σ w) hne)).ne heq
  exact ((theorem_5_2_13 h hP hw hw').2 hfoP).2.1 w σ hv hGσ

/-! ### Order-reversing FDPs -/

variable (M) in
/-- An FDP read with `V̂^∂` in place of `V̂`. -/
def dualize : FDP V Wᵒᵈ P where
  F := OrderDual.toDual ∘ M.F
  G σ w := M.G σ (OrderDual.ofDual w)
  greatest w := M.greatest (OrderDual.ofDual w)
  nonempty := M.nonempty

theorem dualize_isOrderPreserving (hR : M.IsOrderReversing) : M.dualize.IsOrderPreserving :=
  ⟨fun _ _ h => hR.1 h, fun σ _ _ h => hR.2 σ h⟩

theorem dualize_monotonic (hR : M.IsOrderReversing) : M.dualize.Monotonic :=
  Or.inl (dualize_isOrderPreserving hR)

/-- Dualizing `V̂` leaves the primary ADP unchanged … -/
theorem dualize_primary (h : M.Monotonic) (hR : M.IsOrderReversing) :
    M.dualize.primary (dualize_monotonic hR) = M.primary h := rfl

/-- … and turns the subordinate ADP into its dual. -/
theorem dualize_sub (h : M.Monotonic) (hR : M.IsOrderReversing) :
    M.dualize.sub (dualize_monotonic hR) = (M.sub h).dual := rfl

theorem dualize_Gsup (w : W) : M.dualize.Gsup (OrderDual.toDual w) = M.Gsup w := rfl

/-- **Lemma 5.2.16** (p. 172): for an order-reversing FDP, (i) the Bellman min-operator of the
subordinate ADP is `T̂▿ = F ∘ G`, with min-greedy policies everywhere, and (ii) `G_σ v̂ = Gv̂`
implies that `σ` is `v̂`-min-greedy. -/
theorem lemma_5_2_16 (h : M.Monotonic) (hR : M.IsOrderReversing) :
    (M.sub h).MinRegular ∧ (∀ w, (M.sub h).IsMinBellmanValue w (M.F (M.Gsup w))) ∧
      ∀ w σ, M.G σ w = M.Gsup w → (M.sub h).IsMinGreedy w σ := by
  have hP := dualize_isOrderPreserving hR
  have hd := dualize_monotonic hR
  refine ⟨((M.sub h).minRegular_iff).2 (sub_regular hd hP.1), fun w => ?_,
    fun w σ he => sub_isGreedy_of_eq hd hP.1 (w := OrderDual.toDual w) he⟩
  have hreg := sub_regular hd hP.1
  have h1 := (M.dualize.sub hd).isBellmanValue_bellman (hreg (OrderDual.toDual w))
  rw [sub_bellman hd hP.1] at h1
  exact h1

/-- **Lemma 5.2.17** (p. 172): for an order-reversing FDP, `(V, T)` and `(V̂, T̂▿)` are strongly
semiconjugate under `F, G`, where `T̂▿ = F ∘ G` is the Bellman min-operator (Lemma 5.2.16). -/
theorem lemma_5_2_17 (h : M.Monotonic) :
    IsStronglySemiconj (M.primary h).bellman (fun w => M.F (M.Gsup w)) M.F M.Gsup :=
  ⟨primary_bellman h, fun _ => rfl⟩

/-- **Theorem 5.2.18** (p. 173): for an order-reversing FDP, (a) the fundamental max-optimality
properties hold for the primary ADP iff (b) the fundamental min-optimality properties hold for the
subordinate ADP. In that case (i) `v* = Gv̂▿*` and `v̂▿* = Fv*` (5.26), (ii) `G_σ v̂▿* = Gv̂▿*`
implies that `σ` is optimal, and (iii) optimal policies are min-optimal for the subordinate ADP;
if `F` is strictly order reversing, (iv) min-optimal policies of the subordinate ADP are
optimal for the primary ADP. -/
theorem theorem_5_2_18 (h : M.Monotonic) (hR : M.IsOrderReversing)
    (hw : (M.primary h).WellPosed) (hw' : (M.sub h).WellPosed) :
    ((M.primary h).FundamentalOptimality hw ↔ (M.sub h).MinFundamentalOptimality hw') ∧
      ((M.primary h).FundamentalOptimality hw →
        (∀ v w, (M.primary h).IsValueFunction v → (M.sub h).IsMinValueFunction w →
          v = M.Gsup w ∧ w = M.F v) ∧
        (∀ w σ, (M.sub h).IsMinValueFunction w → M.G σ w = M.Gsup w →
          (M.primary h).IsOptimal hw σ) ∧
        (∀ σ, (M.primary h).IsOptimal hw σ → (M.sub h).IsMinOptimal hw' σ) ∧
        (StrictAnti M.F → ∀ σ, (M.sub h).IsMinOptimal hw' σ → (M.primary h).IsOptimal hw σ)) := by
  have hP := dualize_isOrderPreserving hR
  have hd := dualize_monotonic hR
  have hwd : (M.dualize.sub hd).WellPosed := hw'
  have key := theorem_5_2_13 hd hP hw hwd
  refine ⟨key.1.trans ((M.sub h).minFundamentalOptimality_iff hw').symm, fun hfo => ?_⟩
  obtain ⟨h1, h2, h3⟩ := key.2 hfo
  refine ⟨fun v w hv hw₀ => ?_, fun w σ hw₀ hσ => h2 (OrderDual.toDual w) σ hw₀ hσ,
    fun σ hσ => ((M.sub h).isMinOptimal_iff hw' σ).2 (h3 σ hσ), fun hstrict σ hσ => ?_⟩
  · obtain ⟨e1, e2⟩ := h1 v (OrderDual.toDual w) hv hw₀
    exact ⟨e1, congrArg OrderDual.ofDual e2⟩
  · have hfo' : (M.dualize.sub hd).FundamentalOptimality hwd := key.1.1 hfo
    exact (proposition_5_2_14 hd hP (fun _ _ hab => hstrict hab) hw hwd hfo').2 σ
      (((M.sub h).isMinOptimal_iff hw' σ).1 hσ)

end FDP

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Concavity, convexity and Du's theorem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.1.3 (pp. 131–132).

`E` is a Banach lattice and `V = [a, b]`. An order preserving self-map `S` of `[a, b]` satisfies
*Du's conditions* if either (a) `S` is concave and `Sa ≥ a + ε(b − a)` or (b) `S` is convex and
`Sb ≤ b − ε(b − a)`, for some `ε ∈ (0, 1)`.

* **Theorem 4.1.10 (Du)**: Du's conditions imply global stability on `[a, b]`. The book cites
  Du (1990); the proof here squeezes the orbits of `a` and `b` together at rate `(1 − ε)ᵏ`, and uses
  completeness and the lattice norm.
* **Lemma 4.1.9**: if `Sa − a` (or `b − Sb`) is interior to the positive cone, Du's conditions
  hold.
* **Theorem 4.1.11**: a regular ADP on `[a, b]` whose policy operators satisfy Du's conditions
  satisfies the fundamental optimality properties, with convergence of VFI, OPI and HPI, if
  (a) `E` is countably Dedekind complete, (b) `𝕋` is finite, or (c) the Bellman operator satisfies
  Du's conditions.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

namespace BanachLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] [PosSMulMono ℝ E]

/-- `F` is globally stable on `U`: a unique fixed point in `U` attracting every orbit from `U`. -/
def GloballyStableOn (F : E → E) (U : Set E) : Prop :=
  ∃ u ∈ U, F u = u ∧ (∀ w ∈ U, F w = w → w = u) ∧
    ∀ v ∈ U, Tendsto (fun k => F^[k] v) atTop (𝓝 u)

/-- Du's conditions (p. 131) for a self-map `F` of `[a, b]`. -/
def DuConditions (a b : E) (F : E → E) : Prop :=
  (ConcaveOn ℝ (Icc a b) F ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a + ε • (b - a) ≤ F a) ∨
    (ConvexOn ℝ (Icc a b) F ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ F b ≤ b - ε • (b - a))

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] in
/-- Points of `[l, h]` are at most `h − l` apart. -/
theorem abs_sub_le_of_mem_Icc {l h x y : E} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    |x - y| ≤ h - l := by
  rw [abs]
  refine sup_le (sub_le_sub hx.2 hy.1) ?_
  rw [neg_sub]
  exact sub_le_sub hy.2 hx.1

omit [NormedSpace ℝ E] [PosSMulMono ℝ E] in
theorem norm_sub_le_of_mem_Icc {l h x y : E} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    ‖x - y‖ ≤ ‖h - l‖ :=
  norm_le_norm_of_abs_le_abs ((abs_sub_le_of_mem_Icc hx hy).trans_eq
    (abs_of_nonneg (sub_nonneg.2 (hx.1.trans hx.2))).symm)

omit [NormedAddCommGroup E] [IsOrderedAddMonoid E] [HasSolidNorm E] [NormedSpace ℝ E]
  [PosSMulMono ℝ E] in
theorem iterate_mem_Icc {a b : E} {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) {v : E} (hv : v ∈ Icc a b) (k : ℕ) :
    F^[k] v ∈ Icc (F^[k] a) (F^[k] b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hv.1.trans hv.2⟩
  have hb : b ∈ Icc a b := ⟨hv.1.trans hv.2, le_rfl⟩
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
    exact ⟨hmono (hmaps.iterate k ha) (hmaps.iterate k hv) ih.1,
      hmono (hmaps.iterate k hv) (hmaps.iterate k hb) ih.2⟩

variable [CompleteSpace E]

/-- **Theorem 4.1.10 (Du)** (p. 131), concave case: an order preserving concave self-map of
`[a, b]` with `Sa ≥ a + ε(b − a)` for some `ε ∈ (0, 1]` is globally stable on `[a, b]`. -/
theorem du_concave {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hconc : ConcaveOn ℝ (Icc a b) F) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hFa : a + ε • (b - a) ≤ F a) : GloballyStableOn F (Icc a b) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  set q : ℕ → ℝ := fun k => (1 - ε) ^ k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => pow_nonneg (by linarith) k
  have hq1 : ∀ k, q k ≤ 1 := fun k => pow_le_one₀ (by linarith) (by linarith)
  -- `Fᵏa ≥ a + (1 − qₖ)(Fᵏb − a)`
  have key : ∀ k, a + (1 - q k) • (F^[k] b - a) ≤ F^[k] a := by
    intro k
    induction k with
    | zero => simp [hq]
    | succ k ih =>
      set w := F^[k] b
      set u := F^[k] a
      have hw := hmaps.iterate k hb
      have hu := hmaps.iterate k ha
      have hFw := (hmaps hw).2
      set z := q k • a + (1 - q k) • w
      have hz : z ∈ Icc a b := (convex_Icc a b) ha hw (hq0 k) (by linarith [hq1 k]) (by ring)
      have hzu : z ≤ u := by
        have : z = a + (1 - q k) • (w - a) := by simp only [z]; module
        rw [this]
        exact ih
      have hqs : q (k + 1) = q k * (1 - ε) := by simp only [hq]; ring
      rw [iterate_succ_apply', iterate_succ_apply', hqs]
      have hid : q k • (a + ε • (b - a)) + (1 - q k) • F w =
          (a + (1 - q k * (1 - ε)) • (F w - a)) + (q k * ε) • (b - F w) := by module
      calc a + (1 - q k * (1 - ε)) • (F w - a)
          ≤ (a + (1 - q k * (1 - ε)) • (F w - a)) + (q k * ε) • (b - F w) :=
            le_add_of_nonneg_right (smul_nonneg (mul_nonneg (hq0 k) hε.le) (sub_nonneg.2 hFw))
        _ = q k • (a + ε • (b - a)) + (1 - q k) • F w := hid.symm
        _ ≤ q k • F a + (1 - q k) • F w :=
            add_le_add (smul_le_smul_of_nonneg_left hFa (hq0 k)) le_rfl
        _ ≤ F z := hconc.2 ha hw (hq0 k) (by linarith [hq1 k]) (by ring)
        _ ≤ F u := hmono hz hu hzu
  -- the orbits of `a` and `b` are `qₖ(b − a)` apart
  have gap : ∀ k, ‖F^[k] b - F^[k] a‖ ≤ q k * ‖b - a‖ := by
    intro k
    have hwb := (hmaps.iterate k hb).2
    have h1 : F^[k] b - F^[k] a ≤ q k • (b - a) := by
      have h2 : F^[k] b - F^[k] a ≤ F^[k] b - (a + (1 - q k) • (F^[k] b - a)) :=
        sub_le_sub le_rfl (key k)
      have h3 : F^[k] b - (a + (1 - q k) • (F^[k] b - a)) = q k • (F^[k] b - a) := by module
      rw [h3] at h2
      exact h2.trans (smul_le_smul_of_nonneg_left (sub_le_sub_right hwb a) (hq0 k))
    have h0 : 0 ≤ F^[k] b - F^[k] a := sub_nonneg.2 (iterate_mem_Icc hmaps hmono ha k).2
    have := norm_le_norm_of_abs_le_abs (a := F^[k] b - F^[k] a) (b := q k • (b - a))
      (by rw [abs_of_nonneg h0]; exact h1.trans (le_abs_self _))
    rwa [norm_smul, Real.norm_of_nonneg (hq0 k)] at this
  have hqlim : Tendsto (fun k => q k * ‖b - a‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const
      ‖b - a‖
  have hzero : ∀ x : E, (∀ k, ‖x‖ ≤ q k * ‖b - a‖) → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (ge_of_tendsto' hqlim hx)
  -- points of `[Fᵏa, Fᵏb]` are within `qₖ‖b − a‖` of each other
  have hsq : ∀ k {x y : E}, x ∈ Icc (F^[k] a) (F^[k] b) → y ∈ Icc (F^[k] a) (F^[k] b) →
      ‖x - y‖ ≤ q k * ‖b - a‖ := fun k _ _ hx hy => (norm_sub_le_of_mem_Icc hx hy).trans (gap k)
  have hmem : ∀ k j, F^[k + j] a ∈ Icc (F^[k] a) (F^[k] b) := fun k j => by
    rw [iterate_add_apply]
    exact iterate_mem_Icc hmaps hmono (hmaps.iterate j ha) k
  -- the orbit of `a` is Cauchy
  have hcauchy : CauchySeq fun k => F^[k] a := by
    refine Metric.cauchySeq_iff'.2 fun δ hδ => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hqlim.eventually (gt_mem_nhds hδ))
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [dist_eq_norm]
    exact (hsq N (hmem N j) (iterate_mem_Icc hmaps hmono ha N)).trans_lt (hN N le_rfl)
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  have huk : ∀ k, u ∈ Icc (F^[k] a) (F^[k] b) := fun k =>
    isClosed_Icc.mem_of_tendsto (hu.comp (tendsto_add_atTop_nat k))
      (Eventually.of_forall fun j => by
        simp only [Function.comp_apply]
        rw [add_comm]
        exact hmem k j)
  have huI : u ∈ Icc a b := huk 0
  have hfix : F u = u := by
    refine sub_eq_zero.1 (hzero _ fun k => ?_)
    have hFu : F u ∈ Icc (F^[k + 1] a) (F^[k + 1] b) := by
      rw [iterate_succ_apply', iterate_succ_apply']
      exact ⟨hmono (hmaps.iterate k ha) huI (huk k).1, hmono huI (hmaps.iterate k hb) (huk k).2⟩
    have hqk : q (k + 1) ≤ q k := pow_le_pow_of_le_one (by linarith) (by linarith) k.le_succ
    exact (hsq (k + 1) hFu (huk (k + 1))).trans
      (mul_le_mul_of_nonneg_right hqk (norm_nonneg _))
  refine ⟨u, huI, hfix, fun w hw hwfix => sub_eq_zero.1 (hzero _ fun k => ?_), fun v hv => ?_⟩
  · have := iterate_mem_Icc hmaps hmono hw k
    rw [iterate_fixed hwfix] at this
    exact hsq k this (huk k)
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => hsq k (iterate_mem_Icc hmaps hmono hv k) (huk k)) hqlim)

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
theorem neg_mem_Icc_iff' {a b w : E} : -w ∈ Icc a b ↔ w ∈ Icc (-b) (-a) := by
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨neg_le.1 h2, le_neg.1 h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨le_neg.2 h2, neg_le.2 h1⟩

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] [Lattice E]
  [IsOrderedAddMonoid E] in
theorem iterate_reflect (F : E → E) (k : ℕ) (w : E) :
    (fun x => -F (-x))^[k] w = -F^[k] (-w) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, ih, neg_neg]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E] in
/-- Global stability of the reflection `w ↦ −F(−w)` on `[−b, −a]` gives global stability of `F`
on `[a, b]`. -/
theorem globallyStableOn_of_reflect {a b : E} {F : E → E}
    (h : GloballyStableOn (fun w => -F (-w)) (Icc (-b) (-a))) : GloballyStableOn F (Icc a b) := by
  obtain ⟨u, hu, hfix, huniq, hlim⟩ := h
  refine ⟨-u, neg_mem_Icc_iff'.2 hu, ?_, fun w hw hwfix => ?_, fun v hv => ?_⟩
  · have := congrArg Neg.neg hfix
    simpa using this
  · have := huniq (-w) (neg_mem_Icc_iff'.1 (by rwa [neg_neg])) (by simp [hwfix])
    rw [← this, neg_neg]
  · have := (hlim (-v) (neg_mem_Icc_iff'.1 (by rwa [neg_neg]))).neg
    simpa [iterate_reflect] using this

/-- **Theorem 4.1.10 (Du)** (p. 131), convex case: an order preserving convex self-map of `[a, b]`
with `Sb ≤ b − ε(b − a)` for some `ε ∈ (0, 1]` is globally stable on `[a, b]`. -/
theorem du_convex {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hconv : ConvexOn ℝ (Icc a b) F) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hFb : F b ≤ b - ε • (b - a)) : GloballyStableOn F (Icc a b) := by
  have hmem : ∀ w ∈ Icc (-b) (-a), -w ∈ Icc a b := fun w hw => neg_mem_Icc_iff'.2 hw
  refine globallyStableOn_of_reflect (du_concave (neg_le_neg hab) ?_ ?_ ?_ hε hε1 ?_)
  · intro w hw
    exact neg_mem_Icc_iff'.1 (by rw [neg_neg]; exact hmaps (hmem w hw))
  · intro u hu w hw huw
    exact neg_le_neg (hmono (hmem w hw) (hmem u hu) (neg_le_neg huw))
  · refine ⟨convex_Icc _ _, fun u hu w hw s t hs ht hst => ?_⟩
    have := hconv.2 (hmem u hu) (hmem w hw) hs ht hst
    have h2 : -(s • u + t • w) = s • -u + t • -w := by rw [neg_add, smul_neg, smul_neg]
    change s • -F (-u) + t • -F (-w) ≤ -F (-(s • u + t • w))
    rw [h2, smul_neg, smul_neg, ← neg_add]
    exact neg_le_neg this
  · rw [neg_neg]
    have : -b + ε • (-a - -b) = -(b - ε • (b - a)) := by module
    rw [this]
    exact neg_le_neg hFb

/-- **Theorem 4.1.10 (Du)** (p. 131): an order preserving self-map of `[a, b]` satisfying Du's
conditions is globally stable on `[a, b]`. -/
theorem theorem_4_1_10 {a b : E} (hab : a ≤ b) {F : E → E} (hmaps : MapsTo F (Icc a b) (Icc a b))
    (hmono : MonotoneOn F (Icc a b)) (hdu : DuConditions a b F) : GloballyStableOn F (Icc a b) := by
  rcases hdu with ⟨hconc, ε, hε, hε1, hFa⟩ | ⟨hconv, ε, hε, hε1, hFb⟩
  · exact du_concave hab hmaps hmono hconc hε hε1.le hFa
  · exact du_convex hab hmaps hmono hconv hε hε1.le hFb

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131), (a'): if `Sa − a` is interior to the positive cone, then
`Sa ≥ a + ε(b − a)` for some `ε ∈ (0, 1)`. -/
theorem lemma_4_1_9_concave {a b : E} {F : E → E} (h : F a - a ∈ interior {x : E | 0 ≤ x}) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a + ε • (b - a) ≤ F a := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h)
  set ε := min (1 / 2) (r / (2 * (‖b - a‖ + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨ε, hε, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  have hmem : F a - a - ε • (b - a) ∈ Metric.ball (F a - a) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hε.le]
    calc ε * ‖b - a‖ ≤ r / (2 * (‖b - a‖ + 1)) * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ < r := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (b - a)]
  have h0 : 0 ≤ F a - a - ε • (b - a) := hball hmem
  rw [sub_sub, sub_nonneg] at h0
  exact h0

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131), (b'): if `b − Sb` is interior to the positive cone, then
`Sb ≤ b − ε(b − a)` for some `ε ∈ (0, 1)`. -/
theorem lemma_4_1_9_convex {a b : E} {F : E → E} (h : b - F b ∈ interior {x : E | 0 ≤ x}) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ F b ≤ b - ε • (b - a) := by
  obtain ⟨ε, hε, hε1, hle⟩ := lemma_4_1_9_concave (a := F b) (b := F b + (b - a))
    (F := fun _ => b) h
  refine ⟨ε, hε, hε1, ?_⟩
  have : F b + ε • (F b + (b - a) - F b) = F b + ε • (b - a) := by abel_nf
  rw [this] at hle
  rw [le_sub_iff_add_le]
  exact hle

omit [CompleteSpace E] [HasSolidNorm E] [PosSMulMono ℝ E] in
/-- **Lemma 4.1.9** (p. 131): an order preserving `S` that is concave with `a ≪ Sa`, or convex with
`Sb ≪ b`, satisfies Du's conditions. -/
theorem lemma_4_1_9 {a b : E} {F : E → E}
    (h : (ConcaveOn ℝ (Icc a b) F ∧ F a - a ∈ interior {x : E | 0 ≤ x}) ∨
      (ConvexOn ℝ (Icc a b) F ∧ b - F b ∈ interior {x : E | 0 ≤ x})) : DuConditions a b F := by
  rcases h with ⟨hc, hi⟩ | ⟨hc, hi⟩
  · exact Or.inl ⟨hc, lemma_4_1_9_concave hi⟩
  · exact Or.inr ⟨hc, lemma_4_1_9_convex hi⟩

/-! ### Optimality theory on order intervals -/

open scoped Classical in
/-- A self-map of the subtype `[a, b]`, extended by the identity to `E`. -/
noncomputable def extendIcc {a b : E} (S : Icc a b → Icc a b) (v : E) : E :=
  if h : v ∈ Icc a b then (S ⟨v, h⟩ : E) else v

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
theorem extendIcc_apply {a b : E} (S : Icc a b → Icc a b) (v : Icc a b) :
    extendIcc S v = S v := by
  simp [extendIcc, v.2]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
theorem extendIcc_iterate {a b : E} (S : Icc a b → Icc a b) (k : ℕ) (v : Icc a b) :
    (extendIcc S)^[k] v = (S^[k] v : E) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, extendIcc_apply, ih, iterate_succ_apply]

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [IsOrderedAddMonoid E] in
/-- A globally stable extension makes the subtype map globally stable. -/
theorem globallyStable_of_extendIcc {a b : E} {S : Icc a b → Icc a b}
    (h : GloballyStableOn (extendIcc S) (Icc a b)) : GloballyStable S := by
  obtain ⟨u, hu, hfix, huniq, hlim⟩ := h
  refine ⟨⟨u, hu⟩, Subtype.ext ?_, fun w hw => Subtype.ext (huniq w w.2 ?_), fun v => ?_⟩
  · rw [← extendIcc_apply S ⟨u, hu⟩]
    exact hfix
  · rw [extendIcc_apply, hw]
  · refine tendsto_subtype_rng.2 ?_
    simp only [← extendIcc_iterate]
    exact hlim v v.2

/-- **Theorem 4.1.10** for a self-map of the subtype `[a, b]`. -/
theorem theorem_4_1_10_subtype {a b : E} (hab : a ≤ b) {S : Icc a b → Icc a b}
    (hS : Monotone S) (hdu : DuConditions a b (extendIcc S)) : GloballyStable S := by
  refine globallyStable_of_extendIcc (theorem_4_1_10 hab (fun v hv => ?_) (fun v hv w hw h => ?_)
    hdu)
  · rw [show v = ((⟨v, hv⟩ : Icc a b) : E) from rfl, extendIcc_apply]
    exact (S ⟨v, hv⟩).2
  · rw [show v = ((⟨v, hv⟩ : Icc a b) : E) from rfl, show w = ((⟨w, hw⟩ : Icc a b) : E) from rfl,
      extendIcc_apply, extendIcc_apply]
    exact hS h

omit [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E] [IsOrderedAddMonoid E] in
/-- Order intervals of a countably Dedekind complete space are countably Dedekind complete. -/
theorem countablyDedekindComplete_Icc {a b : E} (hE : CountablyDedekindComplete E) :
    CountablyDedekindComplete (Icc a b) := by
  intro A hne hc
  obtain ⟨x₀, hx₀⟩ := hne
  have h := hE (Subtype.val '' A) ⟨x₀.1, x₀, hx₀, rfl⟩ (hc.image _)
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨s, hs⟩ := h.1 ⟨b, by rintro _ ⟨x, -, rfl⟩; exact x.2.2⟩
    have hsI : s ∈ Icc a b :=
      ⟨x₀.2.1.trans (hs.1 ⟨x₀, hx₀, rfl⟩), hs.2 (by rintro _ ⟨x, -, rfl⟩; exact x.2.2)⟩
    exact ⟨⟨s, hsI⟩, fun x hx => hs.1 ⟨x, hx, rfl⟩, fun w hw =>
      hs.2 (by rintro _ ⟨x, hx, rfl⟩; exact hw hx)⟩
  · obtain ⟨i, hi⟩ := h.2 ⟨a, by rintro _ ⟨x, -, rfl⟩; exact x.2.1⟩
    have hiI : i ∈ Icc a b :=
      ⟨hi.2 (by rintro _ ⟨x, -, rfl⟩; exact x.2.1), (hi.1 ⟨x₀, hx₀, rfl⟩).trans x₀.2.2⟩
    exact ⟨⟨i, hiI⟩, fun x hx => hi.1 ⟨x, hx, rfl⟩, fun w hw =>
      hi.2 (by rintro _ ⟨x, hx, rfl⟩; exact hw hx)⟩

/-- **Theorem 4.1.11** (p. 132): let `(V, 𝕋)` be a regular ADP on `V = [a, b]` whose policy
operators satisfy Du's conditions. If (a) `E` is countably Dedekind complete, (b) `𝕋` is finite,
or (c) the Bellman operator also satisfies Du's conditions, then (i) the fundamental optimality
properties hold and (ii) VFI, OPI and HPI all converge. -/
theorem theorem_4_1_11 {a b : E} (hab : a ≤ b) {P : Type*} (A : ADP (Icc a b) P)
    (hr : A.Regular) (hdu : ∀ σ, DuConditions a b (extendIcc (A.T σ)))
    (hcase : CountablyDedekindComplete E ∨ A.IsFinite ∨
      DuConditions a b (extendIcc A.bellman)) :
    ∃ hw : A.WellPosed, A.FundamentalOptimality hw ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧ A.HPIConverges hw g vstar := by
  have hgs : A.IsGloballyStable := fun σ => theorem_4_1_10_subtype hab (A.mono σ) (hdu σ)
  refine ⟨hgs.wellPosed, ?_⟩
  rcases hcase with hE | hfin | hT
  · exact ADP.theorem_3_1_4 hr hgs ⟨⟨b, hab, le_rfl⟩, fun σ => (A.T σ _).2.2⟩
      (countablyDedekindComplete_Icc hE)
  · exact ADP.corollary_3_1_3 hr hgs hfin
  · obtain ⟨w, hw, -, -⟩ := theorem_4_1_10_subtype hab (ADP.Regular.bellman_monotone A hr) hT
    exact ADP.theorem_3_1_2 hr hgs hw

end BanachLattice

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Operators on `L¹(ψ)`

The Banach lattice `L¹(ψ)` with the `ψ`-a.e. order (§A.5.2.5, Example A.5.7), and the operators
used in §4.2.1.2 and §4.2.2.

* If `ψ` is stationary for the stochastic kernel `P` (`ψP = ψ`, §A.5.4.4), then
  `(Pv)(x) = ∫ v(x')P(x, dx')` is a well defined positive operator on `L¹(ψ)` with `‖P‖ ≤ 1`
  (Lemma A.5.32): `ψ`-null sets are `P(x, ·)`-null for `ψ`-almost every `x`.
* Multiplication by a bounded measurable function is a bounded operator on `L¹(ψ)`, positive when
  the function is nonnegative.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace SargentStachurski.AdditionalApplications

namespace L1

variable {X : Type*} [MeasurableSpace X] (ψ : Measure X)

/-! ### Stationary distributions -/

/-- If `ψP = ψ`, a `ψ`-a.e. property holds `P(x, ·)`-a.e. for `ψ`-a.e. `x`. -/
theorem ae_ae_of_stationary {P : Kernel X X} (hst : ψ.bind P = ψ) {p : X → Prop}
    (h : ∀ᵐ y ∂ψ, p y) : ∀ᵐ x ∂ψ, ∀ᵐ y ∂(P x), p y :=
  Measure.ae_ae_of_ae_bind P.measurable.aemeasurable (by rw [hst]; exact h)

/-- If `ψP = ψ`, then `∫∫ f(y) P(x, dy) ψ(dx) = ∫ f dψ`. -/
theorem lintegral_stationary {P : Kernel X X} (hst : ψ.bind P = ψ) {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, ∫⁻ y, f y ∂(P x) ∂ψ = ∫⁻ y, f y ∂ψ := by
  conv_rhs => rw [← hst]
  rw [Measure.lintegral_bind P.measurable.aemeasurable hf.aemeasurable]

/-! ### The Markov operator on `L¹(ψ)` -/

variable {ψ} {P : Kernel X X} (hst : ψ.bind P = ψ)

/-- `x ↦ ∫ v(x')P(x, dx')` for a representative of `v ∈ L¹(ψ)`. -/
noncomputable def markovFun (f : Lp ℝ 1 ψ) (x : X) : ℝ := ∫ y, f y ∂(P x)

include hst in
theorem lintegral_markov_le (f : Lp ℝ 1 ψ) :
    ∫⁻ x, ‖markovFun (P := P) f x‖ₑ ∂ψ ≤ ∫⁻ y, ‖f y‖ₑ ∂ψ := by
  rw [← lintegral_stationary ψ hst (Lp.stronglyMeasurable f).measurable.enorm]
  exact lintegral_mono fun x => enorm_integral_le_lintegral_enorm _

include hst in
theorem memLp_markovFun (f : Lp ℝ 1 ψ) : MemLp (markovFun (P := P) f) 1 ψ := by
  refine memLp_one_iff_integrable.2
    ⟨((Lp.stronglyMeasurable f).integral_kernel (κ := P)).aestronglyMeasurable, ?_⟩
  exact (lintegral_markov_le hst f).trans_lt
    ((memLp_one_iff_integrable.1 (Lp.memLp f)).hasFiniteIntegral)

include hst in
/-- For `ψ`-a.e. `x`, `v ∈ L¹(ψ)` is `P(x, ·)`-integrable. -/
theorem ae_integrable (f : Lp ℝ 1 ψ) : ∀ᵐ x ∂ψ, Integrable f (P x) := by
  have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(P x) ∂ψ < ∞ := by
    rw [lintegral_stationary ψ hst (Lp.stronglyMeasurable f).measurable.enorm]
    exact (memLp_one_iff_integrable.1 (Lp.memLp f)).hasFiniteIntegral
  filter_upwards [ae_lt_top ((Lp.stronglyMeasurable f).measurable.enorm.lintegral_kernel)
    hfin.ne] with x hx
  exact ⟨(Lp.stronglyMeasurable f).aestronglyMeasurable, hx⟩

include hst in
/-- `markovFun` respects `ψ`-a.e. equality. -/
theorem markovFun_congr {f : Lp ℝ 1 ψ} {g : X → ℝ} (h : ⇑f =ᵐ[ψ] g) :
    ∀ᵐ x ∂ψ, markovFun (P := P) f x = ∫ y, g y ∂(P x) := by
  filter_upwards [ae_ae_of_stationary ψ hst h] with x hx
  exact integral_congr_ae hx

/-- The Markov operator on `L¹(ψ)`, as a linear map. -/
noncomputable def markovLin : Lp ℝ 1 ψ →ₗ[ℝ] Lp ℝ 1 ψ where
  toFun f := (memLp_markovFun hst f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_markovFun hst (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_markovFun hst f).toLp _) ((memLp_markovFun hst g).toLp _),
      (memLp_markovFun hst f).coeFn_toLp, (memLp_markovFun hst g).coeFn_toLp,
      markovFun_congr hst (Lp.coeFn_add f g), ae_integrable hst f, ae_integrable hst g]
      with x h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    exact integral_add h6 h7
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_markovFun hst (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_markovFun hst f).toLp _), (memLp_markovFun hst f).coeFn_toLp,
      markovFun_congr hst (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _

theorem markovLin_apply (f : Lp ℝ 1 ψ) :
    markovLin hst f = (memLp_markovFun hst f).toLp _ := rfl

theorem markovLin_norm_le (f : Lp ℝ 1 ψ) : ‖markovLin hst f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, Lp.norm_def, Lp.norm_def, markovLin_apply]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  rw [eLpNorm_congr_ae (memLp_markovFun hst f).coeFn_toLp,
    eLpNorm_one_eq_lintegral_enorm (memLp_markovFun hst f).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (Lp.stronglyMeasurable f).aestronglyMeasurable]
  exact lintegral_markov_le hst f

/-- The Markov operator `(Pv)(x) = ∫ v(x')P(x, dx')` on `L¹(ψ)`, with `‖P‖ ≤ 1`. -/
noncomputable def markovCLM : Lp ℝ 1 ψ →L[ℝ] Lp ℝ 1 ψ :=
  (markovLin hst).mkContinuous 1 (markovLin_norm_le hst)

/-- **Lemma A.5.32**, the bound used here: `‖P‖ ≤ 1` on `L¹(ψ)`. -/
theorem markovCLM_norm_le : ‖markovCLM hst‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem markovCLM_coeFn (f : Lp ℝ 1 ψ) :
    ⇑(markovCLM hst f) =ᵐ[ψ] fun x => ∫ y, f y ∂(P x) :=
  (memLp_markovFun hst f).coeFn_toLp

/-- The Markov operator is positive. -/
theorem markovCLM_isPositive : BanachLattice.IsPositiveOp (markovCLM hst) := fun f hf => by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  filter_upwards [markovCLM_coeFn hst f, ae_ae_of_stationary ψ hst hf] with x h1 h2
  rw [h1]
  exact integral_nonneg_of_ae h2

/-! ### Multiplication operators -/

theorem memLp_mul {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : MemLp (fun x => h x * f x) 1 ψ :=
  memLp_one_iff_integrable.2 ((memLp_one_iff_integrable.1 (Lp.memLp f)).bdd_mul
    hm.aestronglyMeasurable (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x))

variable (ψ) in
/-- Multiplication by a bounded measurable `h`, as a linear map on `L¹(ψ)`. -/
noncomputable def mulLin {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Lp ℝ 1 ψ →ₗ[ℝ] Lp ℝ 1 ψ where
  toFun f := (memLp_mul hm hC f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_mul hm hC (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul hm hC f).toLp _) ((memLp_mul hm hC g).toLp _),
      (memLp_mul hm hC f).coeFn_toLp, (memLp_mul hm hC g).coeFn_toLp, Lp.coeFn_add f g]
      with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_mul hm hC (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_mul hm hC f).toLp _), (memLp_mul hm hC f).coeFn_toLp,
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring

theorem mulLin_apply {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : mulLin ψ hm hC f = (memLp_mul hm hC f).toLp _ := rfl

variable (ψ) in
/-- Multiplication by a bounded measurable `h`, `|h| ≤ C`, as a bounded operator on `L¹(ψ)`. -/
noncomputable def mulCLM {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Lp ℝ 1 ψ →L[ℝ] Lp ℝ 1 ψ :=
  (mulLin ψ hm hC).mkContinuous C fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_mul hm hC f).coeFn_toLp] with x hx
    rw [mulLin_apply, hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem mulCLM_coeFn {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (f : Lp ℝ 1 ψ) : ⇑(mulCLM ψ hm hC f) =ᵐ[ψ] fun x => h x * f x :=
  (memLp_mul hm hC f).coeFn_toLp

/-- Multiplication by `h ≥ 0` is positive. -/
theorem mulCLM_isPositive {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hh : ∀ x, 0 ≤ h x) : BanachLattice.IsPositiveOp (mulCLM ψ hm hC) := fun f hf => by
  rw [← Lp.coeFn_nonneg] at hf ⊢
  filter_upwards [mulCLM_coeFn hm hC f, hf] with x h1 h2
  rw [h1]
  exact mul_nonneg (hh x) h2

/-- Multiplication by `0 ≤ h ≤ 1` lies below the identity on the positive cone. -/
theorem mulCLM_le_self {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hh1 : ∀ x, h x ≤ 1) {f : Lp ℝ 1 ψ} (hf : 0 ≤ f) : mulCLM ψ hm hC f ≤ f := by
  rw [← Lp.coeFn_nonneg] at hf
  rw [← Lp.coeFn_le]
  filter_upwards [mulCLM_coeFn hm hC f, hf] with x h1 h2
  rw [h1]
  exact mul_le_of_le_one_left h2 (hh1 x)

end L1

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search on `L¹(φ)`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.1 and §8.1.3.1 (pp. 246–256).

The wage offer process is `P`-Markov on a state space `X` with a stationary distribution `φ`
(Assumption 8.1.2); the offer at state `x` is `w(x)`, with `w ∈ L¹(φ)` (finite mean). The iid
model of §8.1.1 (Assumption 8.1.1) is the case `P(x, ·) = φ`. The book's `W ⊆ ℝ₊` with `w(x) = x`
is the case `X = W`; signs of wages are not needed for the optimality results.

* (8.19): `T_σ v = σe + (1 − σ)(c + βPv)` with `e = w/(1 − β)`, an affine operator
  `T_σ v = r_σ + K_σ v` on `L¹(φ)` with `0 ≤ K_σ = (1 − σ)βP ≤ βP`.
* **Exercises 8.1.14–8.1.17**: `T_σ` is an order preserving self-map; the policy (8.20) is
  greedy and the Bellman operator is (8.21); `T_σ` is order continuous; `v_σ` is the Neumann
  series (8.22).
* **Proposition 8.1.2** (Theorem 4.1.8, `ρ(βP) ≤ ‖βP‖ ≤ β`).
* **Exercises 8.1.18–8.1.20**: with `w, c ≥ 0`, the order interval `[0, v̄]`,
  `v̄ = (I − βP)⁻¹(e + c)`, is invariant, contains every `v_σ`, and the optimality results hold
  on it; with `X` finite, HPI terminates.
* The iid case: **Exercises 8.1.1–8.1.3** and **Proposition 8.1.1**.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

/-- Accept/reject policies: measurable `σ : X → Bool`, `true` meaning "accept". -/
abbrev StopPolicy (X : Type*) [MeasurableSpace X] : Type _ := {σ : X → Bool // Measurable σ}

variable {X : Type*} [MeasurableSpace X]

/-- `σ` as a `{0, 1}`-valued function. -/
def polInd (σ : StopPolicy X) (x : X) : ℝ := if σ.1 x then 1 else 0

/-- `1 − σ`. -/
def polCont (σ : StopPolicy X) (x : X) : ℝ := if σ.1 x then 0 else 1

theorem measurable_polInd (σ : StopPolicy X) : Measurable (polInd σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem measurable_polCont (σ : StopPolicy X) : Measurable (polCont σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem abs_polInd_le (σ : StopPolicy X) (x : X) : |polInd σ x| ≤ 1 := by
  simp only [polInd]; split_ifs <;> simp

theorem abs_polCont_le (σ : StopPolicy X) (x : X) : |polCont σ x| ≤ 1 := by
  simp only [polCont]; split_ifs <;> simp

theorem polCont_nonneg (σ : StopPolicy X) (x : X) : 0 ≤ polCont σ x := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polCont_le_one (σ : StopPolicy X) (x : X) : polCont σ x ≤ 1 := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polInd_nonneg (σ : StopPolicy X) (x : X) : 0 ≤ polInd σ x := by
  simp only [polInd]; split_ifs <;> norm_num

/-- The policy accepting where `s ≥ h`, for measurable `s` and `h`. -/
noncomputable def acceptWhere {s h : X → ℝ} (hs : Measurable s) (hh : Measurable h) :
    StopPolicy X :=
  ⟨fun x => decide (h x ≤ s x), measurable_to_bool (by
    have : (fun x => decide (h x ≤ s x)) ⁻¹' {true} = {x | h x ≤ s x} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le hh hs)⟩

theorem acceptWhere_apply {s h : X → ℝ} (hs : Measurable s) (hh : Measurable h) (x : X) :
    (if (acceptWhere hs hh).1 x then s x else h x) = max (s x) (h x) := by
  by_cases hx : h x ≤ s x
  · simp [acceptWhere, hx]
  · simp only [acceptWhere, hx, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge hx)).symm

/-- `id` is an isometric order embedding of `L¹(φ)` into itself. -/
theorem isIsoOrderEmbedding_id_L1 (φ : Measure X) :
    BanachLattice.IsIsoOrderEmbedding (id : Lp ℝ 1 φ → Lp ℝ 1 φ) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

/-- The job search model with `P`-Markov offers (Assumption 8.1.2). -/
structure JobSearch (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- a stationary distribution -/
  φ : Measure X
  [isProb : IsProbabilityMeasure φ]
  stationary : φ.bind P = φ
  /-- the wage offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  integrable_wage : Integrable wage φ
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

variable (M : JobSearch X)

/-- The Markov operator `P` on `L¹(φ)`. -/
noncomputable def Pop : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := L1.markovCLM M.stationary

/-- `K = βP`. -/
noncomputable def D : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := M.β • M.Pop

/-- The stopping value `e(x) = w(x)/(1 − β)` (8.2). -/
noncomputable def efun (x : X) : ℝ := M.wage x / (1 - M.β)

theorem measurable_efun : Measurable M.efun := M.measurable_wage.div_const _

/-- `e ∈ L¹(φ)`. -/
noncomputable def e : Lp ℝ 1 M.φ :=
  (memLp_one_iff_integrable.2 (M.integrable_wage.div_const (1 - M.β))).toLp M.efun

/-- The constant `c` in `L¹(φ)`. -/
noncomputable def cconst : Lp ℝ 1 M.φ := (memLp_const M.c).toLp _

theorem e_coeFn : ⇑M.e =ᵐ[M.φ] M.efun :=
  (memLp_one_iff_integrable.2 (M.integrable_wage.div_const (1 - M.β))).coeFn_toLp

theorem cconst_coeFn : ⇑M.cconst =ᵐ[M.φ] fun _ => M.c := (memLp_const M.c).coeFn_toLp

/-- `r_σ = σe + (1 − σ)c`. -/
noncomputable def rσ (σ : StopPolicy X) : Lp ℝ 1 M.φ :=
  L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e +
    L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst

/-- `K_σ = (1 − σ)βP`. -/
noncomputable def Kσ (σ : StopPolicy X) : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ :=
  L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) ∘L M.D

theorem D_isPositive : BanachLattice.IsPositiveOp M.D := fun v hv => by
  have h := L1.markovCLM_isPositive M.stationary v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul M.β (M.Pop v), h] with x h1 h2
  change 0 ≤ (M.β • M.Pop v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg M.β_nonneg h2

theorem Kσ_isPositive (σ : StopPolicy X) : BanachLattice.IsPositiveOp (M.Kσ σ) := fun v hv =>
  L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ) _
    (M.D_isPositive v hv)

theorem Kσ_le_D (σ : StopPolicy X) (h : Lp ℝ 1 M.φ) (hh : 0 ≤ h) : M.Kσ σ h ≤ M.D h :=
  L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ) (polCont_le_one σ)
    (M.D_isPositive h hh)

theorem norm_D_le : ‖M.D‖ ≤ M.β :=
  ContinuousLinearMap.opNorm_le_bound _ M.β_nonneg fun v => by
    change ‖M.β • M.Pop v‖ ≤ M.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((M.Pop.le_opNorm v).trans ?_) M.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)

/-- `ρ(βP) ≤ ‖βP‖ ≤ β < 1` (the book cites Lemma A.5.32 for `ρ(βP) = β`). -/
theorem specRad_D_lt_one : BanachLattice.specRad M.D < 1 :=
  ((BanachLattice.specRad_le_norm _).trans M.norm_D_le).trans_lt M.β_lt_one

/-- The job search ADP `(L¹(φ), 𝕋)`. -/
noncomputable def adp : ADP (Lp ℝ 1 M.φ) (StopPolicy X) where
  T σ v := M.rσ σ + M.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl ((M.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (8.19): `T_σ v = σe + (1 − σ)(c + βPv)` almost everywhere. -/
theorem T_coeFn (σ : StopPolicy X) (v : Lp ℝ 1 M.φ) :
    ⇑(M.adp.T σ v) =ᵐ[M.φ] fun x => if σ.1 x then M.efun x else M.c + M.β * M.Pop v x := by
  filter_upwards [Lp.coeFn_add (M.rσ σ) (M.Kσ σ v),
    Lp.coeFn_add (L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e)
      (L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) M.e,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) M.cconst,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) (M.D v),
    Lp.coeFn_smul M.β (M.Pop v), M.e_coeFn, M.cconst_coeFn]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  change (M.rσ σ + M.Kσ σ v) x = _
  rw [h1, Pi.add_apply]
  change (L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e +
    L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst) x +
    (L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) (M.D v)) x = _
  rw [h2, Pi.add_apply, h3, h4, h5]
  change polInd σ x * M.e x + polCont σ x * M.cconst x + polCont σ x * (M.β • M.Pop v) x = _
  rw [h6, Pi.smul_apply, smul_eq_mul, h7, h8]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- **Exercise 8.1.14** (p. 255): `T_σ` is an order preserving self-map on `L¹(φ)`. -/
theorem exercise_8_1_14 (σ : StopPolicy X) : Monotone (M.adp.T σ) := M.adp.mono σ

/-- The policy (8.20): accept when `e ≥ c + βPv`. -/
noncomputable def accept (v : Lp ℝ 1 M.φ) : StopPolicy X :=
  acceptWhere (s := M.efun) (h := fun x => M.c + M.β * M.Pop v x) M.measurable_efun
    (measurable_const.add (measurable_const.mul (Lp.stronglyMeasurable (M.Pop v)).measurable))

theorem T_accept_coeFn (v : Lp ℝ 1 M.φ) :
    ⇑(M.adp.T (M.accept v) v) =ᵐ[M.φ] fun x => max (M.efun x) (M.c + M.β * M.Pop v x) := by
  filter_upwards [M.T_coeFn (M.accept v) v] with x hx
  rw [hx]
  exact acceptWhere_apply M.measurable_efun _ x

/-- **Exercise 8.1.15** (p. 255): the policy (8.20) is `v`-greedy, and the Bellman operator is
(8.21), `(Tv)(w) = max{w/(1 − β), c + β ∫ v(w')P(w, dw')}` almost everywhere. -/
theorem exercise_8_1_15 (v : Lp ℝ 1 M.φ) :
    M.adp.IsGreedy v (M.accept v) ∧
      ⇑(M.adp.bellman v) =ᵐ[M.φ] fun x => max (M.efun x) (M.c + M.β * M.Pop v x) := by
  have hg : M.adp.IsGreedy v (M.accept v) := fun τ => by
    rw [← Lp.coeFn_le]
    filter_upwards [M.T_coeFn τ v, M.T_accept_coeFn v] with x h1 h2
    rw [h1, h2]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨hg, ?_⟩
  have heq : M.adp.bellman v = M.adp.T (M.accept v) v :=
    le_antisymm (hg _) (M.adp.isGreedy_greedy ⟨_, hg⟩ _)
  rw [heq]
  exact M.T_accept_coeFn v

theorem regular : M.adp.Regular := fun v => ⟨_, (M.exercise_8_1_15 v).1⟩

theorem isAdditive : BanachLattice.IsAdditive id M.adp M.rσ M.Kσ :=
  ⟨M.Kσ_isPositive, fun _ _ => rfl⟩

theorem isGloballyStable : M.adp.IsGloballyStable := fun σ =>
  (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 M.φ)
    ⟨BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one, fun v w =>
      (M.isAdditive.abs_sub σ v w).trans (M.Kσ_le_D σ _ (abs_nonneg _))⟩).1

/-- Iterating `T_σ` from `0` gives the partial sums `∑_{t < n} K_σ^t r_σ`. -/
theorem iterate_T_zero (σ : StopPolicy X) (n : ℕ) :
    (M.adp.T σ)^[n] 0 = ∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ']
    change M.rσ σ + M.Kσ σ (∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ)) = _
    rw [map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ']
    rfl

/-- **Exercise 8.1.17** (p. 256): `T_σ` has a unique fixed point `v_σ` in `L¹(φ)`, the Neumann
series `v_σ = ∑_{t ≥ 0} [β(1 − σ)P]^t (σe + (1 − σ)c)` (8.22). -/
theorem exercise_8_1_17 (σ : StopPolicy X) :
    ∃ vσ, M.adp.T σ vσ = vσ ∧ (∀ w, M.adp.T σ w = w → w = vσ) ∧
      Tendsto (fun n => ∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ)) atTop (𝓝 vσ) := by
  obtain ⟨u, hu, huniq, hlim⟩ := M.isGloballyStable σ
  exact ⟨u, hu, huniq, (hlim 0).congr fun n => M.iterate_T_zero σ n⟩

/-- **Exercise 8.1.1** (p. 247) and the well-posedness claim of Proposition 8.1.2: every `T_σ` has
a unique fixed point. -/
theorem wellPosed : M.adp.WellPosed := M.isGloballyStable.wellPosed

/-- **Proposition 8.1.2** (p. 256): under Assumption 8.1.2, the job search ADP `(L¹(φ), 𝕋)` is
well-posed, (i) the fundamental optimality properties hold, and (ii) VFI, OPI and HPI all
converge (Theorem 4.1.8). -/
theorem proposition_8_1_2 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar,
      M.adp.VFIGeometric univ vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one
  have hsr : M.adp.IsSemiRegular univ := ⟨isClosed_univ, fun v _ => M.regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 M.φ) M.adp M.isAdditive hD M.Kσ_le_D hsr univ_nonempty
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 M.regular M.isGloballyStable
    ((M.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv M.regular⟩

end JobSearch

/-! ### Order continuity -/

/-- In `L¹(φ)`, an increasing sequence with supremum `v` converges to `v` in norm: the norm is
σ-order continuous (monotone convergence). -/
theorem L1.tendsto_of_monotone_isLUB {φ : Measure X} {f : ℕ → Lp ℝ 1 φ} {v : Lp ℝ 1 φ}
    (hf : Monotone f) (hv : IsLUB (range f) v) : Tendsto f atTop (𝓝 v) := by
  have hmono : ∀ᵐ x ∂φ, Monotone fun n => f n x := by
    have h2 : ∀ᵐ x ∂φ, ∀ n m, n ≤ m → f n x ≤ f m x := by
      rw [ae_all_iff]
      intro n
      rw [ae_all_iff]
      intro m
      by_cases h : n ≤ m
      · filter_upwards [(Lp.coeFn_le _ _).2 (hf h)] with x hx _ using hx
      · exact Eventually.of_forall fun x h' => absurd h' h
    filter_upwards [h2] with x hx n m h using hx n m h
  have hle : ∀ᵐ x ∂φ, ∀ n, f n x ≤ v x := ae_all_iff.2 fun n => (Lp.coeFn_le _ _).2 (hv.1 ⟨n, rfl⟩)
  -- the pointwise limit `g = sup_n f_n`
  let g : X → ℝ := fun x => ⨆ n, f n x
  have hlim : ∀ᵐ x ∂φ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [hmono, hle] with x h1 h2
    exact tendsto_atTop_ciSup h1 ⟨v x, by rintro _ ⟨n, rfl⟩; exact h2 n⟩
  have hgle : ∀ᵐ x ∂φ, g x ≤ v x := by
    filter_upwards [hle] with x h2
    exact ciSup_le h2
  have hge : ∀ᵐ x ∂φ, ∀ n, f n x ≤ g x := by
    filter_upwards [hle] with x h2 n
    exact le_ciSup ⟨v x, by rintro _ ⟨m, rfl⟩; exact h2 m⟩ n
  have hgm : AEStronglyMeasurable g φ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable (f n)) hlim
  have hgi : Integrable g φ := by
    refine ((L1.integrable_coeFn (f 0)).norm.add (L1.integrable_coeFn v).norm).mono' hgm ?_
    filter_upwards [hge, hgle] with x h1 h2
    rw [Real.norm_eq_abs, abs_le]
    have h3 := h1 0
    constructor <;> simp only [Pi.add_apply, Real.norm_eq_abs] <;>
      linarith [neg_abs_le (f 0 x), le_abs_self (v x), abs_nonneg (f 0 x), abs_nonneg (v x)]
  have hGcoe := hgi.coeFn_toL1
  -- `v` is the class of `g`
  have hvG : v = hgi.toL1 g := by
    refine le_antisymm (hv.2 ?_) ((Lp.coeFn_le _ _).1 ?_)
    · rintro _ ⟨n, rfl⟩
      refine (Lp.coeFn_le _ _).1 ?_
      filter_upwards [hge, hGcoe] with x h1 h2
      rw [h2]
      exact h1 n
    · filter_upwards [hGcoe, hgle] with x h1 h2
      rw [h1]
      exact h2
  have hvg : ∀ᵐ x ∂φ, v x = g x := by
    rw [hvG]
    exact hGcoe
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖f n - v‖ = ∫ x, |f n x - v x| ∂φ := fun n => by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f n) v] with x hx
    rw [hx, Pi.sub_apply, Real.norm_eq_abs]
  simp_rw [hnorm]
  have := tendsto_integral_of_dominated_convergence (μ := φ)
    (F := fun n x => |f n x - v x|) (f := fun _ => (0 : ℝ)) (fun x => |f 0 x - v x|)
    (fun n => continuous_abs.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable v)))
    ((L1.integrable_coeFn (f 0)).sub (L1.integrable_coeFn v)).abs
    (fun n => by
      filter_upwards [hle, hmono] with x h1 h2
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.2 (h1 n)),
        abs_of_nonpos (sub_nonpos.2 (h1 0))]
      linarith [h2 (Nat.zero_le n)])
    (by
      filter_upwards [hlim, hvg] with x h1 h2
      have := (h1.sub_const (v x)).abs
      rwa [← h2, sub_self, abs_zero] at this)
  simpa using this

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

variable (M : JobSearch X)

/-- **Exercise 8.1.16** (p. 256): every policy operator `T_σ` is order continuous on `L¹(φ)`. -/
theorem exercise_8_1_16 (σ : StopPolicy X) : OrderContinuous (M.adp.T σ) := fun f v hf hv => by
  have hcont : Continuous (M.adp.T σ) := continuous_const.add (M.Kσ σ).continuous
  exact isLUB_of_tendsto_of_le (hcont.continuousAt.tendsto.comp
    (L1.tendsto_of_monotone_isLUB hf hv)) fun n => M.adp.mono σ (hv.1 ⟨n, rfl⟩)

/-! ### The order interval `[0, v̄]` -/

/-- `v ↦ e + c + βPv`, a contraction of modulus `β`. -/
noncomputable def Sbar (v : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := M.e + M.cconst + M.D v

theorem Sbar_contracting : ContractingWith ⟨M.β, M.β_nonneg⟩ M.Sbar := by
  refine ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Sbar, Sbar, add_sub_add_left_eq_sub, ← map_sub]
  exact (M.D.le_opNorm _).trans (mul_le_mul_of_nonneg_right M.norm_D_le (norm_nonneg _))

/-- `v̄ = (I − βP)⁻¹(e + c)`: the unique solution of `v̄ = e + c + βPv̄`. -/
noncomputable def vbar : Lp ℝ 1 M.φ := ContractingWith.fixedPoint M.Sbar M.Sbar_contracting

theorem vbar_eq : M.vbar = M.e + M.cconst + M.D M.vbar :=
  (ContractingWith.fixedPoint_isFixedPt M.Sbar_contracting).symm

theorem e_nonneg (hw : ∀ x, 0 ≤ M.wage x) : 0 ≤ M.e := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [M.e_coeFn] with x hx
  rw [hx]
  exact div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)

theorem cconst_nonneg (hc : 0 ≤ M.c) : 0 ≤ M.cconst := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [M.cconst_coeFn] with x hx
  rw [hx]
  exact hc

theorem vbar_nonneg (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) : 0 ≤ M.vbar := by
  have hpos : ∀ n, 0 ≤ M.Sbar^[n] 0 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact add_nonneg (add_nonneg (M.e_nonneg hw) (M.cconst_nonneg hc)) (M.D_isPositive _ ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint M.Sbar_contracting 0) hpos

/-- `T_σ v ≤ e + c + βPv` when `w, c ≥ 0` and `v ≥ 0`. -/
theorem T_le_Sbar (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) (σ : StopPolicy X) {v : Lp ℝ 1 M.φ}
    (hv : 0 ≤ v) : M.adp.T σ v ≤ M.Sbar v := by
  rw [← Lp.coeFn_le]
  have hD := M.D_isPositive v hv
  rw [← Lp.coeFn_nonneg] at hD
  filter_upwards [M.T_coeFn σ v, Lp.coeFn_add (M.e + M.cconst) (M.D v),
    Lp.coeFn_add M.e M.cconst, M.e_coeFn, M.cconst_coeFn, Lp.coeFn_smul M.β (M.Pop v), hD]
    with x h1 h2 h3 h4 h5 h6 h7
  change _ ≤ (M.e + M.cconst + M.D v) x
  rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5]
  have h8 : (M.D v) x = M.β * M.Pop v x := by
    change (M.β • M.Pop v) x = _
    rw [h6, Pi.smul_apply, smul_eq_mul]
  rw [h8] at h7 ⊢
  have h7' : (0 : ℝ) ≤ M.β * M.Pop v x := h7
  have he : 0 ≤ M.efun x := div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)
  split_ifs <;> linarith

theorem T_nonneg (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) (σ : StopPolicy X) {v : Lp ℝ 1 M.φ}
    (hv : 0 ≤ v) : 0 ≤ M.adp.T σ v := by
  rw [← Lp.coeFn_nonneg]
  have hD := M.D_isPositive v hv
  rw [← Lp.coeFn_nonneg] at hD
  filter_upwards [M.T_coeFn σ v, Lp.coeFn_smul M.β (M.Pop v), hD] with x h1 h2 h3
  rw [h1]
  have h4 : (M.D v) x = M.β * M.Pop v x := by
    change (M.β • M.Pop v) x = _
    rw [h2, Pi.smul_apply, smul_eq_mul]
  rw [h4] at h3
  have h3' : (0 : ℝ) ≤ M.β * M.Pop v x := h3
  split_ifs
  · exact div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)
  · change (0 : ℝ) ≤ M.c + M.β * M.Pop v x
    linarith

/-- **Exercise 8.1.18** (p. 256): if wages and `c` are nonnegative, then `v_σ ≤ v̄` for every `σ`
and every `T_σ` maps `V = [0, v̄]` into itself. -/
theorem exercise_8_1_18 (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    (∀ σ, M.adp.vσ M.wellPosed σ ≤ M.vbar) ∧
      ∀ σ v, 0 ≤ v → v ≤ M.vbar → 0 ≤ M.adp.T σ v ∧ M.adp.T σ v ≤ M.vbar := by
  have hTv : ∀ σ, M.adp.T σ M.vbar ≤ M.vbar := fun σ => by
    have := M.T_le_Sbar hw hc σ (M.vbar_nonneg hw hc)
    rwa [show M.Sbar M.vbar = M.vbar from (M.vbar_eq).symm] at this
  refine ⟨fun σ => M.isGloballyStable.isOrderStable.vσ_le σ M.vbar (hTv σ),
    fun σ v hv0 hv => ⟨M.T_nonneg hw hc σ hv0, (M.adp.mono σ hv).trans (hTv σ)⟩⟩

/-- The ADP `(V, 𝕋)` on `V = [0, v̄]` (Exercise 8.1.18). -/
noncomputable def adpV (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    ADP (Icc 0 M.vbar) (StopPolicy X) where
  T σ v := ⟨M.adp.T σ v, (M.exercise_8_1_18 hw hc).2 σ v v.2.1 v.2.2⟩
  mono σ _ _ h := M.adp.mono σ h
  nonempty := M.adp.nonempty

/-- **Exercise 8.1.19** (p. 256): the optimality results hold for `(V, 𝕋)`, `V = [0, v̄]`: the
fundamental optimality properties hold and VFI, OPI and HPI converge (Theorem 4.1.8 on the
closed order interval). -/
theorem exercise_8_1_19 (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    ∃ hw' : (M.adpV hw hc).WellPosed, (M.adpV hw hc).FundamentalOptimality hw' ∧ ∃ vstar,
      (M.adpV hw hc).VFIGeometric univ vstar ∧
        ∀ g, (M.adpV hw hc).IsSelector g →
          (M.adpV hw hc).OPIConverges g vstar ∧ (M.adpV hw hc).HPIConverges hw' g vstar := by
  have : CompleteSpace (Icc 0 M.vbar) := isClosed_Icc.completeSpace_coe
  have : Nonempty (Icc 0 M.vbar) := ⟨⟨0, le_rfl, M.vbar_nonneg hw hc⟩⟩
  have hι : BanachLattice.IsIsoOrderEmbedding (Subtype.val : Icc 0 M.vbar → Lp ℝ 1 M.φ) :=
    ⟨fun v w => dist_eq_norm (v : Lp ℝ 1 M.φ) w, fun _ _ => Iff.rfl⟩
  have hadd : BanachLattice.IsAdditive Subtype.val (M.adpV hw hc) M.rσ M.Kσ :=
    ⟨M.Kσ_isPositive, fun _ _ => rfl⟩
  have hreg : (M.adpV hw hc).Regular := fun v => ⟨M.accept v, fun τ =>
    (M.exercise_8_1_15 v).1 τ⟩
  have hsr : (M.adpV hw hc).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => hreg v, mapsTo_univ _ _⟩
  obtain ⟨hw', hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8 hι (M.adpV hw hc) hadd
    (BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one) M.Kσ_le_D hsr univ_nonempty
  exact ⟨hw', hFO, vstar, hgeo, hconv hreg⟩

/-- **Exercise 8.1.20** (p. 256): if the state space is finite, HPI converges in finitely many
steps: from every `v ∈ V_U`, some iterate of Howard's operator is the value function
(Theorem 2.2.6). -/
theorem exercise_8_1_20 [Finite X] :
    M.adp.FundamentalOptimality M.isGloballyStable.isOrderStable.wellPosed ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.isGloballyStable.isOrderStable.wellPosed g)^[n]
          v) :=
  ADP.fundamentalOptimality_of_finite M.isGloballyStable.isOrderStable M.regular
    (Set.finite_range _)

/-! ### The iid model -/

/-- The iid job search model (Assumption 8.1.1): offers drawn from `φ` each period, as the
Markov model with `P(x, ·) = φ`. -/
noncomputable abbrev iid (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    JobSearch X where
  P := Kernel.const X φ
  φ := φ
  stationary := by
    change φ.bind (fun _ => φ) = φ
    rw [Measure.bind_const, measure_univ, one_smul]
  wage := wage
  measurable_wage := hm
  integrable_wage := hi
  c := c
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

/-- In the iid model, `Pv = ∫ v dφ` almost everywhere. -/
theorem iid_Pop_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Lp ℝ 1 φ) :
    ⇑((iid φ wage hm hi c β hβ0 hβ1).Pop v) =ᵐ[φ] fun _ => ∫ y, v y ∂φ :=
  L1.markovCLM_coeFn _ v

/-- **Exercises 8.1.2–8.1.3** (p. 247): in the iid model the policy (8.5),
`σ(w) = 𝟙{w/(1 − β) ≥ c + β ∫ v dφ}`, is `v`-greedy, and the Bellman operator is (8.7),
`(Tv)(w) = max{w/(1 − β), c + β ∫ v dφ}`. -/
theorem exercise_8_1_2_3 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Lp ℝ 1 φ) :
    (iid φ wage hm hi c β hβ0 hβ1).adp.IsGreedy v ((iid φ wage hm hi c β hβ0 hβ1).accept v) ∧
      ⇑((iid φ wage hm hi c β hβ0 hβ1).adp.bellman v) =ᵐ[φ]
        fun x => max (wage x / (1 - β)) (c + β * ∫ y, v y ∂φ) := by
  obtain ⟨hg, hT⟩ := (iid φ wage hm hi c β hβ0 hβ1).exercise_8_1_15 v
  refine ⟨hg, ?_⟩
  filter_upwards [hT, iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 v] with x h1 h2
  rw [h1, h2]
  rfl

/-- **Exercise 8.1.1** (p. 247) and **Proposition 8.1.1** (p. 249): under Assumption 8.1.1 the
iid job search ADP `(L¹(φ), 𝕋)` is well-posed, the fundamental optimality properties hold, and
VFI, OPI and HPI all converge. -/
theorem proposition_8_1_1 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ hw : (iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed,
      (iid φ wage hm hi c β hβ0 hβ1).adp.FundamentalOptimality hw ∧ ∃ vstar,
        (iid φ wage hm hi c β hβ0 hβ1).adp.VFIConverges vstar ∧
        ∀ g, (iid φ wage hm hi c β hβ0 hβ1).adp.IsSelector g →
          (iid φ wage hm hi c β hβ0 hβ1).adp.OPIConverges g vstar ∧
            (iid φ wage hm hi c β hβ0 hβ1).adp.HPIConverges hw g vstar := by
  obtain ⟨hw, hFO, vstar, -, hvfi, hconv⟩ := (iid φ wage hm hi c β hβ0 hβ1).proposition_8_1_2
  exact ⟨hw, hFO, vstar, hvfi, hconv⟩

end JobSearch

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search with bounded offers

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.1.2 (pp. 248–249).

Offers lie in a bounded Borel set `W ⊆ ℝ`, drawn iid from `φ`, and
`(T_σ v)(w) = σ(w) w/(1 − β) + (1 − σ(w))[c + β ∫ v dφ]` (8.4) acts on bounded functions.

* **Exercise 8.1.4**: `(bW, 𝕋)` is an ADP with Bellman operator (8.7), and the Bellman operator
  maps `bcW`, `ibcW` and (for `W ⊆ ℝ₊`) `ibcW₊` into themselves. The exercise also asserts that
  `(V, 𝕋)` is an ADP for these three spaces; that is false, since a policy operator `T_σ` with a
  discontinuous `σ` does not map `bcW` into itself (`exercise_8_1_4_counterexample`).
* **Exercise 8.1.5**: the problem is an RDP on `bW` with `Γ(w) = {0, 1}` and aggregator (8.8).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

namespace BoundedSearch

variable {W : Set ℝ} (φ : Measure W) [IsProbabilityMeasure φ] (c β : ℝ)

/-- The continuation value `c + β ∫ v dφ`. -/
noncomputable def cont (v : BM W) : ℝ := c + β * ∫ w, v.toFun w ∂φ

/-- (8.4): `(T_σ v)(w) = σ(w) w/(1 − β) + (1 − σ(w))[c + β ∫ v dφ]`. -/
noncomputable def T (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (σ : StopPolicy W) (v : BM W) : BM W :=
  ⟨fun w => if σ.1 w then (w : ℝ) / (1 - β) else cont φ c β v,
    Measurable.ite (σ.2 (measurableSet_singleton true))
      (measurable_subtype_coe.div_const _) measurable_const, by
    obtain ⟨K, hK⟩ := hW
    refine ⟨K / |1 - β| + |cont φ c β v|, fun w => ?_⟩
    split_ifs
    · rw [abs_div]
      exact le_add_of_le_of_nonneg (div_le_div_of_nonneg_right (hK w w.2) (abs_nonneg _))
        (abs_nonneg _)
    · exact le_add_of_nonneg_left (div_nonneg ((abs_nonneg _).trans (hK w w.2))
        (abs_nonneg _))⟩

omit [IsProbabilityMeasure φ] in
theorem T_apply (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (σ : StopPolicy W) (v : BM W) (w : W) :
    (T φ c β hW σ v).toFun w = if σ.1 w then (w : ℝ) / (1 - β) else cont φ c β v := rfl

theorem cont_mono (hβ : 0 ≤ β) {v v' : BM W} (h : v ≤ v') : cont φ c β v ≤ cont φ c β v' :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (Integrable.of_bound v.measurable'.aestronglyMeasurable ‖v‖
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v w))
    (Integrable.of_bound v'.measurable'.aestronglyMeasurable ‖v'‖
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v' w))
    fun w => BM.le_def.1 h w) hβ)

/-- The job search ADP `(bW, 𝕋)` (Exercise 8.1.4). -/
noncomputable def adp (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) : ADP (BM W) (StopPolicy W) where
  T := T φ c β hW
  mono σ v v' h := BM.le_def.2 fun w => by
    rw [T_apply, T_apply]
    split_ifs
    · exact le_rfl
    · exact cont_mono φ c β hβ h
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy (8.5): accept when `w/(1 − β) ≥ c + β ∫ v dφ`. -/
noncomputable def accept (v : BM W) : StopPolicy W :=
  acceptWhere (s := fun w : W => (w : ℝ) / (1 - β)) (h := fun _ => cont φ c β v)
    (measurable_subtype_coe.div_const _) measurable_const

/-- **Exercise 8.1.4** (p. 248), first part: `(bW, 𝕋)` is an ADP, the policy (8.5) is
`v`-greedy, and the Bellman operator is (8.7), `(Tv)(w) = max{w/(1 − β), c + β ∫ v dφ}`. -/
theorem exercise_8_1_4 (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) (v : BM W) :
    (adp φ c β hW hβ).IsGreedy v (accept φ c β v) ∧
      ∀ w, ((adp φ c β hW hβ).bellman v).toFun w = max ((w : ℝ) / (1 - β)) (cont φ c β v) := by
  have hval : ∀ w, ((adp φ c β hW hβ).T (accept φ c β v) v).toFun w =
      max ((w : ℝ) / (1 - β)) (cont φ c β v) := fun w =>
    acceptWhere_apply (s := fun w : W => (w : ℝ) / (1 - β)) (h := fun _ => cont φ c β v)
      (measurable_subtype_coe.div_const _) measurable_const w
  have hg : (adp φ c β hW hβ).IsGreedy v (accept φ c β v) := fun τ => BM.le_def.2 fun w => by
    rw [hval]
    change (if τ.1 w then (w : ℝ) / (1 - β) else cont φ c β v) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : (adp φ c β hW hβ).bellman v = (adp φ c β hW hβ).T (accept φ c β v) v :=
    le_antisymm (hg _) ((adp φ c β hW hβ).isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun w => by rw [heq, hval]⟩

/-- **Exercise 8.1.4** (p. 248), second part: the Bellman operator maps `bcW`, `ibcW` and, when
`W ⊆ ℝ₊` and `β < 1`, `ibcW₊` into themselves. -/
theorem exercise_8_1_4_bellman (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (v : BM W) :
    Continuous ((adp φ c β hW hβ).bellman v).toFun ∧
      Monotone ((adp φ c β hW hβ).bellman v).toFun ∧
      ((∀ w ∈ W, 0 ≤ w) → ∀ w, 0 ≤ ((adp φ c β hW hβ).bellman v).toFun w) := by
  have hb := (exercise_8_1_4 φ c β hW hβ v).2
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  refine ⟨?_, fun w w' h => ?_, fun hW0 w => ?_⟩
  · rw [show ((adp φ c β hW hβ).bellman v).toFun = fun w : W =>
      max ((w : ℝ) / (1 - β)) (cont φ c β v) from funext hb]
    exact (continuous_subtype_val.div_const _).max continuous_const
  · rw [hb, hb]
    exact max_le_max (div_le_div_of_nonneg_right (Subtype.coe_le_coe.2 h) hpos.le) le_rfl
  · rw [hb]
    exact le_max_of_le_left (div_nonneg (hW0 w w.2) hpos.le)

/-- **Exercise 8.1.4** is false for `bcW`: with `W = [0, 1]`, `β = 1/2`, `c = 0` and
`σ = 𝟙{w ≥ 1/2}`, `T_σ 0 = 2w 𝟙{w ≥ 1/2}` is discontinuous, so `T_σ` does not map `bcW` (nor
`ibcW`, `ibcW₊`) into itself. -/
theorem exercise_8_1_4_counterexample :
    ∃ (φ : Measure (Icc (0 : ℝ) 1)) (_ : IsProbabilityMeasure φ)
      (hW : ∃ K, ∀ w ∈ Icc (0 : ℝ) 1, |w| ≤ K) (σ : StopPolicy (Icc (0 : ℝ) 1)),
      ¬ Continuous (T φ 0 (1 / 2) hW σ 0).toFun := by
  let φ : Measure (Icc (0 : ℝ) 1) := Measure.dirac ⟨0, le_rfl, zero_le_one⟩
  have hW : ∃ K, ∀ w ∈ Icc (0 : ℝ) 1, |w| ≤ K :=
    ⟨1, fun w hw => by rw [abs_of_nonneg hw.1]; exact hw.2⟩
  let σ : StopPolicy (Icc (0 : ℝ) 1) :=
    acceptWhere (s := fun w : Icc (0 : ℝ) 1 => (w : ℝ)) (h := fun _ => 1 / 2)
      measurable_subtype_coe measurable_const
  refine ⟨φ, inferInstance, hW, σ, fun hc => ?_⟩
  let F : ℝ → ℝ := fun t => (T φ 0 (1 / 2) hW σ 0).toFun (projIcc 0 1 zero_le_one t)
  have hF : ∀ t, F t = if (1 : ℝ) / 2 ≤ (projIcc 0 1 zero_le_one t : ℝ)
      then (projIcc 0 1 zero_le_one t : ℝ) / (1 - 1 / 2) else 0 := fun t => by
    simp only [F, T_apply, σ, acceptWhere, cont, BM.zero_apply, integral_zero, mul_zero,
      add_zero, decide_eq_true_eq]
  have hcF : Continuous F := hc.comp continuous_projIcc
  -- `F = 0` to the left of `1/2` and `F(1/2) = 1`
  have hleft : F =ᶠ[𝓝[<] ((1 : ℝ) / 2)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hF]
    have hlt : (projIcc 0 1 zero_le_one t : ℝ) < 1 / 2 := by
      rw [coe_projIcc]
      exact max_lt (by norm_num) (min_lt_of_right_lt ht)
    simp only [not_le.2 hlt, ↓reduceIte]
  have hhalf : F (1 / 2) = 1 := by
    rw [hF, projIcc_of_mem _ ⟨by norm_num, by norm_num⟩]
    norm_num
  have h1 : Tendsto F (𝓝[<] ((1 : ℝ) / 2)) (𝓝 (F (1 / 2))) :=
    (hcF.continuousAt (x := 1 / 2)).tendsto.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' hleft.symm)
  rw [hhalf] at h2
  norm_num at h2

/-- The aggregator (8.8): `B(w, a, v) = a w/(1 − β) + (1 − a)[c + β ∫ v dφ]`. -/
noncomputable def Bagg (w : W) (a : ℝ) (v : W → ℝ) : ℝ :=
  a * ((w : ℝ) / (1 - β)) + (1 - a) * (c + β * ∫ x, v x ∂φ)

/-- **Exercise 8.1.5** (p. 249): with `Γ(w) = {0, 1}` and `V = bW`, the job search problem is an
RDP with aggregator (8.8): `B` is measurable in `(w, a)`, monotone in `v` and bounded on `G` for
each `v`. -/
noncomputable def exercise_8_1_5 (hW : ∃ K, ∀ w ∈ W, |w| ≤ K) (hβ : 0 ≤ β) : BRDP W ℝ where
  Γ _ := {0, 1}
  B := Bagg φ c β
  measurable v := (measurable_snd.mul
    ((measurable_subtype_coe.comp measurable_fst).div_const _)).add
    ((measurable_const.sub measurable_snd).mul measurable_const)
  mono w a ha v v' h := by
    have h1 : 0 ≤ 1 - a := by rcases ha with rfl | rfl <;> norm_num
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (cont_mono φ c β hβ h) h1)
  bdd v := by
    obtain ⟨K, hK⟩ := hW
    refine ⟨K / |1 - β| + |cont φ c β v|, fun w a ha => ?_⟩
    rcases ha with rfl | rfl
    · simp only [Bagg, zero_mul, sub_zero, one_mul, zero_add]
      exact le_add_of_nonneg_left (div_nonneg ((abs_nonneg _).trans (hK w w.2)) (abs_nonneg _))
    · simp only [Bagg, one_mul, sub_self, zero_mul, add_zero]
      rw [abs_div]
      exact le_add_of_le_of_nonneg (div_le_div_of_nonneg_right (hK w w.2) (abs_nonneg _))
        (abs_nonneg _)
  exists_policy := ⟨fun _ => 0, measurable_const, fun _ => Or.inl rfl⟩

end BoundedSearch

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuation values and the reservation wage

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.2 (pp. 250–254).

In the iid model, `g(h) = c + β ∫ max{w/(1 − β), h} φ(dw)` (8.14).

* **Exercise 8.1.6**: `g` is a contraction of modulus `β`, via (8.15); its fixed point `h*` is the
  optimal continuation value. **Exercise 8.1.7**: `g` maps `[0, K]` into itself.
* §8.1.2.1: `h* = c + β ∫ v* dφ`, `v* = max{e, h*}`, and the policy (8.12)–(8.13) accepting when
  `w ≥ w* = (1 − β)h*` is optimal.
* §8.1.2.2: `(L¹(φ), F, ℝ, 𝔾)` with `Fv = c + β ∫ v dφ` and `G_σ h = σe + (1 − σ)h` is an
  order-preserving FDP whose primary ADP is the job search ADP and whose subordinate Bellman
  operator is `g`; Theorem 5.2.13 gives the optimality of (8.16) at `h*`.
* §8.1.2.3: Proposition A.5.20 for contractions on `ℝ`; **Example 8.1.1**, **Exercises 8.1.9,
  8.1.10, 8.1.12, 8.1.13**: `h*` and `w*` increase with `c`; `h*` increases with `β`; `w*`
  increases with `β` when `c ≤ w̄`, under first order stochastic dominance and under
  mean-preserving spreads.
* **Exercise 8.1.11**: the mean first passage time to employment increases with `c`, since the
  first passage time is pathwise increasing in `w*`.

Exercise 8.1.8 is computational.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

variable {X : Type*} [MeasurableSpace X]

/-- (8.14): `g(h) = c + β ∫ max{w(x)/(1 − β), h} φ(dx)`. -/
noncomputable def gfun (φ : Measure X) (wage : X → ℝ) (c β h : ℝ) : ℝ :=
  c + β * ∫ x, max (wage x / (1 - β)) h ∂φ

theorem integrable_max_wage {φ : Measure X} [IsFiniteMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (β h : ℝ) : Integrable (fun x => max (wage x / (1 - β)) h) φ :=
  (hi.div_const _).sup (integrable_const h)

/-- **Exercise 8.1.6** (p. 251): by (8.15), `|g(h) − g(h')| ≤ β|h − h'|`. -/
theorem exercise_8_1_6 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (h h' : ℝ) :
    |gfun φ wage c β h - gfun φ wage c β h'| ≤ β * |h - h'| := by
  rw [gfun, gfun, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0,
    ← integral_sub (integrable_max_wage hi β h) (integrable_max_wage hi β h')]
  refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans ?_) hβ0
  calc ∫ x, |max (wage x / (1 - β)) h - max (wage x / (1 - β)) h'| ∂φ
      ≤ ∫ _, |h - h'| ∂φ := integral_mono
        ((integrable_max_wage hi β h).sub (integrable_max_wage hi β h')).abs
        (integrable_const _) fun x => by
          rw [max_comm _ h, max_comm _ h']
          exact abs_max_sub_max_le_abs _ _ _
    _ = |h - h'| := by simp

theorem gfun_contracting {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith ⟨β, hβ0⟩ (gfun φ wage c β) :=
  ⟨hβ1, LipschitzWith.of_dist_le_mul fun h h' => by
    rw [Real.dist_eq, Real.dist_eq]
    exact exercise_8_1_6 hi c hβ0 h h'⟩

theorem gfun_mono {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) : Monotone (gfun φ wage c β) :=
  fun h h' hh => add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (integrable_max_wage hi β h) (integrable_max_wage hi β h') fun _ => max_le_max le_rfl hh) hβ0)

/-- The optimal continuation value `h*`, the unique fixed point of `g`. -/
noncomputable def hstar (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ℝ :=
  ContractingWith.fixedPoint _ (gfun_contracting hi c hβ0 hβ1)

theorem hstar_eq (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    gfun φ wage c β (hstar φ hi c hβ0 hβ1) = hstar φ hi c hβ0 hβ1 :=
  ContractingWith.fixedPoint_isFixedPt _

theorem hstar_unique (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {h : ℝ}
    (hh : gfun φ wage c β h = h) : h = hstar φ hi c hβ0 hβ1 :=
  ContractingWith.fixedPoint_unique _ hh

/-- The reservation wage `w* = (1 − β)h*` (8.13). -/
noncomputable def wstar (φ : Measure X) [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ℝ :=
  (1 - β) * hstar φ hi c hβ0 hβ1

/-- **Exercise 8.1.7** (p. 251): with nonnegative wages and `c ≥ 0`, `g` maps `[0, K]` into
itself, `K = (c + β w̄/(1 − β))/(1 − β)`. -/
theorem exercise_8_1_7 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (hw : ∀ x, 0 ≤ wage x) {c : ℝ} (hc : 0 ≤ c) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    MapsTo (gfun φ wage c β) (Icc 0 ((c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β)))
      (Icc 0 ((c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β))) := by
  intro h hh
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  have hI : ∫ x, wage x / (1 - β) ∂φ = (∫ x, wage x ∂φ) / (1 - β) := integral_div _ _
  have hw0 : 0 ≤ ∫ x, wage x ∂φ := integral_nonneg hw
  have hlow : (∫ x, wage x ∂φ) / (1 - β) ≤ ∫ x, max (wage x / (1 - β)) h ∂φ := by
    rw [← hI]
    exact integral_mono (hi.div_const _) (integrable_max_wage hi β h) fun _ => le_max_left _ _
  have hup : ∫ x, max (wage x / (1 - β)) h ∂φ ≤ (∫ x, wage x ∂φ) / (1 - β) + h := by
    have h1 : ∫ x, max (wage x / (1 - β)) h ∂φ ≤ ∫ x, (wage x / (1 - β) + h) ∂φ :=
      integral_mono (integrable_max_wage hi β h) ((hi.div_const _).add (integrable_const h))
        fun x => max_le (le_add_of_nonneg_right hh.1)
          (le_add_of_nonneg_left (div_nonneg (hw x) hpos.le))
    rw [integral_add (hi.div_const _) (integrable_const h), hI] at h1
    simpa using h1
  constructor
  · exact add_nonneg hc (mul_nonneg hβ0 ((div_nonneg hw0 hpos.le).trans hlow))
  · have hK : (c + β * (∫ x, wage x ∂φ) / (1 - β)) / (1 - β) * (1 - β) =
        c + β * (∫ x, wage x ∂φ) / (1 - β) := div_mul_cancel₀ _ hpos.ne'
    have h2 := mul_le_mul_of_nonneg_left hup hβ0
    have h3 := mul_le_mul_of_nonneg_left hh.2 hβ0
    change c + β * ∫ x, max (wage x / (1 - β)) h ∂φ ≤ _
    have : β * ((∫ x, wage x ∂φ) / (1 - β)) = β * (∫ x, wage x ∂φ) / (1 - β) := by ring
    nlinarith

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

/-- §8.1.2.1 (pp. 250–251): in the iid model, the value function satisfies `v* = max{e, h*}`
almost everywhere with `h* = c + β ∫ v* dφ` the fixed point of `g`, and the policy (8.12)
accepting when `w/(1 − β) ≥ h*`, i.e. `w ≥ w* = (1 − β)h*` (8.13), is optimal. -/
theorem section_8_1_2_1 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ hw : (iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed, ∃ vstar,
      (iid φ wage hm hi c β hβ0 hβ1).adp.IsValueFunction vstar ∧
      hstar φ hi c hβ0 hβ1 = c + β * ∫ x, vstar x ∂φ ∧
      ⇑vstar =ᵐ[φ] (fun x => max (wage x / (1 - β)) (hstar φ hi c hβ0 hβ1)) ∧
      (iid φ wage hm hi c β hβ0 hβ1).adp.IsOptimal hw
        (acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => hstar φ hi c hβ0 hβ1)
          (hm.div_const _) measurable_const) := by
  set M := iid φ wage hm hi c β hβ0 hβ1
  obtain ⟨hw, hFO, -⟩ := proposition_8_1_1 φ wage hm hi c β hβ0 hβ1
  obtain ⟨vstar, -, hv, -, hvG, hb⟩ := hFO.exists_vstar
  have hbell : M.adp.bellman vstar = vstar := (M.adp.solvesBellman_iff hvG).1 hb
  have hT := (exercise_8_1_2_3 φ wage hm hi c β hβ0 hβ1 vstar).2
  rw [hbell] at hT
  -- `h₀ = c + β ∫ v*` is a fixed point of `g`
  set h₀ := c + β * ∫ x, vstar x ∂φ
  have hfix : gfun φ wage c β h₀ = h₀ := by
    change c + β * ∫ x, max (wage x / (1 - β)) h₀ ∂φ = c + β * ∫ x, vstar x ∂φ
    rw [integral_congr_ae hT.symm]
  have hh₀ : h₀ = hstar φ hi c hβ0 hβ1 := hstar_unique φ hi c hβ0 hβ1 hfix
  refine ⟨hw, vstar, hv, hh₀.symm, ?_, ?_⟩
  · rw [← hh₀]
    exact hT
  · -- the policy (8.12) is `v*`-greedy, hence optimal
    set σ := acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => hstar φ hi c hβ0 hβ1)
      (hm.div_const _) measurable_const
    have hTσ : M.adp.T σ vstar = M.adp.bellman vstar := by
      refine Lp.ext ?_
      filter_upwards [M.T_coeFn σ vstar, iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 vstar,
        (exercise_8_1_2_3 φ wage hm hi c β hβ0 hβ1 vstar).2] with x h1 h2 h3
      rw [h1, h2, h3]
      have h4 := acceptWhere_apply (s := fun x => wage x / (1 - β))
        (h := fun _ => hstar φ hi c hβ0 hβ1) (hm.div_const _) measurable_const x
      have e : c + β * ∫ y, vstar y ∂φ = hstar φ hi c hβ0 hβ1 := hh₀
      change (if σ.1 x then wage x / (1 - β) else c + β * ∫ y, vstar y ∂φ) = _
      rw [e]
      exact h4
    exact (hFO.2.2 σ).2 ⟨vstar, hv, ((M.adp.isGreedy_iff hvG σ).2 hTσ)⟩

end JobSearch

/-! ### The FDP perspective -/

namespace JobSearchFDP


/-- `e = w/(1 − β)` in `L¹(φ)`. -/
noncomputable def eL (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) : Lp ℝ 1 φ :=
  (memLp_one_iff_integrable.2 (hi.div_const (1 - β))).toLp fun x => wage x / (1 - β)

/-- `G_σ h = σe + (1 − σ)h`. -/
noncomputable def G (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) (σ : StopPolicy X) (h : ℝ) : Lp ℝ 1 φ :=
  L1.mulCLM φ (measurable_polInd σ) (abs_polInd_le σ) (eL φ wage hi β) +
    L1.mulCLM φ (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _)

theorem G_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hi : Integrable wage φ) (β : ℝ) (σ : StopPolicy X) (h : ℝ) :
    ⇑(G φ wage hi β σ h) =ᵐ[φ]
      fun x => if σ.1 x then wage x / (1 - β) else h := by
  filter_upwards [Lp.coeFn_add (L1.mulCLM φ (measurable_polInd σ) (abs_polInd_le σ)
      (eL φ wage hi β))
      (L1.mulCLM φ (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _)),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (eL φ wage hi β),
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) ((memLp_const h).toLp _),
    (memLp_one_iff_integrable.2 (hi.div_const (1 - β))).coeFn_toLp,
    (memLp_const (μ := φ) h).coeFn_toLp]
    with x h1 h2 h3 h4 h5
  rw [G, h1, Pi.add_apply, h2, h3]
  change polInd σ x * (eL φ wage hi β) x + polCont σ x * ((memLp_const h).toLp _) x = _
  rw [eL, h4, h5]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- The order-preserving FDP `(L¹(φ), F, ℝ, 𝔾)` of §8.1.2.2, `Fv = c + β ∫ v dφ`. -/
noncomputable def fdp (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) :
    FDP (Lp ℝ 1 φ) ℝ (StopPolicy X) where
  F v := c + β * ∫ x, v x ∂φ
  G := G φ wage hi β
  greatest h := ⟨acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => h)
    (hm.div_const _) measurable_const, fun τ => by
    rw [← Lp.coeFn_le]
    filter_upwards [G_coeFn φ wage hi β τ h, G_coeFn φ wage hi β _ h]
      with x h1 h2
    rw [h1, h2, acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _⟩
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem isOrderPreserving (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) :
    (fdp φ wage hm hi c β).IsOrderPreserving := by
  refine ⟨fun v w hvw => add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono_ae (L1.integrable_coeFn v) (L1.integrable_coeFn w)
      ((Lp.coeFn_le _ _).2 hvw)) hβ0), fun σ h h' hh => ?_⟩
  rw [← Lp.coeFn_le]
  filter_upwards [G_coeFn φ wage hi β σ h, G_coeFn φ wage hi β σ h']
    with x h1 h2
  change (G φ wage hi β σ h) x ≤ (G φ wage hi β σ h') x
  rw [h1, h2]
  split_ifs
  · exact le_rfl
  · exact hh

/-- `Gh = max{e, h}` almost everywhere. -/
theorem Gsup_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β h : ℝ) :
    ⇑((fdp φ wage hm hi c β).Gsup h) =ᵐ[φ] fun x => max (wage x / (1 - β)) h := by
  set σ := acceptWhere (s := fun x => wage x / (1 - β)) (h := fun _ => h)
    (hm.div_const _) measurable_const
  have hσ : (fdp φ wage hm hi c β).Gsup h = G φ wage hi β σ h := by
    refine le_antisymm ?_ ((fdp φ wage hm hi c β).G_le_Gsup σ h)
    have hg := (fdp φ wage hm hi c β).isGreatest_Gsup h
    obtain ⟨⟨τ, hτ⟩, -⟩ := hg
    rw [← hτ]
    rw [← Lp.coeFn_le]
    filter_upwards [G_coeFn φ wage hi β τ h, G_coeFn φ wage hi β σ h]
      with x h1 h2
    change (G φ wage hi β τ h) x ≤ (G φ wage hi β σ h) x
    rw [h1, h2, acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [hσ]
  filter_upwards [G_coeFn φ wage hi β σ h] with x hx
  rw [hx, acceptWhere_apply]

theorem ADP.ext_T {V P : Type*} [PartialOrder V] {A B : ADP V P} (h : A.T = B.T) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- §8.1.2.2 (pp. 252–253): the FDP `(L¹(φ), F, ℝ, 𝔾)` is order preserving, (i) its primary ADP
is the job search ADP `(L¹(φ), 𝕋)`, (ii) the Bellman operator of its subordinate ADP is `g` of
(8.14), (iii) by Theorem 5.2.13 the subordinate ADP has the fundamental optimality properties
with value function `h*`, and every `σ` with `G_σ h* = Gh*`, such as (8.16) at `h*`, is optimal
for the job search problem. -/
theorem section_8_1_2_2 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (fdp φ wage hm hi c β).primary (Or.inl (isOrderPreserving φ wage hm hi c hβ0)) =
        (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp ∧
      (∀ h, ((fdp φ wage hm hi c β).sub
        (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).bellman h =
          gfun φ wage c β h) ∧
      ∃ hw' : ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).WellPosed,
        ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).FundamentalOptimality hw' ∧
        ((fdp φ wage hm hi c β).sub
          (Or.inl (isOrderPreserving φ wage hm hi c hβ0))).IsValueFunction
            (hstar φ hi c hβ0 hβ1) ∧
        ∀ hw : (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed, ∀ σ,
          G φ wage hi β σ (hstar φ hi c hβ0 hβ1) =
              (fdp φ wage hm hi c β).Gsup (hstar φ hi c hβ0 hβ1) →
            (JobSearch.iid φ wage hm hi c β hβ0 hβ1).adp.IsOptimal hw σ := by
  set M := JobSearch.iid φ wage hm hi c β hβ0 hβ1
  set D := fdp φ wage hm hi c β
  have hP := isOrderPreserving φ wage hm hi c hβ0
  have hprim : D.primary (Or.inl hP) = M.adp := by
    refine ADP.ext_T (funext fun σ => funext fun v => Lp.ext ?_)
    filter_upwards [G_coeFn φ wage hi β σ (c + β * ∫ x, v x ∂φ), M.T_coeFn σ v,
      JobSearch.iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 v] with x h1 h2 h3
    change (G φ wage hi β σ (c + β * ∫ x, v x ∂φ)) x = _
    rw [h1, h2, h3]
    rfl
  have hsubT : ∀ h, (D.sub (Or.inl hP)).bellman h = gfun φ wage c β h := fun h => by
    rw [(FDP.lemma_5_2_10 (Or.inl hP) hP).1]
    change c + β * ∫ x, (D.Gsup h) x ∂φ = c + β * ∫ x, max (wage x / (1 - β)) h ∂φ
    rw [integral_congr_ae (Gsup_coeFn φ wage hm hi c β h)]
  obtain ⟨hw, hFO, -⟩ := JobSearch.proposition_8_1_1 φ wage hm hi c β hβ0 hβ1
  have hwP : (D.primary (Or.inl hP)).WellPosed := by rw [hprim]; exact hw
  have hw' : (D.sub (Or.inl hP)).WellPosed := ((FDP.lemma_5_2_12 (Or.inl hP)).1).2 hwP
  have hFOP : (D.primary (Or.inl hP)).FundamentalOptimality hwP := by
    revert hwP
    rw [hprim]
    intro hwP
    exact hFO
  have h513 := FDP.theorem_5_2_13 (Or.inl hP) hP hwP hw'
  have hFO' := h513.1.1 hFOP
  -- the subordinate value function solves `g w = w`, so it is `h*`
  obtain ⟨w, hwv, hwG, hwb, -⟩ := hFO'.2.1
  have hwfix : gfun φ wage c β w = w := by
    rw [← hsubT]
    exact ((D.sub (Or.inl hP)).solvesBellman_iff hwG).1 hwb
  have hwh : w = hstar φ hi c hβ0 hβ1 := hstar_unique φ hi c hβ0 hβ1 hwfix
  rw [hwh] at hwv
  refine ⟨hprim, hsubT, hw', hFO', hwv, fun hw₀ σ hσ => ?_⟩
  have hopt := (h513.2 hFOP).2.1 _ σ hwv hσ
  revert hopt
  have : ∀ (A : ADP (Lp ℝ 1 φ) (StopPolicy X)) (h₁ : A.WellPosed) (h₂ : M.adp.WellPosed),
      A = M.adp → A.IsOptimal h₁ σ → M.adp.IsOptimal h₂ σ := by
    rintro A h₁ h₂ rfl hA
    exact hA
  exact this _ hwP hw₀ hprim

end JobSearchFDP

/-! ### Parametric monotonicity -/

/-- **Proposition A.5.20** (p. 380) for contractions: if `g₂` is an increasing contraction of a
complete space with a closed order, `g₁ ≤ g₂` pointwise and `g₁ h₁ = h₁`, then `h₁` lies below the
fixed point of `g₂`. -/
theorem fixedPoint_ge_of_le {V : Type*} [MetricSpace V] [CompleteSpace V] [Nonempty V]
    [PartialOrder V] [OrderClosedTopology V] {g₁ g₂ : V → V} {K : NNReal}
    (hg₂ : ContractingWith K g₂)
    (hmono : Monotone g₂) (hle : ∀ h, g₁ h ≤ g₂ h) {h₁ : V} (hh₁ : g₁ h₁ = h₁) :
    h₁ ≤ ContractingWith.fixedPoint g₂ hg₂ := by
  have hiter : ∀ n, h₁ ≤ g₂^[n] h₁ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc h₁ = g₁ h₁ := hh₁.symm
        _ ≤ g₂ h₁ := hle h₁
        _ ≤ g₂ (g₂^[n] h₁) := hmono ih
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint hg₂ h₁) hiter

/-- **Example 8.1.1** (p. 253) and **Exercise 8.1.9**, first part (p. 254): `h*` and the
reservation wage `w*` are increasing in unemployment compensation `c`. -/
theorem example_8_1_1 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    hstar φ hi c₁ hβ0 hβ1 ≤ hstar φ hi c₂ hβ0 hβ1 ∧
      wstar φ hi c₁ hβ0 hβ1 ≤ wstar φ hi c₂ hβ0 hβ1 := by
  have h := fixedPoint_ge_of_le (gfun_contracting hi c₂ hβ0 hβ1) (gfun_mono hi c₂ hβ0)
    (fun h => add_le_add hc le_rfl) (hstar_eq φ hi c₁ hβ0 hβ1)
  exact ⟨h, mul_le_mul_of_nonneg_left h (sub_nonneg.2 hβ1.le)⟩

/-- **Exercise 8.1.9**, second part (p. 254): with nonnegative wages, `h*` is increasing in
`β`. -/
theorem exercise_8_1_9 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (hw : ∀ x, 0 ≤ wage x) (c : ℝ) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁)
    (h12 : β₁ ≤ β₂) (h1 : β₂ < 1) :
    hstar φ hi c h0 (h12.trans_lt h1) ≤ hstar φ hi c (h0.trans h12) h1 := by
  refine fixedPoint_ge_of_le (gfun_contracting hi c (h0.trans h12) h1)
    (gfun_mono hi c (h0.trans h12)) (fun h => ?_) (hstar_eq φ hi c h0 (h12.trans_lt h1))
  have hp1 : 0 < 1 - β₁ := sub_pos.2 (h12.trans_lt h1)
  have hp2 : 0 < 1 - β₂ := sub_pos.2 h1
  have hint : ∀ x, max (wage x / (1 - β₁)) h ≤ max (wage x / (1 - β₂)) h := fun x =>
    max_le_max (div_le_div_of_nonneg_left (hw x) hp2 (by linarith)) le_rfl
  have hI0 : 0 ≤ ∫ x, max (wage x / (1 - β₁)) h ∂φ :=
    (integral_nonneg fun x => div_nonneg (hw x) hp1.le).trans
      (integral_mono (hi.div_const _) (integrable_max_wage hi β₁ h) fun _ => le_max_left _ _)
  have hmono := integral_mono (integrable_max_wage hi β₁ h) (integrable_max_wage hi β₂ h) hint
  change c + β₁ * ∫ x, max (wage x / (1 - β₁)) h ∂φ ≤ c + β₂ * ∫ x, max (wage x / (1 - β₂)) h ∂φ
  nlinarith

/-- (8.17): `f(w) = c(1 − β) + β ∫ max{w', w} φ(dw')`. -/
noncomputable def ffun (φ : Measure X) (wage : X → ℝ) (c β w : ℝ) : ℝ :=
  c * (1 - β) + β * ∫ x, max (wage x) w ∂φ

theorem ffun_contracting {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith ⟨β, hβ0⟩ (ffun φ wage c β) := by
  have hI : ∀ w, Integrable (fun x => max (wage x) w) φ := fun w => hi.sup (integrable_const w)
  refine ⟨hβ1, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, ffun, ffun, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg hβ0, ← integral_sub (hI w) (hI w')]
  refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans ?_) hβ0
  calc ∫ x, |max (wage x) w - max (wage x) w'| ∂φ
      ≤ ∫ _, |w - w'| ∂φ := integral_mono
        ((hI w).sub (hI w')).abs
        (integrable_const _) fun x => by
          rw [max_comm _ w, max_comm _ w']
          exact abs_max_sub_max_le_abs _ _ _
    _ = |w - w'| := by simp

theorem ffun_mono {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) : Monotone (ffun φ wage c β) :=
  fun w w' hww => add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono
    (hi.sup (integrable_const w)) (hi.sup (integrable_const w')) fun _ =>
      max_le_max le_rfl hww) hβ0)

/-- The reservation wage is the fixed point of `f` in (8.17). -/
theorem wstar_eq_fixedPoint {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    wstar φ hi c hβ0 hβ1 = ContractingWith.fixedPoint _ (ffun_contracting hi c hβ0 hβ1) := by
  refine ContractingWith.fixedPoint_unique _ ?_
  have hpos : 0 < 1 - β := sub_pos.2 hβ1
  have hg := hstar_eq φ hi c hβ0 hβ1
  change c * (1 - β) + β * ∫ x, max (wage x) ((1 - β) * hstar φ hi c hβ0 hβ1) ∂φ =
    (1 - β) * hstar φ hi c hβ0 hβ1
  have hmax : ∀ x, max (wage x) ((1 - β) * hstar φ hi c hβ0 hβ1) =
      (1 - β) * max (wage x / (1 - β)) (hstar φ hi c hβ0 hβ1) := fun x => by
    rw [mul_max_of_nonneg _ _ hpos.le, mul_div_cancel₀ _ hpos.ne']
  simp_rw [hmax]
  rw [integral_const_mul]
  conv_rhs => rw [← hg]
  rw [gfun]
  ring

/-- **Exercise 8.1.10** (p. 254): if `c ≤ w̄ = ∫ w φ(dw)`, the reservation wage is increasing in
`β`. -/
theorem exercise_8_1_10 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {c : ℝ} (hc : c ≤ ∫ x, wage x ∂φ) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁)
    (h12 : β₁ ≤ β₂) (h1 : β₂ < 1) :
    wstar φ hi c h0 (h12.trans_lt h1) ≤ wstar φ hi c (h0.trans h12) h1 := by
  rw [wstar_eq_fixedPoint hi c (h0.trans h12) h1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ wage c β₁) (ffun_contracting hi c (h0.trans h12) h1)
    (ffun_mono hi c (h0.trans h12)) (fun w => ?_) ?_
  · have hI : c ≤ ∫ x, max (wage x) w ∂φ :=
      hc.trans (integral_mono hi (hi.sup (integrable_const w)) fun _ => le_max_left _ _)
    change c * (1 - β₁) + β₁ * ∫ x, max (wage x) w ∂φ ≤ c * (1 - β₂) + β₂ * ∫ x, max (wage x) w ∂φ
    nlinarith
  · rw [wstar_eq_fixedPoint hi c h0 (h12.trans_lt h1)]
    exact ContractingWith.fixedPoint_isFixedPt _

/-- First order stochastic dominance `φ ⪯_F ψ` (§A.5.5): `∫ u dφ ≤ ∫ u dψ` for every bounded,
increasing, measurable `u`. -/
def FOSDle (φ ψ : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → Measurable u → (∃ C, ∀ x, |u x| ≤ C) → ∫ x, u x ∂φ ≤ ∫ x, u x ∂ψ

/-- **Exercise 8.1.12** (p. 254): if `ψ` first order stochastically dominates `φ` and both are
supported on `[0, M]`, then `w*_φ ≤ w*_ψ`. -/
theorem exercise_8_1_12 {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ) {M : ℝ} (hφM : ∀ᵐ x ∂φ, x ∈ Icc 0 M)
    (hψM : ∀ᵐ x ∂ψ, x ∈ Icc 0 M) (hFOSD : FOSDle φ ψ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : wstar φ hiφ c hβ0 hβ1 ≤ wstar ψ hiψ c hβ0 hβ1 := by
  rw [wstar_eq_fixedPoint hiψ c hβ0 hβ1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ id c β) (ffun_contracting hiψ c hβ0 hβ1)
    (ffun_mono hiψ c hβ0) (fun w => ?_) ?_
  · -- clamp to `[0, M]`: a bounded increasing function equal to `max(·, w)` on the supports
    let u : ℝ → ℝ := fun x => max (max 0 (min x M)) w
    have hu : Monotone u := fun x y h => max_le_max (max_le_max le_rfl (min_le_min h le_rfl)) le_rfl
    have hum : Measurable u := (measurable_const.max (measurable_id.min measurable_const)).max
      measurable_const
    have hub : ∃ C, ∀ x, |u x| ≤ C := ⟨|M| + |w|, fun x => by
      simp only [u]
      rw [abs_le]
      constructor
      · have := le_max_right (max 0 (min x M)) w
        linarith [neg_abs_le w, abs_nonneg M]
      · refine max_le ?_ ?_
        · refine max_le (by positivity) ((min_le_right _ _).trans ?_)
          linarith [le_abs_self M, abs_nonneg w]
        · linarith [le_abs_self w, abs_nonneg M]⟩
    have heq : ∀ μ : Measure ℝ, (∀ᵐ x ∂μ, x ∈ Icc 0 M) →
        ∫ x, max (id x) w ∂μ = ∫ x, u x ∂μ := fun μ hμ => integral_congr_ae (by
      filter_upwards [hμ] with x hx
      simp only [id, u, min_eq_left hx.2, max_eq_right hx.1])
    change c * (1 - β) + β * ∫ x, max (id x) w ∂φ ≤ c * (1 - β) + β * ∫ x, max (id x) w ∂ψ
    rw [heq φ hφM, heq ψ hψM]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hFOSD u hu hum hub) hβ0)
  · rw [wstar_eq_fixedPoint hiφ c hβ0 hβ1]
    exact ContractingWith.fixedPoint_isFixedPt _

/-- `ψ` is a mean-preserving spread of `φ` (p. 391): there are random variables `W` and `Z` on a
probability space with `W ∼ φ`, `W + Z ∼ ψ` and `𝔼[Z | W] = 0`. -/
def IsMPS (ψ φ : Measure ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (W Z : Ω → ℝ), Measurable W ∧ Measurable Z ∧ Integrable W P ∧ Integrable Z P ∧
      P.map W = φ ∧ P.map (W + Z) = ψ ∧
      P[Z | MeasurableSpace.comap W inferInstance] =ᵐ[P] 0

/-- (8.18), by conditional expectations: if `ψ` is a mean-preserving spread of `φ`, then
`∫ max{w', w} φ(dw') ≤ ∫ max{w', w} ψ(dw')`. -/
theorem integral_max_le_of_isMPS {ψ φ : Measure ℝ} (h : IsMPS ψ φ) (w : ℝ) :
    ∫ x, max x w ∂φ ≤ ∫ x, max x w ∂ψ := by
  obtain ⟨Ω, mΩ, P, _, W, Z, hWm, hZm, hWi, hZi, hW, hWZ, hZ⟩ := h
  have hm : MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ) ≤ mΩ := hWm.comap_le
  have hmeas : Measurable fun x : ℝ => max x w := measurable_id.max measurable_const
  rw [← hW, ← hWZ, integral_map hWm.aemeasurable hmeas.aestronglyMeasurable,
    integral_map (hWm.add hZm).aemeasurable hmeas.aestronglyMeasurable]
  have hY : Integrable (fun ω => max ((W + Z) ω) w) P := (hWi.add hZi).sup (integrable_const w)
  -- `𝔼[max(W + Z, w) | W] ≥ max(W, w)`
  have hWst : StronglyMeasurable[MeasurableSpace.comap W (inferInstance : MeasurableSpace ℝ)] W :=
    (comap_measurable W).stronglyMeasurable
  have h1 : P[W + Z | MeasurableSpace.comap W inferInstance] =ᵐ[P] W := by
    filter_upwards [condExp_add hWi hZi (MeasurableSpace.comap W inferInstance), hZ]
      with ω h1 h2
    rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable hm hWst hWi, h2]
    simp
  have h2 : P[W + Z | MeasurableSpace.comap W inferInstance] ≤ᵐ[P]
      P[fun ω => max ((W + Z) ω) w | MeasurableSpace.comap W inferInstance] :=
    condExp_mono (hWi.add hZi) hY (Eventually.of_forall fun ω => le_max_left _ _)
  have h3 : P[fun _ => w | MeasurableSpace.comap W inferInstance] ≤ᵐ[P]
      P[fun ω => max ((W + Z) ω) w | MeasurableSpace.comap W inferInstance] :=
    condExp_mono (integrable_const w) hY (Eventually.of_forall fun ω => le_max_right _ _)
  rw [condExp_const hm] at h3
  rw [← integral_condExp hm (μ := P) (f := fun ω => max ((W + Z) ω) w)]
  refine integral_mono_ae (hWi.sup (integrable_const w)) integrable_condExp ?_
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1] at e2
  exact max_le e2 e3

/-- **Exercise 8.1.13** (p. 254): if `ψ` is a mean-preserving spread of `φ`, then
`w*_φ ≤ w*_ψ`. -/
theorem exercise_8_1_13 {φ ψ : Measure ℝ} [IsProbabilityMeasure φ] [IsProbabilityMeasure ψ]
    (hiφ : Integrable id φ) (hiψ : Integrable id ψ) (hMPS : IsMPS ψ φ) (c : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) : wstar φ hiφ c hβ0 hβ1 ≤ wstar ψ hiψ c hβ0 hβ1 := by
  rw [wstar_eq_fixedPoint hiψ c hβ0 hβ1]
  refine fixedPoint_ge_of_le (g₁ := ffun φ id c β) (ffun_contracting hiψ c hβ0 hβ1)
    (ffun_mono hiψ c hβ0) (fun w => add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_max_le_of_isMPS hMPS w) hβ0)) ?_
  rw [wstar_eq_fixedPoint hiφ c hβ0 hβ1]
  exact ContractingWith.fixedPoint_isFixedPt _

/-- The optimal policy (8.16) accepts exactly the offers `w ≥ w* = (1 − β)h*`. -/
theorem accept_iff {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) (c : ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x : X) :
    hstar φ hi c hβ0 hβ1 ≤ wage x / (1 - β) ↔ wstar φ hi c hβ0 hβ1 ≤ wage x := by
  rw [wstar, le_div_iff₀ (sub_pos.2 hβ1), mul_comm]

/-- The first passage time to employment `τ = inf{t ≥ 0 : σ*(W_t) = 1}` along an offer path `ω`,
when `σ*` accepts the offers `w(x) ≥ w*` (`⊤` if no offer is accepted). -/
noncomputable def firstPassage (wage : X → ℝ) (w : ℝ) (ω : ℕ → X) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : w ≤ wage (ω t)), (t : ℕ∞)

omit [MeasurableSpace X] in
theorem firstPassage_mono (wage : X → ℝ) {w₁ w₂ : ℝ} (h : w₁ ≤ w₂) (ω : ℕ → X) :
    firstPassage wage w₁ ω ≤ firstPassage wage w₂ ω :=
  iInf₂_mono' fun t ht => ⟨t, h.trans ht, le_rfl⟩

/-- **Exercise 8.1.11** (p. 254): with iid offers `W_t = w(ξ_t)`, `ξ_t ~ φ`, the mean first
passage time to employment `𝔼τ` is increasing in unemployment compensation `c`: `w*` increases
with `c` (Exercise 8.1.9), so `τ` does along every path. -/
theorem exercise_8_1_11 {φ : Measure X} [IsProbabilityMeasure φ] {wage : X → ℝ}
    (hi : Integrable wage φ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    ∫⁻ ω, (firstPassage wage (wstar φ hi c₁ hβ0 hβ1) ω : ENNReal)
        ∂(Measure.infinitePi fun _ : ℕ => φ) ≤
      ∫⁻ ω, (firstPassage wage (wstar φ hi c₂ hβ0 hβ1) ω : ENNReal)
        ∂(Measure.infinitePi fun _ : ℕ => φ) :=
  lintegral_mono fun ω =>
    ENat.toENNReal_mono (firstPassage_mono wage (example_8_1_1 hi hβ0 hβ1 hc).2 ω)

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Persistent and transient wage components

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.3.3 (pp. 257–261).

The persistent state `z` is `P`-Markov on `Z` with stationary distribution `φ`; next period's
offer is `w' = ω(z', ζ')` with `ζ'` drawn iid from `ν`, independent of everything else. The book's
(8.23) is the case `Z = ℝ`, `Z_{t+1} = ρZ_t + d + sε_{t+1}`, `ζ ∼ N(0, 1)` and
`ω(z, ζ) = exp(z) + exp(μ + σζ)`. Continuation values `h ∈ L¹(φ)` satisfy (8.26), and policies
`σ(w', z')` act through

`(T̂_σ h)(z) = c + β 𝔼_z{σ(w', z') w'/(1 − β) + (1 − σ(w', z'))h(z')}` (8.28),

which is `T̂_σ h = c + βP(Φ_σ h)` with `(Φ_σ h)(z') = ∫ [σ e + (1 − σ)h(z')] ν(dζ')`. It is affine,
`T̂_σ h = m_σ + K_σ h` with `0 ≤ K_σ ≤ K = βP`.

* **Exercise 8.1.21**: the policy `σ(w', z') = 𝟙{w'/(1 − β) ≥ h(z')}` is `h`-greedy; hence, by
  Theorem 4.1.8, the fundamental optimality properties hold and VFI, OPI and HPI converge.
* **Exercise 8.1.22**: the Bellman operator is (8.29),
  `(T̂h)(z) = c + β 𝔼_z max{w'/(1 − β), h(z')}`.
* **Exercise 8.1.23**: `T̂` is a contraction of modulus `β` on `L¹(φ)`.
* **Exercise 8.1.24**: the fixed point `h*` is increasing in `c` (almost everywhere).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

/-- The job search model with persistent and transient wage components. -/
structure PersistentSearch (Z Ξ : Type*) [MeasurableSpace Z] [MeasurableSpace Ξ] where
  /-- the kernel of the persistent state -/
  P : Kernel Z Z
  [isMarkov : IsMarkovKernel P]
  /-- a stationary distribution of `P` -/
  φ : Measure Z
  [isProb : IsProbabilityMeasure φ]
  stationary : φ.bind P = φ
  /-- the distribution of the transient shock -/
  ν : Measure Ξ
  [isProbν : IsProbabilityMeasure ν]
  /-- the offer `w' = ω(z', ζ')` -/
  ω : Z → Ξ → ℝ
  measurable_ω : Measurable (uncurry ω)
  integrable_ω : Integrable (uncurry ω) (φ.prod ν)
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace PersistentSearch

attribute [local instance] PersistentSearch.isMarkov PersistentSearch.isProb
  PersistentSearch.isProbν

variable {Z Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ] (M : PersistentSearch Z Ξ)

/-- The stopping value `e(z', ζ') = ω(z', ζ')/(1 − β)`. -/
noncomputable def e (z : Z) (ζ : Ξ) : ℝ := M.ω z ζ / (1 - M.β)

theorem measurable_e : Measurable (uncurry M.e) := M.measurable_ω.div_const _

theorem integrable_e : Integrable (uncurry M.e) (M.φ.prod M.ν) := M.integrable_ω.div_const _

theorem ae_integrable_e : ∀ᵐ z ∂M.φ, Integrable (M.e z) M.ν := M.integrable_e.prod_right_ae

theorem integrable_absInt : Integrable (fun z => ∫ ζ, |M.e z ζ| ∂M.ν) M.φ := by
  have := M.integrable_e.norm.integral_prod_left
  simpa [Real.norm_eq_abs] using this

/-- The Markov operator `P` on `L¹(φ)`. -/
noncomputable def Pop : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := L1.markovCLM M.stationary

/-- The constant `c` in `L¹(φ)`. -/
noncomputable def cconst : Lp ℝ 1 M.φ := (memLp_const M.c).toLp _

theorem measurable_pair (σ : StopPolicy (ℝ × Z)) :
    Measurable fun p : Z × Ξ => σ.1 (M.ω p.1 p.2, p.1) :=
  σ.2.comp (M.measurable_ω.prodMk measurable_fst)

/-- `z' ↦ ∫ σ(w', z') e ν(dζ')`. -/
noncomputable def accF (σ : StopPolicy (ℝ × Z)) (z : Z) : ℝ :=
  ∫ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) ∂M.ν

/-- `q_σ(z') = ν{ζ' : σ(w', z') = 0}`, as `∫ (1 − σ) dν`. -/
noncomputable def qF (σ : StopPolicy (ℝ × Z)) (z : Z) : ℝ :=
  ∫ ζ, (if σ.1 (M.ω z ζ, z) then 0 else 1) ∂M.ν

theorem measurable_accF (σ : StopPolicy (ℝ × Z)) : Measurable (M.accF σ) := by
  have hm : Measurable fun p : Z × Ξ => if σ.1 (M.ω p.1 p.2, p.1) then M.e p.1 p.2 else 0 :=
    Measurable.ite ((M.measurable_pair σ) (measurableSet_singleton true)) M.measurable_e
      measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem measurable_qF (σ : StopPolicy (ℝ × Z)) : Measurable (M.qF σ) := by
  have hm : Measurable fun p : Z × Ξ => if σ.1 (M.ω p.1 p.2, p.1) then (0 : ℝ) else 1 :=
    Measurable.ite ((M.measurable_pair σ) (measurableSet_singleton true)) measurable_const
      measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem qF_nonneg (σ : StopPolicy (ℝ × Z)) (z : Z) : 0 ≤ M.qF σ z :=
  integral_nonneg fun ζ => by dsimp only; split_ifs <;> norm_num

theorem qF_le_one (σ : StopPolicy (ℝ × Z)) (z : Z) : M.qF σ z ≤ 1 := by
  calc M.qF σ z ≤ ∫ _, (1 : ℝ) ∂M.ν := integral_mono_of_nonneg
        (Eventually.of_forall fun ζ => by dsimp only; split_ifs <;> norm_num) (integrable_const _)
        (Eventually.of_forall fun ζ => by dsimp only; split_ifs <;> norm_num)
    _ = 1 := by simp

theorem abs_qF_le (σ : StopPolicy (ℝ × Z)) (z : Z) : |M.qF σ z| ≤ 1 := by
  rw [abs_of_nonneg (M.qF_nonneg σ z)]
  exact M.qF_le_one σ z

theorem ae_abs_accF_le (σ : StopPolicy (ℝ × Z)) :
    ∀ᵐ z ∂M.φ, |M.accF σ z| ≤ ∫ ζ, |M.e z ζ| ∂M.ν := by
  filter_upwards [M.ae_integrable_e] with z hi
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) hi.abs (Eventually.of_forall fun ζ => ?_))
  dsimp only
  split_ifs
  · exact le_rfl
  · simp

theorem integrable_accF (σ : StopPolicy (ℝ × Z)) : Integrable (M.accF σ) M.φ :=
  M.integrable_absInt.mono' (M.measurable_accF σ).aestronglyMeasurable
    (by filter_upwards [M.ae_abs_accF_le σ] with z hz; rw [Real.norm_eq_abs]; exact hz)

/-- `accF σ` in `L¹(φ)`. -/
noncomputable def accL (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ := (M.integrable_accF σ).toL1 _

/-- `Φ_σ h = ∫ [σe + (1 − σ)h(z')] ν(dζ')`. -/
noncomputable def Φσ (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ :=
  M.accL σ + L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h

/-- `m_σ = c + βP(accF σ)`. -/
noncomputable def mσ (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ := M.cconst + M.β • M.Pop (M.accL σ)

/-- `K_σ h = βP((1 − σ)h)`. -/
noncomputable def Kσ (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ :=
  M.β • (M.Pop.comp (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ)))

/-- `K = βP`. -/
noncomputable def D : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := M.β • M.Pop

theorem smul_isPositive {A : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ} (hA : BanachLattice.IsPositiveOp A) :
    BanachLattice.IsPositiveOp (M.β • A) := fun v hv => by
  have h := hA v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul M.β (A v), h] with x h1 h2
  change 0 ≤ (M.β • A v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg M.β_nonneg h2

theorem smul_le_smul' {a b : Lp ℝ 1 M.φ} (h : a ≤ b) : M.β • a ≤ M.β • b := by
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.coeFn_smul M.β a, Lp.coeFn_smul M.β b, (Lp.coeFn_le _ _).2 h]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left h3 M.β_nonneg

theorem D_isPositive : BanachLattice.IsPositiveOp M.D :=
  M.smul_isPositive (L1.markovCLM_isPositive M.stationary)

theorem Kσ_isPositive (σ : StopPolicy (ℝ × Z)) : BanachLattice.IsPositiveOp (M.Kσ σ) :=
  M.smul_isPositive fun v hv => L1.markovCLM_isPositive M.stationary _
    (L1.mulCLM_isPositive (M.measurable_qF σ) (M.abs_qF_le σ) (M.qF_nonneg σ) v hv)

theorem Kσ_le_D (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) (hh : 0 ≤ h) : M.Kσ σ h ≤ M.D h := by
  change M.β • M.Pop (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h) ≤ M.β • M.Pop h
  exact M.smul_le_smul' ((L1.markovCLM_isPositive M.stationary).mono
    (L1.mulCLM_le_self (M.measurable_qF σ) (M.abs_qF_le σ) (M.qF_le_one σ) hh))

theorem norm_D_le : ‖M.D‖ ≤ M.β :=
  ContinuousLinearMap.opNorm_le_bound _ M.β_nonneg fun v => by
    change ‖M.β • M.Pop v‖ ≤ M.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((M.Pop.le_opNorm v).trans ?_) M.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)

theorem specRad_D_lt_one : BanachLattice.specRad M.D < 1 :=
  ((BanachLattice.specRad_le_norm _).trans M.norm_D_le).trans_lt M.β_lt_one

/-- The continuation value ADP `(L¹(φ), 𝕋̂)` of (8.28). -/
noncomputable def adp : ADP (Lp ℝ 1 M.φ) (StopPolicy (ℝ × Z)) where
  T σ h := M.mσ σ + M.Kσ σ h
  mono σ _ _ h := add_le_add le_rfl ((M.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (8.28): `T̂_σ h = c + βP(Φ_σ h)`. -/
theorem T_eq (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) :
    M.adp.T σ h = M.cconst + M.β • M.Pop (M.Φσ σ h) := by
  change M.cconst + M.β • M.Pop (M.accL σ) +
    M.β • M.Pop (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h) = _
  rw [Φσ, map_add, smul_add, add_assoc]

/-- `Φ_σ h = ∫ [σe + (1 − σ)h(z')] ν(dζ')` almost everywhere. -/
theorem Φσ_coeFn (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) :
    ⇑(M.Φσ σ h) =ᵐ[M.φ] fun z => ∫ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) ∂M.ν := by
  filter_upwards [Lp.coeFn_add (M.accL σ) (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h),
    (M.integrable_accF σ).coeFn_toL1,
    L1.mulCLM_coeFn (M.measurable_qF σ) (M.abs_qF_le σ) h, M.ae_integrable_e] with z h1 h2 h3 hi
  rw [Φσ, h1, Pi.add_apply, accL, h2, h3]
  have hsplit : ∀ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) =
      (if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) + h z * (if σ.1 (M.ω z ζ, z) then 0 else 1) :=
    fun ζ => by split_ifs <;> ring
  have hm1 : Measurable fun ζ => σ.1 (M.ω z ζ, z) :=
    (M.measurable_pair σ).comp measurable_prodMk_left
  have hi1 : Integrable (fun ζ => if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) M.ν :=
    hi.norm.mono' (Measurable.ite (hm1 (measurableSet_singleton true))
      (M.measurable_e.comp measurable_prodMk_left) measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ζ => by
        split_ifs
        · exact le_rfl
        · simp)
  have hi2 : Integrable (fun ζ => h z * (if σ.1 (M.ω z ζ, z) then (0 : ℝ) else 1)) M.ν :=
    (Integrable.of_bound (Measurable.ite (hm1 (measurableSet_singleton true)) measurable_const
      measurable_const).aestronglyMeasurable 1 (Eventually.of_forall fun ζ => by
        split_ifs <;> norm_num)).const_mul _
  simp_rw [hsplit]
  rw [integral_add hi1 hi2, integral_const_mul, mul_comm]
  rfl

/-- `Φh = ∫ max{e, h(z')} ν(dζ')`. -/
noncomputable def ΦmaxF (h : Lp ℝ 1 M.φ) (z : Z) : ℝ := ∫ ζ, max (M.e z ζ) (h z) ∂M.ν

theorem measurable_ΦmaxF (h : Lp ℝ 1 M.φ) : Measurable (M.ΦmaxF h) := by
  have hm : Measurable fun p : Z × Ξ => max (M.e p.1 p.2) (h p.1) :=
    M.measurable_e.max ((Lp.stronglyMeasurable h).measurable.comp measurable_fst)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem integrable_ΦmaxF (h : Lp ℝ 1 M.φ) : Integrable (M.ΦmaxF h) M.φ := by
  refine (M.integrable_absInt.add (L1.integrable_coeFn h).abs).mono'
    (M.measurable_ΦmaxF h).aestronglyMeasurable ?_
  filter_upwards [M.ae_integrable_e] with z hi
  rw [Real.norm_eq_abs, Pi.add_apply]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ζ, |max (M.e z ζ) (h z)| ∂M.ν ≤ ∫ ζ, (|M.e z ζ| + |h z|) ∂M.ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hi.abs.add (integrable_const _)) (Eventually.of_forall fun ζ => by
            rw [abs_le]
            constructor
            · linarith [le_max_left (M.e z ζ) (h z), neg_abs_le (M.e z ζ), abs_nonneg (h z)]
            · exact max_le (by linarith [le_abs_self (M.e z ζ), abs_nonneg (h z)])
                (by linarith [le_abs_self (h z), abs_nonneg (M.e z ζ)]))
    _ = ∫ ζ, |M.e z ζ| ∂M.ν + |h z| := by
        rw [integral_add hi.abs (integrable_const _)]
        simp

/-- `Φh` in `L¹(φ)`. -/
noncomputable def Φmax (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := (M.integrable_ΦmaxF h).toL1 _

/-- The policy of Exercise 8.1.21: accept when `w'/(1 − β) ≥ h(z')`. -/
noncomputable def accept (h : Lp ℝ 1 M.φ) : StopPolicy (ℝ × Z) :=
  acceptWhere (s := fun p : ℝ × Z => p.1 / (1 - M.β)) (h := fun p => h p.2)
    (measurable_fst.div_const _) ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)

theorem integrable_choice (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) {z : Z}
    (hi : Integrable (M.e z) M.ν) :
    Integrable (fun ζ => if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) M.ν := by
  have hm1 : Measurable fun ζ => σ.1 (M.ω z ζ, z) :=
    (M.measurable_pair σ).comp measurable_prodMk_left
  refine (hi.abs.add (integrable_const |h z|)).mono' (Measurable.ite
    (hm1 (measurableSet_singleton true)) (M.measurable_e.comp measurable_prodMk_left)
    measurable_const).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  split_ifs
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem integrable_max_e (h : Lp ℝ 1 M.φ) {z : Z} (hi : Integrable (M.e z) M.ν) :
    Integrable (fun ζ => max (M.e z ζ) (h z)) M.ν :=
  hi.sup (integrable_const (h z))

theorem Φσ_le_Φmax (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) : M.Φσ σ h ≤ M.Φmax h := by
  rw [← Lp.coeFn_le]
  filter_upwards [M.Φσ_coeFn σ h, (M.integrable_ΦmaxF h).coeFn_toL1, M.ae_integrable_e]
    with z h1 h2 hi
  rw [Φmax, h1, h2, ΦmaxF]
  refine integral_mono (M.integrable_choice σ h hi) (M.integrable_max_e h hi) fun ζ => ?_
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Φσ_accept (h : Lp ℝ 1 M.φ) : M.Φσ (M.accept h) h = M.Φmax h := by
  refine Lp.ext ?_
  filter_upwards [M.Φσ_coeFn (M.accept h) h, (M.integrable_ΦmaxF h).coeFn_toL1] with z h1 h2
  rw [Φmax, h1, h2, ΦmaxF]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  exact acceptWhere_apply (s := fun p : ℝ × Z => p.1 / (1 - M.β)) (h := fun p => h p.2)
    (measurable_fst.div_const _) ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)
    (M.ω z ζ, z)

/-- The continuation value Bellman operator (8.29), `T̂h = c + βP(Φh)`. -/
noncomputable def That (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := M.cconst + M.β • M.Pop (M.Φmax h)

/-- **Exercises 8.1.21–8.1.22** (p. 260): the policy `σ(w', z') = 𝟙{w'/(1 − β) ≥ h(z')}` is
`h`-greedy, and the Bellman operator is (8.29), `(T̂h)(z) = c + β 𝔼_z max{w'/(1 − β), h(z')}`, i.e.
`T̂h = c + βP(Φh)`, `(Φh)(z') = ∫ max{ω(z', ζ')/(1 − β), h(z')} ν(dζ')`. -/
theorem exercise_8_1_21_22 (h : Lp ℝ 1 M.φ) :
    M.adp.IsGreedy h (M.accept h) ∧ M.adp.bellman h = M.That h := by
  have hT : M.adp.T (M.accept h) h = M.That h := by rw [T_eq, Φσ_accept]; rfl
  have hg : M.adp.IsGreedy h (M.accept h) := fun τ => by
    rw [T_eq, T_eq]
    exact add_le_add le_rfl (M.smul_le_smul'
      ((L1.markovCLM_isPositive M.stationary).mono ((M.Φσ_le_Φmax τ h).trans
        (by rw [Φσ_accept]))))
  refine ⟨hg, ?_⟩
  rw [← hT]
  exact le_antisymm (M.adp.isGreedy_greedy ⟨_, hg⟩ _) (hg _) |>.symm

theorem regular : M.adp.Regular := fun h => ⟨_, (M.exercise_8_1_21_22 h).1⟩

/-- The Bellman operator (8.29) almost everywhere:
`(T̂h)(z) = c + β ∫ ∫ max{ω(z', ζ')/(1 − β), h(z')} ν(dζ') P(z, dz')`. -/
theorem That_coeFn (h : Lp ℝ 1 M.φ) :
    ⇑(M.That h) =ᵐ[M.φ] fun z => M.c + M.β * ∫ z', M.ΦmaxF h z' ∂(M.P z) := by
  filter_upwards [Lp.coeFn_add M.cconst (M.β • M.Pop (M.Φmax h)),
    (memLp_const (μ := M.φ) M.c).coeFn_toLp, Lp.coeFn_smul M.β (M.Pop (M.Φmax h)),
    L1.markovCLM_coeFn M.stationary (M.Φmax h),
    L1.markovFun_congr M.stationary (M.integrable_ΦmaxF h).coeFn_toL1] with z h1 h2 h3 h4 h5
  rw [That, h1, Pi.add_apply]
  change M.cconst z + (M.β • M.Pop (M.Φmax h)) z = _
  rw [h3, Pi.smul_apply, smul_eq_mul]
  change ((memLp_const M.c).toLp _) z + M.β * (L1.markovCLM M.stationary (M.Φmax h)) z = _
  rw [h2, h4]
  change M.c + M.β * L1.markovFun (M.Φmax h) z = _
  rw [show L1.markovFun (M.Φmax h) z = _ from h5]

/-- **Exercise 8.1.23** (p. 260): `T̂` is a contraction of modulus `β` on `L¹(φ)`. -/
theorem exercise_8_1_23 (g h : Lp ℝ 1 M.φ) : ‖M.That g - M.That h‖ ≤ M.β * ‖g - h‖ := by
  rw [That, That, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, norm_smul,
    Real.norm_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
  refine (M.Pop.le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary) (norm_nonneg _)).trans ?_
  rw [one_mul, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  refine integral_mono_ae (L1.integrable_coeFn _).norm (L1.integrable_coeFn _).norm ?_
  filter_upwards [Lp.coeFn_sub (M.Φmax g) (M.Φmax h), Lp.coeFn_sub g h,
    (M.integrable_ΦmaxF g).coeFn_toL1, (M.integrable_ΦmaxF h).coeFn_toL1, M.ae_integrable_e]
    with z h1 h2 h3 h4 hi
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  change |(M.Φmax g) z - (M.Φmax h) z| ≤ _
  rw [Φmax, Φmax, h3, h4, ΦmaxF, ΦmaxF, ← integral_sub (M.integrable_max_e g hi)
    (M.integrable_max_e h hi)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ζ, |max (M.e z ζ) (g z) - max (M.e z ζ) (h z)| ∂M.ν ≤ ∫ _, |g z - h z| ∂M.ν :=
        integral_mono ((M.integrable_max_e g hi).sub (M.integrable_max_e h hi)).abs
          (integrable_const _) fun ζ => by
            rw [max_comm _ (g z), max_comm _ (h z)]
            exact abs_max_sub_max_le_abs _ _ _
    _ = |g z - h z| := by simp

theorem That_contracting : ContractingWith ⟨M.β, M.β_nonneg⟩ M.That :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun g h => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.exercise_8_1_23 g h⟩

theorem That_mono : Monotone M.That := fun g h hgh => by
  refine add_le_add le_rfl (M.smul_le_smul'
    ((L1.markovCLM_isPositive M.stationary).mono ?_))
  rw [← Lp.coeFn_le]
  filter_upwards [(M.integrable_ΦmaxF g).coeFn_toL1, (M.integrable_ΦmaxF h).coeFn_toL1,
    (Lp.coeFn_le _ _).2 hgh, M.ae_integrable_e] with z h1 h2 h3 hi
  rw [Φmax, Φmax, h1, h2]
  exact integral_mono (M.integrable_max_e g hi) (M.integrable_max_e h hi) fun ζ =>
    max_le_max le_rfl h3

theorem isAdditive : BanachLattice.IsAdditive id M.adp M.mσ M.Kσ :=
  ⟨M.Kσ_isPositive, fun _ _ => rfl⟩

/-- §8.1.3.3 (p. 260): by Theorem 4.1.8, the fundamental optimality properties hold for
`(L¹(φ), 𝕋̂)` and VFI, OPI and HPI converge. -/
theorem section_8_1_3_3 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar,
      M.adp.VFIGeometric univ vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one
  have hsr : M.adp.IsSemiRegular univ := ⟨isClosed_univ, fun v _ => M.regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 M.φ) M.adp M.isAdditive hD M.Kσ_le_D hsr univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv M.regular⟩

/-- The model with unemployment compensation `c'`. -/
abbrev withC (c' : ℝ) : PersistentSearch Z Ξ := { M with c := c' }

/-- **Exercise 8.1.24** (p. 260): if `c_a ≤ c_b`, the fixed points of the corresponding
continuation value operators satisfy `h_a ≤ h_b` (almost everywhere, the order of `L¹(φ)`). -/
theorem exercise_8_1_24 {ca cb : ℝ} (hc : ca ≤ cb) :
    ContractingWith.fixedPoint _ (M.withC ca).That_contracting ≤
      ContractingWith.fixedPoint _ (M.withC cb).That_contracting := by
  refine fixedPoint_ge_of_le (M.withC cb).That_contracting (M.withC cb).That_mono (fun h => ?_)
    (ContractingWith.fixedPoint_isFixedPt (M.withC ca).That_contracting)
  refine add_le_add ?_ le_rfl
  rw [← Lp.coeFn_le]
  filter_upwards [(memLp_const (μ := M.φ) ca).coeFn_toLp, (memLp_const (μ := M.φ) cb).coeFn_toLp]
    with z h1 h2
  change ((memLp_const ca).toLp _) z ≤ ((memLp_const cb).toLp _) z
  rw [h1, h2]
  exact hc

end PersistentSearch

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Power means

The Kreps–Porteus certainty equivalent `M_p(v) = (∫ v^p dμ)^{1/p}`, `p ≠ 0`, on positive bounded
measurable functions, for a probability measure `μ`. It is monotone, fixes constants and is
positively homogeneous; it is superadditive, hence concave, for `p ≤ 1`, and subadditive, hence
convex, for `p ≥ 1`. The proof normalises `v` and `w` to unit power mean and applies the
concavity (`0 < p ≤ 1`) or convexity (`p < 0`, `p ≥ 1`) of `t ↦ t^p` to the convex combination
`(v + w)/(a + b) = (a/(a + b))(v/a) + (b/(a + b))(w/b)`.
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

/-- `t ↦ t^p` is convex on `(0, ∞)` for `p < 0`. -/
theorem convexOn_rpow_of_neg {p : ℝ} (hp : p < 0) : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p := by
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
  have h1 : t ^ (p - 1) ≤ s ^ (p - 1) := Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Positive, bounded, bounded-away-from-zero measurable functions. -/
def PosBdd (v : Ω → ℝ) : Prop :=
  Measurable v ∧ ∃ lo hi : ℝ, 0 < lo ∧ ∀ x, v x ∈ Icc lo hi

/-- The power mean `M_p(v) = (∫ v^p dμ)^{1/p}`. -/
noncomputable def pmean (p : ℝ) (v : Ω → ℝ) : ℝ := (∫ x, v x ^ p ∂μ) ^ p⁻¹

variable {μ}

theorem PosBdd.pos {v : Ω → ℝ} (hv : PosBdd v) (x : Ω) : 0 < v x := by
  obtain ⟨-, lo, hi, hlo, h⟩ := hv
  exact hlo.trans_le (h x).1

theorem PosBdd.integrable_rpow {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) :
    Integrable (fun x => v x ^ p) μ := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  refine Integrable.of_bound (hm.pow_const p).aestronglyMeasurable (lo ^ p + hi ^ p)
    (Eventually.of_forall fun x => ?_)
  have hx := h x
  have hpos : 0 < v x := hlo.trans_le hx.1
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  rcases le_total 0 p with hp | hp
  · exact (Real.rpow_le_rpow hpos.le hx.2 hp).trans
      (le_add_of_nonneg_left (Real.rpow_pos_of_pos hlo _).le)
  · exact (Real.rpow_le_rpow_of_nonpos hlo hx.1 hp).trans
      (le_add_of_nonneg_right (Real.rpow_pos_of_pos (hlo.trans_le (hx.1.trans hx.2)) _).le)

theorem PosBdd.integral_rpow_pos {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) :
    0 < ∫ x, v x ^ p ∂μ := by
  have heq : (fun x => v x ^ p) = fun x => Real.exp (Real.log (v x) * p) :=
    funext fun x => Real.rpow_def_of_pos (hv.pos x) p
  rw [heq]
  exact integral_exp_pos (by rw [← heq]; exact hv.integrable_rpow p)

theorem PosBdd.pmean_pos {v : Ω → ℝ} (hv : PosBdd v) (p : ℝ) : 0 < pmean μ p v :=
  Real.rpow_pos_of_pos (hv.integral_rpow_pos p) _

theorem PosBdd.add {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) : PosBdd (v + w) := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  obtain ⟨hm', lo', hi', hlo', h'⟩ := hw
  exact ⟨hm.add hm', lo + lo', hi + hi', by linarith, fun x =>
    ⟨add_le_add (h x).1 (h' x).1, add_le_add (h x).2 (h' x).2⟩⟩

theorem PosBdd.smul {v : Ω → ℝ} (hv : PosBdd v) {c : ℝ} (hc : 0 < c) : PosBdd (c • v) := by
  obtain ⟨hm, lo, hi, hlo, h⟩ := hv
  exact ⟨hm.const_smul c, c * lo, c * hi, mul_pos hc hlo, fun x =>
    ⟨mul_le_mul_of_nonneg_left (h x).1 hc.le, mul_le_mul_of_nonneg_left (h x).2 hc.le⟩⟩

theorem posBdd_const {c : ℝ} (hc : 0 < c) : PosBdd (fun _ : Ω => c) :=
  ⟨measurable_const, c, c, hc, fun _ => ⟨le_rfl, le_rfl⟩⟩

/-- `M_p` fixes constants. -/
theorem pmean_const {p : ℝ} (hp : p ≠ 0) {c : ℝ} (hc : 0 < c) :
    pmean μ p (fun _ => c) = c := by
  rw [pmean, integral_const, probReal_univ, one_smul, Real.rpow_rpow_inv hc.le hp]

/-- `M_p` is monotone. -/
theorem pmean_mono {p : ℝ} (hp : p ≠ 0) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w)
    (h : v ≤ w) : pmean μ p v ≤ pmean μ p w := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have hle : ∫ x, w x ^ p ∂μ ≤ ∫ x, v x ^ p ∂μ :=
      integral_mono (hw.integrable_rpow p) (hv.integrable_rpow p) fun x =>
        Real.rpow_le_rpow_of_nonpos (hv.pos x) (h x) hneg.le
    exact Real.rpow_le_rpow_of_nonpos (hw.integral_rpow_pos p) hle (inv_nonpos.2 hneg.le)
  · have hle : ∫ x, v x ^ p ∂μ ≤ ∫ x, w x ^ p ∂μ :=
      integral_mono (hv.integrable_rpow p) (hw.integrable_rpow p) fun x =>
        Real.rpow_le_rpow (hv.pos x).le (h x) hpos.le
    exact Real.rpow_le_rpow (hv.integral_rpow_pos p).le hle (inv_nonneg.2 hpos.le)

/-- `M_p` is positively homogeneous. -/
theorem pmean_smul {p : ℝ} (hp : p ≠ 0) {v : Ω → ℝ} (hv : PosBdd v) {c : ℝ} (hc : 0 < c) :
    pmean μ p (c • v) = c * pmean μ p v := by
  have heq : (fun x => (c • v) x ^ p) = fun x => c ^ p * v x ^ p := funext fun x => by
    rw [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hc.le (hv.pos x).le]
  rw [pmean, pmean, heq, integral_const_mul,
    Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (hv.integral_rpow_pos p).le,
    Real.rpow_rpow_inv hc.le hp]

/-- The normalised power mean: `∫ (v/a)^p = 1` for `a = M_p(v)`. -/
theorem integral_rpow_normalize {p : ℝ} (hp : p ≠ 0) {v : Ω → ℝ} (hv : PosBdd v) :
    ∫ x, ((pmean μ p v)⁻¹ * v x) ^ p ∂μ = 1 := by
  have ha := hv.pmean_pos (μ := μ) p
  have heq : (fun x => ((pmean μ p v)⁻¹ * v x) ^ p) =
      fun x => ((pmean μ p v) ^ p)⁻¹ * v x ^ p := funext fun x => by
    rw [Real.mul_rpow (inv_pos.2 ha).le (hv.pos x).le, Real.inv_rpow ha.le]
  rw [heq, integral_const_mul, pmean, Real.rpow_inv_rpow (hv.integral_rpow_pos p).le hp,
    inv_mul_cancel₀ (hv.integral_rpow_pos p).ne']

/-- The level-set inequality: if `t ↦ t^p` is convex on `(0, ∞)`, then
`∫ (v + w)^p ≤ (M_p v + M_p w)^p`. -/
theorem integral_rpow_add_le {p : ℝ} (hp : p ≠ 0) (hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p)
    {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    ∫ x, (v x + w x) ^ p ∂μ ≤ (pmean μ p v + pmean μ p w) ^ p := by
  set a := pmean μ p v
  set b := pmean μ p w
  have ha : 0 < a := hv.pmean_pos p
  have hb : 0 < b := hw.pmean_pos p
  have hab : 0 < a + b := by linarith
  have hpt : ∀ x, ((a + b)⁻¹ * (v x + w x)) ^ p ≤
      a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p := fun x => by
    have hcomb : (a + b)⁻¹ * (v x + w x) =
        a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := by field_simp
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv.pos x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw.pos x))
      (by positivity) (by positivity) (by field_simp)
  have hiv : Integrable (fun x => (a⁻¹ * v x) ^ p) μ := (hv.smul (inv_pos.2 ha)).integrable_rpow p
  have hiw : Integrable (fun x => (b⁻¹ * w x) ^ p) μ := (hw.smul (inv_pos.2 hb)).integrable_rpow p
  have hivw : Integrable (fun x => ((a + b)⁻¹ * (v x + w x)) ^ p) μ :=
    ((hv.add hw).smul (inv_pos.2 hab)).integrable_rpow p
  have hint : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ ≤
      ∫ x, (a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p) ∂μ :=
    integral_mono hivw ((hiv.const_mul _).add (hiw.const_mul _)) hpt
  rw [integral_add (hiv.const_mul _) (hiw.const_mul _), integral_const_mul, integral_const_mul,
    integral_rpow_normalize hp hv, integral_rpow_normalize hp hw] at hint
  have h1 : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ =
      ((a + b) ^ p)⁻¹ * ∫ x, (v x + w x) ^ p ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ((a + b)⁻¹ * (v x + w x)) ^ p = ((a + b) ^ p)⁻¹ * (v x + w x) ^ p
    rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv.pos x) (hw.pos x)).le, Real.inv_rpow hab.le]
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2] at hint
  have h3 : 0 < (a + b) ^ p := Real.rpow_pos_of_pos hab _
  rwa [inv_mul_le_iff₀ h3, mul_one] at hint

/-- The concave counterpart: if `t ↦ t^p` is concave on `(0, ∞)`, then
`(M_p v + M_p w)^p ≤ ∫ (v + w)^p`. -/
theorem le_integral_rpow_add {p : ℝ} (hp : p ≠ 0) (hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ p)
    {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    (pmean μ p v + pmean μ p w) ^ p ≤ ∫ x, (v x + w x) ^ p ∂μ := by
  set a := pmean μ p v
  set b := pmean μ p w
  have ha : 0 < a := hv.pmean_pos p
  have hb : 0 < b := hw.pmean_pos p
  have hab : 0 < a + b := by linarith
  have hpt : ∀ x, a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p ≤
      ((a + b)⁻¹ * (v x + w x)) ^ p := fun x => by
    have hcomb : (a + b)⁻¹ * (v x + w x) =
        a / (a + b) * (a⁻¹ * v x) + b / (a + b) * (b⁻¹ * w x) := by field_simp
    rw [hcomb]
    exact hφ.2 (show a⁻¹ * v x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 ha) (hv.pos x))
      (show b⁻¹ * w x ∈ Ioi (0 : ℝ) from mul_pos (inv_pos.2 hb) (hw.pos x))
      (by positivity) (by positivity) (by field_simp)
  have hiv : Integrable (fun x => (a⁻¹ * v x) ^ p) μ := (hv.smul (inv_pos.2 ha)).integrable_rpow p
  have hiw : Integrable (fun x => (b⁻¹ * w x) ^ p) μ := (hw.smul (inv_pos.2 hb)).integrable_rpow p
  have hivw : Integrable (fun x => ((a + b)⁻¹ * (v x + w x)) ^ p) μ :=
    ((hv.add hw).smul (inv_pos.2 hab)).integrable_rpow p
  have hint : ∫ x, (a / (a + b) * (a⁻¹ * v x) ^ p + b / (a + b) * (b⁻¹ * w x) ^ p) ∂μ ≤
      ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ :=
    integral_mono ((hiv.const_mul _).add (hiw.const_mul _)) hivw hpt
  rw [integral_add (hiv.const_mul _) (hiw.const_mul _), integral_const_mul, integral_const_mul,
    integral_rpow_normalize hp hv, integral_rpow_normalize hp hw] at hint
  have h1 : ∫ x, ((a + b)⁻¹ * (v x + w x)) ^ p ∂μ =
      ((a + b) ^ p)⁻¹ * ∫ x, (v x + w x) ^ p ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change ((a + b)⁻¹ * (v x + w x)) ^ p = ((a + b) ^ p)⁻¹ * (v x + w x) ^ p
    rw [Real.mul_rpow (inv_pos.2 hab).le (add_pos (hv.pos x) (hw.pos x)).le, Real.inv_rpow hab.le]
  have h2 : a / (a + b) * 1 + b / (a + b) * 1 = 1 := by field_simp
  rw [h1, h2] at hint
  have h3 : 0 < (a + b) ^ p := Real.rpow_pos_of_pos hab _
  rwa [le_inv_mul_iff₀ h3, mul_one] at hint

/-- `M_p` is superadditive for `p ≤ 1`, `p ≠ 0`. -/
theorem pmean_add_ge {p : ℝ} (hp : p ≠ 0) (hp1 : p ≤ 1) {v w : Ω → ℝ} (hv : PosBdd v)
    (hw : PosBdd w) : pmean μ p v + pmean μ p w ≤ pmean μ p (v + w) := by
  have hab : 0 < pmean μ p v + pmean μ p w := add_pos (hv.pmean_pos p) (hw.pmean_pos p)
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have h1 := integral_rpow_add_le hp (convexOn_rpow_of_neg hneg) hv hw (μ := μ)
    have h2 := Real.rpow_le_rpow_of_nonpos ((hv.add hw).integral_rpow_pos p) h1
      (inv_nonpos.2 hneg.le)
    rwa [Real.rpow_rpow_inv hab.le hp] at h2
  · have hφ : ConcaveOn ℝ (Ioi 0) fun t : ℝ => t ^ p :=
      (Real.concaveOn_rpow hpos.le hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)
    have h1 := le_integral_rpow_add hp hφ hv hw (μ := μ)
    have h2 := Real.rpow_le_rpow (Real.rpow_pos_of_pos hab _).le h1 (inv_nonneg.2 hpos.le)
    rwa [Real.rpow_rpow_inv hab.le hp] at h2

/-- `M_p` is subadditive for `p ≥ 1` (Minkowski). -/
theorem pmean_add_le {p : ℝ} (hp1 : 1 ≤ p) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w) :
    pmean μ p (v + w) ≤ pmean μ p v + pmean μ p w := by
  have hp : p ≠ 0 := by linarith
  have hab : 0 < pmean μ p v + pmean μ p w := add_pos (hv.pmean_pos p) (hw.pmean_pos p)
  have hφ : ConvexOn ℝ (Ioi 0) fun t : ℝ => t ^ p :=
    (convexOn_rpow hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)
  have h1 := integral_rpow_add_le hp hφ hv hw (μ := μ)
  have h2 := Real.rpow_le_rpow ((hv.add hw).integral_rpow_pos p).le h1
    (inv_nonneg.2 (zero_le_one.trans hp1))
  rwa [Real.rpow_rpow_inv hab.le hp] at h2

/-- Concavity of `M_p` along a convex combination, `p ≤ 1`, `p ≠ 0`. -/
theorem pmean_concave {p : ℝ} (hp : p ≠ 0) (hp1 : p ≤ 1) {v w : Ω → ℝ} (hv : PosBdd v)
    (hw : PosBdd w) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * pmean μ p v + b * pmean μ p w ≤ pmean μ p (a • v + b • w) := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h := pmean_add_ge hp hp1 (hv.smul ha') (hw.smul hb') (μ := μ)
      rwa [pmean_smul hp hv ha', pmean_smul hp hw hb'] at h
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- Convexity of `M_p` along a convex combination, `p ≥ 1`. -/
theorem pmean_convex {p : ℝ} (hp1 : 1 ≤ p) {v w : Ω → ℝ} (hv : PosBdd v) (hw : PosBdd w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    pmean μ p (a • v + b • w) ≤ a * pmean μ p v + b * pmean μ p w := by
  have hp : p ≠ 0 := by linarith
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h := pmean_add_le hp1 (hv.smul ha') (hw.smul hb') (μ := μ)
      rwa [pmean_smul hp hv ha', pmean_smul hp hw hb'] at h
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search with nonlinear discounting and nonlinear expectations

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.1–§8.2.2 (pp. 261–264).

Offers are `P`-Markov on a state space `X`, with the offer `w(x) ∈ [w₁, w₂]`, `0 < c < w₁`. The
book takes `X = W = [w₁, w₂]` with `w(x) = x`.

* §8.2.1, nonlinear discounting: the continuation value is `c + ∫ β[v(w')]P(w, dw')` with a
  discount function `β`. The book's `β(x) = b(1 − e^{−λx})` (`bexp`) is continuous, increasing,
  concave on `ℝ₊`, with `β(0) = 0` and `β < b`; these properties are all that is used.
  * **Exercises 8.2.1–8.2.2**: `(Hg)(w) = w + β(g(w))` is an order preserving self-map of
    `V = [0, v̄]`, `v̄ = (c + w₂)/(1 − b)`, satisfies Du's conditions, and has a unique fixed point
    `e ∈ V`, the lifetime value of a constant wage stream.
  * **Exercises 8.2.3–8.2.4**: each `T_σ` maps `V` into itself, is concave and satisfies Du's
    conditions; with the greedy policy, Theorem 4.1.11 applies: the fundamental optimality
    properties hold and VFI, OPI and HPI converge.
* §8.2.2, nonlinear expectations: `T_σ v = σe + (1 − σ)(c + βRv)` with the Kreps–Porteus operator
  `(Rv)(w) = (∫ v^{1−γ} dP(w, ·))^{1/(1−γ)}`, `γ ≠ 1`, on `V = [c, v̄]`, `v̄ = (c + w₂)/(1 − β)`.
  * **Exercise 8.2.5**: `R` is order preserving and fixes constants; it is concave for `γ ≥ 0` and
    convex for `γ ≤ 0` (power means, `PowerMean`).
  * The `ε` bounds of p. 264 and Theorem 4.1.11: the fundamental optimality properties hold and
    VFI, OPI and HPI converge, for every `γ ≠ 1`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X : Type*} [MeasurableSpace X]

/-- A continuous function of a bounded function is bounded. -/
theorem bdd_comp {f : ℝ → ℝ} (hf : Continuous f) (g : BM X) : ∃ C, ∀ x, |f (g.toFun x)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -‖g‖) (b := ‖g‖)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun x => by
    have := hC (g.toFun x) (abs_le.1 (BM.abs_le_norm g x))
    rwa [Real.norm_eq_abs] at this⟩

/-- The book's discount function `β(x) = b(1 − e^{−λx})`. -/
noncomputable def bexp (b lam : ℝ) (x : ℝ) : ℝ := b * (1 - Real.exp (-lam * x))

/-- `β(x) = b(1 − e^{−λx})` is continuous, increasing, concave, `β(0) = 0` and `β < b`. -/
theorem bexp_properties {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    Continuous (bexp b lam) ∧ Monotone (bexp b lam) ∧ ConcaveOn ℝ (Ici 0) (bexp b lam) ∧
      bexp b lam 0 = 0 ∧ ∀ x, bexp b lam x < b := by
  refine ⟨continuous_const.mul (continuous_const.sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))),
    fun x y h => mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.exp_le_exp.2
      (by nlinarith)) 1) hb.le, ⟨convex_Ici 0, fun x _ y _ a c ha hc hac => ?_⟩, by simp [bexp],
    fun x => by
      unfold bexp
      have := Real.exp_pos (-lam * x)
      nlinarith⟩
  have hconv := convexOn_exp.2 (mem_univ (-lam * x)) (mem_univ (-lam * y)) ha hc hac
  simp only [smul_eq_mul] at hconv ⊢
  have heq : a * (-lam * x) + c * (-lam * y) = -lam * (a * x + c * y) := by ring
  rw [heq] at hconv
  unfold bexp
  nlinarith

/-! ### Nonlinear discounting -/

/-- Job search with nonlinear discounting (§8.2.1). -/
structure NLDiscount (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  w₁ : ℝ
  w₂ : ℝ
  w₁_lt : w₁ < w₂
  wage_mem : ∀ x, wage x ∈ Icc w₁ w₂
  /-- unemployment compensation -/
  c : ℝ
  c_pos : 0 < c
  c_lt : c < w₁
  /-- the bound `b` of the discount function -/
  b : ℝ
  b_pos : 0 < b
  b_lt_one : b < 1
  w₂_ge : 1 - b ≤ w₂
  /-- the discount function -/
  βf : ℝ → ℝ
  continuous_βf : Continuous βf
  monotone_βf : Monotone βf
  concave_βf : ConcaveOn ℝ (Ici 0) βf
  βf_zero : βf 0 = 0
  βf_lt : ∀ x, βf x < b

namespace NLDiscount

attribute [local instance] NLDiscount.isMarkov

variable (M : NLDiscount X)

/-- `v̄ = (c + w₂)/(1 − b)`. -/
noncomputable def vbarR : ℝ := (M.c + M.w₂) / (1 - M.b)

/-- `v̄` as a constant function. -/
noncomputable def vbar : BM X := BM.const M.vbarR

theorem one_sub_b_pos : 0 < 1 - M.b := sub_pos.2 M.b_lt_one

theorem w₂_add_b_le : M.w₂ + M.b ≤ M.vbarR := by
  rw [vbarR, le_div_iff₀ M.one_sub_b_pos]
  have := M.w₂_ge
  have := M.c_pos
  have := M.b_pos
  nlinarith

theorem c_add_b_le : M.c + M.b ≤ M.vbarR := by
  have := M.w₂_add_b_le
  have := M.c_lt
  have := M.w₁_lt
  linarith

theorem w₁_pos : 0 < M.w₁ := M.c_pos.trans M.c_lt

theorem w₁_lt_vbar : M.w₁ < M.vbarR := by
  have := M.w₂_add_b_le
  have := M.w₁_lt
  have := M.b_pos
  linarith

theorem vbar_pos : 0 < M.vbarR := M.w₁_pos.trans M.w₁_lt_vbar

theorem zero_le_vbar : (0 : BM X) ≤ M.vbar := BM.le_def.2 fun _ => M.vbar_pos.le

/-- `(Hg)(w) = w + β(g(w))` (8.31). -/
noncomputable def H (g : BM X) : BM X :=
  ⟨fun x => M.wage x + M.βf (g.toFun x),
    M.measurable_wage.add (M.continuous_βf.measurable.comp g.measurable'), by
    obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf g
    refine ⟨|M.w₁| + |M.w₂| + C, fun x => ?_⟩
    have h1 := M.wage_mem x
    refine (abs_add_le _ _).trans (add_le_add ?_ (hC x))
    rw [abs_le]
    constructor <;> linarith [neg_abs_le M.w₁, le_abs_self M.w₂, abs_nonneg M.w₁,
      abs_nonneg M.w₂, h1.1, h1.2]⟩

theorem H_apply (g : BM X) (x : X) : (M.H g).toFun x = M.wage x + M.βf (g.toFun x) := rfl

/-- **Exercise 8.2.1** (p. 262): `H` is an order preserving self-map of `V = [0, v̄]`. -/
theorem exercise_8_2_1 : Monotone M.H ∧ MapsTo M.H (Icc 0 M.vbar) (Icc 0 M.vbar) := by
  refine ⟨fun g g' h => BM.le_def.2 fun x => add_le_add le_rfl
    (M.monotone_βf (BM.le_def.1 h x)), fun g hg => ⟨BM.le_def.2 fun x => ?_,
      BM.le_def.2 fun x => ?_⟩⟩
  · have h0 : M.βf 0 ≤ M.βf (g.toFun x) := M.monotone_βf (BM.le_def.1 hg.1 x)
    rw [M.βf_zero] at h0
    change (0 : ℝ) ≤ M.wage x + M.βf (g.toFun x)
    linarith [(M.wage_mem x).1, M.w₁_pos]
  · change M.wage x + M.βf (g.toFun x) ≤ M.vbarR
    linarith [(M.wage_mem x).2, M.βf_lt (g.toFun x), M.w₂_add_b_le]

theorem concaveOn_H : ConcaveOn ℝ (Icc 0 M.vbar) M.H := by
  refine ⟨convex_Icc _ _, fun g hg g' hg' a b ha hb hab => BM.le_def.2 fun x => ?_⟩
  have h0 : g.toFun x ∈ Ici (0 : ℝ) := BM.le_def.1 hg.1 x
  have h0' : g'.toFun x ∈ Ici (0 : ℝ) := BM.le_def.1 hg'.1 x
  have hc := M.concave_βf.2 h0 h0' ha hb hab
  simp only [smul_eq_mul] at hc
  change a * (M.wage x + M.βf (g.toFun x)) + b * (M.wage x + M.βf (g'.toFun x)) ≤
    M.wage x + M.βf (a * g.toFun x + b * g'.toFun x)
  have : a * M.wage x + b * M.wage x = M.wage x := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- **Exercise 8.2.2** (p. 262): `H` satisfies Du's conditions on `V` (concave, with
`H0 = w ≥ w₁ ≥ ε v̄`), so it is globally stable on `V` (Theorem 4.1.10). -/
theorem exercise_8_2_2 :
    BanachLattice.DuConditions 0 M.vbar M.H ∧
      BanachLattice.GloballyStableOn M.H (Icc 0 M.vbar) := by
  have hdu : BanachLattice.DuConditions 0 M.vbar M.H := by
    refine Or.inl ⟨M.concaveOn_H, M.w₁ / M.vbarR, div_pos M.w₁_pos M.vbar_pos,
      (div_lt_one M.vbar_pos).2 M.w₁_lt_vbar, BM.le_def.2 fun x => ?_⟩
    change 0 + M.w₁ / M.vbarR * (M.vbarR - 0) ≤ M.wage x + M.βf 0
    rw [M.βf_zero, div_mul_eq_mul_div, sub_zero, mul_div_assoc, div_self M.vbar_pos.ne']
    linarith [(M.wage_mem x).1]
  exact ⟨hdu, BanachLattice.theorem_4_1_10 M.zero_le_vbar M.exercise_8_2_1.2
    (M.exercise_8_2_1.1.monotoneOn _) hdu⟩

/-- The lifetime value `e ∈ V` of a constant wage stream: the unique fixed point of `H`. -/
noncomputable def e : BM X := M.exercise_8_2_2.2.choose

theorem e_mem : M.e ∈ Icc 0 M.vbar := M.exercise_8_2_2.2.choose_spec.1

theorem H_e : M.H M.e = M.e := M.exercise_8_2_2.2.choose_spec.2.1

theorem e_ge_w₁ (x : X) : M.w₁ ≤ M.e.toFun x := by
  have h := congrArg (fun g : BM X => g.toFun x) M.H_e
  simp only [H_apply] at h
  have h0 : M.βf 0 ≤ M.βf (M.e.toFun x) := M.monotone_βf (BM.le_def.1 M.e_mem.1 x)
  rw [M.βf_zero] at h0
  linarith [(M.wage_mem x).1]

/-- The continuation value `c + ∫ β[v(w')]P(w, dw')`. -/
noncomputable def cont (v : BM X) (x : X) : ℝ := M.c + ∫ y, M.βf (v.toFun y) ∂(M.P x)

theorem measurable_cont (v : BM X) : Measurable (M.cont v) :=
  measurable_const.add (measurable_markovOp M.P (M.continuous_βf.measurable.comp v.measurable'))

theorem integrable_βf (v : BM X) (x : X) : Integrable (fun y => M.βf (v.toFun y)) (M.P x) := by
  obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf v
  exact Integrable.of_bound (M.continuous_βf.measurable.comp v.measurable').aestronglyMeasurable C
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)

theorem cont_bounds {v : BM X} (hv : v ∈ Icc 0 M.vbar) (x : X) :
    M.c ≤ M.cont v x ∧ M.cont v x ≤ M.c + M.b := by
  constructor
  · refine le_add_of_nonneg_right (integral_nonneg fun y => ?_)
    have := M.monotone_βf (BM.le_def.1 hv.1 y)
    rw [BM.zero_apply, M.βf_zero] at this
    exact this
  · refine add_le_add le_rfl ?_
    calc ∫ y, M.βf (v.toFun y) ∂(M.P x) ≤ ∫ _, M.b ∂(M.P x) :=
          integral_mono (M.integrable_βf v x) (integrable_const _) fun y => (M.βf_lt _).le
      _ = M.b := by simp

/-- `(T_σ v)(w) = σ(w)e(w) + (1 − σ(w))[c + ∫ β[v(w')]P(w, dw')]`. -/
noncomputable def Tfun (σ : StopPolicy X) (v : BM X) : BM X :=
  ⟨fun x => if σ.1 x then M.e.toFun x else M.cont v x,
    Measurable.ite (σ.2 (measurableSet_singleton true)) M.e.measurable' (M.measurable_cont v), by
    obtain ⟨C, hC⟩ := bdd_comp M.continuous_βf v
    refine ⟨‖M.e‖ + |M.c| + C, fun x => ?_⟩
    split_ifs
    · exact le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (BM.abs_le_norm _ _) (abs_nonneg _))
        ((abs_nonneg _).trans (hC x))
    · refine (abs_add_le _ _).trans ?_
      refine add_le_add (le_add_of_nonneg_left (norm_nonneg _)) ?_
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ y, |M.βf (v.toFun y)| ∂(M.P x) ≤ ∫ _, C ∂(M.P x) :=
            integral_mono (M.integrable_βf v x).abs (integrable_const _) fun y => hC y
        _ = C := by simp⟩

/-- **Exercise 8.2.3** (p. 263): every `T_σ` maps `V = [0, v̄]` into itself. -/
theorem exercise_8_2_3 (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc 0 M.vbar) :
    M.Tfun σ v ∈ Icc 0 M.vbar := by
  refine ⟨BM.le_def.2 fun x => ?_, BM.le_def.2 fun x => ?_⟩
  · change (0 : ℝ) ≤ if σ.1 x then M.e.toFun x else M.cont v x
    split_ifs
    · exact BM.le_def.1 M.e_mem.1 x
    · linarith [(M.cont_bounds hv x).1, M.c_pos]
  · change (if σ.1 x then M.e.toFun x else M.cont v x) ≤ M.vbarR
    split_ifs
    · exact BM.le_def.1 M.e_mem.2 x
    · linarith [(M.cont_bounds hv x).2, M.c_add_b_le]

theorem cont_mono {v w : BM X} (h : v ≤ w) (x : X) : M.cont v x ≤ M.cont w x :=
  add_le_add le_rfl (integral_mono (M.integrable_βf v x) (M.integrable_βf w x) fun y =>
    M.monotone_βf (BM.le_def.1 h y))

/-- The nonlinear discount ADP `(V, 𝕋)` on `V = [0, v̄]`. -/
noncomputable def adp : ADP (Icc 0 M.vbar) (StopPolicy X) where
  T σ v := ⟨M.Tfun σ v, M.exercise_8_2_3 σ v.2⟩
  mono σ v w h := BM.le_def.2 fun x => by
    change (if σ.1 x then M.e.toFun x else M.cont v x) ≤
      (if σ.1 x then M.e.toFun x else M.cont w x)
    split_ifs
    · exact le_rfl
    · exact M.cont_mono h x
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The greedy policy: accept when `e(w) ≥ c + ∫ β[v(w')]P(w, dw')`. -/
noncomputable def accept (v : BM X) : StopPolicy X :=
  acceptWhere (s := M.e.toFun) (h := M.cont v) M.e.measurable' (M.measurable_cont v)

theorem regular : M.adp.Regular := fun v => ⟨M.accept v, fun τ => BM.le_def.2 fun x => by
  change (if τ.1 x then M.e.toFun x else M.cont v x) ≤
    (if (M.accept v).1 x then M.e.toFun x else M.cont v x)
  rw [accept, acceptWhere_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _⟩

theorem concaveOn_T (σ : StopPolicy X) :
    ConcaveOn ℝ (Icc 0 M.vbar) (BanachLattice.extendIcc (M.adp.T σ)) := by
  refine ⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩
  have hvw : a • v + b • w ∈ Icc 0 M.vbar := convex_Icc _ _ hv hw ha hb hab
  rw [show v = ((⟨v, hv⟩ : Icc 0 M.vbar) : BM X) from rfl,
    show w = ((⟨w, hw⟩ : Icc 0 M.vbar) : BM X) from rfl,
    BanachLattice.extendIcc_apply, BanachLattice.extendIcc_apply,
    show a • v + b • w = ((⟨a • v + b • w, hvw⟩ : Icc 0 M.vbar) : BM X) from rfl,
    BanachLattice.extendIcc_apply]
  refine BM.le_def.2 fun x => ?_
  change a * (if σ.1 x then M.e.toFun x else M.cont v x) +
    b * (if σ.1 x then M.e.toFun x else M.cont w x) ≤
      if σ.1 x then M.e.toFun x else M.cont (a • v + b • w) x
  split_ifs
  · rw [← add_mul, hab, one_mul]
  · have hpt : ∀ y, a * M.βf (v.toFun y) + b * M.βf (w.toFun y) ≤
        M.βf ((a • v + b • w).toFun y) := fun y => by
      have hc := M.concave_βf.2 (show v.toFun y ∈ Ici (0 : ℝ) from BM.le_def.1 hv.1 y)
        (show w.toFun y ∈ Ici (0 : ℝ) from BM.le_def.1 hw.1 y) ha hb hab
      simpa using hc
    have hI : ∫ y, (a * M.βf (v.toFun y) + b * M.βf (w.toFun y)) ∂(M.P x) ≤
        ∫ y, M.βf ((a • v + b • w).toFun y) ∂(M.P x) :=
      integral_mono (((M.integrable_βf v x).const_mul a).add
        ((M.integrable_βf w x).const_mul b)) (M.integrable_βf _ x) hpt
    rw [integral_add ((M.integrable_βf v x).const_mul a) ((M.integrable_βf w x).const_mul b),
      integral_const_mul, integral_const_mul] at hI
    change a * (M.c + ∫ y, M.βf (v.toFun y) ∂(M.P x)) +
      b * (M.c + ∫ y, M.βf (w.toFun y) ∂(M.P x)) ≤
        M.c + ∫ y, M.βf ((a • v + b • w).toFun y) ∂(M.P x)
    have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
    nlinarith

/-- **Exercise 8.2.4** (p. 263): the nonlinear discount ADP satisfies the conditions of
Theorem 4.1.11 (regular; every `T_σ` concave with `T_σ 0 ≥ c ≥ ε v̄`; `bW` countably Dedekind
complete), so the fundamental optimality properties hold and VFI, OPI and HPI all converge. -/
theorem exercise_8_2_4 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  refine BanachLattice.theorem_4_1_11 M.zero_le_vbar M.adp M.regular (fun σ => Or.inl
    ⟨M.concaveOn_T σ, M.c / M.vbarR, div_pos M.c_pos M.vbar_pos,
      (div_lt_one M.vbar_pos).2 (M.c_lt.trans M.w₁_lt_vbar), ?_⟩)
    (Or.inl BM.countablyDedekindComplete)
  have h0 : BanachLattice.extendIcc (M.adp.T σ) (0 : BM X) = M.Tfun σ 0 :=
    BanachLattice.extendIcc_apply (M.adp.T σ) ⟨0, le_rfl, M.zero_le_vbar⟩
  rw [h0]
  refine BM.le_def.2 fun x => ?_
  change 0 + M.c / M.vbarR * (M.vbarR - 0) ≤
    if σ.1 x then M.e.toFun x else M.cont 0 x
  rw [zero_add, sub_zero, div_mul_cancel₀ _ M.vbar_pos.ne']
  have hc := (M.cont_bounds ⟨le_rfl, M.zero_le_vbar⟩ x).1
  split_ifs
  · linarith [M.e_ge_w₁ x, M.c_lt]
  · exact hc

end NLDiscount

/-! ### Nonlinear expectations -/

/-- Job search with Kreps–Porteus expectations (§8.2.2). -/
structure KPSearch (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  w₁ : ℝ
  w₂ : ℝ
  w₁_lt : w₁ < w₂
  wage_mem : ∀ x, wage x ∈ Icc w₁ w₂
  /-- unemployment compensation -/
  c : ℝ
  c_pos : 0 < c
  c_lt : c < w₁
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  /-- the risk parameter `γ ≠ 1` -/
  γ : ℝ
  γ_ne : γ ≠ 1

namespace KPSearch

attribute [local instance] KPSearch.isMarkov

variable (M : KPSearch X)

theorem p_ne : 1 - M.γ ≠ 0 := sub_ne_zero.2 M.γ_ne.symm

/-- The Kreps–Porteus operator `(Rv)(w) = (∫ v^{1−γ} dP(w, ·))^{1/(1−γ)}`. -/
noncomputable def Rf (v : X → ℝ) (x : X) : ℝ := pmean (M.P x) (1 - M.γ) v

/-- **Exercise 8.2.5** (p. 264): (i) `R` is order preserving and maps constants to themselves;
(ii) `R` is concave when `γ ≥ 0` and convex when `γ ≤ 0`, on positive bounded measurable
functions. -/
theorem exercise_8_2_5 :
    (∀ v w : X → ℝ, PosBdd v → PosBdd w → v ≤ w → M.Rf v ≤ M.Rf w) ∧
    (∀ k : ℝ, 0 < k → M.Rf (fun _ => k) = fun _ => k) ∧
    (0 ≤ M.γ → ∀ v w : X → ℝ, PosBdd v → PosBdd w → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ x, a * M.Rf v x + b * M.Rf w x ≤ M.Rf (a • v + b • w) x) ∧
    (M.γ ≤ 0 → ∀ v w : X → ℝ, PosBdd v → PosBdd w → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ x, M.Rf (a • v + b • w) x ≤ a * M.Rf v x + b * M.Rf w x) :=
  ⟨fun _ _ hv hw h x => pmean_mono M.p_ne hv hw h, fun _ hk => funext fun _ =>
    pmean_const M.p_ne hk, fun hγ _ _ hv hw _ _ ha hb hab _ =>
      pmean_concave M.p_ne (by linarith) hv hw ha hb hab,
    fun hγ _ _ hv hw _ _ ha hb hab _ => pmean_convex (by linarith) hv hw ha hb hab⟩

/-- `v̄ = (c + w₂)/(1 − β)`. -/
noncomputable def vbarR : ℝ := (M.c + M.w₂) / (1 - M.β)

/-- The order interval `V = [c, v̄]` in `bW`. -/
noncomputable def lo : BM X := BM.const M.c

noncomputable def vbar : BM X := BM.const M.vbarR

theorem one_sub_β_pos : 0 < 1 - M.β := sub_pos.2 M.β_lt_one

theorem w₂_pos : 0 < M.w₂ := M.c_pos.trans (M.c_lt.trans M.w₁_lt)

theorem vbar_eq : M.vbarR * (1 - M.β) = M.c + M.w₂ := div_mul_cancel₀ _ M.one_sub_β_pos.ne'

theorem c_lt_vbar : M.c < M.vbarR := by
  rw [vbarR, lt_div_iff₀ M.one_sub_β_pos]
  have := M.w₂_pos
  have := M.β_pos
  nlinarith [M.c_pos]

theorem lo_le_vbar : M.lo ≤ M.vbar := BM.le_def.2 fun _ => M.c_lt_vbar.le

/-- `e(w) = w/(1 − β)`. -/
noncomputable def efun (x : X) : ℝ := M.wage x / (1 - M.β)

theorem efun_bounds (x : X) :
    M.c + M.β * M.c ≤ M.efun x ∧ M.efun x ≤ M.vbarR - M.c / (1 - M.β) := by
  have h := M.wage_mem x
  have hp := M.one_sub_β_pos
  constructor
  · rw [efun, le_div_iff₀ hp]
    have h2 : (M.c + M.β * M.c) * (1 - M.β) ≤ M.c := by nlinarith [M.c_pos, sq_nonneg M.β]
    linarith [h.1, M.c_lt]
  · rw [efun, vbarR, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [h.2]) hp.le

theorem measurable_efun : Measurable M.efun := M.measurable_wage.div_const _

theorem posBdd {v : BM X} (hv : v ∈ Icc M.lo M.vbar) : PosBdd v.toFun :=
  ⟨v.measurable', M.c, M.vbarR, M.c_pos, fun x => ⟨BM.le_def.1 hv.1 x, BM.le_def.1 hv.2 x⟩⟩

theorem Rf_bounds {v : BM X} (hv : v ∈ Icc M.lo M.vbar) (x : X) :
    M.c ≤ M.Rf v.toFun x ∧ M.Rf v.toFun x ≤ M.vbarR := by
  obtain ⟨hmono, hconst, -, -⟩ := M.exercise_8_2_5
  have h1 := hmono _ _ (posBdd_const M.c_pos) (M.posBdd hv) (fun x => BM.le_def.1 hv.1 x) x
  have h2 := hmono _ _ (M.posBdd hv) (posBdd_const (M.c_pos.trans M.c_lt_vbar))
    (fun x => BM.le_def.1 hv.2 x) x
  rw [hconst _ M.c_pos] at h1
  rw [hconst _ (M.c_pos.trans M.c_lt_vbar)] at h2
  exact ⟨h1, h2⟩

theorem measurable_Rf (v : BM X) : Measurable (M.Rf v.toFun) :=
  (measurable_markovOp M.P (v.measurable'.pow_const _)).pow_const _

/-- The value of `T_σ v`: `σe + (1 − σ)(c + βRv)`. -/
noncomputable def Tval (σ : StopPolicy X) (v : BM X) (x : X) : ℝ :=
  if σ.1 x then M.efun x else M.c + M.β * M.Rf v.toFun x

theorem Tval_bounds (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc M.lo M.vbar) (x : X) :
    M.c ≤ M.Tval σ v x ∧ M.Tval σ v x ≤ M.vbarR := by
  have he := M.efun_bounds x
  have hR := M.Rf_bounds hv x
  have hβ := M.β_pos
  have hp := M.one_sub_β_pos
  have hcp : 0 < M.c / (1 - M.β) := div_pos M.c_pos hp
  have hv1 := M.vbar_eq
  unfold Tval
  split_ifs
  · constructor <;> nlinarith [M.c_pos]
  · constructor <;> nlinarith [M.c_pos, M.w₂_pos]

/-- `T_σ` on `V = [c, v̄]`. -/
noncomputable def Tfun (σ : StopPolicy X) (v : Icc M.lo M.vbar) : Icc M.lo M.vbar :=
  ⟨⟨M.Tval σ v, Measurable.ite (σ.2 (measurableSet_singleton true))
      (M.measurable_wage.div_const _) (measurable_const.add (measurable_const.mul
        (M.measurable_Rf v))),
    ⟨M.vbarR, fun x => by
      have h := M.Tval_bounds σ v.2 x
      rw [abs_le]
      constructor <;> linarith [M.c_pos]⟩⟩,
    BM.le_def.2 fun x => (M.Tval_bounds σ v.2 x).1, BM.le_def.2 fun x => (M.Tval_bounds σ v.2 x).2⟩

/-- The Kreps–Porteus job search ADP `(V, 𝕋)` of §8.2.2. -/
noncomputable def adp : ADP (Icc M.lo M.vbar) (StopPolicy X) where
  T := M.Tfun
  mono σ v w h := BM.le_def.2 fun x => by
    change M.Tval σ v x ≤ M.Tval σ w x
    unfold Tval
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (M.exercise_8_2_5.1 _ _ (M.posBdd v.2)
        (M.posBdd w.2) (fun y => BM.le_def.1 h y) x) M.β_pos.le)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem regular : M.adp.Regular := fun v => ⟨acceptWhere (s := M.efun)
    (h := fun x => M.c + M.β * M.Rf v.1.toFun x) M.measurable_efun
    (measurable_const.add (measurable_const.mul (M.measurable_Rf v))),
  fun τ => BM.le_def.2 fun x => by
    change M.Tval τ v x ≤ M.Tval _ v x
    unfold Tval
    rw [acceptWhere_apply]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _⟩

theorem extendIcc_eq (σ : StopPolicy X) {v : BM X} (hv : v ∈ Icc M.lo M.vbar) :
    BanachLattice.extendIcc (M.adp.T σ) v = ⟨M.Tval σ v, (M.Tfun σ ⟨v, hv⟩).1.measurable',
      (M.Tfun σ ⟨v, hv⟩).1.bdd'⟩ :=
  BanachLattice.extendIcc_apply (M.adp.T σ) ⟨v, hv⟩

/-- §8.2.2 (p. 264): for every `γ ≠ 1`, the policy operators satisfy Du's conditions — concave
with `T_σ c ≥ c + ε(v̄ − c)` when `γ ≥ 0`, convex with `T_σ v̄ ≤ v̄ − ε(v̄ − c)` when `γ ≤ 0` — so,
by Theorem 4.1.11, the fundamental optimality properties hold and VFI, OPI and HPI converge. -/
theorem section_8_2_2 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  obtain ⟨-, -, hconc, hconv⟩ := M.exercise_8_2_5
  have hp := M.one_sub_β_pos
  have hβ := M.β_pos
  have hvc := M.c_lt_vbar
  have hv1 := M.vbar_eq
  have hcomb : ∀ {v w : BM X}, v ∈ Icc M.lo M.vbar → w ∈ Icc M.lo M.vbar → ∀ {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 → a • v + b • w ∈ Icc M.lo M.vbar :=
    fun hv hw _ _ ha hb hab => convex_Icc _ _ hv hw ha hb hab
  refine BanachLattice.theorem_4_1_11 M.lo_le_vbar M.adp M.regular (fun σ => ?_)
    (Or.inl BM.countablyDedekindComplete)
  rcases le_total 0 M.γ with hγ | hγ
  · -- concave case
    refine Or.inl ⟨⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩,
      M.β * M.c / (M.vbarR - M.c), div_pos (mul_pos hβ M.c_pos) (sub_pos.2 hvc), ?_, ?_⟩
    · rw [M.extendIcc_eq σ hv, M.extendIcc_eq σ hw, M.extendIcc_eq σ (hcomb hv hw ha hb hab)]
      refine BM.le_def.2 fun x => ?_
      change a * M.Tval σ v x + b * M.Tval σ w x ≤ M.Tval σ (a • v + b • w) x
      unfold Tval
      split_ifs
      · rw [← add_mul, hab, one_mul]
      · have h := hconc hγ _ _ (M.posBdd hv) (M.posBdd hw) a b ha hb hab x
        have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
        change a * (M.c + M.β * M.Rf v.toFun x) + b * (M.c + M.β * M.Rf w.toFun x) ≤
          M.c + M.β * M.Rf (a • v.toFun + b • w.toFun) x
        nlinarith
    · rw [div_lt_one (sub_pos.2 hvc)]
      nlinarith [M.c_pos, M.w₂_pos]
    · rw [M.extendIcc_eq σ ⟨le_rfl, M.lo_le_vbar⟩]
      refine BM.le_def.2 fun x => ?_
      change M.c + M.β * M.c / (M.vbarR - M.c) * (M.vbarR - M.c) ≤ M.Tval σ M.lo x
      rw [div_mul_cancel₀ _ (sub_pos.2 hvc).ne']
      have he := M.efun_bounds x
      have hR := M.Rf_bounds ⟨le_rfl, M.lo_le_vbar⟩ x
      unfold Tval
      split_ifs
      · exact he.1
      · nlinarith
  · -- convex case
    have hm : 0 < min (M.c / (1 - M.β)) M.w₂ := lt_min (div_pos M.c_pos hp) M.w₂_pos
    have hmlt : min (M.c / (1 - M.β)) M.w₂ < M.vbarR - M.c := by
      refine (min_le_left _ _).trans_lt ?_
      rw [div_lt_iff₀ hp]
      nlinarith [M.c_pos, M.w₂_pos, M.c_lt, M.w₁_lt]
    refine Or.inr ⟨⟨convex_Icc _ _, fun v hv w hw a b ha hb hab => ?_⟩,
      min (M.c / (1 - M.β)) M.w₂ / (M.vbarR - M.c), div_pos hm (sub_pos.2 hvc),
      (div_lt_one (sub_pos.2 hvc)).2 hmlt, ?_⟩
    · rw [M.extendIcc_eq σ hv, M.extendIcc_eq σ hw, M.extendIcc_eq σ (hcomb hv hw ha hb hab)]
      refine BM.le_def.2 fun x => ?_
      change M.Tval σ (a • v + b • w) x ≤ a * M.Tval σ v x + b * M.Tval σ w x
      unfold Tval
      split_ifs
      · rw [← add_mul, hab, one_mul]
      · have h := hconv hγ _ _ (M.posBdd hv) (M.posBdd hw) a b ha hb hab x
        have : a * M.c + b * M.c = M.c := by rw [← add_mul, hab, one_mul]
        change M.c + M.β * M.Rf (a • v.toFun + b • w.toFun) x ≤
          a * (M.c + M.β * M.Rf v.toFun x) + b * (M.c + M.β * M.Rf w.toFun x)
        nlinarith
    · rw [M.extendIcc_eq σ ⟨M.lo_le_vbar, le_rfl⟩]
      refine BM.le_def.2 fun x => ?_
      change M.Tval σ M.vbar x ≤
        M.vbarR - min (M.c / (1 - M.β)) M.w₂ / (M.vbarR - M.c) * (M.vbarR - M.c)
      rw [div_mul_cancel₀ _ (sub_pos.2 hvc).ne']
      have he := M.efun_bounds x
      have hR := M.Rf_bounds ⟨M.lo_le_vbar, le_rfl⟩ x
      unfold Tval
      split_ifs
      · linarith [min_le_left (M.c / (1 - M.β)) M.w₂]
      · have : M.c + M.β * M.vbarR = M.vbarR - M.w₂ := by nlinarith
        nlinarith [min_le_right (M.c / (1 - M.β)) M.w₂]

end KPSearch

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search with separation

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.4 (pp. 269–272).

Offers are `P`-Markov on a state space `X` with offer `w(x) ∈ [0, M]`; a match dissolves with
probability `α`. Eliminating the employed value with (8.41), `v_e = h + γPv_u`,
`h = w/(1 − β(1 − α))`, `γ = αβ/(1 − β(1 − α))`, the policy operators on `bW` are (8.42),
`T_σ v = σ(h + γPv) + (1 − σ)(c + βPv)`.

* (8.41): solving (8.39) for the employed value.
* The policy (8.43) is greedy, so `(bW, 𝕋)` is regular.
* **Exercise 8.2.12**: each `T_σ` is a contraction of modulus `β ∨ γ < 1`.
* **Proposition 8.2.2**: well-posedness, the fundamental optimality properties, and convergence
  of VFI, OPI and HPI (Theorem 3.1.5).
* **Exercise 8.2.13**: (8.46) has a unique solution `v*_u ∈ bW`, computed by iterating the
  Bellman operator from any starting point; with `v*_e = h + γPv*_u`, the pair solves
  (8.44)–(8.45), and it is the only solution in `bW × bW`.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- (8.41): `v_e = w + β[α s + (1 − α)v_e]` iff `v_e = (w + αβ s)/(1 − β(1 − α))`, for `0 ≤ α`
and `0 ≤ β < 1`. -/
theorem eq_8_41 {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (w s ve : ℝ) :
    ve = w + β * (α * s + (1 - α) * ve) ↔ ve = (w + α * β * s) / (1 - β * (1 - α)) := by
  have hd : 0 < 1 - β * (1 - α) := by nlinarith
  rw [eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

variable {X : Type*} [MeasurableSpace X]

/-- Job search with separation (§8.2.4). -/
structure Separation (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- the offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  /-- the upper bound of offers -/
  M : ℝ
  wage_mem : ∀ x, wage x ∈ Icc 0 M
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  /-- the separation probability -/
  α : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1

namespace Separation

attribute [local instance] Separation.isMarkov

variable (S : Separation X)

theorem denom_pos : 0 < 1 - S.β * (1 - S.α) := by
  nlinarith [S.β_pos, S.β_lt_one, S.α_pos, S.α_lt_one]

/-- `h(w) = w/(1 − β(1 − α))`. -/
noncomputable def h (x : X) : ℝ := S.wage x / (1 - S.β * (1 - S.α))

/-- `γ = αβ/(1 − β(1 − α))`. -/
noncomputable def γ : ℝ := S.α * S.β / (1 - S.β * (1 - S.α))

theorem γ_nonneg : 0 ≤ S.γ := div_nonneg (mul_pos S.α_pos S.β_pos).le S.denom_pos.le

theorem γ_lt_one : S.γ < 1 := by
  rw [γ, div_lt_one S.denom_pos]
  nlinarith [S.β_lt_one, S.α_pos]

/-- The Markov operator `P` on `bW`. -/
noncomputable def Pop : BM X →L[ℝ] BM X := BM.markovCLM S.P

theorem abs_Pop_sub_le (v w : BM X) (x : X) :
    |(S.Pop v).toFun x - (S.Pop w).toFun x| ≤ ‖v - w‖ := by
  have h1 : (S.Pop v).toFun x - (S.Pop w).toFun x = (S.Pop (v - w)).toFun x := by
    rw [map_sub, BM.sub_apply]
  rw [h1, Pop, BM.markovCLM_apply]
  exact abs_markovOp_le S.P (BM.abs_le_norm (v - w)) x

/-- The stop value `h + γPv` and the continuation value `c + βPv`. -/
noncomputable def stopV (v : BM X) (x : X) : ℝ := S.h x + S.γ * (S.Pop v).toFun x

noncomputable def contV (v : BM X) (x : X) : ℝ := S.c + S.β * (S.Pop v).toFun x

/-- (8.42): `T_σ v = σ(h + γPv) + (1 − σ)(c + βPv)`. -/
noncomputable def T (σ : StopPolicy X) (v : BM X) : BM X :=
  ⟨fun x => if σ.1 x then S.stopV v x else S.contV v x,
    Measurable.ite (σ.2 (measurableSet_singleton true))
      ((S.measurable_wage.div_const _).add (measurable_const.mul (S.Pop v).measurable'))
      (measurable_const.add (measurable_const.mul (S.Pop v).measurable')), by
    refine ⟨S.M / (1 - S.β * (1 - S.α)) + S.γ * ‖S.Pop v‖ + |S.c| + S.β * ‖S.Pop v‖,
      fun x => ?_⟩
    have hw := S.wage_mem x
    have hP := BM.abs_le_norm (S.Pop v) x
    have hh : |S.h x| ≤ S.M / (1 - S.β * (1 - S.α)) := by
      rw [h, abs_div, abs_of_pos S.denom_pos, abs_of_nonneg hw.1]
      exact div_le_div_of_nonneg_right hw.2 S.denom_pos.le
    have hγ := S.γ_nonneg
    have hβ := S.β_pos.le
    split_ifs
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hγ]
      nlinarith [abs_nonneg S.c, mul_nonneg hβ (norm_nonneg (S.Pop v)),
        mul_le_mul_of_nonneg_left hP hγ]
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos S.β_pos]
      nlinarith [abs_nonneg (S.h x), mul_nonneg hγ (norm_nonneg (S.Pop v)),
        mul_le_mul_of_nonneg_left hP hβ, (abs_nonneg (S.h x)).trans hh]⟩

theorem T_apply (σ : StopPolicy X) (v : BM X) (x : X) :
    (S.T σ v).toFun x = if σ.1 x then S.stopV v x else S.contV v x := rfl

/-- The ADP `(bW, 𝕋)` of (8.42). -/
noncomputable def adp : ADP (BM X) (StopPolicy X) where
  T := S.T
  mono σ v w hvw := BM.le_def.2 fun x => by
    have hP := BM.le_def.1 ((BM.markovCLM_isPositive S.P).mono hvw) x
    change (if σ.1 x then S.stopV v x else S.contV v x) ≤
      (if σ.1 x then S.stopV w x else S.contV w x)
    split_ifs
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hP S.γ_nonneg)
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hP S.β_pos.le)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy (8.43): accept when `h + γPv ≥ c + βPv`. -/
noncomputable def accept (v : BM X) : StopPolicy X :=
  acceptWhere (s := S.stopV v) (h := S.contV v)
    ((S.measurable_wage.div_const _).add (measurable_const.mul (S.Pop v).measurable'))
    (measurable_const.add (measurable_const.mul (S.Pop v).measurable'))

/-- (8.43): the policy `𝟙{h + γPv ≥ c + βPv}` is `v`-greedy, and `Tv = (h + γPv) ∨ (c + βPv)`. -/
theorem accept_isGreedy (v : BM X) :
    S.adp.IsGreedy v (S.accept v) ∧
      ∀ x, (S.adp.bellman v).toFun x = max (S.stopV v x) (S.contV v x) := by
  have hval : ∀ x, (S.adp.T (S.accept v) v).toFun x = max (S.stopV v x) (S.contV v x) :=
    fun x => acceptWhere_apply _ _ x
  have hg : S.adp.IsGreedy v (S.accept v) := fun τ => BM.le_def.2 fun x => by
    rw [hval]
    change (if τ.1 x then S.stopV v x else S.contV v x) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : S.adp.bellman v = S.adp.T (S.accept v) v :=
    le_antisymm (hg _) (S.adp.isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun x => by rw [heq, hval]⟩

theorem regular : S.adp.Regular := fun v => ⟨_, (S.accept_isGreedy v).1⟩

/-- **Exercise 8.2.12** (p. 271): each `T_σ` is a contraction of modulus `λ = β ∨ γ ∈ (0, 1)`. -/
theorem exercise_8_2_12 :
    0 < max S.β S.γ ∧ max S.β S.γ < 1 ∧
      ∀ σ v w, dist (S.adp.T σ v) (S.adp.T σ w) ≤ max S.β S.γ * dist v w := by
  refine ⟨lt_max_of_lt_left S.β_pos, max_lt S.β_lt_one S.γ_lt_one, fun σ v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg (le_max_of_le_left S.β_pos.le) (norm_nonneg _)) fun x => ?_
  have hP := S.abs_Pop_sub_le v w x
  change |(if σ.1 x then S.stopV v x else S.contV v x) -
    (if σ.1 x then S.stopV w x else S.contV w x)| ≤ _
  split_ifs
  · rw [stopV, stopV, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.γ_nonneg]
    exact mul_le_mul (le_max_right _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)
  · rw [contV, contV, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos S.β_pos]
    exact mul_le_mul (le_max_left _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)

/-- **Proposition 8.2.2** (p. 271): `(bW, 𝕋)` is well-posed, (i) the fundamental optimality
properties hold, and (ii) VFI, OPI and HPI all converge (Exercise 8.2.12 and Theorem 3.1.5). -/
theorem proposition_8_2_2 :
    ∃ hw : S.adp.WellPosed, S.adp.FundamentalOptimality hw ∧ ∃ vstar,
      S.adp.VFIGeometric univ vstar ∧
        ∀ g, S.adp.IsSelector g → S.adp.OPIConverges g vstar ∧ S.adp.HPIConverges hw g vstar := by
  obtain ⟨h0, h1, hT⟩ := S.exercise_8_2_12
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive h0.le h1 hT
    (V₀ := univ) ⟨isClosed_univ, fun v _ => S.regular v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨_, hFO, vstar, hgeo, hconv S.regular⟩

/-- The Bellman operator of (8.46): `v ↦ (h + γPv) ∨ (c + βPv)`. -/
theorem bellman_apply (v : BM X) (x : X) :
    (S.adp.bellman v).toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x) :=
  (S.accept_isGreedy v).2 x

theorem bellman_contracting : ContractingWith ⟨max S.β S.γ, (lt_max_of_lt_left S.β_pos).le⟩
    S.adp.bellman := by
  obtain ⟨-, h1, -⟩ := S.exercise_8_2_12
  refine ⟨h1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg (le_max_of_le_left S.β_pos.le) (norm_nonneg _)) fun x => ?_
  have hP := S.abs_Pop_sub_le v w x
  rw [BM.sub_apply, S.bellman_apply, S.bellman_apply]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.γ_nonneg]
    exact mul_le_mul (le_max_right _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)
  · rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_pos S.β_pos]
    exact mul_le_mul (le_max_left _ _) hP (abs_nonneg _) (le_max_of_le_left S.β_pos.le)

/-- **Exercise 8.2.13** (p. 272): (8.46) has a unique solution `v*_u ∈ bW`; iterating the Bellman
operator from any `v ∈ bW` converges to it (a convergent method), and `v*_e = h + γPv*_u`. The pair
`(v*_e, v*_u)` solves (8.44)–(8.45) and is the only solution in `bW × bW`. -/
theorem exercise_8_2_13 :
    ∃ vu : BM X, (∀ x, vu.toFun x = max (S.h x + S.γ * (S.Pop vu).toFun x)
        (S.c + S.β * (S.Pop vu).toFun x)) ∧
      (∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
        (S.c + S.β * (S.Pop v).toFun x)) → v = vu) ∧
      (∀ v, Tendsto (fun n => S.adp.bellman^[n] v) atTop (𝓝 vu)) ∧
      ∀ ve u : BM X, ((∀ x, u.toFun x = max (ve.toFun x) (S.c + S.β * (S.Pop u).toFun x)) ∧
        ∀ x, ve.toFun x = S.wage x + S.β * (S.α * (S.Pop u).toFun x + (1 - S.α) * ve.toFun x)) ↔
        (u = vu ∧ ∀ x, ve.toFun x = S.h x + S.γ * (S.Pop vu).toFun x) := by
  have hc := S.bellman_contracting
  set vu := ContractingWith.fixedPoint _ hc
  have hfix : S.adp.bellman vu = vu := ContractingWith.fixedPoint_isFixedPt hc
  have hsol : ∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x)) ↔ S.adp.bellman v = v := fun v =>
    ⟨fun h => BM.ext fun x => by rw [S.bellman_apply, h x], fun h x => by
      rw [← S.bellman_apply, h]⟩
  have huniq : ∀ v : BM X, (∀ x, v.toFun x = max (S.h x + S.γ * (S.Pop v).toFun x)
      (S.c + S.β * (S.Pop v).toFun x)) → v = vu := fun v h =>
    ContractingWith.fixedPoint_unique hc ((hsol v).1 h)
  -- (8.45) is (8.41) with `s = Pv_u`
  have h841 : ∀ (ve u : BM X) (x : X), ve.toFun x =
      S.wage x + S.β * (S.α * (S.Pop u).toFun x + (1 - S.α) * ve.toFun x) ↔
      ve.toFun x = S.h x + S.γ * (S.Pop u).toFun x := fun ve u x => by
    rw [eq_8_41 S.α_pos.le S.β_pos.le S.β_lt_one, h, γ]
    constructor <;> intro hx <;> rw [hx] <;> field_simp
  refine ⟨vu, (hsol vu).2 hfix, huniq, fun v => ContractingWith.tendsto_iterate_fixedPoint hc v,
    fun ve u => ⟨fun ⟨h44, h45⟩ => ?_, fun ⟨hu, hve⟩ => ?_⟩⟩
  · have hve : ∀ x, ve.toFun x = S.h x + S.γ * (S.Pop u).toFun x := fun x => (h841 ve u x).1 (h45 x)
    have hu : u = vu := huniq u fun x => by rw [h44 x, hve x]
    subst hu
    exact ⟨rfl, hve⟩
  · subst hu
    refine ⟨fun x => ?_, fun x => (h841 ve vu x).2 (hve x)⟩
    rw [hve x]
    exact (hsol vu).2 hfix x

end Separation

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Job search with learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.2.3 (pp. 264–269), with
Proposition A.5.34 (p. 391).

Offers are drawn iid from one of two densities `f`, `g` on `ℝ`, positive on `(0, M)` and zero
elsewhere (Assumption 8.2.1); the worker's belief that the density is `f` updates by Bayes' rule
`κ(w, π) = πf(w)/(πf(w) + (1 − π)g(w))` (8.32), and `φ_π = πf + (1 − π)g`.

The state space is taken to be `[0, M] × [0, 1]` rather than `(0, M) × (0, 1)`: the closed
intervals are invariant (`κ(w', π) ∈ [0, 1]` for `π ∈ [0, 1]`), and offers outside `(0, M)` carry
no weight.

* **Exercises 8.2.6–8.2.7**: the ADP on `b([0, M] × [0, 1])`; the stopping policy is greedy and
  the Bellman equation is (8.33).
* **Exercises 8.2.8–8.2.9**: the reservation wage operator `T̂` (8.36) is a contraction of
  modulus `β` on `b[0, 1]` and maps `bc[0, 1]` into itself.
* **Proposition A.5.34** (monotone likelihood ratio implies first order stochastic dominance),
  **Exercise 8.2.10** (mixtures are ordered in `α`) and **Proposition 8.2.1**: under the monotone
  likelihood ratio property, the optimal reservation wage `ω*` is increasing in `π`.
* **Exercise 8.2.11**: the Beta(4, 2) and Beta(2, 4) densities of (8.38) have the monotone
  likelihood ratio property.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-! ### Monotone likelihood ratios and stochastic dominance -/

/-- The monotone likelihood ratio property on `(0, M)`: `g/f` is decreasing, written without
division as `g(w₂)f(w₁) ≤ g(w₁)f(w₂)` for `w₁ ≤ w₂`. -/
def IsMLR (f g : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ w₁ ∈ Ioo 0 M, ∀ w₂ ∈ Ioo 0 M, w₁ ≤ w₂ → g w₂ * f w₁ ≤ g w₁ * f w₂

/-- Two densities positive on `(0, M)` and vanishing elsewhere (Assumption 8.2.1). -/
structure TwoDensities (M : ℝ) where
  M_pos : 0 < M
  f : ℝ → ℝ
  g : ℝ → ℝ
  measurable_f : Measurable f
  measurable_g : Measurable g
  integral_f : ∫ w, f w = 1
  integral_g : ∫ w, g w = 1
  f_pos : ∀ w ∈ Ioo 0 M, 0 < f w
  g_pos : ∀ w ∈ Ioo 0 M, 0 < g w
  f_zero : ∀ w ∉ Ioo 0 M, f w = 0
  g_zero : ∀ w ∉ Ioo 0 M, g w = 0

namespace TwoDensities

variable {M : ℝ} (D : TwoDensities M)

theorem f_nonneg (w : ℝ) : 0 ≤ D.f w := by
  by_cases h : w ∈ Ioo 0 M
  · exact (D.f_pos w h).le
  · rw [D.f_zero w h]

theorem g_nonneg (w : ℝ) : 0 ≤ D.g w := by
  by_cases h : w ∈ Ioo 0 M
  · exact (D.g_pos w h).le
  · rw [D.g_zero w h]

theorem integrable_f : Integrable D.f :=
  Integrable.of_integral_ne_zero (by rw [D.integral_f]; exact one_ne_zero)

theorem integrable_g : Integrable D.g :=
  Integrable.of_integral_ne_zero (by rw [D.integral_g]; exact one_ne_zero)

theorem integrable_mul {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ} (hC : ∀ w, |u w| ≤ C)
    {h : ℝ → ℝ} (hh : Integrable h) : Integrable (fun w => u w * h w) :=
  hh.bdd_mul hum.aestronglyMeasurable (Eventually.of_forall fun w => by
    rw [Real.norm_eq_abs]; exact hC w)

/-- **Proposition A.5.34** (p. 391), for densities: if `g/f` is decreasing on `(0, M)`, then
`G ⪯_F F`: `∫ ug ≤ ∫ uf` for every bounded measurable `u` increasing on `(0, M)`. The densities
cross once: `f < g` on an initial segment of `(0, M)` and `f ≥ g` after it. -/
theorem proposition_A_5_34 (hmlr : IsMLR D.f D.g M) {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ}
    (hC : ∀ w, |u w| ≤ C) (hmono : MonotoneOn u (Ioo 0 M)) :
    ∫ w, u w * D.g w ≤ ∫ w, u w * D.f w := by
  classical
  -- the set where `f < g` is an initial segment of `(0, M)`
  set A := {w ∈ Ioo 0 M | D.f w < D.g w}
  have hdown : ∀ w ∈ A, ∀ w' ∈ Ioo 0 M, w' ≤ w → w' ∈ A := by
    rintro w ⟨hw, hfg⟩ w' hw' hle
    refine ⟨hw', not_le.1 fun hge => ?_⟩
    have h1 := hmlr w' hw' w hw hle
    have hf' := D.f_pos w' hw'
    have : D.g w * D.f w' ≤ D.f w' * D.f w := h1.trans (mul_le_mul_of_nonneg_right hge
      (D.f_pos w hw).le)
    have : D.g w ≤ D.f w := by nlinarith
    linarith
  have hbdd : BddAbove (insert 0 A) := ⟨M, by
    rintro x (rfl | hx)
    · exact D.M_pos.le
    · exact hx.1.2.le⟩
  set x0 := sSup (insert 0 A)
  have hleft : ∀ w ∈ Ioo 0 M, w < x0 → D.f w < D.g w := by
    intro w hw hlt
    obtain ⟨a, ha, hwa⟩ := exists_lt_of_lt_csSup (insert_nonempty 0 A) hlt
    rcases ha with rfl | ha
    · exact absurd hwa (not_lt.2 hw.1.le)
    · exact (hdown a ha w hw hwa.le).2
  have hright : ∀ w ∈ Ioo 0 M, x0 < w → D.g w ≤ D.f w := by
    intro w hw hlt
    by_contra h
    have : w ∈ A := ⟨hw, not_le.1 h⟩
    exact absurd (le_csSup hbdd (mem_insert_of_mem 0 this)) (not_le.2 hlt)
  -- a constant separating the values of `u` on either side of `x0`
  set L := {w ∈ Ioo 0 M | w < x0}
  set k : ℝ := if L.Nonempty then sSup (u '' L) else -C
  have hkL : ∀ w ∈ L, u w ≤ k := by
    intro w hw
    have hne : L.Nonempty := ⟨w, hw⟩
    simp only [k, hne, ↓reduceIte]
    exact le_csSup ⟨C, by rintro _ ⟨y, -, rfl⟩; exact (le_abs_self _).trans (hC y)⟩ ⟨w, hw, rfl⟩
  have hkR : ∀ w ∈ Ioo 0 M, x0 < w → k ≤ u w := by
    intro w hw hlt
    by_cases hne : L.Nonempty
    · simp only [k, hne, ↓reduceIte]
      refine csSup_le (hne.image u) ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hmono hy.1 hw (hy.2.trans hlt).le
    · simp only [k, hne, ↓reduceIte]
      exact neg_le_of_abs_le (hC w)
  -- the integrand `(u − k)(f − g)` is nonnegative off `x0`
  have hpt : ∀ w, w ≠ x0 → 0 ≤ (u w - k) * (D.f w - D.g w) := by
    intro w hne
    by_cases hw : w ∈ Ioo 0 M
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hkL w ⟨hw, hlt⟩))
          (sub_nonpos.2 (hleft w hw hlt).le)
      · exact mul_nonneg (sub_nonneg.2 (hkR w hw hgt)) (sub_nonneg.2 (hright w hw hgt))
    · rw [D.f_zero w hw, D.g_zero w hw, sub_self, mul_zero]
  have hae : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ x0 := by
    rw [ae_iff]
    simp
  have hint : 0 ≤ ∫ w, (u w - k) * (D.f w - D.g w) :=
    integral_nonneg_of_ae (hae.mono fun w hw => hpt w hw)
  have hiuf := integrable_mul hum hC D.integrable_f
  have hiug := integrable_mul hum hC D.integrable_g
  have h1 : Integrable (fun w => u w * D.f w - u w * D.g w) := hiuf.sub hiug
  have h2 : Integrable (fun w => D.f w - D.g w) := D.integrable_f.sub D.integrable_g
  have h3 : Integrable (fun w => k * (D.f w - D.g w)) := h2.const_mul k
  have e1 : ∫ w, (u w - k) * (D.f w - D.g w) =
      (∫ w, (u w * D.f w - u w * D.g w)) - ∫ w, k * (D.f w - D.g w) := by
    rw [← integral_sub h1 h3]
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only; ring)
  have e2 : ∫ w, (u w * D.f w - u w * D.g w) = (∫ w, u w * D.f w) - ∫ w, u w * D.g w :=
    integral_sub hiuf hiug
  have e3 : ∫ w, k * (D.f w - D.g w) = 0 := by
    rw [integral_const_mul, integral_sub D.integrable_f D.integrable_g, D.integral_f,
      D.integral_g, sub_self, mul_zero]
  rw [e1, e2, e3, sub_zero] at hint
  exact sub_nonneg.1 hint

end TwoDensities

/-- **Exercise 8.2.10** (p. 269): if `G ⪯_F F` and `H_α = αF + (1 − α)G`, then `α₁ ≤ α₂` implies
`H_{α₁} ⪯_F H_{α₂}`. -/
theorem exercise_8_2_10 {F G : Measure ℝ} [IsFiniteMeasure F] [IsFiniteMeasure G]
    (h : FOSDle G F) {α₁ α₂ : ℝ} (h0 : 0 ≤ α₁) (h12 : α₁ ≤ α₂) (h1 : α₂ ≤ 1) :
    FOSDle (ENNReal.ofReal α₁ • F + ENNReal.ofReal (1 - α₁) • G)
      (ENNReal.ofReal α₂ • F + ENNReal.ofReal (1 - α₂) • G) := by
  intro u hu hum hub
  obtain ⟨C, hC⟩ := hub
  have hi : ∀ μ : Measure ℝ, IsFiniteMeasure μ → Integrable u μ := fun μ _ =>
    Integrable.of_bound hum.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hmix : ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      ∫ x, u x ∂(ENNReal.ofReal α • F + ENNReal.ofReal (1 - α) • G) =
        α * ∫ x, u x ∂F + (1 - α) * ∫ x, u x ∂G := fun α ha0 ha1 => by
    rw [integral_add_measure ((hi F inferInstance).smul_measure ENNReal.ofReal_ne_top)
      ((hi G inferInstance).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul, smul_eq_mul]
  rw [hmix α₁ h0 (h12.trans h1), hmix α₂ (h0.trans h12) h1]
  have := h u hu hum ⟨C, hC⟩
  nlinarith

/-- The Beta(4, 2) density `20w³(1 − w)` on `(0, 1)` (8.38). -/
def betaF (w : ℝ) : ℝ := 20 * w ^ 3 * (1 - w)

/-- The Beta(2, 4) density `20w(1 − w)³` on `(0, 1)` (8.38). -/
def betaG (w : ℝ) : ℝ := 20 * w * (1 - w) ^ 3

/-- **Exercise 8.2.11** (p. 269): the densities (8.38) have the monotone likelihood ratio
property: `g/f = ((1 − w)/w)²` is decreasing on `(0, 1)`. -/
theorem exercise_8_2_11 : IsMLR betaF betaG 1 := by
  rintro w₁ ⟨h10, h11⟩ w₂ ⟨h20, h21⟩ h12
  have key : (1 - w₂) * w₁ ≤ (1 - w₁) * w₂ := by nlinarith
  have hsq : ((1 - w₂) * w₁) ^ 2 ≤ ((1 - w₁) * w₂) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) h10.le) key 2
  have hpos : 0 ≤ 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) := by
    have : 0 ≤ 1 - w₁ := by linarith
    have : 0 ≤ 1 - w₂ := by linarith
    positivity
  calc betaG w₂ * betaF w₁ = 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) * ((1 - w₂) * w₁) ^ 2 := by
        unfold betaF betaG; ring
    _ ≤ 400 * w₁ * w₂ * (1 - w₁) * (1 - w₂) * ((1 - w₁) * w₂) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hpos
    _ = betaG w₁ * betaF w₂ := by unfold betaF betaG; ring

/-! ### Beliefs -/

namespace TwoDensities

variable {M : ℝ} (D : TwoDensities M)

/-- The estimated offer density `φ_π = πf + (1 − π)g`. -/
def φ (π w : ℝ) : ℝ := π * D.f w + (1 - π) * D.g w

/-- Bayes' rule (8.32): `κ(w, π) = πf(w)/(πf(w) + (1 − π)g(w))`. -/
noncomputable def κ (w π : ℝ) : ℝ := π * D.f w / D.φ π w

/-- The updated belief `κ(w, π)`, as a point of `[0, 1]`. -/
noncomputable def pκ (w π : ℝ) : Icc (0 : ℝ) 1 := projIcc 0 1 zero_le_one (D.κ w π)

/-- The offer `w`, as a point of `[0, M]`. -/
noncomputable def pw (w : ℝ) : Icc (0 : ℝ) M := projIcc 0 M D.M_pos.le w

theorem φ_nonneg {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : 0 ≤ D.φ π w :=
  add_nonneg (mul_nonneg hπ.1 (D.f_nonneg w)) (mul_nonneg (sub_nonneg.2 hπ.2) (D.g_nonneg w))

theorem φ_le {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : D.φ π w ≤ D.f w + D.g w := by
  unfold φ
  nlinarith [D.f_nonneg w, D.g_nonneg w, hπ.1, hπ.2, mul_nonneg hπ.1 (D.g_nonneg w),
    mul_nonneg (sub_nonneg.2 hπ.2) (D.f_nonneg w)]

theorem φ_pos {w : ℝ} (hw : w ∈ Ioo 0 M) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    0 < D.φ π w := by
  have hf := D.f_pos w hw
  have hg := D.g_pos w hw
  have h1 : 0 ≤ 1 - π := sub_nonneg.2 hπ.2
  unfold φ
  rcases le_total (D.f w) (D.g w) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h h1]
  · nlinarith [mul_le_mul_of_nonneg_left h hπ.1]

theorem φ_zero {w : ℝ} (hw : w ∉ Ioo 0 M) (π : ℝ) : D.φ π w = 0 := by
  rw [φ, D.f_zero w hw, D.g_zero w hw]
  ring

theorem measurable_φ : Measurable (fun p : ℝ × ℝ => D.φ p.1 p.2) :=
  (measurable_fst.mul (D.measurable_f.comp measurable_snd)).add
    ((measurable_const.sub measurable_fst).mul (D.measurable_g.comp measurable_snd))

theorem measurable_κ : Measurable (fun p : ℝ × ℝ => D.κ p.2 p.1) :=
  (measurable_fst.mul (D.measurable_f.comp measurable_snd)).div D.measurable_φ

theorem measurable_pκ : Measurable (fun p : ℝ × ℝ => D.pκ p.2 p.1) :=
  continuous_projIcc.measurable.comp D.measurable_κ

theorem measurable_pw : Measurable D.pw :=
  (continuous_projIcc (a := (0 : ℝ)) (b := M) (h := D.M_pos.le)).measurable

theorem integrable_φ (π : ℝ) : Integrable (D.φ π) :=
  (D.integrable_f.const_mul π).add (D.integrable_g.const_mul (1 - π))

theorem integral_φ (π : ℝ) : ∫ w, D.φ π w = 1 := by
  unfold φ
  rw [integral_add (D.integrable_f.const_mul π) (D.integrable_g.const_mul (1 - π)),
    integral_const_mul, integral_const_mul, D.integral_f, D.integral_g]
  ring

/-- `∫ u φ_π = π ∫ uf + (1 − π) ∫ ug`. -/
theorem integral_mul_φ {u : ℝ → ℝ} (hum : Measurable u) {C : ℝ} (hC : ∀ w, |u w| ≤ C)
    (π : ℝ) :
    ∫ w, u w * D.φ π w = π * (∫ w, u w * D.f w) + (1 - π) * ∫ w, u w * D.g w := by
  have hf := integrable_mul hum hC D.integrable_f
  have hg := integrable_mul hum hC D.integrable_g
  have e : (fun w => u w * D.φ π w) = fun w => π * (u w * D.f w) + (1 - π) * (u w * D.g w) :=
    funext fun w => by simp only [φ]; ring
  rw [e, integral_add (hf.const_mul π) (hg.const_mul (1 - π)), integral_const_mul,
    integral_const_mul]

/-- Integration against `φ_π` is an average: `|∫ u φ_π| ≤ C` when `|u| ≤ C`. -/
theorem abs_integral_mul_φ_le {u : ℝ → ℝ} {C : ℝ} (hC : ∀ w, |u w| ≤ C) {π : ℝ}
    (hπ : π ∈ Set.Icc (0 : ℝ) 1) : |∫ w, u w * D.φ π w| ≤ C := by
  have h := norm_integral_le_of_norm_le (f := fun w => u w * D.φ π w)
    ((D.integrable_φ π).const_mul C) (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (D.φ_nonneg hπ w)]
      exact mul_le_mul_of_nonneg_right (hC w) (D.φ_nonneg hπ w))
  rwa [integral_const_mul, D.integral_φ, mul_one, Real.norm_eq_abs] at h

theorem κ_mem {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) : D.κ w π ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (mul_nonneg hπ.1 (D.f_nonneg w)) (D.φ_nonneg hπ w), ?_⟩
  refine div_le_one_of_le₀ ?_ (D.φ_nonneg hπ w)
  unfold φ
  linarith [mul_nonneg (sub_nonneg.2 hπ.2) (D.g_nonneg w)]

/-- The posterior `κ(w, π)` is increasing in the prior `π`. -/
theorem κ_mono_prior (w : ℝ) {π₁ π₂ : ℝ} (h1 : π₁ ∈ Set.Icc (0 : ℝ) 1)
    (h2 : π₂ ∈ Set.Icc (0 : ℝ) 1) (h12 : π₁ ≤ π₂) : D.κ w π₁ ≤ D.κ w π₂ := by
  by_cases hw : w ∈ Ioo 0 M
  · rw [κ, κ, div_le_div_iff₀ (D.φ_pos hw h1) (D.φ_pos hw h2), φ, φ]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h12) (D.f_nonneg w)) (D.g_nonneg w)]
  · rw [κ, κ, D.φ_zero hw, D.φ_zero hw, div_zero, div_zero]

/-- Under the monotone likelihood ratio property the posterior `κ(w, π)` is increasing in the
offer `w`. -/
theorem κ_mono_offer (hmlr : IsMLR D.f D.g M) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1)
    {w₁ w₂ : ℝ} (hw₁ : w₁ ∈ Ioo 0 M) (hw₂ : w₂ ∈ Ioo 0 M) (h12 : w₁ ≤ w₂) :
    D.κ w₁ π ≤ D.κ w₂ π := by
  rw [κ, κ, div_le_div_iff₀ (D.φ_pos hw₁ hπ) (D.φ_pos hw₂ hπ), φ, φ]
  have h := hmlr w₁ hw₁ w₂ hw₂ h12
  nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hπ.1 (sub_nonneg.2 hπ.2))]

theorem continuous_κ (w : ℝ) : Continuous fun π : Set.Icc (0 : ℝ) 1 => D.κ w π := by
  by_cases hw : w ∈ Ioo 0 M
  · change Continuous fun π : Set.Icc (0 : ℝ) 1 =>
      (π : ℝ) * D.f w / ((π : ℝ) * D.f w + (1 - (π : ℝ)) * D.g w)
    exact (continuous_subtype_val.mul continuous_const).div
      ((continuous_subtype_val.mul continuous_const).add
        ((continuous_const.sub continuous_subtype_val).mul continuous_const))
      fun π => (D.φ_pos hw π.2).ne'
  · have : (fun π : Set.Icc (0 : ℝ) 1 => D.κ w π) = fun _ => 0 :=
      funext fun π => by rw [κ, D.φ_zero hw, div_zero]
    rw [this]
    exact continuous_const

end TwoDensities

/-! ### The learning model -/

/-- The job search model with learning (§8.2.3.1). -/
structure LearningSearch (M : ℝ) where
  /-- the two candidate offer densities -/
  D : TwoDensities M
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

/-- The state space `[0, M] × [0, 1]` of offers and beliefs. -/
abbrev LState (M : ℝ) := Set.Icc (0 : ℝ) M × Set.Icc (0 : ℝ) 1

namespace LearningSearch

variable {M : ℝ} (L : LearningSearch M)

theorem one_sub_β_pos : 0 < 1 - L.β := sub_pos.2 L.β_lt_one

/-- The continuation value `c + β ∫ v(w', κ(w', π)) φ_π(w') dw'`. -/
noncomputable def contR (v : BM (LState M)) (π : ℝ) : ℝ :=
  L.c + L.β * ∫ w, v.toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w

theorem measurable_integrand (v : BM (LState M)) :
    Measurable (fun p : ℝ × ℝ => v.toFun (L.D.pw p.2, L.D.pκ p.2 p.1) * L.D.φ p.1 p.2) :=
  (v.measurable'.comp ((L.D.measurable_pw.comp measurable_snd).prodMk L.D.measurable_pκ)).mul
    L.D.measurable_φ

theorem measurable_section (v : BM (LState M)) (π : ℝ) :
    Measurable (fun w => v.toFun (L.D.pw w, L.D.pκ w π)) :=
  v.measurable'.comp (L.D.measurable_pw.prodMk
    (L.D.measurable_pκ.comp (measurable_const.prodMk measurable_id)))

theorem integrable_section (v : BM (LState M)) (π : ℝ) :
    Integrable (fun w => v.toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w) :=
  TwoDensities.integrable_mul (L.measurable_section v π) (fun _ => BM.abs_le_norm v _)
    (L.D.integrable_φ π)

theorem measurable_contR (v : BM (LState M)) : Measurable (L.contR v) :=
  measurable_const.add (measurable_const.mul
    (L.measurable_integrand v).stronglyMeasurable.integral_prod_right'.measurable)

theorem abs_contR_le (v : BM (LState M)) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    |L.contR v π| ≤ |L.c| + L.β * ‖v‖ := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left
    (L.D.abs_integral_mul_φ_le (fun _ => BM.abs_le_norm v _) hπ) L.β_pos.le

theorem abs_contR_sub_le (v w : BM (LState M)) {π : ℝ} (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    |L.contR v π - L.contR w π| ≤ L.β * ‖v - w‖ := by
  have h : L.contR v π - L.contR w π =
      L.β * ∫ x, (v - w).toFun (L.D.pw x, L.D.pκ x π) * L.D.φ π x := by
    rw [contR, contR, add_sub_add_left_eq_sub, ← mul_sub,
      ← integral_sub (L.integrable_section v π) (L.integrable_section w π)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [BM.sub_apply]; ring)
  rw [h, abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left
    (L.D.abs_integral_mul_φ_le (fun _ => BM.abs_le_norm (v - w) _) hπ) L.β_pos.le

theorem measurable_stop : Measurable (fun x : LState M => (x.1 : ℝ) / (1 - L.β)) :=
  (measurable_subtype_coe.comp measurable_fst).div_const _

theorem measurable_cont (v : BM (LState M)) : Measurable (fun x : LState M => L.contR v x.2) :=
  (L.measurable_contR v).comp (measurable_subtype_coe.comp measurable_snd)

/-- The policy operator `T_σ v = σ w/(1 − β) + (1 − σ)[c + β ∫ v(w', κ(w', π)) φ_π(w') dw']`. -/
noncomputable def T (σ : StopPolicy (LState M)) (v : BM (LState M)) : BM (LState M) :=
  ⟨fun x => if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2,
    Measurable.ite (σ.2 (measurableSet_singleton true)) L.measurable_stop (L.measurable_cont v), by
    refine ⟨M / (1 - L.β) + (|L.c| + L.β * ‖v‖), fun x => ?_⟩
    have h1 := L.one_sub_β_pos
    have hs : |(x.1 : ℝ) / (1 - L.β)| ≤ M / (1 - L.β) := by
      rw [abs_div, abs_of_pos h1, abs_of_nonneg x.1.2.1]
      exact div_le_div_of_nonneg_right x.1.2.2 h1.le
    have hc := L.abs_contR_le v x.2.2
    have hM : 0 ≤ M / (1 - L.β) := div_nonneg L.D.M_pos.le h1.le
    have hcn : 0 ≤ |L.c| + L.β * ‖v‖ :=
      add_nonneg (abs_nonneg _) (mul_nonneg L.β_pos.le (norm_nonneg _))
    split_ifs
    · linarith
    · linarith⟩

/-- The ADP `(V, 𝕋)` of §8.2.3.1, on `V = b([0, M] × [0, 1])`. -/
noncomputable def adp : ADP (BM (LState M)) (StopPolicy (LState M)) where
  T := L.T
  mono σ v w hvw := BM.le_def.2 fun x => by
    have hc : L.contR v x.2 ≤ L.contR w x.2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_mono (L.integrable_section v _)
        (L.integrable_section w _) fun y => mul_le_mul_of_nonneg_right (BM.le_def.1 hvw _)
          (L.D.φ_nonneg x.2.2 y)) L.β_pos.le)
    change (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) ≤
      (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR w x.2)
    split_ifs
    · exact le_rfl
    · exact hc
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- The policy of Exercise 8.2.6: accept when `w/(1 − β) ≥ c + β ∫ v(w', κ(w', π)) φ_π(w') dw'`. -/
noncomputable def accept (v : BM (LState M)) : StopPolicy (LState M) :=
  acceptWhere L.measurable_stop (L.measurable_cont v)

theorem accept_isGreedy (v : BM (LState M)) :
    L.adp.IsGreedy v (L.accept v) ∧
      ∀ x, (L.adp.bellman v).toFun x = max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) := by
  have hval : ∀ x, (L.adp.T (L.accept v) v).toFun x =
      max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) := fun x => acceptWhere_apply _ _ x
  have hg : L.adp.IsGreedy v (L.accept v) := fun τ => BM.le_def.2 fun x => by
    rw [hval]
    change (if τ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) ≤ _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have heq : L.adp.bellman v = L.adp.T (L.accept v) v :=
    le_antisymm (hg _) (L.adp.isGreedy_greedy ⟨_, hg⟩ _)
  exact ⟨hg, fun x => by rw [heq, hval]⟩

/-- **Exercise 8.2.6** (p. 266): the policy `σ = 𝟙{w/(1 − β) ≥ c + β ∫ v(w', κ(w', π)) φ_π}` is
`v`-greedy. -/
theorem exercise_8_2_6 (v : BM (LState M)) : L.adp.IsGreedy v (L.accept v) :=
  (L.accept_isGreedy v).1

/-- **Exercise 8.2.7** (p. 266): the Bellman operator is (8.33),
`(Tv)(w, π) = max{w/(1 − β), c + β ∫ v(w', κ(w', π)) φ_π(w') dw'}`. -/
theorem exercise_8_2_7 (v : BM (LState M)) (x : LState M) :
    (L.adp.bellman v).toFun x = max ((x.1 : ℝ) / (1 - L.β)) (L.contR v x.2) :=
  (L.accept_isGreedy v).2 x

theorem regular : L.adp.Regular := fun v => ⟨_, L.exercise_8_2_6 v⟩

theorem T_contraction (σ : StopPolicy (LState M)) (v w : BM (LState M)) :
    dist (L.adp.T σ v) (L.adp.T σ w) ≤ L.β * dist v w := by
  rw [dist_eq_norm, dist_eq_norm]
  refine BM.norm_le (mul_nonneg L.β_pos.le (norm_nonneg _)) fun x => ?_
  change |(if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR v x.2) -
    (if σ.1 x then (x.1 : ℝ) / (1 - L.β) else L.contR w x.2)| ≤ _
  split_ifs
  · rw [sub_self, abs_zero]
    exact mul_nonneg L.β_pos.le (norm_nonneg _)
  · exact L.abs_contR_sub_le v w x.2.2

/-- The learning ADP is well-posed, the fundamental optimality properties hold, and VFI, OPI and
HPI converge: each `T_σ` is a contraction of modulus `β` (Theorem 3.1.5). -/
theorem optimality :
    ∃ hw : L.adp.WellPosed, L.adp.FundamentalOptimality hw ∧ ∃ vstar,
      L.adp.VFIGeometric univ vstar ∧
        ∀ g, L.adp.IsSelector g → L.adp.OPIConverges g vstar ∧ L.adp.HPIConverges hw g vstar := by
  obtain ⟨hFO, vstar, -, hgeo, hconv⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive L.β_pos.le
    L.β_lt_one L.T_contraction (V₀ := univ)
    ⟨isClosed_univ, fun v _ => L.regular v, mapsTo_univ _ _⟩ univ_nonempty
  exact ⟨_, hFO, vstar, hgeo, hconv L.regular⟩

/-! ### The reservation wage operator -/

/-- The integrand `max{w', ω[κ(w', π)]}` of (8.36), with the offer read in `[0, M]` (this changes
nothing where `φ_π > 0`; see `That_eq`). -/
noncomputable def G (ω : BM (Set.Icc (0 : ℝ) 1)) (π w : ℝ) : ℝ :=
  max (L.D.pw w : ℝ) (ω.toFun (L.D.pκ w π))

theorem measurable_Gφ (ω : BM (Set.Icc (0 : ℝ) 1)) :
    Measurable (fun p : ℝ × ℝ => L.G ω p.1 p.2 * L.D.φ p.1 p.2) :=
  ((measurable_subtype_coe.comp (L.D.measurable_pw.comp measurable_snd)).max
    (ω.measurable'.comp L.D.measurable_pκ)).mul L.D.measurable_φ

theorem measurable_G (ω : BM (Set.Icc (0 : ℝ) 1)) (π : ℝ) : Measurable (L.G ω π) :=
  (measurable_subtype_coe.comp L.D.measurable_pw).max
    (ω.measurable'.comp (L.D.measurable_pκ.comp (measurable_const.prodMk measurable_id)))

theorem abs_G_le (ω : BM (Set.Icc (0 : ℝ) 1)) (π w : ℝ) : |L.G ω π w| ≤ M + ‖ω‖ := by
  have hw := (L.D.pw w).2
  refine (abs_max_le_max_abs_abs).trans (max_le ?_ ?_)
  · rw [abs_of_nonneg hw.1]
    linarith [norm_nonneg ω, hw.2]
  · linarith [BM.abs_le_norm ω (L.D.pκ w π), L.D.M_pos]

theorem integrable_Gφ (ω : BM (Set.Icc (0 : ℝ) 1)) (π : ℝ) :
    Integrable (fun w => L.G ω π w * L.D.φ π w) :=
  TwoDensities.integrable_mul (L.measurable_G ω π) (L.abs_G_le ω π) (L.D.integrable_φ π)

/-- The reservation wage operator (8.36),
`(T̂ω)(π) = (1 − β)c + β ∫ max{w', ω[κ(w', π)]} φ_π(w') dw'`, on `V̂ = b[0, 1]`. -/
noncomputable def That (ω : BM (Set.Icc (0 : ℝ) 1)) : BM (Set.Icc (0 : ℝ) 1) :=
  ⟨fun π => (1 - L.β) * L.c + L.β * ∫ w, L.G ω π w * L.D.φ π w,
    measurable_const.add (measurable_const.mul
      ((L.measurable_Gφ ω).stronglyMeasurable.integral_prod_right'.measurable.comp
        measurable_subtype_coe)), by
    refine ⟨|(1 - L.β) * L.c| + L.β * (M + ‖ω‖), fun π => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_pos L.β_pos]
    exact mul_le_mul_of_nonneg_left (L.D.abs_integral_mul_φ_le (L.abs_G_le ω π) π.2)
      L.β_pos.le⟩

theorem That_apply (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    (L.That ω).toFun π = (1 - L.β) * L.c + L.β * ∫ w, L.G ω π w * L.D.φ π w := rfl

/-- `T̂` is (8.36) as written: offers outside `(0, M)` carry no weight. -/
theorem That_eq (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    (L.That ω).toFun π =
      (1 - L.β) * L.c + L.β * ∫ w, max w (ω.toFun (L.D.pκ w π)) * L.D.φ π w := by
  rw [That_apply]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ Ioo 0 M
  · have : (L.D.pw w : ℝ) = w :=
      congrArg Subtype.val (projIcc_of_mem L.D.M_pos.le (Ioo_subset_Icc_self hw))
    simp only [G, this]
  · simp only [L.D.φ_zero hw, mul_zero]

theorem abs_That_sub_le (ω ω' : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    |(L.That ω).toFun π - (L.That ω').toFun π| ≤ L.β * dist ω ω' := by
  have h : (L.That ω).toFun π - (L.That ω').toFun π =
      L.β * ∫ w, (L.G ω π w - L.G ω' π w) * L.D.φ π w := by
    rw [That_apply, That_apply, add_sub_add_left_eq_sub, ← mul_sub,
      ← integral_sub (L.integrable_Gφ ω π) (L.integrable_Gφ ω' π)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only; ring)
  have hG : ∀ w, |L.G ω π w - L.G ω' π w| ≤ dist ω ω' := fun w => by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (BM.abs_sub_le_dist _ _ _))
    rw [sub_self, abs_zero]
    exact dist_nonneg
  rw [h, abs_mul, abs_of_pos L.β_pos]
  exact mul_le_mul_of_nonneg_left (L.D.abs_integral_mul_φ_le hG π.2) L.β_pos.le

/-- **Exercise 8.2.8** (p. 267): `T̂` is a contraction of modulus `β` on `V̂ = b[0, 1]`. -/
theorem exercise_8_2_8 :
    (∀ ω ω', dist (L.That ω) (L.That ω') ≤ L.β * dist ω ω') ∧
      ContractingWith ⟨L.β, L.β_pos.le⟩ L.That := by
  have h : ∀ ω ω', dist (L.That ω) (L.That ω') ≤ L.β * dist ω ω' := fun ω ω' =>
    BM.dist_le (mul_nonneg L.β_pos.le dist_nonneg) (L.abs_That_sub_le ω ω')
  exact ⟨h, L.β_lt_one, LipschitzWith.of_dist_le_mul h⟩

theorem That_contracting : ContractingWith ⟨L.β, L.β_pos.le⟩ L.That := L.exercise_8_2_8.2

/-- **Exercise 8.2.9** (p. 267): `T̂` maps `bc[0, 1]` into itself. -/
theorem exercise_8_2_9 {ω : BM (Set.Icc (0 : ℝ) 1)} (hω : Continuous ω.toFun) :
    Continuous (L.That ω).toFun := by
  refine continuous_const.add (continuous_const.mul (continuous_of_dominated
    (F := fun (π : Set.Icc (0 : ℝ) 1) w => L.G ω π w * L.D.φ π w)
    (bound := fun w => (M + ‖ω‖) * (L.D.f w + L.D.g w))
    (fun π => (L.integrable_Gφ ω π).aestronglyMeasurable)
    (fun π => Eventually.of_forall fun w => ?_)
    ((L.D.integrable_f.add L.D.integrable_g).const_mul _)
    (Eventually.of_forall fun w => ?_)))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (L.D.φ_nonneg π.2 w)]
    exact mul_le_mul (L.abs_G_le ω π w) (L.D.φ_le π.2 w) (L.D.φ_nonneg π.2 w)
      (add_nonneg L.D.M_pos.le (norm_nonneg ω))
  · exact (continuous_const.max (hω.comp (continuous_projIcc.comp (L.D.continuous_κ w)))).mul
      ((continuous_subtype_val.mul continuous_const).add
        ((continuous_const.sub continuous_subtype_val).mul continuous_const))

/-- The optimal reservation wage function `ω*`, the fixed point of `T̂`. -/
noncomputable def ωstar : BM (Set.Icc (0 : ℝ) 1) :=
  ContractingWith.fixedPoint L.That L.That_contracting

theorem That_ωstar : L.That L.ωstar = L.ωstar :=
  ContractingWith.fixedPoint_isFixedPt L.That_contracting

theorem tendstoUniformly_ωstar :
    TendstoUniformly (fun n => (L.That^[n] (BM.const 0)).toFun) L.ωstar.toFun atTop :=
  BM.tendstoUniformly_of_tendsto
    (ContractingWith.tendsto_iterate_fixedPoint L.That_contracting (BM.const 0))

/-- `ω*` is continuous: `T̂` preserves `bc[0, 1]` and uniform limits of continuous functions are
continuous. -/
theorem continuous_ωstar : Continuous L.ωstar.toFun := by
  have hit : ∀ n, Continuous (L.That^[n] (BM.const 0)).toFun := by
    intro n
    induction n with
    | zero => exact continuous_const
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact L.exercise_8_2_9 ih
  exact L.tendstoUniformly_ωstar.continuous (Eventually.of_forall hit).frequently

/-- The value `v_ω(w, π) = max{w, ω(π)}/(1 − β)` of a reservation wage function `ω`. -/
noncomputable def vOf (ω : BM (Set.Icc (0 : ℝ) 1)) : BM (LState M) :=
  ⟨fun x => max (x.1 : ℝ) (ω.toFun x.2) / (1 - L.β),
    ((measurable_subtype_coe.comp measurable_fst).max
      (ω.measurable'.comp measurable_snd)).div_const _,
    ⟨(M + ‖ω‖) / (1 - L.β), fun x => by
      have h1 := L.one_sub_β_pos
      rw [abs_div, abs_of_pos h1]
      refine div_le_div_of_nonneg_right ((abs_max_le_max_abs_abs).trans (max_le ?_ ?_)) h1.le
      · rw [abs_of_nonneg x.1.2.1]
        linarith [norm_nonneg ω, x.1.2.2]
      · linarith [BM.abs_le_norm ω x.2, L.D.M_pos]⟩⟩

/-- (8.34)–(8.35): the continuation value of `v_ω` is `(T̂ω)(π)/(1 − β)`. -/
theorem contR_vOf (ω : BM (Set.Icc (0 : ℝ) 1)) (π : Set.Icc (0 : ℝ) 1) :
    L.contR (L.vOf ω) π = (L.That ω).toFun π / (1 - L.β) := by
  have h1 := L.one_sub_β_pos
  have e : ∫ w, (L.vOf ω).toFun (L.D.pw w, L.D.pκ w π) * L.D.φ π w =
      (∫ w, L.G ω π w * L.D.φ π w) / (1 - L.β) := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun w => by
      simp only [vOf, G]
      ring)
  rw [contR, e, That_apply]
  field_simp

theorem abs_bellman_sub_le (v w : BM (LState M)) (x : LState M) :
    |(L.adp.bellman v).toFun x - (L.adp.bellman w).toFun x| ≤ L.β * dist v w := by
  rw [L.exercise_8_2_7, L.exercise_8_2_7, dist_eq_norm]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (L.abs_contR_sub_le v w x.2.2))
  rw [sub_self, abs_zero]
  exact mul_nonneg L.β_pos.le (norm_nonneg _)

theorem bellman_contracting : ContractingWith ⟨L.β, L.β_pos.le⟩ L.adp.bellman :=
  ⟨L.β_lt_one, LipschitzWith.of_dist_le_mul fun v w =>
    BM.dist_le (mul_nonneg L.β_pos.le dist_nonneg) (L.abs_bellman_sub_le v w)⟩

/-- §8.2.3.2: the Bellman equation (8.33) has exactly one solution in `V`, namely
`v*(w, π) = max{w, ω*(π)}/(1 − β)`, so `ω*` is the reservation wage of the optimal policy
(8.34): the worker accepts exactly when `w ≥ ω*(π)`. -/
theorem bellman_eq_iff (v : BM (LState M)) :
    L.adp.bellman v = v ↔ v = L.vOf L.ωstar := by
  have hfix : L.adp.bellman (L.vOf L.ωstar) = L.vOf L.ωstar := BM.ext fun x => by
    rw [L.exercise_8_2_7, L.contR_vOf, L.That_ωstar]
    exact max_div_div_right L.one_sub_β_pos.le _ _
  constructor
  · intro h
    exact (L.bellman_contracting.fixedPoint_unique' h hfix)
  · rintro rfl
    exact hfix

/-! ### Parametric monotonicity -/

/-- Under the monotone likelihood ratio property, `T̂` maps increasing functions to increasing
functions (the proof of Proposition 8.2.1). -/
theorem That_monotone (hmlr : IsMLR L.D.f L.D.g M) {ω : BM (Set.Icc (0 : ℝ) 1)}
    (hω : Monotone ω.toFun) : Monotone (L.That ω).toFun := by
  intro π₁ π₂ h12
  have h12' : (π₁ : ℝ) ≤ π₂ := h12
  rw [That_apply, That_apply]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ L.β_pos.le)
  -- `h(w', π) = ω[κ(w', π)]` is increasing in `π`
  have step1 : ∫ w, L.G ω π₁ w * L.D.φ π₁ w ≤ ∫ w, L.G ω π₂ w * L.D.φ π₁ w :=
    integral_mono (L.integrable_Gφ ω π₁)
      (TwoDensities.integrable_mul (L.measurable_G ω π₂) (L.abs_G_le ω π₂)
        (L.D.integrable_φ π₁)) fun w =>
      mul_le_mul_of_nonneg_right (max_le_max le_rfl (hω (monotone_projIcc zero_le_one
        (L.D.κ_mono_prior w π₁.2 π₂.2 h12'))))
        (L.D.φ_nonneg π₁.2 w)
  -- `w' ↦ max{w', h(w', π₂)}` is increasing on `(0, M)`, and `π ↦ φ_π` is `⪯_F`-isotone
  have hmono : MonotoneOn (L.G ω π₂) (Ioo 0 M) := fun w₁ hw₁ w₂ hw₂ hw12 =>
    max_le_max (monotone_projIcc L.D.M_pos.le hw12)
      (hω (monotone_projIcc zero_le_one (L.D.κ_mono_offer hmlr π₂.2 hw₁ hw₂ hw12)))
  have hA := L.D.proposition_A_5_34 hmlr (L.measurable_G ω π₂) (L.abs_G_le ω π₂) hmono
  have step2 : ∫ w, L.G ω π₂ w * L.D.φ π₁ w ≤ ∫ w, L.G ω π₂ w * L.D.φ π₂ w := by
    rw [L.D.integral_mul_φ (L.measurable_G ω π₂) (L.abs_G_le ω π₂),
      L.D.integral_mul_φ (L.measurable_G ω π₂) (L.abs_G_le ω π₂)]
    nlinarith [mul_nonneg (sub_nonneg.2 h12') (sub_nonneg.2 hA)]
  exact step1.trans step2

/-- **Proposition 8.2.1** (p. 269): if `f` and `g` have the monotone likelihood ratio property,
then the optimal reservation wage `ω*` is increasing in `π`. -/
theorem proposition_8_2_1 (hmlr : IsMLR L.D.f L.D.g M) : Monotone L.ωstar.toFun := by
  have hit : ∀ n, Monotone (L.That^[n] (BM.const 0)).toFun := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact L.That_monotone hmlr ih
  intro π₁ π₂ h12
  exact le_of_tendsto_of_tendsto' (L.tendstoUniformly_ωstar.tendsto_at π₁)
    (L.tendstoUniformly_ωstar.tendsto_at π₂) fun n => hit n h12

end LearningSearch

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Coase meets Bellman: optimality with negative discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.1 (pp. 273–281).

An agent faces a task of measure `x̂`; with `x` units left, effort `a` costs `c(a)` and leaves
`x − a`; losses are discounted by `δ > 1` (8.52). The cost `c` is strictly increasing, strictly
convex and continuously differentiable with `c(0) = 0 < c'(0)`.

The book assumes an `η ∈ (0, x̂)` with `c'(η) = δc'(0)` (8.53), which exists only when `x̂` is
large enough. We assume instead an `η > 0` with `c'(x) ≤ δc'(0) ⟺ x ≤ η` on `[0, x̂]`
(`η_spec`): (8.53) implies it (`η_spec_of_eq`), and such an `η` always exists (`η ≥ x̂` when
`c'(x̂) ≤ δc'(0)`), which is what makes the production chain results unconditional.

Value functions and policies are functions on `ℝ` that vanish off `[0, x̂]`.

* **Exercise 8.3.1**: the iterates (8.54) of `T_σ`.
* **Lemma 8.3.3**: each `T_σ` reaches its unique fixed point `v_σ` in `k₀ = ⌈x̂/η⌉` steps from
  every `v ∈ V`; hence `(V, 𝕋)` is order stable (Lemma A.5.19).
* **Lemma 8.3.4** (**Exercise 8.3.2**): every `v ∈ V₀` has a unique `v`-min-greedy policy, and it
  lies in `Σ`.
* **Lemma 8.3.5** (**Exercise 8.3.3**): `T` maps `V₀` into itself and `T^k v = v̄` for `k ≥ k₀`.
* **Theorem 8.3.6**: the fundamental min-optimality properties, `v̄ = v▿*`, the argmin
  characterisation of optimal policies, and uniqueness of the optimal policy.
* **Propositions 8.3.1 and 8.3.2** and **Definition 8.3.1**: the production chain equilibrium.
-/

open Set Function Filter Topology

namespace SargentStachurski.AdditionalApplications

/-- An order preserving map all of whose `k`-th iterates coincide is order stable, and every orbit
reaches its fixed point in `k` steps (Lemma A.5.19 in the form used by Lemma 8.3.3). -/
theorem orderStable_of_iterate_eq {V : Type*} [PartialOrder V] {S : V → V} (hS : Monotone S)
    {k : ℕ} (h : ∀ v w, S^[k] v = S^[k] w) (v₀ : V) :
    OrderStable S ∧ S (S^[k] v₀) = S^[k] v₀ ∧ (∀ w, S w = w → w = S^[k] v₀) ∧
      ∀ v n, k ≤ n → S^[n] v = S^[k] v₀ := by
  have hfix : S (S^[k] v₀) = S^[k] v₀ := by
    rw [← iterate_succ_apply' S k v₀, iterate_succ_apply, h (S v₀) v₀]
  have huniq : ∀ w, S w = w → w = S^[k] v₀ := fun w hw => by
    rw [← h w v₀]
    exact (iterate_fixed hw k).symm
  refine ⟨orderStable_of_up_down hfix (fun v hv => ?_) (fun v hv => ?_), hfix, huniq,
    fun v n hn => ?_⟩
  · rw [← h v v₀]
    exact hS.monotone_iterate_of_le_map hv (Nat.zero_le k)
  · rw [← h v v₀]
    exact hS.antitone_iterate_of_map_le hv (Nat.zero_le k)
  · rw [← Nat.sub_add_cancel hn, iterate_add_apply, h v v₀]
    exact iterate_fixed hfix _

/-- The negative-discounting problem of §8.3.1.2. -/
structure NegDiscount where
  /-- the effort cost -/
  c : ℝ → ℝ
  /-- the discount factor, `δ > 1` -/
  δ : ℝ
  one_lt_δ : 1 < δ
  /-- the size of the task -/
  xh : ℝ
  xh_pos : 0 < xh
  /-- the threshold below which the agent finishes the task at once -/
  η : ℝ
  η_pos : 0 < η
  c_zero : c 0 = 0
  differentiable : Differentiable ℝ c
  continuous_deriv : Continuous (deriv c)
  strictConvexOn : StrictConvexOn ℝ (Ici 0) c
  strictMonoOn : StrictMonoOn c (Ici 0)
  deriv_zero_pos : 0 < deriv c 0
  η_spec : ∀ x ∈ Set.Icc 0 xh, deriv c x ≤ δ * deriv c 0 ↔ x ≤ η

namespace NegDiscount

variable (N : NegDiscount)

theorem δ_pos : 0 < N.δ := one_pos.trans N.one_lt_δ

theorem zero_mem : (0 : ℝ) ∈ Set.Icc 0 N.xh := ⟨le_rfl, N.xh_pos.le⟩

theorem c_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : N.c a ≤ N.c b :=
  N.strictMonoOn.monotoneOn ha (ha.trans hab) hab

/-- (8.53) gives `η_spec`, since `c'` is strictly increasing. -/
theorem η_spec_of_eq {c : ℝ → ℝ} {δ xh η : ℝ} (hd : Differentiable ℝ c)
    (hc : StrictConvexOn ℝ (Ici 0) c) (hη : η ∈ Ioo 0 xh) (heq : deriv c η = δ * deriv c 0) :
    ∀ x ∈ Set.Icc 0 xh, deriv c x ≤ δ * deriv c 0 ↔ x ≤ η := fun x hx => by
  rw [← heq]
  exact (hc.strictMonoOn_deriv fun y _ => hd y).le_iff_le hx.1 (mem_Ici.2 hη.1.le)

/-- The number of steps `k₀ = ⌈x̂/η⌉` after which every policy has finished the task. -/
noncomputable def k0 : ℕ := ⌈N.xh / N.η⌉₊

/-- The policy set `Σ`: `0 ≤ σ(x) ≤ x`, `σ` and the effort `x − σ(x)` increasing, and
`σ(x) = 0 ⟺ x ≤ η`, all on `[0, x̂]`; `σ` vanishes off `[0, x̂]`. -/
@[ext]
structure Policy (N : NegDiscount) where
  /-- the remaining task after this period's effort -/
  σ : ℝ → ℝ
  mem : ∀ x ∈ Set.Icc 0 N.xh, σ x ∈ Set.Icc 0 x
  monotoneOn : MonotoneOn σ (Set.Icc 0 N.xh)
  monotoneOn_effort : MonotoneOn (fun x => x - σ x) (Set.Icc 0 N.xh)
  eq_zero_iff : ∀ x ∈ Set.Icc 0 N.xh, σ x = 0 ↔ x ≤ N.η
  zero_outside : ∀ x ∉ Set.Icc 0 N.xh, σ x = 0

namespace Policy

variable {N} (σ : N.Policy)

theorem mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) : σ.σ x ∈ Set.Icc 0 N.xh :=
  ⟨(σ.mem x hx).1, (σ.mem x hx).2.trans hx.2⟩

theorem iterate_mem {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (j : ℕ) :
    σ.σ^[j] x ∈ Set.Icc 0 N.xh := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    rw [iterate_succ_apply']
    exact σ.mem_Icc ih

theorem map_zero : σ.σ 0 = 0 := by
  have h := σ.mem 0 N.zero_mem
  exact le_antisymm h.2 h.1

/-- Effort is at least `η` above `η`: `σ(x) ≤ (x − η) ∨ 0`. -/
theorem le_max_sub {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) : σ.σ x ≤ max 0 (x - N.η) := by
  by_cases h : x ≤ N.η
  · rw [(σ.eq_zero_iff x hx).2 h]
    exact le_max_left _ _
  · have hlt := not_le.1 h
    have hη : N.η ∈ Set.Icc 0 N.xh := ⟨N.η_pos.le, hlt.le.trans hx.2⟩
    have h1 : N.η - σ.σ N.η ≤ x - σ.σ x := σ.monotoneOn_effort hη hx hlt.le
    rw [(σ.eq_zero_iff N.η hη).2 le_rfl, sub_zero] at h1
    exact le_max_of_le_right (by linarith)

theorem iterate_le {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (k : ℕ) :
    σ.σ^[k] x ≤ max 0 (x - k * N.η) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    refine (σ.le_max_sub (σ.iterate_mem hx k)).trans (max_le (le_max_left _ _) ?_)
    rcases le_total 0 (x - k * N.η) with h0 | h0
    · rw [max_eq_right h0] at ih
      refine le_max_of_le_right ?_
      push_cast
      linarith
    · rw [max_eq_left h0] at ih
      exact le_max_of_le_left (by linarith [N.η_pos])

/-- Every orbit of `σ` reaches `0` within `k₀ = ⌈x̂/η⌉` steps. -/
theorem iterate_eq_zero {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) {k : ℕ} (hk : N.k0 ≤ k) :
    σ.σ^[k] x = 0 := by
  have h1 : N.xh ≤ k * N.η := by
    have : N.xh / N.η ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.2 hk)
    rwa [div_le_iff₀ N.η_pos] at this
  have h2 := σ.iterate_le hx k
  rw [max_eq_left (by linarith [hx.2])] at h2
  exact le_antisymm h2 (σ.iterate_mem hx k).1

/-- `σ` is `1`-Lipschitz on `[0, x̂]`, by (ii) and (iii). -/
theorem abs_sub_le {x y : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (hy : y ∈ Set.Icc 0 N.xh) :
    |σ.σ x - σ.σ y| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · have h1 := σ.monotoneOn hx hy hxy
    have h2 : x - σ.σ x ≤ y - σ.σ y := σ.monotoneOn_effort hx hy hxy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := σ.monotoneOn hy hx hxy
    have h2 : y - σ.σ y ≤ x - σ.σ x := σ.monotoneOn_effort hy hx hxy
    rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (by linarith)]
    linarith

theorem continuousOn : ContinuousOn σ.σ (Set.Icc 0 N.xh) :=
  (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    exact σ.abs_sub_le hx hy).continuousOn

end Policy

/-- The policy `x ↦ (x − η) ∨ 0`. -/
noncomputable def ση : N.Policy where
  σ := (Set.Icc 0 N.xh).indicator fun x => max 0 (x - N.η)
  mem x hx := by
    rw [Set.indicator_of_mem hx]
    exact ⟨le_max_left _ _, max_le hx.1 (by linarith [N.η_pos])⟩
  monotoneOn x hx y hy hxy := by
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact max_le_max le_rfl (by linarith)
  monotoneOn_effort x hx y hy hxy := by
    have e : ∀ z, z - max 0 (z - N.η) = min z N.η := fun z => by
      rw [← min_sub_sub_left, sub_zero, sub_sub_cancel]
    change x - (Set.Icc 0 N.xh).indicator _ x ≤ y - (Set.Icc 0 N.xh).indicator _ y
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, e, e]
    exact min_le_min hxy le_rfl
  eq_zero_iff x hx := by
    rw [Set.indicator_of_mem hx, max_eq_left_iff, sub_nonpos]
  zero_outside x hx := Set.indicator_of_notMem hx _

/-- The value space `V`: functions increasing on `[0, x̂]`, vanishing at `0` and off `[0, x̂]`. -/
abbrev Val (N : NegDiscount) :=
  {v : ℝ → ℝ // MonotoneOn v (Set.Icc 0 N.xh) ∧ v 0 = 0 ∧ ∀ x ∉ Set.Icc 0 N.xh, v x = 0}

/-- `(T_σ v)(x) = c(x − σ(x)) + δv(σ(x))` on `[0, x̂]`. -/
noncomputable def Tfun (σ v : ℝ → ℝ) : ℝ → ℝ :=
  (Set.Icc 0 N.xh).indicator fun x => N.c (x - σ x) + N.δ * v (σ x)

/-- The policy operator `T_σ` on `V`. -/
noncomputable def T (σ : N.Policy) (v : N.Val) : N.Val :=
  ⟨N.Tfun σ.σ v.1, fun x hx y hy hxy => by
    rw [Tfun, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact add_le_add (N.c_mono (sub_nonneg.2 (σ.mem x hx).2) (σ.monotoneOn_effort hx hy hxy))
      (mul_le_mul_of_nonneg_left (v.2.1 (σ.mem_Icc hx) (σ.mem_Icc hy) (σ.monotoneOn hx hy hxy))
        N.δ_pos.le), by
    rw [Tfun, Set.indicator_of_mem N.zero_mem, σ.map_zero, sub_zero, v.2.2.1, mul_zero, add_zero,
      N.c_zero], fun x hx => Set.indicator_of_notMem hx _⟩

theorem T_apply (σ : N.Policy) (v : N.Val) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    (N.T σ v).1 x = N.c (x - σ.σ x) + N.δ * v.1 (σ.σ x) := by
  change N.Tfun σ.σ v.1 x = _
  exact Set.indicator_of_mem hx _

/-- The ADP `(V, 𝕋)` of §8.3.1.2. -/
noncomputable def adp : ADP N.Val N.Policy where
  T := N.T
  mono σ v w hvw := fun x => by
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · change (N.T σ v).1 x ≤ (N.T σ w).1 x
      rw [N.T_apply σ v hx, N.T_apply σ w hx]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvw _) N.δ_pos.le)
    · change (N.T σ v).1 x ≤ (N.T σ w).1 x
      rw [(N.T σ v).2.2.2 x hx, (N.T σ w).2.2.2 x hx]
  nonempty := ⟨N.ση⟩

/-- **Exercise 8.3.1** (p. 279), (8.54): `(T_σ^k v)(x) = ∑_{j<k} δ^j c(π(σ^j x)) + δ^k v(σ^k x)`,
with `π(x) = x − σ(x)`. -/
theorem exercise_8_3_1 (σ : N.Policy) (v : N.Val) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 N.xh) :
    ((N.adp.T σ)^[k] v).1 x = ∑ j ∈ Finset.range k,
      N.δ ^ j * N.c (σ.σ^[j] x - σ.σ (σ.σ^[j] x)) + N.δ ^ k * v.1 (σ.σ^[k] x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    change (N.T σ _).1 x = _
    rw [N.T_apply σ _ hx, ih (σ.mem_Icc hx), Finset.sum_range_succ', mul_add, Finset.mul_sum]
    simp only [← iterate_succ_apply, iterate_zero, id_eq, pow_zero, one_mul, ← mul_assoc,
      ← pow_succ']
    ring

theorem iterate_k0_eq (σ : N.Policy) (v w : N.Val) :
    (N.adp.T σ)^[N.k0] v = (N.adp.T σ)^[N.k0] w := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · rw [N.exercise_8_3_1 σ v _ hx, N.exercise_8_3_1 σ w _ hx, σ.iterate_eq_zero hx le_rfl,
      v.2.2.1, w.2.2.1]
  · rw [((N.adp.T σ)^[N.k0] v).2.2.2 x hx, ((N.adp.T σ)^[N.k0] w).2.2.2 x hx]

/-- The zero function, an element of `V`. -/
def zeroVal : N.Val := ⟨0, fun _ _ _ _ _ => le_rfl, rfl, fun _ _ => rfl⟩

/-- **Lemma 8.3.3** (p. 280): each `T_σ` has a unique fixed point `v_σ` in `V`, and
`T_σ^k v = v_σ` for all `v ∈ V` and `k ≥ k₀ = ⌈x̂/η⌉`. -/
theorem lemma_8_3_3 (σ : N.Policy) :
    ∃ vσ, N.adp.T σ vσ = vσ ∧ (∀ v, N.adp.T σ v = v → v = vσ) ∧
      ∀ v k, N.k0 ≤ k → (N.adp.T σ)^[k] v = vσ := by
  obtain ⟨-, hfix, huniq, hconv⟩ :=
    orderStable_of_iterate_eq (N.adp.mono σ) (N.iterate_k0_eq σ) N.zeroVal
  exact ⟨_, hfix, huniq, hconv⟩

/-- `(V, 𝕋)` is order stable (Lemma 8.3.3 and Lemma A.5.19). -/
theorem isOrderStable : N.adp.IsOrderStable := fun σ =>
  (orderStable_of_iterate_eq (N.adp.mono σ) (N.iterate_k0_eq σ) N.zeroVal).1

/-! ### The min-greedy policy (Lemma 8.3.4) -/

/-- `V₀`: convex and continuous on `[0, x̂]`, with `c'(0)x ≤ v(x) ≤ c(x)` there. -/
def InV0 (v : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc 0 N.xh) v ∧ ContinuousOn v (Set.Icc 0 N.xh) ∧
    ∀ x ∈ Set.Icc 0 N.xh, deriv N.c 0 * x ≤ v x ∧ v x ≤ N.c x

/-- The objective `g(x, y) = c(x − y) + δv(y)` of the Bellman equation. -/
def g (v : ℝ → ℝ) (x y : ℝ) : ℝ := N.c (x - y) + N.δ * v y

/-- The tangent at `0`: `c'(0)z ≤ c(z)` for `z ≥ 0`. -/
theorem tangent_zero {z : ℝ} (hz : 0 ≤ z) : deriv N.c 0 * z ≤ N.c z := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [mul_zero, N.c_zero]
  · have h := N.strictConvexOn.convexOn.deriv_le_slope (mem_Ici.2 le_rfl) (mem_Ici.2 hz.le) hz
      (N.differentiable 0)
    rwa [slope_def_field, N.c_zero, sub_zero, sub_zero, le_div_iff₀ hz] at h

/-- Strict convexity in the form `c(p) + c(q) < c(a) + c(b)` for `a < p < b`,
`p + q = a + b`. -/
theorem four_point_strict {a b p q : ℝ} (ha : 0 ≤ a) (hap : a < p) (hpb : p < b)
    (hs : p + q = a + b) : N.c p + N.c q < N.c a + N.c b := by
  have hab : a < b := hap.trans hpb
  have hba : 0 < b - a := sub_pos.2 hab
  set t := (b - p) / (b - a) with ht
  have ht0 : 0 < t := div_pos (sub_pos.2 hpb) hba
  have ht1 : 0 < 1 - t := by
    rw [ht, one_sub_div hba.ne']
    exact div_pos (by linarith) hba
  have hp : t * a + (1 - t) * b = p := by
    rw [ht]
    field_simp
    ring
  have hq : (1 - t) * a + t * b = q := by
    rw [ht, show q = a + b - p by linarith]
    field_simp
    ring
  have h1 := N.strictConvexOn.2 (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab.ne ht0 ht1
    (by ring)
  have h2 := N.strictConvexOn.2 (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab.ne ht1 ht0
    (by ring)
  simp only [smul_eq_mul] at h1 h2
  rw [hp] at h1
  rw [hq] at h2
  linarith

/-- Convexity in the form `v(p) + v(q) ≤ v(a) + v(b)` for `a ≤ p, q ≤ b`, `p + q = a + b`. -/
theorem four_point {v : ℝ → ℝ} (hv : ConvexOn ℝ (Set.Icc 0 N.xh) v) {a b p q : ℝ}
    (ha : a ∈ Set.Icc 0 N.xh) (hb : b ∈ Set.Icc 0 N.xh) (hap : a ≤ p) (hpb : p ≤ b)
    (haq : a ≤ q) (hqb : q ≤ b) (hs : p + q = a + b) : v p + v q ≤ v a + v b := by
  rcases (hap.trans hpb).eq_or_lt with hab | hab
  · have hp : p = a := by linarith
    have hq : q = a := by linarith
    rw [hp, hq, ← hab]
  · have hba : 0 < b - a := sub_pos.2 hab
    set t := (b - p) / (b - a) with ht
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hpb) hba.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, one_sub_div hba.ne']
      exact div_nonneg (by linarith) hba.le
    have hp : t * a + (1 - t) * b = p := by
      rw [ht]
      field_simp
      ring
    have hq : (1 - t) * a + t * b = q := by
      rw [ht, show q = a + b - p by linarith]
      field_simp
      ring
    have h1 := hv.2 ha hb ht0 ht1 (by ring)
    have h2 := hv.2 ha hb ht1 ht0 (by ring)
    simp only [smul_eq_mul] at h1 h2
    rw [hp] at h1
    rw [hq] at h2
    linarith

theorem v_zero {v : ℝ → ℝ} (hv : N.InV0 v) : v 0 = 0 := by
  have h := hv.2.2 0 N.zero_mem
  rw [mul_zero, N.c_zero] at h
  exact le_antisymm h.2 h.1

theorem exists_min {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    ∃ y ∈ Set.Icc 0 x, IsMinOn (N.g v x) (Set.Icc 0 x) y := by
  have hc : ContinuousOn (fun y => N.c (x - y) + N.δ * v y) (Set.Icc 0 x) :=
    (N.differentiable.continuous.comp (continuous_const.sub continuous_id)).continuousOn.add
      (continuousOn_const.mul (hv.2.1.mono (Icc_subset_Icc le_rfl hx.2)))
  exact isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hx.1) hc

/-- The minimiser of `g(x, ·)` on `[0, x]` is unique: `g(x, ·)` is strictly convex. -/
theorem unique_min {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc 0 x) (h₂ : y₂ ∈ Set.Icc 0 x) (hm₁ : IsMinOn (N.g v x) (Set.Icc 0 x) y₁)
    (hm₂ : IsMinOn (N.g v x) (Set.Icc 0 x) y₂) : y₁ = y₂ := by
  by_contra hne
  wlog h : y₁ < y₂ generalizing y₁ y₂
  · exact this h₂ h₁ hm₂ hm₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne))
  have hm : (y₁ + y₂) / 2 ∈ Set.Icc 0 x := ⟨by linarith [h₁.1], by linarith [h₂.2]⟩
  have hc := N.strictConvexOn.2 (mem_Ici.2 (sub_nonneg.2 h₁.2)) (mem_Ici.2 (sub_nonneg.2 h₂.2))
    (by intro e; exact hne (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hv' := hv.1.2 ⟨h₁.1, h₁.2.trans hx.2⟩ ⟨h₂.1, h₂.2.trans hx.2⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc hv'
  have e1 : 1 / 2 * (x - y₁) + 1 / 2 * (x - y₂) = x - (y₁ + y₂) / 2 := by ring
  have e2 : 1 / 2 * y₁ + 1 / 2 * y₂ = (y₁ + y₂) / 2 := by ring
  rw [e1] at hc
  rw [e2] at hv'
  have a1 := isMinOn_iff.1 hm₁ _ hm
  have a2 := isMinOn_iff.1 hm₁ _ h₂
  have a3 := isMinOn_iff.1 hm₂ _ h₁
  simp only [g] at a1 a2 a3
  nlinarith [N.δ_pos]

/-- A minimiser of `g(x, ·)` on `[0, x]`. -/
noncomputable def greedyFun (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  Classical.epsilon fun y => y ∈ Set.Icc 0 x ∧ IsMinOn (N.g v x) (Set.Icc 0 x) y

theorem greedy_spec {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    N.greedyFun v x ∈ Set.Icc 0 x ∧ IsMinOn (N.g v x) (Set.Icc 0 x) (N.greedyFun v x) := by
  obtain ⟨y, hy, hm⟩ := N.exists_min hv hx
  exact Classical.epsilon_spec (p := fun y => y ∈ Set.Icc 0 x ∧
    IsMinOn (N.g v x) (Set.Icc 0 x) y) ⟨y, hy, hm⟩

/-- (ii): the minimiser is increasing, since `g` has strictly decreasing differences. -/
theorem greedyFun_monotoneOn {v : ℝ → ℝ} (hv : N.InV0 v) :
    MonotoneOn (N.greedyFun v) (Set.Icc 0 N.xh) := by
  intro x₁ hx₁ x₂ hx₂ h12
  rcases h12.eq_or_lt with rfl | hlt
  · exact le_rfl
  by_contra hcon
  have hyx := not_le.1 hcon
  obtain ⟨s₁, m₁⟩ := N.greedy_spec hv hx₁
  obtain ⟨s₂, m₂⟩ := N.greedy_spec hv hx₂
  have hA := isMinOn_iff.1 m₁ (N.greedyFun v x₂) ⟨s₂.1, hyx.le.trans s₁.2⟩
  have hB := isMinOn_iff.1 m₂ (N.greedyFun v x₁) ⟨s₁.1, s₁.2.trans h12⟩
  have hC := N.four_point_strict (a := x₁ - N.greedyFun v x₁) (b := x₂ - N.greedyFun v x₂)
    (p := x₁ - N.greedyFun v x₂) (q := x₂ - N.greedyFun v x₁) (sub_nonneg.2 s₁.2)
    (by linarith) (by linarith) (by ring)
  simp only [g] at hA hB
  linarith

/-- (iii): the effort `x − σ(x)` is increasing, since `v` is convex and the minimiser unique. -/
theorem greedyFun_effort {v : ℝ → ℝ} (hv : N.InV0 v) :
    MonotoneOn (fun x => x - N.greedyFun v x) (Set.Icc 0 N.xh) := by
  intro x₁ hx₁ x₂ hx₂ h12
  change x₁ - N.greedyFun v x₁ ≤ x₂ - N.greedyFun v x₂
  rcases h12.eq_or_lt with rfl | hlt
  · exact le_rfl
  by_contra hcon
  have hax := not_le.1 hcon
  obtain ⟨s₁, m₁⟩ := N.greedy_spec hv hx₁
  obtain ⟨s₂, m₂⟩ := N.greedy_spec hv hx₂
  set y₁ := N.greedyFun v x₁
  set y₂ := N.greedyFun v x₂
  have hz₁ : x₁ - (x₂ - y₂) ∈ Set.Icc 0 x₁ := ⟨by linarith [s₁.1], by linarith [s₂.2]⟩
  have hz₂ : x₂ - (x₁ - y₁) ∈ Set.Icc 0 x₂ := ⟨by linarith [s₁.1], by linarith [s₁.2]⟩
  have hA := isMinOn_iff.1 m₁ _ hz₁
  have hB := isMinOn_iff.1 m₂ _ hz₂
  have hC := N.four_point hv.1 (a := y₁) (b := y₂) (p := x₁ - (x₂ - y₂)) (q := x₂ - (x₁ - y₁))
    ⟨s₁.1, s₁.2.trans hx₁.2⟩ ⟨s₂.1, s₂.2.trans hx₂.2⟩ (by linarith) (by linarith)
    (by linarith) (by linarith) (by ring)
  simp only [g, sub_sub_cancel] at hA hB
  have hδ := mul_le_mul_of_nonneg_left hC N.δ_pos.le
  -- `x₁ − (x₂ − y₂)` is also a minimiser at `x₁`
  have hmin : IsMinOn (N.g v x₁) (Set.Icc 0 x₁) (x₁ - (x₂ - y₂)) := isMinOn_iff.2 fun y hy => by
    have := isMinOn_iff.1 m₁ y hy
    simp only [g, sub_sub_cancel] at this ⊢
    nlinarith
  have := N.unique_min hv hx₁ hz₁ s₁ hmin m₁
  linarith

/-- (iv): the minimiser vanishes exactly when `x ≤ η`. -/
theorem greedyFun_eq_zero_iff {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ}
    (hx : x ∈ Set.Icc 0 N.xh) : N.greedyFun v x = 0 ↔ x ≤ N.η := by
  obtain ⟨s, m⟩ := N.greedy_spec hv hx
  have hv0 := N.v_zero hv
  constructor
  · intro h0
    by_contra hxη
    have hxη' := not_le.1 hxη
    have hx0 : 0 < x := N.η_pos.trans hxη'
    have hc' : N.δ * deriv N.c 0 < deriv N.c x := not_le.1 (mt (N.η_spec x hx).1 hxη)
    -- `c'(x − y) > δc'(y)` for small `y > 0`
    have hev : ∀ᶠ y in 𝓝 (0 : ℝ), N.δ * deriv N.c y < deriv N.c (x - y) :=
      ContinuousAt.eventually_lt (f := fun y => N.δ * deriv N.c y)
        (g := fun y => deriv N.c (x - y)) (continuous_const.mul N.continuous_deriv).continuousAt
        (N.continuous_deriv.comp (continuous_const.sub continuous_id)).continuousAt
        (by simpa using hc')
    have hlt : ∀ᶠ y in 𝓝 (0 : ℝ), y < x := Iio_mem_nhds hx0
    obtain ⟨y, ⟨h1, h2⟩, h3⟩ :=
      (((hev.and hlt).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have h3' : 0 < y := h3
    rw [h0] at m
    have hA := isMinOn_iff.1 m y ⟨h3'.le, h2.le⟩
    simp only [g, sub_zero, hv0, mul_zero, add_zero] at hA
    have hvy := (hv.2.2 y ⟨h3'.le, h2.le.trans hx.2⟩).2
    have s1 := N.strictConvexOn.deriv_lt_slope (mem_Ici.2 (by linarith : 0 ≤ x - y))
      (mem_Ici.2 hx.1) (by linarith : x - y < x) (N.differentiable _)
    rw [slope_def_field, sub_sub_cancel, lt_div_iff₀ h3'] at s1
    have s2 := N.strictConvexOn.slope_lt_deriv (mem_Ici.2 le_rfl) (mem_Ici.2 h3'.le) h3'
      (N.differentiable y)
    rw [slope_def_field, N.c_zero, sub_zero, sub_zero, div_lt_iff₀ h3'] at s2
    nlinarith [mul_lt_mul_of_pos_right h1 h3', mul_le_mul_of_nonneg_left hvy N.δ_pos.le,
      mul_lt_mul_of_pos_left s2 N.δ_pos]
  · intro hxη
    by_contra hne
    have hy : 0 < N.greedyFun v x := lt_of_le_of_ne s.1 (Ne.symm hne)
    have hA := isMinOn_iff.1 m 0 ⟨le_rfl, hx.1⟩
    simp only [g, sub_zero, hv0, mul_zero, add_zero] at hA
    have hvy := (hv.2.2 _ ⟨s.1, s.2.trans hx.2⟩).1
    have hc' := (N.η_spec x hx).2 hxη
    have s1 := N.strictConvexOn.slope_lt_deriv
      (mem_Ici.2 (sub_nonneg.2 s.2)) (mem_Ici.2 hx.1) (by linarith : x - N.greedyFun v x < x)
      (N.differentiable x)
    rw [slope_def_field, sub_sub_cancel, div_lt_iff₀ hy] at s1
    nlinarith [mul_le_mul_of_nonneg_right hc' hy.le, mul_le_mul_of_nonneg_left hvy N.δ_pos.le]

/-- The `v`-min-greedy policy of Lemma 8.3.4. -/
noncomputable def greedy {v : ℝ → ℝ} (hv : N.InV0 v) : N.Policy where
  σ := (Set.Icc 0 N.xh).indicator (N.greedyFun v)
  mem x hx := by
    rw [Set.indicator_of_mem hx]
    exact (N.greedy_spec hv hx).1
  monotoneOn x hx y hy hxy := by
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact N.greedyFun_monotoneOn hv hx hy hxy
  monotoneOn_effort x hx y hy hxy := by
    change x - (Set.Icc 0 N.xh).indicator _ x ≤ y - (Set.Icc 0 N.xh).indicator _ y
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact N.greedyFun_effort hv hx hy hxy
  eq_zero_iff x hx := by
    rw [Set.indicator_of_mem hx]
    exact N.greedyFun_eq_zero_iff hv hx
  zero_outside x hx := Set.indicator_of_notMem hx _

theorem greedy_isMinOn {v : ℝ → ℝ} (hv : N.InV0 v) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    IsMinOn (N.g v x) (Set.Icc 0 x) ((N.greedy hv).σ x) := by
  change IsMinOn (N.g v x) (Set.Icc 0 x) ((Set.Icc 0 N.xh).indicator (N.greedyFun v) x)
  rw [Set.indicator_of_mem hx]
  exact (N.greedy_spec hv hx).2

/-- **Lemma 8.3.4** (p. 280) and **Exercise 8.3.2**: for `v ∈ V₀` the policy attaining
`min_{0 ≤ a ≤ x} {c(x − a) + δv(a)}` at each `x` lies in `Σ` and is `v`-min-greedy, and
`(Tv)(x) = min_{0 ≤ a ≤ x} {c(x − a) + δv(a)}`. -/
theorem lemma_8_3_4 (v : N.Val) (hv : N.InV0 v.1) :
    N.adp.IsMinGreedy v (N.greedy hv) ∧ N.adp.IsMinBellmanValue v (N.adp.T (N.greedy hv) v) ∧
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g v.1 x) (Set.Icc 0 x) ((N.greedy hv).σ x) ∧
        (N.adp.T (N.greedy hv) v).1 x = N.g v.1 x ((N.greedy hv).σ x) := by
  have hg : N.adp.IsMinGreedy v (N.greedy hv) := fun τ x => by
    change (N.T _ v).1 x ≤ (N.T τ v).1 x
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · rw [N.T_apply _ _ hx, N.T_apply _ _ hx]
      exact isMinOn_iff.1 (N.greedy_isMinOn hv hx) _ (τ.mem x hx)
    · rw [(N.T _ v).2.2.2 x hx, (N.T τ v).2.2.2 x hx]
  refine ⟨hg, IsLeast.isGLB ⟨⟨_, rfl⟩, ?_⟩, fun x hx => ⟨N.greedy_isMinOn hv hx, N.T_apply _ _ hx⟩⟩
  rintro _ ⟨τ, rfl⟩
  exact hg τ

theorem exercise_8_3_2 (v : N.Val) (hv : N.InV0 v.1) :
    N.adp.IsMinGreedy v (N.greedy hv) ∧ N.adp.IsMinBellmanValue v (N.adp.T (N.greedy hv) v) ∧
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g v.1 x) (Set.Icc 0 x) ((N.greedy hv).σ x) ∧
        (N.adp.T (N.greedy hv) v).1 x = N.g v.1 x ((N.greedy hv).σ x) :=
  N.lemma_8_3_4 v hv

/-! ### The Bellman operator on `V₀` (Lemma 8.3.5) -/

/-- `V₀` as a type. -/
abbrev V0 (N : NegDiscount) := {v : N.Val // N.InV0 v.1}

theorem T_greedy_mem (v : N.V0) : N.InV0 (N.T (N.greedy v.2) v.1).1 := by
  set σ := N.greedy v.2
  have hval : ∀ x ∈ Set.Icc 0 N.xh, (N.T σ v.1).1 x = N.c (x - σ.σ x) + N.δ * v.1.1 (σ.σ x) :=
    fun x hx => N.T_apply σ v.1 hx
  refine ⟨⟨convex_Icc 0 N.xh, fun x₁ hx₁ x₂ hx₂ a b ha hb hab => ?_⟩, ?_, fun x hx => ?_⟩
  · have hxl : a * x₁ + b * x₂ ∈ Set.Icc 0 N.xh := by
      simpa only [smul_eq_mul] using convex_Icc 0 N.xh hx₁ hx₂ ha hb hab
    have hyl : a * σ.σ x₁ + b * σ.σ x₂ ∈ Set.Icc 0 (a * x₁ + b * x₂) :=
      ⟨by nlinarith [(σ.mem x₁ hx₁).1, (σ.mem x₂ hx₂).1],
        by nlinarith [(σ.mem x₁ hx₁).2, (σ.mem x₂ hx₂).2]⟩
    have hmin := isMinOn_iff.1 (N.greedy_isMinOn v.2 hxl) _ hyl
    have hc := N.strictConvexOn.convexOn.2 (mem_Ici.2 (sub_nonneg.2 (σ.mem x₁ hx₁).2))
      (mem_Ici.2 (sub_nonneg.2 (σ.mem x₂ hx₂).2)) ha hb hab
    have hv := v.2.1.2 (σ.mem_Icc hx₁) (σ.mem_Icc hx₂) ha hb hab
    simp only [smul_eq_mul] at hc hv ⊢
    rw [hval _ hxl, hval _ hx₁, hval _ hx₂]
    have e : a * x₁ + b * x₂ - (a * σ.σ x₁ + b * σ.σ x₂) =
        a * (x₁ - σ.σ x₁) + b * (x₂ - σ.σ x₂) := by ring
    simp only [g, e] at hmin
    nlinarith [mul_le_mul_of_nonneg_left hv N.δ_pos.le]
  · refine ContinuousOn.congr ?_ hval
    exact (N.differentiable.continuous.comp_continuousOn (continuousOn_id.sub σ.continuousOn)).add
      (continuousOn_const.mul (v.2.2.1.comp σ.continuousOn fun x hx => σ.mem_Icc hx))
  · rw [hval x hx]
    have hm := σ.mem x hx
    have hb := v.2.2.2 _ (σ.mem_Icc hx)
    have ht := N.tangent_zero (sub_nonneg.2 hm.2)
    have hmin := isMinOn_iff.1 (N.greedy_isMinOn v.2 hx) 0 ⟨le_rfl, hx.1⟩
    simp only [g, sub_zero, v.1.2.2.1, mul_zero, add_zero] at hmin
    refine ⟨?_, hmin⟩
    nlinarith [N.deriv_zero_pos, N.one_lt_δ, mul_nonneg N.deriv_zero_pos.le hm.1,
      mul_le_mul_of_nonneg_left hb.1 N.δ_pos.le]

/-- The Bellman operator `T` on `V₀`, `Tv = T_σ v` for the `v`-min-greedy `σ`. -/
noncomputable def bellman (v : N.V0) : N.V0 := ⟨N.T (N.greedy v.2) v.1, N.T_greedy_mem v⟩

theorem bellman_apply (v : N.V0) {x : ℝ} (hx : x ∈ Set.Icc 0 N.xh) :
    (N.bellman v).1.1 x = N.g v.1.1 x ((N.greedy v.2).σ x) :=
  N.T_apply _ _ hx

theorem bellman_le (v : N.V0) {x y : ℝ} (hx : x ∈ Set.Icc 0 N.xh) (hy : y ∈ Set.Icc 0 x) :
    (N.bellman v).1.1 x ≤ N.g v.1.1 x y := by
  rw [N.bellman_apply v hx]
  exact isMinOn_iff.1 (N.greedy_isMinOn v.2 hx) y hy

/-- `c` itself (on `[0, x̂]`) lies in `V₀`. -/
noncomputable def cV0 : N.V0 :=
  ⟨⟨(Set.Icc 0 N.xh).indicator N.c, fun x hx y hy hxy => by
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      exact N.c_mono hx.1 hxy, by
      rw [Set.indicator_of_mem N.zero_mem, N.c_zero], fun x hx => Set.indicator_of_notMem hx _⟩,
    ⟨(N.strictConvexOn.convexOn.subset Icc_subset_Ici_self (convex_Icc 0 N.xh)).congr
        fun x hx => (Set.indicator_of_mem hx _).symm,
      N.differentiable.continuous.continuousOn.congr fun x hx => Set.indicator_of_mem hx _,
      fun x hx => by
        change deriv N.c 0 * x ≤ (Set.Icc 0 N.xh).indicator N.c x ∧
          (Set.Icc 0 N.xh).indicator N.c x ≤ N.c x
        rw [Set.indicator_of_mem hx]
        exact ⟨N.tangent_zero hx.1, le_rfl⟩⟩⟩

/-- `T^k v` does not depend on `v ∈ V₀` on `[0, kη]` (Exercise 8.3.3). -/
theorem bellman_iterate_agree (v w : N.V0) (k : ℕ) {x : ℝ} (hxk : x ≤ k * N.η) :
    (N.bellman^[k] v).1.1 x = (N.bellman^[k] w).1.1 x := by
  induction k generalizing x with
  | zero =>
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · have : x = 0 := le_antisymm (by simpa using hxk) hx.1
      rw [this, iterate_zero, id, id, v.1.2.2.1, w.1.2.2.1]
    · rw [(N.bellman^[0] v).1.2.2.2 x hx, (N.bellman^[0] w).1.2.2.2 x hx]
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    by_cases hx : x ∈ Set.Icc 0 N.xh
    · have key : ∀ p q : N.V0, (∀ z, z ≤ k * N.η → p.1.1 z = q.1.1 z) →
          (N.bellman p).1.1 x ≤ (N.bellman q).1.1 x := fun p q hpq => by
        rw [N.bellman_apply q hx]
        refine (N.bellman_le p hx ((N.greedy q.2).mem x hx)).trans (le_of_eq ?_)
        simp only [g]
        rw [hpq]
        refine ((N.greedy q.2).le_max_sub hx).trans
          (max_le (mul_nonneg (Nat.cast_nonneg k) N.η_pos.le) ?_)
        push_cast at hxk
        linarith
      exact le_antisymm (key _ _ fun z hz => ih hz) (key _ _ fun z hz => (ih hz).symm)
    · rw [(N.bellman _).1.2.2.2 x hx, (N.bellman _).1.2.2.2 x hx]

theorem bellman_iterate_k0 (v w : N.V0) : N.bellman^[N.k0] v = N.bellman^[N.k0] w := by
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · refine N.bellman_iterate_agree v w N.k0 (hx.2.trans ?_)
    have : N.xh / N.η ≤ N.k0 := Nat.le_ceil _
    rwa [div_le_iff₀ N.η_pos] at this
  · rw [(N.bellman^[N.k0] v).1.2.2.2 x hx, (N.bellman^[N.k0] w).1.2.2.2 x hx]

/-- **Lemma 8.3.5** (p. 280) and **Exercise 8.3.3**: `T` maps `V₀` into itself and has a unique
fixed point `v̄` in `V₀`; moreover `T^k v = v̄` for all `v ∈ V₀` and `k ≥ k₀ = ⌈x̂/η⌉`. -/
theorem lemma_8_3_5 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    (∀ q, N.bellman q = q → q = vbar) ∧ ∀ v k, N.k0 ≤ k → N.bellman^[k] v = vbar := by
  have hfix : N.bellman (N.bellman^[N.k0] N.cV0) = N.bellman^[N.k0] N.cV0 := by
    rw [← iterate_succ_apply' N.bellman, iterate_succ_apply, N.bellman_iterate_k0 _ N.cV0]
  refine ⟨_, hfix, fun q hq => ?_, fun v k hk => ?_⟩
  · rw [← N.bellman_iterate_k0 q N.cV0]
    exact (iterate_fixed hq _).symm
  · rw [← Nat.sub_add_cancel hk, iterate_add_apply, N.bellman_iterate_k0 _ N.cV0]
    exact iterate_fixed hfix _

theorem exercise_8_3_3 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    (∀ q, N.bellman q = q → q = vbar) ∧ ∀ v k, N.k0 ≤ k → N.bellman^[k] v = vbar :=
  N.lemma_8_3_5

/-! ### Optimality (Theorem 8.3.6) -/

/-- **Theorem 8.3.6** (p. 280): the fundamental min-optimality properties hold for `(V, 𝕋)`; the
unique fixed point `v̄` of `T` in `V₀` is the min-value function `v▿*`; a policy is optimal iff
`σ(x) ∈ argmin_{a ≤ x} {c(x − a) + δv▿*(a)}` for all `x`; and there is exactly one optimal
policy. -/
theorem theorem_8_3_6 : ∃ vbar : N.V0, N.bellman vbar = vbar ∧
    N.adp.MinFundamentalOptimality N.isOrderStable.wellPosed ∧
    N.adp.IsMinValueFunction vbar.1 ∧
    (∀ σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x)) ∧
    ∃! σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ := by
  obtain ⟨vbar, hfix, -, -⟩ := N.lemma_8_3_5
  obtain ⟨hg, hglb, -⟩ := N.lemma_8_3_4 vbar.1 vbar.2
  have hT : N.adp.T (N.greedy vbar.2) vbar.1 = vbar.1 := congrArg Subtype.val hfix
  have hsolve : N.adp.SolvesMinBellman vbar.1 := by
    rw [hT] at hglb
    exact hglb
  have hVG : vbar.1 ∈ N.adp.VGmin := ⟨_, hg⟩
  have hMFO := N.isOrderStable.minFundamentalOptimality hVG hsolve
  obtain ⟨⟨σo, hσo⟩, ⟨v, hvmin, -, -, huniq⟩, hBP⟩ := hMFO
  have hveq : vbar.1 = v := huniq vbar.1 hVG hsolve
  subst hveq
  have hchar : ∀ σ, N.adp.IsMinGreedy vbar.1 σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x) := fun σ => by
    constructor
    · intro h x hx
      refine isMinOn_iff.2 fun y hy => ?_
      have h1 : (N.T σ vbar.1).1 x ≤ (N.T (N.greedy vbar.2) vbar.1).1 x := h _ x
      rw [N.T_apply _ _ hx, N.T_apply _ _ hx] at h1
      exact h1.trans (isMinOn_iff.1 (N.greedy_isMinOn vbar.2 hx) y hy)
    · intro h τ x
      change (N.T σ vbar.1).1 x ≤ (N.T τ vbar.1).1 x
      by_cases hx : x ∈ Set.Icc 0 N.xh
      · rw [N.T_apply _ _ hx, N.T_apply _ _ hx]
        exact isMinOn_iff.1 (h x hx) _ (τ.mem x hx)
      · rw [(N.T σ vbar.1).2.2.2 x hx, (N.T τ vbar.1).2.2.2 x hx]
  have hopt : ∀ σ, N.adp.IsMinOptimal N.isOrderStable.wellPosed σ ↔
      ∀ x ∈ Set.Icc 0 N.xh, IsMinOn (N.g vbar.1.1 x) (Set.Icc 0 x) (σ.σ x) := fun σ => by
    rw [hBP σ, ← hchar σ]
    constructor
    · rintro ⟨w, hw, hgw⟩
      rw [hw.unique hvmin] at hgw
      exact hgw
    · exact fun h => ⟨_, hvmin, h⟩
  refine ⟨vbar, hfix, ⟨⟨σo, hσo⟩, ⟨vbar.1, hvmin, hVG, hsolve, huniq⟩, hBP⟩, hvmin, hopt,
    σo, hσo, fun σ hσ => ?_⟩
  have h1 := (hopt σ).1 hσ
  have h2 := (hopt σo).1 hσo
  refine Policy.ext (funext fun x => ?_)
  by_cases hx : x ∈ Set.Icc 0 N.xh
  · exact N.unique_min vbar.2 hx (σ.mem x hx) (σo.mem x hx) (h1 x hx) (h2 x hx)
  · rw [σ.zero_outside x hx, σo.zero_outside x hx]

end NegDiscount

/-! ### The production chain (§8.3.1.1) -/

/-- The firm boundaries `t₀ = 1`, `tᵢ = tᵢ₋₁ − aᵢ` of an allocation. Firm `i + 1` in the book's
indexing carries out the range `a i`, from `boundary a (i + 1)` up to `boundary a i`. -/
def boundary (a : ℕ → ℝ) (i : ℕ) : ℝ := 1 - ∑ j ∈ Finset.range i, a j

/-- **Definition 8.3.1** (p. 275): `(p, A)` is an equilibrium for the production chain when `A` is
feasible (nonnegative, finitely many firms complete the good), (i) `p(0) = 0`, (ii) every firm
makes zero profit (8.47), and (iii) `p(s) − c(s − t) − δp(t) ≤ 0` for `0 ≤ t ≤ s ≤ 1`. -/
def IsChainEquilibrium (c : ℝ → ℝ) (δ : ℝ) (p : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ((∀ i, 0 ≤ a i) ∧ ∃ I, ∑ i ∈ Finset.range I, a i = 1) ∧ p 0 = 0 ∧
    (∀ i, p (boundary a i) - c (a i) - δ * p (boundary a (i + 1)) = 0) ∧
    ∀ s t, 0 ≤ t → t ≤ s → s ≤ 1 → p s - c (s - t) - δ * p t ≤ 0

/-- The production chain of §8.3.1.1: processing cost `c` (increasing, strictly convex, `C¹`,
`c(0) = 0 < c'(0)`) and transaction cost `δ > 1`. -/
structure ProductionChain where
  /-- the processing cost -/
  c : ℝ → ℝ
  /-- the transaction cost markup -/
  δ : ℝ
  one_lt_δ : 1 < δ
  c_zero : c 0 = 0
  differentiable : Differentiable ℝ c
  continuous_deriv : Continuous (deriv c)
  strictConvexOn : StrictConvexOn ℝ (Ici 0) c
  strictMonoOn : StrictMonoOn c (Ici 0)
  deriv_zero_pos : 0 < deriv c 0

namespace ProductionChain

variable (C : ProductionChain)

/-- A threshold `η` as in `NegDiscount.η_spec` always exists on `[0, 1]`: the solution of
`c'(η) = δc'(0)` when `δc'(0) ≤ c'(1)` (intermediate value theorem), and `η = 1` otherwise. -/
theorem exists_η : ∃ η, 0 < η ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, deriv C.c x ≤ C.δ * deriv C.c 0 ↔ x ≤ η := by
  have hmono := C.strictConvexOn.strictMonoOn_deriv fun x _ => C.differentiable x
  have hd0 : deriv C.c 0 < C.δ * deriv C.c 0 := lt_mul_left C.deriv_zero_pos C.one_lt_δ
  by_cases h : C.δ * deriv C.c 0 ≤ deriv C.c 1
  · obtain ⟨η, hη, heq⟩ :=
      intermediate_value_Icc zero_le_one C.continuous_deriv.continuousOn ⟨hd0.le, h⟩
    have hη0 : 0 < η := by
      rcases hη.1.eq_or_lt with h0 | h0
      · rw [← h0] at heq
        linarith
      · exact h0
    refine ⟨η, hη0, fun x hx => ?_⟩
    rw [← heq]
    exact hmono.le_iff_le (mem_Ici.2 hx.1) (mem_Ici.2 hη.1)
  · refine ⟨1, one_pos, fun x hx => ⟨fun _ => hx.2, fun _ => ?_⟩⟩
    exact (hmono.monotoneOn (mem_Ici.2 hx.1) (mem_Ici.2 zero_le_one) hx.2).trans
      (not_le.1 h).le

/-- The negative-discounting problem with `x̂ = 1` whose value function is the equilibrium price
function. -/
noncomputable def toNeg : NegDiscount where
  c := C.c
  δ := C.δ
  one_lt_δ := C.one_lt_δ
  xh := 1
  xh_pos := one_pos
  η := C.exists_η.choose
  η_pos := C.exists_η.choose_spec.1
  c_zero := C.c_zero
  differentiable := C.differentiable
  continuous_deriv := C.continuous_deriv
  strictConvexOn := C.strictConvexOn
  strictMonoOn := C.strictMonoOn
  deriv_zero_pos := C.deriv_zero_pos
  η_spec := C.exists_η.choose_spec.2

/-- **Proposition 8.3.1** (p. 275), by Lemma 8.3.5 with `x̂ = 1`, where `V₀ = 𝒫`: (i) the operator
`(Tp)(s) = min_{t ≤ s} {c(s − t) + δp(t)}` of (8.48) maps `𝒫` into itself, (ii) it has a unique
fixed point `p*` in `𝒫`, and (iii) `T^k p → p*` uniformly for every `p ∈ 𝒫` (indeed
`T^k p = p*` for `k ≥ k₀`). -/
theorem proposition_8_3_1 :
    (∀ p : C.toNeg.V0, ∀ s ∈ Set.Icc (0 : ℝ) 1, IsLeast
      ((fun t => C.c (s - t) + C.δ * p.1.1 t) '' Set.Icc 0 s) ((C.toNeg.bellman p).1.1 s)) ∧
    ∃ pstar : C.toNeg.V0, C.toNeg.bellman pstar = pstar ∧
      (∀ q, C.toNeg.bellman q = q → q = pstar) ∧
      ∀ p : C.toNeg.V0,
        TendstoUniformly (fun k => (C.toNeg.bellman^[k] p).1.1) pstar.1.1 atTop := by
  obtain ⟨pstar, hfix, huniq, hconv⟩ := C.toNeg.lemma_8_3_5
  refine ⟨fun p s hs => ⟨⟨_, (C.toNeg.greedy p.2).mem s hs,
    (C.toNeg.bellman_apply p hs).symm⟩, ?_⟩, pstar, hfix, huniq, fun p => ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact C.toNeg.bellman_le p hs ht
  · refine Metric.tendstoUniformly_iff.2 fun ε hε => eventually_atTop.2 ⟨C.toNeg.k0,
      fun n hn x => ?_⟩
    rw [hconv p n hn, dist_self]
    exact hε

/-- **Proposition 8.3.2** (p. 276): with `t*` the equilibrium choice function (8.49) and
`t*_i = t*(t*_{i−1})`, `t*_0 = 1` (8.50), the number of firms `n* = inf{i : t*_i = 0}` is
well-defined and finite, and `(p*, A*)` with `a*_i = t*_{i−1} − t*_i` is an equilibrium. -/
theorem proposition_8_3_2 : ∃ pstar : C.toNeg.V0, C.toNeg.bellman pstar = pstar ∧
    (∃ n, (C.toNeg.greedy pstar.2).σ^[n] 1 = 0 ∧ ∀ i < n, (C.toNeg.greedy pstar.2).σ^[i] 1 ≠ 0) ∧
    IsChainEquilibrium C.c C.δ pstar.1.1
      (fun i => (C.toNeg.greedy pstar.2).σ^[i] 1 - (C.toNeg.greedy pstar.2).σ^[i + 1] 1) := by
  classical
  obtain ⟨pstar, hfix, -, -⟩ := C.toNeg.lemma_8_3_5
  refine ⟨pstar, hfix, ?_⟩
  set σ := C.toNeg.greedy pstar.2
  have h1 : (1 : ℝ) ∈ Set.Icc 0 C.toNeg.xh := ⟨zero_le_one, le_rfl⟩
  have hex : ∃ n, σ.σ^[n] 1 = 0 := ⟨_, σ.iterate_eq_zero h1 le_rfl⟩
  have hp : ∀ x ∈ Set.Icc 0 C.toNeg.xh,
      pstar.1.1 x = C.c (x - σ.σ x) + C.δ * pstar.1.1 (σ.σ x) := fun x hx =>
    calc pstar.1.1 x = (C.toNeg.bellman pstar).1.1 x := by rw [hfix]
      _ = _ := C.toNeg.bellman_apply pstar hx
  have hle : ∀ s t, 0 ≤ t → t ≤ s → s ≤ 1 → pstar.1.1 s ≤ C.c (s - t) + C.δ * pstar.1.1 t :=
    fun s t ht hts hs1 =>
    calc pstar.1.1 s = (C.toNeg.bellman pstar).1.1 s := by rw [hfix]
      _ ≤ _ := C.toNeg.bellman_le pstar ⟨ht.trans hts, hs1⟩ ⟨ht, hts⟩
  have hb : ∀ i, boundary (fun i => σ.σ^[i] 1 - σ.σ^[i + 1] 1) i = σ.σ^[i] 1 := fun i => by
    rw [boundary, Finset.sum_range_sub' (fun i => σ.σ^[i] 1), iterate_zero, id]
    ring
  refine ⟨⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩,
    ⟨fun i => ?_, Nat.find hex, ?_⟩, pstar.1.2.2.1, fun i => ?_, fun s t ht hts hs1 => ?_⟩
  · change 0 ≤ σ.σ^[i] 1 - σ.σ^[i + 1] 1
    rw [iterate_succ_apply']
    exact sub_nonneg.2 (σ.mem _ (σ.iterate_mem h1 i)).2
  · rw [Finset.sum_range_sub' (fun i => σ.σ^[i] 1), Nat.find_spec hex, iterate_zero, id, sub_zero]
  · beta_reduce
    rw [hb, hb, iterate_succ_apply', hp _ (σ.iterate_mem h1 i)]
    ring
  · linarith [hle s t ht hts hs1]

end ProductionChain

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal harvests

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.2 (pp. 281–284).

A plantation with biomass `s` faces an iid price `p ~ φ`. Harvesting (`a = 1`) earns
`ps − m(s)` and regrowth starts from `q(0)`; waiting (`a = 0`) costs `c(s)` and biomass grows to
`q(s)`. So `r(s, p, a) = a(ps − m(s)) − (1 − a)c(s)` and `f(s, a) = q[(1 − a)s]`.

We work with general measurable spaces of biomass and prices, a bounded measurable harvest
revenue `rev(s, p)` (the book's `ps − m(s)` on compact `S × E`), a bounded measurable cost
`cost(s)`, a measurable growth map `q`, and a point `s₀` (the book's biomass `0`). Actions are
`Bool` (`true` = harvest), `V = b(S × E)` and `V̂ = b(S × {0, 1})`.

* **Exercise 8.3.4**: `(V, F, V̂, 𝔾)` with `(Fv)(s, a) = ∫ v(f(s, a), p') φ(dp')` and
  `G_σ w = r_σ + βw(s, σ(s, p))` is an order-preserving FDP whose primary ADP is the harvest ADP,
  and `T̂_σ w = FG_σ w` is the subordinate policy operator of §8.3.2.2.
* **§8.3.2.2**: by Theorem 5.2.13, the fundamental optimality properties hold for both ADPs, the
  subordinate Bellman operator `T̂` has a unique fixed point `ŵ*`, and any `σ` with
  `σ(s, p) ∈ argmax_a {r(s, p, a) + βŵ*(s, a)}` is optimal for the harvest problem.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The optimal harvest model (§8.3.2.1). -/
structure Harvest (S E : Type*) [MeasurableSpace S] [MeasurableSpace E] where
  /-- the iid price distribution -/
  φ : Measure E
  [isProb : IsProbabilityMeasure φ]
  /-- the harvest revenue `ps − m(s)` -/
  rev : S × E → ℝ
  measurable_rev : Measurable rev
  bdd_rev : ∃ C, ∀ x, |rev x| ≤ C
  /-- the maintenance cost `c(s)` -/
  cost : S → ℝ
  measurable_cost : Measurable cost
  bdd_cost : ∃ C, ∀ s, |cost s| ≤ C
  /-- the growth map -/
  q : S → S
  measurable_q : Measurable q
  /-- the biomass left after a harvest -/
  s₀ : S
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace Harvest

variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] (H : Harvest S E)

attribute [local instance] Harvest.isProb

/-- Next period's biomass `f(s, a) = q[(1 − a)s]`. -/
def f (s : S) (a : Bool) : S := if a then H.q H.s₀ else H.q s

/-- The reward `r(s, p, a) = a(ps − m(s)) − (1 − a)c(s)`. -/
def r (x : S × E) (a : Bool) : ℝ := if a then H.rev x else -H.cost x.1

theorem measurable_f : Measurable fun y : S × Bool => H.f y.1 y.2 :=
  Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
    (H.measurable_q.comp measurable_fst)

theorem integrable_section (v : BM (S × E)) (s : S) : Integrable (fun p => v.toFun (s, p)) H.φ :=
  Integrable.of_bound
    (v.measurable'.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ‖v‖
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

theorem abs_integral_le (v : BM (S × E)) (s : S) : |∫ p, v.toFun (s, p) ∂H.φ| ≤ ‖v‖ := by
  have := norm_integral_le_of_norm_le_const (μ := H.φ) (f := fun p => v.toFun (s, p)) (C := ‖v‖)
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
  simpa using this

/-- `(Fv)(s, a) = ∫ v(f(s, a), p') φ(dp')`. -/
noncomputable def F (v : BM (S × E)) : BM (S × Bool) :=
  ⟨fun y => ∫ p, v.toFun (H.f y.1 y.2, p) ∂H.φ,
    (v.measurable'.comp ((H.measurable_f.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable,
    ⟨‖v‖, fun _ => H.abs_integral_le v _⟩⟩

theorem measurable_r (σ : StopPolicy (S × E)) : Measurable fun x => H.r x (σ.1 x) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) H.measurable_rev
    (H.measurable_cost.comp measurable_fst).neg

/-- `(G_σ w)(s, p) = r_σ(s, p) + βw(s, σ(s, p))`. -/
noncomputable def G (σ : StopPolicy (S × E)) (w : BM (S × Bool)) : BM (S × E) :=
  ⟨fun x => H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x),
    (H.measurable_r σ).add (measurable_const.mul (w.measurable'.comp
      (measurable_fst.prodMk σ.2))), by
    obtain ⟨C₁, hC₁⟩ := H.bdd_rev
    obtain ⟨C₂, hC₂⟩ := H.bdd_cost
    refine ⟨C₁ + C₂ + H.β * ‖w‖, fun x => (abs_add_le _ _).trans ?_⟩
    have hw := BM.abs_le_norm w (x.1, σ.1 x)
    have hr : |H.r x (σ.1 x)| ≤ C₁ + C₂ := by
      unfold r
      split_ifs
      · linarith [hC₁ x, (abs_nonneg _).trans (hC₂ x.1)]
      · rw [abs_neg]
        linarith [hC₂ x.1, (abs_nonneg _).trans (hC₁ x)]
    rw [abs_mul, abs_of_nonneg H.β_nonneg]
    linarith [mul_le_mul_of_nonneg_left hw H.β_nonneg]⟩

theorem G_apply (σ : StopPolicy (S × E)) (w : BM (S × Bool)) (x : S × E) :
    (H.G σ w).toFun x = if σ.1 x then H.rev x + H.β * w.toFun (x.1, true)
      else -H.cost x.1 + H.β * w.toFun (x.1, false) := by
  change H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) = _
  rcases σ.1 x with _ | _ <;> simp [r]

/-- The policy harvesting when `r(s, p, 1) + βw(s, 1) ≥ r(s, p, 0) + βw(s, 0)`. -/
noncomputable def harvestWhere (w : BM (S × Bool)) : StopPolicy (S × E) :=
  acceptWhere (s := fun x => H.rev x + H.β * w.toFun (x.1, true))
    (h := fun x => -H.cost x.1 + H.β * w.toFun (x.1, false))
    (H.measurable_rev.add (measurable_const.mul (w.measurable'.comp
      (measurable_fst.prodMk measurable_const))))
    ((H.measurable_cost.comp measurable_fst).neg.add (measurable_const.mul
      (w.measurable'.comp (measurable_fst.prodMk measurable_const))))

theorem G_harvestWhere (w : BM (S × Bool)) (x : S × E) :
    (H.G (H.harvestWhere w) w).toFun x = max (H.rev x + H.β * w.toFun (x.1, true))
      (-H.cost x.1 + H.β * w.toFun (x.1, false)) := by
  rw [G_apply]
  exact acceptWhere_apply _ _ x

theorem G_le_G_harvestWhere (σ : StopPolicy (S × E)) (w : BM (S × Bool)) :
    H.G σ w ≤ H.G (H.harvestWhere w) w := BM.le_def.2 fun x => by
  rw [G_harvestWhere, G_apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The FDP `(V, F, V̂, 𝔾)` of §8.3.2.2. -/
noncomputable def fdp : FDP (BM (S × E)) (BM (S × Bool)) (StopPolicy (S × E)) where
  F := H.F
  G := H.G
  greatest w := ⟨H.harvestWhere w, fun τ => H.G_le_G_harvestWhere τ w⟩
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

theorem isOrderPreserving : H.fdp.IsOrderPreserving := by
  refine ⟨fun v w hvw => BM.le_def.2 fun y => integral_mono (H.integrable_section v _)
    (H.integrable_section w _) fun p => BM.le_def.1 hvw _,
    fun σ w w' hww => BM.le_def.2 fun x => ?_⟩
  change H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) ≤
    H.r x (σ.1 x) + H.β * w'.toFun (x.1, σ.1 x)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (BM.le_def.1 hww _) H.β_nonneg)

/-- **Exercise 8.3.4** (p. 283): (i) `(V, F, V̂, 𝔾)` is an order-preserving FDP and (ii) its primary
ADP has the harvest policy operators
`(T_σ v)(s, p) = r_σ(s, p) + β ∫ v[f(s, σ(s, p)), p'] φ(dp')`, while its subordinate ADP has
`(T̂_σ w)(s, a) = ∫ {r_σ(f(s, a), p') + βw[f(s, a), σ(f(s, a), p')]} φ(dp')`. -/
theorem exercise_8_3_4 :
    H.fdp.IsOrderPreserving ∧
      (∀ σ v x, ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ v).toFun x =
        H.r x (σ.1 x) + H.β * ∫ p, v.toFun (H.f x.1 (σ.1 x), p) ∂H.φ) ∧
      ∀ σ w y, ((H.fdp.sub (Or.inl H.isOrderPreserving)).T σ w).toFun y =
        ∫ p, (H.r (H.f y.1 y.2, p) (σ.1 (H.f y.1 y.2, p)) +
          H.β * w.toFun (H.f y.1 y.2, σ.1 (H.f y.1 y.2, p))) ∂H.φ :=
  ⟨H.isOrderPreserving, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem abs_F_sub_le (v w : BM (S × E)) (y : S × Bool) :
    |(H.F v).toFun y - (H.F w).toFun y| ≤ dist v w := by
  have h : (H.F v).toFun y - (H.F w).toFun y = ∫ p, (v - w).toFun (H.f y.1 y.2, p) ∂H.φ := by
    change ∫ p, v.toFun (H.f y.1 y.2, p) ∂H.φ - ∫ p, w.toFun (H.f y.1 y.2, p) ∂H.φ = _
    rw [← integral_sub (H.integrable_section v _) (H.integrable_section w _)]
    rfl
  rw [h, dist_eq_norm]
  exact H.abs_integral_le (v - w) _

theorem primary_contraction (σ : StopPolicy (S × E)) (v w : BM (S × E)) :
    dist ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ v)
      ((H.fdp.primary (Or.inl H.isOrderPreserving)).T σ w) ≤ H.β * dist v w := by
  refine BM.dist_le (mul_nonneg H.β_nonneg dist_nonneg) fun x => ?_
  change |(H.r x (σ.1 x) + H.β * (H.F v).toFun (x.1, σ.1 x)) -
    (H.r x (σ.1 x) + H.β * (H.F w).toFun (x.1, σ.1 x))| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg H.β_nonneg]
  exact mul_le_mul_of_nonneg_left (H.abs_F_sub_le v w _) H.β_nonneg

/-- `G_σ w = Gw` iff `σ(s, p) ∈ argmax_a {r(s, p, a) + βw(s, a)}` at every `(s, p)`. -/
theorem G_eq_Gsup_iff (σ : StopPolicy (S × E)) (w : BM (S × Bool)) :
    H.fdp.G σ w = H.fdp.Gsup w ↔ ∀ x, H.r x (σ.1 x) + H.β * w.toFun (x.1, σ.1 x) =
      max (H.rev x + H.β * w.toFun (x.1, true)) (-H.cost x.1 + H.β * w.toFun (x.1, false)) := by
  have hsup : H.fdp.Gsup w = H.G (H.harvestWhere w) w := by
    obtain ⟨⟨τ, hτ⟩, -⟩ := H.fdp.isGreatest_Gsup w
    refine le_antisymm ?_ (H.fdp.G_le_Gsup (H.harvestWhere w) w)
    rw [← hτ]
    exact H.G_le_G_harvestWhere τ w
  rw [hsup]
  constructor
  · intro h x
    rw [← H.G_harvestWhere w x, ← h]
    rfl
  · intro h
    exact BM.ext fun x => by rw [H.G_harvestWhere w x, ← h x]; rfl

/-- §8.3.2.2 (p. 283), via Theorem 5.2.13: the fundamental optimality properties hold for the
harvest ADP and for the subordinate ADP; the subordinate Bellman operator `T̂` has a unique fixed
point `ŵ*`, the subordinate value function; and any `σ` with
`σ(s, p) ∈ argmax_a {r(s, p, a) + βŵ*(s, a)}` is optimal for the harvest problem. -/
theorem section_8_3_2_2 :
    ∃ hw : (H.fdp.primary (Or.inl H.isOrderPreserving)).WellPosed,
    ∃ hw' : (H.fdp.sub (Or.inl H.isOrderPreserving)).WellPosed,
      (H.fdp.primary (Or.inl H.isOrderPreserving)).FundamentalOptimality hw ∧
      (H.fdp.sub (Or.inl H.isOrderPreserving)).FundamentalOptimality hw' ∧
      ∃ wstar, (H.fdp.sub (Or.inl H.isOrderPreserving)).IsValueFunction wstar ∧
        (H.fdp.sub (Or.inl H.isOrderPreserving)).bellman wstar = wstar ∧
        (∀ w, (H.fdp.sub (Or.inl H.isOrderPreserving)).bellman w = w → w = wstar) ∧
        ∀ σ : StopPolicy (S × E), (∀ x, H.r x (σ.1 x) + H.β * wstar.toFun (x.1, σ.1 x) =
          max (H.rev x + H.β * wstar.toFun (x.1, true))
            (-H.cost x.1 + H.β * wstar.toFun (x.1, false))) →
          (H.fdp.primary (Or.inl H.isOrderPreserving)).IsOptimal hw σ := by
  have hP := H.isOrderPreserving
  obtain ⟨hFO, -, -, -, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive H.β_nonneg H.β_lt_one
    H.primary_contraction (V₀ := univ)
    ⟨isClosed_univ, fun v _ => FDP.primary_regular _ v, mapsTo_univ _ _⟩ univ_nonempty
  set hw := (ADP.isGloballyStable_of_contraction ⟨(univ_nonempty (α := BM (S × E))).some⟩
    H.β_nonneg H.β_lt_one H.primary_contraction).wellPosed
  have hw' : (H.fdp.sub (Or.inl hP)).WellPosed := ((FDP.lemma_5_2_12 (Or.inl hP)).1).2 hw
  have h513 := FDP.theorem_5_2_13 (Or.inl hP) hP hw hw'
  have hFO' := h513.1.1 hFO
  obtain ⟨wstar, hval, -, hsolve, huniq⟩ := hFO'.2.1
  have hreg := FDP.sub_regular (Or.inl hP) hP.1
  refine ⟨hw, hw', hFO, hFO', wstar, hval,
    ((H.fdp.sub _).solvesBellman_iff (hreg wstar)).1 hsolve,
    fun w hw₀ => huniq w (hreg w) (((H.fdp.sub _).solvesBellman_iff (hreg w)).2 hw₀),
    fun σ hσ => (h513.2 hFO).2.1 wstar σ hval ((H.G_eq_Gsup_iff σ wstar).2 hσ)⟩

end Harvest

end SargentStachurski.AdditionalApplications

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Euler equation methods: the stochastic growth model

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.3.3 (pp. 284–290), with the
envelope results used in §8.3.4.

Income evolves as `y' = f(y − c)ξ'` (8.58) and the Bellman equation is (8.59). We take the
state and action spaces to be `ℝ` with `Γ(y) = [0, y ∨ 0]`, so that negative states are
inert, and write `B(y, c, v) = u(c) + β ∫ v(f((y − c) ∨ 0) z) φ(dz)`; on `ℝ₊` this is the book's
aggregator. The shock distribution `φ` is any probability measure on `(0, ∞)` (the book's
continuous density is not used).

* **Exercise 8.3.5**: `u'(c) → 0` as `c → ∞`.
* **Exercise 8.3.6** is false as stated: for `v = 𝟙_(0, ∞) ∈ bX`, `(y, c) ↦ B(y, c, v)` is
  discontinuous at `(y, y)`, and `v` has no greedy policy, so the ADP on `bX` is not regular.
  The continuity holds for `v ∈ bcX` (`exercise_8_3_6`).
* **Proposition 8.3.7** (**Exercise 8.3.7**): the fundamental optimality properties hold,
  `v* ∈ bcX` and VFI converges on `bcX` (Proposition 7.2.2). The book's OPI and HPI claims rest
  on Exercise 8.3.6 for all `v ∈ bX` and are not established.
* **Lemma 8.3.8** (**Exercise 8.3.8**): `v*` is increasing, concave on `ℝ₊` and continuous, and
  the optimal policy is unique (and continuous).
* **Proposition 8.3.9** and **Corollary 8.3.10** (envelope condition), proved with the
  differentiable sandwich of Clausen and Strub (2020): `σ(y) > 0`, `Tv` is strictly increasing,
  and `(Tv)' = u' ∘ σ` on `(0, ∞)`. The interiority claim `σ(y) < y` is false (`v = 0`).
* **Exercises 8.3.9, 8.3.10** and the comparison step of **Exercise 8.3.12**: solutions of the
  functional Euler equation, uniqueness and monotonicity of the Coleman–Reffett map.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

/-- The differentiable sandwich in the concave case (Clausen and Strub, 2020): if `g` is concave
near `y`, `W ≤ g` near `y` with `W(y) = g(y)`, and `W` is differentiable at `y`, then `g` is
differentiable at `y` with the same derivative. -/
theorem hasDerivAt_of_concave_sandwich {g W : ℝ → ℝ} {s : Set ℝ} {y d : ℝ}
    (hg : ConcaveOn ℝ s g) (hs : s ∈ 𝓝 y) (hWg : ∀ᶠ t in 𝓝 y, W t ≤ g t) (hy : W y = g y)
    (hW : HasDerivAt W d y) : HasDerivAt g d y := by
  rw [hasDerivAt_iff_tendsto_slope] at hW ⊢
  have hr : Tendsto (fun t => 2 * y - t) (𝓝 y) (𝓝 y) := by
    have h : Tendsto (fun t : ℝ => 2 * y - t) (𝓝 y) (𝓝 (2 * y - y)) :=
      tendsto_const_nhds.sub tendsto_id
    rwa [show 2 * y - y = y by ring] at h
  have hr' : Tendsto (fun t => 2 * y - t) (𝓝[≠] y) (𝓝[≠] y) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hr.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
        intro h
        exact ht (by linarith))
  have hW2 : Tendsto (fun t => slope W y (2 * y - t)) (𝓝[≠] y) (𝓝 d) := hW.comp hr'
  have hev1 : ∀ᶠ t in 𝓝[≠] y, t ∈ s ∧ W t ≤ g t :=
    (Filter.Eventually.and hs hWg).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ t in 𝓝[≠] y, 2 * y - t ∈ s ∧ W (2 * y - t) ≤ g (2 * y - t) := hr'.eventually hev1
  have hev3 : ∀ᶠ t in 𝓝[≠] y, t ≠ y := self_mem_nhdsWithin
  have hlo := hW.min hW2
  have hhi := hW.max hW2
  rw [min_self] at hlo
  rw [max_self] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev1, hev2, hev3] with t ⟨ht, h1⟩ ⟨ht', h2⟩ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine (min_le_right _ _).trans ?_
      have hadj := hg.slope_anti_adjacent ht ht' hlt (by linarith : y < 2 * y - t)
      rw [slope_comm g, slope_def_field, slope_def_field]
      exact (div_le_div_of_nonneg_right (by linarith) (by linarith)).trans hadj
    · refine (min_le_left _ _).trans ?_
      rw [slope_def_field, slope_def_field]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · filter_upwards [hev1, hev2, hev3] with t ⟨ht, h1⟩ ⟨ht', h2⟩ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine le_trans ?_ (le_max_left _ _)
      rw [slope_comm g, slope_comm W, slope_def_field, slope_def_field]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    · refine le_trans ?_ (le_max_right _ _)
      have hadj := hg.slope_anti_adjacent ht' ht (by linarith : 2 * y - t < y) hgt
      rw [slope_comm W, slope_def_field, slope_def_field]
      exact hadj.trans (div_le_div_of_nonneg_right (by linarith) (by linarith))

/-- The stochastic optimal growth model of §8.3.3.1 under Assumption 8.3.1. -/
structure Growth where
  /-- utility -/
  u : ℝ → ℝ
  /-- production -/
  f : ℝ → ℝ
  /-- the shock distribution, on `(0, ∞)` -/
  φ : Measure ℝ
  [isProb : IsProbabilityMeasure φ]
  shock_pos : ∀ᵐ z ∂φ, 0 < z
  /-- the discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  measurable_u : Measurable u
  u_continuousOn : ContinuousOn u (Set.Ici 0)
  u_strictMonoOn : StrictMonoOn u (Set.Ici 0)
  u_strictConcaveOn : StrictConcaveOn ℝ (Set.Ici 0) u
  u_differentiableAt : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_deriv_continuousOn : ContinuousOn (deriv u) (Set.Ioi 0)
  u_bdd : ∃ C, ∀ c, 0 ≤ c → |u c| ≤ C
  u_zero : u 0 = 0
  /-- `u'(0) = ∞` -/
  u_inada : Tendsto (deriv u) (𝓝[>] 0) atTop
  measurable_f : Measurable f
  f_continuousOn : ContinuousOn f (Set.Ici 0)
  f_strictMonoOn : StrictMonoOn f (Set.Ici 0)
  f_concaveOn : ConcaveOn ℝ (Set.Ici 0) f
  f_differentiableAt : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_zero : f 0 = 0

namespace Growth

variable (G : Growth)

attribute [local instance] Growth.isProb

theorem u_concaveOn : ConcaveOn ℝ (Set.Ici 0) G.u := G.u_strictConcaveOn.concaveOn

theorem u_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : G.u a ≤ G.u b :=
  G.u_strictMonoOn.monotoneOn ha (ha.trans hab) hab

theorem f_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : G.f a ≤ G.f b :=
  G.f_strictMonoOn.monotoneOn ha (ha.trans hab) hab

theorem f_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ G.f k := by
  have := G.f_mono le_rfl hk
  rwa [G.f_zero] at this

theorem f_pos {k : ℝ} (hk : 0 < k) : 0 < G.f k := by
  have := G.f_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hk.le) hk
  rwa [G.f_zero] at this

theorem deriv_u_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ deriv G.u c := by
  have h := G.u_concaveOn.slope_le_deriv (mem_Ici.2 hc.le) (mem_Ici.2 (by linarith : 0 ≤ c + 1))
    (by linarith : c < c + 1) (G.u_differentiableAt c hc)
  rw [slope_def_field] at h
  exact (div_nonneg (sub_nonneg.2 (G.u_mono hc.le (by linarith))) (by linarith)).trans h

theorem deriv_f_nonneg {k : ℝ} (hk : 0 < k) : 0 ≤ deriv G.f k := by
  have h := G.f_concaveOn.slope_le_deriv (mem_Ici.2 hk.le) (mem_Ici.2 (by linarith : 0 ≤ k + 1))
    (by linarith : k < k + 1) (G.f_differentiableAt k hk)
  rw [slope_def_field] at h
  exact (div_nonneg (sub_nonneg.2 (G.f_mono hk.le (by linarith))) (by linarith)).trans h

theorem deriv_u_strictAntiOn : StrictAntiOn (deriv G.u) (Set.Ioi 0) :=
  (G.u_strictConcaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv
    fun c hc => G.u_differentiableAt c hc

theorem deriv_f_antitoneOn : AntitoneOn (deriv G.f) (Set.Ioi 0) :=
  (G.f_concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
    fun k hk => G.f_differentiableAt k hk

/-- **Exercise 8.3.5** (p. 285): under Assumption 8.3.1, `u'(c) → 0` as `c → ∞`. (The book's
solution uses the tangent inequality in the wrong direction for concave `u`; we use
`u(c) − u(c₀) ≥ u'(c)(c − c₀)`.) -/
theorem exercise_8_3_5 : Tendsto (deriv G.u) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := G.u_bdd
  have hanti : AntitoneOn (deriv G.u) (Set.Ioi 0) := G.deriv_u_strictAntiOn.antitoneOn
  have hsmall : ∀ ε > 0, ∃ c > 0, deriv G.u c < ε := by
    intro ε hε
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    set c := 1 + (2 * C + 1) / ε
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 le_rfl)
    have hc1 : 1 < c := by
      have : 0 < (2 * C + 1) / ε := div_pos (by linarith) hε
      linarith
    have h := G.u_concaveOn.deriv_le_slope (mem_Ici.2 zero_le_one) (mem_Ici.2 (by linarith))
      hc1 (G.u_differentiableAt c (by linarith))
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    have h2 := hcon c (by linarith)
    have h3 : ε * (c - 1) = 2 * C + 1 := by
      simp only [c]
      field_simp
      ring
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ c - 1)
    have h5 := abs_le.1 (hC c (by linarith))
    have h6 := abs_le.1 (hC 1 zero_le_one)
    linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with c hc
    exact ha.trans_le (G.deriv_u_nonneg hc)
  · obtain ⟨c₀, hc₀, hlt⟩ := hsmall a ha
    filter_upwards [eventually_ge_atTop c₀] with c hc
    exact (hanti hc₀ (hc₀.trans_le hc) hc).trans_lt hlt

/-! ### The RDP of §8.3.3.1 -/

/-- The feasible correspondence `Γ(y) = [0, y ∨ 0]`. -/
def Γ (y : ℝ) : Set ℝ := Set.Icc 0 (max y 0)

/-- The continuation term `∫ v(f((y − c) ∨ 0) z) φ(dz)`. -/
noncomputable def cont (v : ℝ → ℝ) (y c : ℝ) : ℝ := ∫ z, v (G.f (max (y - c) 0) * z) ∂G.φ

/-- The aggregator `B(y, c, v) = u(c) + β ∫ v(f(y − c) z) φ(dz)`. -/
noncomputable def B (y c : ℝ) (v : ℝ → ℝ) : ℝ := G.u c + G.β * G.cont v y c

theorem measurable_integrand (v : BM ℝ) :
    Measurable fun q : (ℝ × ℝ) × ℝ => v.toFun (G.f (max (q.1.1 - q.1.2) 0) * q.2) :=
  v.measurable'.comp ((G.measurable_f.comp ((measurable_fst.fst.sub measurable_fst.snd).max
    measurable_const)).mul measurable_snd)

theorem integrable_cont (v : BM ℝ) (k : ℝ) : Integrable (fun z => v.toFun (k * z)) G.φ :=
  Integrable.of_bound (v.measurable'.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    ‖v‖ (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)

theorem abs_cont_le (v : BM ℝ) (y c : ℝ) : |G.cont v.toFun y c| ≤ ‖v‖ := by
  have := norm_integral_le_of_norm_le_const (μ := G.φ)
    (f := fun z => v.toFun (G.f (max (y - c) 0) * z)) (C := ‖v‖)
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact BM.abs_le_norm v _)
  unfold cont
  simpa using this

theorem cont_add_const (v : BM ℝ) (κ y c : ℝ) :
    G.cont (fun x => v.toFun x + κ) y c = G.cont v.toFun y c + κ := by
  unfold cont
  rw [integral_add (G.integrable_cont v _) (integrable_const κ)]
  simp

/-- The RDP `(Γ, bX, B)` of §8.3.3.1. -/
noncomputable def brdp : BRDP ℝ ℝ where
  Γ := Γ
  B := G.B
  measurable v := (G.measurable_u.comp measurable_snd).add (measurable_const.mul
    (G.measurable_integrand v).stronglyMeasurable.integral_prod_right'.measurable)
  mono y c hc v w hvw := add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_mono (G.integrable_cont v _) (G.integrable_cont w _) fun z => BM.le_def.1 hvw _)
    G.β_pos.le)
  bdd v := by
    obtain ⟨C, hC⟩ := G.u_bdd
    refine ⟨C + G.β * ‖v‖, fun y c hc => (abs_add_le _ _).trans (add_le_add (hC c hc.1) ?_)⟩
    rw [abs_mul, abs_of_pos G.β_pos]
    exact mul_le_mul_of_nonneg_left (G.abs_cont_le v y c) G.β_pos.le
  exists_policy := ⟨fun _ => 0, measurable_const, fun y => ⟨le_rfl, le_max_right _ _⟩⟩

theorem isBlackwell : G.brdp.IsBlackwell G.β := fun y c _ v κ _ => by
  change G.u c + G.β * G.cont (fun x => v.toFun x + κ) y c ≤ G.u c + G.β * G.cont v.toFun y c +
    G.β * κ
  rw [G.cont_add_const]
  linarith

theorem hasMaxSelections : HasMaxSelections G.brdp.Γ :=
  hasMaxSelections_Icc (g := fun _ => 0) (h := fun y => max y 0) continuous_const
    (continuous_id.max continuous_const) fun y => le_max_right y 0

/-- **Exercise 8.3.6**, corrected (p. 285): `(y, c) ↦ B(y, c, v)` is continuous on `G` for every
`v ∈ bcX` (dominated convergence; the book's proof uses continuity of `v`). -/
theorem exercise_8_3_6 (v : BM ℝ) (hv : Continuous v.toFun) :
    ContinuousOn (fun p : ℝ × ℝ => G.B p.1 p.2 v.toFun) {p | p.2 ∈ G.brdp.Γ p.1} := by
  have hu : ContinuousOn (fun p : ℝ × ℝ => G.u p.2) {p | p.2 ∈ G.brdp.Γ p.1} :=
    G.u_continuousOn.comp continuousOn_snd fun p hp => mem_Ici.2 hp.1
  have hfk : Continuous fun p : ℝ × ℝ => G.f (max (p.1 - p.2) 0) :=
    G.f_continuousOn.comp_continuous ((continuous_fst.sub continuous_snd).max continuous_const)
      fun p => mem_Ici.2 (le_max_right _ _)
  have hc : Continuous fun p : ℝ × ℝ => G.cont v.toFun p.1 p.2 :=
    continuous_of_dominated (bound := fun _ => ‖v‖)
      (fun p => (v.measurable'.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
      (fun p => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact BM.abs_le_norm v _)
      (integrable_const _) (Eventually.of_forall fun z => hv.comp (hfk.mul continuous_const))
  exact hu.add (continuous_const.mul hc).continuousOn

/-- `𝟙_(0, ∞)` as an element of `bX`. -/
noncomputable def indPos : BM ℝ :=
  ⟨(Set.Ioi 0).indicator 1, measurable_const.indicator measurableSet_Ioi, ⟨1, fun x => by
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]⟩⟩

theorem cont_indPos_lt {y c : ℝ} (hcy : c < y) : G.cont indPos.toFun y c = 1 := by
  have hf := G.f_pos (lt_max_of_lt_left (sub_pos.2 hcy) : 0 < max (y - c) 0)
  have h : (fun z => indPos.toFun (G.f (max (y - c) 0) * z)) =ᵐ[G.φ] fun _ => (1 : ℝ) :=
    G.shock_pos.mono fun z hz => by
      change (Set.Ioi (0 : ℝ)).indicator 1 (G.f (max (y - c) 0) * z) = 1
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 (mul_pos hf hz))]
      rfl
  unfold cont
  rw [integral_congr_ae h]
  simp

theorem cont_indPos_self (y : ℝ) : G.cont indPos.toFun y y = 0 := by
  unfold cont
  rw [sub_self, max_self, G.f_zero]
  simp only [zero_mul]
  change ∫ _, (Set.Ioi (0 : ℝ)).indicator 1 0 ∂G.φ = 0
  rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) (lt_irrefl (0 : ℝ))]
  simp

theorem tendsto_u_left : Tendsto G.u (𝓝[<] 1) (𝓝 (G.u 1)) :=
  ((G.u_continuousOn 1 (mem_Ici.2 zero_le_one)).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds zero_lt_one))).tendsto

/-- **Exercise 8.3.6** is false for discontinuous `v ∈ bX`: with `v = 𝟙_(0, ∞)`,
`B(y, c, v) = u(c) + β𝟙{c < y}` jumps at `c = y`. -/
theorem exercise_8_3_6_false :
    ¬ ContinuousOn (fun p : ℝ × ℝ => G.B p.1 p.2 indPos.toFun) {p | p.2 ∈ G.brdp.Γ p.1} := by
  intro hc
  have hp0 : ((1 : ℝ), (1 : ℝ)) ∈ {p : ℝ × ℝ | p.2 ∈ G.brdp.Γ p.1} :=
    ⟨zero_le_one, le_max_left 1 0⟩
  have hpath : Tendsto (fun t : ℝ => ((1 : ℝ), t)) (𝓝[<] 1)
      (𝓝[{p : ℝ × ℝ | p.2 ∈ G.brdp.Γ p.1}] ((1 : ℝ), (1 : ℝ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.prodMk continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
      exact ⟨ht.1.le, ht.2.le.trans (le_max_left _ _)⟩
  have hlim := (hc _ hp0).tendsto.comp hpath
  have heq : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      ((fun p : ℝ × ℝ => G.B p.1 p.2 indPos.toFun) ∘ fun t : ℝ => ((1 : ℝ), t)) t =
        G.u t + G.β := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
    simp only [Function.comp_apply, B]
    rw [G.cont_indPos_lt ht.2, mul_one]
  have h2 := tendsto_nhds_unique (hlim.congr' heq) (G.tendsto_u_left.add tendsto_const_nhds)
  simp only [B, G.cont_indPos_self, mul_zero, add_zero] at h2
  linarith [G.β_pos]

/-- With `v = 𝟙_(0, ∞)` no policy is `v`-greedy (`sup_{c < y} u(c) + β = u(y) + β` is not
attained), so the ADP `(bX, 𝕋)` is not regular. -/
theorem not_regular : ¬ G.brdp.toRDP.adp.Regular := by
  intro hreg
  obtain ⟨σ, hσ⟩ := hreg indPos
  have hg := (G.brdp.toRDP.isGreedy_iff indPos σ).1 hσ
  have hτ : ∀ c, 0 ≤ c → G.B 1 (min c (max 1 0)) indPos.toFun ≤ G.B 1 (σ.1 1) indPos.toFun :=
    fun c hc => hg ⟨fun y => min c (max y 0), measurable_const.min (measurable_id.max
      measurable_const), fun y => ⟨le_min hc (le_max_right _ _), min_le_right _ _⟩⟩ 1
  have h10 : max (1 : ℝ) 0 = 1 := max_eq_left zero_le_one
  have ha := σ.2.2 1
  change σ.1 1 ∈ Set.Icc 0 (max 1 0) at ha
  rw [h10] at ha hτ
  rcases ha.2.lt_or_eq with hlt | heq
  · have hc := hτ ((σ.1 1 + 1) / 2) (by linarith [ha.1])
    rw [min_eq_left (by linarith), B, B, G.cont_indPos_lt (by linarith), G.cont_indPos_lt hlt]
      at hc
    have := G.u_strictMonoOn (mem_Ici.2 ha.1) (mem_Ici.2 (by linarith [ha.1]) :
      (σ.1 1 + 1) / 2 ∈ Set.Ici (0 : ℝ)) (by linarith : σ.1 1 < (σ.1 1 + 1) / 2)
    linarith
  · have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), G.u 1 - G.β < G.u t ∧ t ∈ Set.Ioo 0 1 :=
      (G.tendsto_u_left.eventually (lt_mem_nhds (by linarith [G.β_pos]))).and
        (Ioo_mem_nhdsLT zero_lt_one)
    obtain ⟨t, ht1, ht2⟩ := hev.exists
    have hc := hτ t ht2.1.le
    rw [min_eq_left ht2.2.le, heq, B, B, G.cont_indPos_lt ht2.2, G.cont_indPos_self] at hc
    linarith

/-- **Proposition 8.3.7** (p. 285) and **Exercise 8.3.7**: under Assumption 8.3.1, the
fundamental optimality properties hold, `v* ∈ bcX`, and VFI converges geometrically on `bcX`
(Proposition 7.2.2 with Exercise 8.3.6 for `v ∈ bcX`). The ADP is not regular on `bX`
(`not_regular`), so the convergence of OPI and HPI claimed in the book is not covered. -/
theorem proposition_8_3_7 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ LDP.bc ℝ, G.brdp.toRDP.adp.VFIGeometric (LDP.bc ℝ) vstar := by
  obtain ⟨hw, hFO, vstar, hv, hgeo, -⟩ := G.brdp.proposition_7_2_2 G.hasMaxSelections
    G.β_pos.le G.β_lt_one G.isBlackwell fun v hv => G.exercise_8_3_6 v hv
  exact ⟨hw, hFO, vstar, hv, hgeo⟩

/-! ### Properties of the value function (Lemma 8.3.8) -/

/-- The continuous, increasing functions in `bX` that are concave on `ℝ₊`. -/
def ICC : Set (BM ℝ) :=
  {v | Continuous v.toFun ∧ Monotone v.toFun ∧ ConcaveOn ℝ (Set.Ici 0) v.toFun}

theorem isClosed_ICC : IsClosed ICC := by
  refine isSeqClosed_iff_isClosed.1 fun vs v hvs hlim => ?_
  have hu := BM.tendstoUniformly_of_tendsto hlim
  have hpt : ∀ x, Tendsto (fun n => (vs n).toFun x) atTop (𝓝 (v.toFun x)) := fun x =>
    hu.tendsto_at x
  refine ⟨hu.continuous (Frequently.of_forall fun n => (hvs n).1), fun x y hxy =>
    le_of_tendsto_of_tendsto' (hpt x) (hpt y) fun n => (hvs n).2.1 hxy, convex_Ici 0,
    fun x hx y hy a b ha hb hab => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hpt x).const_smul a).add ((hpt y).const_smul b)) (hpt _)
    fun n => (hvs n).2.2.2 hx hy ha hb hab

theorem zero_mem_ICC : (0 : BM ℝ) ∈ ICC :=
  ⟨continuous_const, monotone_const, concaveOn_const 0 (convex_Ici 0)⟩

theorem cont_mono {v : BM ℝ} (hv : Monotone v.toFun) {y y' : ℝ} (hyy : y ≤ y') (c : ℝ) :
    G.cont v.toFun y c ≤ G.cont v.toFun y' c :=
  integral_mono_ae (G.integrable_cont v _) (G.integrable_cont v _) (G.shock_pos.mono fun _ hz =>
    hv (mul_le_mul_of_nonneg_right (G.f_mono (le_max_right _ _)
      (max_le_max (sub_le_sub_right hyy c) le_rfl)) hz.le))

/-- `(y, c) ↦ ∫ v(f(y − c)z) φ(dz)` is concave on `{0 ≤ c ≤ y}` for increasing `v` concave on
`ℝ₊`. -/
theorem cont_concave {v : BM ℝ} (hvm : Monotone v.toFun) (hvc : ConcaveOn ℝ (Set.Ici 0) v.toFun)
    {y₁ c₁ y₂ c₂ a b : ℝ} (h₁ : c₁ ≤ y₁) (h₂ : c₂ ≤ y₂) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * G.cont v.toFun y₁ c₁ + b * G.cont v.toFun y₂ c₂ ≤
      G.cont v.toFun (a * y₁ + b * y₂) (a * c₁ + b * c₂) := by
  have hk₁ : max (y₁ - c₁) 0 = y₁ - c₁ := max_eq_left (sub_nonneg.2 h₁)
  have hk₂ : max (y₂ - c₂) 0 = y₂ - c₂ := max_eq_left (sub_nonneg.2 h₂)
  have hkl : max (a * y₁ + b * y₂ - (a * c₁ + b * c₂)) 0 = a * (y₁ - c₁) + b * (y₂ - c₂) := by
    have h0 : 0 ≤ a * y₁ + b * y₂ - (a * c₁ + b * c₂) := by
      nlinarith [mul_nonneg ha (sub_nonneg.2 h₁), mul_nonneg hb (sub_nonneg.2 h₂)]
    rw [max_eq_left h0]
    ring
  unfold cont
  rw [hk₁, hk₂, hkl, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((G.integrable_cont v _).const_mul a) ((G.integrable_cont v _).const_mul b)]
  refine integral_mono_ae (((G.integrable_cont v _).const_mul a).add
    ((G.integrable_cont v _).const_mul b)) (G.integrable_cont v _)
    (G.shock_pos.mono fun z hz => ?_)
  have hf := G.f_concaveOn.2 (mem_Ici.2 (sub_nonneg.2 h₁)) (mem_Ici.2 (sub_nonneg.2 h₂)) ha hb
    hab
  simp only [smul_eq_mul] at hf
  have hp₁ : 0 ≤ G.f (y₁ - c₁) * z := mul_nonneg (G.f_nonneg (sub_nonneg.2 h₁)) hz.le
  have hp₂ : 0 ≤ G.f (y₂ - c₂) * z := mul_nonneg (G.f_nonneg (sub_nonneg.2 h₂)) hz.le
  have hv := hvc.2 (mem_Ici.2 hp₁) (mem_Ici.2 hp₂) ha hb hab
  simp only [smul_eq_mul] at hv
  exact hv.trans (hvm (by nlinarith [mul_le_mul_of_nonneg_right hf hz.le]))

/-- `(y, c) ↦ B(y, c, v)` is concave on `{0 ≤ c ≤ y}` for increasing `v` concave on `ℝ₊`
(Assumption 7.2.9). -/
theorem B_concave {v : BM ℝ} (hvm : Monotone v.toFun) (hvc : ConcaveOn ℝ (Set.Ici 0) v.toFun)
    {y₁ c₁ y₂ c₂ a b : ℝ} (h₁ : c₁ ∈ Set.Icc 0 y₁) (h₂ : c₂ ∈ Set.Icc 0 y₂) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * G.B y₁ c₁ v.toFun + b * G.B y₂ c₂ v.toFun ≤
      G.B (a * y₁ + b * y₂) (a * c₁ + b * c₂) v.toFun := by
  have hu := G.u_concaveOn.2 (mem_Ici.2 h₁.1) (mem_Ici.2 h₂.1) ha hb hab
  have hc := G.cont_concave hvm hvc h₁.2 h₂.2 ha hb hab
  simp only [smul_eq_mul] at hu
  unfold B
  nlinarith [mul_le_mul_of_nonneg_left hc G.β_pos.le]

/-- `T` maps the continuous increasing functions concave on `ℝ₊` into themselves
(Propositions 7.2.6 and 7.2.7). -/
theorem bellman_mem_ICC {v : BM ℝ} (hv : v ∈ ICC) : G.brdp.toRDP.adp.bellman v ∈ ICC := by
  obtain ⟨-, -, -, hTc, hgr, -⟩ :=
    G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections v (G.exercise_8_3_6 v hv.1)
  have hw : ∀ y, IsGreatest ((fun c => G.B y c v.toFun) '' Γ y)
      ((G.brdp.toRDP.adp.bellman v).toFun y) := hgr
  refine ⟨hTc, fun y y' hyy => ?_, convex_Ici 0, fun y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_⟩
  · obtain ⟨⟨c, hc, hcy⟩, -⟩ := hw y
    rw [← hcy]
    refine le_trans ?_ ((hw y').2 ⟨c, ⟨hc.1, hc.2.trans (max_le_max hyy le_rfl)⟩, rfl⟩)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (G.cont_mono hv.2.1 hyy c) G.β_pos.le)
  · obtain ⟨⟨c₁, hc₁, e₁⟩, -⟩ := hw y₁
    obtain ⟨⟨c₂, hc₂, e₂⟩, -⟩ := hw y₂
    rw [Γ, max_eq_left (mem_Ici.1 hy₁)] at hc₁
    rw [Γ, max_eq_left (mem_Ici.1 hy₂)] at hc₂
    simp only [smul_eq_mul]
    rw [← e₁, ← e₂]
    have hmem : a * c₁ + b * c₂ ∈ Γ (a * y₁ + b * y₂) :=
      ⟨by nlinarith [hc₁.1, hc₂.1], le_max_of_le_left (by nlinarith [hc₁.2, hc₂.2])⟩
    exact (G.B_concave hv.2.1 hv.2.2 hc₁ hc₂ ha hb hab).trans ((hw _).2 ⟨_, hmem, rfl⟩)

/-- `c ↦ B(y, c, v)` is strictly concave on `Γ(y)` (Assumption 7.2.10). -/
theorem strictConcaveOn_B {v : BM ℝ} (hv : v ∈ ICC) (y : ℝ) :
    StrictConcaveOn ℝ (G.brdp.Γ y) fun c => G.B y c v.toFun := by
  have hΓ : Γ y ⊆ Set.Ici 0 := fun c hc => hc.1
  refine (G.u_strictConcaveOn.subset hΓ (convex_Icc _ _)).add_concaveOn
    ⟨convex_Icc _ _, fun c₁ hc₁ c₂ hc₂ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases le_or_gt 0 y with hy | hy
  · have hc₁' : c₁ ≤ y := hc₁.2.trans (max_eq_left hy).le
    have hc₂' : c₂ ≤ y := hc₂.2.trans (max_eq_left hy).le
    have h := G.cont_concave hv.2.1 hv.2.2 hc₁' hc₂' ha hb hab
    rw [show a * y + b * y = y by rw [← add_mul, hab, one_mul]] at h
    nlinarith [mul_le_mul_of_nonneg_left h G.β_pos.le]
  · have h₁ : c₁ = 0 := le_antisymm (hc₁.2.trans (max_eq_right hy.le).le) hc₁.1
    have h₂ : c₂ = 0 := le_antisymm (hc₂.2.trans (max_eq_right hy.le).le) hc₂.1
    subst h₁ h₂
    simp only [mul_zero, add_zero]
    rw [← add_mul, hab, one_mul]

/-- **Lemma 8.3.8** (p. 286) and **Exercise 8.3.8**: under Assumption 8.3.1, (i) the value
function `v*` is increasing, concave (on `ℝ₊`) and continuous, and (ii) the optimal policy is
unique; it attains `max_{0 ≤ c ≤ y} B(y, c, v*)` and is continuous. -/
theorem lemma_8_3_8 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar : BM ℝ, G.brdp.toRDP.adp.IsValueFunction vstar ∧ vstar ∈ ICC ∧
      ∃ σ, G.brdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        G.brdp.toRDP.IsArgmax vstar σ ∧ Continuous σ.1 := by
  obtain ⟨hw, hFO, vstar, -, hgeo⟩ := G.proposition_8_3_7
  have hv : vstar ∈ ICC := lemma_A_2_6 (fun u hu => hgeo.tendsto hu.1) isClosed_ICC
    (fun v hv => G.bellman_mem_ICC hv) ⟨0, zero_mem_ICC⟩
  have hvf := hgeo.1
  obtain ⟨hiff, ⟨σ₀, hσ₀⟩, -, -, -, hcont⟩ :=
    G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections vstar (G.exercise_8_3_6 vstar hv.1)
  have hσ := (hiff σ₀).1 hσ₀
  have huniq : ∀ y, ∀ c ∈ G.brdp.Γ y, G.B y (σ₀.1 y) vstar.toFun ≤ G.B y c vstar.toFun →
      c = σ₀.1 y := fun y c hc hle =>
    eq_of_isMax_of_strictConcaveOn (G.strictConcaveOn_B hv y) hc (σ₀.2.2 y)
      (fun c' hc' => (hσ y c' hc').trans hle) (hσ y)
  have hopt : ∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ ↔ G.brdp.toRDP.IsArgmax vstar τ := fun τ => by
    rw [hFO.2.2 τ]
    constructor
    · rintro ⟨w, hw', hg⟩
      rw [hw'.unique hvf] at hg
      exact (hiff τ).1 hg
    · exact fun h => ⟨vstar, hvf, (hiff τ).2 h⟩
  refine ⟨hw, hFO, vstar, hvf, hv, σ₀, (hopt σ₀).2 hσ, fun τ hτ => ?_, hσ,
    hcont (hasContinuousUniqueMax_Icc continuous_const (continuous_id.max continuous_const)
      fun y => le_max_right y 0) σ₀ hσ huniq⟩
  have hτ' := (hopt τ).1 hτ
  exact Subtype.ext (funext fun y => huniq y _ (τ.2.2 y) (hτ' y _ (σ₀.2.2 y)))

theorem exercise_8_3_8 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, G.brdp.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar : BM ℝ, G.brdp.toRDP.adp.IsValueFunction vstar ∧ vstar ∈ ICC ∧
      ∃ σ, G.brdp.toRDP.adp.IsOptimal hw σ ∧ (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
        G.brdp.toRDP.IsArgmax vstar σ ∧ Continuous σ.1 :=
  G.lemma_8_3_8

/-! ### Envelope theorems (Proposition 8.3.9 and Corollary 8.3.10) -/

/-- A `v`-maximizing policy consumes a positive amount at positive income: `u'(0) = ∞`, while
`c ↦ ∫ v(f(y − c)z) φ(dz)` is concave with a finite slope at `c = 0`. -/
theorem argmax_pos {v : BM ℝ} (hv : v ∈ ICC) {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax v σ) {y : ℝ} (hy : 0 < y) : 0 < σ.1 y := by
  have hmem := σ.2.2 y
  change σ.1 y ∈ Set.Icc 0 (max y 0) at hmem
  refine lt_of_le_of_ne hmem.1 fun h0 => ?_
  set L := 2 * ‖v‖ / y
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), G.β * L < deriv G.u c ∧ c ∈ Set.Ioo 0 y :=
    (G.u_inada.eventually (eventually_gt_atTop _)).and (Ioo_mem_nhdsGT hy)
  obtain ⟨c, hcL, hc⟩ := hev.exists
  have hmax := hσ y c ⟨hc.1.le, hc.2.le.trans (le_max_left _ _)⟩
  change G.B y c v.toFun ≤ G.B y (σ.1 y) v.toFun at hmax
  rw [← h0] at hmax
  -- the chord of the concave map `c ↦ ∫ v(f(y − c)z)` from `0` to `y`
  have hchord := G.cont_concave hv.2.1 hv.2.2 (y₁ := y) (c₁ := y) (y₂ := y) (c₂ := 0) le_rfl
    hy.le (div_nonneg hc.1.le hy.le) (sub_nonneg.2 ((div_le_one hy).2 hc.2.le))
    (by ring)
  rw [show c / y * y + (1 - c / y) * y = y by ring,
    show c / y * y + (1 - c / y) * 0 = c by rw [mul_zero, add_zero, div_mul_cancel₀ c hy.ne']]
    at hchord
  have hb1 := abs_le.1 (G.abs_cont_le v y y)
  have hb2 := abs_le.1 (G.abs_cont_le v y 0)
  -- `u(c) ≥ u'(c)c`
  have hslope := G.u_concaveOn.deriv_le_slope (mem_Ici.2 le_rfl) (mem_Ici.2 hc.1.le) hc.1
    (G.u_differentiableAt c hc.1)
  rw [slope_def_field, G.u_zero, sub_zero, sub_zero, le_div_iff₀ hc.1] at hslope
  have hcy : c / y * (G.cont v.toFun y 0 - G.cont v.toFun y y) ≤ c * L := by
    rw [show c * L = c / y * (2 * ‖v‖) by simp only [L]; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hc.1.le hy.le)
  unfold B at hmax
  rw [G.u_zero] at hmax
  nlinarith [mul_lt_mul_of_pos_right hcL hc.1, G.β_pos]

/-- **Proposition 8.3.9** (p. 286), corrected. Let `v ∈ bcℝ₊` be increasing and concave and let
`σ` be a `v`-greedy (maximizing) policy. Then `σ(y) > 0` for `y > 0`, `Tv` is concave and strictly
increasing on `ℝ₊`, and `Tv` is differentiable on `(0, ∞)` with `(Tv)' = u' ∘ σ` (8.60), a
continuous function. The claim that `σ` is interior (`σ(y) < y`) is false in general
(`proposition_8_3_9_not_interior`). The derivative is obtained from the concave sandwich
`u(t − (y − σ(y))) + β ∫ v(f(y − σ(y))z) φ(dz) ≤ (Tv)(t)`, with equality at `t = y`. -/
theorem proposition_8_3_9 {v : BM ℝ} (hv : v ∈ ICC) {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax v σ) :
    (∀ y, 0 < y → 0 < σ.1 y) ∧ ConcaveOn ℝ (Set.Ici 0) (G.brdp.toRDP.adp.bellman v).toFun ∧
      StrictMonoOn (G.brdp.toRDP.adp.bellman v).toFun (Set.Ici 0) ∧
      (∀ y, 0 < y → HasDerivAt (G.brdp.toRDP.adp.bellman v).toFun (deriv G.u (σ.1 y)) y) ∧
      ContinuousOn (fun y => deriv G.u (σ.1 y)) (Set.Ioi 0) := by
  obtain ⟨-, hval, -⟩ := G.brdp.toRDP.bellman_of_isArgmax hσ
  have hval' : ∀ y, (G.brdp.toRDP.adp.bellman v).toFun y = G.B y (σ.1 y) v.toFun := hval
  have hpos : ∀ y, 0 < y → 0 < σ.1 y := fun y hy => G.argmax_pos hv hσ hy
  have hconc := (G.bellman_mem_ICC hv).2.2
  have hle : ∀ y, 0 ≤ y → σ.1 y ≤ y := fun y hy => by
    have : σ.1 y ≤ max y 0 := (σ.2.2 y).2
    rwa [max_eq_left hy] at this
  -- keeping savings `y − σ(y)` fixed is feasible at income `t ≥ y − σ(y)`
  have hkeep : ∀ y t, 0 ≤ y → y - σ.1 y ≤ t →
      G.u (t - (y - σ.1 y)) + G.β * G.cont v.toFun y (σ.1 y) ≤
        (G.brdp.toRDP.adp.bellman v).toFun t := fun y t hy ht => by
    have hc : t - (y - σ.1 y) ∈ G.brdp.Γ t :=
      ⟨by linarith, le_max_of_le_left (by linarith [hle y hy])⟩
    have h := hσ t _ hc
    change G.B t (t - (y - σ.1 y)) v.toFun ≤ G.B t (σ.1 t) v.toFun at h
    rw [hval']
    refine le_trans (le_of_eq ?_) h
    unfold B cont
    rw [sub_sub_cancel]
  refine ⟨hpos, hconc, fun y hy y' hy' hyy => ?_, fun y hy => ?_, ?_⟩
  · have h := hkeep y y' hy (by linarith [(σ.2.2 y).1])
    rw [hval' y]
    refine lt_of_lt_of_le ?_ h
    unfold B
    have := G.u_strictMonoOn (mem_Ici.2 (σ.2.2 y).1)
      (mem_Ici.2 (by linarith [(σ.2.2 y).1, hle y hy] : (0 : ℝ) ≤ y' - (y - σ.1 y)))
      (by linarith : σ.1 y < y' - (y - σ.1 y))
    linarith
  · have hσy := hpos y hy
    have hW : HasDerivAt (fun t => G.u (t - (y - σ.1 y)) + G.β * G.cont v.toFun y (σ.1 y))
        (deriv G.u (σ.1 y)) y := by
      have hd : HasDerivAt G.u (deriv G.u (σ.1 y)) (y - (y - σ.1 y)) := by
        rw [sub_sub_cancel]
        exact (G.u_differentiableAt _ hσy).hasDerivAt
      exact (hd.comp_sub_const y (y - σ.1 y)).add_const _
    refine hasDerivAt_of_concave_sandwich hconc (Ici_mem_nhds hy) ?_ ?_ hW
    · filter_upwards [Ioi_mem_nhds (by linarith : y - σ.1 y < y)] with t ht
      exact hkeep y t hy.le (le_of_lt ht)
    · rw [hval', sub_sub_cancel]
      rfl
  · obtain ⟨-, -, -, -, -, hcont⟩ :=
      G.brdp.toRDP.lemma_7_1_2 G.hasMaxSelections v (G.exercise_8_3_6 v hv.1)
    have huniq : ∀ y, ∀ c ∈ G.brdp.Γ y, G.B y (σ.1 y) v.toFun ≤ G.B y c v.toFun →
        c = σ.1 y := fun y c hc hle' =>
      eq_of_isMax_of_strictConcaveOn (G.strictConcaveOn_B hv y) hc (σ.2.2 y)
        (fun c' hc' => (hσ y c' hc').trans hle') (hσ y)
    have hσc := hcont (hasContinuousUniqueMax_Icc continuous_const
      (continuous_id.max continuous_const) fun y => le_max_right y 0) σ hσ huniq
    exact G.u_deriv_continuousOn.comp hσc.continuousOn fun y hy => hpos y hy

/-- The interiority claim of Proposition 8.3.9 (i) fails: `v = 0` is increasing, concave and
continuous, and its greedy policy consumes everything, `σ(y) = y`. -/
theorem proposition_8_3_9_not_interior {σ : G.brdp.toRDP.Policy}
    (hσ : G.brdp.toRDP.IsArgmax 0 σ) {y : ℝ} (hy : 0 ≤ y) : σ.1 y = y := by
  have hmem := σ.2.2 y
  change σ.1 y ∈ Set.Icc 0 (max y 0) at hmem
  rw [max_eq_left hy] at hmem
  have h := hσ y y ⟨hy, le_max_left _ _⟩
  change G.B y y (fun _ => 0) ≤ G.B y (σ.1 y) (fun _ => 0) at h
  simp only [B, cont, integral_zero, mul_zero, add_zero] at h
  by_contra hne
  have := G.u_strictMonoOn (mem_Ici.2 hmem.1) (mem_Ici.2 hy) (lt_of_le_of_ne hmem.2 hne)
  linarith

/-- **Corollary 8.3.10** (p. 286), the envelope condition: with `σ` the unique optimal policy and
`v*` the value function, `σ(y) > 0` for `y > 0`, `v*` is concave and strictly increasing on `ℝ₊`,
and `v*` is continuously differentiable on `(0, ∞)` with `(v*)' = u' ∘ σ` (8.61). -/
theorem corollary_8_3_10 :
    ∃ hw : G.brdp.toRDP.adp.WellPosed, ∃ vstar : BM ℝ, ∃ σ : G.brdp.toRDP.Policy,
      G.brdp.toRDP.adp.IsValueFunction vstar ∧ G.brdp.toRDP.adp.IsOptimal hw σ ∧
      (∀ τ, G.brdp.toRDP.adp.IsOptimal hw τ → τ = σ) ∧
      (∀ y, 0 < y → 0 < σ.1 y) ∧ ConcaveOn ℝ (Set.Ici 0) vstar.toFun ∧
      StrictMonoOn vstar.toFun (Set.Ici 0) ∧
      (∀ y, 0 < y → HasDerivAt vstar.toFun (deriv G.u (σ.1 y)) y) ∧
      ContinuousOn (fun y => deriv G.u (σ.1 y)) (Set.Ioi 0) := by
  obtain ⟨hw, hFO, vstar, hvf, hv, σ, hopt, huniq, hσ, -⟩ := G.lemma_8_3_8
  obtain ⟨w, hwv, hwG, hws, -⟩ := hFO.2.1
  have hfix : G.brdp.toRDP.adp.bellman vstar = vstar := by
    rw [hvf.unique hwv]
    exact (G.brdp.toRDP.adp.solvesBellman_iff hwG).1 hws
  obtain ⟨h1, h2, h3, h4, h5⟩ := G.proposition_8_3_9 hv hσ
  rw [hfix] at h2 h3 h4
  exact ⟨hw, vstar, σ, hvf, hopt, huniq, h1, h2, h3, h4, h5⟩

/-! ### The Euler equation and the Coleman–Reffett operator -/

/-- `Σ𝒞`: continuous, strictly increasing policies with `0 < σ(y) < y` for `y > 0`. -/
def SigmaC (σ : ℝ → ℝ) : Prop :=
  ContinuousOn σ (Set.Ici 0) ∧ StrictMonoOn σ (Set.Ici 0) ∧ ∀ y, 0 < y → 0 < σ y ∧ σ y < y

/-- The integrand `(u' ∘ σ)(f(y − c)z) f'(y − c) z` of (8.63). -/
noncomputable def eulerIntegrand (σ : ℝ → ℝ) (y c z : ℝ) : ℝ :=
  deriv G.u (σ (G.f (y - c) * z)) * deriv G.f (y - c) * z

/-- `c ∈ (0, y)` solves `u'(c) = β ∫ (u' ∘ σ)(f(y − c)z) f'(y − c) z φ(dz)`, the integral
existing; for the Coleman–Reffett operator, `c = Kσ(y)`. -/
def SolvesEuler (β : ℝ) (σ : ℝ → ℝ) (y c : ℝ) : Prop :=
  c ∈ Set.Ioo 0 y ∧ Integrable (G.eulerIntegrand σ y c) G.φ ∧
    deriv G.u c = β * ∫ z, G.eulerIntegrand σ y c z ∂G.φ

/-- (8.63): `σ` satisfies the Euler equation. -/
def SatisfiesEuler (σ : ℝ → ℝ) : Prop := ∀ y, 0 < y → G.SolvesEuler G.β σ y (σ y)

/-- **Exercise 8.3.9** (p. 287): if `σ` satisfies (8.63) and `c_t = σ(y_t)` with
`y_{t+1} = f(y_t − c_t)ξ_{t+1}` (8.58), then `u'(c_t) = β ∫ g_t(z) φ(dz)` where the integrand at the
realised shock is `g_t(ξ_{t+1}) = u'(c_{t+1}) f'(y_t − c_t) ξ_{t+1}`: this is (8.62) with `𝔼_t`
the expectation over `ξ_{t+1} ~ φ`. -/
theorem exercise_8_3_9 {σ : ℝ → ℝ} (hσ : G.SatisfiesEuler σ) (y ξ : ℕ → ℝ)
    (hy : ∀ t, 0 < y t) (hlaw : ∀ t, y (t + 1) = G.f (y t - σ (y t)) * ξ (t + 1)) (t : ℕ) :
    deriv G.u (σ (y t)) = G.β * ∫ z, G.eulerIntegrand σ (y t) (σ (y t)) z ∂G.φ ∧
      G.eulerIntegrand σ (y t) (σ (y t)) (ξ (t + 1)) =
        deriv G.u (σ (y (t + 1))) * deriv G.f (y t - σ (y t)) * ξ (t + 1) := by
  refine ⟨(hσ _ (hy t)).2.2, ?_⟩
  rw [hlaw]
  rfl

theorem eulerIntegrand_nonneg {σ : ℝ → ℝ} (hσ : ∀ x, 0 < x → 0 < σ x) {y c z : ℝ}
    (hc : c ∈ Set.Ioo 0 y) (hz : 0 < z) : 0 ≤ G.eulerIntegrand σ y c z := by
  have hk : 0 < y - c := sub_pos.2 hc.2
  exact mul_nonneg (mul_nonneg (G.deriv_u_nonneg (hσ _ (mul_pos (G.f_pos hk) hz)))
    (G.deriv_f_nonneg hk)) hz.le

/-- The integrand of (8.63) increases with consumption `c` (savings and hence next income
fall). -/
theorem eulerIntegrand_mono {σ : ℝ → ℝ} (hσm : MonotoneOn σ (Set.Ici 0))
    (hσ : ∀ x, 0 < x → 0 < σ x) {y c₁ c₂ z : ℝ} (hc₂ : c₂ ∈ Set.Ioo 0 y)
    (h12 : c₁ ≤ c₂) (hz : 0 < z) : G.eulerIntegrand σ y c₁ z ≤ G.eulerIntegrand σ y c₂ z := by
  have hk₂ : 0 < y - c₂ := sub_pos.2 hc₂.2
  have hk : y - c₂ ≤ y - c₁ := by linarith
  have hx₂ : 0 < G.f (y - c₂) * z := mul_pos (G.f_pos hk₂) hz
  have hx : G.f (y - c₂) * z ≤ G.f (y - c₁) * z :=
    mul_le_mul_of_nonneg_right (G.f_mono hk₂.le hk) hz.le
  have hs : σ (G.f (y - c₂) * z) ≤ σ (G.f (y - c₁) * z) :=
    hσm (mem_Ici.2 hx₂.le) (mem_Ici.2 (hx₂.le.trans hx)) hx
  have hu : deriv G.u (σ (G.f (y - c₁) * z)) ≤ deriv G.u (σ (G.f (y - c₂) * z)) :=
    G.deriv_u_strictAntiOn.antitoneOn (hσ _ hx₂) (hσ _ (hx₂.trans_le hx)) hs
  have hf : deriv G.f (y - c₁) ≤ deriv G.f (y - c₂) :=
    G.deriv_f_antitoneOn hk₂ (hk₂.trans_le hk) hk
  unfold eulerIntegrand
  exact mul_le_mul_of_nonneg_right (mul_le_mul hu hf (G.deriv_f_nonneg (hk₂.trans_le hk))
    (G.deriv_u_nonneg (hσ _ hx₂))) hz.le

/-- **Exercise 8.3.10** (p. 288): the Coleman–Reffett operator is order preserving on `Σ𝒞`: if
`σ_a ≤ σ_b` and `c_a = Kσ_a(y)`, `c_b = Kσ_b(y)` solve the Euler equation at `y`, then
`c_a ≤ c_b`. -/
theorem exercise_8_3_10 {σa σb : ℝ → ℝ} (ha : SigmaC σa) (hb : SigmaC σb)
    (hab : ∀ x, 0 < x → σa x ≤ σb x) {y ca cb : ℝ} (hca : G.SolvesEuler G.β σa y ca)
    (hcb : G.SolvesEuler G.β σb y cb) : ca ≤ cb := by
  by_contra h
  have hlt := not_le.1 h
  have hpa : ∀ x, 0 < x → 0 < σa x := fun x hx => (ha.2.2 x hx).1
  have hpb : ∀ x, 0 < x → 0 < σb x := fun x hx => (hb.2.2 x hx).1
  have hI : ∫ z, G.eulerIntegrand σb y cb z ∂G.φ ≤ ∫ z, G.eulerIntegrand σa y ca z ∂G.φ :=
    integral_mono_ae hcb.2.1 hca.2.1 (G.shock_pos.mono fun z hz => by
      refine (G.eulerIntegrand_mono hb.2.1.monotoneOn hpb hca.1 hlt.le hz).trans ?_
      have hk : 0 < y - ca := sub_pos.2 hca.1.2
      have hx : 0 < G.f (y - ca) * z := mul_pos (G.f_pos hk) hz
      unfold eulerIntegrand
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (G.deriv_u_strictAntiOn.antitoneOn (hpa _ hx) (hpb _ hx) (hab _ hx))
        (G.deriv_f_nonneg hk)) hz.le)
  have hu := G.deriv_u_strictAntiOn hcb.1.1 hca.1.1 hlt
  rw [hca.2.2, hcb.2.2] at hu
  nlinarith [mul_le_mul_of_nonneg_left hI G.β_pos.le]

/-- The Euler equation at `y` has at most one solution `c ∈ (0, y)`: `K` is well defined where a
solution exists. -/
theorem solvesEuler_unique {σ : ℝ → ℝ} (hσ : SigmaC σ) {y c₁ c₂ : ℝ}
    (h₁ : G.SolvesEuler G.β σ y c₁) (h₂ : G.SolvesEuler G.β σ y c₂) : c₁ = c₂ :=
  le_antisymm (G.exercise_8_3_10 hσ hσ (fun _ _ => le_rfl) h₁ h₂)
    (G.exercise_8_3_10 hσ hσ (fun _ _ => le_rfl) h₂ h₁)

/-- The comparison step of **Exercise 8.3.12** (p. 293): for `β_a ≤ β_b`, `K_b σ ≤ K_a σ`. (The
conclusion `σ_b ≤ σ_a` also needs the global stability of `K` from Proposition 8.3.13.) -/
theorem exercise_8_3_12_step {σ : ℝ → ℝ} (hσ : SigmaC σ) {βa βb : ℝ} (hβa : 0 < βa)
    (hβ : βa ≤ βb) {y ca cb : ℝ} (hca : G.SolvesEuler βa σ y ca)
    (hcb : G.SolvesEuler βb σ y cb) : cb ≤ ca := by
  by_contra h
  have hlt := not_le.1 h
  have hp : ∀ x, 0 < x → 0 < σ x := fun x hx => (hσ.2.2 x hx).1
  have hI : ∫ z, G.eulerIntegrand σ y ca z ∂G.φ ≤ ∫ z, G.eulerIntegrand σ y cb z ∂G.φ :=
    integral_mono_ae hca.2.1 hcb.2.1 (G.shock_pos.mono fun z hz =>
      G.eulerIntegrand_mono hσ.2.1.monotoneOn hp hcb.1 hlt.le hz)
  have h0 : 0 ≤ ∫ z, G.eulerIntegrand σ y ca z ∂G.φ :=
    integral_nonneg_of_ae (G.shock_pos.mono fun z hz => G.eulerIntegrand_nonneg hp hca.1 hz)
  have hu := G.deriv_u_strictAntiOn hca.1.1 hcb.1.1 hlt
  rw [hca.2.2, hcb.2.2] at hu
  nlinarith [mul_le_mul_of_nonneg_right hβ h0, mul_le_mul_of_nonneg_left hI (hβa.le.trans hβ)]

end Growth

end SargentStachurski.AdditionalApplications

set_option linter.style.longLine false
#print axioms SargentStachurski.AdditionalApplications.IsMarkov
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.mk
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.nonneg
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.rowsum
#print axioms SargentStachurski.AdditionalApplications.IsDistribution
#print axioms SargentStachurski.AdditionalApplications.IsDistribution.mk
#print axioms SargentStachurski.AdditionalApplications.IsDistribution.nonneg
#print axioms SargentStachurski.AdditionalApplications.IsDistribution.sum_eq_one
#print axioms SargentStachurski.AdditionalApplications.mulVec_apply_eq
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.mul
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.pow
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.mulVec_le_mulVec
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.mulVec_const
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.abs_mulVec_le
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.norm_mulVec_le
#print axioms SargentStachurski.AdditionalApplications.IsMarkov.abs_mulVec_sub_le
#print axioms SargentStachurski.AdditionalApplications.GloballyStable
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.mk
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.mapsTo
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.nonneg
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.lt_one
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.norm_sub_le
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.fixedPt_unique
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.iterate_mem
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.tendsto_iterate_fixedPt
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.exists_fixedPt
#print axioms SargentStachurski.AdditionalApplications.IsContractionOn.globallyStable_univ
#print axioms SargentStachurski.AdditionalApplications.fixedPt_le_of_le
#print axioms SargentStachurski.AdditionalApplications.le_fixedPt_of_le_apply
#print axioms SargentStachurski.AdditionalApplications.isContractionOn_of_blackwell
#print axioms SargentStachurski.AdditionalApplications.abs_sup'_sub_sup'_le
#print axioms SargentStachurski.AdditionalApplications.IsBdd
#print axioms SargentStachurski.AdditionalApplications.IsSupContraction
#print axioms SargentStachurski.AdditionalApplications.IsUniformlyClosed
#print axioms SargentStachurski.AdditionalApplications.isBdd_const
#print axioms SargentStachurski.AdditionalApplications.IsBdd.sub
#print axioms SargentStachurski.AdditionalApplications.IsBdd.add
#print axioms SargentStachurski.AdditionalApplications.IsBdd.nonneg_bound
#print axioms SargentStachurski.AdditionalApplications.IsBdd.exists_dist
#print axioms SargentStachurski.AdditionalApplications.IsSupContraction.iterate
#print axioms SargentStachurski.AdditionalApplications.IsSupContraction.eq_of_isFixedPt
#print axioms SargentStachurski.AdditionalApplications.IsSupContraction.exists_limit
#print axioms SargentStachurski.AdditionalApplications.IsSupContraction.globallyStable
#print axioms SargentStachurski.AdditionalApplications.le_of_le_map_of_tendsto
#print axioms SargentStachurski.AdditionalApplications.le_of_map_le_of_tendsto
#print axioms SargentStachurski.AdditionalApplications.bX
#print axioms SargentStachurski.AdditionalApplications.isUniformlyClosed_bX
#print axioms SargentStachurski.AdditionalApplications.const_mem_bX
#print axioms SargentStachurski.AdditionalApplications.abs_max_sub_max_le
#print axioms SargentStachurski.AdditionalApplications.abs_ciSup_sub_ciSup_le
#print axioms SargentStachurski.AdditionalApplications.markovOp
#print axioms SargentStachurski.AdditionalApplications.integrable_of_mem_bX
#print axioms SargentStachurski.AdditionalApplications.measurable_markovOp
#print axioms SargentStachurski.AdditionalApplications.abs_markovOp_le
#print axioms SargentStachurski.AdditionalApplications.markovOp_mem_bX
#print axioms SargentStachurski.AdditionalApplications.markovOp_mono
#print axioms SargentStachurski.AdditionalApplications.markovOp_const
#print axioms SargentStachurski.AdditionalApplications.markovOp_add
#print axioms SargentStachurski.AdditionalApplications.markovOp_sub
#print axioms SargentStachurski.AdditionalApplications.markovOp_smul
#print axioms SargentStachurski.AdditionalApplications.markovOp_sub_const
#print axioms SargentStachurski.AdditionalApplications.abs_markovOp_sub_le
#print axioms SargentStachurski.AdditionalApplications.OrderStable
#print axioms SargentStachurski.AdditionalApplications.IncreasesTo
#print axioms SargentStachurski.AdditionalApplications.DecreasesTo
#print axioms SargentStachurski.AdditionalApplications.StronglyOrderStable
#print axioms SargentStachurski.AdditionalApplications.orderStable_of_up_down
#print axioms SargentStachurski.AdditionalApplications.StronglyOrderStable.orderStable
#print axioms SargentStachurski.AdditionalApplications.dualMap
#print axioms SargentStachurski.AdditionalApplications.orderStable_dual_iff
#print axioms SargentStachurski.AdditionalApplications.dualMap_iterate
#print axioms SargentStachurski.AdditionalApplications.stronglyOrderStable_dual_iff
#print axioms SargentStachurski.AdditionalApplications.ChainComplete
#print axioms SargentStachurski.AdditionalApplications.ChainComplete.exists_least
#print axioms SargentStachurski.AdditionalApplications.ChainComplete.exists_fixedPt_ge
#print axioms SargentStachurski.AdditionalApplications.ChainComplete.exists_fixedPt_le
#print axioms SargentStachurski.AdditionalApplications.ChainComplete.exists_fixedPt
#print axioms SargentStachurski.AdditionalApplications.ChainComplete.orderStable
#print axioms SargentStachurski.AdditionalApplications.chainComplete_Icc
#print axioms SargentStachurski.AdditionalApplications.CountablyDedekindComplete
#print axioms SargentStachurski.AdditionalApplications.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms SargentStachurski.AdditionalApplications.CountablyDedekindComplete.dual
#print axioms SargentStachurski.AdditionalApplications.OrderContinuous
#print axioms SargentStachurski.AdditionalApplications.OrderContinuous.monotone
#print axioms SargentStachurski.AdditionalApplications.isLUB_range_succ_iff
#print axioms SargentStachurski.AdditionalApplications.tarski_kantorovich
#print axioms SargentStachurski.AdditionalApplications.stronglyOrderStable_of_globallyStable
#print axioms SargentStachurski.AdditionalApplications.ADP
#print axioms SargentStachurski.AdditionalApplications.ADP.mk
#print axioms SargentStachurski.AdditionalApplications.ADP.T
#print axioms SargentStachurski.AdditionalApplications.ADP.mono
#print axioms SargentStachurski.AdditionalApplications.ADP.nonempty
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGreedy
#print axioms SargentStachurski.AdditionalApplications.ADP.VG
#print axioms SargentStachurski.AdditionalApplications.ADP.WellPosed
#print axioms SargentStachurski.AdditionalApplications.ADP.IsFinite
#print axioms SargentStachurski.AdditionalApplications.ADP.Regular
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.IsStronglyOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.IsBellmanValue
#print axioms SargentStachurski.AdditionalApplications.ADP.SolvesBellman
#print axioms SargentStachurski.AdditionalApplications.ADP.IsStronglyOrderStable.isOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable.wellPosed
#print axioms SargentStachurski.AdditionalApplications.ADP.regular_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.greedy
#print axioms SargentStachurski.AdditionalApplications.ADP.isGreedy_greedy
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman
#print axioms SargentStachurski.AdditionalApplications.ADP.T_le_bellman
#print axioms SargentStachurski.AdditionalApplications.ADP.isBellmanValue_bellman
#print axioms SargentStachurski.AdditionalApplications.ADP.isGreedy_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.isGreedy_of_isBellmanValue
#print axioms SargentStachurski.AdditionalApplications.ADP.solvesBellman_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman_mono
#print axioms SargentStachurski.AdditionalApplications.ADP.VU
#print axioms SargentStachurski.AdditionalApplications.ADP.VSig
#print axioms SargentStachurski.AdditionalApplications.ADP.VSig_inter_VG_subset
#print axioms SargentStachurski.AdditionalApplications.ADP.vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.T_vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.eq_vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.VSig_eq_range
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOptimal
#print axioms SargentStachurski.AdditionalApplications.ADP.IsValueFunction
#print axioms SargentStachurski.AdditionalApplications.ADP.BellmanPrinciple
#print axioms SargentStachurski.AdditionalApplications.ADP.FundamentalOptimality
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOptimal.isValueFunction
#print axioms SargentStachurski.AdditionalApplications.ADP.isOptimal_of_isValueFunction
#print axioms SargentStachurski.AdditionalApplications.ADP.isOptimal_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.bellmanPrinciple_of_solves
#print axioms SargentStachurski.AdditionalApplications.ADP.exists_solves_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.fundamentalOptimality_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.isOptimal_iff_solvesBellman
#print axioms SargentStachurski.AdditionalApplications.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable.fundamentalOptimality
#print axioms SargentStachurski.AdditionalApplications.ADP.WellPosed.isOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.fundamentalOptimality_of_chainComplete
#print axioms SargentStachurski.AdditionalApplications.ADP.IsSelector
#print axioms SargentStachurski.AdditionalApplications.ADP.Regular.isSelector_greedy
#print axioms SargentStachurski.AdditionalApplications.ADP.howard
#print axioms SargentStachurski.AdditionalApplications.ADP.opt
#print axioms SargentStachurski.AdditionalApplications.ADP.IsSelector.T_eq
#print axioms SargentStachurski.AdditionalApplications.ADP.mem_VU_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman_eq_of_howard_eq
#print axioms SargentStachurski.AdditionalApplications.ADP.iterate_mono_of_le
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman_le_opt
#print axioms SargentStachurski.AdditionalApplications.ADP.chain_2_9
#print axioms SargentStachurski.AdditionalApplications.ADP.mapsTo_VU
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman_le_of_le
#print axioms SargentStachurski.AdditionalApplications.ADP.iterates_of_mem_VU
#print axioms SargentStachurski.AdditionalApplications.ADP.VFIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.OPIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.HPIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.opt_one
#print axioms SargentStachurski.AdditionalApplications.ADP.OPIConverges.vfi
#print axioms SargentStachurski.AdditionalApplications.ADP.le_vstar_of_mem_VU
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable.le_vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable.vσ_le
#print axioms SargentStachurski.AdditionalApplications.ADP.iterates_le_vstar
#print axioms SargentStachurski.AdditionalApplications.ADP.increasesTo_of_squeeze
#print axioms SargentStachurski.AdditionalApplications.ADP.VFIConverges.opi_hpi
#print axioms SargentStachurski.AdditionalApplications.ADP.VU_nonempty
#print axioms SargentStachurski.AdditionalApplications.ADP.IsFinite.VSig_finite
#print axioms SargentStachurski.AdditionalApplications.ADP.exists_succ_eq_of_finite
#print axioms SargentStachurski.AdditionalApplications.ADP.fundamentalOptimality_of_finite
#print axioms SargentStachurski.AdditionalApplications.ADP.FundamentalOptimality.exists_vstar
#print axioms SargentStachurski.AdditionalApplications.ADP.convergence_of_chainComplete
#print axioms SargentStachurski.AdditionalApplications.ADP.OrderBounded
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderContinuous
#print axioms SargentStachurski.AdditionalApplications.ADP.le_of_orderBounded
#print axioms SargentStachurski.AdditionalApplications.ADP.convergence_of_dedekind
#print axioms SargentStachurski.AdditionalApplications.isLUB_of_tendsto_of_le
#print axioms SargentStachurski.AdditionalApplications.isGLB_of_tendsto_of_le
#print axioms SargentStachurski.AdditionalApplications.ADP.monotone_iterate_of_le
#print axioms SargentStachurski.AdditionalApplications.ADP.Regular.bellman_monotone
#print axioms SargentStachurski.AdditionalApplications.ADP.Regular.iterate_T_le_bellman
#print axioms SargentStachurski.AdditionalApplications.ADP.bellman_iterate_le_of_bound
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable.wellPosed
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable.tendsto_vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable.isStronglyOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable.isOrderStable
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_2
#print axioms SargentStachurski.AdditionalApplications.ADP.corollary_3_1_3
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_4
#print axioms SargentStachurski.AdditionalApplications.IsSupNonexpansive
#print axioms SargentStachurski.AdditionalApplications.IsInfNonexpansive
#print axioms SargentStachurski.AdditionalApplications.isInfNonexpansive_iff
#print axioms SargentStachurski.AdditionalApplications.isSupNonexpansive_real
#print axioms SargentStachurski.AdditionalApplications.isSupNonexpansive_pi
#print axioms SargentStachurski.AdditionalApplications.ADP.lemma_A_5_21
#print axioms SargentStachurski.AdditionalApplications.ADP.IsSemiRegular
#print axioms SargentStachurski.AdditionalApplications.ADP.VFIGeometric
#print axioms SargentStachurski.AdditionalApplications.ADP.isGloballyStable_of_contraction
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_5
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_5_needs_nonempty
#print axioms SargentStachurski.AdditionalApplications.BM
#print axioms SargentStachurski.AdditionalApplications.BM.mk
#print axioms SargentStachurski.AdditionalApplications.BM.toFun
#print axioms SargentStachurski.AdditionalApplications.BM.measurable'
#print axioms SargentStachurski.AdditionalApplications.BM.bdd'
#print axioms SargentStachurski.AdditionalApplications.BM.ext
#print axioms SargentStachurski.AdditionalApplications.BM.bddAbove
#print axioms SargentStachurski.AdditionalApplications.BM.const
#print axioms SargentStachurski.AdditionalApplications.BM.toFun_injective
#print axioms SargentStachurski.AdditionalApplications.BM.zero
#print axioms SargentStachurski.AdditionalApplications.BM.add
#print axioms SargentStachurski.AdditionalApplications.BM.neg
#print axioms SargentStachurski.AdditionalApplications.BM.sub
#print axioms SargentStachurski.AdditionalApplications.BM.smulReal
#print axioms SargentStachurski.AdditionalApplications.BM.nsmul
#print axioms SargentStachurski.AdditionalApplications.BM.zsmul
#print axioms SargentStachurski.AdditionalApplications.BM.addCommGroup
#print axioms SargentStachurski.AdditionalApplications.BM.supNorm
#print axioms SargentStachurski.AdditionalApplications.BM.abs_le_supNorm
#print axioms SargentStachurski.AdditionalApplications.BM.supNorm_le
#print axioms SargentStachurski.AdditionalApplications.BM.supNorm_nonneg
#print axioms SargentStachurski.AdditionalApplications.BM.normedAddCommGroup
#print axioms SargentStachurski.AdditionalApplications.BM.add_apply
#print axioms SargentStachurski.AdditionalApplications.BM.sub_apply
#print axioms SargentStachurski.AdditionalApplications.BM.neg_apply
#print axioms SargentStachurski.AdditionalApplications.BM.zero_apply
#print axioms SargentStachurski.AdditionalApplications.BM.const_apply
#print axioms SargentStachurski.AdditionalApplications.BM.norm_def
#print axioms SargentStachurski.AdditionalApplications.BM.abs_le_norm
#print axioms SargentStachurski.AdditionalApplications.BM.norm_le
#print axioms SargentStachurski.AdditionalApplications.BM.abs_sub_le_dist
#print axioms SargentStachurski.AdditionalApplications.BM.dist_le
#print axioms SargentStachurski.AdditionalApplications.BM.module
#print axioms SargentStachurski.AdditionalApplications.BM.smul_apply
#print axioms SargentStachurski.AdditionalApplications.BM.normedSpace
#print axioms SargentStachurski.AdditionalApplications.BM.lattice
#print axioms SargentStachurski.AdditionalApplications.BM.le_def
#print axioms SargentStachurski.AdditionalApplications.BM.sup_apply
#print axioms SargentStachurski.AdditionalApplications.BM.inf_apply
#print axioms SargentStachurski.AdditionalApplications.BM.abs_apply
#print axioms SargentStachurski.AdditionalApplications.BM.isOrderedAddMonoid
#print axioms SargentStachurski.AdditionalApplications.BM.hasSolidNorm
#print axioms SargentStachurski.AdditionalApplications.BM.completeSpace
#print axioms SargentStachurski.AdditionalApplications.BM.countablyDedekindComplete
#print axioms SargentStachurski.AdditionalApplications.BM.isSupNonexpansive
#print axioms SargentStachurski.AdditionalApplications.BM.isInfNonexpansive
#print axioms SargentStachurski.AdditionalApplications.BM.mem_bX
#print axioms SargentStachurski.AdditionalApplications.BM.tendsto_of_tendstoUniformly
#print axioms SargentStachurski.AdditionalApplications.BM.tendstoUniformly_of_tendsto
#print axioms SargentStachurski.AdditionalApplications.BM.globallyStable_of_bX
#print axioms SargentStachurski.AdditionalApplications.pow_div_le_geometric
#print axioms SargentStachurski.AdditionalApplications.theorem_4_1_1
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsNormalizedOrderUnit
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsNormalizedOrderUnit.smul_mono
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsNormalizedOrderUnit.le_add
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsNormalizedOrderUnit.norm_sub_le
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.isSupNonexpansive
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.isInfNonexpansive
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.isSupNonexpansive_subtype
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.lemma_4_1_2
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.lemma_4_1_2_subtype
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_3
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_3_univ
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsCertaintyEquivalent
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.exercise_4_1_2
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.exercise_4_1_2_subtype
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsDiscountOperator
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsDiscountOperator.exercise_4_1_3
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsDiscountOperator.iterate_nonneg
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsDiscountOperator.iterate_mono
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.specRad
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.exercise_A_4_2
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.specRad_le_norm
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsPositiveOp
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsPositiveOp.mono
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsPositiveOp.abs_le
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsPositiveOp.iterate
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.example_4_1_1
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsIsoOrderEmbedding
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsOrderContraction
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsOrderContraction.iterate
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_4
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.example_4_1_2
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.exercise_4_1_4
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_5
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.bellman_orderContraction
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_6
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsAdditive
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.IsAdditive.abs_sub
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_7
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_8
#print axioms SargentStachurski.AdditionalApplications.BM.posSMulMono
#print axioms SargentStachurski.AdditionalApplications.BM.one_apply
#print axioms SargentStachurski.AdditionalApplications.BM.isNormalizedOrderUnit_one
#print axioms SargentStachurski.AdditionalApplications.BM.markovLin
#print axioms SargentStachurski.AdditionalApplications.BM.markovCLM
#print axioms SargentStachurski.AdditionalApplications.BM.markovCLM_apply
#print axioms SargentStachurski.AdditionalApplications.BM.markovCLM_isPositive
#print axioms SargentStachurski.AdditionalApplications.BM.markovCLM_const
#print axioms SargentStachurski.AdditionalApplications.BM.mulLin
#print axioms SargentStachurski.AdditionalApplications.BM.mulCLM
#print axioms SargentStachurski.AdditionalApplications.BM.mulCLM_apply
#print axioms SargentStachurski.AdditionalApplications.BM.mulCLM_isPositive
#print axioms SargentStachurski.AdditionalApplications.sup'_add_const
#print axioms SargentStachurski.AdditionalApplications.harrisonKreps
#print axioms SargentStachurski.AdditionalApplications.exercise_4_1_1
#print axioms SargentStachurski.AdditionalApplications.IsLHC
#print axioms SargentStachurski.AdditionalApplications.IsUHC
#print axioms SargentStachurski.AdditionalApplications.IsContinuousCorr
#print axioms SargentStachurski.AdditionalApplications.clamp_mem
#print axioms SargentStachurski.AdditionalApplications.clamp_eq
#print axioms SargentStachurski.AdditionalApplications.exists_subseq_Icc
#print axioms SargentStachurski.AdditionalApplications.exercise_A_3_1
#print axioms SargentStachurski.AdditionalApplications.HasMaxSelections
#print axioms SargentStachurski.AdditionalApplications.IccMax.argmax
#print axioms SargentStachurski.AdditionalApplications.IccMax.sel
#print axioms SargentStachurski.AdditionalApplications.IccMax.continuousOn_section
#print axioms SargentStachurski.AdditionalApplications.IccMax.argmax_nonempty
#print axioms SargentStachurski.AdditionalApplications.IccMax.isClosed_argmax
#print axioms SargentStachurski.AdditionalApplications.IccMax.sel_mem
#print axioms SargentStachurski.AdditionalApplications.IccMax.isClosed_le_sel
#print axioms SargentStachurski.AdditionalApplications.IccMax.exists_param
#print axioms SargentStachurski.AdditionalApplications.IccMax.continuous_max
#print axioms SargentStachurski.AdditionalApplications.IccMax.measurable_sel
#print axioms SargentStachurski.AdditionalApplications.hasMaxSelections_Icc
#print axioms SargentStachurski.AdditionalApplications.LDP
#print axioms SargentStachurski.AdditionalApplications.LDP.mk
#print axioms SargentStachurski.AdditionalApplications.LDP.Γ
#print axioms SargentStachurski.AdditionalApplications.LDP.r
#print axioms SargentStachurski.AdditionalApplications.LDP.β
#print axioms SargentStachurski.AdditionalApplications.LDP.β_nonneg
#print axioms SargentStachurski.AdditionalApplications.LDP.P
#print axioms SargentStachurski.AdditionalApplications.LDP.exists_policy
#print axioms SargentStachurski.AdditionalApplications.LDP.Policy
#print axioms SargentStachurski.AdditionalApplications.LDP.nonempty_policy
#print axioms SargentStachurski.AdditionalApplications.LDP.measurable_graph
#print axioms SargentStachurski.AdditionalApplications.LDP.along
#print axioms SargentStachurski.AdditionalApplications.LDP.rσ
#print axioms SargentStachurski.AdditionalApplications.LDP.βσ
#print axioms SargentStachurski.AdditionalApplications.LDP.Pσ
#print axioms SargentStachurski.AdditionalApplications.LDP.K
#print axioms SargentStachurski.AdditionalApplications.LDP.K_apply
#print axioms SargentStachurski.AdditionalApplications.LDP.K_isPositive
#print axioms SargentStachurski.AdditionalApplications.LDP.norm_K_le
#print axioms SargentStachurski.AdditionalApplications.LDP.adp
#print axioms SargentStachurski.AdditionalApplications.LDP.T_apply
#print axioms SargentStachurski.AdditionalApplications.LDP.isAdditive
#print axioms SargentStachurski.AdditionalApplications.LDP.obj
#print axioms SargentStachurski.AdditionalApplications.LDP.T_apply_obj
#print axioms SargentStachurski.AdditionalApplications.LDP.isGreedy_iff
#print axioms SargentStachurski.AdditionalApplications.LDP.isGreedy_of_argmax
#print axioms SargentStachurski.AdditionalApplications.LDP.argmax_of_isGreedy
#print axioms SargentStachurski.AdditionalApplications.LDP.iterate_T_zero
#print axioms SargentStachurski.AdditionalApplications.LDP.globallyStable_T
#print axioms SargentStachurski.AdditionalApplications.LDP.lifetime_value
#print axioms SargentStachurski.AdditionalApplications.LDP.firm
#print axioms SargentStachurski.AdditionalApplications.LDP.firm_T_apply
#print axioms SargentStachurski.AdditionalApplications.example_6_1_6
#print axioms SargentStachurski.AdditionalApplications.argmaxSet
#print axioms SargentStachurski.AdditionalApplications.argmaxSet_nonempty
#print axioms SargentStachurski.AdditionalApplications.argmaxSel
#print axioms SargentStachurski.AdditionalApplications.argmaxSel_max
#print axioms SargentStachurski.AdditionalApplications.measurable_argmaxSel
#print axioms SargentStachurski.AdditionalApplications.LDP.regular_of_isFinite
#print axioms SargentStachurski.AdditionalApplications.LDP.proposition_6_1_2
#print axioms SargentStachurski.AdditionalApplications.LDP.G
#print axioms SargentStachurski.AdditionalApplications.LDP.IsWeakFeller
#print axioms SargentStachurski.AdditionalApplications.LDP.IsStrongFeller
#print axioms SargentStachurski.AdditionalApplications.LDP.IsStrongFeller.isWeakFeller
#print axioms SargentStachurski.AdditionalApplications.LDP.bc
#print axioms SargentStachurski.AdditionalApplications.LDP.isClosed_bc
#print axioms SargentStachurski.AdditionalApplications.LDP.zero_mem_bc
#print axioms SargentStachurski.AdditionalApplications.LDP.continuousOn_obj
#print axioms SargentStachurski.AdditionalApplications.LDP.greedy_of_continuousOn
#print axioms SargentStachurski.AdditionalApplications.LDP.proposition_6_1_3
#print axioms SargentStachurski.AdditionalApplications.LDP.implications
#print axioms SargentStachurski.AdditionalApplications.LDP.implications_bc
#print axioms SargentStachurski.AdditionalApplications.measurable_section
#print axioms SargentStachurski.AdditionalApplications.shockKernel
#print axioms SargentStachurski.AdditionalApplications.shockKernel_apply
#print axioms SargentStachurski.AdditionalApplications.shockKernel_isMarkov
#print axioms SargentStachurski.AdditionalApplications.integral_shockKernel
#print axioms SargentStachurski.AdditionalApplications.example_6_1_1
#print axioms SargentStachurski.AdditionalApplications.scheffe
#print axioms SargentStachurski.AdditionalApplications.lemma_6_1_1
#print axioms SargentStachurski.AdditionalApplications.example_6_1_2
#print axioms SargentStachurski.AdditionalApplications.exists_measurable_argmax
#print axioms SargentStachurski.AdditionalApplications.HasContinuousUniqueMax
#print axioms SargentStachurski.AdditionalApplications.hasContinuousUniqueMax_Icc
#print axioms SargentStachurski.AdditionalApplications.FeasiblePolicy
#print axioms SargentStachurski.AdditionalApplications.RDP
#print axioms SargentStachurski.AdditionalApplications.RDP.mk
#print axioms SargentStachurski.AdditionalApplications.RDP.ev
#print axioms SargentStachurski.AdditionalApplications.RDP.ev_le_iff
#print axioms SargentStachurski.AdditionalApplications.RDP.Γ
#print axioms SargentStachurski.AdditionalApplications.RDP.B
#print axioms SargentStachurski.AdditionalApplications.RDP.mono
#print axioms SargentStachurski.AdditionalApplications.RDP.consistent
#print axioms SargentStachurski.AdditionalApplications.RDP.exists_policy
#print axioms SargentStachurski.AdditionalApplications.RDP.Policy
#print axioms SargentStachurski.AdditionalApplications.RDP.ev_injective
#print axioms SargentStachurski.AdditionalApplications.RDP.nonempty_Γ
#print axioms SargentStachurski.AdditionalApplications.RDP.T
#print axioms SargentStachurski.AdditionalApplications.RDP.ev_T
#print axioms SargentStachurski.AdditionalApplications.RDP.adp
#print axioms SargentStachurski.AdditionalApplications.RDP.ev_adp_T
#print axioms SargentStachurski.AdditionalApplications.RDP.isGreedy_iff
#print axioms SargentStachurski.AdditionalApplications.RDP.IsArgmax
#print axioms SargentStachurski.AdditionalApplications.RDP.isGreedy_of_isArgmax
#print axioms SargentStachurski.AdditionalApplications.RDP.bellman_of_isArgmax
#print axioms SargentStachurski.AdditionalApplications.RDP.isGreedy_iff_isArgmax
#print axioms SargentStachurski.AdditionalApplications.RDP.lemma_7_1_1
#print axioms SargentStachurski.AdditionalApplications.RDP.lemma_7_1_2
#print axioms SargentStachurski.AdditionalApplications.RDP.exercise_7_1_5
#print axioms SargentStachurski.AdditionalApplications.BRDP
#print axioms SargentStachurski.AdditionalApplications.BRDP.mk
#print axioms SargentStachurski.AdditionalApplications.BRDP.Γ
#print axioms SargentStachurski.AdditionalApplications.BRDP.B
#print axioms SargentStachurski.AdditionalApplications.BRDP.measurable
#print axioms SargentStachurski.AdditionalApplications.BRDP.mono
#print axioms SargentStachurski.AdditionalApplications.BRDP.bdd
#print axioms SargentStachurski.AdditionalApplications.BRDP.exists_policy
#print axioms SargentStachurski.AdditionalApplications.BRDP.toRDP
#print axioms SargentStachurski.AdditionalApplications.BRDP.toRDP_T_apply
#print axioms SargentStachurski.AdditionalApplications.BRDP.IsBlackwell
#print axioms SargentStachurski.AdditionalApplications.BRDP.T_blackwell
#print axioms SargentStachurski.AdditionalApplications.BRDP.regular_of_finite
#print axioms SargentStachurski.AdditionalApplications.BRDP.proposition_7_2_1
#print axioms SargentStachurski.AdditionalApplications.BRDP.proposition_7_2_1_finite
#print axioms SargentStachurski.AdditionalApplications.BRDP.greedy_of_continuous
#print axioms SargentStachurski.AdditionalApplications.BRDP.proposition_7_2_2
#print axioms SargentStachurski.AdditionalApplications.wnorm
#print axioms SargentStachurski.AdditionalApplications.bl
#print axioms SargentStachurski.AdditionalApplications.blPlus
#print axioms SargentStachurski.AdditionalApplications.wevB
#print axioms SargentStachurski.AdditionalApplications.wevB_mem
#print axioms SargentStachurski.AdditionalApplications.norm_eq_wnorm
#print axioms SargentStachurski.AdditionalApplications.exercise_A_5_22
#print axioms SargentStachurski.AdditionalApplications.exercise_A_5_24
#print axioms SargentStachurski.AdditionalApplications.exercise_A_5_25
#print axioms SargentStachurski.AdditionalApplications.posCone
#print axioms SargentStachurski.AdditionalApplications.isClosed_posCone
#print axioms SargentStachurski.AdditionalApplications.add_mem_posCone
#print axioms SargentStachurski.AdditionalApplications.wev
#print axioms SargentStachurski.AdditionalApplications.wev_mem
#print axioms SargentStachurski.AdditionalApplications.ofBl
#print axioms SargentStachurski.AdditionalApplications.wev_ofBl
#print axioms SargentStachurski.AdditionalApplications.wev_le_iff
#print axioms SargentStachurski.AdditionalApplications.bcPlus
#print axioms SargentStachurski.AdditionalApplications.isClosed_bcPlus
#print axioms SargentStachurski.AdditionalApplications.zero_mem_bcPlus
#print axioms SargentStachurski.AdditionalApplications.WRDP
#print axioms SargentStachurski.AdditionalApplications.WRDP.mk
#print axioms SargentStachurski.AdditionalApplications.WRDP.ℓ
#print axioms SargentStachurski.AdditionalApplications.WRDP.measurable_ℓ
#print axioms SargentStachurski.AdditionalApplications.WRDP.one_le_ℓ
#print axioms SargentStachurski.AdditionalApplications.WRDP.Γ
#print axioms SargentStachurski.AdditionalApplications.WRDP.B
#print axioms SargentStachurski.AdditionalApplications.WRDP.measurable
#print axioms SargentStachurski.AdditionalApplications.WRDP.nonneg
#print axioms SargentStachurski.AdditionalApplications.WRDP.mono
#print axioms SargentStachurski.AdditionalApplications.WRDP.U2
#print axioms SargentStachurski.AdditionalApplications.WRDP.exists_policy
#print axioms SargentStachurski.AdditionalApplications.WRDP.toRDP
#print axioms SargentStachurski.AdditionalApplications.WRDP.toRDP_T_apply
#print axioms SargentStachurski.AdditionalApplications.WRDP.IsBlackwell
#print axioms SargentStachurski.AdditionalApplications.WRDP.T_blackwell
#print axioms SargentStachurski.AdditionalApplications.WRDP.regular_of_finite
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_4
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_4_finite
#print axioms SargentStachurski.AdditionalApplications.WRDP.greedy_of_continuous
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_5
#print axioms SargentStachurski.AdditionalApplications.lemma_A_2_6
#print axioms SargentStachurski.AdditionalApplications.eq_of_isMax_of_strictConcaveOn
#print axioms SargentStachurski.AdditionalApplications.ADP.VFIGeometric.tendsto
#print axioms SargentStachurski.AdditionalApplications.coneZero
#print axioms SargentStachurski.AdditionalApplications.wev_coneZero
#print axioms SargentStachurski.AdditionalApplications.exercise_7_2_1
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.mk
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.ℓ_continuous
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.maxSel
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.blackwell
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.continuousOn
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.prop
#print axioms SargentStachurski.AdditionalApplications.WRDP.ContinuousCase.vstar_mem
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_6
#print axioms SargentStachurski.AdditionalApplications.WRDP.isClosed_concave
#print axioms SargentStachurski.AdditionalApplications.WRDP.feasibleOn
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_7
#print axioms SargentStachurski.AdditionalApplications.WRDP.proposition_7_2_8
#print axioms SargentStachurski.AdditionalApplications.ADP.dual
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_dual
#print axioms SargentStachurski.AdditionalApplications.ADP.IsMinGreedy
#print axioms SargentStachurski.AdditionalApplications.ADP.VGmin
#print axioms SargentStachurski.AdditionalApplications.ADP.MinRegular
#print axioms SargentStachurski.AdditionalApplications.ADP.MinOrderBounded
#print axioms SargentStachurski.AdditionalApplications.ADP.IsMinBellmanValue
#print axioms SargentStachurski.AdditionalApplications.ADP.SolvesMinBellman
#print axioms SargentStachurski.AdditionalApplications.ADP.IsMinValueFunction
#print axioms SargentStachurski.AdditionalApplications.ADP.IsMinOptimal
#print axioms SargentStachurski.AdditionalApplications.ADP.MinBellmanPrinciple
#print axioms SargentStachurski.AdditionalApplications.ADP.MinFundamentalOptimality
#print axioms SargentStachurski.AdditionalApplications.ADP.isMinGreedy_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.minRegular_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.minOrderBounded_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.isMinBellmanValue_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.VGmin_eq
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_VSig
#print axioms SargentStachurski.AdditionalApplications.ADP.WellPosed.dual
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_vσ
#print axioms SargentStachurski.AdditionalApplications.ADP.isMinValueFunction_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.isMinOptimal_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_opt_howard
#print axioms SargentStachurski.AdditionalApplications.ADP.minBellmanPrinciple_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.minFundamentalOptimality_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.VD
#print axioms SargentStachurski.AdditionalApplications.ADP.MinVFIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.minVFIConverges_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms SargentStachurski.AdditionalApplications.ADP.IsOrderStable.minFundamentalOptimality
#print axioms SargentStachurski.AdditionalApplications.ADP.IsMinSelector
#print axioms SargentStachurski.AdditionalApplications.ADP.MinOPIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.MinHPIConverges
#print axioms SargentStachurski.AdditionalApplications.ADP.isMinSelector_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_opt_iterate
#print axioms SargentStachurski.AdditionalApplications.ADP.dual_howard_iterate
#print axioms SargentStachurski.AdditionalApplications.ADP.minOPIConverges_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.minHPIConverges_iff
#print axioms SargentStachurski.AdditionalApplications.ADP.min_of_dual
#print axioms SargentStachurski.AdditionalApplications.ADP.IsGloballyStable.dual
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_6
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_8
#print axioms SargentStachurski.AdditionalApplications.ADP.theorem_3_1_7
#print axioms SargentStachurski.AdditionalApplications.vShapeOrder
#print axioms SargentStachurski.AdditionalApplications.vShapeDist
#print axioms SargentStachurski.AdditionalApplications.vShapeDist_metric
#print axioms SargentStachurski.AdditionalApplications.vShape_isLUB
#print axioms SargentStachurski.AdditionalApplications.vShape_sup_not_inf
#print axioms SargentStachurski.AdditionalApplications.IsUniqueFixed
#print axioms SargentStachurski.AdditionalApplications.IsConjugate
#print axioms SargentStachurski.AdditionalApplications.IsConjugate.symm
#print axioms SargentStachurski.AdditionalApplications.IsConjugate.iterate
#print axioms SargentStachurski.AdditionalApplications.IsConjugate.fixed_iff
#print axioms SargentStachurski.AdditionalApplications.IsConjugate.fixed_iff_symm
#print axioms SargentStachurski.AdditionalApplications.IsConjugate.isUniqueFixed_iff
#print axioms SargentStachurski.AdditionalApplications.example_5_1_1
#print axioms SargentStachurski.AdditionalApplications.coordChange
#print axioms SargentStachurski.AdditionalApplications.example_5_1_2
#print axioms SargentStachurski.AdditionalApplications.IsTopConjugate
#print axioms SargentStachurski.AdditionalApplications.IsTopConjugate.symm
#print axioms SargentStachurski.AdditionalApplications.IsTopConjugate.globallyStable
#print axioms SargentStachurski.AdditionalApplications.proposition_5_1_2
#print axioms SargentStachurski.AdditionalApplications.coordHomeo
#print axioms SargentStachurski.AdditionalApplications.iterate_diagonal_mulVec
#print axioms SargentStachurski.AdditionalApplications.globallyStable_diagonal_iff
#print axioms SargentStachurski.AdditionalApplications.example_5_1_3
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate
#print axioms SargentStachurski.AdditionalApplications.orderIso_increasesTo
#print axioms SargentStachurski.AdditionalApplications.orderIso_decreasesTo
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.refl
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.symm
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.trans
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.orderStable
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.stronglyOrderStable
#print axioms SargentStachurski.AdditionalApplications.IsOrderConjugate.lemma_5_1_3
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj
#print axioms SargentStachurski.AdditionalApplications.OrderContinuousDown
#print axioms SargentStachurski.AdditionalApplications.AntiContinuousUp
#print axioms SargentStachurski.AdditionalApplications.AntiContinuousDown
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.swap
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.exercise_5_2_1
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.iterate_succ
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.fixed_F
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.fixed_G
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.isUniqueFixed
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.existsUnique_iff
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.orderStable_mono
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.orderStable_anti
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.lemma_5_2_2_i
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.increasesTo_of_succ
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.decreasesTo_of_succ
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.stronglyOrderStable_mono
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.stronglyOrderStable_anti
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.lemma_5_2_2_ii
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.theorem_5_2_3
#print axioms SargentStachurski.AdditionalApplications.IsStronglySemiconj.theorem_5_2_4
#print axioms SargentStachurski.AdditionalApplications.FDP
#print axioms SargentStachurski.AdditionalApplications.FDP.mk
#print axioms SargentStachurski.AdditionalApplications.FDP.F
#print axioms SargentStachurski.AdditionalApplications.FDP.G
#print axioms SargentStachurski.AdditionalApplications.FDP.greatest
#print axioms SargentStachurski.AdditionalApplications.FDP.nonempty
#print axioms SargentStachurski.AdditionalApplications.FDP.IsOrderPreserving
#print axioms SargentStachurski.AdditionalApplications.FDP.IsOrderReversing
#print axioms SargentStachurski.AdditionalApplications.FDP.Monotonic
#print axioms SargentStachurski.AdditionalApplications.FDP.gsel
#print axioms SargentStachurski.AdditionalApplications.FDP.Gsup
#print axioms SargentStachurski.AdditionalApplications.FDP.G_le_Gsup
#print axioms SargentStachurski.AdditionalApplications.FDP.isGreatest_Gsup
#print axioms SargentStachurski.AdditionalApplications.FDP.primary
#print axioms SargentStachurski.AdditionalApplications.FDP.sub
#print axioms SargentStachurski.AdditionalApplications.FDP.primary_regular
#print axioms SargentStachurski.AdditionalApplications.FDP.primary_bellman
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_9
#print axioms SargentStachurski.AdditionalApplications.FDP.sub_isGreedy_of_eq
#print axioms SargentStachurski.AdditionalApplications.FDP.sub_regular
#print axioms SargentStachurski.AdditionalApplications.FDP.sub_bellman
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_10
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_11
#print axioms SargentStachurski.AdditionalApplications.FDP.policy_semiconj
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_12
#print axioms SargentStachurski.AdditionalApplications.FDP.sub_isValueFunction
#print axioms SargentStachurski.AdditionalApplications.FDP.primary_isValueFunction
#print axioms SargentStachurski.AdditionalApplications.FDP.fo_sub_of_primary
#print axioms SargentStachurski.AdditionalApplications.FDP.fo_primary_of_sub
#print axioms SargentStachurski.AdditionalApplications.FDP.theorem_5_2_13
#print axioms SargentStachurski.AdditionalApplications.FDP.proposition_5_2_14
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize_isOrderPreserving
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize_monotonic
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize_primary
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize_sub
#print axioms SargentStachurski.AdditionalApplications.FDP.dualize_Gsup
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_16
#print axioms SargentStachurski.AdditionalApplications.FDP.lemma_5_2_17
#print axioms SargentStachurski.AdditionalApplications.FDP.theorem_5_2_18
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.GloballyStableOn
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.DuConditions
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.abs_sub_le_of_mem_Icc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.norm_sub_le_of_mem_Icc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.iterate_mem_Icc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.du_concave
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.neg_mem_Icc_iff'
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.iterate_reflect
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.globallyStableOn_of_reflect
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.du_convex
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_10
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.lemma_4_1_9_concave
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.lemma_4_1_9_convex
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.lemma_4_1_9
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.extendIcc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.extendIcc_apply
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.extendIcc_iterate
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.globallyStable_of_extendIcc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_10_subtype
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.countablyDedekindComplete_Icc
#print axioms SargentStachurski.AdditionalApplications.BanachLattice.theorem_4_1_11
#print axioms SargentStachurski.AdditionalApplications.L1.ae_ae_of_stationary
#print axioms SargentStachurski.AdditionalApplications.L1.lintegral_stationary
#print axioms SargentStachurski.AdditionalApplications.L1.markovFun
#print axioms SargentStachurski.AdditionalApplications.L1.lintegral_markov_le
#print axioms SargentStachurski.AdditionalApplications.L1.memLp_markovFun
#print axioms SargentStachurski.AdditionalApplications.L1.ae_integrable
#print axioms SargentStachurski.AdditionalApplications.L1.markovFun_congr
#print axioms SargentStachurski.AdditionalApplications.L1.markovLin
#print axioms SargentStachurski.AdditionalApplications.L1.markovLin_apply
#print axioms SargentStachurski.AdditionalApplications.L1.markovLin_norm_le
#print axioms SargentStachurski.AdditionalApplications.L1.markovCLM
#print axioms SargentStachurski.AdditionalApplications.L1.markovCLM_norm_le
#print axioms SargentStachurski.AdditionalApplications.L1.markovCLM_coeFn
#print axioms SargentStachurski.AdditionalApplications.L1.markovCLM_isPositive
#print axioms SargentStachurski.AdditionalApplications.L1.memLp_mul
#print axioms SargentStachurski.AdditionalApplications.L1.mulLin
#print axioms SargentStachurski.AdditionalApplications.L1.mulLin_apply
#print axioms SargentStachurski.AdditionalApplications.L1.mulCLM
#print axioms SargentStachurski.AdditionalApplications.L1.mulCLM_coeFn
#print axioms SargentStachurski.AdditionalApplications.L1.mulCLM_isPositive
#print axioms SargentStachurski.AdditionalApplications.L1.mulCLM_le_self
#print axioms SargentStachurski.AdditionalApplications.StopPolicy
#print axioms SargentStachurski.AdditionalApplications.polInd
#print axioms SargentStachurski.AdditionalApplications.polCont
#print axioms SargentStachurski.AdditionalApplications.measurable_polInd
#print axioms SargentStachurski.AdditionalApplications.measurable_polCont
#print axioms SargentStachurski.AdditionalApplications.abs_polInd_le
#print axioms SargentStachurski.AdditionalApplications.abs_polCont_le
#print axioms SargentStachurski.AdditionalApplications.polCont_nonneg
#print axioms SargentStachurski.AdditionalApplications.polCont_le_one
#print axioms SargentStachurski.AdditionalApplications.polInd_nonneg
#print axioms SargentStachurski.AdditionalApplications.acceptWhere
#print axioms SargentStachurski.AdditionalApplications.acceptWhere_apply
#print axioms SargentStachurski.AdditionalApplications.isIsoOrderEmbedding_id_L1
#print axioms SargentStachurski.AdditionalApplications.JobSearch
#print axioms SargentStachurski.AdditionalApplications.JobSearch.mk
#print axioms SargentStachurski.AdditionalApplications.JobSearch.P
#print axioms SargentStachurski.AdditionalApplications.JobSearch.φ
#print axioms SargentStachurski.AdditionalApplications.JobSearch.stationary
#print axioms SargentStachurski.AdditionalApplications.JobSearch.wage
#print axioms SargentStachurski.AdditionalApplications.JobSearch.measurable_wage
#print axioms SargentStachurski.AdditionalApplications.JobSearch.integrable_wage
#print axioms SargentStachurski.AdditionalApplications.JobSearch.c
#print axioms SargentStachurski.AdditionalApplications.JobSearch.β
#print axioms SargentStachurski.AdditionalApplications.JobSearch.β_nonneg
#print axioms SargentStachurski.AdditionalApplications.JobSearch.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Pop
#print axioms SargentStachurski.AdditionalApplications.JobSearch.D
#print axioms SargentStachurski.AdditionalApplications.JobSearch.efun
#print axioms SargentStachurski.AdditionalApplications.JobSearch.measurable_efun
#print axioms SargentStachurski.AdditionalApplications.JobSearch.e
#print axioms SargentStachurski.AdditionalApplications.JobSearch.cconst
#print axioms SargentStachurski.AdditionalApplications.JobSearch.e_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearch.cconst_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearch.rσ
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Kσ
#print axioms SargentStachurski.AdditionalApplications.JobSearch.D_isPositive
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Kσ_isPositive
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Kσ_le_D
#print axioms SargentStachurski.AdditionalApplications.JobSearch.norm_D_le
#print axioms SargentStachurski.AdditionalApplications.JobSearch.specRad_D_lt_one
#print axioms SargentStachurski.AdditionalApplications.JobSearch.adp
#print axioms SargentStachurski.AdditionalApplications.JobSearch.T_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_14
#print axioms SargentStachurski.AdditionalApplications.JobSearch.accept
#print axioms SargentStachurski.AdditionalApplications.JobSearch.T_accept_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_15
#print axioms SargentStachurski.AdditionalApplications.JobSearch.regular
#print axioms SargentStachurski.AdditionalApplications.JobSearch.isAdditive
#print axioms SargentStachurski.AdditionalApplications.JobSearch.isGloballyStable
#print axioms SargentStachurski.AdditionalApplications.JobSearch.iterate_T_zero
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_17
#print axioms SargentStachurski.AdditionalApplications.JobSearch.wellPosed
#print axioms SargentStachurski.AdditionalApplications.JobSearch.proposition_8_1_2
#print axioms SargentStachurski.AdditionalApplications.L1.tendsto_of_monotone_isLUB
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_16
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Sbar
#print axioms SargentStachurski.AdditionalApplications.JobSearch.Sbar_contracting
#print axioms SargentStachurski.AdditionalApplications.JobSearch.vbar
#print axioms SargentStachurski.AdditionalApplications.JobSearch.vbar_eq
#print axioms SargentStachurski.AdditionalApplications.JobSearch.e_nonneg
#print axioms SargentStachurski.AdditionalApplications.JobSearch.cconst_nonneg
#print axioms SargentStachurski.AdditionalApplications.JobSearch.vbar_nonneg
#print axioms SargentStachurski.AdditionalApplications.JobSearch.T_le_Sbar
#print axioms SargentStachurski.AdditionalApplications.JobSearch.T_nonneg
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_18
#print axioms SargentStachurski.AdditionalApplications.JobSearch.adpV
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_19
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_20
#print axioms SargentStachurski.AdditionalApplications.JobSearch.iid
#print axioms SargentStachurski.AdditionalApplications.JobSearch.iid_Pop_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearch.exercise_8_1_2_3
#print axioms SargentStachurski.AdditionalApplications.JobSearch.proposition_8_1_1
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.cont
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.T
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.T_apply
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.cont_mono
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.adp
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.accept
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.exercise_8_1_4
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.exercise_8_1_4_bellman
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.exercise_8_1_4_counterexample
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.Bagg
#print axioms SargentStachurski.AdditionalApplications.BoundedSearch.exercise_8_1_5
#print axioms SargentStachurski.AdditionalApplications.gfun
#print axioms SargentStachurski.AdditionalApplications.integrable_max_wage
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_6
#print axioms SargentStachurski.AdditionalApplications.gfun_contracting
#print axioms SargentStachurski.AdditionalApplications.gfun_mono
#print axioms SargentStachurski.AdditionalApplications.hstar
#print axioms SargentStachurski.AdditionalApplications.hstar_eq
#print axioms SargentStachurski.AdditionalApplications.hstar_unique
#print axioms SargentStachurski.AdditionalApplications.wstar
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_7
#print axioms SargentStachurski.AdditionalApplications.JobSearch.section_8_1_2_1
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.eL
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.G
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.G_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.fdp
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.isOrderPreserving
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.Gsup_coeFn
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.ADP.ext_T
#print axioms SargentStachurski.AdditionalApplications.JobSearchFDP.section_8_1_2_2
#print axioms SargentStachurski.AdditionalApplications.fixedPoint_ge_of_le
#print axioms SargentStachurski.AdditionalApplications.example_8_1_1
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_9
#print axioms SargentStachurski.AdditionalApplications.ffun
#print axioms SargentStachurski.AdditionalApplications.ffun_contracting
#print axioms SargentStachurski.AdditionalApplications.ffun_mono
#print axioms SargentStachurski.AdditionalApplications.wstar_eq_fixedPoint
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_10
#print axioms SargentStachurski.AdditionalApplications.FOSDle
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_12
#print axioms SargentStachurski.AdditionalApplications.IsMPS
#print axioms SargentStachurski.AdditionalApplications.integral_max_le_of_isMPS
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_13
#print axioms SargentStachurski.AdditionalApplications.accept_iff
#print axioms SargentStachurski.AdditionalApplications.firstPassage
#print axioms SargentStachurski.AdditionalApplications.firstPassage_mono
#print axioms SargentStachurski.AdditionalApplications.exercise_8_1_11
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.mk
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.P
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.φ
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.stationary
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.ν
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.ω
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_ω
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_ω
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.c
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.β
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.β_nonneg
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.e
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_e
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_e
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.ae_integrable_e
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_absInt
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Pop
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.cconst
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_pair
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.accF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.qF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_accF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_qF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.qF_nonneg
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.qF_le_one
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.abs_qF_le
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.ae_abs_accF_le
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_accF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.accL
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Φσ
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.mσ
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Kσ
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.D
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.smul_isPositive
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.smul_le_smul'
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.D_isPositive
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Kσ_isPositive
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Kσ_le_D
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.norm_D_le
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.specRad_D_lt_one
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.adp
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.T_eq
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Φσ_coeFn
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.ΦmaxF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.measurable_ΦmaxF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_ΦmaxF
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Φmax
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.accept
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_choice
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.integrable_max_e
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Φσ_le_Φmax
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.Φσ_accept
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.That
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.exercise_8_1_21_22
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.regular
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.That_coeFn
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.exercise_8_1_23
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.That_contracting
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.That_mono
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.isAdditive
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.section_8_1_3_3
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.withC
#print axioms SargentStachurski.AdditionalApplications.PersistentSearch.exercise_8_1_24
#print axioms SargentStachurski.AdditionalApplications.convexOn_rpow_of_neg
#print axioms SargentStachurski.AdditionalApplications.PosBdd
#print axioms SargentStachurski.AdditionalApplications.pmean
#print axioms SargentStachurski.AdditionalApplications.PosBdd.pos
#print axioms SargentStachurski.AdditionalApplications.PosBdd.integrable_rpow
#print axioms SargentStachurski.AdditionalApplications.PosBdd.integral_rpow_pos
#print axioms SargentStachurski.AdditionalApplications.PosBdd.pmean_pos
#print axioms SargentStachurski.AdditionalApplications.PosBdd.add
#print axioms SargentStachurski.AdditionalApplications.PosBdd.smul
#print axioms SargentStachurski.AdditionalApplications.posBdd_const
#print axioms SargentStachurski.AdditionalApplications.pmean_const
#print axioms SargentStachurski.AdditionalApplications.pmean_mono
#print axioms SargentStachurski.AdditionalApplications.pmean_smul
#print axioms SargentStachurski.AdditionalApplications.integral_rpow_normalize
#print axioms SargentStachurski.AdditionalApplications.integral_rpow_add_le
#print axioms SargentStachurski.AdditionalApplications.le_integral_rpow_add
#print axioms SargentStachurski.AdditionalApplications.pmean_add_ge
#print axioms SargentStachurski.AdditionalApplications.pmean_add_le
#print axioms SargentStachurski.AdditionalApplications.pmean_concave
#print axioms SargentStachurski.AdditionalApplications.pmean_convex
#print axioms SargentStachurski.AdditionalApplications.bdd_comp
#print axioms SargentStachurski.AdditionalApplications.bexp
#print axioms SargentStachurski.AdditionalApplications.bexp_properties
#print axioms SargentStachurski.AdditionalApplications.NLDiscount
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.mk
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.P
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.wage
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.measurable_wage
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₁
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₂
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₁_lt
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.wage_mem
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.c
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.c_pos
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.c_lt
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.b
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.b_pos
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.b_lt_one
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₂_ge
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.βf
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.continuous_βf
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.monotone_βf
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.concave_βf
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.βf_zero
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.βf_lt
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.vbarR
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.vbar
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.one_sub_b_pos
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₂_add_b_le
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.c_add_b_le
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₁_pos
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.w₁_lt_vbar
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.vbar_pos
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.zero_le_vbar
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.H
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.H_apply
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.exercise_8_2_1
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.concaveOn_H
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.exercise_8_2_2
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.e
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.e_mem
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.H_e
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.e_ge_w₁
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.cont
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.measurable_cont
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.integrable_βf
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.cont_bounds
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.Tfun
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.exercise_8_2_3
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.cont_mono
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.adp
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.accept
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.regular
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.concaveOn_T
#print axioms SargentStachurski.AdditionalApplications.NLDiscount.exercise_8_2_4
#print axioms SargentStachurski.AdditionalApplications.KPSearch
#print axioms SargentStachurski.AdditionalApplications.KPSearch.mk
#print axioms SargentStachurski.AdditionalApplications.KPSearch.P
#print axioms SargentStachurski.AdditionalApplications.KPSearch.wage
#print axioms SargentStachurski.AdditionalApplications.KPSearch.measurable_wage
#print axioms SargentStachurski.AdditionalApplications.KPSearch.w₁
#print axioms SargentStachurski.AdditionalApplications.KPSearch.w₂
#print axioms SargentStachurski.AdditionalApplications.KPSearch.w₁_lt
#print axioms SargentStachurski.AdditionalApplications.KPSearch.wage_mem
#print axioms SargentStachurski.AdditionalApplications.KPSearch.c
#print axioms SargentStachurski.AdditionalApplications.KPSearch.c_pos
#print axioms SargentStachurski.AdditionalApplications.KPSearch.c_lt
#print axioms SargentStachurski.AdditionalApplications.KPSearch.β
#print axioms SargentStachurski.AdditionalApplications.KPSearch.β_pos
#print axioms SargentStachurski.AdditionalApplications.KPSearch.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.KPSearch.γ
#print axioms SargentStachurski.AdditionalApplications.KPSearch.γ_ne
#print axioms SargentStachurski.AdditionalApplications.KPSearch.p_ne
#print axioms SargentStachurski.AdditionalApplications.KPSearch.Rf
#print axioms SargentStachurski.AdditionalApplications.KPSearch.exercise_8_2_5
#print axioms SargentStachurski.AdditionalApplications.KPSearch.vbarR
#print axioms SargentStachurski.AdditionalApplications.KPSearch.lo
#print axioms SargentStachurski.AdditionalApplications.KPSearch.vbar
#print axioms SargentStachurski.AdditionalApplications.KPSearch.one_sub_β_pos
#print axioms SargentStachurski.AdditionalApplications.KPSearch.w₂_pos
#print axioms SargentStachurski.AdditionalApplications.KPSearch.vbar_eq
#print axioms SargentStachurski.AdditionalApplications.KPSearch.c_lt_vbar
#print axioms SargentStachurski.AdditionalApplications.KPSearch.lo_le_vbar
#print axioms SargentStachurski.AdditionalApplications.KPSearch.efun
#print axioms SargentStachurski.AdditionalApplications.KPSearch.efun_bounds
#print axioms SargentStachurski.AdditionalApplications.KPSearch.measurable_efun
#print axioms SargentStachurski.AdditionalApplications.KPSearch.posBdd
#print axioms SargentStachurski.AdditionalApplications.KPSearch.Rf_bounds
#print axioms SargentStachurski.AdditionalApplications.KPSearch.measurable_Rf
#print axioms SargentStachurski.AdditionalApplications.KPSearch.Tval
#print axioms SargentStachurski.AdditionalApplications.KPSearch.Tval_bounds
#print axioms SargentStachurski.AdditionalApplications.KPSearch.Tfun
#print axioms SargentStachurski.AdditionalApplications.KPSearch.adp
#print axioms SargentStachurski.AdditionalApplications.KPSearch.regular
#print axioms SargentStachurski.AdditionalApplications.KPSearch.extendIcc_eq
#print axioms SargentStachurski.AdditionalApplications.KPSearch.section_8_2_2
#print axioms SargentStachurski.AdditionalApplications.eq_8_41
#print axioms SargentStachurski.AdditionalApplications.Separation
#print axioms SargentStachurski.AdditionalApplications.Separation.mk
#print axioms SargentStachurski.AdditionalApplications.Separation.P
#print axioms SargentStachurski.AdditionalApplications.Separation.wage
#print axioms SargentStachurski.AdditionalApplications.Separation.measurable_wage
#print axioms SargentStachurski.AdditionalApplications.Separation.M
#print axioms SargentStachurski.AdditionalApplications.Separation.wage_mem
#print axioms SargentStachurski.AdditionalApplications.Separation.c
#print axioms SargentStachurski.AdditionalApplications.Separation.β
#print axioms SargentStachurski.AdditionalApplications.Separation.β_pos
#print axioms SargentStachurski.AdditionalApplications.Separation.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.Separation.α
#print axioms SargentStachurski.AdditionalApplications.Separation.α_pos
#print axioms SargentStachurski.AdditionalApplications.Separation.α_lt_one
#print axioms SargentStachurski.AdditionalApplications.Separation.denom_pos
#print axioms SargentStachurski.AdditionalApplications.Separation.h
#print axioms SargentStachurski.AdditionalApplications.Separation.γ
#print axioms SargentStachurski.AdditionalApplications.Separation.γ_nonneg
#print axioms SargentStachurski.AdditionalApplications.Separation.γ_lt_one
#print axioms SargentStachurski.AdditionalApplications.Separation.Pop
#print axioms SargentStachurski.AdditionalApplications.Separation.abs_Pop_sub_le
#print axioms SargentStachurski.AdditionalApplications.Separation.stopV
#print axioms SargentStachurski.AdditionalApplications.Separation.contV
#print axioms SargentStachurski.AdditionalApplications.Separation.T
#print axioms SargentStachurski.AdditionalApplications.Separation.T_apply
#print axioms SargentStachurski.AdditionalApplications.Separation.adp
#print axioms SargentStachurski.AdditionalApplications.Separation.accept
#print axioms SargentStachurski.AdditionalApplications.Separation.accept_isGreedy
#print axioms SargentStachurski.AdditionalApplications.Separation.regular
#print axioms SargentStachurski.AdditionalApplications.Separation.exercise_8_2_12
#print axioms SargentStachurski.AdditionalApplications.Separation.proposition_8_2_2
#print axioms SargentStachurski.AdditionalApplications.Separation.bellman_apply
#print axioms SargentStachurski.AdditionalApplications.Separation.bellman_contracting
#print axioms SargentStachurski.AdditionalApplications.Separation.exercise_8_2_13
#print axioms SargentStachurski.AdditionalApplications.IsMLR
#print axioms SargentStachurski.AdditionalApplications.TwoDensities
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.mk
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.M_pos
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.f
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.g
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_f
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_g
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integral_f
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integral_g
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.f_pos
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.g_pos
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.f_zero
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.g_zero
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.f_nonneg
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.g_nonneg
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integrable_f
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integrable_g
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integrable_mul
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.proposition_A_5_34
#print axioms SargentStachurski.AdditionalApplications.exercise_8_2_10
#print axioms SargentStachurski.AdditionalApplications.betaF
#print axioms SargentStachurski.AdditionalApplications.betaG
#print axioms SargentStachurski.AdditionalApplications.exercise_8_2_11
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.φ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.κ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.pκ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.pw
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.φ_nonneg
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.φ_le
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.φ_pos
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.φ_zero
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_φ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_κ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_pκ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.measurable_pw
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integrable_φ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integral_φ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.integral_mul_φ
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.abs_integral_mul_φ_le
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.κ_mem
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.κ_mono_prior
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.κ_mono_offer
#print axioms SargentStachurski.AdditionalApplications.TwoDensities.continuous_κ
#print axioms SargentStachurski.AdditionalApplications.LearningSearch
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.mk
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.D
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.c
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.β
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.β_pos
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.LState
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.one_sub_β_pos
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.contR
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_integrand
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_section
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.integrable_section
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_contR
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.abs_contR_le
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.abs_contR_sub_le
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_stop
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_cont
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.T
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.adp
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.accept
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.accept_isGreedy
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.exercise_8_2_6
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.exercise_8_2_7
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.regular
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.T_contraction
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.optimality
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.G
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_Gφ
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.measurable_G
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.abs_G_le
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.integrable_Gφ
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That_apply
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That_eq
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.abs_That_sub_le
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.exercise_8_2_8
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That_contracting
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.exercise_8_2_9
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.ωstar
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That_ωstar
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.tendstoUniformly_ωstar
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.continuous_ωstar
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.vOf
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.contR_vOf
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.abs_bellman_sub_le
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.bellman_contracting
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.bellman_eq_iff
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.That_monotone
#print axioms SargentStachurski.AdditionalApplications.LearningSearch.proposition_8_2_1
#print axioms SargentStachurski.AdditionalApplications.orderStable_of_iterate_eq
#print axioms SargentStachurski.AdditionalApplications.NegDiscount
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.mk
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.c
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.δ
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.one_lt_δ
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.xh
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.xh_pos
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.η
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.η_pos
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.c_zero
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.differentiable
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.continuous_deriv
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.strictConvexOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.strictMonoOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.deriv_zero_pos
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.η_spec
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.δ_pos
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.zero_mem
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.c_mono
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.η_spec_of_eq
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.k0
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.mk
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.σ
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.mem
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.monotoneOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.monotoneOn_effort
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.eq_zero_iff
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.zero_outside
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.mem_Icc
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.iterate_mem
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.map_zero
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.le_max_sub
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.iterate_le
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.iterate_eq_zero
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.abs_sub_le
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Policy.continuousOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.ση
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Val
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.Tfun
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.T
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.T_apply
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.adp
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.exercise_8_3_1
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.iterate_k0_eq
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.zeroVal
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.lemma_8_3_3
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.isOrderStable
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.InV0
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.g
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.tangent_zero
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.four_point_strict
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.four_point
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.v_zero
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.exists_min
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.unique_min
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedyFun
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedy_spec
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedyFun_monotoneOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedyFun_effort
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedyFun_eq_zero_iff
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedy
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.greedy_isMinOn
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.lemma_8_3_4
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.exercise_8_3_2
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.V0
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.T_greedy_mem
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.bellman
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.bellman_apply
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.bellman_le
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.cV0
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.bellman_iterate_agree
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.bellman_iterate_k0
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.lemma_8_3_5
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.exercise_8_3_3
#print axioms SargentStachurski.AdditionalApplications.NegDiscount.theorem_8_3_6
#print axioms SargentStachurski.AdditionalApplications.boundary
#print axioms SargentStachurski.AdditionalApplications.IsChainEquilibrium
#print axioms SargentStachurski.AdditionalApplications.ProductionChain
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.mk
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.c
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.δ
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.one_lt_δ
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.c_zero
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.differentiable
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.continuous_deriv
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.strictConvexOn
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.strictMonoOn
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.deriv_zero_pos
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.exists_η
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.toNeg
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.proposition_8_3_1
#print axioms SargentStachurski.AdditionalApplications.ProductionChain.proposition_8_3_2
#print axioms SargentStachurski.AdditionalApplications.Harvest
#print axioms SargentStachurski.AdditionalApplications.Harvest.mk
#print axioms SargentStachurski.AdditionalApplications.Harvest.φ
#print axioms SargentStachurski.AdditionalApplications.Harvest.rev
#print axioms SargentStachurski.AdditionalApplications.Harvest.measurable_rev
#print axioms SargentStachurski.AdditionalApplications.Harvest.bdd_rev
#print axioms SargentStachurski.AdditionalApplications.Harvest.cost
#print axioms SargentStachurski.AdditionalApplications.Harvest.measurable_cost
#print axioms SargentStachurski.AdditionalApplications.Harvest.bdd_cost
#print axioms SargentStachurski.AdditionalApplications.Harvest.q
#print axioms SargentStachurski.AdditionalApplications.Harvest.measurable_q
#print axioms SargentStachurski.AdditionalApplications.Harvest.s₀
#print axioms SargentStachurski.AdditionalApplications.Harvest.β
#print axioms SargentStachurski.AdditionalApplications.Harvest.β_nonneg
#print axioms SargentStachurski.AdditionalApplications.Harvest.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.Harvest.f
#print axioms SargentStachurski.AdditionalApplications.Harvest.r
#print axioms SargentStachurski.AdditionalApplications.Harvest.measurable_f
#print axioms SargentStachurski.AdditionalApplications.Harvest.integrable_section
#print axioms SargentStachurski.AdditionalApplications.Harvest.abs_integral_le
#print axioms SargentStachurski.AdditionalApplications.Harvest.F
#print axioms SargentStachurski.AdditionalApplications.Harvest.measurable_r
#print axioms SargentStachurski.AdditionalApplications.Harvest.G
#print axioms SargentStachurski.AdditionalApplications.Harvest.G_apply
#print axioms SargentStachurski.AdditionalApplications.Harvest.harvestWhere
#print axioms SargentStachurski.AdditionalApplications.Harvest.G_harvestWhere
#print axioms SargentStachurski.AdditionalApplications.Harvest.G_le_G_harvestWhere
#print axioms SargentStachurski.AdditionalApplications.Harvest.fdp
#print axioms SargentStachurski.AdditionalApplications.Harvest.isOrderPreserving
#print axioms SargentStachurski.AdditionalApplications.Harvest.exercise_8_3_4
#print axioms SargentStachurski.AdditionalApplications.Harvest.abs_F_sub_le
#print axioms SargentStachurski.AdditionalApplications.Harvest.primary_contraction
#print axioms SargentStachurski.AdditionalApplications.Harvest.G_eq_Gsup_iff
#print axioms SargentStachurski.AdditionalApplications.Harvest.section_8_3_2_2
#print axioms SargentStachurski.AdditionalApplications.hasDerivAt_of_concave_sandwich
#print axioms SargentStachurski.AdditionalApplications.Growth
#print axioms SargentStachurski.AdditionalApplications.Growth.mk
#print axioms SargentStachurski.AdditionalApplications.Growth.u
#print axioms SargentStachurski.AdditionalApplications.Growth.f
#print axioms SargentStachurski.AdditionalApplications.Growth.φ
#print axioms SargentStachurski.AdditionalApplications.Growth.shock_pos
#print axioms SargentStachurski.AdditionalApplications.Growth.β
#print axioms SargentStachurski.AdditionalApplications.Growth.β_pos
#print axioms SargentStachurski.AdditionalApplications.Growth.β_lt_one
#print axioms SargentStachurski.AdditionalApplications.Growth.measurable_u
#print axioms SargentStachurski.AdditionalApplications.Growth.u_continuousOn
#print axioms SargentStachurski.AdditionalApplications.Growth.u_strictMonoOn
#print axioms SargentStachurski.AdditionalApplications.Growth.u_strictConcaveOn
#print axioms SargentStachurski.AdditionalApplications.Growth.u_differentiableAt
#print axioms SargentStachurski.AdditionalApplications.Growth.u_deriv_continuousOn
#print axioms SargentStachurski.AdditionalApplications.Growth.u_bdd
#print axioms SargentStachurski.AdditionalApplications.Growth.u_zero
#print axioms SargentStachurski.AdditionalApplications.Growth.u_inada
#print axioms SargentStachurski.AdditionalApplications.Growth.measurable_f
#print axioms SargentStachurski.AdditionalApplications.Growth.f_continuousOn
#print axioms SargentStachurski.AdditionalApplications.Growth.f_strictMonoOn
#print axioms SargentStachurski.AdditionalApplications.Growth.f_concaveOn
#print axioms SargentStachurski.AdditionalApplications.Growth.f_differentiableAt
#print axioms SargentStachurski.AdditionalApplications.Growth.f_zero
#print axioms SargentStachurski.AdditionalApplications.Growth.u_concaveOn
#print axioms SargentStachurski.AdditionalApplications.Growth.u_mono
#print axioms SargentStachurski.AdditionalApplications.Growth.f_mono
#print axioms SargentStachurski.AdditionalApplications.Growth.f_nonneg
#print axioms SargentStachurski.AdditionalApplications.Growth.f_pos
#print axioms SargentStachurski.AdditionalApplications.Growth.deriv_u_nonneg
#print axioms SargentStachurski.AdditionalApplications.Growth.deriv_f_nonneg
#print axioms SargentStachurski.AdditionalApplications.Growth.deriv_u_strictAntiOn
#print axioms SargentStachurski.AdditionalApplications.Growth.deriv_f_antitoneOn
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_5
#print axioms SargentStachurski.AdditionalApplications.Growth.Γ
#print axioms SargentStachurski.AdditionalApplications.Growth.cont
#print axioms SargentStachurski.AdditionalApplications.Growth.B
#print axioms SargentStachurski.AdditionalApplications.Growth.measurable_integrand
#print axioms SargentStachurski.AdditionalApplications.Growth.integrable_cont
#print axioms SargentStachurski.AdditionalApplications.Growth.abs_cont_le
#print axioms SargentStachurski.AdditionalApplications.Growth.cont_add_const
#print axioms SargentStachurski.AdditionalApplications.Growth.brdp
#print axioms SargentStachurski.AdditionalApplications.Growth.isBlackwell
#print axioms SargentStachurski.AdditionalApplications.Growth.hasMaxSelections
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_6
#print axioms SargentStachurski.AdditionalApplications.Growth.indPos
#print axioms SargentStachurski.AdditionalApplications.Growth.cont_indPos_lt
#print axioms SargentStachurski.AdditionalApplications.Growth.cont_indPos_self
#print axioms SargentStachurski.AdditionalApplications.Growth.tendsto_u_left
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_6_false
#print axioms SargentStachurski.AdditionalApplications.Growth.not_regular
#print axioms SargentStachurski.AdditionalApplications.Growth.proposition_8_3_7
#print axioms SargentStachurski.AdditionalApplications.Growth.ICC
#print axioms SargentStachurski.AdditionalApplications.Growth.isClosed_ICC
#print axioms SargentStachurski.AdditionalApplications.Growth.zero_mem_ICC
#print axioms SargentStachurski.AdditionalApplications.Growth.cont_mono
#print axioms SargentStachurski.AdditionalApplications.Growth.cont_concave
#print axioms SargentStachurski.AdditionalApplications.Growth.B_concave
#print axioms SargentStachurski.AdditionalApplications.Growth.bellman_mem_ICC
#print axioms SargentStachurski.AdditionalApplications.Growth.strictConcaveOn_B
#print axioms SargentStachurski.AdditionalApplications.Growth.lemma_8_3_8
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_8
#print axioms SargentStachurski.AdditionalApplications.Growth.argmax_pos
#print axioms SargentStachurski.AdditionalApplications.Growth.proposition_8_3_9
#print axioms SargentStachurski.AdditionalApplications.Growth.proposition_8_3_9_not_interior
#print axioms SargentStachurski.AdditionalApplications.Growth.corollary_8_3_10
#print axioms SargentStachurski.AdditionalApplications.Growth.SigmaC
#print axioms SargentStachurski.AdditionalApplications.Growth.eulerIntegrand
#print axioms SargentStachurski.AdditionalApplications.Growth.SolvesEuler
#print axioms SargentStachurski.AdditionalApplications.Growth.SatisfiesEuler
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_9
#print axioms SargentStachurski.AdditionalApplications.Growth.eulerIntegrand_nonneg
#print axioms SargentStachurski.AdditionalApplications.Growth.eulerIntegrand_mono
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_10
#print axioms SargentStachurski.AdditionalApplications.Growth.solvesEuler_unique
#print axioms SargentStachurski.AdditionalApplications.Growth.exercise_8_3_12_step
